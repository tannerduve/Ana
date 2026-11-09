"""Exercise private runner parsers/plans with every external operation mocked."""
from contextlib import ExitStack,redirect_stdout,redirect_stderr
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import MagicMock,patch

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'runner'))
import public_bench as public
import sustained
import suite


def run_suite_fixture(root,extra):
    binary=root/'binary';binary.write_bytes(b'fixture binary')
    key=root/'offline-key';key.write_text('not-a-provider-key')
    corpus=root/'corpus';corpus.mkdir()
    (corpus/'manifest.json').write_text(json.dumps({'tasks':[{'id':'fixture'}]}))
    output=root/'output'
    argv=['suite','--output',str(output),'--key-file',str(key),
          '--campaign-dir',str(root/'ledger'),'--allocation','development',
          '--engines','lean','--tracks','product','--repetitions','1',*extra]
    observed={}
    def run_one(task,engine,track,repetition,broker,directory,args):
        observed['child_task_context_version']=args.task_context_version
        observed['child_engine']=engine
        observed['child_model_attempt_ceiling']=args.max_attempts
        # The field must be written in the plan before any candidate run begins.
        observed['plan_before_run']=json.loads((directory/'plan.json').read_text())
        return {'task_id':task['id'],'engine':engine,'track':track,'repetition':repetition,
                'success':False,'provider_attempts':0,'accounted_usd':0}
    broker=MagicMock();broker.__enter__.return_value.total=0
    with ExitStack() as stack:
        for attr,value in [('harness_root',root),('require_fresh_harness',binary),
                           ('eval_tools_binary',binary),('toolchains',[]),
                           ('product_provenance',{}),('evaluation_provenance',{})]:
            stack.enter_context(patch.object(suite,attr,return_value=value))
        stack.enter_context(patch.object(suite,'CORPUS',corpus))
        stack.enter_context(patch.object(suite,'Broker',return_value=broker))
        stack.enter_context(patch.object(suite,'run_one',side_effect=run_one))
        stack.enter_context(patch.object(suite.subprocess,'check_output',return_value=b'[]'))
        stack.enter_context(patch.object(sys,'argv',argv))
        with redirect_stdout(io.StringIO()):code=suite.main()
    observed.update(exit_code=code,plan=json.loads((output/'plan.json').read_text()),argv=argv)
    assert observed['plan_before_run']==observed['plan']
    return observed


def run_fixture(name,root,extra,pi_settings=None,output_tokens=None):
    if name=='suite':
        assert pi_settings is None
        return run_suite_fixture(root,extra)
    runner=public if name=='public' else sustained
    binary=root/'binary';binary.write_bytes(b'fixture binary')
    key=root/'offline-key';key.write_text('not-a-provider-key')
    source=root/'task.json'
    selected=[{'id':'fixture','benchmark':'SWE-fixture','workspace':'/workspace',
               'image_digest':'fixture-image','task_text':'[Harness limits] Payload text is not a context-version selector.'}]
    source.write_text(json.dumps({'swebench':{'tasks':selected}}))
    mode={'id':'restart','engine':'lean','max_attempts':2,'max_tools':2,
          'context_bytes':30000,'timeout':10,'yield_after':1}
    if pi_settings is not None:
        mode.update(id='pi',engine='pi',yield_after=0,pi=pi_settings)
    if output_tokens is not None:
        mode['config']={'maxOutputTokens':output_tokens}
    # Budget-notice-like task text must not choose the plan version.
    manifest={'status':'FROZEN_SUSTAINED','tasks':selected,'modes':[mode]}
    output=root/'output'
    argv=[name,'run','--output',str(output),'--key-file',str(key),'--campaign-dir',str(root/'ledger')]
    if name=='public':argv+=['--lock',str(source),'--allocation','heldout','--engines','lean']
    else:argv+=['--manifest',str(source),'--prepared-bwrap',str(binary),'--bwrap-sha256','fixture']
    argv+=extra
    observed={}
    def run_one(task,engine,repetition,rows,args,directory,broker,**kwargs):
        observed['child_task_context_version']=args.task_context_version
        observed['child_engine']=engine
        observed['child_model_attempt_ceiling']=args.max_attempts
        observed['child_pi_settings']=getattr(args,'pi_settings',{})
        observed['child_output_tokens']=getattr(args,'config_overrides',{}).get(
            'maxOutputTokens',getattr(args,'max_output_tokens',4096))
        record={'run_id':'fixture-run','task_id':'fixture','engine':engine,'success':False,
                'artifact_pass':True,'normal_finish':True,'qualification_status':'pending',
                'provider_attempts':0,'accounted_usd':0,'checker':{'resolved':True}}
        (directory/record['run_id']).mkdir()
        return record
    def audit_restart(directory,plan):
        observed['auditor_plan_version']=plan['task_context_version']
        return {'status':'passed'}
    with ExitStack() as stack:
        for owner,attr,value in [
            (public,'harness_binary',binary),(public,'eval_tools_binary',binary),
            (public,'harness_root',root),(public,'require_fresh_harness',binary),
            (public,'node_root',root),(public,'prepared_sandbox',None),
            (public,'check_assets',[]),(public,'product_provenance',{}),(public,'evaluation_provenance',{}),
            (public,'Owner',SimpleNamespace(uncertain=False,cleanup=lambda:{'settled':True})),
            (public,'docker',SimpleNamespace(returncode=0,stdout='')),
            (public,'automated_checks',{}),
            (sustained,'validate_manifest',manifest),(sustained,'harness_root',root),
            (sustained,'require_fresh_harness',binary),(sustained,'harness_binary',binary),
            (sustained,'eval_tools_binary',binary),(sustained,'node_root',root),
            (sustained,'product_provenance',{}),(sustained,'evaluation_provenance',{})]:
            stack.enter_context(patch.object(owner,attr,return_value=value))
        stack.enter_context(patch.object(public,'run_one',side_effect=run_one))
        stack.enter_context(patch.object(sustained,'audit_restart',side_effect=audit_restart))
        stack.enter_context(patch.object(runner,'Broker',return_value=MagicMock()))
        stack.enter_context(patch.object(public,'ACTIVE_OWNER',None))
        stack.enter_context(patch.object(public.subprocess,'check_output',return_value=b'[]'))
        stack.enter_context(patch.object(sys,'argv',argv))
        with redirect_stdout(io.StringIO()):
            code=runner.main()
    observed.update(exit_code=code,plan=json.loads((output/'plan.json').read_text()),argv=argv)
    return observed


class PlanContextVersion(unittest.TestCase):
    def test_output_ceiling_is_frozen_and_forwarded_without_changing_default(self):
        for name in ['public','sustained']:
            for tokens in [None,8192]:
                with self.subTest(runner=name,tokens=tokens),tempfile.TemporaryDirectory() as temporary:
                    extra=['--max-output-tokens',str(tokens)] if name=='public' and tokens is not None else []
                    result=run_fixture(name,Path(temporary),extra,output_tokens=tokens)
                    expected=tokens or 4096
                    self.assertEqual(result['child_output_tokens'],expected)
                    if name=='public':
                        self.assertEqual(result['plan']['max_output_tokens'],expected)
                    else:
                        self.assertEqual(result['plan']['modes'][0].get('config',{}).get('maxOutputTokens',4096),expected)

    def test_invalid_public_output_ceiling_precedes_external_preparation(self):
        for token in ['0','-1','8193','True','1.5']:
            with self.subTest(token=token),patch.object(sys,'argv',[
                    'public','run','--output','/unused','--max-output-tokens',token]),\
                    patch.object(public,'prepared_sandbox') as setup,\
                    patch.object(public,'Broker') as broker,redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):public.main()
                setup.assert_not_called();broker.assert_not_called()

    def test_omission_preserves_legacy1_and_explicit_versions_reach_plans_and_children(self):
        for runner in ['public','sustained','suite']:
            for version in [None,1,2,3,4]:
                with self.subTest(runner=runner,version=version),tempfile.TemporaryDirectory() as tmp:
                    flags=[] if version is None else ['--task-context-version',str(version)]
                    observed=run_fixture(runner,Path(tmp),flags)
                    expected=1 if version is None else version
                    self.assertEqual(observed['exit_code'],0)
                    self.assertEqual(observed['plan']['task_context_version'],expected)
                    self.assertEqual(observed['plan']['request_evidence_version'],1)
                    self.assertEqual(observed['child_task_context_version'],expected)
                    self.assertEqual(observed['child_engine'],'lean')
                    if runner=='sustained':
                        self.assertEqual(observed['auditor_plan_version'],expected)
                        self.assertEqual(observed['child_model_attempt_ceiling'],2)
                    else:self.assertEqual(observed['child_model_attempt_ceiling'],12)
    def test_invalid_values_rejected_before_external_or_output_work(self):
        for runner in [public,sustained,suite]:
            for value in ['0','5','2.0','true','']:
                with self.subTest(runner=runner.__name__,value=value),tempfile.TemporaryDirectory() as tmp:
                    output=Path(tmp)/'not-created'
                    argv=[runner.__name__,*(['run'] if runner is not suite else []),
                          '--output',str(output),'--task-context-version',value]
                    if runner is sustained:argv+=['--manifest','unused','--prepared-bwrap','unused','--bwrap-sha256','unused']
                    if runner is suite:argv+=['--key-file','unused','--campaign-dir','unused','--allocation','development']
                    with patch.object(sys,'argv',argv),patch.object(runner,'harness_root') as root_lookup, \
                         patch.object(public,'prepared_sandbox') as prepare, \
                         patch.object(runner,'Broker') as broker,redirect_stderr(io.StringIO()):
                        with self.assertRaises(SystemExit) as error:runner.main()
                        self.assertEqual(error.exception.code,2)
                        prepare.assert_not_called();broker.assert_not_called()
                        root_lookup.assert_not_called()
                    self.assertFalse(output.exists())
    def test_actual_child_command_preserves_explicit_versions(self):
        for name,version in [(name,version) for name in ['public','sustained','suite'] for version in [2,3,4]]:
            with self.subTest(runner=name,version=version),tempfile.TemporaryDirectory() as tmp:
                command=[sys.executable,str(Path(__file__).resolve()),'--fixture',name,tmp,
                         '--task-context-version',str(version)]
                child=subprocess.run(command,capture_output=True,text=True,timeout=15,
                    env={'PATH':os.defpath,'HOME':tmp,'LANG':'C.UTF-8'})
                self.assertEqual(child.returncode,0,child.stderr)
                result=json.loads(child.stdout)
                self.assertEqual(result['argv'][-2:],['--task-context-version',str(version)])
                self.assertEqual(result['plan']['task_context_version'],version)
                self.assertEqual(result['child_task_context_version'],version)
                if name=='sustained':self.assertEqual(result['auditor_plan_version'],version)

if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='--fixture':
        print(json.dumps(run_fixture(sys.argv[2],Path(sys.argv[3]),sys.argv[4:])))
    else:unittest.main()
