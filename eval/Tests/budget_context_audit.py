"""Independent fixtures for explicitly versioned request-only budget notices."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'runner'))
sys.path.insert(0,str(ROOT/'Tests'))
from audit_continuation import AuditError,audit_run,compact
from continuation_audit import fixture,write_frames


def notice(models,tools,output=4096,version=2,timeout_ms=90000):
    # Independent fixture literal; do not call the implementation's formatter.
    timeout = (('Configured command time limit: %d ms; cleanup may take additional time. '
                'The remaining invocation deadline may shorten this limit. '
                'An interrupted command may have partial effects; inspect them before continuing. '
                'Prefer focused checks that fit the time limit. ') % timeout_ms) if version == 3 else ''
    return {'role':'user','content':[{'type':'text','text':(
        '[Harness limits] After this request, at most %d further model requests and %d tool executions remain. '
        'Model requests include task responses, summaries, retries, and response repairs. '
        'This response is capped at %d output tokens. ') % (models,tools,output) + timeout +
        'Inspecting tool results and then responding requires another model request. '
        'These limits do not grant permission.'}]}


def persist(directory,records):
    write_frames(directory/'sessions/session/journal.jsonl',records)
    path=directory/'events.jsonl'
    events=[json.loads(x) for x in path.read_text().split('\n') if x]
    indexed={(r['id'],r['kind']):r for r in records[1:] if r['kind'] in ['intent','completion']}
    for e in events:
        if e['event'] in ['intent','completion']:
            r=indexed[e['operation'],e['event']]
            data=r['action'] if e['event']=='intent' else r['observation']
            e['data']=copy.deepcopy(data) if len(compact(data).encode())<=32768 else {
                'omitted':True,'reason':'event payload exceeds 32768 bytes; inspect the journal'}
    path.write_text(''.join(json.dumps(e)+'\n' for e in events))


def versioned_fixture(directory,repair=None,transient=False,version=2,timed_out=False):
    broker,plan,records=fixture(directory,schema=5 if version==3 or timed_out else 4,
                                with_artifact=True,repair=repair,transient=transient,timed_out=timed_out)
    config=records[0]['config'];config['maxToolCalls']=10
    inspection_path=directory/'inspection.json'
    inspection=json.loads(inspection_path.read_text())
    inspection['state']['config']=copy.deepcopy(config)
    inspection_path.write_text(json.dumps(inspection))
    models=tools=0
    task_records=[]
    for r in records[1:]:
        if r['kind']!='intent':continue
        a=r['action']
        if a['kind']=='tool':tools+=1
        if a['kind']=='model':
            models+=1
            if a['request']['purpose']=='task':
                a['request']['messages'].append(notice(20-models,10-tools,version=version))
                task_records.append(r)
    plan['task_context_version']=version
    persist(directory,records)
    # Use the separate v3 circular-qualification correction simultaneously.
    result_path=directory/'result.json';result=json.loads(result_path.read_text())
    result.update(qualification_version=3,success=False,exit_code=0,checker={'resolved':True})
    result_path.write_text(json.dumps(result))
    return broker,plan,records,task_records


class BudgetContextAudit(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
    def tearDown(self):self.temp.cleanup()
    def make(self,name='case',**kwargs):
        p=self.root/name;p.mkdir()
        return (p,*versioned_fixture(p,**kwargs))
    def test_version2_counts_current_reservation_summaries_and_tools(self):
        p,b,plan,records,tasks=self.make()
        self.assertEqual([t['action']['request']['messages'][-1] for t in tasks],
                         [notice(19,10),notice(17,9),notice(15,8)])
        before=(p/'inspection.json').read_bytes()
        r=audit_run(p,b,plan)
        self.assertEqual((r['task_context_version'],r['model_attempts'],r['tool_dispatches']),(2,5,2))
        self.assertEqual(r['successful_summaries'],2)
        self.assertEqual(before,(p/'inspection.json').read_bytes())
        self.assertNotIn('[Harness limits]',json.dumps(json.loads(before)['state']['history']))
    def test_repair_retry_artifact_catalog_and_restart_counts(self):
        for kind in ['invalidBatch','truncated','malformed']:
            with self.subTest(kind=kind):
                p,b,plan,records,tasks=self.make(kind,repair=kind,transient=True)
                self.assertEqual([t['action']['request']['messages'][-1] for t in tasks],
                    [notice(19,10),notice(18,9),notice(17,9),notice(15,9),notice(13,8)])
                r=audit_run(p,b,plan)
                self.assertEqual((r['model_attempts'],r['response_repairs']),(7,1))
                self.assertTrue(r['post_summary_restart_operations'])
    def test_wrong_model_or_tool_counts_and_output_cap_rejected(self):
        for kind,value in [('model',notice(20,10)),('tool',notice(19,9)),('output',notice(19,10,4095))]:
            with self.subTest(kind=kind):
                p,b,plan,records,tasks=self.make(kind)
                tasks[0]['action']['request']['messages'][-1]=value
                persist(p,records)
                with self.assertRaisesRegex(AuditError,'task context reconstruction'):audit_run(p,b,plan)
    def test_stale_missing_or_duplicate_notice_rejected(self):
        for mode in ['stale','missing','duplicate']:
            with self.subTest(mode=mode):
                p,b,plan,records,tasks=self.make(mode)
                messages=tasks[-1]['action']['request']['messages']
                if mode=='stale':messages[-1]=copy.deepcopy(tasks[0]['action']['request']['messages'][-1])
                elif mode=='missing':messages.pop()
                else:messages.append(copy.deepcopy(messages[-1]))
                persist(p,records)
                with self.assertRaisesRegex(AuditError,'task context reconstruction'):audit_run(p,b,plan)
    def test_no_payload_autodetection(self):
        p,b,plan,records,tasks=self.make()
        for version in [None,1]:
            q=copy.deepcopy(plan)
            if version is None:q.pop('task_context_version')
            else:q['task_context_version']=version
            with self.assertRaisesRegex(AuditError,'task context reconstruction'):audit_run(p,b,q)
        legacy=self.root/'legacy';legacy.mkdir();b,q,_=fixture(legacy,schema=4)
        q['task_context_version']=2
        # Supply complete frozen limits without adding the required notice.
        state=json.loads((legacy/'inspection.json').read_text());state['state']['config']['maxToolCalls']=10
        (legacy/'inspection.json').write_text(json.dumps(state))
        records=[json.loads(x)['record'] for x in (legacy/'sessions/session/journal.jsonl').read_text().split('\n') if x]
        records[0]['config']['maxToolCalls']=10;persist(legacy,records)
        with self.assertRaisesRegex(AuditError,'task context reconstruction'):audit_run(legacy,b,q)
    def test_unknown_version_rejected(self):
        p,b,plan,records,tasks=self.make()
        for version in [0,5,'2',True,None]:
            with self.subTest(version=version):
                with self.assertRaisesRegex(AuditError,'unsupported plan task_context_version'):
                    audit_run(p,b,{**plan,'task_context_version':version})
    def test_legacy_versions_unchanged(self):
        for schema in [2,3,4]:
            with self.subTest(schema=schema):
                p=self.root/f'legacy-{schema}';p.mkdir();b,plan,_=fixture(p,schema=schema)
                for version in [None,1]:
                    q=copy.deepcopy(plan)
                    if version is not None:q['task_context_version']=version
                    self.assertEqual(audit_run(p,b,q)['task_context_version'],1)
    def test_summary_requests_must_not_gain_notice(self):
        p,b,plan,records,tasks=self.make()
        summary=next(r for r in records if r['kind']=='intent' and r['action']['kind']=='model' and r['action']['request']['purpose']=='summary')
        summary['action']['request']['messages'].append(notice(18,9));persist(p,records)
        with self.assertRaisesRegex(AuditError,'summary source reconstruction'):audit_run(p,b,plan)

    def test_version3_timeout_notice_and_skipped_calls_use_only_actual_reservations(self):
        p,b,plan,records,tasks=self.make(version=3,timed_out=True,repair='malformed',transient=True)
        self.assertEqual([t['action']['request']['messages'][-1] for t in tasks],
            [notice(19,10,version=3),notice(18,9,version=3),notice(17,9,version=3),
             notice(15,9,version=3),notice(13,8,version=3)])
        report=audit_run(p,b,plan)
        self.assertEqual(report['task_context_version'],3)
        self.assertEqual(report['tool_dispatches'],2)
        self.assertEqual(report['timed_out_tools'],1)
        self.assertEqual(report['skipped_tool_call_ids'],['skip-create','skip-read'])
        self.assertNotIn('[Harness limits]',json.dumps(json.loads((p/'inspection.json').read_text())['state']['history']))

    def test_version3_requires_exact_frozen_timeout_notice_without_autodetection(self):
        for change in ['wrong-duration','missing-duration','declared-v2']:
            with self.subTest(change=change):
                p,b,plan,records,tasks=self.make(change,version=3)
                if change=='declared-v2':plan['task_context_version']=2
                else:
                    tasks[0]['action']['request']['messages'][-1]=notice(19,10,
                        version=2 if change=='missing-duration' else 3,timeout_ms=89999)
                    persist(p,records)
                with self.assertRaisesRegex(AuditError,'task context reconstruction'):audit_run(p,b,plan)
        for value in [None,-1,True,'90000']:
            with self.subTest(timeout=value):
                p,b,plan,records,tasks=self.make('bound-'+str(value),version=3)
                state=json.loads((p/'inspection.json').read_text())
                state['state']['config']['operationTimeoutMs']=value;records[0]['config']['operationTimeoutMs']=value
                (p/'inspection.json').write_text(json.dumps(state));persist(p,records)
                with self.assertRaisesRegex(AuditError,'frozen operationTimeoutMs'):audit_run(p,b,plan)

if __name__=='__main__':unittest.main()
