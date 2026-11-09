#!/usr/bin/env python3
"""Run the frozen local corpus against Lean and pinned Pi in fresh namespaces."""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import uuid

from broker import Broker

ROOT = Path(__file__).resolve().parents[2]
CORPUS = ROOT / 'eval/corpus'
INSTRUCTIONS = ('You are a coding agent. Inspect README.md and relevant source files, implement the requested behavior, '
                'run the existing tests, and explain the result. Work only in /workspace. Do not modify README.md, '
                'tests, or protected theorem statements. Read before editing and use the returned SHA256 preimage. '
                'Keep changes focused. Installed tools include Python, Node, Rust, and Lean on PATH.')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def toolchains():
    lean = Path(subprocess.check_output(['lean','--print-prefix'],cwd=ROOT,text=True).strip())
    rust = Path.home()/'.rustup/toolchains/1.97.1-x86_64-unknown-linux-gnu'
    node = Path(shutil.which('node')).resolve().parent.parent
    return [(lean,'/opt/lean'),(rust,'/opt/rust'),(node,'/opt/node')]


def sandbox(workspace, mounts=()):
    command=['bwrap','--unshare-all','--share-net','--die-with-parent','--new-session']
    for path in ['/usr','/lib','/lib64','/etc/alternatives','/etc/ssl','/etc/resolv.conf','/etc/hosts','/etc/nsswitch.conf']:
        if Path(path).exists(): command += ['--ro-bind',path,path]
    command += ['--symlink','/usr/bin','/bin','--dev','/dev','--proc','/proc','--tmpfs','/tmp',
                '--bind',str(workspace),'/workspace','--chdir','/workspace']
    for source,dest in toolchains(): command += ['--ro-bind',str(source),dest]
    for source,dest,writable in mounts:
        command += ['--bind' if writable else '--ro-bind',str(source),dest]
    return command


def environment():
    return {'PATH':'/opt/lean/bin:/opt/rust/bin:/opt/node/bin:/usr/bin:/bin','HOME':'/tmp',
            'LANG':'C.UTF-8','PYTHONDONTWRITEBYTECODE':'1','CARGO_HOME':'/tmp/cargo',
            'LEAN_BIN':'/opt/lean/bin/lean','RUSTC_BIN':'/opt/rust/bin/rustc'}


def checker(task, workspace, output, label):
    cmd=sandbox(workspace,[(CORPUS,'/checker',False)])+['/usr/bin/python3','/checker/check.py',task['id'],'/workspace']
    result=subprocess.run(cmd,env={**environment(),'HARNESS_CHECKER_ISOLATE':'1'},capture_output=True,text=True,timeout=task.get('checker_timeout_seconds',120))
    (output/f'{label}.stdout').write_text(result.stdout)
    (output/f'{label}.stderr').write_text(result.stderr)
    try: report=json.loads(result.stdout)
    except ValueError: return {'passed':False,'infrastructure_error':'checker returned invalid JSON','exit':result.returncode}
    if result.returncode not in (0,1) or report.get('passed') != (result.returncode==0):
        report['infrastructure_error']='checker execution failed'
    return report


def run_process(command, output, timeout):
    with (output/'events.jsonl').open('a') as events, (output/'diagnostics.txt').open('a') as diagnostics:
        timed=['/usr/bin/time','-a','-o',str(output/'resources.jsonl'),'-f',
               '{"peak_rss_kib":%M,"user_seconds":%U,"system_seconds":%S}',*command]
        process=subprocess.Popen(timed,stdout=events,stderr=diagnostics,env=environment(),start_new_session=True)
        try: return process.wait(timeout=timeout),False
        except subprocess.TimeoutExpired:
            os.killpg(process.pid,signal.SIGTERM)
            try: process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid,signal.SIGKILL); process.wait()
            return process.returncode,True


def run_one(task, engine, track, repetition, broker, directory, args):
    run_id=f'{task["id"]}-{track}-{engine}-{repetition}-{uuid.uuid4().hex[:8]}'
    output=directory/run_id; output.mkdir(mode=0o700)
    workspace=output/'workspace'
    shutil.copytree(CORPUS/task['fixture'],workspace)
    sessions=output/'sessions'; sessions.mkdir()
    task_text=(workspace/task.get('task_file','README.md')).read_text()
    endpoint=broker.add_run(run_id,args.max_attempts,args.context_bytes+24000)
    config={'model':args.model,'workspace':'/workspace','instructions':INSTRUCTIONS,'commands':'allow',
        'maxModelAttempts':args.max_attempts,'maxToolCalls':args.max_tools,'maxContextBytes':args.context_bytes,
        'maxOutputTokens':4096,'maxRetries':0,'operationTimeoutMs':90000,'maxElapsedMs':args.timeout*1000,
        'maxToolOutputBytes':16384,'testEndpoint':endpoint,'compactionEnabled':track=='product',
        'compactAtPercent':args.compact_at_percent,'compactionKeepMessages':args.keep_messages,
        'maxSummaryBytes':args.summary_bytes}
    (output/'config.json').write_text(json.dumps(config,indent=2)+'\n')
    pi_config={**config,'task':task_text,'track':track}
    (output/'pi-config.json').write_text(json.dumps(pi_config,indent=2)+'\n')
    binary=ROOT/'.lake/build/bin/harness'
    mounts=[(sessions,'/sessions',True),(binary,'/app/harness',False),
        (ROOT/'.lake/build/bin/eval_tools','/app/eval_tools',False),(output/'config.json','/config.json',False),
        (output/'pi-config.json','/pi-config.json',False),(ROOT/'eval/baseline','/baseline',False),
        (directory/'schemas.json','/schemas.json',False)]
    record={'run_id':run_id,'task_id':task['id'],'split':task['split'],'engine':engine,'track':track,
            'repetition':repetition,'model':args.model,'started':time.time(),'success':False}
    started=time.monotonic()
    try:
        baseline=checker(task,workspace,output,'baseline-check')
        record['baseline']=baseline
        if baseline.get('infrastructure_error') or baseline.get('passed'):
            record['infrastructure_error']='invalid task baseline'; return record
        record['setup_seconds']=round(time.monotonic()-started,3)
        started=time.monotonic()
        if engine=='lean':
            command=sandbox(workspace,mounts)+['/app/harness','run','--workspace','/workspace','--config','/config.json',
                '--task',task_text,'--session','/sessions/session','--json']
            if args.yield_after: command += ['--yield-after',str(args.yield_after)]
        else:
            command=sandbox(workspace,mounts)+['/opt/node/bin/node','/baseline/run.mjs','/pi-config.json']
        code,timed_out=run_process(command,output,args.timeout+15)
        checkpoints=[]
        while engine=='lean' and code==75 and not timed_out and len(checkpoints)<32:
            inspection=subprocess.run(sandbox(workspace,mounts)+['/app/harness','inspect','/sessions/session'],
                capture_output=True,text=True,env=environment(),timeout=30)
            if inspection.returncode: raise RuntimeError('suspended session failed inspection')
            saved=json.loads(inspection.stdout)
            if saved['pending']: raise RuntimeError('yield left an unresolved operation')
            state=saved['state']
            checkpoints.append({k:state[k] for k in ['modelAttempts','toolDispatches','nextId']})
            remaining=args.timeout-(time.monotonic()-started)
            if remaining<=0: timed_out=True; break
            command=sandbox(workspace,mounts)+['/app/harness','resume','/sessions/session','--json',
                '--yield-after',str(args.yield_after)]
            code,timed_out=run_process(command,output,remaining)
        record['durable_checkpoints']=checkpoints
        record.update(exit_code=code,timed_out=timed_out,elapsed_seconds=round(time.monotonic()-started,3))
        final=checker(task,workspace,output,'final-check')
        record['checker']=final
        record['checker_passed']=bool(final.get('passed')) and not final.get('infrastructure_error')
        if final.get('infrastructure_error'): record['infrastructure_error']=final['infrastructure_error']
        record['success']=code==0 and not timed_out and final.get('passed',False) and not final.get('infrastructure_error')
        if engine=='lean':
            inspected=subprocess.run(sandbox(workspace,mounts)+['/app/harness','inspect','/sessions/session'],
                capture_output=True,text=True,env=environment(),timeout=30)
            if inspected.returncode==0:
                state=json.loads(inspected.stdout)['state']
                (output/'inspection.json').write_text(inspected.stdout)
                record.update(tool_dispatches=state['toolDispatches'],model_attempts=state['modelAttempts'],
                    summaries=len(state.get('summaries',[])),unknown_usage=state['unknownUsage'])
                replayed=subprocess.run(sandbox(workspace,mounts)+['/app/harness','replay','/sessions/session'],
                    capture_output=True,text=True,env=environment(),timeout=30)
                record['replay_matches']=replayed.returncode==0 and json.loads(replayed.stdout)['state']==state
                record['counters_monotonic']=all(a[k]<=b[k] for a,b in zip(checkpoints,checkpoints[1:]+[state])
                    for k in ['modelAttempts','toolDispatches','nextId'])
                if args.yield_after:
                    record['sustained_gate']=record['success'] and bool(checkpoints) and record['summaries']>0 and record['replay_matches'] and record['counters_monotonic']
            else: record['inspection_failed']=True; record['success']=False
        else:
            final_events=[json.loads(line) for line in (output/'events.jsonl').read_text().splitlines() if line.startswith('{')]
            ends=[e for e in final_events if e.get('type')=='evaluation_end']
            record['tool_dispatches']=ends[-1]['toolDispatches'] if ends else None
    except Exception as error:
        record['infrastructure_error']=type(error).__name__+': '+str(error)
        record['success']=False
    finally:
        try:
            broker.close_run(run_id)
        except TimeoutError:
            record['infrastructure_error']='provider accounting did not settle'
            record['success']=False
        records=[r for r in broker.records if r['run_id']==run_id]
        record['provider_attempts']=len(records)
        record['accounted_usd']=sum(r['charged_usd'] for r in records)
        record['unknown_usage_requests']=sum(r['usage'] is None for r in records)
        resource_file=output/'resources.jsonl'
        if resource_file.exists():
            measurements=[json.loads(line) for line in resource_file.read_text().splitlines() if line.startswith('{')]
            record['max_process_rss_kib']=max((r['peak_rss_kib'] for r in measurements),default=None)
        record['human_interventions']=0
        (output/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    return record


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--key-file',required=True)
    parser.add_argument('--output',required=True)
    parser.add_argument('--budget',type=float,default=150)
    parser.add_argument('--model',default='claude-opus-5-5')
    parser.add_argument('--repetitions',type=int,default=2)
    parser.add_argument('--tracks',nargs='+',choices=['controlled','product'],default=['controlled','product'])
    parser.add_argument('--engines',nargs='+',choices=['lean','pi'],default=['lean','pi'])
    parser.add_argument('--tasks',nargs='*')
    parser.add_argument('--max-attempts',type=int,default=12)
    parser.add_argument('--max-tools',type=int,default=40)
    parser.add_argument('--context-bytes',type=int,default=120000)
    parser.add_argument('--timeout',type=int,default=300)
    parser.add_argument('--concurrency',type=int,choices=[1,2],default=2)
    parser.add_argument('--compact-at-percent',type=int,default=75)
    parser.add_argument('--keep-messages',type=int,default=4)
    parser.add_argument('--summary-bytes',type=int,default=12000)
    parser.add_argument('--yield-after',type=int,default=0)
    args=parser.parse_args()
    directory=Path(args.output).resolve(); directory.mkdir(mode=0o700,parents=True,exist_ok=False)
    manifest=json.loads((CORPUS/'manifest.json').read_text())
    tasks=[t for t in manifest['tasks'] if not args.tasks or t['id'] in args.tasks]
    if not tasks: raise ValueError('no tasks selected')
    schemas=subprocess.check_output([str(ROOT/'.lake/build/bin/eval_tools'),'schemas'])
    (directory/'schemas.json').write_bytes(schemas)
    plan={'model':args.model,'tasks':[t['id'] for t in tasks],'repetitions':args.repetitions,'tracks':args.tracks,
        'engines':args.engines,'budget_usd':args.budget,'max_attempts':args.max_attempts,'max_tools':args.max_tools,
        'timeout_seconds':args.timeout,'context_bytes':args.context_bytes,'instructions':INSTRUCTIONS,
        'compact_at_percent':args.compact_at_percent,'keep_messages':args.keep_messages,
        'summary_bytes':args.summary_bytes,'yield_after':args.yield_after,
        'binary_sha256':sha(ROOT/'.lake/build/bin/harness'),'tool_binary_sha256':sha(ROOT/'.lake/build/bin/eval_tools'),
        'manifest_sha256':sha(CORPUS/'manifest.json'),'pi_lock_sha256':sha(ROOT/'eval/baseline/package-lock.json'),
        'pi_version':'1.5.0','created':time.time(), 'regression_margin_percentage_points':10,
        'minimum_reserved_tasks_for_parity_claim':30,
        'evaluation_sources_sha256':{str(p.relative_to(ROOT)):sha(p) for p in
            [ROOT/'eval/runner/suite.py',ROOT/'eval/runner/broker.py',ROOT/'eval/baseline/run.mjs',CORPUS/'check.py']},
        'analysis':'Report raw counts by split/track. Paired differences bootstrap whole tasks, seed 20261109; repeated runs are not independent tasks. No parity claim unless the lower 95% bound exceeds -10 percentage points on reserved tasks.'}
    (directory/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    key=Path(args.key_file).expanduser().read_text().strip()
    records=[]
    with Broker(key,directory,args.budget,args.model) as broker, concurrent.futures.ThreadPoolExecutor(max_workers=args.concurrency) as pool:
        for repetition in range(args.repetitions):
            for track in args.tracks:
                for index,task in enumerate(tasks):
                    engines=args.engines if (index+repetition)%2==0 else list(reversed(args.engines))
                    futures=[pool.submit(run_one,task,engine,track,repetition,broker,directory,args) for engine in engines]
                    for future in futures:
                        result=future.result()
                        records.append(result)
                        (directory/'results.json').write_text(json.dumps(records,indent=2)+'\n')
                        print(json.dumps({k:result.get(k) for k in ['task_id','engine','track','repetition','success','provider_attempts','accounted_usd','infrastructure_error']}),flush=True)
                    if broker.total>=args.budget-2:
                        executed={(r['task_id'],r['track'],r['engine'],r['repetition']) for r in records}
                        unexecuted=[{'task_id':t['id'],'track':tr,'engine':en,'repetition':rep}
                            for rep in range(args.repetitions) for tr in args.tracks for t in tasks for en in args.engines
                            if (t['id'],tr,en,rep) not in executed]
                        (directory/'unexecuted.json').write_text(json.dumps(unexecuted,indent=2)+'\n')
                        print('Budget margin reached; remaining runs are explicitly unexecuted.',flush=True)
                        return 2
    return 0


if __name__=='__main__':
    sys.exit(main())
