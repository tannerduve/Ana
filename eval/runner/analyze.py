#!/usr/bin/env python3
"""Aggregate all scheduled outcomes; resample tasks, not repeated trials."""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import random
import statistics


def analyze(directory):
    plan=json.loads((directory/'plan.json').read_text())
    records=json.loads((directory/'results.json').read_text())
    ledger=json.loads((directory/'broker.json').read_text())
    groups=defaultdict(list)
    for record in records:
        groups[(record['split'],record['track'],record['engine'])].append(record)
    rows=[]
    for (split,track,engine),runs in sorted(groups.items()):
        succeeded=sum(bool(r.get('success')) and not r.get('infrastructure_error') for r in runs)
        spend=sum(r['charged_usd'] for r in ledger['records'] if r['run_id'] in {v['run_id'] for v in runs})
        rows.append({'split':split,'track':track,'engine':engine,'successes':succeeded,'runs':len(runs),
            'tasks':len({r['task_id'] for r in runs}),'infrastructure_failures':sum(bool(r.get('infrastructure_error')) for r in runs),
            'timeouts':sum(bool(r.get('timed_out')) for r in runs),
            'provider_attempts':sum(r.get('provider_attempts',0) for r in runs),
            'unknown_usage_requests':sum(r.get('unknown_usage_requests',0) for r in runs),
            'accounted_usd':spend,'cost_per_success_usd':spend/succeeded if succeeded else None,
            'median_seconds':statistics.median([r['elapsed_seconds'] for r in runs if 'elapsed_seconds' in r]) if any('elapsed_seconds' in r for r in runs) else None,
            'max_process_rss_kib':max((r.get('max_process_rss_kib') or 0 for r in runs),default=None),
            'memory_metric':'GNU time outside bubblewrap measures the supervisor on this host; agent memory is unavailable and these values must not be compared as agent RSS',
            'checker_passes':sum(bool(r.get('checker_passed')) for r in runs)})
    comparisons=[]
    for split in ['development','reserved']:
        for track in plan['tracks']:
            by_task=defaultdict(lambda:defaultdict(list))
            for r in records:
                if (r['split'],r['track'])==(split,track):
                    by_task[r['task_id']][r['engine']].append(int(bool(r.get('success')) and not r.get('infrastructure_error')))
            differences=[statistics.mean(v['lean'])-statistics.mean(v['pi']) for v in by_task.values() if v['lean'] and v['pi']]
            if not differences: continue
            rng=random.Random(20261109)
            samples=sorted(statistics.mean(rng.choices(differences,k=len(differences))) for _ in range(20000))
            comparisons.append({'split':split,'track':track,'paired_tasks':len(differences),
                'lean_minus_pi_percentage_points':100*statistics.mean(differences),
                'task_bootstrap_95_percent_interval':[100*samples[500],100*samples[19499]],
                'interpretation':'Descriptive pilot only; the reserved sample is below the prespecified 30-task minimum. Bootstrap intervals can collapse when every observed task has the same outcome.'})
    expected=len(plan['tasks'])*len(plan['tracks'])*len(plan['engines'])*plan['repetitions']
    return {'plan':plan,'groups':rows,'paired_comparisons':comparisons,'scheduled_runs':expected,
        'recorded_runs':len(records),'unexecuted_runs':expected-len(records),'ledger_accounted_usd':ledger['accounted_usd'],
        'records':records,'claim':'Development evidence; no general reliability or parity claim.'}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('directory',type=Path); parser.add_argument('--output',type=Path)
    args=parser.parse_args(); result=analyze(args.directory)
    if args.output: args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['records','plan']},indent=2))
