#!/usr/bin/env python3
"""Actual CLI crashes around lost observations and durable recovery records.

The preload library is test-only fault injection; models are scripted and no
network credentials are needed. Independent file/open counters check effects.
"""
import json
import fcntl
import pty
import select
import termios
import time
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from integration import response

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/harness'

SHIM = r'''
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>
static int armed, crash_sync, fail_sync, matches;
static int is_journal(int fd) {
    char source[64], target[4096];
    snprintf(source,sizeof(source),"/proc/self/fd/%d",fd);
    ssize_t n=readlink(source,target,sizeof(target)-1);
    if(n<0) return 0;
    target[n]=0;
    return n>=14 && !strcmp(target+n-14,"/journal.jsonl");
}
static int has(const void *data,size_t size,const char *text) {
    return memmem(data,size,text,strlen(text))!=NULL;
}
ssize_t write(int fd,const void *data,size_t size) {
    static ssize_t (*real_write)(int,const void*,size_t);
    if(!real_write) real_write=dlsym(RTLD_NEXT,"write");
    const char *mode=getenv("OBS_FAULT");
    if(mode && is_journal(fd)) {
        if(has(data,size,"\"kind\":\"recovery\"")) {
            if(!strcmp(mode,"recovery_write_failure")) {errno=ENOSPC;return -1;}
            if(!strcmp(mode,"recovery_after_flush")) crash_sync=1;
            if(!strcmp(mode,"recovery_flush_failure")) fail_sync=1;
        }
        if(has(data,size,"\"kind\":\"intent\"")) {
            const char *kind=getenv("OBS_KIND");
            char marker[128];
            snprintf(marker,sizeof(marker),"\"kind\":\"%s\"",kind?kind:"");
            if(has(data,size,marker)) {
                const char *skip=getenv("OBS_SKIP");
                if(matches++ == (skip?atoi(skip):0)) {
                    armed=1;
                    if(!strcmp(mode,"after_intent")) crash_sync=1;
                }
            }
        }
        if(armed && has(data,size,"\"kind\":\"completion\"") && !strcmp(mode,"before_completion")) _exit(86);
    }
    return real_write(fd,data,size);
}
int fsync(int fd) {
    static int (*real_sync)(int);
    if(!real_sync) real_sync=dlsym(RTLD_NEXT,"fsync");
    if(fail_sync && is_journal(fd)) {errno=EIO;return -1;}
    int result=real_sync(fd);
    if(result==0 && crash_sync && is_journal(fd)) _exit(86);
    return result;
}
int openat(int dirfd,const char *path,int flags,...) {
    static int (*real_openat)(int,const char*,int,...);
    if(!real_openat) real_openat=dlsym(RTLD_NEXT,"openat");
    mode_t mode=0;
    if(flags & O_CREAT) {va_list args;va_start(args,flags);mode=va_arg(args,int);va_end(args);}
    int result=real_openat(dirfd,path,flags,mode);
    const char *counter=getenv("OBS_READ_COUNTER");
    if(result>=0 && counter && !strcmp(path,"observed.txt")) {
        int countfd=(int)syscall(SYS_openat,AT_FDCWD,counter,O_CREAT|O_WRONLY|O_APPEND,0600);
        if(countfd>=0) {syscall(SYS_write,countfd,"x",1);syscall(SYS_close,countfd);}
    }
    return result;
}
'''


class RecoveryObservations(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.compiler_temp = tempfile.TemporaryDirectory(prefix='harness-observation-shim-')
        source = Path(cls.compiler_temp.name) / 'fault.c'
        source.write_text(SHIM)
        cls.shim = source.with_suffix('.so')
        subprocess.run(['cc', '-shared', '-fPIC', str(source), '-o', str(cls.shim), '-ldl'], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.compiler_temp.cleanup()

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='harness-observations-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.workspace = self.root / 'workspace'
        self.workspace.mkdir()
        self.session = self.root / 'session'
        self.read_counter = self.root / 'read-counter'
        self.env = {key: os.environ[key] for key in ['PATH', 'HOME', 'LANG'] if key in os.environ}
        self.env.update(LD_PRELOAD=str(self.shim), OBS_READ_COUNTER=str(self.read_counter))

    def cli(self, args, fault=None, kind=None, skip=0, input_text='', expected=None):
        env = dict(self.env)
        if fault:
            env.update(OBS_FAULT=fault, OBS_KIND=kind or '', OBS_SKIP=str(skip))
        command = [str(BINARY), *map(str, args)]
        if input_text:
            master, slave = pty.openpty()
            def terminal():
                os.setsid()
                fcntl.ioctl(slave, termios.TIOCSCTTY, 0)
            child = subprocess.Popen(command, stdin=slave, stdout=slave, stderr=slave,
                                     env=env, preexec_fn=terminal)
            os.close(slave)
            data, sent = bytearray(), False
            deadline = time.monotonic() + 15
            try:
                while time.monotonic() < deadline:
                    if select.select([master], [], [], 0.05)[0]:
                        try:
                            chunk = os.read(master, 65536)
                        except OSError:
                            break
                        if not chunk:
                            break
                        data.extend(chunk)
                        if not sent and b'Type yes to approve: ' in data:
                            os.write(master, input_text.encode())
                            sent = True
                    if child.poll() is not None:
                        break
                if child.poll() is None:
                    child.wait(max(0.1, deadline - time.monotonic()))
                self.assertTrue(sent, data.decode(errors='replace'))
                result = subprocess.CompletedProcess(command, child.returncode, data.decode(errors='replace'), '')
            finally:
                if child.poll() is None:
                    child.kill()
                child.wait(3)
                os.close(master)
        else:
            result = subprocess.run(command, input='', text=True,
                                    capture_output=True, timeout=15, env=env)
        if expected is not None:
            self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def start(self, script=None, config=None, **kwargs):
        settings = {'model': 'scripted', 'commands': 'allow', 'maxRetries': 2,
                    'maxModelAttempts': 4, 'operationTimeoutMs': 3000, **(config or {})}
        config_path = self.root / 'config.json'
        config_path.write_text(json.dumps(settings))
        script_path = self.root / 'script.json'
        script_path.write_text(json.dumps(script or [response(text='done'), response(text='retried')]))
        return self.cli(['run', '--workspace', self.workspace, '--config', config_path,
                         '--script', script_path, '--task', 'fixture', '--session', self.session], **kwargs)

    def resume(self, **kwargs):
        return self.cli(['resume', self.session], **kwargs)

    def inspect(self):
        return json.loads(self.cli(['inspect', self.session], expected=0).stdout)

    def records(self):
        return [json.loads(line)['record'] for line in (self.session / 'journal.jsonl').read_text().splitlines()]

    def recoveries(self):
        return [record for record in self.records() if record['kind'] == 'recovery']

    def assert_terminal_replay(self):
        before = (self.session / 'journal.jsonl').read_bytes()
        state = self.inspect()
        self.resume(expected=0)
        self.assertEqual((self.session / 'journal.jsonl').read_bytes(), before)
        self.assertEqual(self.inspect(), state)
        replay = json.loads(self.cli(['replay', self.session], expected=0).stdout)
        self.assertEqual(replay, state)

    def test_lost_control_is_reobserved_with_new_id_no_budget_refund(self):
        self.start(fault='after_intent', kind='control', expected=86)
        self.assertEqual(self.inspect()['state']['modelAttempts'], 0)
        self.resume(expected=0)
        recovery = self.recoveries()
        self.assertEqual([(r['id'], r['recovery']['disposition']) for r in recovery], [(0, 'controlLost')])
        controls = [r['id'] for r in self.records() if r['kind'] == 'intent' and r['action']['kind'] == 'control']
        self.assertEqual(controls[:2], [0, 1])
        self.assertEqual(self.inspect()['state']['modelAttempts'], 1)
        self.assert_terminal_replay()

    def test_lost_model_accounts_unknown_usage_and_fresh_attempt(self):
        for fault in ['after_intent', 'before_completion']:
            with self.subTest(fault=fault):
                # Separate sessions retain both pre-dispatch and post-observation cases.
                self.session = self.root / fault
                self.start(fault=fault, kind='model', expected=86)
                before = self.inspect()['state']
                self.assertEqual(before['modelAttempts'], 1)
                self.resume(expected=0)
                state = self.inspect()['state']
                self.assertEqual((state['modelAttempts'], state['unknownUsage']), (2, 1))
                self.assertEqual((state['knownInputTokens'], state['knownOutputTokens']), (20, 10))
                self.assertEqual([r['recovery']['disposition'] for r in self.recoveries()], ['modelLost'])
                models = [r['id'] for r in self.records() if r['kind'] == 'intent' and r['action']['kind'] == 'model']
                self.assertEqual(len(set(models)), 2)
                self.assert_terminal_replay()

    def test_lost_model_cannot_refund_exhausted_attempt_budget(self):
        self.start(config={'maxModelAttempts': 1}, fault='after_intent', kind='model', expected=86)
        self.assertNotEqual(self.resume().returncode, 0)
        state = self.inspect()['state']
        self.assertEqual((state['modelAttempts'], state['unknownUsage']), (1, 1))
        self.assertEqual(sum(r['kind'] == 'intent' and r['action']['kind'] == 'model' for r in self.records()), 1)

    def test_lost_wait_restarts_delay_without_double_charging_model(self):
        self.start(fault='after_intent', kind='model', expected=86)
        self.resume(fault='after_intent', kind='wait', expected=86)
        pending = self.inspect()['state']
        self.assertEqual((pending['modelAttempts'], pending['unknownUsage']), (1, 1))
        self.resume(expected=0)
        self.assertEqual([r['recovery']['disposition'] for r in self.recoveries()], ['modelLost', 'waitLost'])
        state = self.inspect()['state']
        self.assertEqual((state['modelAttempts'], state['unknownUsage']), (2, 1))
        waits = [r['id'] for r in self.records() if r['kind'] == 'intent' and r['action']['kind'] == 'wait']
        self.assertEqual(len(set(waits)), 2)
        self.assert_terminal_replay()

    def test_lost_read_is_settled_unknown_without_reopening_file(self):
        source = self.workspace / 'observed.txt'
        source.write_text('first version')
        self.start([response([('read-once', 'read', {'path': 'observed.txt'})]), response(text='done')],
                   fault='before_completion', kind='tool', expected=86)
        self.assertEqual(self.read_counter.read_bytes(), b'x')
        source.write_text('changed externally')
        self.resume(expected=0)
        self.assertEqual(self.read_counter.read_bytes(), b'x', 'lost read was silently repeated')
        state = self.inspect()['state']
        self.assertEqual(state['toolDispatches'], 1)
        self.assertIn('Read result lost', json.dumps(state['history']))
        self.assertNotIn('changed externally', json.dumps(state['history']))
        self.assertEqual([r['recovery']['disposition'] for r in self.recoveries()], ['readLost'])
        self.assert_terminal_replay()

    def test_lost_yes_approval_requires_a_new_decision(self):
        calls = [('command', 'process', {'argv': ['/bin/sh', '-c', 'printf x >> counter']})]
        self.start([response(calls), response(text='done')], config={'commands': 'ask'},
                   fault='before_completion', kind='ask', input_text='yes\n', expected=86)
        self.assertFalse((self.workspace / 'counter').exists())
        self.assertIsNone(self.inspect()['state']['grant'])
        self.resume(input_text='no\n', expected=0)
        self.assertFalse((self.workspace / 'counter').exists())
        self.assertEqual(self.inspect()['state']['toolDispatches'], 0)
        asks = [r['id'] for r in self.records() if r['kind'] == 'intent' and r['action']['kind'] == 'ask']
        self.assertEqual(len(set(asks)), 2)
        self.assertEqual([r['recovery']['disposition'] for r in self.recoveries()], ['approvalLost'])

    def test_lost_control_invalidates_previously_durable_approval(self):
        calls = [('command', 'process', {'argv': ['/bin/sh', '-c', 'printf x >> counter']})]
        self.start([response(calls), response(text='done')], config={'commands': 'ask'},
                   fault='after_intent', kind='control', skip=2, input_text='yes\n', expected=86)
        self.assertIsNotNone(self.inspect()['state']['grant'])
        self.resume(input_text='no\n', expected=0)
        self.assertFalse((self.workspace / 'counter').exists())
        self.assertEqual(self.inspect()['state']['toolDispatches'], 0)
        self.assertEqual([r['recovery']['disposition'] for r in self.recoveries()], ['controlLost'])

    def test_uncertain_create_requires_explicit_abandonment_and_never_repeats(self):
        for fault, created in [('after_intent', False), ('before_completion', True)]:
            with self.subTest(fault=fault):
                self.session = self.root / fault
                target = self.workspace / 'created.txt'
                target.unlink(missing_ok=True)
                self.start([response([('create-once', 'create', {'path': 'created.txt', 'content': 'first'})]),
                            response(text='done')], fault=fault, kind='tool', expected=86)
                self.assertEqual(target.exists(), created)
                before = (self.session / 'journal.jsonl').read_bytes()
                self.resume(expected=2)
                self.assertEqual((self.session / 'journal.jsonl').read_bytes(), before)
                # External evidence deliberately differs from the requested postimage.
                target.write_text('operator-preserved')
                operation = self.inspect()['recoverableOperation']
                self.cli(['resolve', self.session, '--operation', operation, '--status', 'abandoned',
                          '--note', 'Operator retained external contents and declines a retry'], expected=0)
                self.resume(expected=0)
                self.assertEqual(target.read_text(), 'operator-preserved')
                self.assertEqual(self.inspect()['state']['toolDispatches'], 1)
                self.assertIn('mutationAbandoned', self.recoveries()[0]['recovery']['disposition'])
                self.assert_terminal_replay()

    def test_recovery_record_write_failure_cannot_advance_or_dispatch(self):
        self.start(fault='after_intent', kind='model', expected=86)
        before = (self.session / 'journal.jsonl').read_bytes()
        self.resume(fault='recovery_write_failure', expected=2)
        self.assertEqual((self.session / 'journal.jsonl').read_bytes(), before)
        self.assertTrue(self.inspect()['pending'])
        self.assertEqual(self.inspect()['state']['unknownUsage'], 0)
        self.resume(expected=0)
        self.assertEqual(self.inspect()['state']['unknownUsage'], 1)
        self.assertEqual(len(self.recoveries()), 1)

    def test_recovery_flush_failure_stops_before_new_dispatch(self):
        self.start(fault='after_intent', kind='model', expected=86)
        self.resume(fault='recovery_flush_failure', expected=2)
        # Bytes may be visible after failed fsync; the test does not claim they
        # survived a power loss. No later effect was dispatched in that invocation.
        self.assertEqual(sum(r['kind'] == 'intent' and r['action']['kind'] == 'model'
                             for r in self.records()), 1)
        self.assertEqual(len(self.recoveries()), 1)
        self.resume(expected=0)
        self.assertEqual(self.inspect()['state']['unknownUsage'], 1)
        self.assertEqual(len(self.recoveries()), 1)
        self.assert_terminal_replay()

    def test_durable_recovery_crash_is_replayed_once(self):
        self.start(fault='after_intent', kind='model', expected=86)
        self.resume(fault='recovery_after_flush', expected=86)
        state = self.inspect()['state']
        self.assertEqual((state['modelAttempts'], state['unknownUsage']), (1, 1))
        self.assertFalse(self.inspect()['pending'])
        self.resume(expected=0)
        self.assertEqual(self.inspect()['state']['unknownUsage'], 1)
        self.assertEqual(len(self.recoveries()), 1)
        self.assert_terminal_replay()


if __name__ == '__main__':
    unittest.main(verbosity=2)
