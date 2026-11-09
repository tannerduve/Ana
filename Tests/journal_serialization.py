"""Lossless JSON admission against actual journal IO and a loopback model response."""
import http.server
import json
import os
from pathlib import Path
import subprocess
import tempfile
import threading
import unittest

from provider_streaming import event, header, terminal

ROOT = Path(__file__).resolve().parents[1]
RUNTIME = ROOT / '.lake/build/bin/runtime_contracts'
BINARY = ROOT / '.lake/build/bin/harness'


def invoke(payload):
    result = subprocess.run([str(RUNTIME)], input=payload+'\n', text=True,
                            capture_output=True, check=True, timeout=15)
    return json.loads(result.stdout)


class Serialization(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='harness-json-roundtrip-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.journal = self.root / 'journal.jsonl'

    def append(self, record):
        return invoke('{"op":"journalAppend","path":'+json.dumps(str(self.journal))+
                      ',"record":'+record+'}')

    def test_refusal_preserves_exact_completed_prefix(self):
        self.assertEqual(self.append('{"completed":"unchanged"}')['status'], 'ok')
        before = self.journal.read_bytes()
        for token in ['0e-20', '0.00000000000', '1.0', '1.2300', '-0.0']:
            with self.subTest(token=token):
                outcome = self.append('{"number":'+token+'}')
                self.assertEqual(outcome['status'], 'failed')
                self.assertIn('journal value cannot be serialized losslessly', outcome['text'])
                self.assertEqual(self.journal.read_bytes(), before)
                loaded = invoke(json.dumps({'op':'journalRead','path':str(self.journal)}))
                self.assertEqual(loaded['status'], 'ok')
                self.assertEqual(loaded['records'], [{'completed':'unchanged'}])
                self.assertFalse(loaded['interrupted'])

    def test_canonical_values_and_control_strings_roundtrip(self):
        controls = ''.join(map(chr,range(32)))+'\\t\\u0009é😀\u0085\u2028\u2029'
        for record in ['{"integer":-23}', '{"decimal":2.5}', '{"small":1e-20}',
                       json.dumps({'controls':controls},ensure_ascii=False)]:
            self.assertEqual(self.append(record)['status'], 'ok')
        loaded = invoke(json.dumps({'op':'journalRead','path':str(self.journal)}))
        self.assertEqual(loaded['status'], 'ok')
        self.assertEqual(len(loaded['records']), 4)
        self.assertEqual(loaded['records'][-1]['controls'], controls)

    def test_untrusted_journal_numbers_and_depth_are_bounded_before_checksum(self):
        for value, reason in [('1e50000', 'JSON exponent exceeds magnitude 4096'),
                              ('['*129+'0'+']'*129, 'JSON nesting exceeds 128 containers')]:
            with self.subTest(reason=reason):
                frame = ('{"v":1,"seq":0,"previous":"","record":{"number":'+value+
                         '},"checksum":"'+'0'*64+'"}\n')
                self.journal.write_text(frame)
                before = self.journal.read_bytes()
                outcome = invoke(json.dumps({'op':'journalRead','path':str(self.journal)}))
                self.assertEqual(outcome['status'], 'failed')
                self.assertIn(reason, outcome['text'])
                self.assertNotIn('invalid journal frame', outcome['text'])
                self.assertEqual(self.journal.read_bytes(), before)

    def test_nonlossless_model_reply_never_advances_or_dispatches(self):
        workspace = self.root / 'workspace'; workspace.mkdir()
        (workspace/'source').write_text('observed\n')
        session = self.root / 'session'
        journal = session/'journal.jsonl'
        calls = [('mutation', 'process', '{"argv":["/bin/sh","-c","printf dispatched >> counter"]}'),
                 ('read', 'read', '{"path":"source","startLine":1.0}')]
        stream = header()
        for index,(ident,name,arguments) in enumerate(calls):
            stream += event('content_block_start', index=index,
                            content_block={'type':'tool_use','id':ident,'name':name,'input':{}})
            stream += event('content_block_delta', index=index,
                            delta={'type':'input_json_delta','partial_json':arguments})
            stream += event('content_block_stop', index=index)
        stream += terminal('tool_use')
        final_stream = (header() + event('content_block_start', index=0,
            content_block={'type':'text','text':''}) + event('content_block_delta', index=0,
            delta={'type':'text_delta','text':'recovered without running the discarded calls'}) +
            event('content_block_stop', index=0) + terminal())
        class Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self,*_):pass
            def do_POST(self):
                self.rfile.read(int(self.headers['Content-Length']))
                self.server.requests += 1
                self.server.prefix = journal.read_bytes()
                body = stream if self.server.requests == 1 else final_stream
                self.send_response(200);self.send_header('Content-Type','text/event-stream')
                self.send_header('Content-Length',str(len(body)));self.end_headers()
                self.wfile.write(body)
        server = http.server.ThreadingHTTPServer(('127.0.0.1',0),Handler)
        server.requests = 0; server.prefix = None
        thread = threading.Thread(target=server.serve_forever,daemon=True);thread.start()
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        config = self.root/'config.json'
        config.write_text(json.dumps({'model':'loopback','commands':'allow',
             'testEndpoint':f'http://127.0.0.1:{server.server_port}/messages'}))
        env = {key:value for key,value in os.environ.items() if key != 'ANTHROPIC_API_KEY'}
        result = subprocess.run([str(BINARY),'run','--workspace',str(workspace),'--session',str(session),
            '--config',str(config),'--task','inspect and change source','--json'],
            text=True,capture_output=True,env=env,timeout=20)
        self.assertEqual(result.returncode, 2, result.stdout+result.stderr)
        self.assertIn('journal value cannot be serialized losslessly', result.stderr+result.stdout)
        self.assertEqual(server.requests,1)
        self.assertEqual(journal.read_bytes(),server.prefix)
        self.assertFalse((workspace/'counter').exists())
        events = [json.loads(line) for line in result.stdout.split('\n') if line]
        self.assertFalse(any(row.get('event')=='intent' and row.get('data',{}).get('kind')=='tool'
                             for row in events))
        snapshots=[]
        for command in ['inspect','replay']:
            replay=subprocess.run([str(BINARY),command,str(session)],text=True,capture_output=True,
                                  check=True,timeout=15)
            snapshots.append(json.loads(replay.stdout))
        self.assertEqual(*snapshots)
        state=snapshots[0]
        self.assertTrue(state['pending']);self.assertFalse(state['terminal'])
        self.assertEqual(state['state']['modelAttempts'],1)
        self.assertEqual(state['state']['toolDispatches'],0)
        self.assertEqual(len(state['state']['history']),1)
        self.assertEqual(journal.read_bytes(),server.prefix)
        resumed = subprocess.run([str(BINARY),'resume',str(session)],text=True,capture_output=True,
                                 env=env,timeout=20)
        self.assertEqual(resumed.returncode,0,resumed.stdout+resumed.stderr)
        self.assertEqual(server.requests,2)
        self.assertFalse((workspace/'counter').exists())
        completed = subprocess.run([str(BINARY),'inspect',str(session)],text=True,capture_output=True,
                                   check=True,timeout=15)
        settled = json.loads(completed.stdout)
        self.assertTrue(settled['terminal']);self.assertFalse(settled['pending'])
        self.assertEqual(settled['state']['modelAttempts'],2)
        self.assertEqual(settled['state']['unknownUsage'],1)
        self.assertEqual(settled['state']['toolDispatches'],0)
        records = [json.loads(line)['record'] for line in journal.read_text().split('\n') if line]
        self.assertFalse(any(record.get('kind')=='intent' and record['action']['kind']=='tool'
                             for record in records))

if __name__=='__main__':unittest.main()
