#!/usr/bin/env python3
"""JSON resource admission through the actual provider and Runner.
Hostile numeric fixtures stay small enough to parse safely if admission regresses.
Each Linux child also receives CPU/address-space limits and a wall-clock timeout.
The separate original billion-exponent reproduction used a Docker memory cgroup.
"""
import http.server
import json
import os
from pathlib import Path
import subprocess
import threading
import tempfile
import unittest
from provider_streaming import event, header, terminal

ROOT=Path(__file__).resolve().parents[1]
BINARY=ROOT/'.lake/build/bin/runtime_contracts'

def stream_tools(arguments, stop='tool_use'):
    result=header()
    for index,parts in enumerate(arguments):
        result+=event('content_block_start',index=index,
                      content_block={'type':'tool_use','id':f'call-{index}','name':'read','input':{}})
        for part in parts:
            result+=event('content_block_delta',index=index,
                          delta={'type':'input_json_delta','partial_json':part})
        result+=event('content_block_stop',index=index)
    return result+terminal(stop)

class JsonBounds(unittest.TestCase):
    def request(self, stream, runner=False):
        class Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self,*_):pass
            def do_POST(self):
                self.rfile.read(int(self.headers['Content-Length']))
                self.send_response(200);self.send_header('Content-Type','text/event-stream')
                self.send_header('Content-Length',str(len(stream)));self.end_headers()
                try:self.wfile.write(stream)
                except (BrokenPipeError,ConnectionResetError):pass
        server=http.server.ThreadingHTTPServer(('127.0.0.1',0),Handler)
        threading.Thread(target=server.serve_forever,daemon=True).start()
        temporary=tempfile.TemporaryDirectory(prefix='harness-json-runner-')
        self.addCleanup(temporary.cleanup)
        directory=Path(temporary.name)
        workspace=directory/'workspace';workspace.mkdir()
        sessions=directory/'sessions';sessions.mkdir()
        config=directory/'config.json'
        config.write_text(json.dumps({'model':'fixture','commands':'allow',
            'testEndpoint':f'http://127.0.0.1:{server.server_port}/messages',
            'operationTimeoutMs':1000,'maxResponseBytes':2000000,'maxModelAttempts':1}))
        binary=ROOT/'.lake/build/bin/harness' if runner else BINARY
        # Lean reserves large virtual regions at startup. This is a virtual
        # address limit, not a claim that the process consumes 1536 MiB of RAM.
        command=['/usr/bin/prlimit','--as=1610612736','--cpu=2:2','--core=0:0','--',str(binary)]
        if runner:command+=['run','--workspace',str(workspace),'--session',str(sessions/'session'),
                            '--config',str(config),'--task','inspect repository','--json']
        env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','LEAN_NUM_THREADS':'1',
             'LEAN_STACK_SIZE_KB':'8192','MIMALLOC_ARENA_RESERVE':'32768'}
        request={'op':'modelStream','endpoint':f'http://127.0.0.1:{server.server_port}/messages',
                 'timeoutMs':1000,'responseBytes':2000000}
        try:
            result=subprocess.run(command,input=json.dumps(request)+'\n',text=True,
                                  capture_output=True,timeout=8,env=env)
            self.assertEqual(result.returncode,1 if runner else 0,result.stderr[:1000])
            if runner:
                self.assertFalse((workspace/'effect').exists())
                records=[json.loads(line)['record'] for line in (sessions/'session/journal.jsonl').read_text().splitlines()]
                self.assertEqual(sum(row['kind']=='intent' and row['action']['kind']=='model' for row in records),1)
                self.assertFalse(any(row['kind']=='intent' and row['action']['kind']=='tool' for row in records))
                self.assertEqual(records[-1]['kind'],'terminal')
                return [row['observation'] for row in records if row['kind']=='completion'][-1]
            return json.loads(result.stdout)['observation']
        finally:
            server.shutdown();server.server_close()

    def malformed(self, stream, message):
        observation=self.request(stream)
        self.assertIn('failure',observation)
        self.assertEqual(observation['failure']['kind'],'malformed')
        self.assertIn(message,observation['failure']['message'])

    def test_streamed_argument_limits_and_split_exponent(self):
        for arguments,message in [(['{"path":"x","startLine":1e','50000}'],'exponent'),
                                  (['{"value":1e-50000}'],'exponent'),
                                  (['{"value":'+'1'*4097+'}'],'4096 digits'),
                                  (['{"value":'+'['*128+'0'+']'*128+'}'],'128 containers')]:
            with self.subTest(message=message):
                self.malformed(stream_tools([arguments]),message)

    def test_runner_discards_entire_batch_before_effects(self):
        stream=stream_tools([['{"argv":["/bin/sh","-c","printf effect > effect"]}'],
                             ['{"path":"x","startLine":1e50000}']])
        stream=stream.replace(b'"name": "read"',b'"name": "process"',1)
        observation=self.request(stream,runner=True)
        self.assertEqual(observation['failure']['kind'],'malformed')
        self.assertIn('exponent',observation['failure']['message'])

    def test_outer_event_numeric_limit(self):
        self.malformed(b'event: ping\ndata: {"type":"ping","ignored":1e50000}\n\n','exponent')

    def test_shared_outer_event_budget(self):
        values=','.join(['1e4096']*128)
        ping=('event: ping\ndata: {"type":"ping","ignored":['+values+']}\n\n').encode()
        self.malformed(ping+ping,'cumulative numeric work')

    def test_shared_inner_argument_budget(self):
        arguments='{"ignored":['+','.join(['1e4096']*128)+']}'
        self.malformed(stream_tools([[arguments],[arguments]]),'cumulative numeric work')

    def test_resource_refusal_does_not_parse_truncated_arguments(self):
        self.malformed(stream_tools([['{"value":0e50000}']], 'max_tokens'),'exponent')

    def test_ordinary_text_keeps_literal_and_escaped_quotes(self):
        text='1e1000000000 '+'['*200+' \\" quoted " 🦀'
        stream=(header()+event('content_block_start',index=0,content_block={'type':'text','text':text})
                +event('content_block_stop',index=0)+terminal())
        response=self.request(stream)
        self.assertEqual(response['success']['response']['text'],text)

if __name__=='__main__':unittest.main()
