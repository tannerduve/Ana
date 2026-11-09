"""Contract test for the pinned Pi adapter, with a fake streaming provider."""
import http.server
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'eval/runner'))
from suite import sandbox, environment


class PiBaseline(unittest.TestCase):
    def test_both_tracks_read_through_real_tools(self):
        for track in ['controlled','product']:
            with self.subTest(track=track), tempfile.TemporaryDirectory() as temporary:
                output=Path(temporary); workspace=output/'workspace'; workspace.mkdir()
                (workspace/'README.md').write_text('fixture marker 781\n')
                sessions=output/'sessions'; sessions.mkdir()
                requests=[]
                class Provider(http.server.BaseHTTPRequestHandler):
                    def log_message(self,*_): pass
                    def do_POST(self):
                        request=json.loads(self.rfile.read(int(self.headers['Content-Length'])))
                        requests.append(request)
                        block=({'type':'tool_use','id':'read-fixture','name':'read','input':{'path':'README.md'}}
                               if len(requests)==1 else {'type':'text','text':'done'})
                        message={'id':'msg_test','type':'message','role':'assistant','model':'claude-opus-5-5',
                            'content':[],'stop_reason':None,'stop_sequence':None,'usage':{'input_tokens':10,'output_tokens':1}}
                        initial = {**block,'input':{}} if block['type']=='tool_use' else {**block,'text':''}
                        delta = ({'type':'input_json_delta','partial_json':json.dumps(block['input'])} if block['type']=='tool_use'
                                 else {'type':'text_delta','text':block['text']})
                        events=[{'type':'message_start','message':message},
                            {'type':'content_block_start','index':0,'content_block':initial},
                            {'type':'content_block_delta','index':0,'delta':delta},
                            {'type':'content_block_stop','index':0},
                            {'type':'message_delta','delta':{'stop_reason':'tool_use' if len(requests)==1 else 'end_turn','stop_sequence':None},'usage':{'output_tokens':10}},
                            {'type':'message_stop'}]
                        body=b''.join(('event: '+e['type']+'\ndata: '+json.dumps(e)+'\n\n').encode() for e in events)
                        self.send_response(200); self.send_header('Content-Type','text/event-stream')
                        self.send_header('Content-Length',str(len(body))); self.end_headers(); self.wfile.write(body)
                server=http.server.ThreadingHTTPServer(('127.0.0.1',0),Provider)
                thread=threading.Thread(target=server.serve_forever,daemon=True); thread.start()
                try:
                    config={'model':'claude-opus-5-5','workspace':'/workspace','track':track,
                        'testEndpoint':f'http://127.0.0.1:{server.server_port}/v1/messages','maxOutputTokens':4096,
                        'maxToolCalls':4,'operationTimeoutMs':10000,'maxElapsedMs':20000,
                        'maxToolOutputBytes':16384,'maxContextBytes':120000,
                        'instructions':'Read README.md then answer.','task':'Read README.md then answer.'}
                    (output/'config.json').write_text(json.dumps(config))
                    (output/'schemas.json').write_bytes(subprocess.check_output([str(ROOT/'.lake/build/bin/eval_tools'),'schemas']))
                    mounts=[(sessions,'/sessions',True),(ROOT/'eval/baseline','/baseline',False),
                        (ROOT/'.lake/build/bin/eval_tools','/app/eval_tools',False),
                        (output/'config.json','/config.json',False),(output/'schemas.json','/schemas.json',False)]
                    result=subprocess.run(sandbox(workspace,mounts)+['/opt/node/bin/node','/baseline/run.mjs','/config.json'],
                        env=environment(),capture_output=True,text=True,timeout=30)
                    self.assertEqual(result.returncode,0,result.stderr[-4000:]+result.stdout[-1000:])
                    self.assertEqual(len(requests),2)
                    self.assertIn('fixture marker 781',json.dumps(requests[1]))
                    if track=='controlled':
                        self.assertNotIn('thinking',requests[0])
                        self.assertNotIn('output_config',requests[0])
                        self.assertEqual(requests[0]['tools'],json.loads((output/'schemas.json').read_text()))
                        self.assertEqual(requests[0]['system'],config['instructions'])
                    self.assertNotIn('error',json.loads(result.stdout.splitlines()[-1]))
                finally:
                    server.shutdown(); server.server_close(); thread.join()


if __name__=='__main__': unittest.main()
