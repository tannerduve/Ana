"""Independent tests of evaluation accounting and request admission."""
import http.server
import json
from pathlib import Path
import sys
import tempfile
import threading
import unittest
import urllib.error
import urllib.request

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'eval/runner'))
from broker import Broker, response_usage, usage_cost


class Evaluation(unittest.TestCase):
    def test_stream_usage_requires_terminal_event(self):
        start=b'data: {"type":"message_start","message":{"usage":{"input_tokens":10,"output_tokens":0}}}\n\n'
        delta=b'data: {"type":"message_delta","usage":{"output_tokens":20}}\n\n'
        self.assertIsNone(response_usage(start+delta,True))
        self.assertEqual(response_usage(start+delta+b'data: {"type":"message_stop"}\n',True),
                         {'input_tokens':10,'output_tokens':20})

    def test_cache_usage_is_not_zero(self):
        self.assertAlmostEqual(usage_cost({'input_tokens':10,'output_tokens':20,
            'cache_read_input_tokens':100,'cache_creation_input_tokens':100}),0.00096)
        self.assertIsNone(usage_cost(None))
        self.assertIsNone(usage_cost({'input_tokens':10}))

    def test_no_hidden_retry_and_enforced_admission(self):
        calls=[]
        class Upstream(http.server.BaseHTTPRequestHandler):
            def log_message(self,*_): pass
            def do_POST(self):
                calls.append(json.loads(self.rfile.read(int(self.headers['Content-Length']))))
                body=json.dumps({'usage':{'input_tokens':10,'output_tokens':20}}).encode()
                self.send_response(200); self.send_header('Content-Length',str(len(body)))
                self.end_headers(); self.wfile.write(body)
        server=http.server.ThreadingHTTPServer(('127.0.0.1',0),Upstream)
        thread=threading.Thread(target=server.serve_forever,daemon=True); thread.start()
        try:
            with tempfile.TemporaryDirectory() as temporary:
                with Broker('test-secret',temporary,5,upstream=f'http://127.0.0.1:{server.server_port}') as broker:
                    endpoint=broker.add_run('one',1)
                    def request(**changes):
                        data={'model':'claude-opus-5-5','max_tokens':32,'messages':[],**changes}
                        return urllib.request.urlopen(urllib.request.Request(endpoint,data=json.dumps(data).encode()),timeout=3)
                    with self.assertRaises(urllib.error.HTTPError): request(model='other')
                    self.assertEqual(len(calls),0)
                    with request() as response: response.read()
                    with self.assertRaises(urllib.error.HTTPError): request()
                    self.assertEqual(len(calls),1)
                    broker.close_run('one')
                report=json.loads((Path(temporary)/'broker.json').read_text())
                self.assertEqual(len(report['records']),1)
                self.assertAlmostEqual(report['accounted_usd'],0.00044)
                self.assertNotIn('test-secret',json.dumps(report))
        finally:
            server.shutdown(); server.server_close(); thread.join()

    def test_unknown_usage_retains_reservation(self):
        class Upstream(http.server.BaseHTTPRequestHandler):
            def log_message(self,*_): pass
            def do_POST(self):
                self.rfile.read(int(self.headers['Content-Length']))
                self.send_response(503); self.end_headers(); self.wfile.write(b'{}')
        server=http.server.ThreadingHTTPServer(('127.0.0.1',0),Upstream)
        thread=threading.Thread(target=server.serve_forever,daemon=True); thread.start()
        try:
            with tempfile.TemporaryDirectory() as temporary, Broker('test-secret',temporary,5,
                    upstream=f'http://127.0.0.1:{server.server_port}') as broker:
                endpoint=broker.add_run('lost',1)
                with self.assertRaises(urllib.error.HTTPError):
                    urllib.request.urlopen(urllib.request.Request(endpoint,data=json.dumps(
                        {'model':'claude-opus-5-5','max_tokens':32}).encode()),timeout=3)
                self.assertEqual(broker.total,broker.records[0]['reserved_usd'])
                self.assertIsNone(broker.records[0]['usage'])
        finally:
            server.shutdown(); server.server_close(); thread.join()


if __name__=='__main__': unittest.main()
