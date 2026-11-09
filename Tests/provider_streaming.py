#!/usr/bin/env python3
"""Independent loopback SSE contracts against the actual Lean/curl adapter.
Only a synthetic credential is passed; no external model requests are made.
"""
import http.server
import json
import os
from pathlib import Path
import select
import subprocess
import tempfile
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / '.lake/build/bin/runtime_contracts'


def event(kind, **data):
    return ('event: ' + kind + '\ndata: ' + json.dumps({'type': kind, **data}, ensure_ascii=False) + '\n\n').encode()


def header():
    return event('message_start', message={'type': 'message', 'role': 'assistant', 'id': 'fixture',
        'content': [], 'stop_reason': None, 'usage': {'input_tokens': 12, 'output_tokens': 0}})


def text_prefix():
    return (header() + event('content_block_start', index=0, content_block={'type': 'text', 'text': ''}) +
            event('content_block_delta', index=0, delta={'type': 'text_delta', 'text': 'λ🙂 provisional'}) +
            event('content_block_stop', index=0))


def terminal(stop='end_turn'):
    return (event('message_delta', delta={'stop_reason': stop, 'stop_sequence': None},
                  usage={'output_tokens': 8}) + event('message_stop'))


def incomplete_batch():
    """A complete mutation followed by an unfinished call in the same response."""
    return (header() + event('content_block_start', index=0,
                content_block={'type': 'tool_use', 'id': 'must-not-run', 'name': 'create', 'input': {}}) +
            event('content_block_delta', index=0, delta={'type': 'input_json_delta',
                'partial_json': '{"path":"marker.txt","content":"must not execute"}'}) +
            event('content_block_stop', index=0) +
            event('content_block_start', index=1,
                content_block={'type': 'tool_use', 'id': 'partial-call', 'name': 'read', 'input': {}}) +
            event('content_block_delta', index=1,
                delta={'type': 'input_json_delta', 'partial_json': '{"path":'}))


class Handler(http.server.BaseHTTPRequestHandler):
    def log_message(self, *_):
        pass

    def do_POST(self):
        self.server.payloads.append(json.loads(self.rfile.read(int(self.headers['Content-Length']))))
        self.server.headers_seen.append(dict(self.headers))
        status = 429 if self.path == '/http-error' else 200
        prefix = text_prefix()
        suffix = terminal()
        if self.path == '/json':
            prefix, suffix = b'{"type":"message","content":[]}', b''
        elif self.path == '/missing-stop':
            suffix = b''
        elif self.path == '/late-garbage':
            suffix += event('content_block_start', index=1, content_block={'type': 'text', 'text': 'bad'})
        elif self.path == '/missing-usage':
            suffix = event('message_delta', delta={'stop_reason': 'end_turn'}, usage={}) + event('message_stop')
        elif self.path == '/stream-error':
            suffix = event('error', error={'type': 'overloaded_error', 'message': 'fixture'})
        elif self.path == '/http-error':
            prefix, suffix = b'{"error":"rate limit"}', b''
        elif self.path == '/invalid-utf8':
            suffix = b'data: \xff\n\n'
        elif self.path == '/tool':
            prefix = (header() + event('content_block_start', index=0,
                content_block={'type': 'tool_use', 'id': 'call-1', 'name': 'read', 'input': {}}) +
                event('content_block_delta', index=0,
                    delta={'type': 'input_json_delta', 'partial_json': '{"path": "README.md"}'}) +
                event('content_block_stop', index=0))
            suffix = terminal('tool_use')
        elif self.path == '/overflow':
            prefix, suffix = b':' + b'x' * 10000 + b'\n\n', b''
        elif self.path == '/bad-json-args':
            prefix = (header() + event('content_block_start', index=0,
                content_block={'type': 'tool_use', 'id': 'call-1', 'name': 'read', 'input': {}}) +
                event('content_block_delta', index=0,
                    delta={'type': 'input_json_delta', 'partial_json': '{"path":'}) +
                event('content_block_stop', index=0))
            suffix = terminal('tool_use')
        elif self.path.startswith('/open-limit'):
            prefix, suffix = incomplete_batch(), terminal('max_tokens')
            if self.path == '/open-limit-context':
                suffix = terminal('model_context_window_exceeded')
            elif self.path == '/open-limit-missing-stop':
                suffix = suffix.removesuffix(event('message_stop'))
            elif self.path == '/open-limit-late-content':
                suffix = (suffix.removesuffix(event('message_stop')) +
                          event('content_block_stop', index=1) + event('message_stop'))
            elif self.path == '/open-limit-success':
                suffix = terminal('end_turn')
            elif self.path == '/open-limit-http-error':
                status = 500
        self.send_response(status)
        self.send_header('Content-Type', 'text/event-stream')
        missing_tail = self.path in ['/lost-tail', '/open-limit-lost-tail']
        self.send_header('Content-Length', str(len(prefix) + len(suffix) + (20 if missing_tail else 0)))
        self.end_headers()
        try:
            # Fragment every UTF-8 character and every event delimiter.
            for byte in prefix:
                self.wfile.write(bytes([byte]))
            self.wfile.flush()
            self.server.prefix_sent.set()
            if self.path in ['/pause', '/cancel', '/timeout', '/ordered-cancel']:
                if not self.server.release.wait(5) and self.path == '/ordered-cancel':
                    self.server.barrier_expired.set()
                    return
            self.wfile.write(suffix)
            self.wfile.flush()
        except (BrokenPipeError, ConnectionResetError):
            pass


class Streaming(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='harness-stream-')
        self.root = Path(self.temp.name)
        self.server = http.server.ThreadingHTTPServer(('127.0.0.1', 0), Handler)
        self.server.daemon_threads = True
        self.server.payloads, self.server.headers_seen = [], []
        self.server.prefix_sent, self.server.release = threading.Event(), threading.Event()
        self.server.barrier_expired = threading.Event()
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        self.env = {'PATH': os.defpath, 'HOME': str(self.root), 'LANG': 'C.UTF-8',
                    'ANTHROPIC_API_KEY': 'synthetic-must-not-reach-loopback'}

    def tearDown(self):
        self.server.release.set()
        self.server.shutdown()
        self.server.server_close()
        self.thread.join(2)
        self.temp.cleanup()

    def payload(self, path, **kwargs):
        return {'op': 'modelStream', 'endpoint': f'http://127.0.0.1:{self.server.server_port}{path}',
                'timeoutMs': 3000, **kwargs}

    def request(self, path='/', **kwargs):
        result = subprocess.run([BINARY], input=json.dumps(self.payload(path, **kwargs)) + '\n',
            text=True, capture_output=True, env=self.env, timeout=8, check=True)
        self.assertNotIn(self.env['ANTHROPIC_API_KEY'], result.stdout + result.stderr)
        return json.loads(result.stdout)

    def test_complete_utf8_stream_and_usage(self):
        result = self.request()
        response = result['observation']['success']['response']
        self.assertEqual(response['text'], 'λ🙂 provisional')
        self.assertEqual(response['usage']['inputTokens'], 12)
        self.assertEqual(response['usage']['outputTokens'], 8)
        self.assertTrue(self.server.payloads[0]['stream'])
        self.assertNotIn('x-api-key', {key.lower(): value for key, value in self.server.headers_seen[0].items()})

    def test_progress_precedes_terminal_and_is_not_authoritative(self):
        child = subprocess.Popen([BINARY], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 env=self.env)
        try:
            child.stdin.write((json.dumps(self.payload('/pause', emitProgress=True)) + '\n').encode())
            child.stdin.close()
            self.assertTrue(self.server.prefix_sent.wait(2))
            self.assertTrue(select.select([child.stdout], [], [], 2)[0], 'progress was buffered until completion')
            progress = json.loads(child.stdout.readline())
            self.assertEqual(progress, {'provisional': 'λ🙂 provisional'})
            self.assertIsNone(child.poll(), 'request completed without terminal event')
            self.server.release.set()
            final = json.loads(child.stdout.readline())
            self.assertIn('success', final['observation'])
            self.assertEqual(child.wait(3), 0)
        finally:
            self.server.release.set()
            if child.poll() is None:
                child.kill()
            child.wait(3)
            child.stdout.close()
            child.stderr.close()

    def test_complete_tool_arguments_only_after_terminal(self):
        result = self.request('/tool')
        self.assertEqual(result['progress'], [])
        self.assertEqual(result['observation']['success']['response']['calls'][0]['input'], {'path': 'README.md'})

    def test_open_limit_retains_usage_and_discards_the_whole_batch(self):
        for path, stop in [('/open-limit', 'maxTokens'), ('/open-limit-context', 'contextOverflow')]:
            with self.subTest(path=path):
                result = self.request(path)
                response = result['observation']['success']['response']
                self.assertEqual(response['stop'], stop)
                self.assertEqual(response['calls'], [])
                self.assertEqual(response['content'], [])
                self.assertEqual(response['text'], '')
                self.assertEqual(response['usage']['inputTokens'], 12)
                self.assertEqual(response['usage']['outputTokens'], 8)
                self.assertEqual(result['progress'], [])

    def test_open_limit_still_requires_transport_and_terminal_integrity(self):
        for path in ['/open-limit-missing-stop', '/open-limit-late-content', '/open-limit-success',
                     '/open-limit-http-error', '/open-limit-lost-tail']:
            with self.subTest(path=path):
                self.assertNotIn('success', self.request(path)['observation'])

    def test_incomplete_malformed_or_json_fallback_never_succeeds(self):
        for path in ['/missing-stop', '/late-garbage', '/invalid-utf8', '/bad-json-args', '/json', '/lost-tail', '/missing-usage']:
            with self.subTest(path=path):
                result = self.request(path)
                self.assertNotIn('success', result['observation'])

    def test_http_and_instream_errors_classified(self):
        for path, expected in [('/http-error', 'rateLimit'), ('/stream-error', 'transport')]:
            with self.subTest(path=path):
                self.assertEqual(self.request(path)['observation']['failure']['kind'], expected)

    def test_byte_limit_is_uncertain(self):
        self.assertIn('uncertain', self.request('/overflow', responseBytes=512)['observation'])

    def test_deadline_and_cancellation_never_accept_prefix(self):
        self.assertNotIn('success', self.request('/timeout', timeoutMs=150)['observation'])
        self.server.prefix_sent.clear()
        cancel = self.root / 'cancel'
        def stop():
            self.server.prefix_sent.wait(2)
            cancel.touch()
        thread = threading.Thread(target=stop)
        thread.start()
        result = self.request('/cancel', cancelPath=str(cancel))
        thread.join(3)
        self.assertIn('interrupted', result['observation'])

    def test_cancellation_consumed_before_completion_rejects_late_response(self):
        cancel = self.root / 'ordered-cancel'
        child = subprocess.Popen([BINARY], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 env=self.env, text=True)
        try:
            child.stdin.write(json.dumps(self.payload('/ordered-cancel', timeoutMs=10000, cancelPath=str(cancel))) + '\n')
            child.stdin.close()
            child.stdin = None
            self.assertTrue(self.server.prefix_sent.wait(2), 'provider did not reach the explicit response barrier')
            cancel.touch()
            # The server cannot send its terminal events until after the adapter
            # has returned. This establishes order without a timing-only sleep.
            stdout, stderr = child.communicate(timeout=3)
            self.assertEqual(child.returncode, 0, stderr)
            self.assertIn('interrupted', json.loads(stdout)['observation'])
            self.assertFalse(self.server.barrier_expired.is_set(), 'response barrier expired instead of observing cancellation')
            self.assertFalse(self.server.release.is_set())
            self.server.release.set()
            self.assertIn('interrupted', self.request(cancelPath=str(cancel))['observation'])
            self.assertEqual(len(self.server.payloads), 1, 'consumed cancellation allowed a new provider dispatch')
        finally:
            self.server.release.set()
            if child.poll() is None:
                child.kill()
            child.communicate(timeout=3)

    def test_completion_before_cancellation_stays_complete_and_blocks_next_dispatch(self):
        cancel = self.root / 'after-completion'
        completed = self.request(cancelPath=str(cancel))
        self.assertIn('success', completed['observation'])
        response = completed['observation']['success']['response']
        self.assertEqual(response['text'], 'λ🙂 provisional')
        self.assertEqual(response['usage']['outputTokens'], 8)
        # Request returns only after the validated terminal response. A later
        # cancellation cannot retroactively turn those accepted bytes partial.
        cancel.touch()
        next_result = self.request(cancelPath=str(cancel))
        self.assertIn('interrupted', next_result['observation'])
        self.assertEqual(len(self.server.payloads), 1, 'later cancellation did not stop subsequent admission')
        self.assertIn('success', completed['observation'])


if __name__ == '__main__':
    unittest.main()
