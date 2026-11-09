"""Compare the independent auditor with real Lean journal serialization.

Requires the product runtime_contracts executable; no Node or provider is used.
"""
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from decimal import Decimal

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'runner'))
from audit_continuation import AuditError, _loads, compact, read_lines

BINARY = Path(os.environ.get('HARNESS_RUNTIME_BINARY', str(
    Path(__file__).resolve().parents[2] / '.lake/build/bin/runtime_contracts')))
CONTROLS = ''.join(map(chr, range(32))) + '\\t\\b\\f\\u0009"\\é😀\u0085\u2028\u2029'


def append_record(path, record):
    # Keep numeric fixture spellings intact when sending them to Lean.
    request = ('{"op":"journalAppend","path":' + json.dumps(str(path)) +
               ',"record":' + record + '}\n')
    result = subprocess.run([str(BINARY)], input=request, text=True, capture_output=True,
                            check=True, timeout=10)
    return json.loads(result.stdout)


class Canonical(unittest.TestCase):
    def test_controls_and_literal_backslashes(self):
        encoded = compact(CONTROLS)
        self.assertEqual(json.loads(encoded), CONTROLS)
        self.assertIn('\\u0009', encoded)
        self.assertIn('\\\\t', encoded)
        self.assertNotIn('\\t', encoded.replace('\\\\t', ''))
        self.assertEqual(compact({'b': True, 'a': None}), '{"a":null,"b":true}')
        with self.assertRaises(AuditError):
            compact(1.5)
        with self.assertRaises(AuditError):
            compact('\ud800')

    def test_exact_numeric_expected_examples(self):
        examples = {
            '1.0': '1', '-0.0': '0', '1e20': '100000000000000000000',
            '1e-20': '0.0000000001e-10', '1.234567890123456789': '1.234567890123456789',
            '-2.5000': '-2.5', '1000.000': '1000',
        }
        for source, expected in examples.items():
            self.assertEqual(compact(_loads(source)), expected)
        with self.assertRaises(AuditError):
            compact(_loads('0e-20'))
        with self.assertRaises(AuditError):
            _loads('NaN')

    def test_expanded_integer_bound_is_exact_without_global_changes(self):
        before = sys.get_int_max_str_digits()
        token = '9' * 8192
        value = _loads(token)
        self.assertIs(type(value), int)
        self.assertEqual(compact(value), token)
        self.assertEqual(compact(_loads('-' + token)), '-' + token)
        with self.assertRaises(AuditError):
            _loads('9' * 8193)
        with self.assertRaises(AuditError):
            compact(int(Decimal('9' * 8193)))
        self.assertEqual(sys.get_int_max_str_digits(), before)

    def test_real_compiled_lean_frames(self):
        tokens = ['1', '0', '1e20', '1e-20', '-7e-90', '1.234567890123456789',
                  '1000', '3.14', '1e-10', '1e-11', '9' * 4096]
        rng = random.Random(20261109)
        generated = []
        for _ in range(120):
            whole = str(rng.choice([-1, 1]) * rng.randrange(1, 10**30))
            fraction = str(rng.randrange(10**11)).rjust(11, '0') + str(rng.randrange(1, 10))
            generated.append(whole + '.' + fraction + 'e' + str(rng.randrange(-120, 61)))
        records = [json.dumps({'controls': CONTROLS}, ensure_ascii=False)]
        records += ['{"number":' + token + '}' for token in tokens]
        records += ['{"generated":[' + ','.join(generated) + ']}']
        with tempfile.TemporaryDirectory() as temp:
            journal = Path(temp) / 'journal.jsonl'
            for record in records:
                self.assertEqual(append_record(journal, record)['status'], 'ok')
            frames = read_lines(journal)
            self.assertEqual(len(frames), len(records))
            previous = ''
            for sequence, frame in enumerate(frames):
                self.assertEqual(frame['seq'], sequence)
                self.assertEqual(frame['previous'], previous)
                base = {key: frame[key] for key in ['v', 'seq', 'previous', 'record']}
                self.assertEqual(hashlib.sha256(compact(base).encode()).hexdigest(), frame['checksum'])
                previous = frame['checksum']

    def test_unrepresentable_numeric_frames_are_refused(self):
        with tempfile.TemporaryDirectory() as temp:
            for index, token in enumerate(['0e-20', '0.00000000000', '1.0', '1.2300']):
                journal = Path(temp) / str(index)
                outcome = append_record(journal, '{"number":' + token + '}')
                self.assertEqual(outcome['status'], 'failed')
                self.assertIn('journal value cannot be serialized losslessly', outcome['text'])
                self.assertEqual(journal.read_bytes(), b'')


if __name__ == '__main__':
    unittest.main()
