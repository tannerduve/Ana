#!/usr/bin/env python3
"""Conservative source boundary check plus kernel-reported axiom allowlist.
This is a guardrail; theorem statements still require human review.
"""
import pathlib
import re
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]


def code_only(text):
    # Remove nested Lean comments, line comments, and string literals.
    result, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\': i += 2
                elif text[i] == '"': i += 1; break
                else: i += 1
            result.append(' ')
        else:
            result.append(text[i]); i += 1
    assert depth == 0, 'unclosed comment'
    return ''.join(result)


for path in sorted((ROOT / 'Harness/Core').glob('*.lean')) + sorted((ROOT / 'Harness/Proofs').glob('*.lean')):
    text = code_only(path.read_text())
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|opaque|partial|implemented_by|extern|noncomputable)\b', text), path
    for module in re.findall(r'^import\s+([\w.]+)', text, re.M):
        allowed_import = module == 'Lean' or module.startswith(('Harness.Core.', 'Mathlib.', 'Std'))
        if path.parent.name == 'Proofs':
            allowed_import |= module.startswith('Harness.Proofs.')
        assert allowed_import, (path, module)

names = ['Harness.budget_init', 'Harness.budget_preserved', 'Harness.reachable_budgets', 'Harness.emitted_tool_authorized',
         'Harness.terminal_action', 'Harness.cancellation_terminal', 'Harness.changed_grant_unusable',
         'Harness.validateModelResponse_sound', 'Harness.rejected_model_response_state',
         'Harness.inconsistent_model_response_stops', 'Harness.accepted_tool_response_contract',
         'Harness.inconsistent_model_response_terminal',
         'Harness.config_preserved', 'Harness.reachable_config',
         'Harness.summary_history_preserved', 'Harness.summary_cancel_preserves_view',
         'Harness.summary_failure_preserves_view', 'Harness.accepted_summary_contract',
         'Harness.rejected_summary_preserves_view', 'Harness.emitted_summary_admitted',
         'Harness.admitted_summary_reservation',
         'Harness.task_request_preserves_instructions', 'Harness.summary_request_preserves_instructions',
         'Harness.Recovery.replay_deterministic']
with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', dir=ROOT, delete=False) as file:
    path = pathlib.Path(file.name)
    file.write('import Harness\n' + ''.join(f'#print axioms {name}\n' for name in names))
try:
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, text=True, capture_output=True, check=True)
finally:
    path.unlink()
allowed = {'propext', 'Quot.sound', 'Classical.choice'}
for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', result.stdout):
    assert {v.strip() for v in group.split(',')} <= allowed, group
assert len(re.findall(r"'Harness\.", result.stdout)) == len(names), result.stdout
print(result.stdout.strip())
print('Core import/source boundary and selected theorem axiom audit passed.')
