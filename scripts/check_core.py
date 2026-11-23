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


PURE_APPLICATION_MODULES = {
    'Harness.Applications.Coding.Schemas',
    'Harness.Applications.InventoryData',
    'Harness.Applications.InventoryValidity',
    'Harness.Applications.Inventory',
    'Harness.Applications.Matrix',
}
pure_application_paths = [ROOT / (module.replace('.', '/') + '.lean')
                          for module in sorted(PURE_APPLICATION_MODULES)]
for path in sorted((ROOT / 'Harness/Core').glob('*.lean')) + sorted((ROOT / 'Harness/Proofs').glob('*.lean')) + sorted((ROOT / 'Harness/Theory').glob('*.lean')) + pure_application_paths:
    text = code_only(path.read_text())
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|opaque|partial|implemented_by|extern|noncomputable)\b', text), path
    for module in re.findall(r'^import\s+([\w.]+)', text, re.M):
        if path.parent.name == 'Theory':
            allowed_import = module.startswith(('Harness.Theory.', 'Mathlib.', 'Init.', 'Std.')) or module in {'Init', 'Std', 'Lean.Elab.Tactic.Omega'}
        else:
            allowed_import = module == 'Lean' or module.startswith(('Harness.Core.', 'Mathlib.', 'Std')) or module in PURE_APPLICATION_MODULES
            if path.parent.name == 'Proofs':
                allowed_import |= module.startswith(('Harness.Proofs.', 'Harness.Theory.'))
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
         'Harness.admitted_summary_reservation', 'Harness.admitted_task_context',
         'Harness.task_request_preserves_instructions', 'Harness.summary_request_preserves_instructions',
         'Harness.Recovery.replay_deterministic']
names += ['Harness.validated_batch_ids', 'Harness.reachable_calls', 'Harness.emitted_task_history_valid', 'Harness.no_duplicate_tool_dispatch', 'Harness.accepted_assistant_has_no_results', 'Harness.reachable_result_correlation', 'Harness.emitted_summary_history_valid', 'Harness.execution_rank_decreases', 'Harness.initialized_reply_bound', 'Harness.no_infinite_replies', 'Harness.exhausted_rank_finishes', 'Harness.execution_tool_has_trusted_approval', 'Harness.next_dispatch_needs_fresh_approval', 'Harness.lost_approval_needs_new_approval', 'Harness.lost_control_needs_new_approval', 'Harness.registerArtifacts_contract', 'Harness.reachable_artifacts_valid', 'Harness.ExecutionTrace.artifacts_monotone', 'Harness.emitted_artifact_read_registered', 'Harness.recovery_target_retains_artifacts', 'Harness.core_valid_init', 'Harness.core_valid_step', 'Harness.Recovery.recover_control_lost', 'Harness.Recovery.recover_approval_lost', 'Harness.Recovery.lost_task_response_accounted', 'Harness.Recovery.lost_summary_response_preserves_context', 'Harness.Recovery.cancelled_cursor_has_no_target', 'Harness.Recovery.completed_suspended_source', 'Harness.Recovery.ordinary_prefix_corresponds', 'Harness.Recovery.ordinary_replay_reachable', 'Harness.Recovery.recorded_execution_replays']
names += ['Harness.noncontrol_reservations', 'Harness.Recovery.resolve_continuation', 'Harness.Recovery.recover_tool_continuation', 'Harness.Recovery.resolution_preserves_pending_order', 'Harness.Recovery.recovery_tool_preserves_pending_order', 'Harness.Recovery.checked_target_core_valid', 'Harness.Recovery.complete_core_valid', 'Harness.Recovery.recover_core_valid', 'Harness.Recovery.resolve_core_valid', 'Harness.Recovery.apply_record_core_valid', 'Harness.Recovery.replay_core_valid', 'Harness.Recovery.checked_target_current_reservations', 'Harness.Recovery.resolution_preserves_current_reservations', 'Harness.Recovery.recovery_preserves_current_reservations']
names += ['Harness.ExceptSuccess.bind_iff', 'Harness.ExceptSuccess.foldlM_preserves',
          'Harness.validated_batch_length', 'Harness.Reachable.invariant',
          'PFunctor.Coalgebra.invariant', 'PFunctor.Coalgebra.Trace.append',
          'PFunctor.Coalgebra.Trace.to_reflTransGen', 'PFunctor.Coalgebra.Trace.invariant',
          'PFunctor.Coalgebra.Trace.accumulate', 'PFunctor.Coalgebra.Trace.rank_bound',
          'PFunctor.Coalgebra.no_infinite_replies']
names += ['Harness.validated_batch_all', 'Harness.Recovery.checked_target_property',
          'Harness.Recovery.apply_record_property', 'Harness.Recovery.replay_property',
          'Harness.raw_prefix_preserved', 'Harness.reachable_raw_prefix', 'Harness.replay_raw_prefix',
          'Harness.decode_operation_artifact_bounds', 'Harness.artifact_bounds_preserved',
          'Harness.reachable_artifact_bounds', 'Harness.emitted_artifact_read_bounded',
          'Harness.replay_artifact_read_bounded']
names += ['Harness.Recovery.accepted_intent_frame', 'Harness.Recovery.accepted_terminal_frame', 'Harness.Recovery.accepted_completion_frame', 'Harness.Recovery.accepted_record_kind_known', 'Harness.Recovery.ApprovalRecord.trusted', 'Harness.Recovery.mixed_grant_source', 'Harness.Recovery.new_ask_intent_has_continuous_approval', 'Harness.Recovery.next_intent_needs_fresh_approval']
names += ['Harness.response_repair_feedback_bounded', 'Harness.repair_state_frame',
          'Harness.invalid_batch_repair_state', 'Harness.repair_next_action',
          'Harness.response_repair_count_step', 'Harness.reachable_response_repairs',
          'Harness.ExecutionTrace.responseRepairs_monotone',
          'Harness.Recovery.accepted_recovery_frame', 'Harness.Recovery.accepted_resolution_frame',
          'Harness.Recovery.checked_target_current_repair_count',
          'Harness.Recovery.recovery_preserves_current_repair_count',
          'Harness.Recovery.resolution_preserves_current_repair_count',
          'Harness.Recovery.apply_record_repairs_monotone',
          'Harness.Recovery.record_prefix_repairs_monotone']
names += ['Harness.result_step_contract', 'Harness.result_step_contract_all',
          'Harness.settled_tool_queue', 'Harness.timeout_ordered_errors',
          'Harness.tool_reply_queue_disposition', 'Harness.timeout_state_frame',
          'Harness.timeout_result_has_no_exit_or_hash', 'Harness.invalid_timeout_stops',
          'Harness.timeout_next_action', 'Harness.timeout_suffix_never_dispatches',
          'Harness.timeout_closes_raw_prefix', 'Harness.Recovery.timeout_reply_settled',
          'Harness.Recovery.settled_completion_has_no_target',
          'Harness.Recovery.resolve_ordinary_continuation',
          'Harness.Recovery.recover_tool_ordinary_continuation']
names += ['Harness.Inventory.reserve_stock_contract']
names += ['Harness.Matrix.laws', 'Harness.Matrix.uncertain_receipt_cannot_claim_settlement']
names += ['Harness.Coding.laws', 'Harness.Inventory.laws', 'Harness.Inventory.decoded_result_valid',
          'Harness.coding_emitted_paths_safe', 'Harness.coding_replay_emitted_paths_safe',
          'Harness.decoded_call_valid', 'Harness.reachable_application_valid',
          'Harness.replay_application_valid', 'Harness.replay_emitted_operation_valid',
          'Harness.application_observation_roundtrip', 'Harness.application_tool_reply_roundtrip',
          'Harness.emitted_tool_visible', 'Harness.emitted_success_faithful',
          'Harness.timeout_clears_unestablished_metadata', 'Harness.timeout_skips_without_dispatch',
          'Harness.cancellation_visible', 'Harness.cancelled_control_visible',
          'Harness.denied_approval_visible', 'Harness.cancelled_approval_visible',
          'Harness.denied_policy_visible']
names += ['Harness.Persistence.dispatch_has_durable_intent',
          'Harness.Persistence.committed_has_durable_completion',
          'Harness.Persistence.failed_has_no_continuation',
          'Harness.Persistence.intent_failure_stops',
          'Harness.Persistence.completion_failure_stops',
          'Harness.Persistence.commit_releases_iff',
          'Harness.Persistence.commit_failure_stops',
          'Harness.Persistence.reply_bound',
          'Harness.Journal.accept_generated', 'Harness.Journal.accept_fields',
          'Harness.Journal.accept_bookkeeping', 'Harness.Journal.validatePrefix_bookkeeping',
          'Harness.Journal.validatePrefix_last_checksum']
names += ['Harness.begin_turn_contract', 'Harness.begin_turn_preserves_authority_and_accounting',
          'Harness.begin_turn_core_valid', 'Harness.begin_turn_closed_history',
          'Harness.begin_turn_preserves_retirement', 'Harness.begin_turn_rank',
          'Harness.continued_turn_reply_bound', 'Harness.cancelled_control_settles_undispatched',
          'Harness.cancelled_approval_settles_undispatched', 'Harness.step_advances_operation_id',
          'Harness.step_preserves_turn', 'Harness.ExecutionTrace.operation_ids_unique',
          'Harness.raw_prefix_pairing', 'Harness.cancellation_closes_raw_prefix',
          'Harness.Recovery.new_turn_contract', 'Harness.Recovery.user_turn_record_replays',
          'Harness.Recovery.new_turn_property']
names += ['Harness.Recovery.apply_record_intent_floor_monotone',
          'Harness.Recovery.replay_intent_ids_strict', 'Harness.Recovery.replay_intent_ids_unique']
names += ['Harness.ordinary_tool_reply_map', 'Harness.global_tool_denied',
          'Harness.emitted_tool_global_policy_not_denied',
          'Harness.emitted_application_artifact_read_registered']
names += ['Harness.Capability.PathScope.covers_trans',
          'Harness.Capability.ResourceScope.covers_trans',
          'Harness.Capability.covers_trans',
          'Harness.Capability.permits_intersect',
          'Harness.Capability.permitsAll_intersect',
          'Harness.Capability.contained_refl',
          'Harness.Capability.contained_trans',
          'Harness.Capability.intersect_contained_left',
          'Harness.Capability.intersect_contained_right',
          'Harness.Capability.restrict_contained_parent',
          'Harness.Capability.restrict_contained_layer',
          'Harness.Capability.checkContained_sound',
          'Harness.Capability.permitsAll_nonempty',
          'Harness.Capability.permitsAll_member',
          'Harness.Capability.permitsAll_of_contained',
          'Harness.authorized_capability_contract',
          'Harness.denied_capability_not_authorized',
          'Harness.emitted_tool_capabilities',
          'Harness.emitted_tool_requires_capabilities',
          'Harness.coding_emitted_required_access',
          'Harness.inventory_emitted_required_access',
          'Harness.reachable_tool_capabilities',
          'Harness.replay_tool_capabilities',
          'Harness.authorization_under_contained_policy',
          'Harness.authorization_under_checked_policy',
          'Harness.coding_authorization_restricts',
          'Harness.inventory_authorization_restricts']
names += [f'Harness.ApplicationCapabilities.{application}_{law}'
          for application in ['coding', 'inventory']
          for law in ['demands_complete', 'demands_exact', 'demands_nonempty', 'policy_independent']]
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
reported = re.findall(r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)", result.stdout, re.M)
assert reported == names, result.stdout
print(result.stdout.strip())
print('Core import/source boundary and selected theorem axiom audit passed.')
