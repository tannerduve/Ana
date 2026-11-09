import Harness.Core.Journal
import Harness.Proofs.Except

/-! The actual framing validator preserves sequence, hash linkage and exact byte
accounting. Hash correctness and durable-write acknowledgments remain IO contracts. -/
namespace Harness.Journal
open ExceptRules

/-- The exact header used by the writer is accepted by the reopening validator. -/
theorem accept_generated (cursor : Cursor) (checksum : String) (bytes : Nat)
    (positive : 0 < bytes) :
    accept cursor {
      header := {version := 1, sequence := cursor.sequence, previous := cursor.checksum, checksum}
      expectedChecksum := checksum
      bytes} =
      .ok (advance cursor checksum bytes) := by
  simp [accept, positive]

theorem accept_fields (cursor next : Cursor) (frame : CheckedFrame)
    (accepted : accept cursor frame = .ok next) :
    frame.header.version = 1 ∧ frame.header.sequence = cursor.sequence ∧
    frame.header.previous = cursor.checksum ∧
    frame.header.checksum = frame.expectedChecksum ∧ 0 < frame.bytes ∧
    next = advance cursor frame.header.checksum frame.bytes := by
  simp only [accept] at accepted
  split at accepted
  · rename_i valid
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at valid
    cases accepted
    exact ⟨valid.1.1.1.1, valid.1.1.1.2, valid.1.1.2, valid.1.2, valid.2, rfl⟩
  · cases accepted

theorem accept_bookkeeping (cursor next : Cursor) (frame : CheckedFrame)
    (accepted : accept cursor frame = .ok next) :
    next.sequence = cursor.sequence + 1 ∧ next.bytes = cursor.bytes + frame.bytes ∧
    next.checksum = frame.expectedChecksum := by
  obtain ⟨_, _, _, hash, _, rfl⟩ := accept_fields cursor next frame accepted
  exact ⟨rfl, rfl, hash⟩

/-- Revalidating a complete prefix and incrementally accepting its frames yield
the same next sequence and exact accumulated bytes, starting at any valid head. -/
theorem validatePrefix_bookkeeping (frames : List CheckedFrame) (cursor next : Cursor)
    (accepted : validatePrefix cursor frames = .ok next) :
    next.sequence = cursor.sequence + frames.length ∧
    next.bytes = cursor.bytes + (frames.map CheckedFrame.bytes).sum := by
  induction frames generalizing cursor with
  | nil =>
    simp only [validatePrefix, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    simp
  | cons frame frames ih =>
    simp only [validatePrefix, List.foldlM_cons] at accepted
    cases first : accept cursor frame with
    | error error =>
      rw [first] at accepted
      cases accepted
    | ok middle =>
      simp only [first] at accepted
      obtain ⟨seq, size, _⟩ := accept_bookkeeping cursor middle frame first
      obtain ⟨seqTail, sizeTail⟩ := ih middle accepted
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      constructor <;> omega

/-- Every nonempty accepted suffix ends at its final frame's supplied digest. -/
theorem validatePrefix_last_checksum (frames : List CheckedFrame) (cursor middle next : Cursor)
    (last : CheckedFrame)
    (acceptedPrefix : validatePrefix cursor frames = .ok middle)
    (accepted : accept middle last = .ok next) :
    validatePrefix cursor (frames ++ [last]) = .ok next ∧
    next.checksum = last.expectedChecksum := by
  constructor
  · simp only [validatePrefix, List.foldlM_append]
    change frames.foldlM accept cursor = .ok middle at acceptedPrefix
    rw [acceptedPrefix]
    simp only [ok_bind, List.foldlM_cons, List.foldlM_nil, accepted]
    rfl
  · exact (accept_bookkeeping middle next last accepted).2.2

end Harness.Journal
