import Harness.Core.Capabilities
import Mathlib.Data.List.Basic

/-!
Semantic containment for executable capability ceilings. The finite checker is
sound but deliberately incomplete; its failure is not an escalation witness.
These results concern lexical demands and the grants declared by an application,
not filesystem resolution or the effects of an authorized external process.
-/
namespace Harness.Capability

theorem PathScope.covers_trans {a b c : PathScope}
    (ab : a.covers b = true) (bc : b.covers c = true) : a.covers c = true := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
    simp only [PathScope.covers, PathScope.path] at * <;>
    cases ha : normalizePath a <;> cases hb : normalizePath b <;>
    cases hc : normalizePath c <;> simp_all
  all_goals exact List.IsPrefix.trans ab bc

theorem ResourceScope.covers_trans {a b c : ResourceScope}
    (ab : a.covers b = true) (bc : b.covers c = true) : a.covers c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [ResourceScope.covers]

private theorem process_covers_trans {a b c : Array String} {x y z : String}
    (ab : covers (.process a x) (.process b y) = true)
    (bc : covers (.process b y) (.process c z) = true) :
    covers (.process a x) (.process c z) = true := by
  cases hx : normalizePath x <;> cases hy : normalizePath y <;>
    cases hz : normalizePath z <;> simp_all [covers]

private theorem resource_covers_trans {a b c x y z : String} {p q r : ResourceScope}
    (ab : covers (.resource a x p) (.resource b y q) = true)
    (bc : covers (.resource b y q) (.resource c z r) = true) :
    covers (.resource a x p) (.resource c z r) = true := by
  simp only [covers, Bool.and_eq_true, beq_iff_eq] at ab bc ⊢
  exact ⟨⟨ab.1.1.trans bc.1.1, ab.1.2.trans bc.1.2⟩,
    ResourceScope.covers_trans ab.2 bc.2⟩

theorem covers_trans {a b c : Access}
    (ab : covers a b = true) (bc : covers b c = true) : covers a c = true := by
  cases a <;> cases b <;> cases c <;> simp only [covers] at ab bc ⊢ <;>
    try contradiction
  all_goals first
    | exact PathScope.covers_trans ab bc
    | exact process_covers_trans ab bc
    | exact resource_covers_trans ab bc
    | simp_all

@[simp] theorem permits_intersect (left right : Policy) (demand : Access) :
    permits (intersect left right) demand = (permits left demand && permits right demand) := by
  simp [permits, intersect]

@[simp] theorem permitsAll_intersect (left right : Policy) (demands : List Access) :
    permitsAll (intersect left right) demands =
      (permitsAll left demands && permitsAll right demands) := by
  apply Bool.eq_iff_iff.mpr
  simp [permitsAll, List.all_eq_true, permits_intersect, forall_and, and_assoc, and_left_comm]

theorem contained_refl (policy : Policy) : Contained policy policy := fun _ h => h

theorem contained_trans {child parent ceiling : Policy}
    (first : Contained child parent) (second : Contained parent ceiling) :
    Contained child ceiling := fun demand h => second demand (first demand h)

theorem intersect_contained_left (left right : Policy) :
    Contained (intersect left right) left := by
  intro demand h
  exact (Bool.and_eq_true_iff.mp (by simpa using h)).1

theorem intersect_contained_right (left right : Policy) :
    Contained (intersect left right) right := by
  intro demand h
  exact (Bool.and_eq_true_iff.mp (by simpa using h)).2

theorem restrict_contained_parent (parent : Policy) (layer : List Access) :
    Contained (restrict parent layer) parent := intersect_contained_left parent [layer]

theorem restrict_contained_layer (parent : Policy) (layer : List Access) :
    Contained (restrict parent layer) [layer] := intersect_contained_right parent [layer]

theorem checkContained_sound {child parent : Policy}
    (checked : checkContained child parent = true) : Contained child parent := by
  intro demand allowed
  simp only [checkContained, List.all_eq_true, List.any_eq_true] at checked
  simp only [permits, List.all_eq_true, List.any_eq_true] at allowed ⊢
  intro upper upperMember
  obtain ⟨lower, lowerMember, lowerCovered⟩ := checked upper upperMember
  obtain ⟨grant, grantMember, demandCovered⟩ := allowed lower lowerMember
  obtain ⟨ceiling, ceilingMember, grantCovered⟩ := lowerCovered grant grantMember
  exact ⟨ceiling, ceilingMember, covers_trans grantCovered demandCovered⟩

theorem permitsAll_nonempty {policy : Policy} {demands : List Access}
    (allowed : permitsAll policy demands = true) : demands ≠ [] := by
  cases demands <;> simp_all [permitsAll]

theorem permitsAll_member {policy : Policy} {demands : List Access} {demand : Access}
    (allowed : permitsAll policy demands = true) (member : demand ∈ demands) :
    permits policy demand = true := by
  exact (List.all_eq_true.mp (Bool.and_eq_true_iff.mp allowed).2) demand member

theorem permitsAll_of_contained {child parent : Policy} {demands : List Access}
    (contained : Contained child parent) (allowed : permitsAll child demands = true) :
    permitsAll parent demands = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨(Bool.and_eq_true_iff.mp allowed).1, List.all_eq_true.mpr ?_⟩
  intro demand member
  exact contained demand (permitsAll_member allowed member)

end Harness.Capability
