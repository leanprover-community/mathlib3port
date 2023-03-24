/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module topology.covering
! leanprover-community/mathlib commit 8ef6f08ff8c781c5c07a8b12843710e1a0d8a688
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.IsLocallyHomeomorph
import Mathbin.Topology.FiberBundle.Basic

/-!
# Covering Maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines covering maps.

## Main definitions

* `is_evenly_covered f x I`: A point `x` is evenly coverd by `f : E → X` with fiber `I` if `I` is
  discrete and there is a `trivialization` of `f` at `x` with fiber `I`.
* `is_covering_map f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/


open Bundle

variable {E X : Type _} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

#print IsEvenlyCovered /-
/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood. -/
def IsEvenlyCovered (x : X) (I : Type _) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ t : Trivialization I f, x ∈ t.baseSet
#align is_evenly_covered IsEvenlyCovered
-/

namespace IsEvenlyCovered

variable {f}

/- warning: is_evenly_covered.to_trivialization -> IsEvenlyCovered.toTrivialization is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u_1}} {X : Type.{u_2}} [_inst_1 : TopologicalSpace.{u_1} E] [_inst_2 : TopologicalSpace.{u_2} X] {f : E -> X} {x : X} {I : Type.{u_3}} [_inst_3 : TopologicalSpace.{u_3} I], (IsEvenlyCovered.{u_1, u_2, u_3} E X _inst_1 _inst_2 f x I _inst_3) -> (Trivialization.{u_2, u_1, u_1} X (coeSort.{max (succ u_1) 1, succ (succ u_1)} (Set.{u_1} E) Type.{u_1} (Set.hasCoeToSort.{u_1} E) (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) x))) E _inst_2 (Subtype.topologicalSpace.{u_1} E (fun (x_1 : E) => Membership.Mem.{u_1, u_1} E (Set.{u_1} E) (Set.hasMem.{u_1} E) x_1 (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) x))) _inst_1) _inst_1 f)
but is expected to have type
  forall {E : Type.{u_1}} {X : Type.{u_2}} [_inst_1 : TopologicalSpace.{u_1} E] [_inst_2 : TopologicalSpace.{u_2} X] {f : E -> X} {x : X} {I : Type.{u_3}} [_inst_3 : TopologicalSpace.{u_3} I], (IsEvenlyCovered.{u_1, u_2, u_3} E X _inst_1 _inst_2 f x I _inst_3) -> (Trivialization.{u_2, u_1, u_1} X (Set.Elem.{u_1} E (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.instSingletonSet.{u_2} X) x))) E _inst_2 (instTopologicalSpaceSubtype.{u_1} E (fun (x_1 : E) => Membership.mem.{u_1, u_1} E (Set.{u_1} E) (Set.instMembershipSet.{u_1} E) x_1 (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.instSingletonSet.{u_2} X) x))) _inst_1) _inst_1 f)
Case conversion may be inaccurate. Consider using '#align is_evenly_covered.to_trivialization IsEvenlyCovered.toTrivializationₓ'. -/
/-- If `x` is evenly covered by `f`, then we can construct a trivialization of `f` at `x`. -/
noncomputable def toTrivialization {x : X} {I : Type _} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : Trivialization (f ⁻¹' {x}) f :=
  (Classical.choose h.2).transFiberHomeomorph
    ((Classical.choose h.2).preimageSingletonHomeomorph (Classical.choose_spec h.2)).symm
#align is_evenly_covered.to_trivialization IsEvenlyCovered.toTrivialization

/- warning: is_evenly_covered.mem_to_trivialization_base_set -> IsEvenlyCovered.mem_toTrivialization_baseSet is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u_1}} {X : Type.{u_2}} [_inst_1 : TopologicalSpace.{u_1} E] [_inst_2 : TopologicalSpace.{u_2} X] {f : E -> X} {x : X} {I : Type.{u_3}} [_inst_3 : TopologicalSpace.{u_3} I] (h : IsEvenlyCovered.{u_1, u_2, u_3} E X _inst_1 _inst_2 f x I _inst_3), Membership.Mem.{u_2, u_2} X (Set.{u_2} X) (Set.hasMem.{u_2} X) x (Trivialization.baseSet.{u_2, u_1, u_1} X (coeSort.{max (succ u_1) 1, succ (succ u_1)} (Set.{u_1} E) Type.{u_1} (Set.hasCoeToSort.{u_1} E) (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) x))) E _inst_2 (Subtype.topologicalSpace.{u_1} E (fun (x_1 : E) => Membership.Mem.{u_1, u_1} E (Set.{u_1} E) (Set.hasMem.{u_1} E) x_1 (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) x))) _inst_1) _inst_1 f (IsEvenlyCovered.toTrivialization.{u_1, u_2, u_3, u_4} E X _inst_1 _inst_2 f x I _inst_3 h))
but is expected to have type
  forall {E : Type.{u_2}} {X : Type.{u_3}} [_inst_1 : TopologicalSpace.{u_2} E] [_inst_2 : TopologicalSpace.{u_3} X] {f : E -> X} {x : X} {I : Type.{u_1}} [_inst_3 : TopologicalSpace.{u_1} I] (h : IsEvenlyCovered.{u_2, u_3, u_1} E X _inst_1 _inst_2 f x I _inst_3), Membership.mem.{u_3, u_3} X (Set.{u_3} X) (Set.instMembershipSet.{u_3} X) x (Trivialization.baseSet.{u_3, u_2, u_2} X (Set.Elem.{u_2} E (Set.preimage.{u_2, u_3} E X f (Singleton.singleton.{u_3, u_3} X (Set.{u_3} X) (Set.instSingletonSet.{u_3} X) x))) E _inst_2 (instTopologicalSpaceSubtype.{u_2} E (fun (x_1 : E) => Membership.mem.{u_2, u_2} E (Set.{u_2} E) (Set.instMembershipSet.{u_2} E) x_1 (Set.preimage.{u_2, u_3} E X f (Singleton.singleton.{u_3, u_3} X (Set.{u_3} X) (Set.instSingletonSet.{u_3} X) x))) _inst_1) _inst_1 f (IsEvenlyCovered.toTrivialization.{u_2, u_3, u_1} E X _inst_1 _inst_2 f x I _inst_3 h))
Case conversion may be inaccurate. Consider using '#align is_evenly_covered.mem_to_trivialization_base_set IsEvenlyCovered.mem_toTrivialization_baseSetₓ'. -/
theorem mem_toTrivialization_baseSet {x : X} {I : Type _} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : x ∈ h.toTrivialization.baseSet :=
  Classical.choose_spec h.2
#align is_evenly_covered.mem_to_trivialization_base_set IsEvenlyCovered.mem_toTrivialization_baseSet

/- warning: is_evenly_covered.to_trivialization_apply -> IsEvenlyCovered.toTrivialization_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u_1}} {X : Type.{u_2}} [_inst_1 : TopologicalSpace.{u_1} E] [_inst_2 : TopologicalSpace.{u_2} X] {f : E -> X} {x : E} {I : Type.{u_3}} [_inst_3 : TopologicalSpace.{u_3} I] (h : IsEvenlyCovered.{u_1, u_2, u_3} E X _inst_1 _inst_2 f (f x) I _inst_3), Eq.{succ u_1} (coeSort.{max (succ u_1) 1, succ (succ u_1)} (Set.{u_1} E) Type.{u_1} (Set.hasCoeToSort.{u_1} E) (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) (f x)))) (Prod.snd.{u_2, u_1} X (coeSort.{max (succ u_1) 1, succ (succ u_1)} (Set.{u_1} E) Type.{u_1} (Set.hasCoeToSort.{u_1} E) (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) (f x)))) (coeFn.{max (succ u_2) (succ u_1), max (succ u_2) (succ u_1)} (Trivialization.{u_2, u_1, u_1} X (coeSort.{max (succ u_1) 1, succ (succ u_1)} (Set.{u_1} E) Type.{u_1} (Set.hasCoeToSort.{u_1} E) (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) (f x)))) E _inst_2 (Subtype.topologicalSpace.{u_1} E (fun (x_1 : E) => Membership.Mem.{u_1, u_1} E (Set.{u_1} E) (Set.hasMem.{u_1} E) x_1 (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) (f x)))) _inst_1) _inst_1 f) (fun (_x : Trivialization.{u_2, u_1, u_1} X (coeSort.{max (succ u_1) 1, succ (succ u_1)} (Set.{u_1} E) Type.{u_1} (Set.hasCoeToSort.{u_1} E) (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) (f x)))) E _inst_2 (Subtype.topologicalSpace.{u_1} E (fun (x_1 : E) => Membership.Mem.{u_1, u_1} E (Set.{u_1} E) (Set.hasMem.{u_1} E) x_1 (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) (f x)))) _inst_1) _inst_1 f) => E -> (Prod.{u_2, u_1} X (coeSort.{max (succ u_1) 1, succ (succ u_1)} (Set.{u_1} E) Type.{u_1} (Set.hasCoeToSort.{u_1} E) (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) (f x)))))) (Trivialization.hasCoeToFun.{u_2, u_1, u_1} X (coeSort.{max (succ u_1) 1, succ (succ u_1)} (Set.{u_1} E) Type.{u_1} (Set.hasCoeToSort.{u_1} E) (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) (f x)))) E _inst_2 (Subtype.topologicalSpace.{u_1} E (fun (x_1 : E) => Membership.Mem.{u_1, u_1} E (Set.{u_1} E) (Set.hasMem.{u_1} E) x_1 (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) (f x)))) _inst_1) f _inst_1) (IsEvenlyCovered.toTrivialization.{u_1, u_2, u_3, u_4} E X _inst_1 _inst_2 f (f x) I _inst_3 h) x)) (Subtype.mk.{succ u_1} E (fun (x_1 : E) => Membership.Mem.{u_1, u_1} E (Set.{u_1} E) (Set.hasMem.{u_1} E) x_1 (Set.preimage.{u_1, u_2} E X f (Singleton.singleton.{u_2, u_2} X (Set.{u_2} X) (Set.hasSingleton.{u_2} X) (f x)))) x (rfl.{succ u_2} X (f x)))
but is expected to have type
  forall {E : Type.{u_2}} {X : Type.{u_3}} [_inst_1 : TopologicalSpace.{u_2} E] [_inst_2 : TopologicalSpace.{u_3} X] {f : E -> X} {x : E} {I : Type.{u_1}} [_inst_3 : TopologicalSpace.{u_1} I] (h : IsEvenlyCovered.{u_2, u_3, u_1} E X _inst_1 _inst_2 f (f x) I _inst_3), Eq.{succ u_2} (Set.Elem.{u_2} E (Set.preimage.{u_2, u_3} E X f (Singleton.singleton.{u_3, u_3} X (Set.{u_3} X) (Set.instSingletonSet.{u_3} X) (f x)))) (Prod.snd.{u_3, u_2} X (Set.Elem.{u_2} E (Set.preimage.{u_2, u_3} E X f (Singleton.singleton.{u_3, u_3} X (Set.{u_3} X) (Set.instSingletonSet.{u_3} X) (f x)))) (Trivialization.toFun'.{u_3, u_2, u_2} X (Set.Elem.{u_2} E (Set.preimage.{u_2, u_3} E X f (Singleton.singleton.{u_3, u_3} X (Set.{u_3} X) (Set.instSingletonSet.{u_3} X) (f x)))) E _inst_2 (instTopologicalSpaceSubtype.{u_2} E (fun (x_1 : E) => Membership.mem.{u_2, u_2} E (Set.{u_2} E) (Set.instMembershipSet.{u_2} E) x_1 (Set.preimage.{u_2, u_3} E X f (Singleton.singleton.{u_3, u_3} X (Set.{u_3} X) (Set.instSingletonSet.{u_3} X) (f x)))) _inst_1) f _inst_1 (IsEvenlyCovered.toTrivialization.{u_2, u_3, u_1} E X _inst_1 _inst_2 f (f x) I _inst_3 h) x)) (Subtype.mk.{succ u_2} E (fun (x_1 : E) => Membership.mem.{u_2, u_2} E (Set.{u_2} E) (Set.instMembershipSet.{u_2} E) x_1 (Set.preimage.{u_2, u_3} E X f (Singleton.singleton.{u_3, u_3} X (Set.{u_3} X) (Set.instSingletonSet.{u_3} X) (f x)))) x (rfl.{succ u_3} X (f x)))
Case conversion may be inaccurate. Consider using '#align is_evenly_covered.to_trivialization_apply IsEvenlyCovered.toTrivialization_applyₓ'. -/
theorem toTrivialization_apply {x : E} {I : Type _} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : (h.toTrivialization x).2 = ⟨x, rfl⟩ :=
  let e := Classical.choose h.2
  let h := Classical.choose_spec h.2
  let he := e.mk_proj_snd' h
  Subtype.ext
    ((e.toLocalEquiv.eq_symm_apply (e.mem_source.mpr h)
            (by rwa [he, e.mem_target, e.coe_fst (e.mem_source.mpr h)])).mpr
        he.symm).symm
#align is_evenly_covered.to_trivialization_apply IsEvenlyCovered.toTrivialization_apply

/- warning: is_evenly_covered.continuous_at -> IsEvenlyCovered.continuousAt is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X} {x : E} {I : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} I], (IsEvenlyCovered.{u1, u2, u3} E X _inst_1 _inst_2 f (f x) I _inst_3) -> (ContinuousAt.{u1, u2} E X _inst_1 _inst_2 f x)
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X} {x : E} {I : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} I], (IsEvenlyCovered.{u2, u1, u3} E X _inst_1 _inst_2 f (f x) I _inst_3) -> (ContinuousAt.{u2, u1} E X _inst_1 _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align is_evenly_covered.continuous_at IsEvenlyCovered.continuousAtₓ'. -/
protected theorem continuousAt {x : E} {I : Type _} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : ContinuousAt f x :=
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))
#align is_evenly_covered.continuous_at IsEvenlyCovered.continuousAt

/- warning: is_evenly_covered.to_is_evenly_covered_preimage -> IsEvenlyCovered.to_isEvenlyCovered_preimage is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X} {x : X} {I : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} I], (IsEvenlyCovered.{u1, u2, u3} E X _inst_1 _inst_2 f x I _inst_3) -> (IsEvenlyCovered.{u1, u2, u1} E X _inst_1 _inst_2 f x (coeSort.{succ u1, succ (succ u1)} (Set.{u1} E) Type.{u1} (Set.hasCoeToSort.{u1} E) (Set.preimage.{u1, u2} E X f (Singleton.singleton.{u2, u2} X (Set.{u2} X) (Set.hasSingleton.{u2} X) x))) (Subtype.topologicalSpace.{u1} E (fun (x_1 : E) => Membership.Mem.{u1, u1} E (Set.{u1} E) (Set.hasMem.{u1} E) x_1 (Set.preimage.{u1, u2} E X f (Singleton.singleton.{u2, u2} X (Set.{u2} X) (Set.hasSingleton.{u2} X) x))) _inst_1))
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X} {x : X} {I : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} I], (IsEvenlyCovered.{u2, u1, u3} E X _inst_1 _inst_2 f x I _inst_3) -> (IsEvenlyCovered.{u2, u1, u2} E X _inst_1 _inst_2 f x (Set.Elem.{u2} E (Set.preimage.{u2, u1} E X f (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.instSingletonSet.{u1} X) x))) (instTopologicalSpaceSubtype.{u2} E (fun (x_1 : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x_1 (Set.preimage.{u2, u1} E X f (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.instSingletonSet.{u1} X) x))) _inst_1))
Case conversion may be inaccurate. Consider using '#align is_evenly_covered.to_is_evenly_covered_preimage IsEvenlyCovered.to_isEvenlyCovered_preimageₓ'. -/
theorem to_isEvenlyCovered_preimage {x : X} {I : Type _} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x}) :=
  let ⟨h1, h2⟩ := h
  ⟨((Classical.choose h2).preimageSingletonHomeomorph
          (Classical.choose_spec h2)).Embedding.DiscreteTopology,
    _, h.mem_to_trivialization_base_set⟩
#align is_evenly_covered.to_is_evenly_covered_preimage IsEvenlyCovered.to_isEvenlyCovered_preimage

end IsEvenlyCovered

#print IsCoveringMapOn /-
/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMapOn :=
  ∀ x ∈ s, IsEvenlyCovered f x (f ⁻¹' {x})
#align is_covering_map_on IsCoveringMapOn
-/

namespace IsCoveringMapOn

#print IsCoveringMapOn.mk /-
theorem mk (F : X → Type _) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x ∈ s, Trivialization (F x) f) (h : ∀ (x : X) (hx : x ∈ s), x ∈ (e x hx).baseSet) :
    IsCoveringMapOn f s := fun x hx =>
  IsEvenlyCovered.to_isEvenlyCovered_preimage ⟨hF x, e x hx, h x hx⟩
#align is_covering_map_on.mk IsCoveringMapOn.mk
-/

variable {f} {s}

/- warning: is_covering_map_on.continuous_at -> IsCoveringMapOn.continuousAt is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X} {s : Set.{u2} X}, (IsCoveringMapOn.{u1, u2} E X _inst_1 _inst_2 f s) -> (forall {x : E}, (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) (f x) s) -> (ContinuousAt.{u1, u2} E X _inst_1 _inst_2 f x))
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X} {s : Set.{u1} X}, (IsCoveringMapOn.{u2, u1} E X _inst_1 _inst_2 f s) -> (forall {x : E}, (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) (f x) s) -> (ContinuousAt.{u2, u1} E X _inst_1 _inst_2 f x))
Case conversion may be inaccurate. Consider using '#align is_covering_map_on.continuous_at IsCoveringMapOn.continuousAtₓ'. -/
protected theorem continuousAt (hf : IsCoveringMapOn f s) {x : E} (hx : f x ∈ s) :
    ContinuousAt f x :=
  (hf (f x) hx).ContinuousAt
#align is_covering_map_on.continuous_at IsCoveringMapOn.continuousAt

/- warning: is_covering_map_on.continuous_on -> IsCoveringMapOn.continuousOn is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X} {s : Set.{u2} X}, (IsCoveringMapOn.{u1, u2} E X _inst_1 _inst_2 f s) -> (ContinuousOn.{u1, u2} E X _inst_1 _inst_2 f (Set.preimage.{u1, u2} E X f s))
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X} {s : Set.{u1} X}, (IsCoveringMapOn.{u2, u1} E X _inst_1 _inst_2 f s) -> (ContinuousOn.{u2, u1} E X _inst_1 _inst_2 f (Set.preimage.{u2, u1} E X f s))
Case conversion may be inaccurate. Consider using '#align is_covering_map_on.continuous_on IsCoveringMapOn.continuousOnₓ'. -/
protected theorem continuousOn (hf : IsCoveringMapOn f s) : ContinuousOn f (f ⁻¹' s) :=
  ContinuousAt.continuousOn fun x => hf.ContinuousAt
#align is_covering_map_on.continuous_on IsCoveringMapOn.continuousOn

/- warning: is_covering_map_on.is_locally_homeomorph_on -> IsCoveringMapOn.isLocallyHomeomorphOn is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X} {s : Set.{u2} X}, (IsCoveringMapOn.{u1, u2} E X _inst_1 _inst_2 f s) -> (IsLocallyHomeomorphOn.{u1, u2} E X _inst_1 _inst_2 f (Set.preimage.{u1, u2} E X f s))
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X} {s : Set.{u1} X}, (IsCoveringMapOn.{u2, u1} E X _inst_1 _inst_2 f s) -> (IsLocallyHomeomorphOn.{u2, u1} E X _inst_1 _inst_2 f (Set.preimage.{u2, u1} E X f s))
Case conversion may be inaccurate. Consider using '#align is_covering_map_on.is_locally_homeomorph_on IsCoveringMapOn.isLocallyHomeomorphOnₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
protected theorem isLocallyHomeomorphOn (hf : IsCoveringMapOn f s) :
    IsLocallyHomeomorphOn f (f ⁻¹' s) :=
  by
  refine' IsLocallyHomeomorphOn.mk f (f ⁻¹' s) fun x hx => _
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine'
    ⟨e.to_local_homeomorph.trans
        { toFun := fun p => p.1
          invFun := fun p => ⟨p, x, rfl⟩
          source := e.base_set ×ˢ ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))
          target := e.base_set
          open_source :=
            e.open_base_set.prod (singletons_open_iff_discrete.2 (hf (f x) hx).1 ⟨x, rfl⟩)
          open_target := e.open_base_set
          map_source' := fun p => And.left
          map_target' := fun p hp => ⟨hp, rfl⟩
          left_inv' := fun p hp => Prod.ext rfl hp.2.symm
          right_inv' := fun p hp => rfl
          continuous_toFun := continuous_fst.continuous_on
          continuous_invFun := (continuous_id'.prod_mk continuous_const).ContinuousOn },
      ⟨he, by rwa [e.to_local_homeomorph.symm_symm, e.proj_to_fun x he],
        (hf (f x) hx).toTrivialization_apply⟩,
      fun p h => (e.proj_to_fun p h.1).symm⟩
#align is_covering_map_on.is_locally_homeomorph_on IsCoveringMapOn.isLocallyHomeomorphOn

end IsCoveringMapOn

#print IsCoveringMap /-
/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})
#align is_covering_map IsCoveringMap
-/

variable {f}

/- warning: is_covering_map_iff_is_covering_map_on_univ -> isCoveringMap_iff_isCoveringMapOn_univ is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X}, Iff (IsCoveringMap.{u1, u2} E X _inst_1 _inst_2 f) (IsCoveringMapOn.{u1, u2} E X _inst_1 _inst_2 f (Set.univ.{u2} X))
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X}, Iff (IsCoveringMap.{u2, u1} E X _inst_1 _inst_2 f) (IsCoveringMapOn.{u2, u1} E X _inst_1 _inst_2 f (Set.univ.{u1} X))
Case conversion may be inaccurate. Consider using '#align is_covering_map_iff_is_covering_map_on_univ isCoveringMap_iff_isCoveringMapOn_univₓ'. -/
theorem isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn f Set.univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]
#align is_covering_map_iff_is_covering_map_on_univ isCoveringMap_iff_isCoveringMapOn_univ

/- warning: is_covering_map.is_covering_map_on -> IsCoveringMap.isCoveringMapOn is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X}, (IsCoveringMap.{u1, u2} E X _inst_1 _inst_2 f) -> (IsCoveringMapOn.{u1, u2} E X _inst_1 _inst_2 f (Set.univ.{u2} X))
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X}, (IsCoveringMap.{u2, u1} E X _inst_1 _inst_2 f) -> (IsCoveringMapOn.{u2, u1} E X _inst_1 _inst_2 f (Set.univ.{u1} X))
Case conversion may be inaccurate. Consider using '#align is_covering_map.is_covering_map_on IsCoveringMap.isCoveringMapOnₓ'. -/
protected theorem IsCoveringMap.isCoveringMapOn (hf : IsCoveringMap f) :
    IsCoveringMapOn f Set.univ :=
  isCoveringMap_iff_isCoveringMapOn_univ.mp hf
#align is_covering_map.is_covering_map_on IsCoveringMap.isCoveringMapOn

variable (f)

namespace IsCoveringMap

#print IsCoveringMap.mk /-
theorem mk (F : X → Type _) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x ∈ (e x).baseSet) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr
    (IsCoveringMapOn.mk f Set.univ F (fun x hx => e x) fun x hx => h x)
#align is_covering_map.mk IsCoveringMap.mk
-/

variable {f}

/- warning: is_covering_map.continuous -> IsCoveringMap.continuous is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X}, (IsCoveringMap.{u1, u2} E X _inst_1 _inst_2 f) -> (Continuous.{u1, u2} E X _inst_1 _inst_2 f)
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X}, (IsCoveringMap.{u2, u1} E X _inst_1 _inst_2 f) -> (Continuous.{u2, u1} E X _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_covering_map.continuous IsCoveringMap.continuousₓ'. -/
protected theorem continuous (hf : IsCoveringMap f) : Continuous f :=
  continuous_iff_continuousOn_univ.mpr hf.IsCoveringMapOn.ContinuousOn
#align is_covering_map.continuous IsCoveringMap.continuous

/- warning: is_covering_map.is_locally_homeomorph -> IsCoveringMap.isLocallyHomeomorph is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X}, (IsCoveringMap.{u1, u2} E X _inst_1 _inst_2 f) -> (IsLocallyHomeomorph.{u1, u2} E X _inst_1 _inst_2 f)
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X}, (IsCoveringMap.{u2, u1} E X _inst_1 _inst_2 f) -> (IsLocallyHomeomorph.{u2, u1} E X _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_covering_map.is_locally_homeomorph IsCoveringMap.isLocallyHomeomorphₓ'. -/
protected theorem isLocallyHomeomorph (hf : IsCoveringMap f) : IsLocallyHomeomorph f :=
  isLocallyHomeomorph_iff_isLocallyHomeomorphOn_univ.mpr hf.IsCoveringMapOn.IsLocallyHomeomorphOn
#align is_covering_map.is_locally_homeomorph IsCoveringMap.isLocallyHomeomorph

/- warning: is_covering_map.is_open_map -> IsCoveringMap.isOpenMap is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X}, (IsCoveringMap.{u1, u2} E X _inst_1 _inst_2 f) -> (IsOpenMap.{u1, u2} E X _inst_1 _inst_2 f)
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X}, (IsCoveringMap.{u2, u1} E X _inst_1 _inst_2 f) -> (IsOpenMap.{u2, u1} E X _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_covering_map.is_open_map IsCoveringMap.isOpenMapₓ'. -/
protected theorem isOpenMap (hf : IsCoveringMap f) : IsOpenMap f :=
  hf.IsLocallyHomeomorph.IsOpenMap
#align is_covering_map.is_open_map IsCoveringMap.isOpenMap

/- warning: is_covering_map.quotient_map -> IsCoveringMap.quotientMap is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X}, (IsCoveringMap.{u1, u2} E X _inst_1 _inst_2 f) -> (Function.Surjective.{succ u1, succ u2} E X f) -> (QuotientMap.{u1, u2} E X _inst_1 _inst_2 f)
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X}, (IsCoveringMap.{u2, u1} E X _inst_1 _inst_2 f) -> (Function.Surjective.{succ u2, succ u1} E X f) -> (QuotientMap.{u2, u1} E X _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_covering_map.quotient_map IsCoveringMap.quotientMapₓ'. -/
protected theorem quotientMap (hf : IsCoveringMap f) (hf' : Function.Surjective f) :
    QuotientMap f :=
  hf.IsOpenMap.to_quotientMap hf.Continuous hf'
#align is_covering_map.quotient_map IsCoveringMap.quotientMap

end IsCoveringMap

variable {f}

/- warning: is_fiber_bundle.is_covering_map -> IsFiberBundle.isCoveringMap is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : TopologicalSpace.{u2} X] {f : E -> X} {F : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} F] [_inst_4 : DiscreteTopology.{u3} F _inst_3], (forall (x : X), Exists.{max (succ u2) (succ u3) (succ u1)} (Trivialization.{u2, u3, u1} X F E _inst_2 _inst_3 _inst_1 f) (fun (e : Trivialization.{u2, u3, u1} X F E _inst_2 _inst_3 _inst_1 f) => Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) x (Trivialization.baseSet.{u2, u3, u1} X F E _inst_2 _inst_3 _inst_1 f e))) -> (IsCoveringMap.{u1, u2} E X _inst_1 _inst_2 f)
but is expected to have type
  forall {E : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : TopologicalSpace.{u1} X] {f : E -> X} {F : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} F] [_inst_4 : DiscreteTopology.{u3} F _inst_3], (forall (x : X), Exists.{max (max (succ u2) (succ u1)) (succ u3)} (Trivialization.{u1, u3, u2} X F E _inst_2 _inst_3 _inst_1 f) (fun (e : Trivialization.{u1, u3, u2} X F E _inst_2 _inst_3 _inst_1 f) => Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x (Trivialization.baseSet.{u1, u3, u2} X F E _inst_2 _inst_3 _inst_1 f e))) -> (IsCoveringMap.{u2, u1} E X _inst_1 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align is_fiber_bundle.is_covering_map IsFiberBundle.isCoveringMapₓ'. -/
protected theorem IsFiberBundle.isCoveringMap {F : Type _} [TopologicalSpace F] [DiscreteTopology F]
    (hf : ∀ x : X, ∃ e : Trivialization F f, x ∈ e.baseSet) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun x => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)
#align is_fiber_bundle.is_covering_map IsFiberBundle.isCoveringMap

/- warning: fiber_bundle.is_covering_map -> FiberBundle.isCoveringMap is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] {F : Type.{u2}} {E : X -> Type.{u3}} [_inst_3 : TopologicalSpace.{u2} F] [_inst_4 : DiscreteTopology.{u2} F _inst_3] [_inst_5 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u1, u3} X E)] [_inst_6 : forall (x : X), TopologicalSpace.{u3} (E x)] [hf : FiberBundle.{u1, u2, u3} X F _inst_2 _inst_3 E _inst_5 (fun (b : X) => _inst_6 b)], IsCoveringMap.{max u1 u3, u1} (Bundle.TotalSpace.{u1, u3} X E) X _inst_5 _inst_2 (Bundle.TotalSpace.proj.{u1, u3} X E)
but is expected to have type
  forall {X : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} X] {F : Type.{u3}} {E : X -> Type.{u2}} [_inst_3 : TopologicalSpace.{u3} F] [_inst_4 : DiscreteTopology.{u3} F _inst_3] [_inst_5 : TopologicalSpace.{max u2 u1} (Bundle.TotalSpace.{u1, u2} X E)] [_inst_6 : forall (x : X), TopologicalSpace.{u2} (E x)] [hf : FiberBundle.{u1, u3, u2} X F _inst_2 _inst_3 E _inst_5 (fun (b : X) => _inst_6 b)], IsCoveringMap.{max u1 u2, u1} (Bundle.TotalSpace.{u1, u2} X E) X _inst_5 _inst_2 (Bundle.TotalSpace.proj.{u1, u2} X E)
Case conversion may be inaccurate. Consider using '#align fiber_bundle.is_covering_map FiberBundle.isCoveringMapₓ'. -/
protected theorem FiberBundle.isCoveringMap {F : Type _} {E : X → Type _} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace (Bundle.TotalSpace E)] [∀ x, TopologicalSpace (E x)]
    [hf : FiberBundle F E] : IsCoveringMap (π E) :=
  IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩
#align fiber_bundle.is_covering_map FiberBundle.isCoveringMap

