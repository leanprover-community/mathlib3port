/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module dynamics.minimal
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.Topology.Algebra.ConstMulAction

/-!
# Minimal action of a group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define an action of a monoid `M` on a topological space `α` to be *minimal* if the
`M`-orbit of every point `x : α` is dense. We also provide an additive version of this definition
and prove some basic facts about minimal actions.

## TODO

* Define a minimal set of an action.

## Tags

group action, minimal
-/


open Pointwise

#print AddAction.IsMinimal /-
/-- An action of an additive monoid `M` on a topological space is called *minimal* if the `M`-orbit
of every point `x : α` is dense. -/
class AddAction.IsMinimal (M α : Type _) [AddMonoid M] [TopologicalSpace α] [AddAction M α] :
  Prop where
  dense_orbit : ∀ x : α, Dense (AddAction.orbit M x)
#align add_action.is_minimal AddAction.IsMinimal
-/

#print MulAction.IsMinimal /-
/-- An action of a monoid `M` on a topological space is called *minimal* if the `M`-orbit of every
point `x : α` is dense. -/
@[to_additive]
class MulAction.IsMinimal (M α : Type _) [Monoid M] [TopologicalSpace α] [MulAction M α] :
  Prop where
  dense_orbit : ∀ x : α, Dense (MulAction.orbit M x)
#align mul_action.is_minimal MulAction.IsMinimal
#align add_action.is_minimal AddAction.IsMinimal
-/

open MulAction Set

variable (M G : Type _) {α : Type _} [Monoid M] [Group G] [TopologicalSpace α] [MulAction M α]
  [MulAction G α]

/- warning: mul_action.dense_orbit -> MulAction.dense_orbit is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : MulAction.{u1, u2} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u1, u2} M α _inst_1 _inst_3 _inst_4] (x : α), Dense.{u2} α _inst_3 (MulAction.orbit.{u1, u2} M α _inst_1 _inst_4 x)
but is expected to have type
  forall (M : Type.{u2}) {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : MulAction.{u2, u1} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u2, u1} M α _inst_1 _inst_3 _inst_4] (x : α), Dense.{u1} α _inst_3 (MulAction.orbit.{u2, u1} M α _inst_1 _inst_4 x)
Case conversion may be inaccurate. Consider using '#align mul_action.dense_orbit MulAction.dense_orbitₓ'. -/
@[to_additive]
theorem MulAction.dense_orbit [IsMinimal M α] (x : α) : Dense (orbit M x) :=
  MulAction.IsMinimal.dense_orbit x
#align mul_action.dense_orbit MulAction.dense_orbit
#align add_action.dense_orbit AddAction.dense_orbit

/- warning: dense_range_smul -> denseRange_smul is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : MulAction.{u1, u2} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u1, u2} M α _inst_1 _inst_3 _inst_4] (x : α), DenseRange.{u2, u1} α _inst_3 M (fun (c : M) => SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_4) c x)
but is expected to have type
  forall (M : Type.{u2}) {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : MulAction.{u2, u1} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u2, u1} M α _inst_1 _inst_3 _inst_4] (x : α), DenseRange.{u1, u2} α _inst_3 M (fun (c : M) => HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_4)) c x)
Case conversion may be inaccurate. Consider using '#align dense_range_smul denseRange_smulₓ'. -/
@[to_additive]
theorem denseRange_smul [IsMinimal M α] (x : α) : DenseRange fun c : M => c • x :=
  MulAction.dense_orbit M x
#align dense_range_smul denseRange_smul
#align dense_range_vadd denseRange_vadd

#print MulAction.isMinimal_of_pretransitive /-
@[to_additive]
instance (priority := 100) MulAction.isMinimal_of_pretransitive [IsPretransitive M α] :
    IsMinimal M α :=
  ⟨fun x => (surjective_smul M x).DenseRange⟩
#align mul_action.is_minimal_of_pretransitive MulAction.isMinimal_of_pretransitive
#align add_action.is_minimal_of_pretransitive AddAction.isMinimal_of_pretransitive
-/

/- warning: is_open.exists_smul_mem -> IsOpen.exists_smul_mem is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : MulAction.{u1, u2} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u1, u2} M α _inst_1 _inst_3 _inst_4] (x : α) {U : Set.{u2} α}, (IsOpen.{u2} α _inst_3 U) -> (Set.Nonempty.{u2} α U) -> (Exists.{succ u1} M (fun (c : M) => Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_4) c x) U))
but is expected to have type
  forall (M : Type.{u2}) {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : MulAction.{u2, u1} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u2, u1} M α _inst_1 _inst_3 _inst_4] (x : α) {U : Set.{u1} α}, (IsOpen.{u1} α _inst_3 U) -> (Set.Nonempty.{u1} α U) -> (Exists.{succ u2} M (fun (c : M) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_4)) c x) U))
Case conversion may be inaccurate. Consider using '#align is_open.exists_smul_mem IsOpen.exists_smul_memₓ'. -/
@[to_additive]
theorem IsOpen.exists_smul_mem [IsMinimal M α] (x : α) {U : Set α} (hUo : IsOpen U)
    (hne : U.Nonempty) : ∃ c : M, c • x ∈ U :=
  (denseRange_smul M x).exists_mem_open hUo hne
#align is_open.exists_smul_mem IsOpen.exists_smul_mem
#align is_open.exists_vadd_mem IsOpen.exists_vadd_mem

/- warning: is_open.Union_preimage_smul -> IsOpen.unionᵢ_preimage_smul is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : MulAction.{u1, u2} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u1, u2} M α _inst_1 _inst_3 _inst_4] {U : Set.{u2} α}, (IsOpen.{u2} α _inst_3 U) -> (Set.Nonempty.{u2} α U) -> (Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, succ u1} α M (fun (c : M) => Set.preimage.{u2, u2} α α (SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_4) c) U)) (Set.univ.{u2} α))
but is expected to have type
  forall (M : Type.{u2}) {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : MulAction.{u2, u1} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u2, u1} M α _inst_1 _inst_3 _inst_4] {U : Set.{u1} α}, (IsOpen.{u1} α _inst_3 U) -> (Set.Nonempty.{u1} α U) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α M (fun (c : M) => Set.preimage.{u1, u1} α α ((fun (x._@.Mathlib.Dynamics.Minimal._hyg.339 : M) (x._@.Mathlib.Dynamics.Minimal._hyg.341 : α) => HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_4)) x._@.Mathlib.Dynamics.Minimal._hyg.339 x._@.Mathlib.Dynamics.Minimal._hyg.341) c) U)) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align is_open.Union_preimage_smul IsOpen.unionᵢ_preimage_smulₓ'. -/
@[to_additive]
theorem IsOpen.unionᵢ_preimage_smul [IsMinimal M α] {U : Set α} (hUo : IsOpen U)
    (hne : U.Nonempty) : (⋃ c : M, (· • ·) c ⁻¹' U) = univ :=
  unionᵢ_eq_univ_iff.2 fun x => hUo.exists_smul_mem M x hne
#align is_open.Union_preimage_smul IsOpen.unionᵢ_preimage_smul
#align is_open.Union_preimage_vadd IsOpen.unionᵢ_preimage_vadd

/- warning: is_open.Union_smul -> IsOpen.unionᵢ_smul is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) {α : Type.{u2}} [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalSpace.{u2} α] [_inst_5 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_6 : MulAction.IsMinimal.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3 _inst_5] {U : Set.{u2} α}, (IsOpen.{u2} α _inst_3 U) -> (Set.Nonempty.{u2} α U) -> (Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, succ u1} α G (fun (g : G) => SMul.smul.{u1, u2} G (Set.{u2} α) (Set.smulSet.{u1, u2} G α (MulAction.toHasSmul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5)) g U)) (Set.univ.{u2} α))
but is expected to have type
  forall (G : Type.{u2}) {α : Type.{u1}} [_inst_2 : Group.{u2} G] [_inst_3 : TopologicalSpace.{u1} α] [_inst_5 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_6 : MulAction.IsMinimal.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3 _inst_5] {U : Set.{u1} α}, (IsOpen.{u1} α _inst_3 U) -> (Set.Nonempty.{u1} α U) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α G (fun (g : G) => HSMul.hSMul.{u2, u1, u1} G (Set.{u1} α) (Set.{u1} α) (instHSMul.{u2, u1} G (Set.{u1} α) (Set.smulSet.{u2, u1} G α (MulAction.toSMul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_5))) g U)) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align is_open.Union_smul IsOpen.unionᵢ_smulₓ'. -/
@[to_additive]
theorem IsOpen.unionᵢ_smul [IsMinimal G α] {U : Set α} (hUo : IsOpen U) (hne : U.Nonempty) :
    (⋃ g : G, g • U) = univ :=
  unionᵢ_eq_univ_iff.2 fun x =>
    let ⟨g, hg⟩ := hUo.exists_smul_mem G x hne
    ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩
#align is_open.Union_smul IsOpen.unionᵢ_smul
#align is_open.Union_vadd IsOpen.unionᵢ_vadd

/- warning: is_compact.exists_finite_cover_smul -> IsCompact.exists_finite_cover_smul is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) {α : Type.{u2}} [_inst_2 : Group.{u1} G] [_inst_3 : TopologicalSpace.{u2} α] [_inst_5 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_6 : MulAction.IsMinimal.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3 _inst_5] [_inst_7 : ContinuousConstSMul.{u1, u2} G α _inst_3 (MulAction.toHasSmul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5)] {K : Set.{u2} α} {U : Set.{u2} α}, (IsCompact.{u2} α _inst_3 K) -> (IsOpen.{u2} α _inst_3 U) -> (Set.Nonempty.{u2} α U) -> (Exists.{succ u1} (Finset.{u1} G) (fun (I : Finset.{u1} G) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) K (Set.unionᵢ.{u2, succ u1} α G (fun (g : G) => Set.unionᵢ.{u2, 0} α (Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) g I) (fun (H : Membership.Mem.{u1, u1} G (Finset.{u1} G) (Finset.hasMem.{u1} G) g I) => SMul.smul.{u1, u2} G (Set.{u2} α) (Set.smulSet.{u1, u2} G α (MulAction.toHasSmul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_5)) g U)))))
but is expected to have type
  forall (G : Type.{u2}) {α : Type.{u1}} [_inst_2 : Group.{u2} G] [_inst_3 : TopologicalSpace.{u1} α] [_inst_5 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_6 : MulAction.IsMinimal.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3 _inst_5] [_inst_7 : ContinuousConstSMul.{u2, u1} G α _inst_3 (MulAction.toSMul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_5)] {K : Set.{u1} α} {U : Set.{u1} α}, (IsCompact.{u1} α _inst_3 K) -> (IsOpen.{u1} α _inst_3 U) -> (Set.Nonempty.{u1} α U) -> (Exists.{succ u2} (Finset.{u2} G) (fun (I : Finset.{u2} G) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) K (Set.unionᵢ.{u1, succ u2} α G (fun (g : G) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} G (Finset.{u2} G) (Finset.instMembershipFinset.{u2} G) g I) (fun (H : Membership.mem.{u2, u2} G (Finset.{u2} G) (Finset.instMembershipFinset.{u2} G) g I) => HSMul.hSMul.{u2, u1, u1} G (Set.{u1} α) (Set.{u1} α) (instHSMul.{u2, u1} G (Set.{u1} α) (Set.smulSet.{u2, u1} G α (MulAction.toSMul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_5))) g U)))))
Case conversion may be inaccurate. Consider using '#align is_compact.exists_finite_cover_smul IsCompact.exists_finite_cover_smulₓ'. -/
@[to_additive]
theorem IsCompact.exists_finite_cover_smul [IsMinimal G α] [ContinuousConstSMul G α] {K U : Set α}
    (hK : IsCompact K) (hUo : IsOpen U) (hne : U.Nonempty) : ∃ I : Finset G, K ⊆ ⋃ g ∈ I, g • U :=
  (hK.elim_finite_subcover (fun g : G => g • U) fun g => hUo.smul _) <|
    calc
      K ⊆ univ := subset_univ K
      _ = ⋃ g : G, g • U := (hUo.unionᵢ_smul G hne).symm
      
#align is_compact.exists_finite_cover_smul IsCompact.exists_finite_cover_smul
#align is_compact.exists_finite_cover_vadd IsCompact.exists_finite_cover_vadd

/- warning: dense_of_nonempty_smul_invariant -> dense_of_nonempty_smul_invariant is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : MulAction.{u1, u2} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u1, u2} M α _inst_1 _inst_3 _inst_4] {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (forall (c : M), HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (SMul.smul.{u1, u2} M (Set.{u2} α) (Set.smulSet.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_4)) c s) s) -> (Dense.{u2} α _inst_3 s)
but is expected to have type
  forall (M : Type.{u2}) {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : MulAction.{u2, u1} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u2, u1} M α _inst_1 _inst_3 _inst_4] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall (c : M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HSMul.hSMul.{u2, u1, u1} M (Set.{u1} α) (Set.{u1} α) (instHSMul.{u2, u1} M (Set.{u1} α) (Set.smulSet.{u2, u1} M α (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_4))) c s) s) -> (Dense.{u1} α _inst_3 s)
Case conversion may be inaccurate. Consider using '#align dense_of_nonempty_smul_invariant dense_of_nonempty_smul_invariantₓ'. -/
@[to_additive]
theorem dense_of_nonempty_smul_invariant [IsMinimal M α] {s : Set α} (hne : s.Nonempty)
    (hsmul : ∀ c : M, c • s ⊆ s) : Dense s :=
  let ⟨x, hx⟩ := hne
  (MulAction.dense_orbit M x).mono (range_subset_iff.2 fun c => hsmul c <| ⟨x, hx, rfl⟩)
#align dense_of_nonempty_smul_invariant dense_of_nonempty_smul_invariant
#align dense_of_nonempty_vadd_invariant dense_of_nonempty_vadd_invariant

/- warning: eq_empty_or_univ_of_smul_invariant_closed -> eq_empty_or_univ_of_smul_invariant_closed is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : MulAction.{u1, u2} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u1, u2} M α _inst_1 _inst_3 _inst_4] {s : Set.{u2} α}, (IsClosed.{u2} α _inst_3 s) -> (forall (c : M), HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (SMul.smul.{u1, u2} M (Set.{u2} α) (Set.smulSet.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_4)) c s) s) -> (Or (Eq.{succ u2} (Set.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.hasEmptyc.{u2} α))) (Eq.{succ u2} (Set.{u2} α) s (Set.univ.{u2} α)))
but is expected to have type
  forall (M : Type.{u2}) {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : MulAction.{u2, u1} M α _inst_1] [_inst_6 : MulAction.IsMinimal.{u2, u1} M α _inst_1 _inst_3 _inst_4] {s : Set.{u1} α}, (IsClosed.{u1} α _inst_3 s) -> (forall (c : M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HSMul.hSMul.{u2, u1, u1} M (Set.{u1} α) (Set.{u1} α) (instHSMul.{u2, u1} M (Set.{u1} α) (Set.smulSet.{u2, u1} M α (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_4))) c s) s) -> (Or (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Eq.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α)))
Case conversion may be inaccurate. Consider using '#align eq_empty_or_univ_of_smul_invariant_closed eq_empty_or_univ_of_smul_invariant_closedₓ'. -/
@[to_additive]
theorem eq_empty_or_univ_of_smul_invariant_closed [IsMinimal M α] {s : Set α} (hs : IsClosed s)
    (hsmul : ∀ c : M, c • s ⊆ s) : s = ∅ ∨ s = univ :=
  s.eq_empty_or_nonempty.imp_right fun hne =>
    hs.closure_eq ▸ (dense_of_nonempty_smul_invariant M hne hsmul).closure_eq
#align eq_empty_or_univ_of_smul_invariant_closed eq_empty_or_univ_of_smul_invariant_closed
#align eq_empty_or_univ_of_vadd_invariant_closed eq_empty_or_univ_of_vadd_invariant_closed

/- warning: is_minimal_iff_closed_smul_invariant -> isMinimal_iff_closed_smul_invariant is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : MulAction.{u1, u2} M α _inst_1] [_inst_6 : ContinuousConstSMul.{u1, u2} M α _inst_3 (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_4)], Iff (MulAction.IsMinimal.{u1, u2} M α _inst_1 _inst_3 _inst_4) (forall (s : Set.{u2} α), (IsClosed.{u2} α _inst_3 s) -> (forall (c : M), HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (SMul.smul.{u1, u2} M (Set.{u2} α) (Set.smulSet.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_4)) c s) s) -> (Or (Eq.{succ u2} (Set.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.hasEmptyc.{u2} α))) (Eq.{succ u2} (Set.{u2} α) s (Set.univ.{u2} α))))
but is expected to have type
  forall (M : Type.{u2}) {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : MulAction.{u2, u1} M α _inst_1] [_inst_6 : ContinuousConstSMul.{u2, u1} M α _inst_3 (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_4)], Iff (MulAction.IsMinimal.{u2, u1} M α _inst_1 _inst_3 _inst_4) (forall (s : Set.{u1} α), (IsClosed.{u1} α _inst_3 s) -> (forall (c : M), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HSMul.hSMul.{u2, u1, u1} M (Set.{u1} α) (Set.{u1} α) (instHSMul.{u2, u1} M (Set.{u1} α) (Set.smulSet.{u2, u1} M α (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_4))) c s) s) -> (Or (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Eq.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))))
Case conversion may be inaccurate. Consider using '#align is_minimal_iff_closed_smul_invariant isMinimal_iff_closed_smul_invariantₓ'. -/
@[to_additive]
theorem isMinimal_iff_closed_smul_invariant [ContinuousConstSMul M α] :
    IsMinimal M α ↔ ∀ s : Set α, IsClosed s → (∀ c : M, c • s ⊆ s) → s = ∅ ∨ s = univ :=
  by
  constructor;
  · intro h s
    exact eq_empty_or_univ_of_smul_invariant_closed M
  refine' fun H => ⟨fun x => dense_iff_closure_eq.2 <| (H _ _ _).resolve_left _⟩
  exacts[isClosed_closure, fun c => smul_closure_orbit_subset _ _,
    (orbit_nonempty _).closure.ne_empty]
#align is_minimal_iff_closed_smul_invariant isMinimal_iff_closed_smul_invariant
#align is_minimal_iff_closed_vadd_invariant isMinimal_iff_closed_vadd_invariant

