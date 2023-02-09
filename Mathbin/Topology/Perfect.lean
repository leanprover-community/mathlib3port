/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher

! This file was ported from Lean 3 source module topology.perfect
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Separation
import Mathbin.Topology.Bases

/-!
# Perfect Sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.

## Main Statements

* `perfect.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `exists_countable_union_perfect_of_is_closed`: One version of the **Cantor-Bendixson Theorem**:
  A closed set in a second countable space can be written as the union of a countable set and a
  perfect set.

## Implementation Notes

We do not require perfect sets to be nonempty.

We define a nonstandard predicate, `preperfect`, which drops the closed-ness requirement
from the definition of perfect. In T1 spaces, this is equivalent to having a perfect closure,
see `preperfect_iff_perfect_closure`.

## References

* [kechris1995] (Chapter 6)

## Tags

accumulation point, perfect set, Cantor-Bendixson.

-/


open Topology Filter

open TopologicalSpace Filter Set

variable {α : Type _} [TopologicalSpace α] {C : Set α}

/- warning: acc_pt.nhds_inter -> AccPt.nhds_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} {x : α} {U : Set.{u1} α}, (AccPt.{u1} α _inst_1 x (Filter.principal.{u1} α C)) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (AccPt.{u1} α _inst_1 x (Filter.principal.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U C)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} {x : α} {U : Set.{u1} α}, (AccPt.{u1} α _inst_1 x (Filter.principal.{u1} α C)) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (AccPt.{u1} α _inst_1 x (Filter.principal.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U C)))
Case conversion may be inaccurate. Consider using '#align acc_pt.nhds_inter AccPt.nhds_interₓ'. -/
/-- If `x` is an accumulation point of a set `C` and `U` is a neighborhood of `x`,
then `x` is an accumulation point of `U ∩ C`. -/
theorem AccPt.nhds_inter {x : α} {U : Set α} (h_acc : AccPt x (𝓟 C)) (hU : U ∈ 𝓝 x) :
    AccPt x (𝓟 (U ∩ C)) :=
  by
  have : 𝓝[≠] x ≤ 𝓟 U := by
    rw [le_principal_iff]
    exact mem_nhdsWithin_of_mem_nhds hU
  rw [AccPt, ← inf_principal, ← inf_assoc, inf_of_le_left this]
  exact h_acc
#align acc_pt.nhds_inter AccPt.nhds_inter

#print Preperfect /-
/-- A set `C` is preperfect if all of its points are accumulation points of itself.
If `C` is nonempty and `α` is a T1 space, this is equivalent to the closure of `C` being perfect.
See `preperfect_iff_perfect_closure`.-/
def Preperfect (C : Set α) : Prop :=
  ∀ x ∈ C, AccPt x (𝓟 C)
#align preperfect Preperfect
-/

#print Perfect /-
/-- A set `C` is called perfect if it is closed and all of its
points are accumulation points of itself.
Note that we do not require `C` to be nonempty.-/
structure Perfect (C : Set α) : Prop where
  closed : IsClosed C
  Acc : Preperfect C
#align perfect Perfect
-/

/- warning: preperfect_iff_nhds -> preperfect_iff_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α}, Iff (Preperfect.{u1} α _inst_1 C) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x C) -> (forall (U : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U C)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U C)) => Ne.{succ u1} α y x)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α}, Iff (Preperfect.{u1} α _inst_1 C) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x C) -> (forall (U : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) U (nhds.{u1} α _inst_1 x)) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U C)) (Ne.{succ u1} α y x)))))
Case conversion may be inaccurate. Consider using '#align preperfect_iff_nhds preperfect_iff_nhdsₓ'. -/
theorem preperfect_iff_nhds : Preperfect C ↔ ∀ x ∈ C, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := by
  simp only [Preperfect, accPt_iff_nhds]
#align preperfect_iff_nhds preperfect_iff_nhds

/- warning: preperfect.open_inter -> Preperfect.open_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} {U : Set.{u1} α}, (Preperfect.{u1} α _inst_1 C) -> (IsOpen.{u1} α _inst_1 U) -> (Preperfect.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U C))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} {U : Set.{u1} α}, (Preperfect.{u1} α _inst_1 C) -> (IsOpen.{u1} α _inst_1 U) -> (Preperfect.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U C))
Case conversion may be inaccurate. Consider using '#align preperfect.open_inter Preperfect.open_interₓ'. -/
/-- The intersection of a preperfect set and an open set is preperfect-/
theorem Preperfect.open_inter {U : Set α} (hC : Preperfect C) (hU : IsOpen U) :
    Preperfect (U ∩ C) := by
  rintro x ⟨xU, xC⟩
  apply (hC _ xC).nhds_inter
  exact hU.mem_nhds xU
#align preperfect.open_inter Preperfect.open_inter

#print Preperfect.perfect_closure /-
/-- The closure of a preperfect set is perfect.
For a converse, see `preperfect_iff_perfect_closure`-/
theorem Preperfect.perfect_closure (hC : Preperfect C) : Perfect (closure C) :=
  by
  constructor; · exact isClosed_closure
  intro x hx
  by_cases h : x ∈ C <;> apply AccPt.mono _ (principal_mono.mpr subset_closure)
  · exact hC _ h
  have : {x}ᶜ ∩ C = C := by simp [h]
  rw [AccPt, nhdsWithin, inf_assoc, inf_principal, this]
  rw [closure_eq_cluster_pts] at hx
  exact hx
#align preperfect.perfect_closure Preperfect.perfect_closure
-/

#print preperfect_iff_perfect_closure /-
/-- In a T1 space, being preperfect is equivalent to having perfect closure.-/
theorem preperfect_iff_perfect_closure [T1Space α] : Preperfect C ↔ Perfect (closure C) :=
  by
  constructor <;> intro h
  · exact h.perfect_closure
  intro x xC
  have H : AccPt x (𝓟 (closure C)) := h.acc _ (subset_closure xC)
  rw [accPt_iff_frequently] at *
  have : ∀ y, y ≠ x ∧ y ∈ closure C → ∃ᶠ z in 𝓝 y, z ≠ x ∧ z ∈ C :=
    by
    rintro y ⟨hyx, yC⟩
    simp only [← mem_compl_singleton_iff, @and_comm _ (_ ∈ C), ← frequently_nhdsWithin_iff,
      hyx.nhds_within_compl_singleton, ← mem_closure_iff_frequently]
    exact yC
  rw [← frequently_frequently_nhds]
  exact H.mono this
#align preperfect_iff_perfect_closure preperfect_iff_perfect_closure
-/

/- warning: perfect.closure_nhds_inter -> Perfect.closure_nhds_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} {U : Set.{u1} α}, (Perfect.{u1} α _inst_1 C) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x C) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x U) -> (IsOpen.{u1} α _inst_1 U) -> (And (Perfect.{u1} α _inst_1 (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U C))) (Set.Nonempty.{u1} α (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) U C)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} {U : Set.{u1} α}, (Perfect.{u1} α _inst_1 C) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x C) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x U) -> (IsOpen.{u1} α _inst_1 U) -> (And (Perfect.{u1} α _inst_1 (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U C))) (Set.Nonempty.{u1} α (closure.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) U C)))))
Case conversion may be inaccurate. Consider using '#align perfect.closure_nhds_inter Perfect.closure_nhds_interₓ'. -/
theorem Perfect.closure_nhds_inter {U : Set α} (hC : Perfect C) (x : α) (xC : x ∈ C) (xU : x ∈ U)
    (Uop : IsOpen U) : Perfect (closure (U ∩ C)) ∧ (closure (U ∩ C)).Nonempty :=
  by
  constructor
  · apply Preperfect.perfect_closure
    exact hC.acc.open_inter Uop
  apply Nonempty.closure
  exact ⟨x, ⟨xU, xC⟩⟩
#align perfect.closure_nhds_inter Perfect.closure_nhds_inter

/- warning: perfect.splitting -> Perfect.splitting is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} [_inst_2 : T25Space.{u1} α _inst_1], (Perfect.{u1} α _inst_1 C) -> (Set.Nonempty.{u1} α C) -> (Exists.{succ u1} (Set.{u1} α) (fun (C₀ : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (C₁ : Set.{u1} α) => And (And (Perfect.{u1} α _inst_1 C₀) (And (Set.Nonempty.{u1} α C₀) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) C₀ C))) (And (And (Perfect.{u1} α _inst_1 C₁) (And (Set.Nonempty.{u1} α C₁) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) C₁ C))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) C₀ C₁)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} [_inst_2 : T25Space.{u1} α _inst_1], (Perfect.{u1} α _inst_1 C) -> (Set.Nonempty.{u1} α C) -> (Exists.{succ u1} (Set.{u1} α) (fun (C₀ : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (C₁ : Set.{u1} α) => And (And (Perfect.{u1} α _inst_1 C₀) (And (Set.Nonempty.{u1} α C₀) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) C₀ C))) (And (And (Perfect.{u1} α _inst_1 C₁) (And (Set.Nonempty.{u1} α C₁) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) C₁ C))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) C₀ C₁)))))
Case conversion may be inaccurate. Consider using '#align perfect.splitting Perfect.splittingₓ'. -/
/-- Given a perfect nonempty set in a T2.5 space, we can find two disjoint perfect subsets
This is the main inductive step in the proof of the Cantor-Bendixson Theorem-/
theorem Perfect.splitting [T25Space α] (hC : Perfect C) (hnonempty : C.Nonempty) :
    ∃ C₀ C₁ : Set α,
      (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ ⊆ C) ∧ (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ ⊆ C) ∧ Disjoint C₀ C₁ :=
  by
  cases' hnonempty with y yC
  obtain ⟨x, xC, hxy⟩ : ∃ x ∈ C, x ≠ y :=
    by
    have := hC.acc _ yC
    rw [accPt_iff_nhds] at this
    rcases this univ univ_mem with ⟨x, xC, hxy⟩
    exact ⟨x, xC.2, hxy⟩
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy
  use closure (U ∩ C), closure (V ∩ C)
  constructor <;> rw [← and_assoc']
  · refine' ⟨hC.closure_nhds_inter x xC xU Uop, _⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right _ _
  constructor
  · refine' ⟨hC.closure_nhds_inter y yC yV Vop, _⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right _ _
  apply Disjoint.mono _ _ hUV <;> apply closure_mono <;> exact inter_subset_left _ _
#align perfect.splitting Perfect.splitting

section Kernel

/- warning: exists_countable_union_perfect_of_is_closed -> exists_countable_union_perfect_of_isClosed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} [_inst_2 : TopologicalSpace.SecondCountableTopology.{u1} α _inst_1], (IsClosed.{u1} α _inst_1 C) -> (Exists.{succ u1} (Set.{u1} α) (fun (V : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (D : Set.{u1} α) => And (Set.Countable.{u1} α V) (And (Perfect.{u1} α _inst_1 D) (Eq.{succ u1} (Set.{u1} α) C (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) V D))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} [_inst_2 : TopologicalSpace.SecondCountableTopology.{u1} α _inst_1], (IsClosed.{u1} α _inst_1 C) -> (Exists.{succ u1} (Set.{u1} α) (fun (V : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (D : Set.{u1} α) => And (Set.Countable.{u1} α V) (And (Perfect.{u1} α _inst_1 D) (Eq.{succ u1} (Set.{u1} α) C (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) V D))))))
Case conversion may be inaccurate. Consider using '#align exists_countable_union_perfect_of_is_closed exists_countable_union_perfect_of_isClosedₓ'. -/
/-- The **Cantor-Bendixson Theorem**: Any closed subset of a second countable space
can be written as the union of a countable set and a perfect set.-/
theorem exists_countable_union_perfect_of_isClosed [SecondCountableTopology α]
    (hclosed : IsClosed C) : ∃ V D : Set α, V.Countable ∧ Perfect D ∧ C = V ∪ D :=
  by
  obtain ⟨b, bct, bnontrivial, bbasis⟩ := TopologicalSpace.exists_countable_basis α
  let v := { U ∈ b | (U ∩ C).Countable }
  let V := ⋃ U ∈ v, U
  let D := C \ V
  have Vct : (V ∩ C).Countable :=
    by
    simp only [unionᵢ_inter, mem_sep_iff]
    apply Countable.bunionᵢ
    · exact Countable.mono (inter_subset_left _ _) bct
    · exact inter_subset_right _ _
  refine' ⟨V ∩ C, D, Vct, ⟨_, _⟩, _⟩
  · refine' hclosed.sdiff (isOpen_bunionᵢ fun U => _)
    exact fun ⟨Ub, _⟩ => IsTopologicalBasis.isOpen bbasis Ub
  · rw [preperfect_iff_nhds]
    intro x xD E xE
    have : ¬(E ∩ D).Countable := by
      intro h
      obtain ⟨U, hUb, xU, hU⟩ : ∃ U ∈ b, x ∈ U ∧ U ⊆ E :=
        (IsTopologicalBasis.mem_nhds_iff bbasis).mp xE
      have hU_cnt : (U ∩ C).Countable :=
        by
        apply @countable.mono _ _ (E ∩ D ∪ V ∩ C)
        · rintro y ⟨yU, yC⟩
          by_cases y ∈ V
          · exact mem_union_right _ (mem_inter h yC)
          · exact mem_union_left _ (mem_inter (hU yU) ⟨yC, h⟩)
        exact Countable.union h Vct
      have : U ∈ v := ⟨hUb, hU_cnt⟩
      apply xD.2
      exact mem_bunionᵢ this xU
    by_contra h
    push_neg  at h
    exact absurd (Countable.mono h (Set.countable_singleton _)) this
  · rw [inter_comm, inter_union_diff]
#align exists_countable_union_perfect_of_is_closed exists_countable_union_perfect_of_isClosed

#print exists_perfect_nonempty_of_isClosed_of_not_countable /-
/-- Any uncountable closed set in a second countable space contains a nonempty perfect subset.-/
theorem exists_perfect_nonempty_of_isClosed_of_not_countable [SecondCountableTopology α]
    (hclosed : IsClosed C) (hunc : ¬C.Countable) : ∃ D : Set α, Perfect D ∧ D.Nonempty ∧ D ⊆ C :=
  by
  rcases exists_countable_union_perfect_of_isClosed hclosed with ⟨V, D, Vct, Dperf, VD⟩
  refine' ⟨D, ⟨Dperf, _⟩⟩
  constructor
  · rw [nonempty_iff_ne_empty]
    by_contra
    rw [h, union_empty] at VD
    rw [VD] at hunc
    contradiction
  rw [VD]
  exact subset_union_right _ _
#align exists_perfect_nonempty_of_is_closed_of_not_countable exists_perfect_nonempty_of_isClosed_of_not_countable
-/

end Kernel

