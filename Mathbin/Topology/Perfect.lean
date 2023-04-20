/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher

! This file was ported from Lean 3 source module topology.perfect
! leanprover-community/mathlib commit 49b7f94aab3a3bdca1f9f34c5d818afb253b3993
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Separation
import Mathbin.Topology.Bases
import Mathbin.Topology.MetricSpace.CantorScheme

/-!
# Perfect Sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.
* `set.scheme β α`: A `β`-scheme on `α`, a collection of subsets of `α` indexed by `list β`.
  Used to construct maps `(β → ℕ) → α` as limiting objects.

## Main Statements

* `perfect.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `exists_countable_union_perfect_of_is_closed`: One version of the **Cantor-Bendixson Theorem**:
  A closed set in a second countable space can be written as the union of a countable set and a
  perfect set.
* `exists_nat_bool_injection_of_perfect_nonempty`: A perfect nonempty set in a complete metric space
  admits an embedding from the Cantor space.

## Implementation Notes

We do not require perfect sets to be nonempty.

We define a nonstandard predicate, `preperfect`, which drops the closed-ness requirement
from the definition of perfect. In T1 spaces, this is equivalent to having a perfect closure,
see `preperfect_iff_perfect_closure`.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, cantor-bendixson.

-/


open Topology Filter

open TopologicalSpace Filter Set

section Basic

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
    simp only [← mem_compl_singleton_iff, @and_comm' _ (_ ∈ C), ← frequently_nhdsWithin_iff,
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
  apply nonempty.closure
  exact ⟨x, ⟨xU, xC⟩⟩
#align perfect.closure_nhds_inter Perfect.closure_nhds_inter

/- warning: perfect.splitting -> Perfect.splitting is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} [_inst_2 : T25Space.{u1} α _inst_1], (Perfect.{u1} α _inst_1 C) -> (Set.Nonempty.{u1} α C) -> (Exists.{succ u1} (Set.{u1} α) (fun (C₀ : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (C₁ : Set.{u1} α) => And (And (Perfect.{u1} α _inst_1 C₀) (And (Set.Nonempty.{u1} α C₀) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) C₀ C))) (And (And (Perfect.{u1} α _inst_1 C₁) (And (Set.Nonempty.{u1} α C₁) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) C₁ C))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) C₀ C₁)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {C : Set.{u1} α} [_inst_2 : T25Space.{u1} α _inst_1], (Perfect.{u1} α _inst_1 C) -> (Set.Nonempty.{u1} α C) -> (Exists.{succ u1} (Set.{u1} α) (fun (C₀ : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (C₁ : Set.{u1} α) => And (And (Perfect.{u1} α _inst_1 C₀) (And (Set.Nonempty.{u1} α C₀) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) C₀ C))) (And (And (Perfect.{u1} α _inst_1 C₁) (And (Set.Nonempty.{u1} α C₁) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) C₁ C))) (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) C₀ C₁)))))
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
    simp only [Union_inter, mem_sep_iff]
    apply countable.bUnion
    · exact countable.mono (inter_subset_left _ _) bct
    · exact inter_subset_right _ _
  refine' ⟨V ∩ C, D, Vct, ⟨_, _⟩, _⟩
  · refine' hclosed.sdiff (isOpen_bunionᵢ fun U => _)
    exact fun ⟨Ub, _⟩ => is_topological_basis.is_open bbasis Ub
  · rw [preperfect_iff_nhds]
    intro x xD E xE
    have : ¬(E ∩ D).Countable := by
      intro h
      obtain ⟨U, hUb, xU, hU⟩ : ∃ U ∈ b, x ∈ U ∧ U ⊆ E :=
        (is_topological_basis.mem_nhds_iff bbasis).mp xE
      have hU_cnt : (U ∩ C).Countable :=
        by
        apply @countable.mono _ _ (E ∩ D ∪ V ∩ C)
        · rintro y ⟨yU, yC⟩
          by_cases y ∈ V
          · exact mem_union_right _ (mem_inter h yC)
          · exact mem_union_left _ (mem_inter (hU yU) ⟨yC, h⟩)
        exact countable.union h Vct
      have : U ∈ v := ⟨hUb, hU_cnt⟩
      apply xD.2
      exact mem_bUnion this xU
    by_contra h
    push_neg  at h
    exact absurd (countable.mono h (Set.countable_singleton _)) this
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

end Basic

section CantorInj

open Function

open ENNReal

variable {α : Type _} [MetricSpace α] {C : Set α} (hC : Perfect C) {ε : ℝ≥0∞}

include hC

private theorem perfect.small_diam_aux (ε_pos : 0 < ε) {x : α} (xC : x ∈ C) :
    let D := closure (EMetric.ball x (ε / 2) ∩ C)
    Perfect D ∧ D.Nonempty ∧ D ⊆ C ∧ EMetric.diam D ≤ ε :=
  by
  have : x ∈ EMetric.ball x (ε / 2) :=
    by
    apply EMetric.mem_ball_self
    rw [ENNReal.div_pos_iff]
    exact ⟨ne_of_gt ε_pos, by norm_num⟩
  have := hC.closure_nhds_inter x xC this EMetric.isOpen_ball
  refine' ⟨this.1, this.2, _, _⟩
  · rw [IsClosed.closure_subset_iff hC.closed]
    apply inter_subset_right
  rw [EMetric.diam_closure]
  apply le_trans (EMetric.diam_mono (inter_subset_left _ _))
  convert EMetric.diam_ball
  rw [mul_comm, ENNReal.div_mul_cancel] <;> norm_num
#align perfect.small_diam_aux perfect.small_diam_aux

variable (hnonempty : C.Nonempty)

include hnonempty

/- warning: perfect.small_diam_splitting -> Perfect.small_diam_splitting is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {C : Set.{u1} α}, (Perfect.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) C) -> (forall {ε : ENNReal}, (Set.Nonempty.{u1} α C) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) ε) -> (Exists.{succ u1} (Set.{u1} α) (fun (C₀ : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (C₁ : Set.{u1} α) => And (And (Perfect.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) C₀) (And (Set.Nonempty.{u1} α C₀) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) C₀ C) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)) C₀) ε)))) (And (And (Perfect.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) C₁) (And (Set.Nonempty.{u1} α C₁) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) C₁ C) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EMetric.diam.{u1} α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1)) C₁) ε)))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) C₀ C₁))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {C : Set.{u1} α}, (Perfect.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) C) -> (forall {ε : ENNReal}, (Set.Nonempty.{u1} α C) -> (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) ε) -> (Exists.{succ u1} (Set.{u1} α) (fun (C₀ : Set.{u1} α) => Exists.{succ u1} (Set.{u1} α) (fun (C₁ : Set.{u1} α) => And (And (Perfect.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) C₀) (And (Set.Nonempty.{u1} α C₀) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) C₀ C) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toEMetricSpace.{u1} α _inst_1)) C₀) ε)))) (And (And (Perfect.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) C₁) (And (Set.Nonempty.{u1} α C₁) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) C₁ C) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (EMetric.diam.{u1} α (EMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toEMetricSpace.{u1} α _inst_1)) C₁) ε)))) (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) C₀ C₁))))))
Case conversion may be inaccurate. Consider using '#align perfect.small_diam_splitting Perfect.small_diam_splittingₓ'. -/
/-- A refinement of `perfect.splitting` for metric spaces, where we also control
the diameter of the new perfect sets. -/
theorem Perfect.small_diam_splitting (ε_pos : 0 < ε) :
    ∃ C₀ C₁ : Set α,
      (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ ⊆ C ∧ EMetric.diam C₀ ≤ ε) ∧
        (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ ⊆ C ∧ EMetric.diam C₁ ≤ ε) ∧ Disjoint C₀ C₁ :=
  by
  rcases hC.splitting hnonempty with ⟨D₀, D₁, ⟨perf0, non0, sub0⟩, ⟨perf1, non1, sub1⟩, hdisj⟩
  cases' non0 with x₀ hx₀
  cases' non1 with x₁ hx₁
  rcases perf0.small_diam_aux ε_pos hx₀ with ⟨perf0', non0', sub0', diam0⟩
  rcases perf1.small_diam_aux ε_pos hx₁ with ⟨perf1', non1', sub1', diam1⟩
  refine'
    ⟨closure (EMetric.ball x₀ (ε / 2) ∩ D₀), closure (EMetric.ball x₁ (ε / 2) ∩ D₁),
      ⟨perf0', non0', sub0'.trans sub0, diam0⟩, ⟨perf1', non1', sub1'.trans sub1, diam1⟩, _⟩
  apply Disjoint.mono _ _ hdisj <;> assumption
#align perfect.small_diam_splitting Perfect.small_diam_splitting

open CantorScheme

/- warning: perfect.exists_nat_bool_injection -> Perfect.exists_nat_bool_injection is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {C : Set.{u1} α}, (Perfect.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) C) -> (Set.Nonempty.{u1} α C) -> (forall [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))], Exists.{succ u1} ((Nat -> Bool) -> α) (fun (f : (Nat -> Bool) -> α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.range.{u1, 1} α (Nat -> Bool) f) C) (And (Continuous.{0, u1} (Nat -> Bool) α (Pi.topologicalSpace.{0, 0} Nat (fun (ᾰ : Nat) => Bool) (fun (a : Nat) => Bool.topologicalSpace)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) f) (Function.Injective.{1, succ u1} (Nat -> Bool) α f))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MetricSpace.{u1} α] {C : Set.{u1} α}, (Perfect.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) C) -> (Set.Nonempty.{u1} α C) -> (forall [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))], Exists.{succ u1} ((Nat -> Bool) -> α) (fun (f : (Nat -> Bool) -> α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.range.{u1, 1} α (Nat -> Bool) f) C) (And (Continuous.{0, u1} (Nat -> Bool) α (Pi.topologicalSpace.{0, 0} Nat (fun (ᾰ : Nat) => Bool) (fun (a : Nat) => instTopologicalSpaceBool)) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (MetricSpace.toPseudoMetricSpace.{u1} α _inst_1))) f) (Function.Injective.{1, succ u1} (Nat -> Bool) α f))))
Case conversion may be inaccurate. Consider using '#align perfect.exists_nat_bool_injection Perfect.exists_nat_bool_injectionₓ'. -/
/-- Any nonempty perfect set in a complete metric space admits a continuous injection
from the cantor space, `ℕ → bool`. -/
theorem Perfect.exists_nat_bool_injection [CompleteSpace α] :
    ∃ f : (ℕ → Bool) → α, range f ⊆ C ∧ Continuous f ∧ Injective f :=
  by
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  have upos := fun n => (upos' n).1
  let P := Subtype fun E : Set α => Perfect E ∧ E.Nonempty
  choose C0 C1 h0 h1 hdisj using
    fun {C : Set α} (hC : Perfect C) (hnonempty : C.Nonempty) {ε : ℝ≥0∞} (hε : 0 < ε) =>
    hC.small_diam_splitting hnonempty hε
  let DP : List Bool → P := fun l => by
    induction' l with a l ih; · exact ⟨C, ⟨hC, hnonempty⟩⟩
    cases a
    · use C0 ih.property.1 ih.property.2 (upos l.length.succ)
      exact ⟨(h0 _ _ _).1, (h0 _ _ _).2.1⟩
    use C1 ih.property.1 ih.property.2 (upos l.length.succ)
    exact ⟨(h1 _ _ _).1, (h1 _ _ _).2.1⟩
  let D : List Bool → Set α := fun l => (DP l).val
  have hanti : closure_antitone D :=
    by
    refine' antitone.closure_antitone _ fun l => (DP l).property.1.closed
    intro l a
    cases a
    · exact (h0 _ _ _).2.2.1
    exact (h1 _ _ _).2.2.1
  have hdiam : vanishing_diam D := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · simp
    rw [eventually_at_top]
    refine' ⟨1, fun m (hm : 1 ≤ m) => _⟩
    rw [Nat.one_le_iff_ne_zero] at hm
    rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨n, rfl⟩
    dsimp
    cases x n
    · convert(h0 _ _ _).2.2.2
      rw [PiNat.res_length]
    convert(h1 _ _ _).2.2.2
    rw [PiNat.res_length]
  have hdisj' : CantorScheme.Disjoint D :=
    by
    rintro l (a | a) (b | b) hab <;> try contradiction
    · exact hdisj _ _ _
    exact (hdisj _ _ _).symm
  have hdom : ∀ {x : ℕ → Bool}, x ∈ ([anonymous] D).1 := fun x => by
    simp [hanti.map_of_vanishing_diam hdiam fun l => (DP l).property.2]
  refine' ⟨fun x => ([anonymous] D).2 ⟨x, hdom⟩, _, _, _⟩
  · rintro y ⟨x, rfl⟩
    exact map_mem ⟨_, hdom⟩ 0
  · continuity
    exact hdiam.map_continuous
  intro x y hxy
  simpa only [← Subtype.val_inj] using hdisj'.map_injective hxy
#align perfect.exists_nat_bool_injection Perfect.exists_nat_bool_injection

end CantorInj

