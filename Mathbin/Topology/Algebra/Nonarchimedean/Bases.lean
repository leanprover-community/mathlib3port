/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.nonarchimedean.bases
! leanprover-community/mathlib commit ce38d86c0b2d427ce208c3cee3159cb421d2b3c4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Nonarchimedean.Basic
import Mathbin.Topology.Algebra.FilterBasis
import Mathbin.Algebra.Module.Submodule.Pointwise

/-!
# Neighborhood bases for non-archimedean rings and modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This files contains special families of filter bases on rings and modules that give rise to
non-archimedean topologies.

The main definition is `ring_subgroups_basis` which is a predicate on a family of
additive subgroups of a ring. The predicate ensures there is a topology
`ring_subgroups_basis.topology` which is compatible with a ring structure and admits the given
family as a basis of neighborhoods of zero. In particular the given subgroups become open subgroups
(bundled in `ring_subgroups_basis.open_add_subgroup`) and we get a non-archimedean topological ring
(`ring_subgroups_basis.nonarchimedean`).

A special case of this construction is given by `submodules_basis` where the subgroups are
sub-modules in a commutative algebra. This important example gives rises to the adic topology
(studied in its own file).

-/


open Set Filter Function Lattice AddGroupWithZeroNhd

open Topology Filter Pointwise

/- warning: ring_subgroups_basis -> RingSubgroupsBasis is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A], (ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))) -> Prop
but is expected to have type
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A], (ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (Ring.toAddGroupWithOne.{u1} A _inst_1)))) -> Prop
Case conversion may be inaccurate. Consider using '#align ring_subgroups_basis RingSubgroupsBasisₓ'. -/
/-- A family of additive subgroups on a ring `A` is a subgroups basis if it satisfies some
axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure RingSubgroupsBasis {A ι : Type _} [Ring A] (B : ι → AddSubgroup A) : Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i
  leftMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (fun y : A => x * y) ⁻¹' B i
  rightMul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (fun y : A => y * x) ⁻¹' B i
#align ring_subgroups_basis RingSubgroupsBasis

namespace RingSubgroupsBasis

variable {A ι : Type _} [Ring A]

/- warning: ring_subgroups_basis.of_comm -> RingSubgroupsBasis.of_comm is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_2 : CommRing.{u1} A] (B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2)))))), (forall (i : ι) (j : ι), Exists.{succ u2} ι (fun (k : ι) => LE.le.{u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Preorder.toHasLe.{u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (PartialOrder.toPreorder.{u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (SetLike.partialOrder.{u1, u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) A (AddSubgroup.setLike.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2)))))))) (B k) (Inf.inf.{u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (AddSubgroup.hasInf.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (B i) (B j)))) -> (forall (i : ι), Exists.{succ u2} ι (fun (j : ι) => HasSubset.Subset.{u1} (Set.{u1} A) (Set.hasSubset.{u1} A) (HMul.hMul.{u1, u1, u1} (Set.{u1} A) (Set.{u1} A) (Set.{u1} A) (instHMul.{u1} (Set.{u1} A) (Set.mul.{u1} A (Distrib.toHasMul.{u1} A (Ring.toDistrib.{u1} A (CommRing.toRing.{u1} A _inst_2))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) A (AddSubgroup.setLike.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2)))))))) (B j)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) A (AddSubgroup.setLike.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2)))))))) (B j))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) A (AddSubgroup.setLike.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2)))))))) (B i)))) -> (forall (x : A) (i : ι), Exists.{succ u2} ι (fun (j : ι) => HasSubset.Subset.{u1} (Set.{u1} A) (Set.hasSubset.{u1} A) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) A (AddSubgroup.setLike.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2)))))))) (B j)) (Set.preimage.{u1, u1} A A (fun (y : A) => HMul.hMul.{u1, u1, u1} A A A (instHMul.{u1} A (Distrib.toHasMul.{u1} A (Ring.toDistrib.{u1} A (CommRing.toRing.{u1} A _inst_2)))) x y) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Set.{u1} A) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2))))) A (AddSubgroup.setLike.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A (CommRing.toRing.{u1} A _inst_2)))))))) (B i))))) -> (RingSubgroupsBasis.{u1, u2} A ι (CommRing.toRing.{u1} A _inst_2) B)
but is expected to have type
  forall {A : Type.{u2}} {ι : Type.{u1}} [_inst_2 : CommRing.{u2} A] (B : ι -> (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2))))), (forall (i : ι) (j : ι), Exists.{succ u1} ι (fun (k : ι) => LE.le.{u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (Preorder.toLE.{u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (PartialOrder.toPreorder.{u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (OmegaCompletePartialOrder.toPartialOrder.{u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (AddSubgroup.instCompleteLatticeAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))))))) (B k) (Inf.inf.{u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (AddSubgroup.instInfAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (B i) (B j)))) -> (forall (i : ι), Exists.{succ u1} ι (fun (j : ι) => HasSubset.Subset.{u2} (Set.{u2} A) (Set.instHasSubsetSet.{u2} A) (HMul.hMul.{u2, u2, u2} (Set.{u2} A) (Set.{u2} A) (Set.{u2} A) (instHMul.{u2} (Set.{u2} A) (Set.mul.{u2} A (NonUnitalNonAssocRing.toMul.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_2)))))) (SetLike.coe.{u2, u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) A (AddSubgroup.instSetLikeAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (B j)) (SetLike.coe.{u2, u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) A (AddSubgroup.instSetLikeAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (B j))) (SetLike.coe.{u2, u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) A (AddSubgroup.instSetLikeAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (B i)))) -> (forall (x : A) (i : ι), Exists.{succ u1} ι (fun (j : ι) => HasSubset.Subset.{u2} (Set.{u2} A) (Set.instHasSubsetSet.{u2} A) (SetLike.coe.{u2, u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) A (AddSubgroup.instSetLikeAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (B j)) (Set.preimage.{u2, u2} A A (fun (y : A) => HMul.hMul.{u2, u2, u2} A A A (instHMul.{u2} A (NonUnitalNonAssocRing.toMul.{u2} A (NonAssocRing.toNonUnitalNonAssocRing.{u2} A (Ring.toNonAssocRing.{u2} A (CommRing.toRing.{u2} A _inst_2))))) x y) (SetLike.coe.{u2, u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) A (AddSubgroup.instSetLikeAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A (CommRing.toRing.{u2} A _inst_2)))) (B i))))) -> (RingSubgroupsBasis.{u2, u1} A ι (CommRing.toRing.{u2} A _inst_2) B)
Case conversion may be inaccurate. Consider using '#align ring_subgroups_basis.of_comm RingSubgroupsBasis.of_commₓ'. -/
theorem of_comm {A ι : Type _} [CommRing A] (B : ι → AddSubgroup A)
    (inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j) (mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i)
    (left_mul : ∀ x : A, ∀ i, ∃ j, (B j : Set A) ⊆ (fun y : A => x * y) ⁻¹' B i) :
    RingSubgroupsBasis B :=
  { inter
    mul
    leftMul
    rightMul := by
      intro x i
      cases' leftMul x i with j hj
      use j
      simpa [mul_comm] using hj }
#align ring_subgroups_basis.of_comm RingSubgroupsBasis.of_comm

/- warning: ring_subgroups_basis.to_ring_filter_basis -> RingSubgroupsBasis.toRingFilterBasis is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))}, (RingSubgroupsBasis.{u1, u2} A ι _inst_1 B) -> (RingFilterBasis.{u1} A _inst_1)
but is expected to have type
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (Ring.toAddGroupWithOne.{u1} A _inst_1)))}, (RingSubgroupsBasis.{u1, u2} A ι _inst_1 B) -> (RingFilterBasis.{u1} A _inst_1)
Case conversion may be inaccurate. Consider using '#align ring_subgroups_basis.to_ring_filter_basis RingSubgroupsBasis.toRingFilterBasisₓ'. -/
/-- Every subgroups basis on a ring leads to a ring filter basis. -/
def toRingFilterBasis [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B) :
    RingFilterBasis A where
  sets := { U | ∃ i, U = B i }
  Nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    cases' hB.inter i j with k hk
    use B k, k, rfl, hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i, i, rfl
    rintro x ⟨y, z, y_in, z_in, rfl⟩
    exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i, i, rfl
    intro x x_in
    exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i, i, rfl
    simp
  mul' := by
    rintro _ ⟨i, rfl⟩
    cases' hB.mul i with k hk
    use B k, k, rfl, hk
  mul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    cases' hB.left_mul x₀ i with k hk
    use B k, k, rfl, hk
  mul_right' := by
    rintro x₀ _ ⟨i, rfl⟩
    cases' hB.right_mul x₀ i with k hk
    use B k, k, rfl, hk
#align ring_subgroups_basis.to_ring_filter_basis RingSubgroupsBasis.toRingFilterBasis

variable [Nonempty ι] {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B)

/- warning: ring_subgroups_basis.mem_add_group_filter_basis_iff -> RingSubgroupsBasis.mem_addGroupFilterBasis_iff is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))} (hB : RingSubgroupsBasis.{u1, u2} A ι _inst_1 B) {V : Set.{u1} A}, Iff (Membership.Mem.{u1, u1} (Set.{u1} A) (AddGroupFilterBasis.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (AddGroupFilterBasis.hasMem.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) V (RingFilterBasis.toAddGroupFilterBasis.{u1} A _inst_1 (RingSubgroupsBasis.toRingFilterBasis.{u1, u2} A ι _inst_1 _inst_2 B hB))) (Exists.{succ u2} ι (fun (i : ι) => Eq.{succ u1} (Set.{u1} A) V ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (Set.{u1} A) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (Set.{u1} A) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (Set.{u1} A) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) A (AddSubgroup.setLike.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))))) (B i))))
but is expected to have type
  forall {A : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Ring.{u2} A] [_inst_2 : Nonempty.{succ u1} ι] {B : ι -> (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1)))} (hB : RingSubgroupsBasis.{u2, u1} A ι _inst_1 B) {V : Set.{u2} A}, Iff (Membership.mem.{u2, u2} (Set.{u2} A) (AddGroupFilterBasis.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) (AddGroupFilterBasis.instMembershipSetAddGroupFilterBasis.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) V (RingFilterBasis.toAddGroupFilterBasis.{u2} A _inst_1 (RingSubgroupsBasis.toRingFilterBasis.{u2, u1} A ι _inst_1 _inst_2 B hB))) (Exists.{succ u1} ι (fun (i : ι) => Eq.{succ u2} (Set.{u2} A) V (SetLike.coe.{u2, u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) A (AddSubgroup.instSetLikeAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) (B i))))
Case conversion may be inaccurate. Consider using '#align ring_subgroups_basis.mem_add_group_filter_basis_iff RingSubgroupsBasis.mem_addGroupFilterBasis_iffₓ'. -/
theorem mem_addGroupFilterBasis_iff {V : Set A} :
    V ∈ hB.toRingFilterBasis.toAddGroupFilterBasis ↔ ∃ i, V = B i :=
  Iff.rfl
#align ring_subgroups_basis.mem_add_group_filter_basis_iff RingSubgroupsBasis.mem_addGroupFilterBasis_iff

/- warning: ring_subgroups_basis.mem_add_group_filter_basis -> RingSubgroupsBasis.mem_addGroupFilterBasis is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))} (hB : RingSubgroupsBasis.{u1, u2} A ι _inst_1 B) (i : ι), Membership.Mem.{u1, u1} (Set.{u1} A) (AddGroupFilterBasis.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (AddGroupFilterBasis.hasMem.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (Set.{u1} A) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (Set.{u1} A) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (Set.{u1} A) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) A (AddSubgroup.setLike.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))))) (B i)) (RingFilterBasis.toAddGroupFilterBasis.{u1} A _inst_1 (RingSubgroupsBasis.toRingFilterBasis.{u1, u2} A ι _inst_1 _inst_2 B hB))
but is expected to have type
  forall {A : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Ring.{u2} A] [_inst_2 : Nonempty.{succ u1} ι] {B : ι -> (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1)))} (hB : RingSubgroupsBasis.{u2, u1} A ι _inst_1 B) (i : ι), Membership.mem.{u2, u2} (Set.{u2} A) (AddGroupFilterBasis.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) (AddGroupFilterBasis.instMembershipSetAddGroupFilterBasis.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) (SetLike.coe.{u2, u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) A (AddSubgroup.instSetLikeAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) (B i)) (RingFilterBasis.toAddGroupFilterBasis.{u2} A _inst_1 (RingSubgroupsBasis.toRingFilterBasis.{u2, u1} A ι _inst_1 _inst_2 B hB))
Case conversion may be inaccurate. Consider using '#align ring_subgroups_basis.mem_add_group_filter_basis RingSubgroupsBasis.mem_addGroupFilterBasisₓ'. -/
theorem mem_addGroupFilterBasis (i) : (B i : Set A) ∈ hB.toRingFilterBasis.toAddGroupFilterBasis :=
  ⟨i, rfl⟩
#align ring_subgroups_basis.mem_add_group_filter_basis RingSubgroupsBasis.mem_addGroupFilterBasis

/- warning: ring_subgroups_basis.topology -> RingSubgroupsBasis.topology is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))}, (RingSubgroupsBasis.{u1, u2} A ι _inst_1 B) -> (TopologicalSpace.{u1} A)
but is expected to have type
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (Ring.toAddGroupWithOne.{u1} A _inst_1)))}, (RingSubgroupsBasis.{u1, u2} A ι _inst_1 B) -> (TopologicalSpace.{u1} A)
Case conversion may be inaccurate. Consider using '#align ring_subgroups_basis.topology RingSubgroupsBasis.topologyₓ'. -/
/-- The topology defined from a subgroups basis, admitting the given subgroups as a basis
of neighborhoods of zero. -/
def topology : TopologicalSpace A :=
  hB.toRingFilterBasis.toAddGroupFilterBasis.topology
#align ring_subgroups_basis.topology RingSubgroupsBasis.topology

/- warning: ring_subgroups_basis.has_basis_nhds_zero -> RingSubgroupsBasis.hasBasis_nhds_zero is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))} (hB : RingSubgroupsBasis.{u1, u2} A ι _inst_1 B), Filter.HasBasis.{u1, succ u2} A ι (nhds.{u1} A (RingSubgroupsBasis.topology.{u1, u2} A ι _inst_1 _inst_2 B hB) (OfNat.ofNat.{u1} A 0 (OfNat.mk.{u1} A 0 (Zero.zero.{u1} A (MulZeroClass.toHasZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A _inst_1))))))))) (fun (_x : ι) => True) (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (Set.{u1} A) (HasLiftT.mk.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (Set.{u1} A) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (Set.{u1} A) (SetLike.Set.hasCoeT.{u1, u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) A (AddSubgroup.setLike.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))))) (B i))
but is expected to have type
  forall {A : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Ring.{u2} A] [_inst_2 : Nonempty.{succ u1} ι] {B : ι -> (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1)))} (hB : RingSubgroupsBasis.{u2, u1} A ι _inst_1 B), Filter.HasBasis.{u2, succ u1} A ι (nhds.{u2} A (RingSubgroupsBasis.topology.{u2, u1} A ι _inst_1 _inst_2 B hB) (OfNat.ofNat.{u2} A 0 (Zero.toOfNat0.{u2} A (MonoidWithZero.toZero.{u2} A (Semiring.toMonoidWithZero.{u2} A (Ring.toSemiring.{u2} A _inst_1)))))) (fun (_x : ι) => True) (fun (i : ι) => SetLike.coe.{u2, u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) A (AddSubgroup.instSetLikeAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) (B i))
Case conversion may be inaccurate. Consider using '#align ring_subgroups_basis.has_basis_nhds_zero RingSubgroupsBasis.hasBasis_nhds_zeroₓ'. -/
theorem hasBasis_nhds_zero : HasBasis (@nhds A hB.topology 0) (fun _ => True) fun i => B i :=
  ⟨by
    intro s
    rw [hB.to_ring_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      exact ⟨i, trivial, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨B i, ⟨i, rfl⟩, hi⟩⟩
#align ring_subgroups_basis.has_basis_nhds_zero RingSubgroupsBasis.hasBasis_nhds_zero

/- warning: ring_subgroups_basis.has_basis_nhds -> RingSubgroupsBasis.hasBasis_nhds is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))} (hB : RingSubgroupsBasis.{u1, u2} A ι _inst_1 B) (a : A), Filter.HasBasis.{u1, succ u2} A ι (nhds.{u1} A (RingSubgroupsBasis.topology.{u1, u2} A ι _inst_1 _inst_2 B hB) a) (fun (_x : ι) => True) (fun (i : ι) => setOf.{u1} A (fun (b : A) => Membership.Mem.{u1, u1} A (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) (SetLike.hasMem.{u1, u1} (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))) A (AddSubgroup.setLike.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))) (HSub.hSub.{u1, u1, u1} A A A (instHSub.{u1} A (SubNegMonoid.toHasSub.{u1} A (AddGroup.toSubNegMonoid.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1)))))) b a) (B i)))
but is expected to have type
  forall {A : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Ring.{u2} A] [_inst_2 : Nonempty.{succ u1} ι] {B : ι -> (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1)))} (hB : RingSubgroupsBasis.{u2, u1} A ι _inst_1 B) (a : A), Filter.HasBasis.{u2, succ u1} A ι (nhds.{u2} A (RingSubgroupsBasis.topology.{u2, u1} A ι _inst_1 _inst_2 B hB) a) (fun (_x : ι) => True) (fun (i : ι) => setOf.{u2} A (fun (b : A) => Membership.mem.{u2, u2} A (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) (SetLike.instMembership.{u2, u2} (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1))) A (AddSubgroup.instSetLikeAddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1)))) (HSub.hSub.{u2, u2, u2} A A A (instHSub.{u2} A (Ring.toSub.{u2} A _inst_1)) b a) (B i)))
Case conversion may be inaccurate. Consider using '#align ring_subgroups_basis.has_basis_nhds RingSubgroupsBasis.hasBasis_nhdsₓ'. -/
theorem hasBasis_nhds (a : A) :
    HasBasis (@nhds A hB.topology a) (fun _ => True) fun i => { b | b - a ∈ B i } :=
  ⟨by
    intro s
    rw [(hB.to_ring_filter_basis.to_add_group_filter_basis.nhds_has_basis a).mem_iff]
    simp only [exists_prop, exists_true_left]
    constructor
    · rintro ⟨-, ⟨i, rfl⟩, hi⟩
      use i
      convert hi
      ext b
      constructor
      · intro h
        use b - a, h
        abel
      · rintro ⟨c, hc, rfl⟩
        simpa using hc
    · rintro ⟨i, hi⟩
      use B i, i, rfl
      rw [image_subset_iff]
      rintro b b_in
      apply hi
      simpa using b_in⟩
#align ring_subgroups_basis.has_basis_nhds RingSubgroupsBasis.hasBasis_nhds

/- warning: ring_subgroups_basis.open_add_subgroup -> RingSubgroupsBasis.openAddSubgroup is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))} (hB : RingSubgroupsBasis.{u1, u2} A ι _inst_1 B), ι -> (OpenAddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))) (RingSubgroupsBasis.topology.{u1, u2} A ι _inst_1 _inst_2 B hB))
but is expected to have type
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (Ring.toAddGroupWithOne.{u1} A _inst_1)))} (hB : RingSubgroupsBasis.{u1, u2} A ι _inst_1 B), ι -> (OpenAddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (Ring.toAddGroupWithOne.{u1} A _inst_1)) (RingSubgroupsBasis.topology.{u1, u2} A ι _inst_1 _inst_2 B hB))
Case conversion may be inaccurate. Consider using '#align ring_subgroups_basis.open_add_subgroup RingSubgroupsBasis.openAddSubgroupₓ'. -/
/-- Given a subgroups basis, the basis elements as open additive subgroups in the associated
topology. -/
def openAddSubgroup (i : ι) : @OpenAddSubgroup A _ hB.topology :=
  { B i with
    is_open' := by
      letI := hB.topology
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.has_basis_nhds a).mem_iff]
      use i, trivial
      rintro b b_in
      simpa using (B i).add_mem a_in b_in }
#align ring_subgroups_basis.open_add_subgroup RingSubgroupsBasis.openAddSubgroup

/- warning: ring_subgroups_basis.nonarchimedean -> RingSubgroupsBasis.nonarchimedean is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Ring.{u1} A] [_inst_2 : Nonempty.{succ u2} ι] {B : ι -> (AddSubgroup.{u1} A (AddGroupWithOne.toAddGroup.{u1} A (AddCommGroupWithOne.toAddGroupWithOne.{u1} A (Ring.toAddCommGroupWithOne.{u1} A _inst_1))))} (hB : RingSubgroupsBasis.{u1, u2} A ι _inst_1 B), NonarchimedeanRing.{u1} A _inst_1 (RingSubgroupsBasis.topology.{u1, u2} A ι _inst_1 _inst_2 B hB)
but is expected to have type
  forall {A : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Ring.{u2} A] [_inst_2 : Nonempty.{succ u1} ι] {B : ι -> (AddSubgroup.{u2} A (AddGroupWithOne.toAddGroup.{u2} A (Ring.toAddGroupWithOne.{u2} A _inst_1)))} (hB : RingSubgroupsBasis.{u2, u1} A ι _inst_1 B), NonarchimedeanRing.{u2} A _inst_1 (RingSubgroupsBasis.topology.{u2, u1} A ι _inst_1 _inst_2 B hB)
Case conversion may be inaccurate. Consider using '#align ring_subgroups_basis.nonarchimedean RingSubgroupsBasis.nonarchimedeanₓ'. -/
-- see Note [nonarchimedean non instances]
theorem nonarchimedean : @NonarchimedeanRing A _ hB.topology :=
  by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨i, -, hi : (B i : Set A) ⊆ U⟩ := hB.has_basis_nhds_zero.mem_iff.mp hU
  exact ⟨hB.open_add_subgroup i, hi⟩
#align ring_subgroups_basis.nonarchimedean RingSubgroupsBasis.nonarchimedean

end RingSubgroupsBasis

variable {ι R A : Type _} [CommRing R] [CommRing A] [Algebra R A]

#print SubmodulesRingBasis /-
/-- A family of submodules in a commutative `R`-algebra `A` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `A` which is compatible with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure SubmodulesRingBasis (B : ι → Submodule R A) : Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  leftMul : ∀ (a : A) (i), ∃ j, a • B j ≤ B i
  mul : ∀ i, ∃ j, (B j : Set A) * B j ⊆ B i
#align submodules_ring_basis SubmodulesRingBasis
-/

namespace SubmodulesRingBasis

variable {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)

/- warning: submodules_ring_basis.to_ring_subgroups_basis -> SubmodulesRingBasis.toRing_subgroups_basis is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2))] {B : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)) _inst_3))}, (SubmodulesRingBasis.{u1, u2, u3} ι R A _inst_1 _inst_2 _inst_3 B) -> (RingSubgroupsBasis.{u3, u1} A ι (CommRing.toRing.{u3} A _inst_2) (fun (i : ι) => Submodule.toAddSubgroup.{u2, u3} R A (CommRing.toRing.{u2} R _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2)))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)) _inst_3) (B i)))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))] {B : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))}, (SubmodulesRingBasis.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 B) -> (RingSubgroupsBasis.{u1, u3} A ι (CommRing.toRing.{u1} A _inst_2) (fun (i : ι) => Submodule.toAddSubgroup.{u2, u1} R A (CommRing.toRing.{u2} R _inst_1) (Ring.toAddCommGroup.{u1} A (CommRing.toRing.{u1} A _inst_2)) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3) (B i)))
Case conversion may be inaccurate. Consider using '#align submodules_ring_basis.to_ring_subgroups_basis SubmodulesRingBasis.toRing_subgroups_basisₓ'. -/
theorem toRing_subgroups_basis (hB : SubmodulesRingBasis B) :
    RingSubgroupsBasis fun i => (B i).toAddSubgroup :=
  by
  apply RingSubgroupsBasis.of_comm (fun i => (B i).toAddSubgroup) hB.inter hB.mul
  intro a i
  rcases hB.left_mul a i with ⟨j, hj⟩
  use j
  rintro b (b_in : b ∈ B j)
  exact hj ⟨b, b_in, rfl⟩
#align submodules_ring_basis.to_ring_subgroups_basis SubmodulesRingBasis.toRing_subgroups_basis

#print SubmodulesRingBasis.topology /-
/-- The topology associated to a basis of submodules in an algebra. -/
def topology [Nonempty ι] (hB : SubmodulesRingBasis B) : TopologicalSpace A :=
  hB.toRing_subgroups_basis.topology
#align submodules_ring_basis.topology SubmodulesRingBasis.topology
-/

end SubmodulesRingBasis

variable {M : Type _} [AddCommGroup M] [Module R M]

#print SubmodulesBasis /-
/-- A family of submodules in an `R`-module `M` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `M` which is compatible with the module structure and
admits this family as a basis of neighborhoods of zero. -/
structure SubmodulesBasis [TopologicalSpace R] (B : ι → Submodule R M) : Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  smul : ∀ (m : M) (i : ι), ∀ᶠ a in 𝓝 (0 : R), a • m ∈ B i
#align submodules_basis SubmodulesBasis
-/

namespace SubmodulesBasis

variable [TopologicalSpace R] [Nonempty ι] {B : ι → Submodule R M} (hB : SubmodulesBasis B)

include hB

#print SubmodulesBasis.toModuleFilterBasis /-
/-- The image of a submodules basis is a module filter basis. -/
def toModuleFilterBasis : ModuleFilterBasis R M
    where
  sets := { U | ∃ i, U = B i }
  Nonempty := by
    inhabit ι
    exact ⟨B default, default, rfl⟩
  inter_sets := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    cases' hB.inter i j with k hk
    use B k, k, rfl, hk
  zero' := by
    rintro _ ⟨i, rfl⟩
    exact (B i).zero_mem
  add' := by
    rintro _ ⟨i, rfl⟩
    use B i, i, rfl
    rintro x ⟨y, z, y_in, z_in, rfl⟩
    exact (B i).add_mem y_in z_in
  neg' := by
    rintro _ ⟨i, rfl⟩
    use B i, i, rfl
    intro x x_in
    exact (B i).neg_mem x_in
  conj' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i, i, rfl
    simp
  smul' := by
    rintro _ ⟨i, rfl⟩
    use univ, univ_mem, B i, i, rfl
    rintro _ ⟨a, m, -, hm, rfl⟩
    exact (B i).smul_mem _ hm
  smul_left' := by
    rintro x₀ _ ⟨i, rfl⟩
    use B i, i, rfl
    intro m
    exact (B i).smul_mem _
  smul_right' := by
    rintro m₀ _ ⟨i, rfl⟩
    exact hB.smul m₀ i
#align submodules_basis.to_module_filter_basis SubmodulesBasis.toModuleFilterBasis
-/

#print SubmodulesBasis.topology /-
/-- The topology associated to a basis of submodules in a module. -/
def topology : TopologicalSpace M :=
  hB.toModuleFilterBasis.toAddGroupFilterBasis.topology
#align submodules_basis.topology SubmodulesBasis.topology
-/

#print SubmodulesBasis.openAddSubgroup /-
/-- Given a submodules basis, the basis elements as open additive subgroups in the associated
topology. -/
def openAddSubgroup (i : ι) : @OpenAddSubgroup M _ hB.topology :=
  { (B i).toAddSubgroup with
    is_open' := by
      letI := hB.topology
      rw [isOpen_iff_mem_nhds]
      intro a a_in
      rw [(hB.to_module_filter_basis.to_add_group_filter_basis.nhds_has_basis a).mem_iff]
      use B i, i, rfl
      rintro - ⟨b, b_in, rfl⟩
      exact (B i).add_mem a_in b_in }
#align submodules_basis.open_add_subgroup SubmodulesBasis.openAddSubgroup
-/

/- warning: submodules_basis.nonarchimedean -> SubmodulesBasis.nonarchimedean is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {M : Type.{u3}} [_inst_4 : AddCommGroup.{u3} M] [_inst_5 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)] [_inst_6 : TopologicalSpace.{u2} R] [_inst_7 : Nonempty.{succ u1} ι] {B : ι -> (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) _inst_5)} (hB : SubmodulesBasis.{u1, u2, u3} ι R _inst_1 M _inst_4 _inst_5 _inst_6 B), NonarchimedeanAddGroup.{u3} M (AddCommGroup.toAddGroup.{u3} M _inst_4) (SubmodulesBasis.topology.{u1, u2, u3} ι R _inst_1 M _inst_4 _inst_5 _inst_6 _inst_7 B hB)
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {M : Type.{u1}} [_inst_4 : AddCommGroup.{u1} M] [_inst_5 : Module.{u2, u1} R M (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_4)] [_inst_6 : TopologicalSpace.{u2} R] [_inst_7 : Nonempty.{succ u3} ι] {B : ι -> (Submodule.{u2, u1} R M (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_4) _inst_5)} (hB : SubmodulesBasis.{u3, u2, u1} ι R _inst_1 M _inst_4 _inst_5 _inst_6 B), NonarchimedeanAddGroup.{u1} M (AddCommGroup.toAddGroup.{u1} M _inst_4) (SubmodulesBasis.topology.{u3, u2, u1} ι R _inst_1 M _inst_4 _inst_5 _inst_6 _inst_7 B hB)
Case conversion may be inaccurate. Consider using '#align submodules_basis.nonarchimedean SubmodulesBasis.nonarchimedeanₓ'. -/
-- see Note [nonarchimedean non instances]
theorem nonarchimedean (hB : SubmodulesBasis B) : @NonarchimedeanAddGroup M _ hB.topology :=
  by
  letI := hB.topology
  constructor
  intro U hU
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : Set M) ⊆ U⟩ :=
    hB.to_module_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff.mp hU
  exact ⟨hB.open_add_subgroup i, hi⟩
#align submodules_basis.nonarchimedean SubmodulesBasis.nonarchimedean

library_note "nonarchimedean non instances"/--
The non archimedean subgroup basis lemmas cannot be instances because some instances
(such as `measure_theory.ae_eq_fun.add_monoid ` or `topological_add_group.to_has_continuous_add`)
cause the search for `@topological_add_group β ?m1 ?m2`, i.e. a search for a topological group where
the topology/group structure are unknown. -/


end SubmodulesBasis

section

/-
In this section, we check that, in a `R`-algebra `A` over a ring equipped with a topology,
a basis of `R`-submodules which is compatible with the topology on `R` is also a submodule basis
in the sense of `R`-modules (forgetting about the ring structure on `A`) and those two points of
view definitionaly gives the same topology on `A`.
-/
variable [TopologicalSpace R] {B : ι → Submodule R A} (hB : SubmodulesRingBasis B)
  (hsmul : ∀ (m : A) (i : ι), ∀ᶠ a : R in 𝓝 0, a • m ∈ B i)

/- warning: submodules_ring_basis.to_submodules_basis -> SubmodulesRingBasis.toSubmodulesBasis is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u3} A] [_inst_3 : Algebra.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2))] [_inst_6 : TopologicalSpace.{u2} R] {B : ι -> (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)) _inst_3))}, (SubmodulesRingBasis.{u1, u2, u3} ι R A _inst_1 _inst_2 _inst_3 B) -> (forall (m : A) (i : ι), Filter.Eventually.{u2} R (fun (a : R) => Membership.Mem.{u3, u3} A (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)) _inst_3)) (SetLike.hasMem.{u3, u3} (Submodule.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)) _inst_3)) A (Submodule.setLike.{u2, u3} R A (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)) _inst_3))) (SMul.smul.{u2, u3} R A (SMulZeroClass.toHasSmul.{u2, u3} R A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)))))))) (SMulWithZero.toSmulZeroClass.{u2, u3} R A (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)))))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)))))))) (MulActionWithZero.toSMulWithZero.{u2, u3} R A (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)))))))) (Module.toMulActionWithZero.{u2, u3} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2))))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)) _inst_3))))) a m) (B i)) (nhds.{u2} R _inst_6 (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_1))))))))))) -> (SubmodulesBasis.{u1, u2, u3} ι R _inst_1 A (NonUnitalNonAssocRing.toAddCommGroup.{u3} A (NonAssocRing.toNonUnitalNonAssocRing.{u3} A (Ring.toNonAssocRing.{u3} A (CommRing.toRing.{u3} A _inst_2)))) (Algebra.toModule.{u2, u3} R A (CommRing.toCommSemiring.{u2} R _inst_1) (Ring.toSemiring.{u3} A (CommRing.toRing.{u3} A _inst_2)) _inst_3) _inst_6 B)
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : CommRing.{u1} A] [_inst_3 : Algebra.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2))] [_inst_6 : TopologicalSpace.{u2} R] {B : ι -> (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))}, (SubmodulesRingBasis.{u3, u2, u1} ι R A _inst_1 _inst_2 _inst_3 B) -> (forall (m : A) (i : ι), Filter.Eventually.{u2} R (fun (a : R) => Membership.mem.{u1, u1} A (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3)) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3)) A (Submodule.setLike.{u2, u1} R A (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_2))))) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3))) (HSMul.hSMul.{u2, u1, u1} R A A (instHSMul.{u2, u1} R A (Algebra.toSMul.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3)) a m) (B i)) (nhds.{u2} R _inst_6 (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (CommRing.toCommSemiring.{u2} R _inst_1))))))) -> (SubmodulesBasis.{u3, u2, u1} ι R _inst_1 A (Ring.toAddCommGroup.{u1} A (CommRing.toRing.{u1} A _inst_2)) (Algebra.toModule.{u2, u1} R A (CommRing.toCommSemiring.{u2} R _inst_1) (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_2)) _inst_3) _inst_6 B)
Case conversion may be inaccurate. Consider using '#align submodules_ring_basis.to_submodules_basis SubmodulesRingBasis.toSubmodulesBasisₓ'. -/
theorem SubmodulesRingBasis.toSubmodulesBasis : SubmodulesBasis B :=
  { inter := hB.inter
    smul := hsmul }
#align submodules_ring_basis.to_submodules_basis SubmodulesRingBasis.toSubmodulesBasis

example [Nonempty ι] : hB.topology = (hB.toSubmodulesBasis hsmul).topology :=
  rfl

end

#print RingFilterBasis.SubmodulesBasis /-
/-- Given a ring filter basis on a commutative ring `R`, define a compatibility condition
on a family of submodules of a `R`-module `M`. This compatibility condition allows to get
a topological module structure. -/
structure RingFilterBasis.SubmodulesBasis (BR : RingFilterBasis R) (B : ι → Submodule R M) :
  Prop where
  inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j
  smul : ∀ (m : M) (i : ι), ∃ U ∈ BR, U ⊆ (fun a => a • m) ⁻¹' B i
#align ring_filter_basis.submodules_basis RingFilterBasis.SubmodulesBasis
-/

/- warning: ring_filter_basis.submodules_basis_is_basis -> RingFilterBasis.submodulesBasisIsBasis is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] {M : Type.{u3}} [_inst_4 : AddCommGroup.{u3} M] [_inst_5 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)] (BR : RingFilterBasis.{u2} R (CommRing.toRing.{u2} R _inst_1)) {B : ι -> (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4) _inst_5)}, (RingFilterBasis.SubmodulesBasis.{u1, u2, u3} ι R _inst_1 M _inst_4 _inst_5 BR B) -> (SubmodulesBasis.{u1, u2, u3} ι R _inst_1 M _inst_4 _inst_5 (RingFilterBasis.topology.{u2} R (CommRing.toRing.{u2} R _inst_1) BR) B)
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} [_inst_1 : CommRing.{u3} R] {M : Type.{u2}} [_inst_4 : AddCommGroup.{u2} M] [_inst_5 : Module.{u3, u2} R M (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_4)] (BR : RingFilterBasis.{u3} R (CommRing.toRing.{u3} R _inst_1)) {B : ι -> (Submodule.{u3, u2} R M (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_4) _inst_5)}, (RingFilterBasis.SubmodulesBasis.{u1, u3, u2} ι R _inst_1 M _inst_4 _inst_5 BR B) -> (SubmodulesBasis.{u1, u3, u2} ι R _inst_1 M _inst_4 _inst_5 (RingFilterBasis.topology.{u3} R (CommRing.toRing.{u3} R _inst_1) BR) B)
Case conversion may be inaccurate. Consider using '#align ring_filter_basis.submodules_basis_is_basis RingFilterBasis.submodulesBasisIsBasisₓ'. -/
theorem RingFilterBasis.submodulesBasisIsBasis (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @SubmodulesBasis ι R _ M _ _ BR.topology B :=
  { inter := hB.inter
    smul := by
      letI := BR.topology
      intro m i
      rcases hB.smul m i with ⟨V, V_in, hV⟩
      exact mem_of_superset (BR.to_add_group_filter_basis.mem_nhds_zero V_in) hV }
#align ring_filter_basis.submodules_basis_is_basis RingFilterBasis.submodulesBasisIsBasis

#print RingFilterBasis.moduleFilterBasis /-
/-- The module filter basis associated to a ring filter basis and a compatible submodule basis.
This allows to build a topological module structure compatible with the given module structure
and the topology associated to the given ring filter basis. -/
def RingFilterBasis.moduleFilterBasis [Nonempty ι] (BR : RingFilterBasis R) {B : ι → Submodule R M}
    (hB : BR.SubmodulesBasis B) : @ModuleFilterBasis R M _ BR.topology _ _ :=
  @SubmodulesBasis.toModuleFilterBasis ι R _ M _ _ BR.topology _ _ (BR.submodulesBasisIsBasis hB)
#align ring_filter_basis.module_filter_basis RingFilterBasis.moduleFilterBasis
-/

