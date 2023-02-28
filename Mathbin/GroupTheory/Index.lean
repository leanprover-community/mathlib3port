/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning

! This file was ported from Lean 3 source module group_theory.index
! leanprover-community/mathlib commit 1ead22342e1a078bd44744ace999f85756555d35
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finite.Card
import Mathbin.GroupTheory.Finiteness
import Mathbin.GroupTheory.GroupAction.Quotient

/-!
# Index of a Subgroup

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the index of a subgroup, and prove several divisibility properties.
Several theorems proved in this file are known as Lagrange's theorem.

## Main definitions

- `H.index` : the index of `H : subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.relindex K` : the relative index of `H : subgroup G` in `K : subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

# Main results

- `card_mul_index` : `nat.card H * H.index = nat.card G`
- `index_mul_card` : `H.index * fintype.card H = fintype.card G`
- `index_dvd_card` : `H.index ∣ fintype.card G`
- `index_eq_mul_of_le` : If `H ≤ K`, then `H.index = K.index * (H.subgroup_of K).index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`
- `relindex_mul_relindex` : `relindex` is multiplicative in towers

-/


namespace Subgroup

open BigOperators Cardinal

variable {G : Type _} [Group G] (H K L : Subgroup G)

#print Subgroup.index /-
/-- The index of a subgroup as a natural number, and returns 0 if the index is infinite. -/
@[to_additive
      "The index of a subgroup as a natural number,\nand returns 0 if the index is infinite."]
noncomputable def index : ℕ :=
  Nat.card (G ⧸ H)
#align subgroup.index Subgroup.index
#align add_subgroup.index AddSubgroup.index
-/

#print Subgroup.relindex /-
/-- The relative index of a subgroup as a natural number,
  and returns 0 if the relative index is infinite. -/
@[to_additive
      "The relative index of a subgroup as a natural number,\n  and returns 0 if the relative index is infinite."]
noncomputable def relindex : ℕ :=
  (H.subgroupOf K).index
#align subgroup.relindex Subgroup.relindex
#align add_subgroup.relindex AddSubgroup.relindex
-/

/- warning: subgroup.index_comap_of_surjective -> Subgroup.index_comap_of_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u2, u1} G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))}, (Function.Surjective.{succ u2, succ u1} G' G (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (fun (_x : MonoidHom.{u2, u1} G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) => G' -> G) (MonoidHom.hasCoeToFun.{u2, u1} G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) f)) -> (Eq.{1} Nat (Subgroup.index.{u2} G' _inst_2 (Subgroup.comap.{u2, u1} G' _inst_2 G _inst_1 f H)) (Subgroup.index.{u1} G _inst_1 H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u2, u1} G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))}, (Function.Surjective.{succ u2, succ u1} G' G (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidHom.{u2, u1} G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) G' (fun (_x : G') => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G') => G) _x) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) G' G (MulOneClass.toMul.{u2} G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MonoidHom.monoidHomClass.{u2, u1} G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) f)) -> (Eq.{1} Nat (Subgroup.index.{u2} G' _inst_2 (Subgroup.comap.{u2, u1} G' _inst_2 G _inst_1 f H)) (Subgroup.index.{u1} G _inst_1 H))
Case conversion may be inaccurate. Consider using '#align subgroup.index_comap_of_surjective Subgroup.index_comap_of_surjectiveₓ'. -/
@[to_additive]
theorem index_comap_of_surjective {G' : Type _} [Group G'] {f : G' →* G}
    (hf : Function.Surjective f) : (H.comap f).index = H.index :=
  by
  letI := QuotientGroup.leftRel H
  letI := QuotientGroup.leftRel (H.comap f)
  have key : ∀ x y : G', Setoid.r x y ↔ Setoid.r (f x) (f y) :=
    by
    simp only [QuotientGroup.leftRel_apply]
    exact fun x y => iff_of_eq (congr_arg (· ∈ H) (by rw [f.map_mul, f.map_inv]))
  refine' Cardinal.toNat_congr (Equiv.ofBijective (Quotient.map' f fun x y => (key x y).mp) ⟨_, _⟩)
  · simp_rw [← Quotient.eq''] at key
    refine' Quotient.ind' fun x => _
    refine' Quotient.ind' fun y => _
    exact (key x y).mpr
  · refine' Quotient.ind' fun x => _
    obtain ⟨y, hy⟩ := hf x
    exact ⟨y, (Quotient.map'_mk'' f _ y).trans (congr_arg Quotient.mk'' hy)⟩
#align subgroup.index_comap_of_surjective Subgroup.index_comap_of_surjective
#align add_subgroup.index_comap_of_surjective AddSubgroup.index_comap_of_surjective

#print Subgroup.index_comap /-
@[to_additive]
theorem index_comap {G' : Type _} [Group G'] (f : G' →* G) :
    (H.comap f).index = H.relindex f.range :=
  Eq.trans (congr_arg index (by rfl))
    ((H.subgroupOf f.range).index_comap_of_surjective f.rangeRestrict_surjective)
#align subgroup.index_comap Subgroup.index_comap
#align add_subgroup.index_comap AddSubgroup.index_comap
-/

#print Subgroup.relindex_comap /-
@[to_additive]
theorem relindex_comap {G' : Type _} [Group G'] (f : G' →* G) (K : Subgroup G') :
    relindex (comap f H) K = relindex H (map f K) := by
  rw [relindex, subgroup_of, comap_comap, index_comap, ← f.map_range, K.subtype_range]
#align subgroup.relindex_comap Subgroup.relindex_comap
#align add_subgroup.relindex_comap AddSubgroup.relindex_comap
-/

variable {H K L}

/- warning: subgroup.relindex_mul_index -> Subgroup.relindex_mul_index is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H K) -> (Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Subgroup.relindex.{u1} G _inst_1 H K) (Subgroup.index.{u1} G _inst_1 K)) (Subgroup.index.{u1} G _inst_1 H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K) -> (Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Subgroup.relindex.{u1} G _inst_1 H K) (Subgroup.index.{u1} G _inst_1 K)) (Subgroup.index.{u1} G _inst_1 H))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_mul_index Subgroup.relindex_mul_indexₓ'. -/
@[to_additive relindex_mul_index]
theorem relindex_mul_index (h : H ≤ K) : H.relindex K * K.index = H.index :=
  ((mul_comm _ _).trans (Cardinal.toNat_mul _ _).symm).trans
    (congr_arg Cardinal.toNat (Equiv.cardinal_eq (quotientEquivProdOfLe h))).symm
#align subgroup.relindex_mul_index Subgroup.relindex_mul_index
#align add_subgroup.relindex_mul_index AddSubgroup.relindex_mul_index

/- warning: subgroup.index_dvd_of_le -> Subgroup.index_dvd_of_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H K) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Subgroup.index.{u1} G _inst_1 K) (Subgroup.index.{u1} G _inst_1 H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Subgroup.index.{u1} G _inst_1 K) (Subgroup.index.{u1} G _inst_1 H))
Case conversion may be inaccurate. Consider using '#align subgroup.index_dvd_of_le Subgroup.index_dvd_of_leₓ'. -/
@[to_additive]
theorem index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
  dvd_of_mul_left_eq (H.relindex K) (relindex_mul_index h)
#align subgroup.index_dvd_of_le Subgroup.index_dvd_of_le
#align add_subgroup.index_dvd_of_le AddSubgroup.index_dvd_of_le

/- warning: subgroup.relindex_dvd_index_of_le -> Subgroup.relindex_dvd_index_of_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H K) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Subgroup.relindex.{u1} G _inst_1 H K) (Subgroup.index.{u1} G _inst_1 H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Subgroup.relindex.{u1} G _inst_1 H K) (Subgroup.index.{u1} G _inst_1 H))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_dvd_index_of_le Subgroup.relindex_dvd_index_of_leₓ'. -/
@[to_additive]
theorem relindex_dvd_index_of_le (h : H ≤ K) : H.relindex K ∣ H.index :=
  dvd_of_mul_right_eq K.index (relindex_mul_index h)
#align subgroup.relindex_dvd_index_of_le Subgroup.relindex_dvd_index_of_le
#align add_subgroup.relindex_dvd_index_of_le AddSubgroup.relindex_dvd_index_of_le

/- warning: subgroup.relindex_subgroup_of -> Subgroup.relindex_subgroupOf is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) K L) -> (Eq.{1} Nat (Subgroup.relindex.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) L) (Subgroup.toGroup.{u1} G _inst_1 L) (Subgroup.subgroupOf.{u1} G _inst_1 H L) (Subgroup.subgroupOf.{u1} G _inst_1 K L)) (Subgroup.relindex.{u1} G _inst_1 H K))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) K L) -> (Eq.{1} Nat (Subgroup.relindex.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x L)) (Subgroup.toGroup.{u1} G _inst_1 L) (Subgroup.subgroupOf.{u1} G _inst_1 H L) (Subgroup.subgroupOf.{u1} G _inst_1 K L)) (Subgroup.relindex.{u1} G _inst_1 H K))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_subgroup_of Subgroup.relindex_subgroupOfₓ'. -/
@[to_additive]
theorem relindex_subgroupOf (hKL : K ≤ L) :
    (H.subgroupOf L).relindex (K.subgroupOf L) = H.relindex K :=
  ((index_comap (H.subgroupOf L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm
#align subgroup.relindex_subgroup_of Subgroup.relindex_subgroupOf
#align add_subgroup.relindex_add_subgroup_of AddSubgroup.relindex_addSubgroupOf

variable (H K L)

/- warning: subgroup.relindex_mul_relindex -> Subgroup.relindex_mul_relindex is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1) (L : Subgroup.{u1} G _inst_1), (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H K) -> (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) K L) -> (Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Subgroup.relindex.{u1} G _inst_1 H K) (Subgroup.relindex.{u1} G _inst_1 K L)) (Subgroup.relindex.{u1} G _inst_1 H L))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1) (L : Subgroup.{u1} G _inst_1), (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K) -> (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) K L) -> (Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Subgroup.relindex.{u1} G _inst_1 H K) (Subgroup.relindex.{u1} G _inst_1 K L)) (Subgroup.relindex.{u1} G _inst_1 H L))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_mul_relindex Subgroup.relindex_mul_relindexₓ'. -/
@[to_additive relindex_mul_relindex]
theorem relindex_mul_relindex (hHK : H ≤ K) (hKL : K ≤ L) :
    H.relindex K * K.relindex L = H.relindex L :=
  by
  rw [← relindex_subgroup_of hKL]
  exact relindex_mul_index fun x hx => hHK hx
#align subgroup.relindex_mul_relindex Subgroup.relindex_mul_relindex
#align add_subgroup.relindex_mul_relindex AddSubgroup.relindex_mul_relindex

/- warning: subgroup.inf_relindex_right -> Subgroup.inf_relindex_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K) K) (Subgroup.relindex.{u1} G _inst_1 H K)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K) K) (Subgroup.relindex.{u1} G _inst_1 H K)
Case conversion may be inaccurate. Consider using '#align subgroup.inf_relindex_right Subgroup.inf_relindex_rightₓ'. -/
@[to_additive]
theorem inf_relindex_right : (H ⊓ K).relindex K = H.relindex K := by
  rw [relindex, relindex, inf_subgroup_of_right]
#align subgroup.inf_relindex_right Subgroup.inf_relindex_right
#align add_subgroup.inf_relindex_right AddSubgroup.inf_relindex_right

/- warning: subgroup.inf_relindex_left -> Subgroup.inf_relindex_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K) H) (Subgroup.relindex.{u1} G _inst_1 K H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K) H) (Subgroup.relindex.{u1} G _inst_1 K H)
Case conversion may be inaccurate. Consider using '#align subgroup.inf_relindex_left Subgroup.inf_relindex_leftₓ'. -/
@[to_additive]
theorem inf_relindex_left : (H ⊓ K).relindex H = K.relindex H := by
  rw [inf_comm, inf_relindex_right]
#align subgroup.inf_relindex_left Subgroup.inf_relindex_left
#align add_subgroup.inf_relindex_left AddSubgroup.inf_relindex_left

/- warning: subgroup.relindex_inf_mul_relindex -> Subgroup.relindex_inf_mul_relindex is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1) (L : Subgroup.{u1} G _inst_1), Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Subgroup.relindex.{u1} G _inst_1 H (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) K L)) (Subgroup.relindex.{u1} G _inst_1 K L)) (Subgroup.relindex.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K) L)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1) (L : Subgroup.{u1} G _inst_1), Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Subgroup.relindex.{u1} G _inst_1 H (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) K L)) (Subgroup.relindex.{u1} G _inst_1 K L)) (Subgroup.relindex.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K) L)
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_inf_mul_relindex Subgroup.relindex_inf_mul_relindexₓ'. -/
@[to_additive relindex_inf_mul_relindex]
theorem relindex_inf_mul_relindex : H.relindex (K ⊓ L) * K.relindex L = (H ⊓ K).relindex L := by
  rw [← inf_relindex_right H (K ⊓ L), ← inf_relindex_right K L, ← inf_relindex_right (H ⊓ K) L,
    inf_assoc, relindex_mul_relindex (H ⊓ (K ⊓ L)) (K ⊓ L) L inf_le_right inf_le_right]
#align subgroup.relindex_inf_mul_relindex Subgroup.relindex_inf_mul_relindex
#align add_subgroup.relindex_inf_mul_relindex AddSubgroup.relindex_inf_mul_relindex

/- warning: subgroup.relindex_sup_right -> Subgroup.relindex_sup_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1) [_inst_2 : Subgroup.Normal.{u1} G _inst_1 K], Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 K (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) H K)) (Subgroup.relindex.{u1} G _inst_1 K H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1) [_inst_2 : Subgroup.Normal.{u1} G _inst_1 K], Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 K (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K)) (Subgroup.relindex.{u1} G _inst_1 K H)
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_sup_right Subgroup.relindex_sup_rightₓ'. -/
@[simp, to_additive]
theorem relindex_sup_right [K.Normal] : K.relindex (H ⊔ K) = K.relindex H :=
  Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H K).toEquiv.symm
#align subgroup.relindex_sup_right Subgroup.relindex_sup_right
#align add_subgroup.relindex_sup_right AddSubgroup.relindex_sup_right

/- warning: subgroup.relindex_sup_left -> Subgroup.relindex_sup_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1) [_inst_2 : Subgroup.Normal.{u1} G _inst_1 K], Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 K (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) K H)) (Subgroup.relindex.{u1} G _inst_1 K H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1) [_inst_2 : Subgroup.Normal.{u1} G _inst_1 K], Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 K (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) K H)) (Subgroup.relindex.{u1} G _inst_1 K H)
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_sup_left Subgroup.relindex_sup_leftₓ'. -/
@[simp, to_additive]
theorem relindex_sup_left [K.Normal] : K.relindex (K ⊔ H) = K.relindex H := by
  rw [sup_comm, relindex_sup_right]
#align subgroup.relindex_sup_left Subgroup.relindex_sup_left
#align add_subgroup.relindex_sup_left AddSubgroup.relindex_sup_left

#print Subgroup.relindex_dvd_index_of_normal /-
@[to_additive]
theorem relindex_dvd_index_of_normal [H.Normal] : H.relindex K ∣ H.index :=
  relindex_sup_right K H ▸ relindex_dvd_index_of_le le_sup_right
#align subgroup.relindex_dvd_index_of_normal Subgroup.relindex_dvd_index_of_normal
#align add_subgroup.relindex_dvd_index_of_normal AddSubgroup.relindex_dvd_index_of_normal
-/

variable {H K}

/- warning: subgroup.relindex_dvd_of_le_left -> Subgroup.relindex_dvd_of_le_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} (L : Subgroup.{u1} G _inst_1), (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H K) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Subgroup.relindex.{u1} G _inst_1 K L) (Subgroup.relindex.{u1} G _inst_1 H L))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} (L : Subgroup.{u1} G _inst_1), (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Subgroup.relindex.{u1} G _inst_1 K L) (Subgroup.relindex.{u1} G _inst_1 H L))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_dvd_of_le_left Subgroup.relindex_dvd_of_le_leftₓ'. -/
@[to_additive]
theorem relindex_dvd_of_le_left (hHK : H ≤ K) : K.relindex L ∣ H.relindex L :=
  inf_of_le_left hHK ▸ dvd_of_mul_left_eq _ (relindex_inf_mul_relindex _ _ _)
#align subgroup.relindex_dvd_of_le_left Subgroup.relindex_dvd_of_le_left
#align add_subgroup.relindex_dvd_of_le_left AddSubgroup.relindex_dvd_of_le_left

/- warning: subgroup.index_eq_two_iff -> Subgroup.index_eq_two_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, Iff (Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Exists.{succ u1} G (fun (a : G) => forall (b : G), Xor' (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a) H) (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) b H)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, Iff (Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Exists.{succ u1} G (fun (a : G) => forall (b : G), Xor' (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a) H) (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) b H)))
Case conversion may be inaccurate. Consider using '#align subgroup.index_eq_two_iff Subgroup.index_eq_two_iffₓ'. -/
/-- A subgroup has index two if and only if there exists `a` such that for all `b`, exactly one
of `b * a` and `b` belong to `H`. -/
@[to_additive
      "/-- An additive subgroup has index two if and only if there exists `a` such that for\nall `b`, exactly one of `b + a` and `b` belong to `H`. -/"]
theorem index_eq_two_iff : H.index = 2 ↔ ∃ a, ∀ b, Xor' (b * a ∈ H) (b ∈ H) :=
  by
  simp only [index, Nat.card_eq_two_iff' ((1 : G) : G ⧸ H), ExistsUnique, inv_mem_iff,
    QuotientGroup.exists_mk, QuotientGroup.forall_mk, Ne.def, QuotientGroup.eq, mul_one,
    xor_iff_iff_not]
  refine'
    exists_congr fun a => ⟨fun ha b => ⟨fun hba hb => _, fun hb => _⟩, fun ha => ⟨_, fun b hb => _⟩⟩
  · exact ha.1 ((mul_mem_cancel_left hb).1 hba)
  · exact inv_inv b ▸ ha.2 _ (mt inv_mem_iff.1 hb)
  · rw [← inv_mem_iff, ← ha, inv_mul_self]
    exact one_mem _
  · rwa [ha, inv_mem_iff]
#align subgroup.index_eq_two_iff Subgroup.index_eq_two_iff
#align add_subgroup.index_eq_two_iff AddSubgroup.index_eq_two_iff

/- warning: subgroup.mul_mem_iff_of_index_two -> Subgroup.mul_mem_iff_of_index_two is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (forall {a : G} {b : G}, Iff (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) H) (Iff (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) a H) (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) b H)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> (forall {a : G} {b : G}, Iff (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) H) (Iff (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) a H) (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) b H)))
Case conversion may be inaccurate. Consider using '#align subgroup.mul_mem_iff_of_index_two Subgroup.mul_mem_iff_of_index_twoₓ'. -/
@[to_additive]
theorem mul_mem_iff_of_index_two (h : H.index = 2) {a b : G} : a * b ∈ H ↔ (a ∈ H ↔ b ∈ H) :=
  by
  by_cases ha : a ∈ H; · simp only [ha, true_iff_iff, mul_mem_cancel_left ha]
  by_cases hb : b ∈ H; · simp only [hb, iff_true_iff, mul_mem_cancel_right hb]
  simp only [ha, hb, iff_self_iff, iff_true_iff]
  rcases index_eq_two_iff.1 h with ⟨c, hc⟩
  refine' (hc _).Or.resolve_left _
  rwa [mul_assoc, mul_mem_cancel_right ((hc _).Or.resolve_right hb)]
#align subgroup.mul_mem_iff_of_index_two Subgroup.mul_mem_iff_of_index_two
#align add_subgroup.add_mem_iff_of_index_two AddSubgroup.add_mem_iff_of_index_two

/- warning: subgroup.mul_self_mem_of_index_two -> Subgroup.mul_self_mem_of_index_two is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (forall (a : G), Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a a) H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> (forall (a : G), Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a a) H)
Case conversion may be inaccurate. Consider using '#align subgroup.mul_self_mem_of_index_two Subgroup.mul_self_mem_of_index_twoₓ'. -/
@[to_additive]
theorem mul_self_mem_of_index_two (h : H.index = 2) (a : G) : a * a ∈ H := by
  rw [mul_mem_iff_of_index_two h]
#align subgroup.mul_self_mem_of_index_two Subgroup.mul_self_mem_of_index_two
#align add_subgroup.add_self_mem_of_index_two AddSubgroup.add_self_mem_of_index_two

/- warning: subgroup.sq_mem_of_index_two -> Subgroup.sq_mem_of_index_two is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (forall (a : G), Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, (Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> (forall (a : G), Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) H)
Case conversion may be inaccurate. Consider using '#align subgroup.sq_mem_of_index_two Subgroup.sq_mem_of_index_twoₓ'. -/
@[to_additive two_smul_mem_of_index_two]
theorem sq_mem_of_index_two (h : H.index = 2) (a : G) : a ^ 2 ∈ H :=
  (pow_two a).symm ▸ mul_self_mem_of_index_two h a
#align subgroup.sq_mem_of_index_two Subgroup.sq_mem_of_index_two
#align add_subgroup.two_smul_mem_of_index_two AddSubgroup.two_smul_mem_of_index_two

variable (H K)

/- warning: subgroup.index_top -> Subgroup.index_top is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align subgroup.index_top Subgroup.index_topₓ'. -/
@[simp, to_additive]
theorem index_top : (⊤ : Subgroup G).index = 1 :=
  Cardinal.toNat_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
#align subgroup.index_top Subgroup.index_top
#align add_subgroup.index_top AddSubgroup.index_top

/- warning: subgroup.index_bot -> Subgroup.index_bot is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1))) (Nat.card.{u1} G)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1))) (Nat.card.{u1} G)
Case conversion may be inaccurate. Consider using '#align subgroup.index_bot Subgroup.index_botₓ'. -/
@[simp, to_additive]
theorem index_bot : (⊥ : Subgroup G).index = Nat.card G :=
  Cardinal.toNat_congr QuotientGroup.quotientBot.toEquiv
#align subgroup.index_bot Subgroup.index_bot
#align add_subgroup.index_bot AddSubgroup.index_bot

/- warning: subgroup.index_bot_eq_card -> Subgroup.index_bot_eq_card is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Fintype.{u1} G], Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1))) (Fintype.card.{u1} G _inst_2)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : Fintype.{u1} G], Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1))) (Fintype.card.{u1} G _inst_2)
Case conversion may be inaccurate. Consider using '#align subgroup.index_bot_eq_card Subgroup.index_bot_eq_cardₓ'. -/
@[to_additive]
theorem index_bot_eq_card [Fintype G] : (⊥ : Subgroup G).index = Fintype.card G :=
  index_bot.trans Nat.card_eq_fintype_card
#align subgroup.index_bot_eq_card Subgroup.index_bot_eq_card
#align add_subgroup.index_bot_eq_card AddSubgroup.index_bot_eq_card

/- warning: subgroup.relindex_top_left -> Subgroup.relindex_top_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1)) H) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1)) H) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_top_left Subgroup.relindex_top_leftₓ'. -/
@[simp, to_additive]
theorem relindex_top_left : (⊤ : Subgroup G).relindex H = 1 :=
  index_top
#align subgroup.relindex_top_left Subgroup.relindex_top_left
#align add_subgroup.relindex_top_left AddSubgroup.relindex_top_left

/- warning: subgroup.relindex_top_right -> Subgroup.relindex_top_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1))) (Subgroup.index.{u1} G _inst_1 H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1))) (Subgroup.index.{u1} G _inst_1 H)
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_top_right Subgroup.relindex_top_rightₓ'. -/
@[simp, to_additive]
theorem relindex_top_right : H.relindex ⊤ = H.index := by
  rw [← relindex_mul_index (show H ≤ ⊤ from le_top), index_top, mul_one]
#align subgroup.relindex_top_right Subgroup.relindex_top_right
#align add_subgroup.relindex_top_right AddSubgroup.relindex_top_right

/- warning: subgroup.relindex_bot_left -> Subgroup.relindex_bot_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)) H) (Nat.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)) H) (Nat.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_bot_left Subgroup.relindex_bot_leftₓ'. -/
@[simp, to_additive]
theorem relindex_bot_left : (⊥ : Subgroup G).relindex H = Nat.card H := by
  rw [relindex, bot_subgroup_of, index_bot]
#align subgroup.relindex_bot_left Subgroup.relindex_bot_left
#align add_subgroup.relindex_bot_left AddSubgroup.relindex_bot_left

/- warning: subgroup.relindex_bot_left_eq_card -> Subgroup.relindex_bot_left_eq_card is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)], Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)) H) (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) _inst_2)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_2 : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))], Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)) H) (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) _inst_2)
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_bot_left_eq_card Subgroup.relindex_bot_left_eq_cardₓ'. -/
@[to_additive]
theorem relindex_bot_left_eq_card [Fintype H] : (⊥ : Subgroup G).relindex H = Fintype.card H :=
  H.relindex_bot_left.trans Nat.card_eq_fintype_card
#align subgroup.relindex_bot_left_eq_card Subgroup.relindex_bot_left_eq_card
#align add_subgroup.relindex_bot_left_eq_card AddSubgroup.relindex_bot_left_eq_card

/- warning: subgroup.relindex_bot_right -> Subgroup.relindex_bot_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_bot_right Subgroup.relindex_bot_rightₓ'. -/
@[simp, to_additive]
theorem relindex_bot_right : H.relindex ⊥ = 1 := by rw [relindex, subgroup_of_bot_eq_top, index_top]
#align subgroup.relindex_bot_right Subgroup.relindex_bot_right
#align add_subgroup.relindex_bot_right AddSubgroup.relindex_bot_right

#print Subgroup.relindex_self /-
@[simp, to_additive]
theorem relindex_self : H.relindex H = 1 := by rw [relindex, subgroup_of_self, index_top]
#align subgroup.relindex_self Subgroup.relindex_self
#align add_subgroup.relindex_self AddSubgroup.relindex_self
-/

/- warning: subgroup.index_ker -> Subgroup.index_ker is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_2 : Group.{u2} H] (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))), Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 (MonoidHom.ker.{u1, u2} G _inst_1 H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) f)) (Nat.card.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} H) Type.{u2} (Set.hasCoeToSort.{u2} H) (Set.range.{u2, succ u1} H G (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) f))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_2 : Group.{u2} H] (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))), Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 (MonoidHom.ker.{u1, u2} G _inst_1 H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) f)) (Nat.card.{u2} (Set.Elem.{u2} H (Set.range.{u2, succ u1} H G (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) G H (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))))) f))))
Case conversion may be inaccurate. Consider using '#align subgroup.index_ker Subgroup.index_kerₓ'. -/
@[to_additive]
theorem index_ker {H} [Group H] (f : G →* H) : f.ker.index = Nat.card (Set.range f) :=
  by
  rw [← MonoidHom.comap_bot, index_comap, relindex_bot_left]
  rfl
#align subgroup.index_ker Subgroup.index_ker
#align add_subgroup.index_ker AddSubgroup.index_ker

/- warning: subgroup.relindex_ker -> Subgroup.relindex_ker is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_2 : Group.{u2} H] (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (K : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (MonoidHom.ker.{u1, u2} G _inst_1 H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) f) K) (Nat.card.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} H) Type.{u2} (Set.hasCoeToSort.{u2} H) (Set.image.{u1, u2} G H (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_1) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) K))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Type.{u2}} [_inst_2 : Group.{u2} H] (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (K : Subgroup.{u1} G _inst_1), Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (MonoidHom.ker.{u1, u2} G _inst_1 H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) f) K) (Nat.card.{u2} (Set.Elem.{u2} H (Set.image.{u1, u2} G H (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) G H (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))))) f) (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) K))))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_ker Subgroup.relindex_kerₓ'. -/
@[to_additive]
theorem relindex_ker {H} [Group H] (f : G →* H) (K : Subgroup G) :
    f.ker.relindex K = Nat.card (f '' K) :=
  by
  rw [← MonoidHom.comap_bot, relindex_comap, relindex_bot_left]
  rfl
#align subgroup.relindex_ker Subgroup.relindex_ker
#align add_subgroup.relindex_ker AddSubgroup.relindex_ker

/- warning: subgroup.card_mul_index -> Subgroup.card_mul_index is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Nat.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)) (Subgroup.index.{u1} G _inst_1 H)) (Nat.card.{u1} G)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1), Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Nat.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))) (Subgroup.index.{u1} G _inst_1 H)) (Nat.card.{u1} G)
Case conversion may be inaccurate. Consider using '#align subgroup.card_mul_index Subgroup.card_mul_indexₓ'. -/
@[simp, to_additive card_mul_index]
theorem card_mul_index : Nat.card H * H.index = Nat.card G :=
  by
  rw [← relindex_bot_left, ← index_bot]
  exact relindex_mul_index bot_le
#align subgroup.card_mul_index Subgroup.card_mul_index
#align add_subgroup.card_mul_index AddSubgroup.card_mul_index

/- warning: subgroup.nat_card_dvd_of_injective -> Subgroup.nat_card_dvd_of_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_2 : Group.{u1} G] [_inst_3 : Group.{u2} H] (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))), (Function.Injective.{succ u1, succ u2} G H (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) f)) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Nat.card.{u1} G) (Nat.card.{u2} H))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_2 : Group.{u2} G] [_inst_3 : Group.{u1} H] (f : MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))), (Function.Injective.{succ u2, succ u1} G H (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3))) (MonoidHom.monoidHomClass.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))))) f)) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Nat.card.{u2} G) (Nat.card.{u1} H))
Case conversion may be inaccurate. Consider using '#align subgroup.nat_card_dvd_of_injective Subgroup.nat_card_dvd_of_injectiveₓ'. -/
@[to_additive]
theorem nat_card_dvd_of_injective {G H : Type _} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) : Nat.card G ∣ Nat.card H :=
  by
  rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  exact Dvd.intro f.range.index f.range.card_mul_index
#align subgroup.nat_card_dvd_of_injective Subgroup.nat_card_dvd_of_injective
#align add_subgroup.nat_card_dvd_of_injective AddSubgroup.nat_card_dvd_of_injective

/- warning: subgroup.nat_card_dvd_of_le -> Subgroup.nat_card_dvd_of_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1), (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H K) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Nat.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)) (Nat.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) K)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (K : Subgroup.{u1} G _inst_1), (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Nat.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))) (Nat.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K))))
Case conversion may be inaccurate. Consider using '#align subgroup.nat_card_dvd_of_le Subgroup.nat_card_dvd_of_leₓ'. -/
@[to_additive]
theorem nat_card_dvd_of_le (hHK : H ≤ K) : Nat.card H ∣ Nat.card K :=
  nat_card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)
#align subgroup.nat_card_dvd_of_le Subgroup.nat_card_dvd_of_le
#align add_subgroup.nat_card_dvd_of_le AddSubgroup.nat_card_dvd_of_le

/- warning: subgroup.nat_card_dvd_of_surjective -> Subgroup.nat_card_dvd_of_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_2 : Group.{u1} G] [_inst_3 : Group.{u2} H] (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))), (Function.Surjective.{succ u1, succ u2} G H (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) f)) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Nat.card.{u2} H) (Nat.card.{u1} G))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_2 : Group.{u2} G] [_inst_3 : Group.{u1} H] (f : MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))), (Function.Surjective.{succ u2, succ u1} G H (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3))) (MonoidHom.monoidHomClass.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))))) f)) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Nat.card.{u1} H) (Nat.card.{u2} G))
Case conversion may be inaccurate. Consider using '#align subgroup.nat_card_dvd_of_surjective Subgroup.nat_card_dvd_of_surjectiveₓ'. -/
@[to_additive]
theorem nat_card_dvd_of_surjective {G H : Type _} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : Nat.card H ∣ Nat.card G :=
  by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact Dvd.intro_left (Nat.card f.ker) f.ker.card_mul_index
#align subgroup.nat_card_dvd_of_surjective Subgroup.nat_card_dvd_of_surjective
#align add_subgroup.nat_card_dvd_of_surjective AddSubgroup.nat_card_dvd_of_surjective

/- warning: subgroup.card_dvd_of_surjective -> Subgroup.card_dvd_of_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_2 : Group.{u1} G] [_inst_3 : Group.{u2} H] [_inst_4 : Fintype.{u1} G] [_inst_5 : Fintype.{u2} H] (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))), (Function.Surjective.{succ u1, succ u2} G H (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_3)))) f)) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Fintype.card.{u2} H _inst_5) (Fintype.card.{u1} G _inst_4))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_2 : Group.{u2} G] [_inst_3 : Group.{u1} H] [_inst_4 : Fintype.{u2} G] [_inst_5 : Fintype.{u1} H] (f : MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))), (Function.Surjective.{succ u2, succ u1} G H (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => H) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))) G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3))) (MonoidHom.monoidHomClass.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_3)))))) f)) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Fintype.card.{u1} H _inst_5) (Fintype.card.{u2} G _inst_4))
Case conversion may be inaccurate. Consider using '#align subgroup.card_dvd_of_surjective Subgroup.card_dvd_of_surjectiveₓ'. -/
@[to_additive]
theorem card_dvd_of_surjective {G H : Type _} [Group G] [Group H] [Fintype G] [Fintype H]
    (f : G →* H) (hf : Function.Surjective f) : Fintype.card H ∣ Fintype.card G := by
  simp only [← Nat.card_eq_fintype_card, nat_card_dvd_of_surjective f hf]
#align subgroup.card_dvd_of_surjective Subgroup.card_dvd_of_surjective
#align add_subgroup.card_dvd_of_surjective AddSubgroup.card_dvd_of_surjective

/- warning: subgroup.index_map -> Subgroup.index_map is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] (f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))), Eq.{1} Nat (Subgroup.index.{u2} G' _inst_2 (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f H)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Subgroup.index.{u1} G _inst_1 (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) H (MonoidHom.ker.{u1, u2} G _inst_1 G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) f))) (Subgroup.index.{u2} G' _inst_2 (MonoidHom.range.{u1, u2} G _inst_1 G' _inst_2 f)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] (f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))), Eq.{1} Nat (Subgroup.index.{u2} G' _inst_2 (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f H)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Subgroup.index.{u1} G _inst_1 (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H (MonoidHom.ker.{u1, u2} G _inst_1 G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) f))) (Subgroup.index.{u2} G' _inst_2 (MonoidHom.range.{u1, u2} G _inst_1 G' _inst_2 f)))
Case conversion may be inaccurate. Consider using '#align subgroup.index_map Subgroup.index_mapₓ'. -/
@[to_additive]
theorem index_map {G' : Type _} [Group G'] (f : G →* G') :
    (H.map f).index = (H ⊔ f.ker).index * f.range.index := by
  rw [← comap_map_eq, index_comap, relindex_mul_index (H.map_le_range f)]
#align subgroup.index_map Subgroup.index_map
#align add_subgroup.index_map AddSubgroup.index_map

/- warning: subgroup.index_map_dvd -> Subgroup.index_map_dvd is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))}, (Function.Surjective.{succ u1, succ u2} G G' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) => G -> G') (MonoidHom.hasCoeToFun.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) f)) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Subgroup.index.{u2} G' _inst_2 (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f H)) (Subgroup.index.{u1} G _inst_1 H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))}, (Function.Surjective.{succ u1, succ u2} G G' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => G') _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) G G' (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))))) f)) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Subgroup.index.{u2} G' _inst_2 (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f H)) (Subgroup.index.{u1} G _inst_1 H))
Case conversion may be inaccurate. Consider using '#align subgroup.index_map_dvd Subgroup.index_map_dvdₓ'. -/
@[to_additive]
theorem index_map_dvd {G' : Type _} [Group G'] {f : G →* G'} (hf : Function.Surjective f) :
    (H.map f).index ∣ H.index :=
  by
  rw [index_map, f.range_top_of_surjective hf, index_top, mul_one]
  exact index_dvd_of_le le_sup_left
#align subgroup.index_map_dvd Subgroup.index_map_dvd
#align add_subgroup.index_map_dvd AddSubgroup.index_map_dvd

/- warning: subgroup.dvd_index_map -> Subgroup.dvd_index_map is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) (MonoidHom.ker.{u1, u2} G _inst_1 G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) f) H) -> (Dvd.Dvd.{0} Nat Nat.hasDvd (Subgroup.index.{u1} G _inst_1 H) (Subgroup.index.{u2} G' _inst_2 (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f H)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) (MonoidHom.ker.{u1, u2} G _inst_1 G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) f) H) -> (Dvd.dvd.{0} Nat Nat.instDvdNat (Subgroup.index.{u1} G _inst_1 H) (Subgroup.index.{u2} G' _inst_2 (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f H)))
Case conversion may be inaccurate. Consider using '#align subgroup.dvd_index_map Subgroup.dvd_index_mapₓ'. -/
@[to_additive]
theorem dvd_index_map {G' : Type _} [Group G'] {f : G →* G'} (hf : f.ker ≤ H) :
    H.index ∣ (H.map f).index := by
  rw [index_map, sup_of_le_left hf]
  apply dvd_mul_right
#align subgroup.dvd_index_map Subgroup.dvd_index_map
#align add_subgroup.dvd_index_map AddSubgroup.dvd_index_map

/- warning: subgroup.index_map_eq -> Subgroup.index_map_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))}, (Function.Surjective.{succ u1, succ u2} G G' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) => G -> G') (MonoidHom.hasCoeToFun.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) f)) -> (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) (MonoidHom.ker.{u1, u2} G _inst_1 G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) f) H) -> (Eq.{1} Nat (Subgroup.index.{u2} G' _inst_2 (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f H)) (Subgroup.index.{u1} G _inst_1 H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))}, (Function.Surjective.{succ u1, succ u2} G G' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : G) => G') _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) G G' (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))))) f)) -> (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) (MonoidHom.ker.{u1, u2} G _inst_1 G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) f) H) -> (Eq.{1} Nat (Subgroup.index.{u2} G' _inst_2 (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f H)) (Subgroup.index.{u1} G _inst_1 H))
Case conversion may be inaccurate. Consider using '#align subgroup.index_map_eq Subgroup.index_map_eqₓ'. -/
@[to_additive]
theorem index_map_eq {G' : Type _} [Group G'] {f : G →* G'} (hf1 : Function.Surjective f)
    (hf2 : f.ker ≤ H) : (H.map f).index = H.index :=
  Nat.dvd_antisymm (H.index_map_dvd hf1) (H.dvd_index_map hf2)
#align subgroup.index_map_eq Subgroup.index_map_eq
#align add_subgroup.index_map_eq AddSubgroup.index_map_eq

#print Subgroup.index_eq_card /-
@[to_additive]
theorem index_eq_card [Fintype (G ⧸ H)] : H.index = Fintype.card (G ⧸ H) :=
  Nat.card_eq_fintype_card
#align subgroup.index_eq_card Subgroup.index_eq_card
#align add_subgroup.index_eq_card AddSubgroup.index_eq_card
-/

/- warning: subgroup.index_mul_card -> Subgroup.index_mul_card is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_2 : Fintype.{u1} G] [hH : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)], Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Subgroup.index.{u1} G _inst_1 H) (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) hH)) (Fintype.card.{u1} G _inst_2)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_2 : Fintype.{u1} G] [hH : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))], Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Subgroup.index.{u1} G _inst_1 H) (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) hH)) (Fintype.card.{u1} G _inst_2)
Case conversion may be inaccurate. Consider using '#align subgroup.index_mul_card Subgroup.index_mul_cardₓ'. -/
@[to_additive index_mul_card]
theorem index_mul_card [Fintype G] [hH : Fintype H] : H.index * Fintype.card H = Fintype.card G :=
  by
  rw [← relindex_bot_left_eq_card, ← index_bot_eq_card, mul_comm] <;>
    exact relindex_mul_index bot_le
#align subgroup.index_mul_card Subgroup.index_mul_card
#align add_subgroup.index_mul_card AddSubgroup.index_mul_card

#print Subgroup.index_dvd_card /-
@[to_additive]
theorem index_dvd_card [Fintype G] : H.index ∣ Fintype.card G := by
  classical exact ⟨Fintype.card H, H.index_mul_card.symm⟩
#align subgroup.index_dvd_card Subgroup.index_dvd_card
#align add_subgroup.index_dvd_card AddSubgroup.index_dvd_card
-/

variable {H K L}

/- warning: subgroup.relindex_eq_zero_of_le_left -> Subgroup.relindex_eq_zero_of_le_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H K) -> (Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 K L) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H L) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K) -> (Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 K L) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H L) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_eq_zero_of_le_left Subgroup.relindex_eq_zero_of_le_leftₓ'. -/
@[to_additive]
theorem relindex_eq_zero_of_le_left (hHK : H ≤ K) (hKL : K.relindex L = 0) : H.relindex L = 0 :=
  eq_zero_of_zero_dvd (hKL ▸ relindex_dvd_of_le_left L hHK)
#align subgroup.relindex_eq_zero_of_le_left Subgroup.relindex_eq_zero_of_le_left
#align add_subgroup.relindex_eq_zero_of_le_left AddSubgroup.relindex_eq_zero_of_le_left

/- warning: subgroup.relindex_eq_zero_of_le_right -> Subgroup.relindex_eq_zero_of_le_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) K L) -> (Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H K) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H L) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) K L) -> (Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H K) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H L) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_eq_zero_of_le_right Subgroup.relindex_eq_zero_of_le_rightₓ'. -/
@[to_additive]
theorem relindex_eq_zero_of_le_right (hKL : K ≤ L) (hHK : H.relindex K = 0) : H.relindex L = 0 :=
  Finite.card_eq_zero_of_embedding (quotientSubgroupOfEmbeddingOfLe H hKL) hHK
#align subgroup.relindex_eq_zero_of_le_right Subgroup.relindex_eq_zero_of_le_right
#align add_subgroup.relindex_eq_zero_of_le_right AddSubgroup.relindex_eq_zero_of_le_right

#print Subgroup.index_eq_zero_of_relindex_eq_zero /-
@[to_additive]
theorem index_eq_zero_of_relindex_eq_zero (h : H.relindex K = 0) : H.index = 0 :=
  H.relindex_top_right.symm.trans (relindex_eq_zero_of_le_right le_top h)
#align subgroup.index_eq_zero_of_relindex_eq_zero Subgroup.index_eq_zero_of_relindex_eq_zero
#align add_subgroup.index_eq_zero_of_relindex_eq_zero AddSubgroup.index_eq_zero_of_relindex_eq_zero
-/

/- warning: subgroup.relindex_le_of_le_left -> Subgroup.relindex_le_of_le_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H K) -> (Ne.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H L) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (LE.le.{0} Nat Nat.hasLe (Subgroup.relindex.{u1} G _inst_1 K L) (Subgroup.relindex.{u1} G _inst_1 H L))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K) -> (Ne.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H L) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (LE.le.{0} Nat instLENat (Subgroup.relindex.{u1} G _inst_1 K L) (Subgroup.relindex.{u1} G _inst_1 H L))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_le_of_le_left Subgroup.relindex_le_of_le_leftₓ'. -/
@[to_additive]
theorem relindex_le_of_le_left (hHK : H ≤ K) (hHL : H.relindex L ≠ 0) :
    K.relindex L ≤ H.relindex L :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hHL) (relindex_dvd_of_le_left L hHK)
#align subgroup.relindex_le_of_le_left Subgroup.relindex_le_of_le_left
#align add_subgroup.relindex_le_of_le_left AddSubgroup.relindex_le_of_le_left

/- warning: subgroup.relindex_le_of_le_right -> Subgroup.relindex_le_of_le_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) K L) -> (Ne.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H L) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (LE.le.{0} Nat Nat.hasLe (Subgroup.relindex.{u1} G _inst_1 H K) (Subgroup.relindex.{u1} G _inst_1 H L))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) K L) -> (Ne.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H L) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (LE.le.{0} Nat instLENat (Subgroup.relindex.{u1} G _inst_1 H K) (Subgroup.relindex.{u1} G _inst_1 H L))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_le_of_le_right Subgroup.relindex_le_of_le_rightₓ'. -/
@[to_additive]
theorem relindex_le_of_le_right (hKL : K ≤ L) (hHL : H.relindex L ≠ 0) :
    H.relindex K ≤ H.relindex L :=
  Finite.card_le_of_embedding' (quotientSubgroupOfEmbeddingOfLe H hKL) fun h => (hHL h).elim
#align subgroup.relindex_le_of_le_right Subgroup.relindex_le_of_le_right
#align add_subgroup.relindex_le_of_le_right AddSubgroup.relindex_le_of_le_right

#print Subgroup.relindex_ne_zero_trans /-
@[to_additive]
theorem relindex_ne_zero_trans (hHK : H.relindex K ≠ 0) (hKL : K.relindex L ≠ 0) :
    H.relindex L ≠ 0 := fun h =>
  mul_ne_zero (mt (relindex_eq_zero_of_le_right (show K ⊓ L ≤ K from inf_le_left)) hHK) hKL
    ((relindex_inf_mul_relindex H K L).trans (relindex_eq_zero_of_le_left inf_le_left h))
#align subgroup.relindex_ne_zero_trans Subgroup.relindex_ne_zero_trans
#align add_subgroup.relindex_ne_zero_trans AddSubgroup.relindex_ne_zero_trans
-/

/- warning: subgroup.relindex_inf_ne_zero -> Subgroup.relindex_inf_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (Ne.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H L) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Ne.{1} Nat (Subgroup.relindex.{u1} G _inst_1 K L) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Ne.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K) L) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, (Ne.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H L) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Ne.{1} Nat (Subgroup.relindex.{u1} G _inst_1 K L) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Ne.{1} Nat (Subgroup.relindex.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K) L) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_inf_ne_zero Subgroup.relindex_inf_ne_zeroₓ'. -/
@[to_additive]
theorem relindex_inf_ne_zero (hH : H.relindex L ≠ 0) (hK : K.relindex L ≠ 0) :
    (H ⊓ K).relindex L ≠ 0 :=
  by
  replace hH : H.relindex (K ⊓ L) ≠ 0 := mt (relindex_eq_zero_of_le_right inf_le_right) hH
  rw [← inf_relindex_right] at hH hK⊢
  rw [inf_assoc]
  exact relindex_ne_zero_trans hH hK
#align subgroup.relindex_inf_ne_zero Subgroup.relindex_inf_ne_zero
#align add_subgroup.relindex_inf_ne_zero AddSubgroup.relindex_inf_ne_zero

/- warning: subgroup.index_inf_ne_zero -> Subgroup.index_inf_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (Ne.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Ne.{1} Nat (Subgroup.index.{u1} G _inst_1 K) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Ne.{1} Nat (Subgroup.index.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, (Ne.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Ne.{1} Nat (Subgroup.index.{u1} G _inst_1 K) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Ne.{1} Nat (Subgroup.index.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align subgroup.index_inf_ne_zero Subgroup.index_inf_ne_zeroₓ'. -/
@[to_additive]
theorem index_inf_ne_zero (hH : H.index ≠ 0) (hK : K.index ≠ 0) : (H ⊓ K).index ≠ 0 :=
  by
  rw [← relindex_top_right] at hH hK⊢
  exact relindex_inf_ne_zero hH hK
#align subgroup.index_inf_ne_zero Subgroup.index_inf_ne_zero
#align add_subgroup.index_inf_ne_zero AddSubgroup.index_inf_ne_zero

/- warning: subgroup.relindex_inf_le -> Subgroup.relindex_inf_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, LE.le.{0} Nat Nat.hasLe (Subgroup.relindex.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K) L) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Subgroup.relindex.{u1} G _inst_1 H L) (Subgroup.relindex.{u1} G _inst_1 K L))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} {L : Subgroup.{u1} G _inst_1}, LE.le.{0} Nat instLENat (Subgroup.relindex.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K) L) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Subgroup.relindex.{u1} G _inst_1 H L) (Subgroup.relindex.{u1} G _inst_1 K L))
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_inf_le Subgroup.relindex_inf_leₓ'. -/
@[to_additive]
theorem relindex_inf_le : (H ⊓ K).relindex L ≤ H.relindex L * K.relindex L :=
  by
  by_cases h : H.relindex L = 0
  · exact (le_of_eq (relindex_eq_zero_of_le_left inf_le_left h)).trans (zero_le _)
  rw [← inf_relindex_right, inf_assoc, ← relindex_mul_relindex _ _ L inf_le_right inf_le_right,
    inf_relindex_right, inf_relindex_right]
  exact mul_le_mul_right' (relindex_le_of_le_right inf_le_right h) (K.relindex L)
#align subgroup.relindex_inf_le Subgroup.relindex_inf_le
#align add_subgroup.relindex_inf_le AddSubgroup.relindex_inf_le

/- warning: subgroup.index_inf_le -> Subgroup.index_inf_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, LE.le.{0} Nat Nat.hasLe (Subgroup.index.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) H K)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Subgroup.index.{u1} G _inst_1 H) (Subgroup.index.{u1} G _inst_1 K))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, LE.le.{0} Nat instLENat (Subgroup.index.{u1} G _inst_1 (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) H K)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Subgroup.index.{u1} G _inst_1 H) (Subgroup.index.{u1} G _inst_1 K))
Case conversion may be inaccurate. Consider using '#align subgroup.index_inf_le Subgroup.index_inf_leₓ'. -/
@[to_additive]
theorem index_inf_le : (H ⊓ K).index ≤ H.index * K.index := by
  simp_rw [← relindex_top_right, relindex_inf_le]
#align subgroup.index_inf_le Subgroup.index_inf_le
#align add_subgroup.index_inf_le AddSubgroup.index_inf_le

#print Subgroup.relindex_infᵢ_ne_zero /-
@[to_additive]
theorem relindex_infᵢ_ne_zero {ι : Type _} [hι : Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).relindex L ≠ 0) : (⨅ i, f i).relindex L ≠ 0 :=
  haveI := Fintype.ofFinite ι
  (finset.prod_ne_zero_iff.mpr fun i hi => hf i) ∘
    nat.card_pi.symm.trans ∘
      Finite.card_eq_zero_of_embedding (quotient_infi_subgroup_of_embedding f L)
#align subgroup.relindex_infi_ne_zero Subgroup.relindex_infᵢ_ne_zero
#align add_subgroup.relindex_infi_ne_zero AddSubgroup.relindex_infᵢ_ne_zero
-/

#print Subgroup.relindex_infᵢ_le /-
@[to_additive]
theorem relindex_infᵢ_le {ι : Type _} [Fintype ι] (f : ι → Subgroup G) :
    (⨅ i, f i).relindex L ≤ ∏ i, (f i).relindex L :=
  le_of_le_of_eq
    (Finite.card_le_of_embedding' (quotientInfᵢSubgroupOfEmbedding f L) fun h =>
      let ⟨i, hi, h⟩ := Finset.prod_eq_zero_iff.mp (Nat.card_pi.symm.trans h)
      relindex_eq_zero_of_le_left (infᵢ_le f i) h)
    Nat.card_pi
#align subgroup.relindex_infi_le Subgroup.relindex_infᵢ_le
#align add_subgroup.relindex_infi_le AddSubgroup.relindex_infᵢ_le
-/

#print Subgroup.index_infᵢ_ne_zero /-
@[to_additive]
theorem index_infᵢ_ne_zero {ι : Type _} [Finite ι] {f : ι → Subgroup G}
    (hf : ∀ i, (f i).index ≠ 0) : (⨅ i, f i).index ≠ 0 :=
  by
  simp_rw [← relindex_top_right] at hf⊢
  exact relindex_infi_ne_zero hf
#align subgroup.index_infi_ne_zero Subgroup.index_infᵢ_ne_zero
#align add_subgroup.index_infi_ne_zero AddSubgroup.index_infᵢ_ne_zero
-/

#print Subgroup.index_infᵢ_le /-
@[to_additive]
theorem index_infᵢ_le {ι : Type _} [Fintype ι] (f : ι → Subgroup G) :
    (⨅ i, f i).index ≤ ∏ i, (f i).index := by simp_rw [← relindex_top_right, relindex_infi_le]
#align subgroup.index_infi_le Subgroup.index_infᵢ_le
#align add_subgroup.index_infi_le AddSubgroup.index_infᵢ_le
-/

/- warning: subgroup.index_eq_one -> Subgroup.index_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, Iff (Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, Iff (Eq.{1} Nat (Subgroup.index.{u1} G _inst_1 H) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align subgroup.index_eq_one Subgroup.index_eq_oneₓ'. -/
@[simp, to_additive index_eq_one]
theorem index_eq_one : H.index = 1 ↔ H = ⊤ :=
  ⟨fun h =>
    QuotientGroup.subgroup_eq_top_of_subsingleton H (Cardinal.toNat_eq_one_iff_unique.mp h).1,
    fun h => (congr_arg index h).trans index_top⟩
#align subgroup.index_eq_one Subgroup.index_eq_one
#align add_subgroup.index_eq_one AddSubgroup.index_eq_one

/- warning: subgroup.relindex_eq_one -> Subgroup.relindex_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, Iff (Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H K) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) K H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1}, Iff (Eq.{1} Nat (Subgroup.relindex.{u1} G _inst_1 H K) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) K H)
Case conversion may be inaccurate. Consider using '#align subgroup.relindex_eq_one Subgroup.relindex_eq_oneₓ'. -/
@[simp, to_additive relindex_eq_one]
theorem relindex_eq_one : H.relindex K = 1 ↔ K ≤ H :=
  index_eq_one.trans subgroupOf_eq_top
#align subgroup.relindex_eq_one Subgroup.relindex_eq_one
#align add_subgroup.relindex_eq_one AddSubgroup.relindex_eq_one

/- warning: subgroup.card_eq_one -> Subgroup.card_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, Iff (Eq.{1} Nat (Nat.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1}, Iff (Eq.{1} Nat (Nat.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align subgroup.card_eq_one Subgroup.card_eq_oneₓ'. -/
@[simp, to_additive card_eq_one]
theorem card_eq_one : Nat.card H = 1 ↔ H = ⊥ :=
  H.relindex_bot_left ▸ relindex_eq_one.trans le_bot_iff
#align subgroup.card_eq_one Subgroup.card_eq_one
#align add_subgroup.card_eq_one AddSubgroup.card_eq_one

#print Subgroup.index_ne_zero_of_finite /-
@[to_additive]
theorem index_ne_zero_of_finite [hH : Finite (G ⧸ H)] : H.index ≠ 0 :=
  by
  cases nonempty_fintype (G ⧸ H)
  rw [index_eq_card]
  exact Fintype.card_ne_zero
#align subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite
#align add_subgroup.index_ne_zero_of_finite AddSubgroup.index_ne_zero_of_finite
-/

#print Subgroup.fintypeOfIndexNeZero /-
/-- Finite index implies finite quotient. -/
@[to_additive "Finite index implies finite quotient."]
noncomputable def fintypeOfIndexNeZero (hH : H.index ≠ 0) : Fintype (G ⧸ H) :=
  (Cardinal.lt_aleph0_iff_fintype.mp (lt_of_not_ge (mt Cardinal.toNat_apply_of_aleph0_le hH))).some
#align subgroup.fintype_of_index_ne_zero Subgroup.fintypeOfIndexNeZero
#align add_subgroup.fintype_of_index_ne_zero AddSubgroup.fintypeOfIndexNeZero
-/

/- warning: subgroup.one_lt_index_of_ne_top -> Subgroup.one_lt_index_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} [_inst_2 : Finite.{succ u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.Subgroup.hasQuotient.{u1} G _inst_1) H)], (Ne.{succ u1} (Subgroup.{u1} G _inst_1) H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1))) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Subgroup.index.{u1} G _inst_1 H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} [_inst_2 : Finite.{succ u1} (HasQuotient.Quotient.{u1, u1} G (Subgroup.{u1} G _inst_1) (QuotientGroup.instHasQuotientSubgroup.{u1} G _inst_1) H)], (Ne.{succ u1} (Subgroup.{u1} G _inst_1) H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1))) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Subgroup.index.{u1} G _inst_1 H))
Case conversion may be inaccurate. Consider using '#align subgroup.one_lt_index_of_ne_top Subgroup.one_lt_index_of_ne_topₓ'. -/
@[to_additive one_lt_index_of_ne_top]
theorem one_lt_index_of_ne_top [Finite (G ⧸ H)] (hH : H ≠ ⊤) : 1 < H.index :=
  Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_finite, mt index_eq_one.mp hH⟩
#align subgroup.one_lt_index_of_ne_top Subgroup.one_lt_index_of_ne_top
#align add_subgroup.one_lt_index_of_ne_top AddSubgroup.one_lt_index_of_ne_top

section FiniteIndex

variable (H K)

#print Subgroup.FiniteIndex /-
/-- Typeclass for finite index subgroups. -/
class FiniteIndex : Prop where
  FiniteIndex : H.index ≠ 0
#align subgroup.finite_index Subgroup.FiniteIndex
-/

#print AddSubgroup.FiniteIndex /-
/-- Typeclass for finite index subgroups. -/
class AddSubgroup.FiniteIndex {G : Type _} [AddGroup G] (H : AddSubgroup G) : Prop where
  FiniteIndex : H.index ≠ 0
#align add_subgroup.finite_index AddSubgroup.FiniteIndex
-/

#print Subgroup.fintypeQuotientOfFiniteIndex /-
/-- A finite index subgroup has finite quotient. -/
@[to_additive "A finite index subgroup has finite quotient"]
noncomputable def fintypeQuotientOfFiniteIndex [FiniteIndex H] : Fintype (G ⧸ H) :=
  fintypeOfIndexNeZero FiniteIndex.finiteIndex
#align subgroup.fintype_quotient_of_finite_index Subgroup.fintypeQuotientOfFiniteIndex
#align add_subgroup.fintype_quotient_of_finite_index AddSubgroup.fintypeQuotientOfFiniteIndex
-/

#print Subgroup.finite_quotient_of_finiteIndex /-
@[to_additive]
instance finite_quotient_of_finiteIndex [FiniteIndex H] : Finite (G ⧸ H) :=
  H.fintypeQuotientOfFiniteIndex.Finite
#align subgroup.finite_quotient_of_finite_index Subgroup.finite_quotient_of_finiteIndex
#align add_subgroup.finite_quotient_of_finite_index AddSubgroup.finite_quotient_of_finiteIndex
-/

#print Subgroup.finiteIndex_of_finite_quotient /-
@[to_additive]
theorem finiteIndex_of_finite_quotient [Finite (G ⧸ H)] : FiniteIndex H :=
  ⟨index_ne_zero_of_finite⟩
#align subgroup.finite_index_of_finite_quotient Subgroup.finiteIndex_of_finite_quotient
#align add_subgroup.finite_index_of_finite_quotient AddSubgroup.finiteIndex_of_finite_quotient
-/

#print Subgroup.finiteIndex_of_finite /-
@[to_additive]
instance (priority := 100) finiteIndex_of_finite [Finite G] : FiniteIndex H :=
  finiteIndex_of_finite_quotient H
#align subgroup.finite_index_of_finite Subgroup.finiteIndex_of_finite
#align add_subgroup.finite_index_of_finite AddSubgroup.finiteIndex_of_finite
-/

@[to_additive]
instance : FiniteIndex (⊤ : Subgroup G) :=
  ⟨ne_of_eq_of_ne index_top one_ne_zero⟩

@[to_additive]
instance [FiniteIndex H] [FiniteIndex K] : FiniteIndex (H ⊓ K) :=
  ⟨index_inf_ne_zero FiniteIndex.finiteIndex FiniteIndex.finiteIndex⟩

variable {H K}

/- warning: subgroup.finite_index_of_le -> Subgroup.finiteIndex_of_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} [_inst_2 : Subgroup.FiniteIndex.{u1} G _inst_1 H], (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H K) -> (Subgroup.FiniteIndex.{u1} G _inst_1 K)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {H : Subgroup.{u1} G _inst_1} {K : Subgroup.{u1} G _inst_1} [_inst_2 : Subgroup.FiniteIndex.{u1} G _inst_1 H], (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H K) -> (Subgroup.FiniteIndex.{u1} G _inst_1 K)
Case conversion may be inaccurate. Consider using '#align subgroup.finite_index_of_le Subgroup.finiteIndex_of_leₓ'. -/
@[to_additive]
theorem finiteIndex_of_le [FiniteIndex H] (h : H ≤ K) : FiniteIndex K :=
  ⟨ne_zero_of_dvd_ne_zero FiniteIndex.finiteIndex (index_dvd_of_le h)⟩
#align subgroup.finite_index_of_le Subgroup.finiteIndex_of_le
#align add_subgroup.finite_index_of_le AddSubgroup.finiteIndex_of_le

variable (H K)

/- warning: subgroup.finite_index_ker -> Subgroup.finiteIndex_ker is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] (f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) [_inst_3 : Finite.{succ u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G' _inst_2) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G' _inst_2) G' (Subgroup.setLike.{u2} G' _inst_2)) (MonoidHom.range.{u1, u2} G _inst_1 G' _inst_2 f))], Subgroup.FiniteIndex.{u1} G _inst_1 (MonoidHom.ker.{u1, u2} G _inst_1 G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) f)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {G' : Type.{u2}} [_inst_2 : Group.{u2} G'] (f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) [_inst_3 : Finite.{succ u2} (Subtype.{succ u2} G' (fun (x : G') => Membership.mem.{u2, u2} G' (Subgroup.{u2} G' _inst_2) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G' _inst_2) G' (Subgroup.instSetLikeSubgroup.{u2} G' _inst_2)) x (MonoidHom.range.{u1, u2} G _inst_1 G' _inst_2 f)))], Subgroup.FiniteIndex.{u1} G _inst_1 (MonoidHom.ker.{u1, u2} G _inst_1 G' (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align subgroup.finite_index_ker Subgroup.finiteIndex_kerₓ'. -/
@[to_additive]
instance finiteIndex_ker {G' : Type _} [Group G'] (f : G →* G') [Finite f.range] :
    f.ker.FiniteIndex :=
  @finiteIndex_of_finite_quotient G _ f.ker
    (Finite.of_equiv f.range (QuotientGroup.quotientKerEquivRange f).symm)
#align subgroup.finite_index_ker Subgroup.finiteIndex_ker
#align add_subgroup.finite_index_ker AddSubgroup.finiteIndex_ker

#print Subgroup.finiteIndex_normalCore /-
instance finiteIndex_normalCore [H.FiniteIndex] : H.normalCore.FiniteIndex :=
  by
  rw [normal_core_eq_ker]
  infer_instance
#align subgroup.finite_index_normal_core Subgroup.finiteIndex_normalCore
-/

variable (G)

#print Subgroup.finiteIndex_center /-
instance finiteIndex_center [Finite (commutatorSet G)] [Group.Fg G] : FiniteIndex (center G) :=
  by
  obtain ⟨S, -, hS⟩ := Group.rank_spec G
  exact ⟨mt (Finite.card_eq_zero_of_embedding (quotient_center_embedding hS)) finite.card_pos.ne'⟩
#align subgroup.finite_index_center Subgroup.finiteIndex_center
-/

#print Subgroup.index_center_le_pow /-
theorem index_center_le_pow [Finite (commutatorSet G)] [Group.Fg G] :
    (center G).index ≤ Nat.card (commutatorSet G) ^ Group.rank G :=
  by
  obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
  rw [← hS1, ← Fintype.card_coe, ← Nat.card_eq_fintype_card, ← Finset.coe_sort_coe, ← Nat.card_fun]
  exact Finite.card_le_of_embedding (quotient_center_embedding hS2)
#align subgroup.index_center_le_pow Subgroup.index_center_le_pow
-/

end FiniteIndex

end Subgroup

