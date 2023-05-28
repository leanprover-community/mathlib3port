/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang

! This file was ported from Lean 3 source module ring_theory.polynomial.vieta
! leanprover-community/mathlib commit 31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Splits
import Mathbin.RingTheory.MvPolynomial.Symmetric

/-!
# Vieta's Formula

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The main result is `multiset.prod_X_add_C_eq_sum_esymm`, which shows that the product of
linear terms `X + λ` with `λ` in a `multiset s` is equal to a linear combination of the
symmetric functions `esymm s`.

From this, we deduce `mv_polynomial.prod_X_add_C_eq_sum_esymm` which is the equivalent formula
for the product of linear terms `X + X i` with `i` in a `fintype σ` as a linear combination
of the symmetric polynomials `esymm σ R j`.

For `R` be an integral domain (so that `p.roots` is defined for any `p : R[X]` as a multiset),
we derive `polynomial.coeff_eq_esymm_roots_of_card`, the relationship between the coefficients and
the roots of `p` for a polynomial `p` that splits (i.e. having as many roots as its degree).
-/


open BigOperators Polynomial

namespace Multiset

open Polynomial

section Semiring

variable {R : Type _} [CommSemiring R]

/- warning: multiset.prod_X_add_C_eq_sum_esymm -> Multiset.prod_X_add_C_eq_sum_esymm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align multiset.prod_X_add_C_eq_sum_esymm Multiset.prod_X_add_C_eq_sum_esymmₓ'. -/
/-- A sum version of Vieta's formula for `multiset`: the product of the linear terms `X + λ` where
`λ` runs through a multiset `s` is equal to a linear combination of the symmetric functions
`esymm s` of the `λ`'s .-/
theorem prod_X_add_C_eq_sum_esymm (s : Multiset R) :
    (s.map fun r => X + C r).Prod =
      ∑ j in Finset.range (s.card + 1), C (s.esymm j) * X ^ (s.card - j) :=
  by
  classical
    rw [prod_map_add, antidiagonal_eq_map_powerset, map_map, ← bind_powerset_len, Function.comp,
      map_bind, sum_bind, Finset.sum_eq_multiset_sum, Finset.range_val, map_congr (Eq.refl _)]
    intro _ _
    rw [esymm, ← sum_hom', ← sum_map_mul_right, map_congr (Eq.refl _)]
    intro _ ht
    rw [mem_powerset_len] at ht
    simp [ht, map_const, prod_replicate, prod_hom', map_id', card_sub]
#align multiset.prod_X_add_C_eq_sum_esymm Multiset.prod_X_add_C_eq_sum_esymm

/- warning: multiset.prod_X_add_C_coeff -> Multiset.prod_X_add_C_coeff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align multiset.prod_X_add_C_coeff Multiset.prod_X_add_C_coeffₓ'. -/
/-- Vieta's formula for the coefficients of the product of linear terms `X + λ` where `λ` runs
through a multiset `s` : the `k`th coefficient is the symmetric function `esymm (card s - k) s`. -/
theorem prod_X_add_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ s.card) :
    (s.map fun r => X + C r).Prod.coeff k = s.esymm (s.card - k) :=
  by
  convert polynomial.ext_iff.mp (prod_X_add_C_eq_sum_esymm s) k
  simp_rw [finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single_of_mem (s.card - k) _]
  · rw [if_pos (Nat.sub_sub_self h).symm]
  · intro j hj1 hj2
    suffices k ≠ card s - j by rw [if_neg this]
    · intro hn
      rw [hn, Nat.sub_sub_self (nat.lt_succ_iff.mp (finset.mem_range.mp hj1))] at hj2
      exact Ne.irrefl hj2
  · rw [Finset.mem_range]
    exact Nat.sub_lt_succ s.card k
#align multiset.prod_X_add_C_coeff Multiset.prod_X_add_C_coeff

/- warning: multiset.prod_X_add_C_coeff' -> Multiset.prod_X_add_C_coeff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align multiset.prod_X_add_C_coeff' Multiset.prod_X_add_C_coeff'ₓ'. -/
theorem prod_X_add_C_coeff' {σ} (s : Multiset σ) (r : σ → R) {k : ℕ} (h : k ≤ s.card) :
    (s.map fun i => X + C (r i)).Prod.coeff k = (s.map r).esymm (s.card - k) := by
  rw [← map_map (fun r => X + C r) r, prod_X_add_C_coeff] <;> rwa [s.card_map r]
#align multiset.prod_X_add_C_coeff' Multiset.prod_X_add_C_coeff'

/- warning: finset.prod_X_add_C_coeff -> Finset.prod_X_add_C_coeff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align finset.prod_X_add_C_coeff Finset.prod_X_add_C_coeffₓ'. -/
theorem Finset.prod_X_add_C_coeff {σ} (s : Finset σ) (r : σ → R) {k : ℕ} (h : k ≤ s.card) :
    (∏ i in s, X + C (r i)).coeff k = ∑ t in s.powersetLen (s.card - k), ∏ i in t, r i := by
  rw [Finset.prod, prod_X_add_C_coeff' _ r h, Finset.esymm_map_val]; rfl
#align finset.prod_X_add_C_coeff Finset.prod_X_add_C_coeff

end Semiring

section Ring

variable {R : Type _} [CommRing R]

/- warning: multiset.esymm_neg -> Multiset.esymm_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (s : Multiset.{u1} R) (k : Nat), Eq.{succ u1} R (Multiset.esymm.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Multiset.map.{u1, u1} R R (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) s) k) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))))))) k) (Multiset.esymm.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) s k))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (s : Multiset.{u1} R) (k : Nat), Eq.{succ u1} R (Multiset.esymm.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Multiset.map.{u1, u1} R R (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1))) s) k) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) k) (Multiset.esymm.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) s k))
Case conversion may be inaccurate. Consider using '#align multiset.esymm_neg Multiset.esymm_negₓ'. -/
theorem esymm_neg (s : Multiset R) (k : ℕ) : (map Neg.neg s).esymm k = (-1) ^ k * esymm s k :=
  by
  rw [esymm, esymm, ← Multiset.sum_map_mul_left, Multiset.powersetLen_map, Multiset.map_map,
    map_congr (Eq.refl _)]
  intro x hx
  rw [(mem_powerset_len.mp hx).right.symm, ← prod_replicate, ← Multiset.map_const]
  nth_rw 3 [← map_id' x]
  rw [← prod_map_mul, map_congr (Eq.refl _)]
  exact fun z _ => neg_one_mul z
#align multiset.esymm_neg Multiset.esymm_neg

/- warning: multiset.prod_X_sub_C_eq_sum_esymm -> Multiset.prod_X_sub_X_eq_sum_esymm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align multiset.prod_X_sub_C_eq_sum_esymm Multiset.prod_X_sub_X_eq_sum_esymmₓ'. -/
theorem prod_X_sub_X_eq_sum_esymm (s : Multiset R) :
    (s.map fun t => X - C t).Prod =
      ∑ j in Finset.range (s.card + 1), (-1) ^ j * (C (s.esymm j) * X ^ (s.card - j)) :=
  by
  conv_lhs =>
    congr
    congr
    ext
    rw [sub_eq_add_neg]
    rw [← map_neg C _]
  convert prod_X_add_C_eq_sum_esymm (map (fun t => -t) s) using 1
  · rwa [map_map]
  · simp only [esymm_neg, card_map, mul_assoc, map_mul, map_pow, map_neg, map_one]
#align multiset.prod_X_sub_C_eq_sum_esymm Multiset.prod_X_sub_X_eq_sum_esymm

/- warning: multiset.prod_X_sub_C_coeff -> Multiset.prod_X_sub_C_coeff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align multiset.prod_X_sub_C_coeff Multiset.prod_X_sub_C_coeffₓ'. -/
theorem prod_X_sub_C_coeff (s : Multiset R) {k : ℕ} (h : k ≤ s.card) :
    (s.map fun t => X - C t).Prod.coeff k = (-1) ^ (s.card - k) * s.esymm (s.card - k) :=
  by
  conv_lhs =>
    congr
    congr
    congr
    ext
    rw [sub_eq_add_neg]
    rw [← map_neg C _]
  convert prod_X_add_C_coeff (map (fun t => -t) s) _ using 1
  · rwa [map_map]
  · rwa [esymm_neg, card_map]
  · rwa [card_map]
#align multiset.prod_X_sub_C_coeff Multiset.prod_X_sub_C_coeff

/- warning: polynomial.coeff_eq_esymm_roots_of_card -> Polynomial.coeff_eq_esymm_roots_of_card is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] {p : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))}, (Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} R) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} R) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} R) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} R) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} R) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} R) (Multiset.orderedCancelAddCommMonoid.{u1} R)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} R) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} R) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} R) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} R) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} R) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} R) (Multiset.orderedCancelAddCommMonoid.{u1} R)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} R) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} R) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} R) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} R) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} R) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} R) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} R) (Multiset.orderedCancelAddCommMonoid.{u1} R)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} R) (Polynomial.roots.{u1} R _inst_1 _inst_2 p)) (Polynomial.natDegree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p)) -> (forall {k : Nat}, (LE.le.{0} Nat Nat.hasLe k (Polynomial.natDegree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p k) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Polynomial.leadingCoeff.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))))))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Polynomial.natDegree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p) k))) (Multiset.esymm.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Polynomial.roots.{u1} R _inst_1 _inst_2 p) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Polynomial.natDegree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) p) k)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))] {p : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))}, (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} R) => Nat) (Polynomial.roots.{u1} R _inst_1 _inst_2 p)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} R) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} R) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} R) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} R) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} R) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} R) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} R)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} R) (fun (_x : Multiset.{u1} R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} R) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} R) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} R) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} R) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} R) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} R) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} R) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} R)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} R) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} R) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} R) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} R) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} R) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} R) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} R) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} R))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} R) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} R) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} R) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} R) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} R) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} R) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} R)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} R) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} R) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} R) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} R) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} R) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} R) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} R)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} R) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} R) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} R) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} R) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} R) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} R) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} R)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} R) (Polynomial.roots.{u1} R _inst_1 _inst_2 p)) (Polynomial.natDegree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) p)) -> (forall {k : Nat}, (LE.le.{0} Nat instLENat k (Polynomial.natDegree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) p)) -> (Eq.{succ u1} R (Polynomial.coeff.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) p k) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Polynomial.leadingCoeff.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) p) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Polynomial.natDegree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) p) k))) (Multiset.esymm.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) (Polynomial.roots.{u1} R _inst_1 _inst_2 p) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Polynomial.natDegree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) p) k)))))
Case conversion may be inaccurate. Consider using '#align polynomial.coeff_eq_esymm_roots_of_card Polynomial.coeff_eq_esymm_roots_of_cardₓ'. -/
/-- Vieta's formula for the coefficients and the roots of a polynomial over an integral domain
  with as many roots as its degree. -/
theorem Polynomial.coeff_eq_esymm_roots_of_card [IsDomain R] {p : R[X]}
    (hroots : p.roots.card = p.natDegree) {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) :=
  by
  conv_lhs => rw [← C_leading_coeff_mul_prod_multiset_X_sub_C hroots]
  rw [coeff_C_mul, mul_assoc]; congr
  convert p.roots.prod_X_sub_C_coeff _ using 3 <;> rw [hroots]; exact h
#align polynomial.coeff_eq_esymm_roots_of_card Polynomial.coeff_eq_esymm_roots_of_card

/- warning: polynomial.coeff_eq_esymm_roots_of_splits -> Polynomial.coeff_eq_esymm_roots_of_splits is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_2 : Field.{u1} F] {p : Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2)))}, (Polynomial.Splits.{u1, u1} F F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_2)) _inst_2 (RingHom.id.{u1} F (NonAssocRing.toNonAssocSemiring.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))))) p) -> (forall {k : Nat}, (LE.le.{0} Nat Nat.hasLe k (Polynomial.natDegree.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))) p)) -> (Eq.{succ u1} F (Polynomial.coeff.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))) p k) (HMul.hMul.{u1, u1, u1} F F F (instHMul.{u1} F (Distrib.toHasMul.{u1} F (Ring.toDistrib.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))))) (HMul.hMul.{u1, u1, u1} F F F (instHMul.{u1} F (Distrib.toHasMul.{u1} F (Ring.toDistrib.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))))) (Polynomial.leadingCoeff.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))) p) (HPow.hPow.{u1, 0, u1} F Nat F (instHPow.{u1, 0} F Nat (Monoid.Pow.{u1} F (Ring.toMonoid.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))))) (Neg.neg.{u1} F (SubNegMonoid.toHasNeg.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddGroupWithOne.toAddGroup.{u1} F (AddCommGroupWithOne.toAddGroupWithOne.{u1} F (Ring.toAddCommGroupWithOne.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))))))) (OfNat.ofNat.{u1} F 1 (OfNat.mk.{u1} F 1 (One.one.{u1} F (AddMonoidWithOne.toOne.{u1} F (AddGroupWithOne.toAddMonoidWithOne.{u1} F (AddCommGroupWithOne.toAddGroupWithOne.{u1} F (Ring.toAddCommGroupWithOne.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2)))))))))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Polynomial.natDegree.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))) p) k))) (Multiset.esymm.{u1} F (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2)) (Polynomial.roots.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_2)) (Field.isDomain.{u1} F _inst_2) p) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Polynomial.natDegree.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))) p) k)))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_2 : Field.{u1} F] {p : Polynomial.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2)))}, (Polynomial.Splits.{u1, u1} F F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_2)) _inst_2 (RingHom.id.{u1} F (Semiring.toNonAssocSemiring.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2))))) p) -> (forall {k : Nat}, (LE.le.{0} Nat instLENat k (Polynomial.natDegree.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2))) p)) -> (Eq.{succ u1} F (Polynomial.coeff.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2))) p k) (HMul.hMul.{u1, u1, u1} F F F (instHMul.{u1} F (NonUnitalNonAssocRing.toMul.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2)))))) (HMul.hMul.{u1, u1, u1} F F F (instHMul.{u1} F (NonUnitalNonAssocRing.toMul.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2)))))) (Polynomial.leadingCoeff.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2))) p) (HPow.hPow.{u1, 0, u1} F Nat F (instHPow.{u1, 0} F Nat (Monoid.Pow.{u1} F (MonoidWithZero.toMonoid.{u1} F (Semiring.toMonoidWithZero.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2))))))) (Neg.neg.{u1} F (Ring.toNeg.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_2))) (OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F (Semiring.toOne.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2))))))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Polynomial.natDegree.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2))) p) k))) (Multiset.esymm.{u1} F (Semifield.toCommSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2)) (Polynomial.roots.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_2)) (Field.isDomain.{u1} F _inst_2) p) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Polynomial.natDegree.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_2))) p) k)))))
Case conversion may be inaccurate. Consider using '#align polynomial.coeff_eq_esymm_roots_of_splits Polynomial.coeff_eq_esymm_roots_of_splitsₓ'. -/
/-- Vieta's formula for split polynomials over a field. -/
theorem Polynomial.coeff_eq_esymm_roots_of_splits {F} [Field F] {p : F[X]}
    (hsplit : p.Splits (RingHom.id F)) {k : ℕ} (h : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * p.roots.esymm (p.natDegree - k) :=
  Polynomial.coeff_eq_esymm_roots_of_card (splits_iff_card_roots.1 hsplit) h
#align polynomial.coeff_eq_esymm_roots_of_splits Polynomial.coeff_eq_esymm_roots_of_splits

end Ring

end Multiset

section MvPolynomial

open Finset Polynomial Fintype

variable (R σ : Type _) [CommSemiring R] [Fintype σ]

/- warning: mv_polynomial.prod_C_add_X_eq_sum_esymm -> MvPolynomial.prod_C_add_X_eq_sum_esymm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.prod_C_add_X_eq_sum_esymm MvPolynomial.prod_C_add_X_eq_sum_esymmₓ'. -/
/-- A sum version of Vieta's formula for `mv_polynomial`: viewing `X i` as variables,
the product of linear terms `λ + X i` is equal to a linear combination of
the symmetric polynomials `esymm σ R j`. -/
theorem MvPolynomial.prod_C_add_X_eq_sum_esymm :
    (∏ i : σ, X + C (MvPolynomial.X i)) =
      ∑ j in range (card σ + 1), C (MvPolynomial.esymm σ R j) * X ^ (card σ - j) :=
  by
  let s := finset.univ.val.map fun i : σ => MvPolynomial.X i
  rw [(_ : card σ = s.card)]
  · simp_rw [MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
    convert Multiset.prod_X_add_C_eq_sum_esymm s
    rwa [Multiset.map_map]
  · rw [Multiset.card_map]; rfl
#align mv_polynomial.prod_C_add_X_eq_sum_esymm MvPolynomial.prod_C_add_X_eq_sum_esymm

/- warning: mv_polynomial.prod_X_add_C_coeff -> MvPolynomial.prod_X_add_C_coeff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.prod_X_add_C_coeff MvPolynomial.prod_X_add_C_coeffₓ'. -/
theorem MvPolynomial.prod_X_add_C_coeff (k : ℕ) (h : k ≤ card σ) :
    (∏ i : σ, X + C (MvPolynomial.X i)).coeff k = MvPolynomial.esymm σ R (card σ - k) :=
  by
  let s := finset.univ.val.map fun i => (MvPolynomial.X i : MvPolynomial σ R)
  rw [(_ : card σ = s.card)] at h⊢
  · rw [MvPolynomial.esymm_eq_multiset_esymm σ R, Finset.prod_eq_multiset_prod]
    convert Multiset.prod_X_add_C_coeff s h
    rwa [Multiset.map_map]
  repeat' rw [Multiset.card_map]; rfl
#align mv_polynomial.prod_X_add_C_coeff MvPolynomial.prod_X_add_C_coeff

end MvPolynomial

