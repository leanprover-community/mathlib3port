/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker

! This file was ported from Lean 3 source module data.polynomial.monic
! leanprover-community/mathlib commit cbdf7b565832144d024caa5a550117c6df0204a5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Reverse
import Mathbin.Algebra.Regular.Smul

/-!
# Theory of monic polynomials

We give several tools for proving that polynomials are monic, e.g.
`monic.mul`, `monic.map`, `monic.pow`.
-/


noncomputable section

open Finset

open BigOperators Classical Polynomial

namespace Polynomial

universe u v y

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section Semiring

variable [Semiring R] {p q r : R[X]}

#print Polynomial.monic_zero_iff_subsingleton /-
theorem monic_zero_iff_subsingleton : Monic (0 : R[X]) ↔ Subsingleton R :=
  subsingleton_iff_zero_eq_one
#align polynomial.monic_zero_iff_subsingleton Polynomial.monic_zero_iff_subsingleton
-/

/- warning: polynomial.not_monic_zero_iff -> Polynomial.not_monic_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], Iff (Not (Polynomial.Monic.{u1} R _inst_1 (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.zero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1)))))) (Ne.{succ u1} R (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], Iff (Not (Polynomial.Monic.{u1} R _inst_1 (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1))))) (Ne.{succ u1} R (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align polynomial.not_monic_zero_iff Polynomial.not_monic_zero_iffₓ'. -/
theorem not_monic_zero_iff : ¬Monic (0 : R[X]) ↔ (0 : R) ≠ 1 :=
  (monic_zero_iff_subsingleton.trans subsingleton_iff_zero_eq_one.symm).Not
#align polynomial.not_monic_zero_iff Polynomial.not_monic_zero_iff

#print Polynomial.monic_zero_iff_subsingleton' /-
theorem monic_zero_iff_subsingleton' :
    Monic (0 : R[X]) ↔ (∀ f g : R[X], f = g) ∧ ∀ a b : R, a = b :=
  Polynomial.monic_zero_iff_subsingleton.trans
    ⟨by
      intro
      simp, fun h => subsingleton_iff.mpr h.2⟩
#align polynomial.monic_zero_iff_subsingleton' Polynomial.monic_zero_iff_subsingleton'
-/

/- warning: polynomial.monic.as_sum -> Polynomial.Monic.as_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, (Polynomial.Monic.{u1} R _inst_1 p) -> (Eq.{succ u1} (Polynomial.{u1} R _inst_1) p (HAdd.hAdd.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHAdd.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.add'.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (Polynomial.X.{u1} R _inst_1) (Polynomial.natDegree.{u1} R _inst_1 p)) (Finset.sum.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Finset.range (Polynomial.natDegree.{u1} R _inst_1 p)) (fun (i : Nat) => HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) (Polynomial.coeff.{u1} R _inst_1 p i)) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (Polynomial.X.{u1} R _inst_1) i)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1}, (Polynomial.Monic.{u1} R _inst_1 p) -> (Eq.{succ u1} (Polynomial.{u1} R _inst_1) p (HAdd.hAdd.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHAdd.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.add'.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (Polynomial.X.{u1} R _inst_1) (Polynomial.natDegree.{u1} R _inst_1 p)) (Finset.sum.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (Finset.range (Polynomial.natDegree.{u1} R _inst_1 p)) (fun (i : Nat) => HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) (Polynomial.coeff.{u1} R _inst_1 p i)) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) (Polynomial.coeff.{u1} R _inst_1 p i)) (Polynomial.mul'.{u1} R _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) (Polynomial.coeff.{u1} R _inst_1 p i)) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (Polynomial.X.{u1} R _inst_1) i)))))
Case conversion may be inaccurate. Consider using '#align polynomial.monic.as_sum Polynomial.Monic.as_sumₓ'. -/
theorem Monic.as_sum (hp : p.Monic) :
    p = X ^ p.natDegree + ∑ i in range p.natDegree, C (p.coeff i) * X ^ i :=
  by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow, sum_range_succ_comm]
  suffices C (p.coeff p.nat_degree) = 1 by rw [this, one_mul]
  exact congr_arg C hp
#align polynomial.monic.as_sum Polynomial.Monic.as_sum

#print Polynomial.ne_zero_of_ne_zero_of_monic /-
theorem ne_zero_of_ne_zero_of_monic (hp : p ≠ 0) (hq : Monic q) : q ≠ 0 :=
  by
  rintro rfl
  rw [monic.def, leading_coeff_zero] at hq
  rw [← mul_one p, ← C_1, ← hq, C_0, MulZeroClass.mul_zero] at hp
  exact hp rfl
#align polynomial.ne_zero_of_ne_zero_of_monic Polynomial.ne_zero_of_ne_zero_of_monic
-/

#print Polynomial.Monic.map /-
theorem Monic.map [Semiring S] (f : R →+* S) (hp : Monic p) : Monic (p.map f) :=
  by
  nontriviality
  have : f (leading_coeff p) ≠ 0 :=
    by
    rw [show _ = _ from hp, f.map_one]
    exact one_ne_zero
  rw [monic, leading_coeff, coeff_map]
  suffices p.coeff (map f p).natDegree = 1 by simp [this]
  rwa [nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero f this)]
#align polynomial.monic.map Polynomial.Monic.map
-/

/- warning: polynomial.monic_C_mul_of_mul_leading_coeff_eq_one -> Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {b : R}, (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) b (Polynomial.leadingCoeff.{u1} R _inst_1 p)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (Polynomial.Monic.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) b) p))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {b : R}, (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) b (Polynomial.leadingCoeff.{u1} R _inst_1 p)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_1)))) -> (Polynomial.Monic.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) b) (Polynomial.{u1} R _inst_1) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) b) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) b) (Polynomial.mul'.{u1} R _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) b) p))
Case conversion may be inaccurate. Consider using '#align polynomial.monic_C_mul_of_mul_leading_coeff_eq_one Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_oneₓ'. -/
theorem monic_C_mul_of_mul_leadingCoeff_eq_one {b : R} (hp : b * p.leadingCoeff = 1) :
    Monic (C b * p) := by
  nontriviality
  rw [monic, leading_coeff_mul' _] <;> simp [leading_coeff_C b, hp]
#align polynomial.monic_C_mul_of_mul_leading_coeff_eq_one Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one

/- warning: polynomial.monic_mul_C_of_leading_coeff_mul_eq_one -> Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {b : R}, (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Polynomial.leadingCoeff.{u1} R _inst_1 p) b) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) -> (Polynomial.Monic.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) b)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {b : R}, (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Polynomial.leadingCoeff.{u1} R _inst_1 p) b) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_1)))) -> (Polynomial.Monic.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) b) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) b)))
Case conversion may be inaccurate. Consider using '#align polynomial.monic_mul_C_of_leading_coeff_mul_eq_one Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_oneₓ'. -/
theorem monic_mul_C_of_leadingCoeff_mul_eq_one {b : R} (hp : p.leadingCoeff * b = 1) :
    Monic (p * C b) := by
  nontriviality
  rw [monic, leading_coeff_mul' _] <;> simp [leading_coeff_C b, hp]
#align polynomial.monic_mul_C_of_leading_coeff_mul_eq_one Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one

#print Polynomial.monic_of_degree_le /-
theorem monic_of_degree_le (n : ℕ) (H1 : degree p ≤ n) (H2 : coeff p n = 1) : Monic p :=
  Decidable.byCases
    (fun H : degree p < n => eq_of_zero_eq_one (H2 ▸ (coeff_eq_zero_of_degree_lt H).symm) _ _)
    fun H : ¬degree p < n => by
    rwa [monic, leading_coeff, nat_degree, (lt_or_eq_of_le H1).resolve_left H]
#align polynomial.monic_of_degree_le Polynomial.monic_of_degree_le
-/

#print Polynomial.monic_X_pow_add /-
theorem monic_X_pow_add {n : ℕ} (H : degree p ≤ n) : Monic (X ^ (n + 1) + p) :=
  have H1 : degree p < n + 1 := lt_of_le_of_lt H (WithBot.coe_lt_coe.2 (Nat.lt_succ_self n))
  monic_of_degree_le (n + 1)
    (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H1)))
    (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H1, add_zero])
#align polynomial.monic_X_pow_add Polynomial.monic_X_pow_add
-/

/- warning: polynomial.monic_X_add_C -> Polynomial.monic_X_add_C is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (x : R), Polynomial.Monic.{u1} R _inst_1 (HAdd.hAdd.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHAdd.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.add'.{u1} R _inst_1)) (Polynomial.X.{u1} R _inst_1) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (x : R), Polynomial.Monic.{u1} R _inst_1 (HAdd.hAdd.{u1, u1, u1} (Polynomial.{u1} R _inst_1) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) x) (Polynomial.{u1} R _inst_1) (instHAdd.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.add'.{u1} R _inst_1)) (Polynomial.X.{u1} R _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) x))
Case conversion may be inaccurate. Consider using '#align polynomial.monic_X_add_C Polynomial.monic_X_add_Cₓ'. -/
theorem monic_X_add_C (x : R) : Monic (X + C x) :=
  pow_one (X : R[X]) ▸ monic_X_pow_add degree_C_le
#align polynomial.monic_X_add_C Polynomial.monic_X_add_C

#print Polynomial.Monic.mul /-
theorem Monic.mul (hp : Monic p) (hq : Monic q) : Monic (p * q) :=
  if h0 : (0 : R) = 1 then
    haveI := subsingleton_of_zero_eq_one h0
    Subsingleton.elim _ _
  else
    by
    have : leadingCoeff p * leadingCoeff q ≠ 0 := by
      simp [monic.def.1 hp, monic.def.1 hq, Ne.symm h0]
    rw [monic.def, leading_coeff_mul' this, monic.def.1 hp, monic.def.1 hq, one_mul]
#align polynomial.monic.mul Polynomial.Monic.mul
-/

#print Polynomial.Monic.pow /-
theorem Monic.pow (hp : Monic p) : ∀ n : ℕ, Monic (p ^ n)
  | 0 => monic_one
  | n + 1 => by
    rw [pow_succ]
    exact hp.mul (monic.pow n)
#align polynomial.monic.pow Polynomial.Monic.pow
-/

#print Polynomial.Monic.add_of_left /-
theorem Monic.add_of_left (hp : Monic p) (hpq : degree q < degree p) : Monic (p + q) := by
  rwa [monic, add_comm, leading_coeff_add_of_degree_lt hpq]
#align polynomial.monic.add_of_left Polynomial.Monic.add_of_left
-/

#print Polynomial.Monic.add_of_right /-
theorem Monic.add_of_right (hq : Monic q) (hpq : degree p < degree q) : Monic (p + q) := by
  rwa [monic, leading_coeff_add_of_degree_lt hpq]
#align polynomial.monic.add_of_right Polynomial.Monic.add_of_right
-/

#print Polynomial.Monic.of_mul_monic_left /-
theorem Monic.of_mul_monic_left (hp : p.Monic) (hpq : (p * q).Monic) : q.Monic :=
  by
  contrapose! hpq
  rw [monic.def] at hpq⊢
  rwa [leading_coeff_monic_mul hp]
#align polynomial.monic.of_mul_monic_left Polynomial.Monic.of_mul_monic_left
-/

#print Polynomial.Monic.of_mul_monic_right /-
theorem Monic.of_mul_monic_right (hq : q.Monic) (hpq : (p * q).Monic) : p.Monic :=
  by
  contrapose! hpq
  rw [monic.def] at hpq⊢
  rwa [leading_coeff_mul_monic hq]
#align polynomial.monic.of_mul_monic_right Polynomial.Monic.of_mul_monic_right
-/

namespace Monic

#print Polynomial.Monic.natDegree_eq_zero_iff_eq_one /-
@[simp]
theorem natDegree_eq_zero_iff_eq_one (hp : p.Monic) : p.natDegree = 0 ↔ p = 1 :=
  by
  constructor <;> intro h
  swap
  · rw [h]
    exact nat_degree_one
  have : p = C (p.coeff 0) := by
    rw [← Polynomial.degree_le_zero_iff]
    rwa [Polynomial.natDegree_eq_zero_iff_degree_le_zero] at h
  rw [this]
  convert C_1
  rw [← h]
  apply hp
#align polynomial.monic.nat_degree_eq_zero_iff_eq_one Polynomial.Monic.natDegree_eq_zero_iff_eq_one
-/

#print Polynomial.Monic.degree_le_zero_iff_eq_one /-
@[simp]
theorem degree_le_zero_iff_eq_one (hp : p.Monic) : p.degree ≤ 0 ↔ p = 1 := by
  rw [← hp.nat_degree_eq_zero_iff_eq_one, nat_degree_eq_zero_iff_degree_le_zero]
#align polynomial.monic.degree_le_zero_iff_eq_one Polynomial.Monic.degree_le_zero_iff_eq_one
-/

#print Polynomial.Monic.natDegree_mul /-
theorem natDegree_mul (hp : p.Monic) (hq : q.Monic) :
    (p * q).natDegree = p.natDegree + q.natDegree :=
  by
  nontriviality R
  apply nat_degree_mul'
  simp [hp.leading_coeff, hq.leading_coeff]
#align polynomial.monic.nat_degree_mul Polynomial.Monic.natDegree_mul
-/

#print Polynomial.Monic.degree_mul_comm /-
theorem degree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).degree = (q * p).degree :=
  by
  by_cases h : q = 0
  · simp [h]
  rw [degree_mul', hp.degree_mul]
  · exact add_comm _ _
  · rwa [hp.leading_coeff, one_mul, leading_coeff_ne_zero]
#align polynomial.monic.degree_mul_comm Polynomial.Monic.degree_mul_comm
-/

#print Polynomial.Monic.natDegree_mul' /-
theorem natDegree_mul' (hp : p.Monic) (hq : q ≠ 0) :
    (p * q).natDegree = p.natDegree + q.natDegree :=
  by
  rw [nat_degree_mul', add_comm]
  simpa [hp.leading_coeff, leading_coeff_ne_zero]
#align polynomial.monic.nat_degree_mul' Polynomial.Monic.natDegree_mul'
-/

#print Polynomial.Monic.natDegree_mul_comm /-
theorem natDegree_mul_comm (hp : p.Monic) (q : R[X]) : (p * q).natDegree = (q * p).natDegree :=
  by
  by_cases h : q = 0
  · simp [h]
  rw [hp.nat_degree_mul' h, Polynomial.natDegree_mul', add_comm]
  simpa [hp.leading_coeff, leading_coeff_ne_zero]
#align polynomial.monic.nat_degree_mul_comm Polynomial.Monic.natDegree_mul_comm
-/

#print Polynomial.Monic.not_dvd_of_natDegree_lt /-
theorem not_dvd_of_natDegree_lt (hp : Monic p) (h0 : q ≠ 0) (hl : natDegree q < natDegree p) :
    ¬p ∣ q := by
  rintro ⟨r, rfl⟩
  rw [hp.nat_degree_mul' <| right_ne_zero_of_mul h0] at hl
  exact hl.not_le (Nat.le_add_right _ _)
#align polynomial.monic.not_dvd_of_nat_degree_lt Polynomial.Monic.not_dvd_of_natDegree_lt
-/

#print Polynomial.Monic.not_dvd_of_degree_lt /-
theorem not_dvd_of_degree_lt (hp : Monic p) (h0 : q ≠ 0) (hl : degree q < degree p) : ¬p ∣ q :=
  Monic.not_dvd_of_natDegree_lt hp h0 <| natDegree_lt_natDegree h0 hl
#align polynomial.monic.not_dvd_of_degree_lt Polynomial.Monic.not_dvd_of_degree_lt
-/

/- warning: polynomial.monic.next_coeff_mul -> Polynomial.Monic.nextCoeff_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, (Polynomial.Monic.{u1} R _inst_1 p) -> (Polynomial.Monic.{u1} R _inst_1 q) -> (Eq.{succ u1} R (Polynomial.nextCoeff.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Polynomial.nextCoeff.{u1} R _inst_1 p) (Polynomial.nextCoeff.{u1} R _inst_1 q)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {q : Polynomial.{u1} R _inst_1}, (Polynomial.Monic.{u1} R _inst_1 p) -> (Polynomial.Monic.{u1} R _inst_1 q) -> (Eq.{succ u1} R (Polynomial.nextCoeff.{u1} R _inst_1 (HMul.hMul.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHMul.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.mul'.{u1} R _inst_1)) p q)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Polynomial.nextCoeff.{u1} R _inst_1 p) (Polynomial.nextCoeff.{u1} R _inst_1 q)))
Case conversion may be inaccurate. Consider using '#align polynomial.monic.next_coeff_mul Polynomial.Monic.nextCoeff_mulₓ'. -/
theorem nextCoeff_mul (hp : Monic p) (hq : Monic q) :
    nextCoeff (p * q) = nextCoeff p + nextCoeff q :=
  by
  nontriviality
  simp only [← coeff_one_reverse]
  rw [reverse_mul] <;>
    simp [coeff_mul, nat.antidiagonal, hp.leading_coeff, hq.leading_coeff, add_comm]
#align polynomial.monic.next_coeff_mul Polynomial.Monic.nextCoeff_mul

/- warning: polynomial.monic.eq_one_of_map_eq_one -> Polynomial.Monic.eq_one_of_map_eq_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {p : Polynomial.{u1} R _inst_1} {S : Type.{u2}} [_inst_2 : Semiring.{u2} S] [_inst_3 : Nontrivial.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)), (Polynomial.Monic.{u1} R _inst_1 p) -> (Eq.{succ u2} (Polynomial.{u2} S _inst_2) (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p) (OfNat.ofNat.{u2} (Polynomial.{u2} S _inst_2) 1 (OfNat.mk.{u2} (Polynomial.{u2} S _inst_2) 1 (One.one.{u2} (Polynomial.{u2} S _inst_2) (Polynomial.hasOne.{u2} S _inst_2))))) -> (Eq.{succ u1} (Polynomial.{u1} R _inst_1) p (OfNat.ofNat.{u1} (Polynomial.{u1} R _inst_1) 1 (OfNat.mk.{u1} (Polynomial.{u1} R _inst_1) 1 (One.one.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.hasOne.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] {p : Polynomial.{u2} R _inst_1} {S : Type.{u1}} [_inst_2 : Semiring.{u1} S] [_inst_3 : Nontrivial.{u1} S] (f : RingHom.{u2, u1} R S (Semiring.toNonAssocSemiring.{u2} R _inst_1) (Semiring.toNonAssocSemiring.{u1} S _inst_2)), (Polynomial.Monic.{u2} R _inst_1 p) -> (Eq.{succ u1} (Polynomial.{u1} S _inst_2) (Polynomial.map.{u2, u1} R S _inst_1 _inst_2 f p) (OfNat.ofNat.{u1} (Polynomial.{u1} S _inst_2) 1 (One.toOfNat1.{u1} (Polynomial.{u1} S _inst_2) (Polynomial.one.{u1} S _inst_2)))) -> (Eq.{succ u2} (Polynomial.{u2} R _inst_1) p (OfNat.ofNat.{u2} (Polynomial.{u2} R _inst_1) 1 (One.toOfNat1.{u2} (Polynomial.{u2} R _inst_1) (Polynomial.one.{u2} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align polynomial.monic.eq_one_of_map_eq_one Polynomial.Monic.eq_one_of_map_eq_oneₓ'. -/
theorem eq_one_of_map_eq_one {S : Type _} [Semiring S] [Nontrivial S] (f : R →+* S) (hp : p.Monic)
    (map_eq : p.map f = 1) : p = 1 := by
  nontriviality R
  have hdeg : p.degree = 0 :=
    by
    rw [← degree_map_eq_of_leading_coeff_ne_zero f _, map_eq, degree_one]
    · rw [hp.leading_coeff, f.map_one]
      exact one_ne_zero
  have hndeg : p.nat_degree = 0 :=
    with_bot.coe_eq_coe.mp ((degree_eq_nat_degree hp.ne_zero).symm.trans hdeg)
  convert eq_C_of_degree_eq_zero hdeg
  rw [← hndeg, ← Polynomial.leadingCoeff, hp.leading_coeff, C.map_one]
#align polynomial.monic.eq_one_of_map_eq_one Polynomial.Monic.eq_one_of_map_eq_one

#print Polynomial.Monic.natDegree_pow /-
theorem natDegree_pow (hp : p.Monic) (n : ℕ) : (p ^ n).natDegree = n * p.natDegree :=
  by
  induction' n with n hn
  · simp
  · rw [pow_succ, hp.nat_degree_mul (hp.pow n), hn]
    ring
#align polynomial.monic.nat_degree_pow Polynomial.Monic.natDegree_pow
-/

end Monic

/- warning: polynomial.nat_degree_pow_X_add_C -> Polynomial.natDegree_pow_X_add_c is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] (n : Nat) (r : R), Eq.{1} Nat (Polynomial.natDegree.{u1} R _inst_1 (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (Polynomial.{u1} R _inst_1) (instHAdd.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.add'.{u1} R _inst_1)) (Polynomial.X.{u1} R _inst_1) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) => R -> (Polynomial.{u1} R _inst_1)) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (Polynomial.C.{u1} R _inst_1) r)) n)) n
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] (n : Nat) (r : R), Eq.{1} Nat (Polynomial.natDegree.{u1} R _inst_1 (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R _inst_1) Nat (Polynomial.{u1} R _inst_1) (instHPow.{u1, 0} (Polynomial.{u1} R _inst_1) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R _inst_1) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} (Polynomial.{u1} R _inst_1) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) r) (Polynomial.{u1} R _inst_1) (instHAdd.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.add'.{u1} R _inst_1)) (Polynomial.X.{u1} R _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R _inst_1) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1))) R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R _inst_1) (Polynomial.semiring.{u1} R _inst_1)))))) (Polynomial.C.{u1} R _inst_1) r)) n)) n
Case conversion may be inaccurate. Consider using '#align polynomial.nat_degree_pow_X_add_C Polynomial.natDegree_pow_X_add_cₓ'. -/
@[simp]
theorem natDegree_pow_X_add_c [Nontrivial R] (n : ℕ) (r : R) : ((X + C r) ^ n).natDegree = n := by
  rw [(monic_X_add_C r).natDegree_pow, nat_degree_X_add_C, mul_one]
#align polynomial.nat_degree_pow_X_add_C Polynomial.natDegree_pow_X_add_c

#print Polynomial.Monic.eq_one_of_isUnit /-
theorem Monic.eq_one_of_isUnit (hm : Monic p) (hpu : IsUnit p) : p = 1 :=
  by
  nontriviality R
  obtain ⟨q, h⟩ := hpu.exists_right_inv
  have := hm.nat_degree_mul' (right_ne_zero_of_mul_eq_one h)
  rw [h, nat_degree_one, eq_comm, add_eq_zero_iff] at this
  exact hm.nat_degree_eq_zero_iff_eq_one.mp this.1
#align polynomial.monic.eq_one_of_is_unit Polynomial.Monic.eq_one_of_isUnit
-/

#print Polynomial.Monic.isUnit_iff /-
theorem Monic.isUnit_iff (hm : p.Monic) : IsUnit p ↔ p = 1 :=
  ⟨hm.eq_one_of_isUnit, fun h => h.symm ▸ isUnit_one⟩
#align polynomial.monic.is_unit_iff Polynomial.Monic.isUnit_iff
-/

end Semiring

section CommSemiring

variable [CommSemiring R] {p : R[X]}

#print Polynomial.monic_multiset_prod_of_monic /-
theorem monic_multiset_prod_of_monic (t : Multiset ι) (f : ι → R[X]) (ht : ∀ i ∈ t, Monic (f i)) :
    Monic (t.map f).Prod := by
  revert ht
  refine' t.induction_on _ _; · simp
  intro a t ih ht
  rw [Multiset.map_cons, Multiset.prod_cons]
  exact (ht _ (Multiset.mem_cons_self _ _)).mul (ih fun _ hi => ht _ (Multiset.mem_cons_of_mem hi))
#align polynomial.monic_multiset_prod_of_monic Polynomial.monic_multiset_prod_of_monic
-/

#print Polynomial.monic_prod_of_monic /-
theorem monic_prod_of_monic (s : Finset ι) (f : ι → R[X]) (hs : ∀ i ∈ s, Monic (f i)) :
    Monic (∏ i in s, f i) :=
  monic_multiset_prod_of_monic s.1 f hs
#align polynomial.monic_prod_of_monic Polynomial.monic_prod_of_monic
-/

#print Polynomial.Monic.nextCoeff_multiset_prod /-
theorem Monic.nextCoeff_multiset_prod (t : Multiset ι) (f : ι → R[X]) (h : ∀ i ∈ t, Monic (f i)) :
    nextCoeff (t.map f).Prod = (t.map fun i => nextCoeff (f i)).Sum :=
  by
  revert h
  refine' Multiset.induction_on t _ fun a t ih ht => _
  · simp only [Multiset.not_mem_zero, forall_prop_of_true, forall_prop_of_false, Multiset.map_zero,
      Multiset.prod_zero, Multiset.sum_zero, not_false_iff, forall_true_iff]
    rw [← C_1]
    rw [next_coeff_C_eq_zero]
  · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      monic.next_coeff_mul, ih]
    exacts[fun i hi => ht i (Multiset.mem_cons_of_mem hi), ht a (Multiset.mem_cons_self _ _),
      monic_multiset_prod_of_monic _ _ fun b bs => ht _ (Multiset.mem_cons_of_mem bs)]
#align polynomial.monic.next_coeff_multiset_prod Polynomial.Monic.nextCoeff_multiset_prod
-/

#print Polynomial.Monic.nextCoeff_prod /-
theorem Monic.nextCoeff_prod (s : Finset ι) (f : ι → R[X]) (h : ∀ i ∈ s, Monic (f i)) :
    nextCoeff (∏ i in s, f i) = ∑ i in s, nextCoeff (f i) :=
  Monic.nextCoeff_multiset_prod s.1 f h
#align polynomial.monic.next_coeff_prod Polynomial.Monic.nextCoeff_prod
-/

end CommSemiring

section Semiring

variable [Semiring R]

#print Polynomial.Monic.natDegree_map /-
@[simp]
theorem Monic.natDegree_map [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R →+* S) :
    (P.map f).natDegree = P.natDegree :=
  by
  refine' le_antisymm (nat_degree_map_le _ _) (le_nat_degree_of_ne_zero _)
  rw [coeff_map, monic.coeff_nat_degree hmo, RingHom.map_one]
  exact one_ne_zero
#align polynomial.monic.nat_degree_map Polynomial.Monic.natDegree_map
-/

#print Polynomial.Monic.degree_map /-
@[simp]
theorem Monic.degree_map [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R →+* S) :
    (P.map f).degree = P.degree := by
  by_cases hP : P = 0
  · simp [hP]
  · refine' le_antisymm (degree_map_le _ _) _
    rw [degree_eq_nat_degree hP]
    refine' le_degree_of_ne_zero _
    rw [coeff_map, monic.coeff_nat_degree hmo, RingHom.map_one]
    exact one_ne_zero
#align polynomial.monic.degree_map Polynomial.Monic.degree_map
-/

section Injective

open Function

variable [Semiring S] {f : R →+* S} (hf : Injective f)

include hf

/- warning: polynomial.degree_map_eq_of_injective -> Polynomial.degree_map_eq_of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f)) -> (forall (p : Polynomial.{u1} R _inst_1), Eq.{1} (WithBot.{0} Nat) (Polynomial.degree.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) (Polynomial.degree.{u1} R _inst_1 p))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f)) -> (forall (p : Polynomial.{u1} R _inst_1), Eq.{1} (WithBot.{0} Nat) (Polynomial.degree.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) (Polynomial.degree.{u1} R _inst_1 p))
Case conversion may be inaccurate. Consider using '#align polynomial.degree_map_eq_of_injective Polynomial.degree_map_eq_of_injectiveₓ'. -/
theorem degree_map_eq_of_injective (p : R[X]) : degree (p.map f) = degree p :=
  if h : p = 0 then by simp [h]
  else
    degree_map_eq_of_leadingCoeff_ne_zero _
      (by rw [← f.map_zero] <;> exact mt hf.eq_iff.1 (mt leading_coeff_eq_zero.1 h))
#align polynomial.degree_map_eq_of_injective Polynomial.degree_map_eq_of_injective

/- warning: polynomial.nat_degree_map_eq_of_injective -> Polynomial.natDegree_map_eq_of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f)) -> (forall (p : Polynomial.{u1} R _inst_1), Eq.{1} Nat (Polynomial.natDegree.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) (Polynomial.natDegree.{u1} R _inst_1 p))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f)) -> (forall (p : Polynomial.{u1} R _inst_1), Eq.{1} Nat (Polynomial.natDegree.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) (Polynomial.natDegree.{u1} R _inst_1 p))
Case conversion may be inaccurate. Consider using '#align polynomial.nat_degree_map_eq_of_injective Polynomial.natDegree_map_eq_of_injectiveₓ'. -/
theorem natDegree_map_eq_of_injective (p : R[X]) : natDegree (p.map f) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_map_eq_of_injective hf p)
#align polynomial.nat_degree_map_eq_of_injective Polynomial.natDegree_map_eq_of_injective

/- warning: polynomial.leading_coeff_map' -> Polynomial.leadingCoeff_map' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f)) -> (forall (p : Polynomial.{u1} R _inst_1), Eq.{succ u2} S (Polynomial.leadingCoeff.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f (Polynomial.leadingCoeff.{u1} R _inst_1 p)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f)) -> (forall (p : Polynomial.{u1} R _inst_1), Eq.{succ u2} S (Polynomial.leadingCoeff.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f (Polynomial.leadingCoeff.{u1} R _inst_1 p)))
Case conversion may be inaccurate. Consider using '#align polynomial.leading_coeff_map' Polynomial.leadingCoeff_map'ₓ'. -/
theorem leadingCoeff_map' (p : R[X]) : leadingCoeff (p.map f) = f (leadingCoeff p) :=
  by
  unfold leading_coeff
  rw [coeff_map, nat_degree_map_eq_of_injective hf p]
#align polynomial.leading_coeff_map' Polynomial.leadingCoeff_map'

/- warning: polynomial.next_coeff_map -> Polynomial.nextCoeff_map is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f)) -> (forall (p : Polynomial.{u1} R _inst_1), Eq.{succ u2} S (Polynomial.nextCoeff.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f (Polynomial.nextCoeff.{u1} R _inst_1 p)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f)) -> (forall (p : Polynomial.{u1} R _inst_1), Eq.{succ u2} S (Polynomial.nextCoeff.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f (Polynomial.nextCoeff.{u1} R _inst_1 p)))
Case conversion may be inaccurate. Consider using '#align polynomial.next_coeff_map Polynomial.nextCoeff_mapₓ'. -/
theorem nextCoeff_map (p : R[X]) : (p.map f).nextCoeff = f p.nextCoeff :=
  by
  unfold next_coeff
  rw [nat_degree_map_eq_of_injective hf]
  split_ifs <;> simp
#align polynomial.next_coeff_map Polynomial.nextCoeff_map

/- warning: polynomial.leading_coeff_of_injective -> Polynomial.leadingCoeff_of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f)) -> (forall (p : Polynomial.{u1} R _inst_1), Eq.{succ u2} S (Polynomial.leadingCoeff.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f (Polynomial.leadingCoeff.{u1} R _inst_1 p)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f)) -> (forall (p : Polynomial.{u1} R _inst_1), Eq.{succ u2} S (Polynomial.leadingCoeff.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f (Polynomial.leadingCoeff.{u1} R _inst_1 p)))
Case conversion may be inaccurate. Consider using '#align polynomial.leading_coeff_of_injective Polynomial.leadingCoeff_of_injectiveₓ'. -/
theorem leadingCoeff_of_injective (p : R[X]) : leadingCoeff (p.map f) = f (leadingCoeff p) :=
  by
  delta leading_coeff
  rw [coeff_map f, nat_degree_map_eq_of_injective hf p]
#align polynomial.leading_coeff_of_injective Polynomial.leadingCoeff_of_injective

/- warning: polynomial.monic_of_injective -> Polynomial.monic_of_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f)) -> (forall {p : Polynomial.{u1} R _inst_1}, (Polynomial.Monic.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) -> (Polynomial.Monic.{u1} R _inst_1 p))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f)) -> (forall {p : Polynomial.{u1} R _inst_1}, (Polynomial.Monic.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)) -> (Polynomial.Monic.{u1} R _inst_1 p))
Case conversion may be inaccurate. Consider using '#align polynomial.monic_of_injective Polynomial.monic_of_injectiveₓ'. -/
theorem monic_of_injective {p : R[X]} (hp : (p.map f).Monic) : p.Monic :=
  by
  apply hf
  rw [← leading_coeff_of_injective hf, hp.leading_coeff, f.map_one]
#align polynomial.monic_of_injective Polynomial.monic_of_injective

/- warning: function.injective.monic_map_iff -> Function.Injective.monic_map_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f)) -> (forall {p : Polynomial.{u1} R _inst_1}, Iff (Polynomial.Monic.{u1} R _inst_1 p) (Polynomial.Monic.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] {f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)}, (Function.Injective.{succ u1, succ u2} R S (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f)) -> (forall {p : Polynomial.{u1} R _inst_1}, Iff (Polynomial.Monic.{u1} R _inst_1 p) (Polynomial.Monic.{u2} S _inst_2 (Polynomial.map.{u1, u2} R S _inst_1 _inst_2 f p)))
Case conversion may be inaccurate. Consider using '#align function.injective.monic_map_iff Function.Injective.monic_map_iffₓ'. -/
theorem Function.Injective.monic_map_iff {p : R[X]} : p.Monic ↔ (p.map f).Monic :=
  ⟨Monic.map _, Polynomial.monic_of_injective hf⟩
#align function.injective.monic_map_iff Function.Injective.monic_map_iff

end Injective

end Semiring

section Ring

variable [Ring R] {p : R[X]}

/- warning: polynomial.monic_X_sub_C -> Polynomial.monic_X_sub_C is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (x : R), Polynomial.Monic.{u1} R (Ring.toSemiring.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.sub.{u1} R _inst_1)) (Polynomial.X.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) => R -> (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Polynomial.C.{u1} R (Ring.toSemiring.{u1} R _inst_1)) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (x : R), Polynomial.Monic.{u1} R (Ring.toSemiring.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) x) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.sub.{u1} R _inst_1)) (Polynomial.X.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1))))))) (Polynomial.C.{u1} R (Ring.toSemiring.{u1} R _inst_1)) x))
Case conversion may be inaccurate. Consider using '#align polynomial.monic_X_sub_C Polynomial.monic_X_sub_Cₓ'. -/
theorem monic_X_sub_C (x : R) : Monic (X - C x) := by
  simpa only [sub_eq_add_neg, C_neg] using monic_X_add_C (-x)
#align polynomial.monic_X_sub_C Polynomial.monic_X_sub_C

/- warning: polynomial.monic_X_pow_sub -> Polynomial.monic_X_pow_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {p : Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)} {n : Nat}, (LE.le.{0} (WithBot.{0} Nat) (Preorder.toLE.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R _inst_1) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) n)) -> (Polynomial.Monic.{u1} R (Ring.toSemiring.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.sub.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (instHPow.{u1, 0} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Ring.toMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.ring.{u1} R _inst_1)))) (Polynomial.X.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) p))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {p : Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)} {n : Nat}, (LE.le.{0} (WithBot.{0} Nat) (Preorder.toLE.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R _inst_1) p) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) n)) -> (Polynomial.Monic.{u1} R (Ring.toSemiring.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.sub.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (instHPow.{u1, 0} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))) (Polynomial.X.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) p))
Case conversion may be inaccurate. Consider using '#align polynomial.monic_X_pow_sub Polynomial.monic_X_pow_subₓ'. -/
theorem monic_X_pow_sub {n : ℕ} (H : degree p ≤ n) : Monic (X ^ (n + 1) - p) := by
  simpa [sub_eq_add_neg] using monic_X_pow_add (show degree (-p) ≤ n by rwa [← degree_neg p] at H)
#align polynomial.monic_X_pow_sub Polynomial.monic_X_pow_sub

/- warning: polynomial.monic_X_pow_sub_C -> Polynomial.monic_X_pow_sub_C is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Ring.{u1} R] (a : R) {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Polynomial.Monic.{u1} R (Ring.toSemiring.{u1} R _inst_2) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.sub.{u1} R _inst_2)) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (instHPow.{u1, 0} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Ring.toMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.ring.{u1} R _inst_2)))) (Polynomial.X.{u1} R (Ring.toSemiring.{u1} R _inst_2)) n) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) (fun (_x : RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) => R -> (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2))) (RingHom.hasCoeToFun.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) (Polynomial.C.{u1} R (Ring.toSemiring.{u1} R _inst_2)) a)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : Ring.{u1} R] (a : R) {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Polynomial.Monic.{u1} R (Ring.toSemiring.{u1} R _inst_2) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) a) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.sub.{u1} R _inst_2)) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (instHPow.{u1, 0} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))))) (Polynomial.X.{u1} R (Ring.toSemiring.{u1} R _inst_2)) n) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) (NonUnitalNonAssocSemiring.toMul.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2))))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2))) (RingHom.instRingHomClassRingHom.{u1, u1} R (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R _inst_2))))))) (Polynomial.C.{u1} R (Ring.toSemiring.{u1} R _inst_2)) a)))
Case conversion may be inaccurate. Consider using '#align polynomial.monic_X_pow_sub_C Polynomial.monic_X_pow_sub_Cₓ'. -/
/-- `X ^ n - a` is monic. -/
theorem monic_X_pow_sub_C {R : Type u} [Ring R] (a : R) {n : ℕ} (h : n ≠ 0) : (X ^ n - C a).Monic :=
  by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h
  convert monic_X_pow_sub _
  exact le_trans degree_C_le Nat.WithBot.coe_nonneg
#align polynomial.monic_X_pow_sub_C Polynomial.monic_X_pow_sub_C

/- warning: polynomial.not_is_unit_X_pow_sub_one -> Polynomial.not_isUnit_X_pow_sub_one is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_2 : CommRing.{u1} R] [_inst_3 : Nontrivial.{u1} R] (n : Nat), Not (IsUnit.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Ring.toMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.ring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.sub.{u1} R (CommRing.toRing.{u1} R _inst_2))) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (instHPow.{u1, 0} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Ring.toMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.ring.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (Polynomial.X.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) n) (OfNat.ofNat.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) 1 (OfNat.mk.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) 1 (One.one.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.hasOne.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))))))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_2 : CommRing.{u1} R] [_inst_3 : Nontrivial.{u1} R] (n : Nat), Not (IsUnit.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))))) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.sub.{u1} R (CommRing.toRing.{u1} R _inst_2))) (HPow.hPow.{u1, 0, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) Nat (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (instHPow.{u1, 0} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) Nat (Monoid.Pow.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (MonoidWithZero.toMonoid.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Semiring.toMonoidWithZero.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.semiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))))))) (Polynomial.X.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) n) (OfNat.ofNat.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) 1 (One.toOfNat1.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Polynomial.one.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align polynomial.not_is_unit_X_pow_sub_one Polynomial.not_isUnit_X_pow_sub_oneₓ'. -/
theorem not_isUnit_X_pow_sub_one (R : Type _) [CommRing R] [Nontrivial R] (n : ℕ) :
    ¬IsUnit (X ^ n - 1 : R[X]) := by
  intro h
  rcases eq_or_ne n 0 with (rfl | hn)
  · simpa using h
  apply hn
  rw [← @nat_degree_one R, ← (monic_X_pow_sub_C _ hn).eq_one_of_isUnit h, nat_degree_X_pow_sub_C]
#align polynomial.not_is_unit_X_pow_sub_one Polynomial.not_isUnit_X_pow_sub_one

#print Polynomial.Monic.sub_of_left /-
theorem Monic.sub_of_left {p q : R[X]} (hp : Monic p) (hpq : degree q < degree p) : Monic (p - q) :=
  by
  rw [sub_eq_add_neg]
  apply hp.add_of_left
  rwa [degree_neg]
#align polynomial.monic.sub_of_left Polynomial.Monic.sub_of_left
-/

/- warning: polynomial.monic.sub_of_right -> Polynomial.Monic.sub_of_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {p : Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)} {q : Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)}, (Eq.{succ u1} R (Polynomial.leadingCoeff.{u1} R (Ring.toSemiring.{u1} R _inst_1) q) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))))) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R _inst_1) p) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R _inst_1) q)) -> (Polynomial.Monic.{u1} R (Ring.toSemiring.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.sub.{u1} R _inst_1)) p q))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] {p : Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)} {q : Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)}, (Eq.{succ u1} R (Polynomial.leadingCoeff.{u1} R (Ring.toSemiring.{u1} R _inst_1) q) (Neg.neg.{u1} R (Ring.toNeg.{u1} R _inst_1) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R _inst_1) p) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R _inst_1) q)) -> (Polynomial.Monic.{u1} R (Ring.toSemiring.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R _inst_1)) (Polynomial.sub.{u1} R _inst_1)) p q))
Case conversion may be inaccurate. Consider using '#align polynomial.monic.sub_of_right Polynomial.Monic.sub_of_rightₓ'. -/
theorem Monic.sub_of_right {p q : R[X]} (hq : q.leadingCoeff = -1) (hpq : degree p < degree q) :
    Monic (p - q) :=
  by
  have : (-q).coeff (-q).natDegree = 1 := by
    rw [nat_degree_neg, coeff_neg, show q.coeff q.nat_degree = -1 from hq, neg_neg]
  rw [sub_eq_add_neg]
  apply monic.add_of_right this
  rwa [degree_neg]
#align polynomial.monic.sub_of_right Polynomial.Monic.sub_of_right

end Ring

section NonzeroSemiring

variable [Semiring R] [Nontrivial R] {p q : R[X]}

#print Polynomial.not_monic_zero /-
@[simp]
theorem not_monic_zero : ¬Monic (0 : R[X]) :=
  not_monic_zero_iff.mp zero_ne_one
#align polynomial.not_monic_zero Polynomial.not_monic_zero
-/

end NonzeroSemiring

section NotZeroDivisor

-- TODO: using gh-8537, rephrase lemmas that involve commutation around `*` using the op-ring
variable [Semiring R] {p : R[X]}

#print Polynomial.Monic.mul_left_ne_zero /-
theorem Monic.mul_left_ne_zero (hp : Monic p) {q : R[X]} (hq : q ≠ 0) : q * p ≠ 0 :=
  by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne.def, ← degree_eq_bot, hp.degree_mul, WithBot.add_eq_bot, not_or, degree_eq_bot]
  refine' ⟨hq, _⟩
  rw [← hp.degree_le_zero_iff_eq_one, not_le] at h
  refine' (lt_trans _ h).ne'
  simp
#align polynomial.monic.mul_left_ne_zero Polynomial.Monic.mul_left_ne_zero
-/

#print Polynomial.Monic.mul_right_ne_zero /-
theorem Monic.mul_right_ne_zero (hp : Monic p) {q : R[X]} (hq : q ≠ 0) : p * q ≠ 0 :=
  by
  by_cases h : p = 1
  · simpa [h]
  rw [Ne.def, ← degree_eq_bot, hp.degree_mul_comm, hp.degree_mul, WithBot.add_eq_bot, not_or,
    degree_eq_bot]
  refine' ⟨hq, _⟩
  rw [← hp.degree_le_zero_iff_eq_one, not_le] at h
  refine' (lt_trans _ h).ne'
  simp
#align polynomial.monic.mul_right_ne_zero Polynomial.Monic.mul_right_ne_zero
-/

#print Polynomial.Monic.mul_natDegree_lt_iff /-
theorem Monic.mul_natDegree_lt_iff (h : Monic p) {q : R[X]} :
    (p * q).natDegree < p.natDegree ↔ p ≠ 1 ∧ q = 0 :=
  by
  by_cases hq : q = 0
  · suffices 0 < p.nat_degree ↔ p.nat_degree ≠ 0 by simpa [hq, ← h.nat_degree_eq_zero_iff_eq_one]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (Nat.zero_le _) h.symm⟩
  · simp [h.nat_degree_mul', hq]
#align polynomial.monic.mul_nat_degree_lt_iff Polynomial.Monic.mul_natDegree_lt_iff
-/

#print Polynomial.Monic.mul_right_eq_zero_iff /-
theorem Monic.mul_right_eq_zero_iff (h : Monic p) {q : R[X]} : p * q = 0 ↔ q = 0 := by
  by_cases hq : q = 0 <;> simp [h.mul_right_ne_zero, hq]
#align polynomial.monic.mul_right_eq_zero_iff Polynomial.Monic.mul_right_eq_zero_iff
-/

#print Polynomial.Monic.mul_left_eq_zero_iff /-
theorem Monic.mul_left_eq_zero_iff (h : Monic p) {q : R[X]} : q * p = 0 ↔ q = 0 := by
  by_cases hq : q = 0 <;> simp [h.mul_left_ne_zero, hq]
#align polynomial.monic.mul_left_eq_zero_iff Polynomial.Monic.mul_left_eq_zero_iff
-/

#print Polynomial.Monic.isRegular /-
theorem Monic.isRegular {R : Type _} [Ring R] {p : R[X]} (hp : Monic p) : IsRegular p :=
  by
  constructor
  · intro q r h
    rw [← sub_eq_zero, ← hp.mul_right_eq_zero_iff, mul_sub, h, sub_self]
  · intro q r h
    simp only at h
    rw [← sub_eq_zero, ← hp.mul_left_eq_zero_iff, sub_mul, h, sub_self]
#align polynomial.monic.is_regular Polynomial.Monic.isRegular
-/

/- warning: polynomial.degree_smul_of_smul_regular -> Polynomial.degree_smul_of_smul_regular is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {S : Type.{u2}} [_inst_2 : Monoid.{u2} S] [_inst_3 : DistribMulAction.{u2, u1} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))] {k : S} (p : Polynomial.{u1} R _inst_1), (IsSMulRegular.{u2, u1} S R (SMulZeroClass.toHasSmul.{u2, u1} S R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) (DistribSMul.toSmulZeroClass.{u2, u1} S R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (DistribMulAction.toDistribSMul.{u2, u1} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) _inst_3))) k) -> (Eq.{1} (WithBot.{0} Nat) (Polynomial.degree.{u1} R _inst_1 (SMul.smul.{u2, u1} S (Polynomial.{u1} R _inst_1) (SMulZeroClass.toHasSmul.{u2, u1} S (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1) (Polynomial.smulZeroClass.{u1, u2} R _inst_1 S (DistribSMul.toSmulZeroClass.{u2, u1} S R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (DistribMulAction.toDistribSMul.{u2, u1} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) _inst_3)))) k p)) (Polynomial.degree.{u1} R _inst_1 p))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] {S : Type.{u1}} [_inst_2 : Monoid.{u1} S] [_inst_3 : DistribMulAction.{u1, u2} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))] {k : S} (p : Polynomial.{u2} R _inst_1), (IsSMulRegular.{u1, u2} S R (SMulZeroClass.toSMul.{u1, u2} S R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (DistribSMul.toSMulZeroClass.{u1, u2} S R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))) (DistribMulAction.toDistribSMul.{u1, u2} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3))) k) -> (Eq.{1} (WithBot.{0} Nat) (Polynomial.degree.{u2} R _inst_1 (HSMul.hSMul.{u1, u2, u2} S (Polynomial.{u2} R _inst_1) (Polynomial.{u2} R _inst_1) (instHSMul.{u1, u2} S (Polynomial.{u2} R _inst_1) (SMulZeroClass.toSMul.{u1, u2} S (Polynomial.{u2} R _inst_1) (Polynomial.zero.{u2} R _inst_1) (Polynomial.smulZeroClass.{u2, u1} R _inst_1 S (DistribSMul.toSMulZeroClass.{u1, u2} S R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))) (DistribMulAction.toDistribSMul.{u1, u2} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3))))) k p)) (Polynomial.degree.{u2} R _inst_1 p))
Case conversion may be inaccurate. Consider using '#align polynomial.degree_smul_of_smul_regular Polynomial.degree_smul_of_smul_regularₓ'. -/
theorem degree_smul_of_smul_regular {S : Type _} [Monoid S] [DistribMulAction S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).degree = p.degree :=
  by
  refine' le_antisymm _ _
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    simp [hm m le_rfl]
  · rw [degree_le_iff_coeff_zero]
    intro m hm
    rw [degree_lt_iff_coeff_zero] at hm
    refine' h _
    simpa using hm m le_rfl
#align polynomial.degree_smul_of_smul_regular Polynomial.degree_smul_of_smul_regular

/- warning: polynomial.nat_degree_smul_of_smul_regular -> Polynomial.natDegree_smul_of_smul_regular is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {S : Type.{u2}} [_inst_2 : Monoid.{u2} S] [_inst_3 : DistribMulAction.{u2, u1} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))] {k : S} (p : Polynomial.{u1} R _inst_1), (IsSMulRegular.{u2, u1} S R (SMulZeroClass.toHasSmul.{u2, u1} S R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) (DistribSMul.toSmulZeroClass.{u2, u1} S R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (DistribMulAction.toDistribSMul.{u2, u1} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) _inst_3))) k) -> (Eq.{1} Nat (Polynomial.natDegree.{u1} R _inst_1 (SMul.smul.{u2, u1} S (Polynomial.{u1} R _inst_1) (SMulZeroClass.toHasSmul.{u2, u1} S (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1) (Polynomial.smulZeroClass.{u1, u2} R _inst_1 S (DistribSMul.toSmulZeroClass.{u2, u1} S R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (DistribMulAction.toDistribSMul.{u2, u1} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) _inst_3)))) k p)) (Polynomial.natDegree.{u1} R _inst_1 p))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] {S : Type.{u1}} [_inst_2 : Monoid.{u1} S] [_inst_3 : DistribMulAction.{u1, u2} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))] {k : S} (p : Polynomial.{u2} R _inst_1), (IsSMulRegular.{u1, u2} S R (SMulZeroClass.toSMul.{u1, u2} S R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (DistribSMul.toSMulZeroClass.{u1, u2} S R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))) (DistribMulAction.toDistribSMul.{u1, u2} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3))) k) -> (Eq.{1} Nat (Polynomial.natDegree.{u2} R _inst_1 (HSMul.hSMul.{u1, u2, u2} S (Polynomial.{u2} R _inst_1) (Polynomial.{u2} R _inst_1) (instHSMul.{u1, u2} S (Polynomial.{u2} R _inst_1) (SMulZeroClass.toSMul.{u1, u2} S (Polynomial.{u2} R _inst_1) (Polynomial.zero.{u2} R _inst_1) (Polynomial.smulZeroClass.{u2, u1} R _inst_1 S (DistribSMul.toSMulZeroClass.{u1, u2} S R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))) (DistribMulAction.toDistribSMul.{u1, u2} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3))))) k p)) (Polynomial.natDegree.{u2} R _inst_1 p))
Case conversion may be inaccurate. Consider using '#align polynomial.nat_degree_smul_of_smul_regular Polynomial.natDegree_smul_of_smul_regularₓ'. -/
theorem natDegree_smul_of_smul_regular {S : Type _} [Monoid S] [DistribMulAction S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).natDegree = p.natDegree :=
  by
  by_cases hp : p = 0
  · simp [hp]
  rw [← WithBot.coe_eq_coe, ← degree_eq_nat_degree hp, ← degree_eq_nat_degree,
    degree_smul_of_smul_regular p h]
  contrapose! hp
  rw [← smul_zero k] at hp
  exact h.polynomial hp
#align polynomial.nat_degree_smul_of_smul_regular Polynomial.natDegree_smul_of_smul_regular

/- warning: polynomial.leading_coeff_smul_of_smul_regular -> Polynomial.leadingCoeff_smul_of_smul_regular is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {S : Type.{u2}} [_inst_2 : Monoid.{u2} S] [_inst_3 : DistribMulAction.{u2, u1} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))] {k : S} (p : Polynomial.{u1} R _inst_1), (IsSMulRegular.{u2, u1} S R (SMulZeroClass.toHasSmul.{u2, u1} S R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) (DistribSMul.toSmulZeroClass.{u2, u1} S R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (DistribMulAction.toDistribSMul.{u2, u1} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) _inst_3))) k) -> (Eq.{succ u1} R (Polynomial.leadingCoeff.{u1} R _inst_1 (SMul.smul.{u2, u1} S (Polynomial.{u1} R _inst_1) (SMulZeroClass.toHasSmul.{u2, u1} S (Polynomial.{u1} R _inst_1) (Polynomial.zero.{u1} R _inst_1) (Polynomial.smulZeroClass.{u1, u2} R _inst_1 S (DistribSMul.toSmulZeroClass.{u2, u1} S R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (DistribMulAction.toDistribSMul.{u2, u1} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) _inst_3)))) k p)) (SMul.smul.{u2, u1} S R (SMulZeroClass.toHasSmul.{u2, u1} S R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) (DistribSMul.toSmulZeroClass.{u2, u1} S R (AddMonoid.toAddZeroClass.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (DistribMulAction.toDistribSMul.{u2, u1} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) _inst_3))) k (Polynomial.leadingCoeff.{u1} R _inst_1 p)))
but is expected to have type
  forall {R : Type.{u2}} [_inst_1 : Semiring.{u2} R] {S : Type.{u1}} [_inst_2 : Monoid.{u1} S] [_inst_3 : DistribMulAction.{u1, u2} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))] {k : S} (p : Polynomial.{u2} R _inst_1), (IsSMulRegular.{u1, u2} S R (SMulZeroClass.toSMul.{u1, u2} S R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (DistribSMul.toSMulZeroClass.{u1, u2} S R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))) (DistribMulAction.toDistribSMul.{u1, u2} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3))) k) -> (Eq.{succ u2} R (Polynomial.leadingCoeff.{u2} R _inst_1 (HSMul.hSMul.{u1, u2, u2} S (Polynomial.{u2} R _inst_1) (Polynomial.{u2} R _inst_1) (instHSMul.{u1, u2} S (Polynomial.{u2} R _inst_1) (SMulZeroClass.toSMul.{u1, u2} S (Polynomial.{u2} R _inst_1) (Polynomial.zero.{u2} R _inst_1) (Polynomial.smulZeroClass.{u2, u1} R _inst_1 S (DistribSMul.toSMulZeroClass.{u1, u2} S R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))) (DistribMulAction.toDistribSMul.{u1, u2} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3))))) k p)) (HSMul.hSMul.{u1, u2, u2} S R R (instHSMul.{u1, u2} S R (SMulZeroClass.toSMul.{u1, u2} S R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) (DistribSMul.toSMulZeroClass.{u1, u2} S R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))) (DistribMulAction.toDistribSMul.{u1, u2} S R _inst_2 (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3)))) k (Polynomial.leadingCoeff.{u2} R _inst_1 p)))
Case conversion may be inaccurate. Consider using '#align polynomial.leading_coeff_smul_of_smul_regular Polynomial.leadingCoeff_smul_of_smul_regularₓ'. -/
theorem leadingCoeff_smul_of_smul_regular {S : Type _} [Monoid S] [DistribMulAction S R] {k : S}
    (p : R[X]) (h : IsSMulRegular R k) : (k • p).leadingCoeff = k • p.leadingCoeff := by
  rw [leading_coeff, leading_coeff, coeff_smul, nat_degree_smul_of_smul_regular p h]
#align polynomial.leading_coeff_smul_of_smul_regular Polynomial.leadingCoeff_smul_of_smul_regular

#print Polynomial.monic_of_isUnit_leadingCoeff_inv_smul /-
theorem monic_of_isUnit_leadingCoeff_inv_smul (h : IsUnit p.leadingCoeff) : Monic (h.Unit⁻¹ • p) :=
  by
  rw [monic.def, leading_coeff_smul_of_smul_regular _ (isSMulRegular_of_group _), Units.smul_def]
  obtain ⟨k, hk⟩ := h
  simp only [← hk, smul_eq_mul, ← Units.val_mul, Units.val_eq_one, inv_mul_eq_iff_eq_mul]
  simp [Units.ext_iff, IsUnit.unit_spec]
#align polynomial.monic_of_is_unit_leading_coeff_inv_smul Polynomial.monic_of_isUnit_leadingCoeff_inv_smul
-/

#print Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff /-
theorem isUnit_leadingCoeff_mul_right_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} :
    p * q = 0 ↔ q = 0 := by
  constructor
  · intro hp
    rw [← smul_eq_zero_iff_eq h.unit⁻¹] at hp
    have : h.unit⁻¹ • (p * q) = h.unit⁻¹ • p * q :=
      by
      ext
      simp only [Units.smul_def, coeff_smul, coeff_mul, smul_eq_mul, mul_sum]
      refine' sum_congr rfl fun x hx => _
      rw [← mul_assoc]
    rwa [this, monic.mul_right_eq_zero_iff] at hp
    exact monic_of_is_unit_leading_coeff_inv_smul _
  · rintro rfl
    simp
#align polynomial.is_unit_leading_coeff_mul_right_eq_zero_iff Polynomial.isUnit_leadingCoeff_mul_right_eq_zero_iff
-/

#print Polynomial.isUnit_leadingCoeff_mul_left_eq_zero_iff /-
theorem isUnit_leadingCoeff_mul_left_eq_zero_iff (h : IsUnit p.leadingCoeff) {q : R[X]} :
    q * p = 0 ↔ q = 0 := by
  constructor
  · intro hp
    replace hp := congr_arg (· * C ↑h.unit⁻¹) hp
    simp only [MulZeroClass.zero_mul] at hp
    rwa [mul_assoc, monic.mul_left_eq_zero_iff] at hp
    refine' monic_mul_C_of_leading_coeff_mul_eq_one _
    simp [Units.mul_inv_eq_iff_eq_mul, IsUnit.unit_spec]
  · rintro rfl
    rw [MulZeroClass.zero_mul]
#align polynomial.is_unit_leading_coeff_mul_left_eq_zero_iff Polynomial.isUnit_leadingCoeff_mul_left_eq_zero_iff
-/

end NotZeroDivisor

end Polynomial

