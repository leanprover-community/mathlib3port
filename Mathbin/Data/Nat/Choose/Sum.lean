/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens

! This file was ported from Lean 3 source module data.nat.choose.sum
! leanprover-community/mathlib commit 3e32bc908f617039c74c06ea9a897e30c30803c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Choose.Basic
import Mathbin.Tactic.Linarith.Default
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Algebra.BigOperators.Intervals
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Algebra.BigOperators.NatAntidiagonal

/-!
# Sums of binomial coefficients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file includes variants of the binomial theorem and other results on sums of binomial
coefficients. Theorems whose proofs depend on such sums may also go in this file for import
reasons.

-/


open Nat

open Finset

open BigOperators

variable {R : Type _}

namespace Commute

variable [Semiring R] {x y : R} (h : Commute x y) (n : ℕ)

include h

/- warning: commute.add_pow -> Commute.add_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {x : R} {y : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x y) -> (forall (n : Nat), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x y) n) (Finset.sum.{u1, 0} R Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (m : Nat) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) x m) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) y (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n m))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))) (Nat.choose n m)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {x : R} {y : R}, (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) x y) -> (forall (n : Nat), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x y) n) (Finset.sum.{u1, 0} R Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (m : Nat) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) x m) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) y (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n m))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R _inst_1) (Nat.choose n m)))))
Case conversion may be inaccurate. Consider using '#align commute.add_pow Commute.add_powₓ'. -/
/-- A version of the **binomial theorem** for commuting elements in noncommutative semirings. -/
theorem add_pow : (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
  by
  let t : ℕ → ℕ → R := fun n m => x ^ m * y ^ (n - m) * choose n m
  change (x + y) ^ n = ∑ m in range (n + 1), t n m
  have h_first : ∀ n, t n 0 = y ^ n := fun n =>
    by
    dsimp [t]
    rw [choose_zero_right, pow_zero, Nat.cast_one, mul_one, one_mul]
  have h_last : ∀ n, t n n.succ = 0 := fun n =>
    by
    dsimp [t]
    rw [choose_succ_self, Nat.cast_zero, MulZeroClass.mul_zero]
  have h_middle :
    ∀ n i : ℕ, i ∈ range n.succ → (t n.succ ∘ Nat.succ) i = x * t n i + y * t n i.succ :=
    by
    intro n i h_mem
    have h_le : i ≤ n := Nat.le_of_lt_succ (mem_range.mp h_mem)
    dsimp [t]
    rw [choose_succ_succ, Nat.cast_add, mul_add]
    congr 1
    · rw [pow_succ x, succ_sub_succ, mul_assoc, mul_assoc, mul_assoc]
    · rw [← mul_assoc y, ← mul_assoc y, (h.symm.pow_right i.succ).Eq]
      by_cases h_eq : i = n
      · rw [h_eq, choose_succ_self, Nat.cast_zero, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
      · rw [succ_sub (lt_of_le_of_ne h_le h_eq)]
        rw [pow_succ y, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  induction' n with n ih
  · rw [pow_zero, sum_range_succ, range_zero, sum_empty, zero_add]
    dsimp [t]
    rw [pow_zero, pow_zero, choose_self, Nat.cast_one, mul_one, mul_one]
  · rw [sum_range_succ', h_first]
    rw [sum_congr rfl (h_middle n), sum_add_distrib, add_assoc]
    rw [pow_succ (x + y), ih, add_mul, mul_sum, mul_sum]
    congr 1
    rw [sum_range_succ', sum_range_succ, h_first, h_last, MulZeroClass.mul_zero, add_zero, pow_succ]
#align commute.add_pow Commute.add_pow

/- warning: commute.add_pow' -> Commute.add_pow' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {x : R} {y : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) x y) -> (forall (n : Nat), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x y) n) (Finset.sum.{u1, 0} R (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Finset.Nat.antidiagonal n) (fun (m : Prod.{0, 0} Nat Nat) => SMul.smul.{0, u1} Nat R (AddMonoid.SMul.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Nat.choose n (Prod.fst.{0, 0} Nat Nat m)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) x (Prod.fst.{0, 0} Nat Nat m)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) y (Prod.snd.{0, 0} Nat Nat m))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {x : R} {y : R}, (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) x y) -> (forall (n : Nat), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) x y) n) (Finset.sum.{u1, 0} R (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Finset.Nat.antidiagonal n) (fun (m : Prod.{0, 0} Nat Nat) => HSMul.hSMul.{0, u1, u1} Nat R R (instHSMul.{0, u1} Nat R (AddMonoid.SMul.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) (Nat.choose n (Prod.fst.{0, 0} Nat Nat m)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) x (Prod.fst.{0, 0} Nat Nat m)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) y (Prod.snd.{0, 0} Nat Nat m))))))
Case conversion may be inaccurate. Consider using '#align commute.add_pow' Commute.add_pow'ₓ'. -/
/-- A version of `commute.add_pow` that avoids ℕ-subtraction by summing over the antidiagonal and
also with the binomial coefficient applied via scalar action of ℕ. -/
theorem add_pow' :
    (x + y) ^ n = ∑ m in Nat.antidiagonal n, choose n m.fst • (x ^ m.fst * y ^ m.snd) := by
  simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun m p => choose n m • (x ^ m * y ^ p),
    _root_.nsmul_eq_mul, cast_comm, h.add_pow]
#align commute.add_pow' Commute.add_pow'

end Commute

/- warning: add_pow -> add_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (x : R) (y : R) (n : Nat), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) n) (Finset.sum.{u1, 0} R Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (m : Nat) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x m) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n m))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))) (Nat.choose n m))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (x : R) (y : R) (n : Nat), Eq.{succ u1} R (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) x y) n) (Finset.sum.{u1, 0} R Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (m : Nat) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) x m) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) y (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n m))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Nat.choose n m))))
Case conversion may be inaccurate. Consider using '#align add_pow add_powₓ'. -/
/-- The **binomial theorem** -/
theorem add_pow [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ m in range (n + 1), x ^ m * y ^ (n - m) * choose n m :=
  (Commute.all x y).add_pow n
#align add_pow add_pow

namespace Nat

#print Nat.sum_range_choose /-
/-- The sum of entries in a row of Pascal's triangle -/
theorem sum_range_choose (n : ℕ) : (∑ m in range (n + 1), choose n m) = 2 ^ n := by
  simpa using (add_pow 1 1 n).symm
#align nat.sum_range_choose Nat.sum_range_choose
-/

#print Nat.sum_range_choose_halfway /-
theorem sum_range_choose_halfway (m : Nat) : (∑ i in range (m + 1), choose (2 * m + 1) i) = 4 ^ m :=
  have :
    (∑ i in range (m + 1), choose (2 * m + 1) (2 * m + 1 - i)) =
      ∑ i in range (m + 1), choose (2 * m + 1) i :=
    sum_congr rfl fun i hi => choose_symm <| by linarith [mem_range.1 hi]
  mul_right_injective₀ two_ne_zero <|
    calc
      (2 * ∑ i in range (m + 1), choose (2 * m + 1) i) =
          (∑ i in range (m + 1), choose (2 * m + 1) i) +
            ∑ i in range (m + 1), choose (2 * m + 1) (2 * m + 1 - i) :=
        by rw [two_mul, this]
      _ =
          (∑ i in range (m + 1), choose (2 * m + 1) i) +
            ∑ i in Ico (m + 1) (2 * m + 2), choose (2 * m + 1) i :=
        by
        rw [range_eq_Ico, sum_Ico_reflect]
        · congr
          have A : m + 1 ≤ 2 * m + 1 := by linarith
          rw [add_comm, add_tsub_assoc_of_le A, ← add_comm]
          congr
          rw [tsub_eq_iff_eq_add_of_le A]
          ring
        · linarith
      _ = ∑ i in range (2 * m + 2), choose (2 * m + 1) i := (sum_range_add_sum_Ico _ (by linarith))
      _ = 2 ^ (2 * m + 1) := (sum_range_choose (2 * m + 1))
      _ = 2 * 4 ^ m := by
        rw [pow_succ, pow_mul]
        rfl
      
#align nat.sum_range_choose_halfway Nat.sum_range_choose_halfway
-/

#print Nat.choose_middle_le_pow /-
theorem choose_middle_le_pow (n : ℕ) : choose (2 * n + 1) n ≤ 4 ^ n :=
  by
  have t : choose (2 * n + 1) n ≤ ∑ i in range (n + 1), choose (2 * n + 1) i :=
    single_le_sum (fun x _ => by linarith) (self_mem_range_succ n)
  simpa [sum_range_choose_halfway n] using t
#align nat.choose_middle_le_pow Nat.choose_middle_le_pow
-/

#print Nat.four_pow_le_two_mul_add_one_mul_central_binom /-
theorem four_pow_le_two_mul_add_one_mul_central_binom (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * choose (2 * n) n :=
  calc
    4 ^ n = (1 + 1) ^ (2 * n) := by norm_num [pow_mul]
    _ = ∑ m in range (2 * n + 1), choose (2 * n) m := by simp [add_pow]
    _ ≤ ∑ m in range (2 * n + 1), choose (2 * n) (2 * n / 2) :=
      (sum_le_sum fun i hi => choose_le_middle i (2 * n))
    _ = (2 * n + 1) * choose (2 * n) n := by simp
    
#align nat.four_pow_le_two_mul_add_one_mul_central_binom Nat.four_pow_le_two_mul_add_one_mul_central_binom
-/

end Nat

/- warning: int.alternating_sum_range_choose -> Int.alternating_sum_range_choose is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} Int (Finset.sum.{0, 0} Int Nat Int.addCommMonoid (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (m : Nat) => HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Nat.choose n m)))) (ite.{1} Int (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Nat.decidableEq n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {n : Nat}, Eq.{1} Int (Finset.sum.{0, 0} Int Nat Int.instAddCommMonoidInt (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (m : Nat) => HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) m) (Nat.cast.{0} Int instNatCastInt (Nat.choose n m)))) (ite.{1} Int (Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (instDecidableEqNat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.alternating_sum_range_choose Int.alternating_sum_range_chooseₓ'. -/
theorem Int.alternating_sum_range_choose {n : ℕ} :
    (∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℤ)) = if n = 0 then 1 else 0 :=
  by
  cases n; · simp
  have h := add_pow (-1 : ℤ) 1 n.succ
  simp only [one_pow, mul_one, add_left_neg] at h
  rw [← h, zero_pow (Nat.succ_pos n), if_neg (Nat.succ_ne_zero n)]
#align int.alternating_sum_range_choose Int.alternating_sum_range_choose

/- warning: int.alternating_sum_range_choose_of_ne -> Int.alternating_sum_range_choose_of_ne is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} Int (Finset.sum.{0, 0} Int Nat Int.addCommMonoid (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (m : Nat) => HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Nat.choose n m)))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} Int (Finset.sum.{0, 0} Int Nat Int.instAddCommMonoidInt (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (m : Nat) => HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) m) (Nat.cast.{0} Int instNatCastInt (Nat.choose n m)))) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align int.alternating_sum_range_choose_of_ne Int.alternating_sum_range_choose_of_neₓ'. -/
theorem Int.alternating_sum_range_choose_of_ne {n : ℕ} (h0 : n ≠ 0) :
    (∑ m in range (n + 1), ((-1) ^ m * ↑(choose n m) : ℤ)) = 0 := by
  rw [Int.alternating_sum_range_choose, if_neg h0]
#align int.alternating_sum_range_choose_of_ne Int.alternating_sum_range_choose_of_ne

namespace Finset

/- warning: finset.sum_powerset_apply_card -> Finset.sum_powerset_apply_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} α] (f : Nat -> α) {x : Finset.{u2} β}, Eq.{succ u1} α (Finset.sum.{u1, u2} α (Finset.{u2} β) _inst_1 (Finset.powerset.{u2} β x) (fun (m : Finset.{u2} β) => f (Finset.card.{u2} β m))) (Finset.sum.{u1, 0} α Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u2} β x) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (m : Nat) => SMul.smul.{0, u1} Nat α (AddMonoid.SMul.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (Nat.choose (Finset.card.{u2} β x) m) (f m)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} α] (f : Nat -> α) {x : Finset.{u1} β}, Eq.{succ u2} α (Finset.sum.{u2, u1} α (Finset.{u1} β) _inst_1 (Finset.powerset.{u1} β x) (fun (m : Finset.{u1} β) => f (Finset.card.{u1} β m))) (Finset.sum.{u2, 0} α Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} β x) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (m : Nat) => HSMul.hSMul.{0, u2, u2} Nat α α (instHSMul.{0, u2} Nat α (AddMonoid.SMul.{u2} α (AddCommMonoid.toAddMonoid.{u2} α _inst_1))) (Nat.choose (Finset.card.{u1} β x) m) (f m)))
Case conversion may be inaccurate. Consider using '#align finset.sum_powerset_apply_card Finset.sum_powerset_apply_cardₓ'. -/
theorem sum_powerset_apply_card {α β : Type _} [AddCommMonoid α] (f : ℕ → α) {x : Finset β} :
    (∑ m in x.powerset, f m.card) = ∑ m in range (x.card + 1), x.card.choose m • f m :=
  by
  trans ∑ m in range (x.card + 1), ∑ j in x.powerset.filter fun z => z.card = m, f j.card
  · refine' (sum_fiberwise_of_maps_to _ _).symm
    intro y hy
    rw [mem_range, Nat.lt_succ_iff]
    rw [mem_powerset] at hy
    exact card_le_of_subset hy
  · refine' sum_congr rfl fun y hy => _
    rw [← card_powerset_len, ← sum_const]
    refine' sum_congr powerset_len_eq_filter.symm fun z hz => _
    rw [(mem_powerset_len.1 hz).2]
#align finset.sum_powerset_apply_card Finset.sum_powerset_apply_card

/- warning: finset.sum_powerset_neg_one_pow_card -> Finset.sum_powerset_neg_one_pow_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {x : Finset.{u1} α}, Eq.{1} Int (Finset.sum.{0, u1} Int (Finset.{u1} α) Int.addCommMonoid (Finset.powerset.{u1} α x) (fun (m : Finset.{u1} α) => HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (Finset.card.{u1} α m))) (ite.{1} Int (Eq.{succ u1} (Finset.{u1} α) x (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) x (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {x : Finset.{u1} α}, Eq.{1} Int (Finset.sum.{0, u1} Int (Finset.{u1} α) Int.instAddCommMonoidInt (Finset.powerset.{u1} α x) (fun (m : Finset.{u1} α) => HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (Finset.card.{u1} α m))) (ite.{1} Int (Eq.{succ u1} (Finset.{u1} α) x (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) (Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) x (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align finset.sum_powerset_neg_one_pow_card Finset.sum_powerset_neg_one_pow_cardₓ'. -/
theorem sum_powerset_neg_one_pow_card {α : Type _} [DecidableEq α] {x : Finset α} :
    (∑ m in x.powerset, (-1 : ℤ) ^ m.card) = if x = ∅ then 1 else 0 :=
  by
  rw [sum_powerset_apply_card]
  simp only [nsmul_eq_mul', ← card_eq_zero, Int.alternating_sum_range_choose]
#align finset.sum_powerset_neg_one_pow_card Finset.sum_powerset_neg_one_pow_card

/- warning: finset.sum_powerset_neg_one_pow_card_of_nonempty -> Finset.sum_powerset_neg_one_pow_card_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : Finset.{u1} α}, (Finset.Nonempty.{u1} α x) -> (Eq.{1} Int (Finset.sum.{0, u1} Int (Finset.{u1} α) Int.addCommMonoid (Finset.powerset.{u1} α x) (fun (m : Finset.{u1} α) => HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (Finset.card.{u1} α m))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} {x : Finset.{u1} α}, (Finset.Nonempty.{u1} α x) -> (Eq.{1} Int (Finset.sum.{0, u1} Int (Finset.{u1} α) Int.instAddCommMonoidInt (Finset.powerset.{u1} α x) (fun (m : Finset.{u1} α) => HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (Finset.card.{u1} α m))) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align finset.sum_powerset_neg_one_pow_card_of_nonempty Finset.sum_powerset_neg_one_pow_card_of_nonemptyₓ'. -/
theorem sum_powerset_neg_one_pow_card_of_nonempty {α : Type _} {x : Finset α} (h0 : x.Nonempty) :
    (∑ m in x.powerset, (-1 : ℤ) ^ m.card) = 0 := by
  classical
    rw [sum_powerset_neg_one_pow_card, if_neg]
    rw [← Ne.def, ← nonempty_iff_ne_empty]
    apply h0
#align finset.sum_powerset_neg_one_pow_card_of_nonempty Finset.sum_powerset_neg_one_pow_card_of_nonempty

end Finset

