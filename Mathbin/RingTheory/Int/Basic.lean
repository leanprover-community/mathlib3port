/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson

! This file was ported from Lean 3 source module ring_theory.int.basic
! leanprover-community/mathlib commit c085f3044fe585c575e322bfab45b3633c48d820
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.EuclideanDomain.Basic
import Mathbin.Data.Nat.Factors
import Mathbin.RingTheory.Coprime.Basic
import Mathbin.RingTheory.PrincipalIdealDomain

/-!
# Divisibility over ℕ and ℤ

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file collects results for the integers and natural numbers that use abstract algebra in
their proofs or cases of ℕ and ℤ being examples of structures in abstract algebra.

## Main statements

* `nat.factors_eq`: the multiset of elements of `nat.factors` is equal to the factors
   given by the `unique_factorization_monoid` instance
* ℤ is a `normalization_monoid`
* ℤ is a `gcd_monoid`

## Tags

prime, irreducible, natural numbers, integers, normalization monoid, gcd monoid,
greatest common divisor, prime factorization, prime factors, unique factorization,
unique factors
-/


namespace Nat

instance : WfDvdMonoid ℕ :=
  ⟨by
    refine'
      RelHomClass.wellFounded
        (⟨fun x : ℕ => if x = 0 then (⊤ : ℕ∞) else x, _⟩ : DvdNotUnit →r (· < ·))
        (WithTop.wellFounded_lt Nat.lt_wfRel)
    intro a b h
    cases a
    · exfalso
      revert h
      simp [DvdNotUnit]
    cases b
    · simpa [succ_ne_zero] using WithTop.coe_lt_top (a + 1)
    cases' dvd_and_not_dvd_iff.2 h with h1 h2
    simp only [succ_ne_zero, WithTop.coe_lt_coe, if_false]
    apply lt_of_le_of_ne (Nat.le_of_dvd (Nat.succ_pos _) h1) fun con => h2 _
    rw [Con]⟩

instance : UniqueFactorizationMonoid ℕ :=
  ⟨fun _ => Nat.irreducible_iff_prime⟩

end Nat

/-- `ℕ` is a gcd_monoid. -/
instance : GCDMonoid ℕ where
  gcd := Nat.gcd
  lcm := Nat.lcm
  gcd_dvd_left := Nat.gcd_dvd_left
  gcd_dvd_right := Nat.gcd_dvd_right
  dvd_gcd a b c := Nat.dvd_gcd
  gcd_mul_lcm a b := by rw [Nat.gcd_mul_lcm]
  lcm_zero_left := Nat.lcm_zero_left
  lcm_zero_right := Nat.lcm_zero_right

instance : NormalizedGCDMonoid ℕ :=
  { (inferInstance : GCDMonoid ℕ),
    (inferInstance :
      NormalizationMonoid
        ℕ) with
    normalize_gcd := fun a b => normalize_eq _
    normalize_lcm := fun a b => normalize_eq _ }

/- warning: gcd_eq_nat_gcd -> gcd_eq_nat_gcd is a dubious translation:
lean 3 declaration is
  forall (m : Nat) (n : Nat), Eq.{1} Nat (GCDMonoid.gcd.{0} Nat Nat.cancelCommMonoidWithZero Nat.gcdMonoid m n) (Nat.gcd m n)
but is expected to have type
  forall (m : Nat) (n : Nat), Eq.{1} Nat (GCDMonoid.gcd.{0} Nat Nat.cancelCommMonoidWithZero instGCDMonoidNatCancelCommMonoidWithZero m n) (Nat.gcd m n)
Case conversion may be inaccurate. Consider using '#align gcd_eq_nat_gcd gcd_eq_nat_gcdₓ'. -/
theorem gcd_eq_nat_gcd (m n : ℕ) : gcd m n = Nat.gcd m n :=
  rfl
#align gcd_eq_nat_gcd gcd_eq_nat_gcd

/- warning: lcm_eq_nat_lcm -> lcm_eq_nat_lcm is a dubious translation:
lean 3 declaration is
  forall (m : Nat) (n : Nat), Eq.{1} Nat (GCDMonoid.lcm.{0} Nat Nat.cancelCommMonoidWithZero Nat.gcdMonoid m n) (Nat.lcm m n)
but is expected to have type
  forall (m : Nat) (n : Nat), Eq.{1} Nat (GCDMonoid.lcm.{0} Nat Nat.cancelCommMonoidWithZero instGCDMonoidNatCancelCommMonoidWithZero m n) (Nat.lcm m n)
Case conversion may be inaccurate. Consider using '#align lcm_eq_nat_lcm lcm_eq_nat_lcmₓ'. -/
theorem lcm_eq_nat_lcm (m n : ℕ) : lcm m n = Nat.lcm m n :=
  rfl
#align lcm_eq_nat_lcm lcm_eq_nat_lcm

namespace Int

section NormalizationMonoid

instance : NormalizationMonoid ℤ
    where
  normUnit := fun a : ℤ => if 0 ≤ a then 1 else -1
  normUnit_zero := if_pos le_rfl
  normUnit_mul a b hna hnb := by
    cases' hna.lt_or_lt with ha ha <;> cases' hnb.lt_or_lt with hb hb <;>
      simp [mul_nonneg_iff, ha.le, ha.not_le, hb.le, hb.not_le]
  normUnit_coe_units u :=
    (units_eq_one_or u).elim (fun eq => Eq.symm ▸ if_pos zero_le_one) fun eq =>
      Eq.symm ▸ if_neg (not_le_of_gt <| show (-1 : ℤ) < 0 by decide)

/- warning: int.normalize_of_nonneg -> Int.normalize_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {z : Int}, (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) z) -> (Eq.{1} Int (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (fun (_x : MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) => Int -> Int) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) z) z)
but is expected to have type
  forall {z : Int}, (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) z) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) z) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) z) z)
Case conversion may be inaccurate. Consider using '#align int.normalize_of_nonneg Int.normalize_of_nonnegₓ'. -/
theorem normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z :=
  show z * ↑(ite _ _ _) = z by rw [if_pos h, Units.val_one, mul_one]
#align int.normalize_of_nonneg Int.normalize_of_nonneg

/- warning: int.normalize_of_nonpos -> Int.normalize_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {z : Int}, (LE.le.{0} Int Int.hasLe z (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Eq.{1} Int (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (fun (_x : MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) => Int -> Int) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) z) (Neg.neg.{0} Int Int.hasNeg z))
but is expected to have type
  forall {z : Int}, (LE.le.{0} Int Int.instLEInt z (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) z) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) z) (Neg.neg.{0} Int Int.instNegInt z))
Case conversion may be inaccurate. Consider using '#align int.normalize_of_nonpos Int.normalize_of_nonposₓ'. -/
theorem normalize_of_nonpos {z : ℤ} (h : z ≤ 0) : normalize z = -z :=
  by
  obtain rfl | h := h.eq_or_lt
  · simp
  · change z * ↑(ite _ _ _) = -z
    rw [if_neg (not_le_of_gt h), Units.val_neg, Units.val_one, mul_neg_one]
#align int.normalize_of_nonpos Int.normalize_of_nonpos

/- warning: int.normalize_coe_nat -> Int.normalize_coe_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Int (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (fun (_x : MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) => Int -> Int) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)
but is expected to have type
  forall (n : Nat), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) (Nat.cast.{0} Int instNatCastInt n)) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) (Nat.cast.{0} Int instNatCastInt n)) (Nat.cast.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) (Nat.cast.{0} Int instNatCastInt n)) instNatCastInt n)
Case conversion may be inaccurate. Consider using '#align int.normalize_coe_nat Int.normalize_coe_natₓ'. -/
theorem normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n :=
  normalize_of_nonneg (ofNat_le_ofNat_of_le <| Nat.zero_le n)
#align int.normalize_coe_nat Int.normalize_coe_nat

/- warning: int.abs_eq_normalize -> Int.abs_eq_normalize is a dubious translation:
lean 3 declaration is
  forall (z : Int), Eq.{1} Int (Abs.abs.{0} Int (Neg.toHasAbs.{0} Int Int.hasNeg (SemilatticeSup.toHasSup.{0} Int (Lattice.toSemilatticeSup.{0} Int (LinearOrder.toLattice.{0} Int Int.linearOrder)))) z) (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (fun (_x : MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) => Int -> Int) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) z)
but is expected to have type
  forall (z : Int), Eq.{1} Int (Abs.abs.{0} Int (Neg.toHasAbs.{0} Int Int.instNegInt (SemilatticeSup.toSup.{0} Int (Lattice.toSemilatticeSup.{0} Int (DistribLattice.toLattice.{0} Int (instDistribLattice.{0} Int Int.instLinearOrderInt))))) z) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) z)
Case conversion may be inaccurate. Consider using '#align int.abs_eq_normalize Int.abs_eq_normalizeₓ'. -/
theorem abs_eq_normalize (z : ℤ) : |z| = normalize z := by
  cases le_total 0 z <;> simp [normalize_of_nonneg, normalize_of_nonpos, *]
#align int.abs_eq_normalize Int.abs_eq_normalize

/- warning: int.nonneg_of_normalize_eq_self -> Int.nonneg_of_normalize_eq_self is a dubious translation:
lean 3 declaration is
  forall {z : Int}, (Eq.{1} Int (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (fun (_x : MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) => Int -> Int) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) z) z) -> (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) z)
but is expected to have type
  forall {z : Int}, (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) z) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) z) z) -> (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) z)
Case conversion may be inaccurate. Consider using '#align int.nonneg_of_normalize_eq_self Int.nonneg_of_normalize_eq_selfₓ'. -/
theorem nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z :=
  abs_eq_self.1 <| by rw [abs_eq_normalize, hz]
#align int.nonneg_of_normalize_eq_self Int.nonneg_of_normalize_eq_self

/- warning: int.nonneg_iff_normalize_eq_self -> Int.nonneg_iff_normalize_eq_self is a dubious translation:
lean 3 declaration is
  forall (z : Int), Iff (Eq.{1} Int (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (fun (_x : MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) => Int -> Int) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) z) z) (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) z)
but is expected to have type
  forall (z : Int), Iff (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) z) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int (fun (_x : Int) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Int) => Int) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MulOneClass.toMul.{0} Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MulZeroOneClass.toMulOneClass.{0} Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))))) Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Int Int (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))) (MonoidWithZero.toMulZeroOneClass.{0} Int (CommMonoidWithZero.toMonoidWithZero.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))))))))) (normalize.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizationMonoid) z) z) (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) z)
Case conversion may be inaccurate. Consider using '#align int.nonneg_iff_normalize_eq_self Int.nonneg_iff_normalize_eq_selfₓ'. -/
theorem nonneg_iff_normalize_eq_self (z : ℤ) : normalize z = z ↔ 0 ≤ z :=
  ⟨nonneg_of_normalize_eq_self, normalize_of_nonneg⟩
#align int.nonneg_iff_normalize_eq_self Int.nonneg_iff_normalize_eq_self

/- warning: int.eq_of_associated_of_nonneg -> Int.eq_of_associated_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (Associated.{0} Int Int.monoid a b) -> (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a) -> (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) b) -> (Eq.{1} Int a b)
but is expected to have type
  forall {a : Int} {b : Int}, (Associated.{0} Int Int.instMonoidInt a b) -> (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a) -> (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) b) -> (Eq.{1} Int a b)
Case conversion may be inaccurate. Consider using '#align int.eq_of_associated_of_nonneg Int.eq_of_associated_of_nonnegₓ'. -/
theorem eq_of_associated_of_nonneg {a b : ℤ} (h : Associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a = b :=
  dvd_antisymm_of_normalize_eq (normalize_of_nonneg ha) (normalize_of_nonneg hb) h.Dvd h.symm.Dvd
#align int.eq_of_associated_of_nonneg Int.eq_of_associated_of_nonneg

end NormalizationMonoid

section GCDMonoid

instance : GCDMonoid ℤ where
  gcd a b := Int.gcd a b
  lcm a b := Int.lcm a b
  gcd_dvd_left a b := Int.gcd_dvd_left _ _
  gcd_dvd_right a b := Int.gcd_dvd_right _ _
  dvd_gcd a b c := dvd_gcd
  gcd_mul_lcm a b :=
    by
    rw [← Int.ofNat_mul, gcd_mul_lcm, coe_nat_abs, abs_eq_normalize]
    exact normalize_associated (a * b)
  lcm_zero_left a := coe_nat_eq_zero.2 <| Nat.lcm_zero_left _
  lcm_zero_right a := coe_nat_eq_zero.2 <| Nat.lcm_zero_right _

instance : NormalizedGCDMonoid ℤ :=
  { Int.normalizationMonoid,
    (inferInstance :
      GCDMonoid ℤ) with
    normalize_gcd := fun a b => normalize_coe_nat _
    normalize_lcm := fun a b => normalize_coe_nat _ }

#print Int.coe_gcd /-
theorem coe_gcd (i j : ℤ) : ↑(Int.gcd i j) = GCDMonoid.gcd i j :=
  rfl
#align int.coe_gcd Int.coe_gcd
-/

#print Int.coe_lcm /-
theorem coe_lcm (i j : ℤ) : ↑(Int.lcm i j) = GCDMonoid.lcm i j :=
  rfl
#align int.coe_lcm Int.coe_lcm
-/

#print Int.natAbs_gcd /-
theorem natAbs_gcd (i j : ℤ) : natAbs (GCDMonoid.gcd i j) = Int.gcd i j :=
  rfl
#align int.nat_abs_gcd Int.natAbs_gcd
-/

#print Int.natAbs_lcm /-
theorem natAbs_lcm (i j : ℤ) : natAbs (GCDMonoid.lcm i j) = Int.lcm i j :=
  rfl
#align int.nat_abs_lcm Int.natAbs_lcm
-/

end GCDMonoid

/- warning: int.exists_unit_of_abs -> Int.exists_unit_of_abs is a dubious translation:
lean 3 declaration is
  forall (a : Int), Exists.{1} Int (fun (u : Int) => Exists.{0} (IsUnit.{0} Int Int.monoid u) (fun (h : IsUnit.{0} Int Int.monoid u) => Eq.{1} Int ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Int.natAbs a)) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) u a)))
but is expected to have type
  forall (a : Int), Exists.{1} Int (fun (u : Int) => Exists.{0} (IsUnit.{0} Int Int.instMonoidInt u) (fun (h : IsUnit.{0} Int Int.instMonoidInt u) => Eq.{1} Int (Nat.cast.{0} Int instNatCastInt (Int.natAbs a)) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) u a)))
Case conversion may be inaccurate. Consider using '#align int.exists_unit_of_abs Int.exists_unit_of_absₓ'. -/
theorem exists_unit_of_abs (a : ℤ) : ∃ (u : ℤ)(h : IsUnit u), (Int.natAbs a : ℤ) = u * a :=
  by
  cases' nat_abs_eq a with h
  · use 1, isUnit_one
    rw [← h, one_mul]
  · use -1, is_unit_one.neg
    rw [← neg_eq_iff_eq_neg.mpr h]
    simp only [neg_mul, one_mul]
#align int.exists_unit_of_abs Int.exists_unit_of_abs

#print Int.gcd_eq_natAbs /-
theorem gcd_eq_natAbs {a b : ℤ} : Int.gcd a b = Nat.gcd a.natAbs b.natAbs :=
  rfl
#align int.gcd_eq_nat_abs Int.gcd_eq_natAbs
-/

/- warning: int.gcd_eq_one_iff_coprime -> Int.gcd_eq_one_iff_coprime is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, Iff (Eq.{1} Nat (Int.gcd a b) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (IsCoprime.{0} Int Int.commSemiring a b)
but is expected to have type
  forall {a : Int} {b : Int}, Iff (Eq.{1} Nat (Int.gcd a b) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (IsCoprime.{0} Int Int.instCommSemiringInt a b)
Case conversion may be inaccurate. Consider using '#align int.gcd_eq_one_iff_coprime Int.gcd_eq_one_iff_coprimeₓ'. -/
theorem gcd_eq_one_iff_coprime {a b : ℤ} : Int.gcd a b = 1 ↔ IsCoprime a b :=
  by
  constructor
  · intro hg
    obtain ⟨ua, hua, ha⟩ := exists_unit_of_abs a
    obtain ⟨ub, hub, hb⟩ := exists_unit_of_abs b
    use Nat.gcdA (Int.natAbs a) (Int.natAbs b) * ua, Nat.gcdB (Int.natAbs a) (Int.natAbs b) * ub
    rw [mul_assoc, ← ha, mul_assoc, ← hb, mul_comm, mul_comm _ (Int.natAbs b : ℤ), ←
      Nat.gcd_eq_gcd_ab, ← gcd_eq_nat_abs, hg, Int.ofNat_one]
  · rintro ⟨r, s, h⟩
    by_contra hg
    obtain ⟨p, ⟨hp, ha, hb⟩⟩ := nat.prime.not_coprime_iff_dvd.mp hg
    apply Nat.Prime.not_dvd_one hp
    rw [← coe_nat_dvd, Int.ofNat_one, ← h]
    exact dvd_add ((coe_nat_dvd_left.mpr ha).mul_left _) ((coe_nat_dvd_left.mpr hb).mul_left _)
#align int.gcd_eq_one_iff_coprime Int.gcd_eq_one_iff_coprime

/- warning: int.coprime_iff_nat_coprime -> Int.coprime_iff_nat_coprime is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, Iff (IsCoprime.{0} Int Int.commSemiring a b) (Nat.coprime (Int.natAbs a) (Int.natAbs b))
but is expected to have type
  forall {a : Int} {b : Int}, Iff (IsCoprime.{0} Int Int.instCommSemiringInt a b) (Nat.coprime (Int.natAbs a) (Int.natAbs b))
Case conversion may be inaccurate. Consider using '#align int.coprime_iff_nat_coprime Int.coprime_iff_nat_coprimeₓ'. -/
theorem coprime_iff_nat_coprime {a b : ℤ} : IsCoprime a b ↔ Nat.coprime a.natAbs b.natAbs := by
  rw [← gcd_eq_one_iff_coprime, Nat.coprime_iff_gcd_eq_one, gcd_eq_nat_abs]
#align int.coprime_iff_nat_coprime Int.coprime_iff_nat_coprime

#print Int.gcd_ne_one_iff_gcd_mul_right_ne_one /-
/-- If `gcd a (m * n) ≠ 1`, then `gcd a m ≠ 1` or `gcd a n ≠ 1`. -/
theorem gcd_ne_one_iff_gcd_mul_right_ne_one {a : ℤ} {m n : ℕ} :
    a.gcd (m * n) ≠ 1 ↔ a.gcd m ≠ 1 ∨ a.gcd n ≠ 1 := by
  simp only [gcd_eq_one_iff_coprime, ← not_and_or, not_iff_not, IsCoprime.mul_right_iff]
#align int.gcd_ne_one_iff_gcd_mul_right_ne_one Int.gcd_ne_one_iff_gcd_mul_right_ne_one
-/

#print Int.gcd_eq_one_of_gcd_mul_right_eq_one_left /-
/-- If `gcd a (m * n) = 1`, then `gcd a m = 1`. -/
theorem gcd_eq_one_of_gcd_mul_right_eq_one_left {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
    a.gcd m = 1 :=
  Nat.dvd_one.mp <| trans_rel_left _ (gcd_dvd_gcd_mul_right_right a m n) h
#align int.gcd_eq_one_of_gcd_mul_right_eq_one_left Int.gcd_eq_one_of_gcd_mul_right_eq_one_left
-/

#print Int.gcd_eq_one_of_gcd_mul_right_eq_one_right /-
/-- If `gcd a (m * n) = 1`, then `gcd a n = 1`. -/
theorem gcd_eq_one_of_gcd_mul_right_eq_one_right {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
    a.gcd n = 1 :=
  Nat.dvd_one.mp <| trans_rel_left _ (gcd_dvd_gcd_mul_left_right a n m) h
#align int.gcd_eq_one_of_gcd_mul_right_eq_one_right Int.gcd_eq_one_of_gcd_mul_right_eq_one_right
-/

/- warning: int.sq_of_gcd_eq_one -> Int.sq_of_gcd_eq_one is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int} {c : Int}, (Eq.{1} Nat (Int.gcd a b) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) a b) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) c (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) -> (Exists.{1} Int (fun (a0 : Int) => Or (Eq.{1} Int a (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) a0 (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (Eq.{1} Int a (Neg.neg.{0} Int Int.hasNeg (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) a0 (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))))
but is expected to have type
  forall {a : Int} {b : Int} {c : Int}, (Eq.{1} Nat (Int.gcd a b) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) a b) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) c (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) -> (Exists.{1} Int (fun (a0 : Int) => Or (Eq.{1} Int a (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) a0 (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (Eq.{1} Int a (Neg.neg.{0} Int Int.instNegInt (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) a0 (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))
Case conversion may be inaccurate. Consider using '#align int.sq_of_gcd_eq_one Int.sq_of_gcd_eq_oneₓ'. -/
theorem sq_of_gcd_eq_one {a b c : ℤ} (h : Int.gcd a b = 1) (heq : a * b = c ^ 2) :
    ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -a0 ^ 2 :=
  by
  have h' : IsUnit (GCDMonoid.gcd a b) :=
    by
    rw [← coe_gcd, h, Int.ofNat_one]
    exact isUnit_one
  obtain ⟨d, ⟨u, hu⟩⟩ := exists_associated_pow_of_mul_eq_pow h' HEq
  use d
  rw [← hu]
  cases' Int.units_eq_one_or u with hu' hu' <;>
    · rw [hu']
      simp
#align int.sq_of_gcd_eq_one Int.sq_of_gcd_eq_one

/- warning: int.sq_of_coprime -> Int.sq_of_coprime is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int} {c : Int}, (IsCoprime.{0} Int Int.commSemiring a b) -> (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) a b) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) c (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) -> (Exists.{1} Int (fun (a0 : Int) => Or (Eq.{1} Int a (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) a0 (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (Eq.{1} Int a (Neg.neg.{0} Int Int.hasNeg (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) a0 (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))))
but is expected to have type
  forall {a : Int} {b : Int} {c : Int}, (IsCoprime.{0} Int Int.instCommSemiringInt a b) -> (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) a b) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) c (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) -> (Exists.{1} Int (fun (a0 : Int) => Or (Eq.{1} Int a (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) a0 (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (Eq.{1} Int a (Neg.neg.{0} Int Int.instNegInt (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) a0 (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))
Case conversion may be inaccurate. Consider using '#align int.sq_of_coprime Int.sq_of_coprimeₓ'. -/
theorem sq_of_coprime {a b c : ℤ} (h : IsCoprime a b) (heq : a * b = c ^ 2) :
    ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -a0 ^ 2 :=
  sq_of_gcd_eq_one (gcd_eq_one_iff_coprime.mpr h) HEq
#align int.sq_of_coprime Int.sq_of_coprime

/- warning: int.nat_abs_euclidean_domain_gcd -> Int.natAbs_euclideanDomain_gcd is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Eq.{1} Nat (Int.natAbs (EuclideanDomain.gcd.{0} Int Int.euclideanDomain (fun (a : Int) (b : Int) => Int.decidableEq a b) a b)) (Int.gcd a b)
but is expected to have type
  forall (a : Int) (b : Int), Eq.{1} Nat (Int.natAbs (EuclideanDomain.gcd.{0} ([mdata borrowed:1 Int]) Int.euclideanDomain (fun (a : [mdata borrowed:1 Int]) (b : [mdata borrowed:1 Int]) => Int.instDecidableEqInt a b) a b)) (Int.gcd a b)
Case conversion may be inaccurate. Consider using '#align int.nat_abs_euclidean_domain_gcd Int.natAbs_euclideanDomain_gcdₓ'. -/
theorem natAbs_euclideanDomain_gcd (a b : ℤ) : Int.natAbs (EuclideanDomain.gcd a b) = Int.gcd a b :=
  by
  apply Nat.dvd_antisymm <;> rw [← Int.coe_nat_dvd]
  · rw [Int.natAbs_dvd]
    exact Int.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
  · rw [Int.dvd_natAbs]
    exact EuclideanDomain.dvd_gcd (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
#align int.nat_abs_euclidean_domain_gcd Int.natAbs_euclideanDomain_gcd

end Int

/- warning: associates_int_equiv_nat -> associatesIntEquivNat is a dubious translation:
lean 3 declaration is
  Equiv.{1, 1} (Associates.{0} Int Int.monoid) Nat
but is expected to have type
  Equiv.{1, 1} (Associates.{0} Int Int.instMonoidInt) Nat
Case conversion may be inaccurate. Consider using '#align associates_int_equiv_nat associatesIntEquivNatₓ'. -/
/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
def associatesIntEquivNat : Associates ℤ ≃ ℕ :=
  by
  refine' ⟨fun z => z.out.nat_abs, fun n => Associates.mk n, _, _⟩
  · refine' fun a =>
      Quotient.inductionOn' a fun a =>
        Associates.mk_eq_mk_iff_associated.2 <| Associated.symm <| ⟨norm_unit a, _⟩
    show normalize a = Int.natAbs (normalize a)
    rw [Int.coe_natAbs, Int.abs_eq_normalize, normalize_idem]
  · intro n
    dsimp
    rw [← normalize_apply, ← Int.abs_eq_normalize, Int.natAbs_abs, Int.natAbs_ofNat]
#align associates_int_equiv_nat associatesIntEquivNat

/- warning: int.prime.dvd_mul -> Int.Prime.dvd_mul is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int} {p : Nat}, (Nat.Prime p) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) m n)) -> (Or (Dvd.Dvd.{0} Nat Nat.hasDvd p (Int.natAbs m)) (Dvd.Dvd.{0} Nat Nat.hasDvd p (Int.natAbs n)))
but is expected to have type
  forall {m : Int} {n : Int} {p : Nat}, (Nat.Prime p) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) m n)) -> (Or (Dvd.dvd.{0} Nat Nat.instDvdNat p (Int.natAbs m)) (Dvd.dvd.{0} Nat Nat.instDvdNat p (Int.natAbs n)))
Case conversion may be inaccurate. Consider using '#align int.prime.dvd_mul Int.Prime.dvd_mulₓ'. -/
theorem Int.Prime.dvd_mul {m n : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ m * n) :
    p ∣ m.natAbs ∨ p ∣ n.natAbs :=
  by
  apply (Nat.Prime.dvd_mul hp).mp
  rw [← Int.natAbs_mul]
  exact int.coe_nat_dvd_left.mp h
#align int.prime.dvd_mul Int.Prime.dvd_mul

/- warning: int.prime.dvd_mul' -> Int.Prime.dvd_mul' is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int} {p : Nat}, (Nat.Prime p) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) m n)) -> (Or (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) m) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) n))
but is expected to have type
  forall {m : Int} {n : Int} {p : Nat}, (Nat.Prime p) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) m n)) -> (Or (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) m) (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) n))
Case conversion may be inaccurate. Consider using '#align int.prime.dvd_mul' Int.Prime.dvd_mul'ₓ'. -/
theorem Int.Prime.dvd_mul' {m n : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ m * n) :
    (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n :=
  by
  rw [Int.coe_nat_dvd_left, Int.coe_nat_dvd_left]
  exact Int.Prime.dvd_mul hp h
#align int.prime.dvd_mul' Int.Prime.dvd_mul'

/- warning: int.prime.dvd_pow -> Int.Prime.dvd_pow is a dubious translation:
lean 3 declaration is
  forall {n : Int} {k : Nat} {p : Nat}, (Nat.Prime p) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) n k)) -> (Dvd.Dvd.{0} Nat Nat.hasDvd p (Int.natAbs n))
but is expected to have type
  forall {n : Int} {k : Nat} {p : Nat}, (Nat.Prime p) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat n k)) -> (Dvd.dvd.{0} Nat Nat.instDvdNat p (Int.natAbs n))
Case conversion may be inaccurate. Consider using '#align int.prime.dvd_pow Int.Prime.dvd_powₓ'. -/
theorem Int.Prime.dvd_pow {n : ℤ} {k p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ n ^ k) :
    p ∣ n.natAbs := by
  apply @Nat.Prime.dvd_of_dvd_pow _ _ k hp
  rw [← Int.natAbs_pow]
  exact int.coe_nat_dvd_left.mp h
#align int.prime.dvd_pow Int.Prime.dvd_pow

/- warning: int.prime.dvd_pow' -> Int.Prime.dvd_pow' is a dubious translation:
lean 3 declaration is
  forall {n : Int} {k : Nat} {p : Nat}, (Nat.Prime p) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) n k)) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) n)
but is expected to have type
  forall {n : Int} {k : Nat} {p : Nat}, (Nat.Prime p) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat n k)) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) n)
Case conversion may be inaccurate. Consider using '#align int.prime.dvd_pow' Int.Prime.dvd_pow'ₓ'. -/
theorem Int.Prime.dvd_pow' {n : ℤ} {k p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ n ^ k) :
    (p : ℤ) ∣ n := by
  rw [Int.coe_nat_dvd_left]
  exact Int.Prime.dvd_pow hp h
#align int.prime.dvd_pow' Int.Prime.dvd_pow'

/- warning: prime_two_or_dvd_of_dvd_two_mul_pow_self_two -> prime_two_or_dvd_of_dvd_two_mul_pow_self_two is a dubious translation:
lean 3 declaration is
  forall {m : Int} {p : Nat}, (Nat.Prime p) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (OfNat.ofNat.{0} Int 2 (OfNat.mk.{0} Int 2 (bit0.{0} Int Int.hasAdd (One.one.{0} Int Int.hasOne)))) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) m (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))) -> (Or (Eq.{1} Nat p (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Dvd.Dvd.{0} Nat Nat.hasDvd p (Int.natAbs m)))
but is expected to have type
  forall {m : Int} {p : Nat}, (Nat.Prime p) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (OfNat.ofNat.{0} Int 2 (instOfNatInt 2)) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) m (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) -> (Or (Eq.{1} Nat p (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Dvd.dvd.{0} Nat Nat.instDvdNat p (Int.natAbs m)))
Case conversion may be inaccurate. Consider using '#align prime_two_or_dvd_of_dvd_two_mul_pow_self_two prime_two_or_dvd_of_dvd_two_mul_pow_self_twoₓ'. -/
theorem prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m : ℤ} {p : ℕ} (hp : Nat.Prime p)
    (h : (p : ℤ) ∣ 2 * m ^ 2) : p = 2 ∨ p ∣ Int.natAbs m :=
  by
  cases' Int.Prime.dvd_mul hp h with hp2 hpp
  · apply Or.intro_left
    exact le_antisymm (Nat.le_of_dvd zero_lt_two hp2) (Nat.Prime.two_le hp)
  · apply Or.intro_right
    rw [sq, Int.natAbs_mul] at hpp
    exact (or_self_iff _).mp ((Nat.Prime.dvd_mul hp).mp hpp)
#align prime_two_or_dvd_of_dvd_two_mul_pow_self_two prime_two_or_dvd_of_dvd_two_mul_pow_self_two

/- warning: int.exists_prime_and_dvd -> Int.exists_prime_and_dvd is a dubious translation:
lean 3 declaration is
  forall {n : Int}, (Ne.{1} Nat (Int.natAbs n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> (Exists.{1} Int (fun (p : Int) => And (Prime.{0} Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring) p) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) p n)))
but is expected to have type
  forall {n : Int}, (Ne.{1} Nat (Int.natAbs n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> (Exists.{1} Int (fun (p : Int) => And (Prime.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) p) (Dvd.dvd.{0} Int Int.instDvdInt p n)))
Case conversion may be inaccurate. Consider using '#align int.exists_prime_and_dvd Int.exists_prime_and_dvdₓ'. -/
theorem Int.exists_prime_and_dvd {n : ℤ} (hn : n.natAbs ≠ 1) : ∃ p, Prime p ∧ p ∣ n :=
  by
  obtain ⟨p, pp, pd⟩ := Nat.exists_prime_and_dvd hn
  exact ⟨p, nat.prime_iff_prime_int.mp pp, int.coe_nat_dvd_left.mpr pd⟩
#align int.exists_prime_and_dvd Int.exists_prime_and_dvd

open UniqueFactorizationMonoid

/- warning: nat.factors_eq -> Nat.factors_eq is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} (Multiset.{0} Nat) (UniqueFactorizationMonoid.normalizedFactors.{0} Nat Nat.cancelCommMonoidWithZero (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (normalizationMonoidOfUniqueUnits.{0} Nat Nat.cancelCommMonoidWithZero Nat.unique_units) Nat.uniqueFactorizationMonoid n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (List.{0} Nat) (Multiset.{0} Nat) (HasLiftT.mk.{1, 1} (List.{0} Nat) (Multiset.{0} Nat) (CoeTCₓ.coe.{1, 1} (List.{0} Nat) (Multiset.{0} Nat) (coeBase.{1, 1} (List.{0} Nat) (Multiset.{0} Nat) (Multiset.hasCoe.{0} Nat)))) (Nat.factors n))
but is expected to have type
  forall {n : Nat}, Eq.{1} (Multiset.{0} Nat) (UniqueFactorizationMonoid.normalizedFactors.{0} Nat Nat.cancelCommMonoidWithZero (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (NormalizedGCDMonoid.toNormalizationMonoid.{0} Nat Nat.cancelCommMonoidWithZero instNormalizedGCDMonoidNatCancelCommMonoidWithZero) Nat.instUniqueFactorizationMonoidNatCancelCommMonoidWithZero n) (Multiset.ofList.{0} Nat (Nat.factors n))
Case conversion may be inaccurate. Consider using '#align nat.factors_eq Nat.factors_eqₓ'. -/
theorem Nat.factors_eq {n : ℕ} : normalizedFactors n = n.factors :=
  by
  cases n; · simp
  rw [← Multiset.rel_eq, ← associated_eq_eq]
  apply factors_unique irreducible_of_normalized_factor _
  · rw [Multiset.coe_prod, Nat.prod_factors n.succ_ne_zero]
    apply normalized_factors_prod (Nat.succ_ne_zero _)
  · infer_instance
  · intro x hx
    rw [Nat.irreducible_iff_prime, ← Nat.prime_iff]
    exact Nat.prime_of_mem_factors hx
#align nat.factors_eq Nat.factors_eq

/- warning: nat.factors_multiset_prod_of_irreducible -> Nat.factors_multiset_prod_of_irreducible is a dubious translation:
lean 3 declaration is
  forall {s : Multiset.{0} Nat}, (forall (x : Nat), (Membership.Mem.{0, 0} Nat (Multiset.{0} Nat) (Multiset.hasMem.{0} Nat) x s) -> (Irreducible.{0} Nat Nat.monoid x)) -> (Eq.{1} (Multiset.{0} Nat) (UniqueFactorizationMonoid.normalizedFactors.{0} Nat Nat.cancelCommMonoidWithZero (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (normalizationMonoidOfUniqueUnits.{0} Nat Nat.cancelCommMonoidWithZero Nat.unique_units) Nat.uniqueFactorizationMonoid (Multiset.prod.{0} Nat Nat.commMonoid s)) s)
but is expected to have type
  forall {s : Multiset.{0} Nat}, (forall (x : Nat), (Membership.mem.{0, 0} Nat (Multiset.{0} Nat) (Multiset.instMembershipMultiset.{0} Nat) x s) -> (Irreducible.{0} Nat Nat.monoid x)) -> (Eq.{1} (Multiset.{0} Nat) (UniqueFactorizationMonoid.normalizedFactors.{0} Nat Nat.cancelCommMonoidWithZero (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (NormalizedGCDMonoid.toNormalizationMonoid.{0} Nat Nat.cancelCommMonoidWithZero instNormalizedGCDMonoidNatCancelCommMonoidWithZero) Nat.instUniqueFactorizationMonoidNatCancelCommMonoidWithZero (Multiset.prod.{0} Nat Nat.commMonoid s)) s)
Case conversion may be inaccurate. Consider using '#align nat.factors_multiset_prod_of_irreducible Nat.factors_multiset_prod_of_irreducibleₓ'. -/
theorem Nat.factors_multiset_prod_of_irreducible {s : Multiset ℕ}
    (h : ∀ x : ℕ, x ∈ s → Irreducible x) : normalizedFactors s.Prod = s :=
  by
  rw [← Multiset.rel_eq, ← associated_eq_eq]
  apply
    UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor h
      (normalized_factors_prod _)
  rw [Ne.def, Multiset.prod_eq_zero_iff]
  intro con
  exact not_irreducible_zero (h 0 Con)
#align nat.factors_multiset_prod_of_irreducible Nat.factors_multiset_prod_of_irreducible

namespace multiplicity

/- warning: multiplicity.finite_int_iff_nat_abs_finite -> multiplicity.finite_int_iff_natAbs_finite is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, Iff (multiplicity.Finite.{0} Int Int.monoid a b) (multiplicity.Finite.{0} Nat Nat.monoid (Int.natAbs a) (Int.natAbs b))
but is expected to have type
  forall {a : Int} {b : Int}, Iff (multiplicity.Finite.{0} Int Int.instMonoidInt a b) (multiplicity.Finite.{0} Nat Nat.monoid (Int.natAbs a) (Int.natAbs b))
Case conversion may be inaccurate. Consider using '#align multiplicity.finite_int_iff_nat_abs_finite multiplicity.finite_int_iff_natAbs_finiteₓ'. -/
theorem finite_int_iff_natAbs_finite {a b : ℤ} : Finite a b ↔ Finite a.natAbs b.natAbs := by
  simp only [finite_def, ← Int.natAbs_dvd_natAbs, Int.natAbs_pow]
#align multiplicity.finite_int_iff_nat_abs_finite multiplicity.finite_int_iff_natAbs_finite

/- warning: multiplicity.finite_int_iff -> multiplicity.finite_int_iff is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, Iff (multiplicity.Finite.{0} Int Int.monoid a b) (And (Ne.{1} Nat (Int.natAbs a) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Ne.{1} Int b (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))))
but is expected to have type
  forall {a : Int} {b : Int}, Iff (multiplicity.Finite.{0} Int Int.instMonoidInt a b) (And (Ne.{1} Nat (Int.natAbs a) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Ne.{1} Int b (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))))
Case conversion may be inaccurate. Consider using '#align multiplicity.finite_int_iff multiplicity.finite_int_iffₓ'. -/
theorem finite_int_iff {a b : ℤ} : Finite a b ↔ a.natAbs ≠ 1 ∧ b ≠ 0 := by
  rw [finite_int_iff_nat_abs_finite, finite_nat_iff, pos_iff_ne_zero, Int.natAbs_ne_zero]
#align multiplicity.finite_int_iff multiplicity.finite_int_iff

#print multiplicity.decidableNat /-
instance decidableNat : DecidableRel fun a b : ℕ => (multiplicity a b).Dom := fun a b =>
  decidable_of_iff _ finite_nat_iff.symm
#align multiplicity.decidable_nat multiplicity.decidableNat
-/

/- warning: multiplicity.decidable_int -> multiplicity.decidableInt is a dubious translation:
lean 3 declaration is
  DecidableRel.{1} Int (fun (a : Int) (b : Int) => Part.Dom.{0} Nat (multiplicity.{0} Int Int.monoid (fun (a : Int) (b : Int) => Int.decidableDvd a b) a b))
but is expected to have type
  DecidableRel.{1} Int (fun (a : Int) (b : Int) => Part.Dom.{0} Nat (multiplicity.{0} Int Int.instMonoidInt (fun (a : Int) (b : Int) => Int.decidableDvd a b) a b))
Case conversion may be inaccurate. Consider using '#align multiplicity.decidable_int multiplicity.decidableIntₓ'. -/
instance decidableInt : DecidableRel fun a b : ℤ => (multiplicity a b).Dom := fun a b =>
  decidable_of_iff _ finite_int_iff.symm
#align multiplicity.decidable_int multiplicity.decidableInt

end multiplicity

#print induction_on_primes /-
theorem induction_on_primes {P : ℕ → Prop} (h₀ : P 0) (h₁ : P 1)
    (h : ∀ p a : ℕ, p.Prime → P a → P (p * a)) (n : ℕ) : P n :=
  by
  apply UniqueFactorizationMonoid.induction_on_prime
  exact h₀
  · intro n h
    rw [Nat.isUnit_iff.1 h]
    exact h₁
  · intro a p _ hp ha
    exact h p a hp.nat_prime ha
#align induction_on_primes induction_on_primes
-/

/- warning: int.associated_nat_abs -> Int.associated_natAbs is a dubious translation:
lean 3 declaration is
  forall (k : Int), Associated.{0} Int Int.monoid k ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Int.natAbs k))
but is expected to have type
  forall (k : Int), Associated.{0} Int Int.instMonoidInt k (Nat.cast.{0} Int instNatCastInt (Int.natAbs k))
Case conversion may be inaccurate. Consider using '#align int.associated_nat_abs Int.associated_natAbsₓ'. -/
theorem Int.associated_natAbs (k : ℤ) : Associated k k.natAbs :=
  associated_of_dvd_dvd (Int.coe_nat_dvd_right.mpr dvd_rfl) (Int.natAbs_dvd.mpr dvd_rfl)
#align int.associated_nat_abs Int.associated_natAbs

/- warning: int.prime_iff_nat_abs_prime -> Int.prime_iff_natAbs_prime is a dubious translation:
lean 3 declaration is
  forall {k : Int}, Iff (Prime.{0} Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring) k) (Nat.Prime (Int.natAbs k))
but is expected to have type
  forall {k : Int}, Iff (Prime.{0} Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) k) (Nat.Prime (Int.natAbs k))
Case conversion may be inaccurate. Consider using '#align int.prime_iff_nat_abs_prime Int.prime_iff_natAbs_primeₓ'. -/
theorem Int.prime_iff_natAbs_prime {k : ℤ} : Prime k ↔ Nat.Prime k.natAbs :=
  (Int.associated_natAbs k).prime_iff.trans Nat.prime_iff_prime_int.symm
#align int.prime_iff_nat_abs_prime Int.prime_iff_natAbs_prime

/- warning: int.associated_iff_nat_abs -> Int.associated_iff_natAbs is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, Iff (Associated.{0} Int Int.monoid a b) (Eq.{1} Nat (Int.natAbs a) (Int.natAbs b))
but is expected to have type
  forall {a : Int} {b : Int}, Iff (Associated.{0} Int Int.instMonoidInt a b) (Eq.{1} Nat (Int.natAbs a) (Int.natAbs b))
Case conversion may be inaccurate. Consider using '#align int.associated_iff_nat_abs Int.associated_iff_natAbsₓ'. -/
theorem Int.associated_iff_natAbs {a b : ℤ} : Associated a b ↔ a.natAbs = b.natAbs :=
  by
  rw [← dvd_dvd_iff_associated, ← Int.natAbs_dvd_natAbs, ← Int.natAbs_dvd_natAbs,
    dvd_dvd_iff_associated]
  exact associated_iff_eq
#align int.associated_iff_nat_abs Int.associated_iff_natAbs

/- warning: int.associated_iff -> Int.associated_iff is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, Iff (Associated.{0} Int Int.monoid a b) (Or (Eq.{1} Int a b) (Eq.{1} Int a (Neg.neg.{0} Int Int.hasNeg b)))
but is expected to have type
  forall {a : Int} {b : Int}, Iff (Associated.{0} Int Int.instMonoidInt a b) (Or (Eq.{1} Int a b) (Eq.{1} Int a (Neg.neg.{0} Int Int.instNegInt b)))
Case conversion may be inaccurate. Consider using '#align int.associated_iff Int.associated_iffₓ'. -/
theorem Int.associated_iff {a b : ℤ} : Associated a b ↔ a = b ∨ a = -b :=
  by
  rw [Int.associated_iff_natAbs]
  exact Int.natAbs_eq_natAbs_iff
#align int.associated_iff Int.associated_iff

namespace Int

/- warning: int.zmultiples_nat_abs -> Int.zmultiples_natAbs is a dubious translation:
lean 3 declaration is
  forall (a : Int), Eq.{1} (AddSubgroup.{0} Int Int.addGroup) (AddSubgroup.zmultiples.{0} Int Int.addGroup ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Int.natAbs a))) (AddSubgroup.zmultiples.{0} Int Int.addGroup a)
but is expected to have type
  forall (a : Int), Eq.{1} (AddSubgroup.{0} Int Int.instAddGroupInt) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt (Nat.cast.{0} Int instNatCastInt (Int.natAbs a))) (AddSubgroup.zmultiples.{0} Int Int.instAddGroupInt a)
Case conversion may be inaccurate. Consider using '#align int.zmultiples_nat_abs Int.zmultiples_natAbsₓ'. -/
theorem zmultiples_natAbs (a : ℤ) :
    AddSubgroup.zmultiples (a.natAbs : ℤ) = AddSubgroup.zmultiples a :=
  le_antisymm (AddSubgroup.zmultiples_subset (mem_zmultiples_iff.mpr (dvd_natAbs.mpr (dvd_refl a))))
    (AddSubgroup.zmultiples_subset (mem_zmultiples_iff.mpr (natAbs_dvd.mpr (dvd_refl a))))
#align int.zmultiples_nat_abs Int.zmultiples_natAbs

/- warning: int.span_nat_abs -> Int.span_natAbs is a dubious translation:
lean 3 declaration is
  forall (a : Int), Eq.{1} (Ideal.{0} Int Int.semiring) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Int.natAbs a)))) (Ideal.span.{0} Int Int.semiring (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.hasSingleton.{0} Int) a))
but is expected to have type
  forall (a : Int), Eq.{1} (Ideal.{0} Int Int.instSemiringInt) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) (Nat.cast.{0} Int instNatCastInt (Int.natAbs a)))) (Ideal.span.{0} Int Int.instSemiringInt (Singleton.singleton.{0, 0} Int (Set.{0} Int) (Set.instSingletonSet.{0} Int) a))
Case conversion may be inaccurate. Consider using '#align int.span_nat_abs Int.span_natAbsₓ'. -/
theorem span_natAbs (a : ℤ) : Ideal.span ({a.natAbs} : Set ℤ) = Ideal.span {a} :=
  by
  rw [Ideal.span_singleton_eq_span_singleton]
  exact (associated_nat_abs _).symm
#align int.span_nat_abs Int.span_natAbs

/- warning: int.eq_pow_of_mul_eq_pow_bit1_left -> Int.eq_pow_of_mul_eq_pow_bit1_left is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int} {c : Int}, (IsCoprime.{0} Int Int.commSemiring a b) -> (forall {k : Nat}, (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) a b) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) c (bit1.{0} Nat Nat.hasOne Nat.hasAdd k))) -> (Exists.{1} Int (fun (d : Int) => Eq.{1} Int a (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) d (bit1.{0} Nat Nat.hasOne Nat.hasAdd k)))))
but is expected to have type
  forall {a : Int} {b : Int} {c : Int}, (IsCoprime.{0} Int Int.instCommSemiringInt a b) -> (forall {k : Nat}, (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) a b) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat c (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat k))) -> (Exists.{1} Int (fun (d : Int) => Eq.{1} Int a (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) d (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat k)))))
Case conversion may be inaccurate. Consider using '#align int.eq_pow_of_mul_eq_pow_bit1_left Int.eq_pow_of_mul_eq_pow_bit1_leftₓ'. -/
theorem eq_pow_of_mul_eq_pow_bit1_left {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ bit1 k) : ∃ d, a = d ^ bit1 k :=
  by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hab h
  replace hd := hd.symm
  rw [associated_iff_nat_abs, nat_abs_eq_nat_abs_iff, ← neg_pow_bit1] at hd
  obtain rfl | rfl := hd <;> exact ⟨_, rfl⟩
#align int.eq_pow_of_mul_eq_pow_bit1_left Int.eq_pow_of_mul_eq_pow_bit1_left

/- warning: int.eq_pow_of_mul_eq_pow_bit1_right -> Int.eq_pow_of_mul_eq_pow_bit1_right is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int} {c : Int}, (IsCoprime.{0} Int Int.commSemiring a b) -> (forall {k : Nat}, (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) a b) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) c (bit1.{0} Nat Nat.hasOne Nat.hasAdd k))) -> (Exists.{1} Int (fun (d : Int) => Eq.{1} Int b (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) d (bit1.{0} Nat Nat.hasOne Nat.hasAdd k)))))
but is expected to have type
  forall {a : Int} {b : Int} {c : Int}, (IsCoprime.{0} Int Int.instCommSemiringInt a b) -> (forall {k : Nat}, (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) a b) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat c (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat k))) -> (Exists.{1} Int (fun (d : Int) => Eq.{1} Int b (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) d (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat k)))))
Case conversion may be inaccurate. Consider using '#align int.eq_pow_of_mul_eq_pow_bit1_right Int.eq_pow_of_mul_eq_pow_bit1_rightₓ'. -/
theorem eq_pow_of_mul_eq_pow_bit1_right {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ bit1 k) : ∃ d, b = d ^ bit1 k :=
  eq_pow_of_mul_eq_pow_bit1_left hab.symm (by rwa [mul_comm] at h)
#align int.eq_pow_of_mul_eq_pow_bit1_right Int.eq_pow_of_mul_eq_pow_bit1_right

/- warning: int.eq_pow_of_mul_eq_pow_bit1 -> Int.eq_pow_of_mul_eq_pow_bit1 is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int} {c : Int}, (IsCoprime.{0} Int Int.commSemiring a b) -> (forall {k : Nat}, (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) a b) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) c (bit1.{0} Nat Nat.hasOne Nat.hasAdd k))) -> (And (Exists.{1} Int (fun (d : Int) => Eq.{1} Int a (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) d (bit1.{0} Nat Nat.hasOne Nat.hasAdd k)))) (Exists.{1} Int (fun (e : Int) => Eq.{1} Int b (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) e (bit1.{0} Nat Nat.hasOne Nat.hasAdd k))))))
but is expected to have type
  forall {a : Int} {b : Int} {c : Int}, (IsCoprime.{0} Int Int.instCommSemiringInt a b) -> (forall {k : Nat}, (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) a b) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat c (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat k))) -> (And (Exists.{1} Int (fun (d : Int) => Eq.{1} Int a (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) d (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat k)))) (Exists.{1} Int (fun (e : Int) => Eq.{1} Int b (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) e (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat k))))))
Case conversion may be inaccurate. Consider using '#align int.eq_pow_of_mul_eq_pow_bit1 Int.eq_pow_of_mul_eq_pow_bit1ₓ'. -/
theorem eq_pow_of_mul_eq_pow_bit1 {a b c : ℤ} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ bit1 k) : (∃ d, a = d ^ bit1 k) ∧ ∃ e, b = e ^ bit1 k :=
  ⟨eq_pow_of_mul_eq_pow_bit1_left hab h, eq_pow_of_mul_eq_pow_bit1_right hab h⟩
#align int.eq_pow_of_mul_eq_pow_bit1 Int.eq_pow_of_mul_eq_pow_bit1

end Int

