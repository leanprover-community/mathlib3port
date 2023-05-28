/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Yury Kudryashov

! This file was ported from Lean 3 source module data.real.irrational
! leanprover-community/mathlib commit 38df578a6450a8c5142b3727e3ae894c2300cae0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Sqrt
import Mathbin.Tactic.IntervalCases
import Mathbin.RingTheory.Algebraic
import Mathbin.Data.Rat.Sqrt
import Mathbin.RingTheory.Int.Basic

/-!
# Irrational real numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a predicate `irrational` on `ℝ`, prove that the `n`-th root of an integer
number is irrational if it is not integer, and that `sqrt q` is irrational if and only if
`rat.sqrt q * rat.sqrt q ≠ q ∧ 0 ≤ q`.

We also provide dot-style constructors like `irrational.add_rat`, `irrational.rat_sub` etc.
-/


open Rat Real multiplicity

#print Irrational /-
/-- A real number is irrational if it is not equal to any rational number. -/
def Irrational (x : ℝ) :=
  x ∉ Set.range (coe : ℚ → ℝ)
#align irrational Irrational
-/

/- warning: irrational_iff_ne_rational -> irrational_iff_ne_rational is a dubious translation:
lean 3 declaration is
  forall (x : Real), Iff (Irrational x) (forall (a : Int) (b : Int), Ne.{1} Real x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) b)))
but is expected to have type
  forall (x : Real), Iff (Irrational x) (forall (a : Int) (b : Int), Ne.{1} Real x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Int.cast.{0} Real Real.intCast a) (Int.cast.{0} Real Real.intCast b)))
Case conversion may be inaccurate. Consider using '#align irrational_iff_ne_rational irrational_iff_ne_rationalₓ'. -/
theorem irrational_iff_ne_rational (x : ℝ) : Irrational x ↔ ∀ a b : ℤ, x ≠ a / b := by
  simp only [Irrational, Rat.forall, cast_mk, not_exists, Set.mem_range, cast_coe_int, cast_div,
    eq_comm]
#align irrational_iff_ne_rational irrational_iff_ne_rational

#print Transcendental.irrational /-
/-- A transcendental real number is irrational. -/
theorem Transcendental.irrational {r : ℝ} (tr : Transcendental ℚ r) : Irrational r := by
  rintro ⟨a, rfl⟩; exact tr (isAlgebraic_algebraMap a)
#align transcendental.irrational Transcendental.irrational
-/

/-!
### Irrationality of roots of integer and rational numbers
-/


/- warning: irrational_nrt_of_notint_nrt -> irrational_nrt_of_notint_nrt is a dubious translation:
lean 3 declaration is
  forall {x : Real} (n : Nat) (m : Int), (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m)) -> (Not (Exists.{1} Int (fun (y : Int) => Eq.{1} Real x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) y)))) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Irrational x)
but is expected to have type
  forall {x : Real} (n : Nat) (m : Int), (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n) (Int.cast.{0} Real Real.intCast m)) -> (Not (Exists.{1} Int (fun (y : Int) => Eq.{1} Real x (Int.cast.{0} Real Real.intCast y)))) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_nrt_of_notint_nrt irrational_nrt_of_notint_nrtₓ'. -/
/-- If `x^n`, `n > 0`, is integer and is not the `n`-th power of an integer, then
`x` is irrational. -/
theorem irrational_nrt_of_notint_nrt {x : ℝ} (n : ℕ) (m : ℤ) (hxr : x ^ n = m)
    (hv : ¬∃ y : ℤ, x = y) (hnpos : 0 < n) : Irrational x :=
  by
  rintro ⟨⟨N, D, P, C⟩, rfl⟩
  rw [← cast_pow] at hxr
  have c1 : ((D : ℤ) : ℝ) ≠ 0 := by rw [Int.cast_ne_zero, Int.coe_nat_ne_zero]; exact ne_of_gt P
  have c2 : ((D : ℤ) : ℝ) ^ n ≠ 0 := pow_ne_zero _ c1
  rw [num_denom', cast_pow, cast_mk, div_pow, div_eq_iff_mul_eq c2, ← Int.cast_pow, ← Int.cast_pow,
    ← Int.cast_mul, Int.cast_inj] at hxr
  have hdivn : ↑D ^ n ∣ N ^ n := Dvd.intro_left m hxr
  rw [← Int.dvd_natAbs, ← Int.coe_nat_pow, Int.coe_nat_dvd, Int.natAbs_pow,
    Nat.pow_dvd_pow_iff hnpos] at hdivn
  obtain rfl : D = 1 := by rw [← Nat.gcd_eq_right hdivn, C.gcd_eq_one]
  refine' hv ⟨N, _⟩
  rw [num_denom', Int.ofNat_one, mk_eq_div, Int.cast_one, div_one, cast_coe_int]
#align irrational_nrt_of_notint_nrt irrational_nrt_of_notint_nrt

/- warning: irrational_nrt_of_n_not_dvd_multiplicity -> irrational_nrt_of_n_not_dvd_multiplicity is a dubious translation:
lean 3 declaration is
  forall {x : Real} (n : Nat) {m : Int} (hm : Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (p : Nat) [hp : Fact (Nat.Prime p)], (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m)) -> (Ne.{1} Nat (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (Part.get.{0} Nat (multiplicity.{0} Int Int.monoid (fun (a : Int) (b : Int) => Int.decidableDvd a b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) m) (Iff.mpr (multiplicity.Finite.{0} Int Int.monoid ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) m) (And (Ne.{1} Nat (Int.natAbs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))) (multiplicity.finite_int_iff ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) m) (And.intro (Ne.{1} Nat (Int.natAbs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Nat.Prime.ne_one p (Fact.out (Nat.Prime p) hp)) hm))) n) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Irrational x)
but is expected to have type
  forall {x : Real} (n : Nat) {m : Int} (hm : Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (p : Nat) [hp : Fact (Nat.Prime p)], (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n) (Int.cast.{0} Real Real.intCast m)) -> (Ne.{1} Nat (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (Part.get.{0} Nat (multiplicity.{0} Int Int.instMonoidInt (fun (a : Int) (b : Int) => Int.decidableDvd a b) (Nat.cast.{0} Int instNatCastInt p) m) (Iff.mpr (multiplicity.Finite.{0} Int Int.instMonoidInt (Nat.cast.{0} Int instNatCastInt p) m) (And (Ne.{1} Nat (Int.natAbs (Nat.cast.{0} Int instNatCastInt p)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))) (multiplicity.finite_int_iff (Nat.cast.{0} Int instNatCastInt p) m) (And.intro (Ne.{1} Nat (Int.natAbs (Nat.cast.{0} Int instNatCastInt p)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Nat.Prime.ne_one p (Fact.out (Nat.Prime p) hp)) hm))) n) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_nrt_of_n_not_dvd_multiplicity irrational_nrt_of_n_not_dvd_multiplicityₓ'. -/
/-- If `x^n = m` is an integer and `n` does not divide the `multiplicity p m`, then `x`
is irrational. -/
theorem irrational_nrt_of_n_not_dvd_multiplicity {x : ℝ} (n : ℕ) {m : ℤ} (hm : m ≠ 0) (p : ℕ)
    [hp : Fact p.Prime] (hxr : x ^ n = m)
    (hv : (multiplicity (p : ℤ) m).get (finite_int_iff.2 ⟨hp.1.ne_one, hm⟩) % n ≠ 0) :
    Irrational x := by
  rcases Nat.eq_zero_or_pos n with (rfl | hnpos)
  · rw [eq_comm, pow_zero, ← Int.cast_one, Int.cast_inj] at hxr
    simpa [hxr,
      multiplicity.one_right (mt isUnit_iff_dvd_one.1 (mt Int.coe_nat_dvd.1 hp.1.not_dvd_one)),
      Nat.zero_mod] using hv
  refine' irrational_nrt_of_notint_nrt _ _ hxr _ hnpos
  rintro ⟨y, rfl⟩
  rw [← Int.cast_pow, Int.cast_inj] at hxr; subst m
  have : y ≠ 0 := by rintro rfl; rw [zero_pow hnpos] at hm; exact hm rfl
  erw [multiplicity.pow' (Nat.prime_iff_prime_int.1 hp.1) (finite_int_iff.2 ⟨hp.1.ne_one, this⟩),
    Nat.mul_mod_right] at hv
  exact hv rfl
#align irrational_nrt_of_n_not_dvd_multiplicity irrational_nrt_of_n_not_dvd_multiplicity

/- warning: irrational_sqrt_of_multiplicity_odd -> irrational_sqrt_of_multiplicity_odd is a dubious translation:
lean 3 declaration is
  forall (m : Int) (hm : LT.lt.{0} Int Int.hasLt (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) m) (p : Nat) [hp : Fact (Nat.Prime p)], (Eq.{1} Nat (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (Part.get.{0} Nat (multiplicity.{0} Int Int.monoid (fun (a : Int) (b : Int) => Int.decidableDvd a b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) m) (Iff.mpr (multiplicity.Finite.{0} Int Int.monoid ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) m) (And (Ne.{1} Nat (Int.natAbs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))) (multiplicity.finite_int_iff ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) m) (And.intro (Ne.{1} Nat (Int.natAbs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Nat.Prime.ne_one p (Fact.out (Nat.Prime p) hp)) (Ne.symm.{1} Int (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) m (ne_of_lt.{0} Int (PartialOrder.toPreorder.{0} Int (OrderedAddCommGroup.toPartialOrder.{0} Int (StrictOrderedRing.toOrderedAddCommGroup.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) m hm))))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> (Irrational (Real.sqrt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m)))
but is expected to have type
  forall (m : Int) (hm : LT.lt.{0} Int Int.instLTInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) m) (p : Nat) [hp : Fact (Nat.Prime p)], (Eq.{1} Nat (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (Part.get.{0} Nat (multiplicity.{0} Int Int.instMonoidInt (fun (a : Int) (b : Int) => Int.decidableDvd a b) (Nat.cast.{0} Int instNatCastInt p) m) (Iff.mpr (multiplicity.Finite.{0} Int Int.instMonoidInt (Nat.cast.{0} Int instNatCastInt p) m) (And (Ne.{1} Nat (Int.natAbs (Nat.cast.{0} Int instNatCastInt p)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))) (multiplicity.finite_int_iff (Nat.cast.{0} Int instNatCastInt p) m) (And.intro (Ne.{1} Nat (Int.natAbs (Nat.cast.{0} Int instNatCastInt p)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Nat.Prime.ne_one p (Fact.out (Nat.Prime p) hp)) (Ne.symm.{1} Int (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) m (ne_of_lt.{0} Int (PartialOrder.toPreorder.{0} Int (StrictOrderedRing.toPartialOrder.{0} Int (LinearOrderedRing.toStrictOrderedRing.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) m hm))))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> (Irrational (Real.sqrt (Int.cast.{0} Real Real.intCast m)))
Case conversion may be inaccurate. Consider using '#align irrational_sqrt_of_multiplicity_odd irrational_sqrt_of_multiplicity_oddₓ'. -/
theorem irrational_sqrt_of_multiplicity_odd (m : ℤ) (hm : 0 < m) (p : ℕ) [hp : Fact p.Prime]
    (Hpv :
      (multiplicity (p : ℤ) m).get (finite_int_iff.2 ⟨hp.1.ne_one, (ne_of_lt hm).symm⟩) % 2 = 1) :
    Irrational (sqrt m) :=
  @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (Ne.symm (ne_of_lt hm)) p hp
    (sq_sqrt (Int.cast_nonneg.2 <| le_of_lt hm)) (by rw [Hpv] <;> exact one_ne_zero)
#align irrational_sqrt_of_multiplicity_odd irrational_sqrt_of_multiplicity_odd

/- warning: nat.prime.irrational_sqrt -> Nat.Prime.irrational_sqrt is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, (Nat.Prime p) -> (Irrational (Real.sqrt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p)))
but is expected to have type
  forall {p : Nat}, (Nat.Prime p) -> (Irrational (Real.sqrt (Nat.cast.{0} Real Real.natCast p)))
Case conversion may be inaccurate. Consider using '#align nat.prime.irrational_sqrt Nat.Prime.irrational_sqrtₓ'. -/
theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (sqrt p) :=
  @irrational_sqrt_of_multiplicity_odd p (Int.coe_nat_pos.2 hp.Pos) p ⟨hp⟩ <| by
    simp [multiplicity_self (mt isUnit_iff_dvd_one.1 (mt Int.coe_nat_dvd.1 hp.not_dvd_one) : _)] <;>
      rfl
#align nat.prime.irrational_sqrt Nat.Prime.irrational_sqrt

/- warning: irrational_sqrt_two -> irrational_sqrt_two is a dubious translation:
lean 3 declaration is
  Irrational (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  Irrational (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align irrational_sqrt_two irrational_sqrt_twoₓ'. -/
/-- **Irrationality of the Square Root of 2** -/
theorem irrational_sqrt_two : Irrational (sqrt 2) := by simpa using nat.prime_two.irrational_sqrt
#align irrational_sqrt_two irrational_sqrt_two

/- warning: irrational_sqrt_rat_iff -> irrational_sqrt_rat_iff is a dubious translation:
lean 3 declaration is
  forall (q : Rat), Iff (Irrational (Real.sqrt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))) (And (Ne.{1} Rat (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) (Rat.sqrt q) (Rat.sqrt q)) q) (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q))
but is expected to have type
  forall (q : Rat), Iff (Irrational (Real.sqrt (Rat.cast.{0} Real Real.ratCast q))) (And (Ne.{1} Rat (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) (Rat.sqrt q) (Rat.sqrt q)) q) (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q))
Case conversion may be inaccurate. Consider using '#align irrational_sqrt_rat_iff irrational_sqrt_rat_iffₓ'. -/
theorem irrational_sqrt_rat_iff (q : ℚ) :
    Irrational (sqrt q) ↔ Rat.sqrt q * Rat.sqrt q ≠ q ∧ 0 ≤ q :=
  if H1 : Rat.sqrt q * Rat.sqrt q = q then
    iff_of_false
      (not_not_intro
        ⟨Rat.sqrt q, by
          rw [← H1, cast_mul, sqrt_mul_self (cast_nonneg.2 <| Rat.sqrt_nonneg q), sqrt_eq,
            abs_of_nonneg (Rat.sqrt_nonneg q)]⟩)
      fun h => h.1 H1
  else
    if H2 : 0 ≤ q then
      iff_of_true
        (fun ⟨r, hr⟩ =>
          H1 <|
            (exists_mul_self _).1
              ⟨r, by
                rwa [eq_comm, sqrt_eq_iff_mul_self_eq (cast_nonneg.2 H2), ← cast_mul,
                      Rat.cast_inj] at hr <;>
                    rw [← hr] <;>
                  exact Real.sqrt_nonneg _⟩)
        ⟨H1, H2⟩
    else
      iff_of_false
        (not_not_intro
          ⟨0, by
            rw [cast_zero] <;>
              exact (sqrt_eq_zero_of_nonpos (Rat.cast_nonpos.2 <| le_of_not_le H2)).symm⟩)
        fun h => H2 h.2
#align irrational_sqrt_rat_iff irrational_sqrt_rat_iff

instance (q : ℚ) : Decidable (Irrational (sqrt q)) :=
  decidable_of_iff' _ (irrational_sqrt_rat_iff q)

/-!
### Dot-style operations on `irrational`

#### Coercion of a rational/integer/natural number is not irrational
-/


namespace Irrational

variable {x : ℝ}

/-!
#### Irrational number is not equal to a rational/integer/natural number
-/


/- warning: irrational.ne_rat -> Irrational.ne_rat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (q : Rat), Ne.{1} Real x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (q : Rat), Ne.{1} Real x (Rat.cast.{0} Real Real.ratCast q))
Case conversion may be inaccurate. Consider using '#align irrational.ne_rat Irrational.ne_ratₓ'. -/
theorem ne_rat (h : Irrational x) (q : ℚ) : x ≠ q := fun hq => h ⟨q, hq.symm⟩
#align irrational.ne_rat Irrational.ne_rat

/- warning: irrational.ne_int -> Irrational.ne_int is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (m : Int), Ne.{1} Real x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (m : Int), Ne.{1} Real x (Int.cast.{0} Real Real.intCast m))
Case conversion may be inaccurate. Consider using '#align irrational.ne_int Irrational.ne_intₓ'. -/
theorem ne_int (h : Irrational x) (m : ℤ) : x ≠ m := by rw [← Rat.cast_coe_int]; exact h.ne_rat _
#align irrational.ne_int Irrational.ne_int

/- warning: irrational.ne_nat -> Irrational.ne_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (m : Nat), Ne.{1} Real x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (m : Nat), Ne.{1} Real x (Nat.cast.{0} Real Real.natCast m))
Case conversion may be inaccurate. Consider using '#align irrational.ne_nat Irrational.ne_natₓ'. -/
theorem ne_nat (h : Irrational x) (m : ℕ) : x ≠ m :=
  h.ne_int m
#align irrational.ne_nat Irrational.ne_nat

/- warning: irrational.ne_zero -> Irrational.ne_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align irrational.ne_zero Irrational.ne_zeroₓ'. -/
theorem ne_zero (h : Irrational x) : x ≠ 0 := by exact_mod_cast h.ne_nat 0
#align irrational.ne_zero Irrational.ne_zero

/- warning: irrational.ne_one -> Irrational.ne_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align irrational.ne_one Irrational.ne_oneₓ'. -/
theorem ne_one (h : Irrational x) : x ≠ 1 := by simpa only [Nat.cast_one] using h.ne_nat 1
#align irrational.ne_one Irrational.ne_one

end Irrational

/- warning: rat.not_irrational -> Rat.not_irrational is a dubious translation:
lean 3 declaration is
  forall (q : Rat), Not (Irrational ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))
but is expected to have type
  forall (q : Rat), Not (Irrational (Rat.cast.{0} Real Real.ratCast q))
Case conversion may be inaccurate. Consider using '#align rat.not_irrational Rat.not_irrationalₓ'. -/
@[simp]
theorem Rat.not_irrational (q : ℚ) : ¬Irrational q := fun h => h ⟨q, rfl⟩
#align rat.not_irrational Rat.not_irrational

/- warning: int.not_irrational -> Int.not_irrational is a dubious translation:
lean 3 declaration is
  forall (m : Int), Not (Irrational ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))
but is expected to have type
  forall (m : Int), Not (Irrational (Int.cast.{0} Real Real.intCast m))
Case conversion may be inaccurate. Consider using '#align int.not_irrational Int.not_irrationalₓ'. -/
@[simp]
theorem Int.not_irrational (m : ℤ) : ¬Irrational m := fun h => h.ne_int m rfl
#align int.not_irrational Int.not_irrational

/- warning: nat.not_irrational -> Nat.not_irrational is a dubious translation:
lean 3 declaration is
  forall (m : Nat), Not (Irrational ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m))
but is expected to have type
  forall (m : Nat), Not (Irrational (Nat.cast.{0} Real Real.natCast m))
Case conversion may be inaccurate. Consider using '#align nat.not_irrational Nat.not_irrationalₓ'. -/
@[simp]
theorem Nat.not_irrational (m : ℕ) : ¬Irrational m := fun h => h.ne_nat m rfl
#align nat.not_irrational Nat.not_irrational

namespace Irrational

variable (q : ℚ) {x y : ℝ}

/-!
#### Addition of rational/integer/natural numbers
-/


/- warning: irrational.add_cases -> Irrational.add_cases is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x y)) -> (Or (Irrational x) (Irrational y))
but is expected to have type
  forall {x : Real} {y : Real}, (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x y)) -> (Or (Irrational x) (Irrational y))
Case conversion may be inaccurate. Consider using '#align irrational.add_cases Irrational.add_casesₓ'. -/
/-- If `x + y` is irrational, then at least one of `x` and `y` is irrational. -/
theorem add_cases : Irrational (x + y) → Irrational x ∨ Irrational y :=
  by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx + ry, cast_add rx ry⟩
#align irrational.add_cases Irrational.add_cases

/- warning: irrational.of_rat_add -> Irrational.of_rat_add is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x)) -> (Irrational x)
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Rat.cast.{0} Real Real.ratCast q) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_rat_add Irrational.of_rat_addₓ'. -/
theorem of_rat_add (h : Irrational (q + x)) : Irrational x :=
  h.addCases.resolve_left q.not_irrational
#align irrational.of_rat_add Irrational.of_rat_add

/- warning: irrational.rat_add -> Irrational.rat_add is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational x) -> (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x))
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational x) -> (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Rat.cast.{0} Real Real.ratCast q) x))
Case conversion may be inaccurate. Consider using '#align irrational.rat_add Irrational.rat_addₓ'. -/
theorem rat_add (h : Irrational x) : Irrational (q + x) :=
  of_rat_add (-q) <| by rwa [cast_neg, neg_add_cancel_left]
#align irrational.rat_add Irrational.rat_add

/- warning: irrational.of_add_rat -> Irrational.of_add_rat is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))) -> (Irrational x)
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (Rat.cast.{0} Real Real.ratCast q))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_add_rat Irrational.of_add_ratₓ'. -/
theorem of_add_rat : Irrational (x + q) → Irrational x :=
  add_comm (↑q) x ▸ of_rat_add q
#align irrational.of_add_rat Irrational.of_add_rat

/- warning: irrational.add_rat -> Irrational.add_rat is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational x) -> (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q)))
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational x) -> (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (Rat.cast.{0} Real Real.ratCast q)))
Case conversion may be inaccurate. Consider using '#align irrational.add_rat Irrational.add_ratₓ'. -/
theorem add_rat (h : Irrational x) : Irrational (x + q) :=
  add_comm (↑q) x ▸ h.rat_add q
#align irrational.add_rat Irrational.add_rat

/- warning: irrational.of_int_add -> Irrational.of_int_add is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Int), (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x)) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Int), (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Int.cast.{0} Real Real.intCast m) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_int_add Irrational.of_int_addₓ'. -/
theorem of_int_add (m : ℤ) (h : Irrational (m + x)) : Irrational x := by rw [← cast_coe_int] at h;
  exact h.of_rat_add m
#align irrational.of_int_add Irrational.of_int_add

/- warning: irrational.of_add_int -> Irrational.of_add_int is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Int), (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Int), (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (Int.cast.{0} Real Real.intCast m))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_add_int Irrational.of_add_intₓ'. -/
theorem of_add_int (m : ℤ) (h : Irrational (x + m)) : Irrational x :=
  of_int_add m <| add_comm x m ▸ h
#align irrational.of_add_int Irrational.of_add_int

/- warning: irrational.int_add -> Irrational.int_add is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (m : Int), Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (m : Int), Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Int.cast.{0} Real Real.intCast m) x))
Case conversion may be inaccurate. Consider using '#align irrational.int_add Irrational.int_addₓ'. -/
theorem int_add (h : Irrational x) (m : ℤ) : Irrational (m + x) := by rw [← cast_coe_int];
  exact h.rat_add m
#align irrational.int_add Irrational.int_add

/- warning: irrational.add_int -> Irrational.add_int is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (m : Int), Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m)))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (m : Int), Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (Int.cast.{0} Real Real.intCast m)))
Case conversion may be inaccurate. Consider using '#align irrational.add_int Irrational.add_intₓ'. -/
theorem add_int (h : Irrational x) (m : ℤ) : Irrational (x + m) :=
  add_comm (↑m) x ▸ h.int_add m
#align irrational.add_int Irrational.add_int

/- warning: irrational.of_nat_add -> Irrational.of_nat_add is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Nat), (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) x)) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Nat), (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast m) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_nat_add Irrational.of_nat_addₓ'. -/
theorem of_nat_add (m : ℕ) (h : Irrational (m + x)) : Irrational x :=
  h.of_int_add m
#align irrational.of_nat_add Irrational.of_nat_add

/- warning: irrational.of_add_nat -> Irrational.of_add_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Nat), (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m))) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Nat), (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (Nat.cast.{0} Real Real.natCast m))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_add_nat Irrational.of_add_natₓ'. -/
theorem of_add_nat (m : ℕ) (h : Irrational (x + m)) : Irrational x :=
  h.of_add_int m
#align irrational.of_add_nat Irrational.of_add_nat

/- warning: irrational.nat_add -> Irrational.nat_add is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (m : Nat), Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) x))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (m : Nat), Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast m) x))
Case conversion may be inaccurate. Consider using '#align irrational.nat_add Irrational.nat_addₓ'. -/
theorem nat_add (h : Irrational x) (m : ℕ) : Irrational (m + x) :=
  h.int_add m
#align irrational.nat_add Irrational.nat_add

/- warning: irrational.add_nat -> Irrational.add_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (m : Nat), Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m)))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (m : Nat), Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (Nat.cast.{0} Real Real.natCast m)))
Case conversion may be inaccurate. Consider using '#align irrational.add_nat Irrational.add_natₓ'. -/
theorem add_nat (h : Irrational x) (m : ℕ) : Irrational (x + m) :=
  h.add_int m
#align irrational.add_nat Irrational.add_nat

/-!
#### Negation
-/


/- warning: irrational.of_neg -> Irrational.of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational (Neg.neg.{0} Real Real.hasNeg x)) -> (Irrational x)
but is expected to have type
  forall {x : Real}, (Irrational (Neg.neg.{0} Real Real.instNegReal x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_neg Irrational.of_negₓ'. -/
theorem of_neg (h : Irrational (-x)) : Irrational x := fun ⟨q, hx⟩ => h ⟨-q, by rw [cast_neg, hx]⟩
#align irrational.of_neg Irrational.of_neg

/- warning: irrational.neg -> Irrational.neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (Irrational (Neg.neg.{0} Real Real.hasNeg x))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (Irrational (Neg.neg.{0} Real Real.instNegReal x))
Case conversion may be inaccurate. Consider using '#align irrational.neg Irrational.negₓ'. -/
protected theorem neg (h : Irrational x) : Irrational (-x) :=
  of_neg <| by rwa [neg_neg]
#align irrational.neg Irrational.neg

/-!
#### Subtraction of rational/integer/natural numbers
-/


/- warning: irrational.sub_rat -> Irrational.sub_rat is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational x) -> (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q)))
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational x) -> (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (Rat.cast.{0} Real Real.ratCast q)))
Case conversion may be inaccurate. Consider using '#align irrational.sub_rat Irrational.sub_ratₓ'. -/
theorem sub_rat (h : Irrational x) : Irrational (x - q) := by
  simpa only [sub_eq_add_neg, cast_neg] using h.add_rat (-q)
#align irrational.sub_rat Irrational.sub_rat

/- warning: irrational.rat_sub -> Irrational.rat_sub is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational x) -> (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x))
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational x) -> (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Rat.cast.{0} Real Real.ratCast q) x))
Case conversion may be inaccurate. Consider using '#align irrational.rat_sub Irrational.rat_subₓ'. -/
theorem rat_sub (h : Irrational x) : Irrational (q - x) := by
  simpa only [sub_eq_add_neg] using h.neg.rat_add q
#align irrational.rat_sub Irrational.rat_sub

/- warning: irrational.of_sub_rat -> Irrational.of_sub_rat is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))) -> (Irrational x)
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (Rat.cast.{0} Real Real.ratCast q))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_sub_rat Irrational.of_sub_ratₓ'. -/
theorem of_sub_rat (h : Irrational (x - q)) : Irrational x :=
  of_add_rat (-q) <| by simpa only [cast_neg, sub_eq_add_neg] using h
#align irrational.of_sub_rat Irrational.of_sub_rat

/- warning: irrational.of_rat_sub -> Irrational.of_rat_sub is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x)) -> (Irrational x)
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Rat.cast.{0} Real Real.ratCast q) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_rat_sub Irrational.of_rat_subₓ'. -/
theorem of_rat_sub (h : Irrational (q - x)) : Irrational x :=
  of_neg (of_rat_add q (by simpa only [sub_eq_add_neg] using h))
#align irrational.of_rat_sub Irrational.of_rat_sub

/- warning: irrational.sub_int -> Irrational.sub_int is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (m : Int), Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m)))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (m : Int), Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (Int.cast.{0} Real Real.intCast m)))
Case conversion may be inaccurate. Consider using '#align irrational.sub_int Irrational.sub_intₓ'. -/
theorem sub_int (h : Irrational x) (m : ℤ) : Irrational (x - m) := by
  simpa only [Rat.cast_coe_int] using h.sub_rat m
#align irrational.sub_int Irrational.sub_int

/- warning: irrational.int_sub -> Irrational.int_sub is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (m : Int), Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (m : Int), Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Int.cast.{0} Real Real.intCast m) x))
Case conversion may be inaccurate. Consider using '#align irrational.int_sub Irrational.int_subₓ'. -/
theorem int_sub (h : Irrational x) (m : ℤ) : Irrational (m - x) := by
  simpa only [Rat.cast_coe_int] using h.rat_sub m
#align irrational.int_sub Irrational.int_sub

/- warning: irrational.of_sub_int -> Irrational.of_sub_int is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Int), (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Int), (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (Int.cast.{0} Real Real.intCast m))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_sub_int Irrational.of_sub_intₓ'. -/
theorem of_sub_int (m : ℤ) (h : Irrational (x - m)) : Irrational x :=
  of_sub_rat m <| by rwa [Rat.cast_coe_int]
#align irrational.of_sub_int Irrational.of_sub_int

/- warning: irrational.of_int_sub -> Irrational.of_int_sub is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Int), (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x)) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Int), (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Int.cast.{0} Real Real.intCast m) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_int_sub Irrational.of_int_subₓ'. -/
theorem of_int_sub (m : ℤ) (h : Irrational (m - x)) : Irrational x :=
  of_rat_sub m <| by rwa [Rat.cast_coe_int]
#align irrational.of_int_sub Irrational.of_int_sub

/- warning: irrational.sub_nat -> Irrational.sub_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (m : Nat), Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m)))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (m : Nat), Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (Nat.cast.{0} Real Real.natCast m)))
Case conversion may be inaccurate. Consider using '#align irrational.sub_nat Irrational.sub_natₓ'. -/
theorem sub_nat (h : Irrational x) (m : ℕ) : Irrational (x - m) :=
  h.sub_int m
#align irrational.sub_nat Irrational.sub_nat

/- warning: irrational.nat_sub -> Irrational.nat_sub is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall (m : Nat), Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) x))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall (m : Nat), Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Nat.cast.{0} Real Real.natCast m) x))
Case conversion may be inaccurate. Consider using '#align irrational.nat_sub Irrational.nat_subₓ'. -/
theorem nat_sub (h : Irrational x) (m : ℕ) : Irrational (m - x) :=
  h.int_sub m
#align irrational.nat_sub Irrational.nat_sub

/- warning: irrational.of_sub_nat -> Irrational.of_sub_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Nat), (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m))) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Nat), (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (Nat.cast.{0} Real Real.natCast m))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_sub_nat Irrational.of_sub_natₓ'. -/
theorem of_sub_nat (m : ℕ) (h : Irrational (x - m)) : Irrational x :=
  h.of_sub_int m
#align irrational.of_sub_nat Irrational.of_sub_nat

/- warning: irrational.of_nat_sub -> Irrational.of_nat_sub is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Nat), (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) x)) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Nat), (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Nat.cast.{0} Real Real.natCast m) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_nat_sub Irrational.of_nat_subₓ'. -/
theorem of_nat_sub (m : ℕ) (h : Irrational (m - x)) : Irrational x :=
  h.of_int_sub m
#align irrational.of_nat_sub Irrational.of_nat_sub

/-!
#### Multiplication by rational numbers
-/


/- warning: irrational.mul_cases -> Irrational.mul_cases is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y)) -> (Or (Irrational x) (Irrational y))
but is expected to have type
  forall {x : Real} {y : Real}, (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y)) -> (Or (Irrational x) (Irrational y))
Case conversion may be inaccurate. Consider using '#align irrational.mul_cases Irrational.mul_casesₓ'. -/
theorem mul_cases : Irrational (x * y) → Irrational x ∨ Irrational y :=
  by
  delta Irrational
  contrapose!
  rintro ⟨⟨rx, rfl⟩, ⟨ry, rfl⟩⟩
  exact ⟨rx * ry, cast_mul rx ry⟩
#align irrational.mul_cases Irrational.mul_cases

/- warning: irrational.of_mul_rat -> Irrational.of_mul_rat is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))) -> (Irrational x)
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x (Rat.cast.{0} Real Real.ratCast q))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_mul_rat Irrational.of_mul_ratₓ'. -/
theorem of_mul_rat (h : Irrational (x * q)) : Irrational x :=
  h.mul_cases.resolve_right q.not_irrational
#align irrational.of_mul_rat Irrational.of_mul_rat

/- warning: irrational.mul_rat -> Irrational.mul_rat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x (Rat.cast.{0} Real Real.ratCast q))))
Case conversion may be inaccurate. Consider using '#align irrational.mul_rat Irrational.mul_ratₓ'. -/
theorem mul_rat (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (x * q) :=
  of_mul_rat q⁻¹ <| by rwa [mul_assoc, ← cast_mul, mul_inv_cancel hq, cast_one, mul_one]
#align irrational.mul_rat Irrational.mul_rat

/- warning: irrational.of_rat_mul -> Irrational.of_rat_mul is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x)) -> (Irrational x)
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Rat.cast.{0} Real Real.ratCast q) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_rat_mul Irrational.of_rat_mulₓ'. -/
theorem of_rat_mul : Irrational (q * x) → Irrational x :=
  mul_comm x q ▸ of_mul_rat q
#align irrational.of_rat_mul Irrational.of_rat_mul

/- warning: irrational.rat_mul -> Irrational.rat_mul is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x)))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Rat.cast.{0} Real Real.ratCast q) x)))
Case conversion may be inaccurate. Consider using '#align irrational.rat_mul Irrational.rat_mulₓ'. -/
theorem rat_mul (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q * x) :=
  mul_comm x q ▸ h.mul_rat hq
#align irrational.rat_mul Irrational.rat_mul

/- warning: irrational.of_mul_int -> Irrational.of_mul_int is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Int), (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Int), (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x (Int.cast.{0} Real Real.intCast m))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_mul_int Irrational.of_mul_intₓ'. -/
theorem of_mul_int (m : ℤ) (h : Irrational (x * m)) : Irrational x :=
  of_mul_rat m <| by rwa [cast_coe_int]
#align irrational.of_mul_int Irrational.of_mul_int

/- warning: irrational.of_int_mul -> Irrational.of_int_mul is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Int), (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x)) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Int), (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Int.cast.{0} Real Real.intCast m) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_int_mul Irrational.of_int_mulₓ'. -/
theorem of_int_mul (m : ℤ) (h : Irrational (m * x)) : Irrational x :=
  of_rat_mul m <| by rwa [cast_coe_int]
#align irrational.of_int_mul Irrational.of_int_mul

/- warning: irrational.mul_int -> Irrational.mul_int is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {m : Int}, (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {m : Int}, (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x (Int.cast.{0} Real Real.intCast m))))
Case conversion may be inaccurate. Consider using '#align irrational.mul_int Irrational.mul_intₓ'. -/
theorem mul_int (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (x * m) := by
  rw [← cast_coe_int]; refine' h.mul_rat _; rwa [Int.cast_ne_zero]
#align irrational.mul_int Irrational.mul_int

/- warning: irrational.int_mul -> Irrational.int_mul is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {m : Int}, (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x)))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {m : Int}, (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Int.cast.{0} Real Real.intCast m) x)))
Case conversion may be inaccurate. Consider using '#align irrational.int_mul Irrational.int_mulₓ'. -/
theorem int_mul (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (m * x) :=
  mul_comm x m ▸ h.mul_int hm
#align irrational.int_mul Irrational.int_mul

/- warning: irrational.of_mul_nat -> Irrational.of_mul_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Nat), (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m))) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Nat), (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x (Nat.cast.{0} Real Real.natCast m))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_mul_nat Irrational.of_mul_natₓ'. -/
theorem of_mul_nat (m : ℕ) (h : Irrational (x * m)) : Irrational x :=
  h.of_mul_int m
#align irrational.of_mul_nat Irrational.of_mul_nat

/- warning: irrational.of_nat_mul -> Irrational.of_nat_mul is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Nat), (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) x)) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Nat), (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast m) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_nat_mul Irrational.of_nat_mulₓ'. -/
theorem of_nat_mul (m : ℕ) (h : Irrational (m * x)) : Irrational x :=
  h.of_int_mul m
#align irrational.of_nat_mul Irrational.of_nat_mul

/- warning: irrational.mul_nat -> Irrational.mul_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {m : Nat}, (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {m : Nat}, (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x (Nat.cast.{0} Real Real.natCast m))))
Case conversion may be inaccurate. Consider using '#align irrational.mul_nat Irrational.mul_natₓ'. -/
theorem mul_nat (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (x * m) :=
  h.mul_int <| Int.coe_nat_ne_zero.2 hm
#align irrational.mul_nat Irrational.mul_nat

/- warning: irrational.nat_mul -> Irrational.nat_mul is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {m : Nat}, (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) x)))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {m : Nat}, (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast m) x)))
Case conversion may be inaccurate. Consider using '#align irrational.nat_mul Irrational.nat_mulₓ'. -/
theorem nat_mul (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (m * x) :=
  h.int_mul <| Int.coe_nat_ne_zero.2 hm
#align irrational.nat_mul Irrational.nat_mul

/-!
#### Inverse
-/


/- warning: irrational.of_inv -> Irrational.of_inv is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational (Inv.inv.{0} Real Real.hasInv x)) -> (Irrational x)
but is expected to have type
  forall {x : Real}, (Irrational (Inv.inv.{0} Real Real.instInvReal x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_inv Irrational.of_invₓ'. -/
theorem of_inv (h : Irrational x⁻¹) : Irrational x := fun ⟨q, hq⟩ => h <| hq ▸ ⟨q⁻¹, q.cast_inv⟩
#align irrational.of_inv Irrational.of_inv

/- warning: irrational.inv -> Irrational.inv is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (Irrational (Inv.inv.{0} Real Real.hasInv x))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (Irrational (Inv.inv.{0} Real Real.instInvReal x))
Case conversion may be inaccurate. Consider using '#align irrational.inv Irrational.invₓ'. -/
protected theorem inv (h : Irrational x) : Irrational x⁻¹ :=
  of_inv <| by rwa [inv_inv]
#align irrational.inv Irrational.inv

/-!
#### Division
-/


/- warning: irrational.div_cases -> Irrational.div_cases is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x y)) -> (Or (Irrational x) (Irrational y))
but is expected to have type
  forall {x : Real} {y : Real}, (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x y)) -> (Or (Irrational x) (Irrational y))
Case conversion may be inaccurate. Consider using '#align irrational.div_cases Irrational.div_casesₓ'. -/
theorem div_cases (h : Irrational (x / y)) : Irrational x ∨ Irrational y :=
  h.mul_cases.imp id of_inv
#align irrational.div_cases Irrational.div_cases

/- warning: irrational.of_rat_div -> Irrational.of_rat_div is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x)) -> (Irrational x)
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Rat.cast.{0} Real Real.ratCast q) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_rat_div Irrational.of_rat_divₓ'. -/
theorem of_rat_div (h : Irrational (q / x)) : Irrational x :=
  (h.ofRat_mul q).of_inv
#align irrational.of_rat_div Irrational.of_rat_div

/- warning: irrational.of_div_rat -> Irrational.of_div_rat is a dubious translation:
lean 3 declaration is
  forall (q : Rat) {x : Real}, (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))) -> (Irrational x)
but is expected to have type
  forall (q : Rat) {x : Real}, (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Rat.cast.{0} Real Real.ratCast q))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_div_rat Irrational.of_div_ratₓ'. -/
theorem of_div_rat (h : Irrational (x / q)) : Irrational x :=
  h.div_cases.resolve_right q.not_irrational
#align irrational.of_div_rat Irrational.of_div_rat

/- warning: irrational.rat_div -> Irrational.rat_div is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x)))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Rat.cast.{0} Real Real.ratCast q) x)))
Case conversion may be inaccurate. Consider using '#align irrational.rat_div Irrational.rat_divₓ'. -/
theorem rat_div (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q / x) :=
  h.inv.rat_mul hq
#align irrational.rat_div Irrational.rat_div

/- warning: irrational.div_rat -> Irrational.div_rat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Rat.cast.{0} Real Real.ratCast q))))
Case conversion may be inaccurate. Consider using '#align irrational.div_rat Irrational.div_ratₓ'. -/
theorem div_rat (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (x / q) := by
  rw [div_eq_mul_inv, ← cast_inv]; exact h.mul_rat (inv_ne_zero hq)
#align irrational.div_rat Irrational.div_rat

/- warning: irrational.of_int_div -> Irrational.of_int_div is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Int), (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x)) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Int), (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Int.cast.{0} Real Real.intCast m) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_int_div Irrational.of_int_divₓ'. -/
theorem of_int_div (m : ℤ) (h : Irrational (m / x)) : Irrational x :=
  h.div_cases.resolve_left m.not_irrational
#align irrational.of_int_div Irrational.of_int_div

/- warning: irrational.of_div_int -> Irrational.of_div_int is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Int), (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Int), (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Int.cast.{0} Real Real.intCast m))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_div_int Irrational.of_div_intₓ'. -/
theorem of_div_int (m : ℤ) (h : Irrational (x / m)) : Irrational x :=
  h.div_cases.resolve_right m.not_irrational
#align irrational.of_div_int Irrational.of_div_int

/- warning: irrational.int_div -> Irrational.int_div is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {m : Int}, (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x)))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {m : Int}, (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Int.cast.{0} Real Real.intCast m) x)))
Case conversion may be inaccurate. Consider using '#align irrational.int_div Irrational.int_divₓ'. -/
theorem int_div (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (m / x) :=
  h.inv.int_mul hm
#align irrational.int_div Irrational.int_div

/- warning: irrational.div_int -> Irrational.div_int is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {m : Int}, (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {m : Int}, (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Int.cast.{0} Real Real.intCast m))))
Case conversion may be inaccurate. Consider using '#align irrational.div_int Irrational.div_intₓ'. -/
theorem div_int (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (x / m) := by
  rw [← cast_coe_int]; refine' h.div_rat _; rwa [Int.cast_ne_zero]
#align irrational.div_int Irrational.div_int

/- warning: irrational.of_nat_div -> Irrational.of_nat_div is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Nat), (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) x)) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Nat), (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Nat.cast.{0} Real Real.natCast m) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_nat_div Irrational.of_nat_divₓ'. -/
theorem of_nat_div (m : ℕ) (h : Irrational (m / x)) : Irrational x :=
  h.of_int_div m
#align irrational.of_nat_div Irrational.of_nat_div

/- warning: irrational.of_div_nat -> Irrational.of_div_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real} (m : Nat), (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m))) -> (Irrational x)
but is expected to have type
  forall {x : Real} (m : Nat), (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Nat.cast.{0} Real Real.natCast m))) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_div_nat Irrational.of_div_natₓ'. -/
theorem of_div_nat (m : ℕ) (h : Irrational (x / m)) : Irrational x :=
  h.of_div_int m
#align irrational.of_div_nat Irrational.of_div_nat

/- warning: irrational.nat_div -> Irrational.nat_div is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {m : Nat}, (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m) x)))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {m : Nat}, (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Nat.cast.{0} Real Real.natCast m) x)))
Case conversion may be inaccurate. Consider using '#align irrational.nat_div Irrational.nat_divₓ'. -/
theorem nat_div (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (m / x) :=
  h.inv.nat_mul hm
#align irrational.nat_div Irrational.nat_div

/- warning: irrational.div_nat -> Irrational.div_nat is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational x) -> (forall {m : Nat}, (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) m))))
but is expected to have type
  forall {x : Real}, (Irrational x) -> (forall {m : Nat}, (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Nat.cast.{0} Real Real.natCast m))))
Case conversion may be inaccurate. Consider using '#align irrational.div_nat Irrational.div_natₓ'. -/
theorem div_nat (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (x / m) :=
  h.div_int <| by rwa [Int.coe_nat_ne_zero]
#align irrational.div_nat Irrational.div_nat

/- warning: irrational.of_one_div -> Irrational.of_one_div is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x)) -> (Irrational x)
but is expected to have type
  forall {x : Real}, (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_one_div Irrational.of_one_divₓ'. -/
theorem of_one_div (h : Irrational (1 / x)) : Irrational x :=
  of_rat_div 1 <| by rwa [cast_one]
#align irrational.of_one_div Irrational.of_one_div

/-!
#### Natural and integerl power
-/


/- warning: irrational.of_mul_self -> Irrational.of_mul_self is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x x)) -> (Irrational x)
but is expected to have type
  forall {x : Real}, (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x x)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_mul_self Irrational.of_mul_selfₓ'. -/
theorem of_mul_self (h : Irrational (x * x)) : Irrational x :=
  h.mul_cases.elim id id
#align irrational.of_mul_self Irrational.of_mul_self

/- warning: irrational.of_pow -> Irrational.of_pow is a dubious translation:
lean 3 declaration is
  forall {x : Real} (n : Nat), (Irrational (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n)) -> (Irrational x)
but is expected to have type
  forall {x : Real} (n : Nat), (Irrational (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n)) -> (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational.of_pow Irrational.of_powₓ'. -/
theorem of_pow : ∀ n : ℕ, Irrational (x ^ n) → Irrational x
  | 0 => fun h => by rw [pow_zero] at h; exact (h ⟨1, cast_one⟩).elim
  | n + 1 => fun h => by rw [pow_succ] at h; exact h.mul_cases.elim id (of_pow n)
#align irrational.of_pow Irrational.of_pow

#print Irrational.of_zpow /-
theorem of_zpow : ∀ m : ℤ, Irrational (x ^ m) → Irrational x
  | (n : ℕ) => fun h => by rw [zpow_ofNat] at h; exact h.of_pow _
  | -[n+1] => fun h => by rw [zpow_negSucc] at h; exact h.of_inv.of_pow _
#align irrational.of_zpow Irrational.of_zpow
-/

end Irrational

section Polynomial

open Polynomial

open Polynomial

variable (x : ℝ) (p : ℤ[X])

/- warning: one_lt_nat_degree_of_irrational_root -> one_lt_natDegree_of_irrational_root is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align one_lt_nat_degree_of_irrational_root one_lt_natDegree_of_irrational_rootₓ'. -/
theorem one_lt_natDegree_of_irrational_root (hx : Irrational x) (p_nonzero : p ≠ 0)
    (x_is_root : aeval x p = 0) : 1 < p.natDegree :=
  by
  by_contra rid
  rcases exists_eq_X_add_C_of_nat_degree_le_one (not_lt.1 rid) with ⟨a, b, rfl⟩; clear rid
  have : (a : ℝ) * x = -b := by simpa [eq_neg_iff_add_eq_zero] using x_is_root
  rcases em (a = 0) with (rfl | ha)
  · obtain rfl : b = 0 := by simpa
    simpa using p_nonzero
  · rw [mul_comm, ← eq_div_iff_mul_eq, eq_comm] at this
    refine' hx ⟨-b / a, _⟩
    assumption_mod_cast; assumption_mod_cast
#align one_lt_nat_degree_of_irrational_root one_lt_natDegree_of_irrational_root

end Polynomial

section

variable {q : ℚ} {m : ℤ} {n : ℕ} {x : ℝ}

open Irrational

/-!
### Simplification lemmas about operations
-/


/- warning: irrational_rat_add_iff -> irrational_rat_add_iff is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x)) (Irrational x)
but is expected to have type
  forall {q : Rat} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Rat.cast.{0} Real Real.ratCast q) x)) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_rat_add_iff irrational_rat_add_iffₓ'. -/
@[simp]
theorem irrational_rat_add_iff : Irrational (q + x) ↔ Irrational x :=
  ⟨of_rat_add q, rat_add q⟩
#align irrational_rat_add_iff irrational_rat_add_iff

/- warning: irrational_int_add_iff -> irrational_int_add_iff is a dubious translation:
lean 3 declaration is
  forall {m : Int} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x)) (Irrational x)
but is expected to have type
  forall {m : Int} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Int.cast.{0} Real Real.intCast m) x)) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_int_add_iff irrational_int_add_iffₓ'. -/
@[simp]
theorem irrational_int_add_iff : Irrational (m + x) ↔ Irrational x :=
  ⟨of_int_add m, fun h => h.int_add m⟩
#align irrational_int_add_iff irrational_int_add_iff

/- warning: irrational_nat_add_iff -> irrational_nat_add_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) x)) (Irrational x)
but is expected to have type
  forall {n : Nat} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast n) x)) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_nat_add_iff irrational_nat_add_iffₓ'. -/
@[simp]
theorem irrational_nat_add_iff : Irrational (n + x) ↔ Irrational x :=
  ⟨of_nat_add n, fun h => h.natAdd n⟩
#align irrational_nat_add_iff irrational_nat_add_iff

/- warning: irrational_add_rat_iff -> irrational_add_rat_iff is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))) (Irrational x)
but is expected to have type
  forall {q : Rat} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (Rat.cast.{0} Real Real.ratCast q))) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_add_rat_iff irrational_add_rat_iffₓ'. -/
@[simp]
theorem irrational_add_rat_iff : Irrational (x + q) ↔ Irrational x :=
  ⟨of_add_rat q, add_rat q⟩
#align irrational_add_rat_iff irrational_add_rat_iff

/- warning: irrational_add_int_iff -> irrational_add_int_iff is a dubious translation:
lean 3 declaration is
  forall {m : Int} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))) (Irrational x)
but is expected to have type
  forall {m : Int} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (Int.cast.{0} Real Real.intCast m))) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_add_int_iff irrational_add_int_iffₓ'. -/
@[simp]
theorem irrational_add_int_iff : Irrational (x + m) ↔ Irrational x :=
  ⟨of_add_int m, fun h => h.add_int m⟩
#align irrational_add_int_iff irrational_add_int_iff

/- warning: irrational_add_nat_iff -> irrational_add_nat_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) (Irrational x)
but is expected to have type
  forall {n : Nat} {x : Real}, Iff (Irrational (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (Nat.cast.{0} Real Real.natCast n))) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_add_nat_iff irrational_add_nat_iffₓ'. -/
@[simp]
theorem irrational_add_nat_iff : Irrational (x + n) ↔ Irrational x :=
  ⟨of_add_nat n, fun h => h.addNat n⟩
#align irrational_add_nat_iff irrational_add_nat_iff

/- warning: irrational_rat_sub_iff -> irrational_rat_sub_iff is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x)) (Irrational x)
but is expected to have type
  forall {q : Rat} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Rat.cast.{0} Real Real.ratCast q) x)) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_rat_sub_iff irrational_rat_sub_iffₓ'. -/
@[simp]
theorem irrational_rat_sub_iff : Irrational (q - x) ↔ Irrational x :=
  ⟨of_rat_sub q, rat_sub q⟩
#align irrational_rat_sub_iff irrational_rat_sub_iff

/- warning: irrational_int_sub_iff -> irrational_int_sub_iff is a dubious translation:
lean 3 declaration is
  forall {m : Int} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x)) (Irrational x)
but is expected to have type
  forall {m : Int} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Int.cast.{0} Real Real.intCast m) x)) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_int_sub_iff irrational_int_sub_iffₓ'. -/
@[simp]
theorem irrational_int_sub_iff : Irrational (m - x) ↔ Irrational x :=
  ⟨of_int_sub m, fun h => h.int_sub m⟩
#align irrational_int_sub_iff irrational_int_sub_iff

/- warning: irrational_nat_sub_iff -> irrational_nat_sub_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) x)) (Irrational x)
but is expected to have type
  forall {n : Nat} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Nat.cast.{0} Real Real.natCast n) x)) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_nat_sub_iff irrational_nat_sub_iffₓ'. -/
@[simp]
theorem irrational_nat_sub_iff : Irrational (n - x) ↔ Irrational x :=
  ⟨of_nat_sub n, fun h => h.nat_sub n⟩
#align irrational_nat_sub_iff irrational_nat_sub_iff

/- warning: irrational_sub_rat_iff -> irrational_sub_rat_iff is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))) (Irrational x)
but is expected to have type
  forall {q : Rat} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (Rat.cast.{0} Real Real.ratCast q))) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_sub_rat_iff irrational_sub_rat_iffₓ'. -/
@[simp]
theorem irrational_sub_rat_iff : Irrational (x - q) ↔ Irrational x :=
  ⟨of_sub_rat q, sub_rat q⟩
#align irrational_sub_rat_iff irrational_sub_rat_iff

/- warning: irrational_sub_int_iff -> irrational_sub_int_iff is a dubious translation:
lean 3 declaration is
  forall {m : Int} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))) (Irrational x)
but is expected to have type
  forall {m : Int} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (Int.cast.{0} Real Real.intCast m))) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_sub_int_iff irrational_sub_int_iffₓ'. -/
@[simp]
theorem irrational_sub_int_iff : Irrational (x - m) ↔ Irrational x :=
  ⟨of_sub_int m, fun h => h.sub_int m⟩
#align irrational_sub_int_iff irrational_sub_int_iff

/- warning: irrational_sub_nat_iff -> irrational_sub_nat_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) (Irrational x)
but is expected to have type
  forall {n : Nat} {x : Real}, Iff (Irrational (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (Nat.cast.{0} Real Real.natCast n))) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_sub_nat_iff irrational_sub_nat_iffₓ'. -/
@[simp]
theorem irrational_sub_nat_iff : Irrational (x - n) ↔ Irrational x :=
  ⟨of_sub_nat n, fun h => h.subNat n⟩
#align irrational_sub_nat_iff irrational_sub_nat_iff

/- warning: irrational_neg_iff -> irrational_neg_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Irrational (Neg.neg.{0} Real Real.hasNeg x)) (Irrational x)
but is expected to have type
  forall {x : Real}, Iff (Irrational (Neg.neg.{0} Real Real.instNegReal x)) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_neg_iff irrational_neg_iffₓ'. -/
@[simp]
theorem irrational_neg_iff : Irrational (-x) ↔ Irrational x :=
  ⟨of_neg, Irrational.neg⟩
#align irrational_neg_iff irrational_neg_iff

/- warning: irrational_inv_iff -> irrational_inv_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Irrational (Inv.inv.{0} Real Real.hasInv x)) (Irrational x)
but is expected to have type
  forall {x : Real}, Iff (Irrational (Inv.inv.{0} Real Real.instInvReal x)) (Irrational x)
Case conversion may be inaccurate. Consider using '#align irrational_inv_iff irrational_inv_iffₓ'. -/
@[simp]
theorem irrational_inv_iff : Irrational x⁻¹ ↔ Irrational x :=
  ⟨of_inv, Irrational.inv⟩
#align irrational_inv_iff irrational_inv_iff

/- warning: irrational_rat_mul_iff -> irrational_rat_mul_iff is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x)) (And (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) (Irrational x))
but is expected to have type
  forall {q : Rat} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Rat.cast.{0} Real Real.ratCast q) x)) (And (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_rat_mul_iff irrational_rat_mul_iffₓ'. -/
@[simp]
theorem irrational_rat_mul_iff : Irrational (q * x) ↔ q ≠ 0 ∧ Irrational x :=
  ⟨fun h => ⟨Rat.cast_ne_zero.1 <| left_ne_zero_of_mul h.NeZero, h.ofRat_mul q⟩, fun h =>
    h.2.rat_mul h.1⟩
#align irrational_rat_mul_iff irrational_rat_mul_iff

/- warning: irrational_mul_rat_iff -> irrational_mul_rat_iff is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))) (And (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) (Irrational x))
but is expected to have type
  forall {q : Rat} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x (Rat.cast.{0} Real Real.ratCast q))) (And (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_mul_rat_iff irrational_mul_rat_iffₓ'. -/
@[simp]
theorem irrational_mul_rat_iff : Irrational (x * q) ↔ q ≠ 0 ∧ Irrational x := by
  rw [mul_comm, irrational_rat_mul_iff]
#align irrational_mul_rat_iff irrational_mul_rat_iff

/- warning: irrational_int_mul_iff -> irrational_int_mul_iff is a dubious translation:
lean 3 declaration is
  forall {m : Int} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x)) (And (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Irrational x))
but is expected to have type
  forall {m : Int} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Int.cast.{0} Real Real.intCast m) x)) (And (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_int_mul_iff irrational_int_mul_iffₓ'. -/
@[simp]
theorem irrational_int_mul_iff : Irrational (m * x) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_coe_int, irrational_rat_mul_iff, Int.cast_ne_zero]
#align irrational_int_mul_iff irrational_int_mul_iff

/- warning: irrational_mul_int_iff -> irrational_mul_int_iff is a dubious translation:
lean 3 declaration is
  forall {m : Int} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))) (And (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Irrational x))
but is expected to have type
  forall {m : Int} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x (Int.cast.{0} Real Real.intCast m))) (And (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_mul_int_iff irrational_mul_int_iffₓ'. -/
@[simp]
theorem irrational_mul_int_iff : Irrational (x * m) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_coe_int, irrational_mul_rat_iff, Int.cast_ne_zero]
#align irrational_mul_int_iff irrational_mul_int_iff

/- warning: irrational_nat_mul_iff -> irrational_nat_mul_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) x)) (And (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Irrational x))
but is expected to have type
  forall {n : Nat} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast n) x)) (And (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_nat_mul_iff irrational_nat_mul_iffₓ'. -/
@[simp]
theorem irrational_nat_mul_iff : Irrational (n * x) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_coe_nat, irrational_rat_mul_iff, Nat.cast_ne_zero]
#align irrational_nat_mul_iff irrational_nat_mul_iff

/- warning: irrational_mul_nat_iff -> irrational_mul_nat_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) (And (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Irrational x))
but is expected to have type
  forall {n : Nat} {x : Real}, Iff (Irrational (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x (Nat.cast.{0} Real Real.natCast n))) (And (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_mul_nat_iff irrational_mul_nat_iffₓ'. -/
@[simp]
theorem irrational_mul_nat_iff : Irrational (x * n) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_coe_nat, irrational_mul_rat_iff, Nat.cast_ne_zero]
#align irrational_mul_nat_iff irrational_mul_nat_iff

/- warning: irrational_rat_div_iff -> irrational_rat_div_iff is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q) x)) (And (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) (Irrational x))
but is expected to have type
  forall {q : Rat} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Rat.cast.{0} Real Real.ratCast q) x)) (And (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_rat_div_iff irrational_rat_div_iffₓ'. -/
@[simp]
theorem irrational_rat_div_iff : Irrational (q / x) ↔ q ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
#align irrational_rat_div_iff irrational_rat_div_iff

/- warning: irrational_div_rat_iff -> irrational_div_rat_iff is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))) (And (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) (Irrational x))
but is expected to have type
  forall {q : Rat} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Rat.cast.{0} Real Real.ratCast q))) (And (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_div_rat_iff irrational_div_rat_iffₓ'. -/
@[simp]
theorem irrational_div_rat_iff : Irrational (x / q) ↔ q ≠ 0 ∧ Irrational x := by
  rw [div_eq_mul_inv, ← cast_inv, irrational_mul_rat_iff, Ne.def, inv_eq_zero]
#align irrational_div_rat_iff irrational_div_rat_iff

/- warning: irrational_int_div_iff -> irrational_int_div_iff is a dubious translation:
lean 3 declaration is
  forall {m : Int} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m) x)) (And (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Irrational x))
but is expected to have type
  forall {m : Int} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Int.cast.{0} Real Real.intCast m) x)) (And (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_int_div_iff irrational_int_div_iffₓ'. -/
@[simp]
theorem irrational_int_div_iff : Irrational (m / x) ↔ m ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
#align irrational_int_div_iff irrational_int_div_iff

/- warning: irrational_div_int_iff -> irrational_div_int_iff is a dubious translation:
lean 3 declaration is
  forall {m : Int} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) m))) (And (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Irrational x))
but is expected to have type
  forall {m : Int} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Int.cast.{0} Real Real.intCast m))) (And (Ne.{1} Int m (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_div_int_iff irrational_div_int_iffₓ'. -/
@[simp]
theorem irrational_div_int_iff : Irrational (x / m) ↔ m ≠ 0 ∧ Irrational x := by
  rw [← cast_coe_int, irrational_div_rat_iff, Int.cast_ne_zero]
#align irrational_div_int_iff irrational_div_int_iff

/- warning: irrational_nat_div_iff -> irrational_nat_div_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) x)) (And (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Irrational x))
but is expected to have type
  forall {n : Nat} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Nat.cast.{0} Real Real.natCast n) x)) (And (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_nat_div_iff irrational_nat_div_iffₓ'. -/
@[simp]
theorem irrational_nat_div_iff : Irrational (n / x) ↔ n ≠ 0 ∧ Irrational x := by
  simp [div_eq_mul_inv]
#align irrational_nat_div_iff irrational_nat_div_iff

/- warning: irrational_div_nat_iff -> irrational_div_nat_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))) (And (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Irrational x))
but is expected to have type
  forall {n : Nat} {x : Real}, Iff (Irrational (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Nat.cast.{0} Real Real.natCast n))) (And (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Irrational x))
Case conversion may be inaccurate. Consider using '#align irrational_div_nat_iff irrational_div_nat_iffₓ'. -/
@[simp]
theorem irrational_div_nat_iff : Irrational (x / n) ↔ n ≠ 0 ∧ Irrational x := by
  rw [← cast_coe_nat, irrational_div_rat_iff, Nat.cast_ne_zero]
#align irrational_div_nat_iff irrational_div_nat_iff

/- warning: exists_irrational_btwn -> exists_irrational_btwn is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt x y) -> (Exists.{1} Real (fun (r : Real) => And (Irrational r) (And (LT.lt.{0} Real Real.hasLt x r) (LT.lt.{0} Real Real.hasLt r y))))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal x y) -> (Exists.{1} Real (fun (r : Real) => And (Irrational r) (And (LT.lt.{0} Real Real.instLTReal x r) (LT.lt.{0} Real Real.instLTReal r y))))
Case conversion may be inaccurate. Consider using '#align exists_irrational_btwn exists_irrational_btwnₓ'. -/
/-- There is an irrational number `r` between any two reals `x < r < y`. -/
theorem exists_irrational_btwn {x y : ℝ} (h : x < y) : ∃ r, Irrational r ∧ x < r ∧ r < y :=
  let ⟨q, ⟨hq1, hq2⟩⟩ := exists_rat_btwn ((sub_lt_sub_iff_right (Real.sqrt 2)).mpr h)
  ⟨q + Real.sqrt 2, irrational_sqrt_two.rat_add _, sub_lt_iff_lt_add.mp hq1,
    lt_sub_iff_add_lt.mp hq2⟩
#align exists_irrational_btwn exists_irrational_btwn

end

