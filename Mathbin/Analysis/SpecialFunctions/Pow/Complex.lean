/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.pow.complex
! leanprover-community/mathlib commit 4fa54b337f7d52805480306db1b1439c741848c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Complex.Log

/-! # Power function on `ℂ`

We construct the power functions `x ^ y`, where `x` and `y` are complex numbers.
-/


open Classical Real Topology Filter ComplexConjugate

open Filter Finset Set

namespace Complex

#print Complex.cpow /-
/-- The complex power function `x ^ y`, given by `x ^ y = exp(y log x)` (where `log` is the
principal determination of the logarithm), unless `x = 0` where one sets `0 ^ 0 = 1` and
`0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def cpow (x y : ℂ) : ℂ :=
  if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)
#align complex.cpow Complex.cpow
-/

noncomputable instance : Pow ℂ ℂ :=
  ⟨cpow⟩

#print Complex.cpow_eq_pow /-
@[simp]
theorem cpow_eq_pow (x y : ℂ) : cpow x y = x ^ y :=
  rfl
#align complex.cpow_eq_pow Complex.cpow_eq_pow
-/

/- warning: complex.cpow_def -> Complex.cpow_def is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (y : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x y) (ite.{1} Complex (Eq.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (Complex.decidableEq x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (ite.{1} Complex (Eq.{1} Complex y (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (Complex.decidableEq y (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.log x) y)))
but is expected to have type
  forall (x : Complex) (y : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x y) (ite.{1} Complex (Eq.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (Complex.instDecidableEqComplex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (ite.{1} Complex (Eq.{1} Complex y (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (Complex.instDecidableEqComplex y (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.log x) y)))
Case conversion may be inaccurate. Consider using '#align complex.cpow_def Complex.cpow_defₓ'. -/
theorem cpow_def (x y : ℂ) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) :=
  rfl
#align complex.cpow_def Complex.cpow_def

/- warning: complex.cpow_def_of_ne_zero -> Complex.cpow_def_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (forall (y : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x y) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.log x) y)))
but is expected to have type
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (forall (y : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x y) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.log x) y)))
Case conversion may be inaccurate. Consider using '#align complex.cpow_def_of_ne_zero Complex.cpow_def_of_ne_zeroₓ'. -/
theorem cpow_def_of_ne_zero {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y = exp (log x * y) :=
  if_neg hx
#align complex.cpow_def_of_ne_zero Complex.cpow_def_of_ne_zero

/- warning: complex.cpow_zero -> Complex.cpow_zero is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))
Case conversion may be inaccurate. Consider using '#align complex.cpow_zero Complex.cpow_zeroₓ'. -/
@[simp]
theorem cpow_zero (x : ℂ) : x ^ (0 : ℂ) = 1 := by simp [cpow_def]
#align complex.cpow_zero Complex.cpow_zero

/- warning: complex.cpow_eq_zero_iff -> Complex.cpow_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (y : Complex), Iff (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x y) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (And (Eq.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (Ne.{1} Complex y (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))))
but is expected to have type
  forall (x : Complex) (y : Complex), Iff (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x y) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (And (Eq.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (Ne.{1} Complex y (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))))
Case conversion may be inaccurate. Consider using '#align complex.cpow_eq_zero_iff Complex.cpow_eq_zero_iffₓ'. -/
@[simp]
theorem cpow_eq_zero_iff (x y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 :=
  by
  simp only [cpow_def]
  split_ifs <;> simp [*, exp_ne_zero]
#align complex.cpow_eq_zero_iff Complex.cpow_eq_zero_iff

/- warning: complex.zero_cpow -> Complex.zero_cpow is a dubious translation:
lean 3 declaration is
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))) x) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero))))
but is expected to have type
  forall {x : Complex}, (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)) x) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex)))
Case conversion may be inaccurate. Consider using '#align complex.zero_cpow Complex.zero_cpowₓ'. -/
@[simp]
theorem zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 := by simp [cpow_def, *]
#align complex.zero_cpow Complex.zero_cpow

#print Complex.zero_cpow_eq_iff /-
theorem zero_cpow_eq_iff {x : ℂ} {a : ℂ} : 0 ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 :=
  by
  constructor
  · intro hyp
    simp only [cpow_def, eq_self_iff_true, if_true] at hyp
    by_cases x = 0
    · subst h
      simp only [if_true, eq_self_iff_true] at hyp
      right
      exact ⟨rfl, hyp.symm⟩
    · rw [if_neg h] at hyp
      left
      exact ⟨h, hyp.symm⟩
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_cpow h
    · exact cpow_zero _
#align complex.zero_cpow_eq_iff Complex.zero_cpow_eq_iff
-/

#print Complex.eq_zero_cpow_iff /-
theorem eq_zero_cpow_iff {x : ℂ} {a : ℂ} : a = 0 ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_cpow_eq_iff, eq_comm]
#align complex.eq_zero_cpow_iff Complex.eq_zero_cpow_iff
-/

/- warning: complex.cpow_one -> Complex.cpow_one is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))) x
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))) x
Case conversion may be inaccurate. Consider using '#align complex.cpow_one Complex.cpow_oneₓ'. -/
@[simp]
theorem cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
  if hx : x = 0 then by simp [hx, cpow_def]
  else by rw [cpow_def, if_neg (one_ne_zero : (1 : ℂ) ≠ 0), if_neg hx, mul_one, exp_log hx]
#align complex.cpow_one Complex.cpow_one

#print Complex.one_cpow /-
@[simp]
theorem one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 := by
  rw [cpow_def] <;> split_ifs <;> simp_all [one_ne_zero]
#align complex.one_cpow Complex.one_cpow
-/

/- warning: complex.cpow_add -> Complex.cpow_add is a dubious translation:
lean 3 declaration is
  forall {x : Complex} (y : Complex) (z : Complex), (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) y z)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x y) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x z)))
but is expected to have type
  forall {x : Complex} (y : Complex) (z : Complex), (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) y z)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x y) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x z)))
Case conversion may be inaccurate. Consider using '#align complex.cpow_add Complex.cpow_addₓ'. -/
theorem cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [cpow_def, ite_mul, boole_mul, mul_ite, mul_boole] <;> simp_all [exp_add, mul_add]
#align complex.cpow_add Complex.cpow_add

/- warning: complex.cpow_mul -> Complex.cpow_mul is a dubious translation:
lean 3 declaration is
  forall {x : Complex} {y : Complex} (z : Complex), (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg Real.pi) (Complex.im (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.log x) y))) -> (LE.le.{0} Real Real.hasLe (Complex.im (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (Complex.log x) y)) Real.pi) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) y z)) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x y) z))
but is expected to have type
  forall {x : Complex} {y : Complex} (z : Complex), (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal Real.pi) (Complex.im (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.log x) y))) -> (LE.le.{0} Real Real.instLEReal (Complex.im (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.log x) y)) Real.pi) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) y z)) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x y) z))
Case conversion may be inaccurate. Consider using '#align complex.cpow_mul Complex.cpow_mulₓ'. -/
theorem cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
    x ^ (y * z) = (x ^ y) ^ z := by
  simp only [cpow_def]
  split_ifs <;> simp_all [exp_ne_zero, log_exp h₁ h₂, mul_assoc]
#align complex.cpow_mul Complex.cpow_mul

/- warning: complex.cpow_neg -> Complex.cpow_neg is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (y : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (Neg.neg.{0} Complex Complex.hasNeg y)) (Inv.inv.{0} Complex Complex.hasInv (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x y))
but is expected to have type
  forall (x : Complex) (y : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (Neg.neg.{0} Complex Complex.instNegComplex y)) (Inv.inv.{0} Complex Complex.instInvComplex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x y))
Case conversion may be inaccurate. Consider using '#align complex.cpow_neg Complex.cpow_negₓ'. -/
theorem cpow_neg (x y : ℂ) : x ^ (-y) = (x ^ y)⁻¹ := by
  simp only [cpow_def, neg_eq_zero, mul_neg] <;> split_ifs <;> simp [exp_neg]
#align complex.cpow_neg Complex.cpow_neg

/- warning: complex.cpow_sub -> Complex.cpow_sub is a dubious translation:
lean 3 declaration is
  forall {x : Complex} (y : Complex) (z : Complex), (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) y z)) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (DivInvMonoid.toHasDiv.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (NormedDivisionRing.toDivisionRing.{0} Complex (NormedField.toNormedDivisionRing.{0} Complex Complex.normedField))))) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x y) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x z)))
but is expected to have type
  forall {x : Complex} (y : Complex) (z : Complex), (Ne.{1} Complex x (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) y z)) (HDiv.hDiv.{0, 0, 0} Complex Complex Complex (instHDiv.{0} Complex (Field.toDiv.{0} Complex Complex.instFieldComplex)) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x y) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x z)))
Case conversion may be inaccurate. Consider using '#align complex.cpow_sub Complex.cpow_subₓ'. -/
theorem cpow_sub {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y - z) = x ^ y / x ^ z := by
  rw [sub_eq_add_neg, cpow_add _ _ hx, cpow_neg, div_eq_mul_inv]
#align complex.cpow_sub Complex.cpow_sub

/- warning: complex.cpow_neg_one -> Complex.cpow_neg_one is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (Neg.neg.{0} Complex Complex.hasNeg (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))))) (Inv.inv.{0} Complex Complex.hasInv x)
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (Neg.neg.{0} Complex Complex.instNegComplex (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))) (Inv.inv.{0} Complex Complex.instInvComplex x)
Case conversion may be inaccurate. Consider using '#align complex.cpow_neg_one Complex.cpow_neg_oneₓ'. -/
theorem cpow_neg_one (x : ℂ) : x ^ (-1 : ℂ) = x⁻¹ := by simpa using cpow_neg x 1
#align complex.cpow_neg_one Complex.cpow_neg_one

/- warning: complex.cpow_nat_cast -> Complex.cpow_nat_cast is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (n : Nat), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) n)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) x n)
but is expected to have type
  forall (x : Complex) (n : Nat), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (Nat.cast.{0} Complex (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) n)) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex Complex.instSemiringComplex)))) x n)
Case conversion may be inaccurate. Consider using '#align complex.cpow_nat_cast Complex.cpow_nat_castₓ'. -/
@[simp, norm_cast]
theorem cpow_nat_cast (x : ℂ) : ∀ n : ℕ, x ^ (n : ℂ) = x ^ n
  | 0 => by simp
  | n + 1 =>
    if hx : x = 0 then by
      simp only [hx, pow_succ, Complex.zero_cpow (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)),
        MulZeroClass.zero_mul]
    else by simp [cpow_add, hx, pow_add, cpow_nat_cast n]
#align complex.cpow_nat_cast Complex.cpow_nat_cast

/- warning: complex.cpow_two -> Complex.cpow_two is a dubious translation:
lean 3 declaration is
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne))))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall (x : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex Complex.instSemiringComplex)))) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align complex.cpow_two Complex.cpow_twoₓ'. -/
@[simp]
theorem cpow_two (x : ℂ) : x ^ (2 : ℂ) = x ^ 2 :=
  by
  rw [← cpow_nat_cast]
  simp only [Nat.cast_bit0, Nat.cast_one]
#align complex.cpow_two Complex.cpow_two

/- warning: complex.cpow_int_cast -> Complex.cpow_int_cast is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (n : Int), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Complex (HasLiftT.mk.{1, 1} Int Complex (CoeTCₓ.coe.{1, 1} Int Complex (Int.castCoe.{0} Complex (AddGroupWithOne.toHasIntCast.{0} Complex Complex.addGroupWithOne)))) n)) (HPow.hPow.{0, 0, 0} Complex Int Complex (instHPow.{0, 0} Complex Int (DivInvMonoid.Pow.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (NormedDivisionRing.toDivisionRing.{0} Complex (NormedField.toNormedDivisionRing.{0} Complex Complex.normedField))))) x n)
but is expected to have type
  forall (x : Complex) (n : Int), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (Int.cast.{0} Complex (Ring.toIntCast.{0} Complex Complex.instRingComplex) n)) (HPow.hPow.{0, 0, 0} Complex Int Complex (instHPow.{0, 0} Complex Int (DivInvMonoid.Pow.{0} Complex (DivisionRing.toDivInvMonoid.{0} Complex (NormedDivisionRing.toDivisionRing.{0} Complex (NormedField.toNormedDivisionRing.{0} Complex Complex.instNormedFieldComplex))))) x n)
Case conversion may be inaccurate. Consider using '#align complex.cpow_int_cast Complex.cpow_int_castₓ'. -/
@[simp, norm_cast]
theorem cpow_int_cast (x : ℂ) : ∀ n : ℤ, x ^ (n : ℂ) = x ^ n
  | (n : ℕ) => by simp
  | -[n+1] => by
    rw [zpow_negSucc] <;>
      simp only [Int.negSucc_coe, Int.cast_neg, Complex.cpow_neg, inv_eq_one_div, Int.cast_ofNat,
        cpow_nat_cast]
#align complex.cpow_int_cast Complex.cpow_int_cast

/- warning: complex.cpow_nat_inv_pow -> Complex.cpow_nat_inv_pow is a dubious translation:
lean 3 declaration is
  forall (x : Complex) {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (Ring.toMonoid.{0} Complex Complex.ring))) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (Inv.inv.{0} Complex Complex.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) n))) n) x)
but is expected to have type
  forall (x : Complex) {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Nat Complex (instHPow.{0, 0} Complex Nat (Monoid.Pow.{0} Complex (MonoidWithZero.toMonoid.{0} Complex (Semiring.toMonoidWithZero.{0} Complex Complex.instSemiringComplex)))) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x (Inv.inv.{0} Complex Complex.instInvComplex (Nat.cast.{0} Complex (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) n))) n) x)
Case conversion may be inaccurate. Consider using '#align complex.cpow_nat_inv_pow Complex.cpow_nat_inv_powₓ'. -/
theorem cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℂ)) ^ n = x :=
  by
  suffices im (log x * n⁻¹) ∈ Ioc (-π) π
    by
    rw [← cpow_nat_cast, ← cpow_mul _ this.1 this.2, inv_mul_cancel, cpow_one]
    exact_mod_cast hn
  rw [mul_comm, ← of_real_nat_cast, ← of_real_inv, of_real_mul_im, ← div_eq_inv_mul]
  rw [← pos_iff_ne_zero] at hn
  have hn' : 0 < (n : ℝ) := by assumption_mod_cast
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_iff.2 hn
  constructor
  · rw [lt_div_iff hn']
    calc
      -π * n ≤ -π * 1 := mul_le_mul_of_nonpos_left hn1 (neg_nonpos.2 real.pi_pos.le)
      _ = -π := (mul_one _)
      _ < im (log x) := neg_pi_lt_log_im _
      
  · rw [div_le_iff hn']
    calc
      im (log x) ≤ π := log_im_le_pi _
      _ = π * 1 := (mul_one π).symm
      _ ≤ π * n := mul_le_mul_of_nonneg_left hn1 real.pi_pos.le
      
#align complex.cpow_nat_inv_pow Complex.cpow_nat_inv_pow

/- warning: complex.mul_cpow_of_real_nonneg -> Complex.mul_cpow_of_real_nonneg is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) a) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (forall (r : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) b)) r) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) a) r) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) b) r)))
but is expected to have type
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) a) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (forall (r : Complex), Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' a) (Complex.ofReal' b)) r) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' a) r) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Complex.ofReal' b) r)))
Case conversion may be inaccurate. Consider using '#align complex.mul_cpow_of_real_nonneg Complex.mul_cpow_of_real_nonnegₓ'. -/
theorem mul_cpow_of_real_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    ((a : ℂ) * (b : ℂ)) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r :=
  by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp only [cpow_zero, mul_one]
  rcases eq_or_lt_of_le ha with (rfl | ha')
  · rw [of_real_zero, MulZeroClass.zero_mul, zero_cpow hr, MulZeroClass.zero_mul]
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · rw [of_real_zero, MulZeroClass.mul_zero, zero_cpow hr, MulZeroClass.mul_zero]
  have ha'' : (a : ℂ) ≠ 0 := of_real_ne_zero.mpr ha'.ne'
  have hb'' : (b : ℂ) ≠ 0 := of_real_ne_zero.mpr hb'.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero ha'' hb''), log_of_real_mul ha' hb'', of_real_log ha,
    add_mul, exp_add, ← cpow_def_of_ne_zero ha'', ← cpow_def_of_ne_zero hb'']
#align complex.mul_cpow_of_real_nonneg Complex.mul_cpow_of_real_nonneg

#print Complex.inv_cpow_eq_ite /-
theorem inv_cpow_eq_ite (x : ℂ) (n : ℂ) :
    x⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹ :=
  by
  simp_rw [Complex.cpow_def, log_inv_eq_ite, inv_eq_zero, map_eq_zero, ite_mul, neg_mul,
    IsROrC.conj_inv, apply_ite conj, apply_ite exp, apply_ite Inv.inv, map_zero, map_one, exp_neg,
    inv_one, inv_zero, ← exp_conj, map_mul, conj_conj]
  split_ifs with hx hn ha ha <;> rfl
#align complex.inv_cpow_eq_ite Complex.inv_cpow_eq_ite
-/

#print Complex.inv_cpow /-
theorem inv_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  rw [inv_cpow_eq_ite, if_neg hx]
#align complex.inv_cpow Complex.inv_cpow
-/

/- warning: complex.inv_cpow_eq_ite' -> Complex.inv_cpow_eq_ite' is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (n : Complex), Eq.{1} Complex (Inv.inv.{0} Complex Complex.hasInv (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x n)) (ite.{1} Complex (Eq.{1} Real (Complex.arg x) Real.pi) (Real.decidableEq (Complex.arg x) Real.pi) (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (Inv.inv.{0} Complex Complex.hasInv x) (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) n))) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (Inv.inv.{0} Complex Complex.hasInv x) n))
but is expected to have type
  forall (x : Complex) (n : Complex), Eq.{1} Complex (Inv.inv.{0} Complex Complex.instInvComplex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) x n)) (ite.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) (HPow.hPow.{0, 0, 0} Complex ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) n) Complex (instHPow.{0, 0} Complex ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) n) Complex.instPowComplex) (Inv.inv.{0} Complex Complex.instInvComplex x) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (a : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) a) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) n))) (Eq.{1} Real (Complex.arg x) Real.pi) (Real.decidableEq (Complex.arg x) Real.pi) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) (HPow.hPow.{0, 0, 0} Complex ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) n) Complex (instHPow.{0, 0} Complex ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) n) Complex.instPowComplex) (Inv.inv.{0} Complex Complex.instInvComplex x) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) n))) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.instPowComplex) (Inv.inv.{0} Complex Complex.instInvComplex x) n))
Case conversion may be inaccurate. Consider using '#align complex.inv_cpow_eq_ite' Complex.inv_cpow_eq_ite'ₓ'. -/
/-- `complex.inv_cpow_eq_ite` with the `ite` on the other side. -/
theorem inv_cpow_eq_ite' (x : ℂ) (n : ℂ) :
    (x ^ n)⁻¹ = if x.arg = π then conj (x⁻¹ ^ conj n) else x⁻¹ ^ n :=
  by
  rw [inv_cpow_eq_ite, apply_ite conj, conj_conj, conj_conj]
  split_ifs
  · rfl
  · rw [inv_cpow _ _ h]
#align complex.inv_cpow_eq_ite' Complex.inv_cpow_eq_ite'

#print Complex.conj_cpow_eq_ite /-
theorem conj_cpow_eq_ite (x : ℂ) (n : ℂ) :
    conj x ^ n = if x.arg = π then x ^ n else conj (x ^ conj n) :=
  by
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ← exp_conj, map_mul, conj_conj,
    log_conj_eq_ite]
  split_ifs with hcx hn hx <;> rfl
#align complex.conj_cpow_eq_ite Complex.conj_cpow_eq_ite
-/

#print Complex.conj_cpow /-
theorem conj_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : conj x ^ n = conj (x ^ conj n) := by
  rw [conj_cpow_eq_ite, if_neg hx]
#align complex.conj_cpow Complex.conj_cpow
-/

/- warning: complex.cpow_conj -> Complex.cpow_conj is a dubious translation:
lean 3 declaration is
  forall (x : Complex) (n : Complex), (Ne.{1} Real (Complex.arg x) Real.pi) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) x (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) n)) (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) (HPow.hPow.{0, 0, 0} Complex Complex Complex (instHPow.{0, 0} Complex Complex Complex.hasPow) (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) x) n)))
but is expected to have type
  forall (x : Complex) (n : Complex), (Ne.{1} Real (Complex.arg x) Real.pi) -> (Eq.{1} Complex (HPow.hPow.{0, 0, 0} Complex ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) n) Complex (instHPow.{0, 0} Complex ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) n) Complex.instPowComplex) x (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) n)) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex))) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (fun (_x : (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex))) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (NonUnitalNonAssocSemiring.toMul.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex))) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex))) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (CommSemiring.toSemiring.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex)))))) (starRingEnd.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) (instHPow.{0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) x) Complex Complex.instPowComplex) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) x) n)))
Case conversion may be inaccurate. Consider using '#align complex.cpow_conj Complex.cpow_conjₓ'. -/
theorem cpow_conj (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x ^ conj n = conj (conj x ^ n) := by
  rw [conj_cpow _ _ hx, conj_conj]
#align complex.cpow_conj Complex.cpow_conj

end Complex

section Tactics

/-!
## Tactic extensions for complex powers
-/


namespace NormNum

theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c := by
  rw [← h, hb, Complex.cpow_nat_cast]
#align norm_num.cpow_pos NormNum.cpow_pos

theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ) (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') :
    a ^ (-b) = c' := by rw [← hc, ← h, hb, Complex.cpow_neg, Complex.cpow_nat_cast]
#align norm_num.cpow_neg NormNum.cpow_neg

open Tactic

/-- Generalized version of `prove_cpow`, `prove_nnrpow`, `prove_ennrpow`. -/
unsafe def prove_rpow' (pos neg zero : Name) (α β one a b : expr) : tactic (expr × expr) := do
  let na ← a.to_rat
  let icα ← mk_instance_cache α
  let icβ ← mk_instance_cache β
  match match_sign b with
    | Sum.inl b => do
      let nc ← mk_instance_cache q(ℕ)
      let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
      let (icα, c, h) ← prove_pow a na icα b'
      let cr ← c
      let (icα, c', hc) ← prove_inv icα c cr
      pure (c', (expr.const neg []).mk_app [a, b, b', c, c', hb, h, hc])
    | Sum.inr ff => pure (one, expr.const zero [] a)
    | Sum.inr tt => do
      let nc ← mk_instance_cache q(ℕ)
      let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
      let (icα, c, h) ← prove_pow a na icα b'
      pure (c, (expr.const Pos []).mk_app [a, b, b', c, hb, h])
#align norm_num.prove_rpow' norm_num.prove_rpow'

/-- Evaluate `complex.cpow a b` where `a` is a rational numeral and `b` is an integer. -/
unsafe def prove_cpow : expr → expr → tactic (expr × expr) :=
  prove_rpow' `` cpow_pos `` cpow_neg `` Complex.cpow_zero q(ℂ) q(ℂ) q((1 : ℂ))
#align norm_num.prove_cpow norm_num.prove_cpow

/-- Evaluates expressions of the form `cpow a b` and `a ^ b` in the special case where
`b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
@[norm_num]
unsafe def eval_cpow : expr → tactic (expr × expr)
  | q(@Pow.pow _ _ Complex.hasPow $(a) $(b)) => b.to_int >> prove_cpow a b
  | q(Complex.cpow $(a) $(b)) => b.to_int >> prove_cpow a b
  | _ => tactic.failed
#align norm_num.eval_cpow norm_num.eval_cpow

end NormNum

end Tactics

