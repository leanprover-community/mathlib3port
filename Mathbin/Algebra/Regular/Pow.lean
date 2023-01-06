/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.regular.pow
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Iterate
import Mathbin.Algebra.Regular.Basic

/-!
# Regular elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Implementation details

Group powers and other definitions import a lot of the algebra hierarchy.
Lemmas about them are kept separate to be able to provide `is_regular` early in the
algebra hierarchy.

-/


variable {R : Type _} {a b : R}

section Monoid

variable [Monoid R]

/- warning: is_left_regular.pow -> IsLeftRegular.pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] (n : Nat), (IsLeftRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a) -> (IsLeftRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n))
but is expected to have type
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] (n : Nat), (IsLeftRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a) -> (IsLeftRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n))
Case conversion may be inaccurate. Consider using '#align is_left_regular.pow IsLeftRegular.powₓ'. -/
/-- Any power of a left-regular element is left-regular. -/
theorem IsLeftRegular.pow (n : ℕ) (rla : IsLeftRegular a) : IsLeftRegular (a ^ n) := by
  simp only [IsLeftRegular, ← mul_left_iterate, rla.iterate n]
#align is_left_regular.pow IsLeftRegular.pow

/- warning: is_right_regular.pow -> IsRightRegular.pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] (n : Nat), (IsRightRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a) -> (IsRightRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n))
but is expected to have type
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] (n : Nat), (IsRightRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a) -> (IsRightRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n))
Case conversion may be inaccurate. Consider using '#align is_right_regular.pow IsRightRegular.powₓ'. -/
/-- Any power of a right-regular element is right-regular. -/
theorem IsRightRegular.pow (n : ℕ) (rra : IsRightRegular a) : IsRightRegular (a ^ n) :=
  by
  rw [IsRightRegular, ← mul_right_iterate]
  exact rra.iterate n
#align is_right_regular.pow IsRightRegular.pow

/- warning: is_regular.pow -> IsRegular.pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] (n : Nat), (IsRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a) -> (IsRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n))
but is expected to have type
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] (n : Nat), (IsRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a) -> (IsRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n))
Case conversion may be inaccurate. Consider using '#align is_regular.pow IsRegular.powₓ'. -/
/-- Any power of a regular element is regular. -/
theorem IsRegular.pow (n : ℕ) (ra : IsRegular a) : IsRegular (a ^ n) :=
  ⟨IsLeftRegular.pow n ra.left, IsRightRegular.pow n ra.right⟩
#align is_regular.pow IsRegular.pow

/- warning: is_left_regular.pow_iff -> IsLeftRegular.pow_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Iff (IsLeftRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n)) (IsLeftRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a))
but is expected to have type
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Iff (IsLeftRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n)) (IsLeftRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a))
Case conversion may be inaccurate. Consider using '#align is_left_regular.pow_iff IsLeftRegular.pow_iffₓ'. -/
/-- An element `a` is left-regular if and only if a positive power of `a` is left-regular. -/
theorem IsLeftRegular.pow_iff {n : ℕ} (n0 : 0 < n) : IsLeftRegular (a ^ n) ↔ IsLeftRegular a :=
  by
  refine' ⟨_, IsLeftRegular.pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0, pow_succ']
  exact IsLeftRegular.of_mul
#align is_left_regular.pow_iff IsLeftRegular.pow_iff

/- warning: is_right_regular.pow_iff -> IsRightRegular.pow_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Iff (IsRightRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n)) (IsRightRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a))
but is expected to have type
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Iff (IsRightRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n)) (IsRightRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a))
Case conversion may be inaccurate. Consider using '#align is_right_regular.pow_iff IsRightRegular.pow_iffₓ'. -/
/-- An element `a` is right-regular if and only if a positive power of `a` is right-regular. -/
theorem IsRightRegular.pow_iff {n : ℕ} (n0 : 0 < n) : IsRightRegular (a ^ n) ↔ IsRightRegular a :=
  by
  refine' ⟨_, IsRightRegular.pow n⟩
  rw [← Nat.succ_pred_eq_of_pos n0, pow_succ]
  exact IsRightRegular.of_mul
#align is_right_regular.pow_iff IsRightRegular.pow_iff

/- warning: is_regular.pow_iff -> IsRegular.pow_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] {n : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (Iff (IsRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n)) (IsRegular.{u1} R (MulOneClass.toHasMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a))
but is expected to have type
  forall {R : Type.{u1}} {a : R} [_inst_1 : Monoid.{u1} R] {n : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (Iff (IsRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R _inst_1)) a n)) (IsRegular.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_1)) a))
Case conversion may be inaccurate. Consider using '#align is_regular.pow_iff IsRegular.pow_iffₓ'. -/
/-- An element `a` is regular if and only if a positive power of `a` is regular. -/
theorem IsRegular.pow_iff {n : ℕ} (n0 : 0 < n) : IsRegular (a ^ n) ↔ IsRegular a :=
  ⟨fun h => ⟨(IsLeftRegular.pow_iff n0).mp h.left, (IsRightRegular.pow_iff n0).mp h.right⟩, fun h =>
    ⟨IsLeftRegular.pow n h.left, IsRightRegular.pow n h.right⟩⟩
#align is_regular.pow_iff IsRegular.pow_iff

end Monoid

