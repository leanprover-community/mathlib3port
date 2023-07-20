/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathbin.Algebra.Ring.Defs
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Opposites

#align_import algebra.ring.basic from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Semirings and rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gives lemmas about semirings, rings and domains.
This is analogous to `algebra.group.basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `algebra.ring.defs`.

-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

namespace AddHom

#print AddHom.mulLeft /-
/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulLeft {R : Type _} [Distrib R] (r : R) : AddHom R R :=
  ⟨(· * ·) r, mul_add r⟩
#align add_hom.mul_left AddHom.mulLeft
-/

#print AddHom.mulRight /-
/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulRight {R : Type _} [Distrib R] (r : R) : AddHom R R :=
  ⟨fun a => a * r, fun _ _ => add_mul _ _ r⟩
#align add_hom.mul_right AddHom.mulRight
-/

end AddHom

section AddHomClass

variable {F : Type _} [NonAssocSemiring α] [NonAssocSemiring β] [AddHomClass F α β]

#print map_bit0 /-
/-- Additive homomorphisms preserve `bit0`. -/
@[simp]
theorem map_bit0 (f : F) (a : α) : (f (bit0 a) : β) = bit0 (f a) :=
  map_add _ _ _
#align map_bit0 map_bit0
-/

end AddHomClass

namespace AddMonoidHom

#print AddMonoidHom.mulLeft /-
/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulLeft {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : R →+ R
    where
  toFun := (· * ·) r
  map_zero' := MulZeroClass.mul_zero r
  map_add' := mul_add r
#align add_monoid_hom.mul_left AddMonoidHom.mulLeft
-/

#print AddMonoidHom.coe_mulLeft /-
@[simp]
theorem coe_mulLeft {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : ⇑(mulLeft r) = (· * ·) r :=
  rfl
#align add_monoid_hom.coe_mul_left AddMonoidHom.coe_mulLeft
-/

#print AddMonoidHom.mulRight /-
/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulRight {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : R →+ R
    where
  toFun a := a * r
  map_zero' := MulZeroClass.zero_mul r
  map_add' _ _ := add_mul _ _ r
#align add_monoid_hom.mul_right AddMonoidHom.mulRight
-/

#print AddMonoidHom.coe_mulRight /-
@[simp]
theorem coe_mulRight {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : ⇑(mulRight r) = (· * r) :=
  rfl
#align add_monoid_hom.coe_mul_right AddMonoidHom.coe_mulRight
-/

#print AddMonoidHom.mulRight_apply /-
theorem mulRight_apply {R : Type _} [NonUnitalNonAssocSemiring R] (a r : R) :
    mulRight r a = a * r :=
  rfl
#align add_monoid_hom.mul_right_apply AddMonoidHom.mulRight_apply
-/

end AddMonoidHom

section HasDistribNeg

section Mul

variable [Mul α] [HasDistribNeg α]

open MulOpposite

instance : HasDistribNeg αᵐᵒᵖ :=
  {
    MulOpposite.hasInvolutiveNeg
      _ with
    neg_mul := fun _ _ => unop_injective <| mul_neg _ _
    mul_neg := fun _ _ => unop_injective <| neg_mul _ _ }

end Mul

section Group

variable [Group α] [HasDistribNeg α]

#print inv_neg' /-
@[simp]
theorem inv_neg' (a : α) : (-a)⁻¹ = -a⁻¹ := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg, neg_neg, mul_left_inv]
#align inv_neg' inv_neg'
-/

end Group

end HasDistribNeg

section NonUnitalCommRing

variable [NonUnitalCommRing α] {a b c : α}

attribute [local simp] add_assoc add_comm add_left_comm mul_comm

#print vieta_formula_quadratic /-
/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
theorem vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
    ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c :=
  by
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm])
  refine' ⟨b - x, _, by simp, by rw [this]⟩
  rw [this, sub_add, ← sub_mul, sub_self]
#align Vieta_formula_quadratic vieta_formula_quadratic
-/

end NonUnitalCommRing

#print succ_ne_self /-
theorem succ_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 ≠ a := fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))
#align succ_ne_self succ_ne_self
-/

#print pred_ne_self /-
theorem pred_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 ≠ a := fun h =>
  one_ne_zero (neg_injective ((add_right_inj a).mp (by simpa [sub_eq_add_neg] using h)))
#align pred_ne_self pred_ne_self
-/

section NoZeroDivisors

variable (α)

#print IsLeftCancelMulZero.to_noZeroDivisors /-
theorem IsLeftCancelMulZero.to_noZeroDivisors [Ring α] [IsLeftCancelMulZero α] : NoZeroDivisors α :=
  by
  refine' ⟨fun x y h => _⟩
  by_cases hx : x = 0
  · left; exact hx
  · right
    rw [← sub_zero (x * y), ← MulZeroClass.mul_zero x, ← mul_sub] at h 
    convert IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx h
    rw [sub_zero]
#align is_left_cancel_mul_zero.to_no_zero_divisors IsLeftCancelMulZero.to_noZeroDivisors
-/

#print IsRightCancelMulZero.to_noZeroDivisors /-
theorem IsRightCancelMulZero.to_noZeroDivisors [Ring α] [IsRightCancelMulZero α] :
    NoZeroDivisors α := by
  refine' ⟨fun x y h => _⟩
  by_cases hy : y = 0
  · right; exact hy
  · left
    rw [← sub_zero (x * y), ← MulZeroClass.zero_mul y, ← sub_mul] at h 
    convert IsRightCancelMulZero.mul_right_cancel_of_ne_zero hy h
    rw [sub_zero]
#align is_right_cancel_mul_zero.to_no_zero_divisors IsRightCancelMulZero.to_noZeroDivisors
-/

#print NoZeroDivisors.to_isCancelMulZero /-
instance (priority := 100) NoZeroDivisors.to_isCancelMulZero [Ring α] [NoZeroDivisors α] :
    IsCancelMulZero α
    where
  mul_left_cancel_of_ne_zero a b c ha h :=
    by
    rw [← sub_eq_zero, ← mul_sub] at h 
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left ha)
  mul_right_cancel_of_ne_zero a b c hb h :=
    by
    rw [← sub_eq_zero, ← sub_mul] at h 
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb)
#align no_zero_divisors.to_is_cancel_mul_zero NoZeroDivisors.to_isCancelMulZero
-/

#print NoZeroDivisors.to_isDomain /-
theorem NoZeroDivisors.to_isDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] : IsDomain α :=
  { NoZeroDivisors.to_isCancelMulZero α, h with }
#align no_zero_divisors.to_is_domain NoZeroDivisors.to_isDomain
-/

#print IsDomain.to_noZeroDivisors /-
instance (priority := 100) IsDomain.to_noZeroDivisors [Ring α] [IsDomain α] : NoZeroDivisors α :=
  IsRightCancelMulZero.to_noZeroDivisors α
#align is_domain.to_no_zero_divisors IsDomain.to_noZeroDivisors
-/

end NoZeroDivisors

