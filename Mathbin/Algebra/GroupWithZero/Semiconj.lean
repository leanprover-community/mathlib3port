/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.GroupWithZero.Units.Basic
import Mathbin.Algebra.Group.Semiconj

/-!
# Lemmas about semiconjugate elements in a `group_with_zero`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/757
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α M₀ G₀ M₀' G₀' F F' : Type _}

namespace SemiconjBy

/- warning: semiconj_by.zero_right -> SemiconjBy.zero_right is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_1 : MulZeroClass.{u_3} G₀] (a : G₀), SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ _inst_1) a (OfNat.ofNat.{u_3} G₀ 0 (OfNat.mk.{u_3} G₀ 0 (Zero.zero.{u_3} G₀ (MulZeroClass.toHasZero.{u_3} G₀ _inst_1)))) (OfNat.ofNat.{u_3} G₀ 0 (OfNat.mk.{u_3} G₀ 0 (Zero.zero.{u_3} G₀ (MulZeroClass.toHasZero.{u_3} G₀ _inst_1))))
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.27 : MulZeroClass.{u_1} G₀] (a : G₀), SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.27) a (OfNat.ofNat.{u_1} G₀ 0 (Zero.toOfNat0.{u_1} G₀ (MulZeroClass.toZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.27))) (OfNat.ofNat.{u_1} G₀ 0 (Zero.toOfNat0.{u_1} G₀ (MulZeroClass.toZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.27)))
Case conversion may be inaccurate. Consider using '#align semiconj_by.zero_right SemiconjBy.zero_rightₓ'. -/
@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by
  simp only [SemiconjBy, mul_zero, zero_mul]
#align semiconj_by.zero_right SemiconjBy.zero_right

/- warning: semiconj_by.zero_left -> SemiconjBy.zero_left is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_1 : MulZeroClass.{u_3} G₀] (x : G₀) (y : G₀), SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ _inst_1) (OfNat.ofNat.{u_3} G₀ 0 (OfNat.mk.{u_3} G₀ 0 (Zero.zero.{u_3} G₀ (MulZeroClass.toHasZero.{u_3} G₀ _inst_1)))) x y
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.48 : MulZeroClass.{u_1} G₀] (x : G₀) (y : G₀), SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.48) (OfNat.ofNat.{u_1} G₀ 0 (Zero.toOfNat0.{u_1} G₀ (MulZeroClass.toZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.48))) x y
Case conversion may be inaccurate. Consider using '#align semiconj_by.zero_left SemiconjBy.zero_leftₓ'. -/
@[simp]
theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by
  simp only [SemiconjBy, mul_zero, zero_mul]
#align semiconj_by.zero_left SemiconjBy.zero_left

variable [GroupWithZero G₀] {a x y x' y' : G₀}

/- warning: semiconj_by.inv_symm_left_iff₀ -> SemiconjBy.inv_symm_left_iff₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_1 : GroupWithZero.{u_3} G₀] {a : G₀} {x : G₀} {y : G₀}, Iff (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) (Inv.inv.{u_3} G₀ (DivInvMonoid.toHasInv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_1)) a) x y) (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) a y x)
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.92 : GroupWithZero.{u_1} G₀] {a : G₀} {x : G₀} {y : G₀}, Iff (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.92)))) (Inv.inv.{u_1} G₀ (GroupWithZero.toInv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.92) a) x y) (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.92)))) a y x)
Case conversion may be inaccurate. Consider using '#align semiconj_by.inv_symm_left_iff₀ SemiconjBy.inv_symm_left_iff₀ₓ'. -/
@[simp]
theorem inv_symm_left_iff₀ : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x :=
  Classical.by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _
#align semiconj_by.inv_symm_left_iff₀ SemiconjBy.inv_symm_left_iff₀

/- warning: semiconj_by.inv_symm_left₀ -> SemiconjBy.inv_symm_left₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_1 : GroupWithZero.{u_3} G₀] {a : G₀} {x : G₀} {y : G₀}, (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) a x y) -> (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) (Inv.inv.{u_3} G₀ (DivInvMonoid.toHasInv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_1)) a) y x)
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.151 : GroupWithZero.{u_1} G₀] {a : G₀} {x : G₀} {y : G₀}, (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.151)))) a x y) -> (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.151)))) (Inv.inv.{u_1} G₀ (GroupWithZero.toInv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.151) a) y x)
Case conversion may be inaccurate. Consider using '#align semiconj_by.inv_symm_left₀ SemiconjBy.inv_symm_left₀ₓ'. -/
theorem inv_symm_left₀ (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x :=
  SemiconjBy.inv_symm_left_iff₀.2 h
#align semiconj_by.inv_symm_left₀ SemiconjBy.inv_symm_left₀

/- warning: semiconj_by.inv_right₀ -> SemiconjBy.inv_right₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_1 : GroupWithZero.{u_3} G₀] {a : G₀} {x : G₀} {y : G₀}, (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) a x y) -> (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) a (Inv.inv.{u_3} G₀ (DivInvMonoid.toHasInv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_1)) x) (Inv.inv.{u_3} G₀ (DivInvMonoid.toHasInv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_1)) y))
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.181 : GroupWithZero.{u_1} G₀] {a : G₀} {x : G₀} {y : G₀}, (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.181)))) a x y) -> (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.181)))) a (Inv.inv.{u_1} G₀ (GroupWithZero.toInv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.181) x) (Inv.inv.{u_1} G₀ (GroupWithZero.toInv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.181) y))
Case conversion may be inaccurate. Consider using '#align semiconj_by.inv_right₀ SemiconjBy.inv_right₀ₓ'. -/
theorem inv_right₀ (h : SemiconjBy a x y) : SemiconjBy a x⁻¹ y⁻¹ := by
  by_cases ha : a = 0
  · simp only [ha, zero_left]
  by_cases hx : x = 0
  · subst x
    simp only [SemiconjBy, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h
    simp [h.resolve_right ha]
  · have := mul_ne_zero ha hx
    rw [h.eq, mul_ne_zero_iff] at this
    exact @units_inv_right _ _ _ (Units.mk0 x hx) (Units.mk0 y this.1) h
#align semiconj_by.inv_right₀ SemiconjBy.inv_right₀

/- warning: semiconj_by.inv_right_iff₀ -> SemiconjBy.inv_right_iff₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_1 : GroupWithZero.{u_3} G₀] {a : G₀} {x : G₀} {y : G₀}, Iff (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) a (Inv.inv.{u_3} G₀ (DivInvMonoid.toHasInv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_1)) x) (Inv.inv.{u_3} G₀ (DivInvMonoid.toHasInv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_1)) y)) (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) a x y)
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.368 : GroupWithZero.{u_1} G₀] {a : G₀} {x : G₀} {y : G₀}, Iff (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.368)))) a (Inv.inv.{u_1} G₀ (GroupWithZero.toInv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.368) x) (Inv.inv.{u_1} G₀ (GroupWithZero.toInv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.368) y)) (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.368)))) a x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.inv_right_iff₀ SemiconjBy.inv_right_iff₀ₓ'. -/
@[simp]
theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  ⟨fun h => inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩
#align semiconj_by.inv_right_iff₀ SemiconjBy.inv_right_iff₀

/- warning: semiconj_by.div_right -> SemiconjBy.div_right is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_1 : GroupWithZero.{u_3} G₀] {a : G₀} {x : G₀} {y : G₀} {x' : G₀} {y' : G₀}, (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) a x y) -> (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) a x' y') -> (SemiconjBy.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_1)))) a (HDiv.hDiv.{u_3, u_3, u_3} G₀ G₀ G₀ (instHDiv.{u_3} G₀ (DivInvMonoid.toHasDiv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_1))) x x') (HDiv.hDiv.{u_3, u_3, u_3} G₀ G₀ G₀ (instHDiv.{u_3} G₀ (DivInvMonoid.toHasDiv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_1))) y y'))
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.419 : GroupWithZero.{u_1} G₀] {a : G₀} {x : G₀} {y : G₀} {x' : G₀} {y' : G₀}, (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.419)))) a x y) -> (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.419)))) a x' y') -> (SemiconjBy.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.419)))) a (HDiv.hDiv.{u_1, u_1, u_1} G₀ G₀ G₀ (instHDiv.{u_1} G₀ (GroupWithZero.toDiv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.419)) x x') (HDiv.hDiv.{u_1, u_1, u_1} G₀ G₀ G₀ (instHDiv.{u_1} G₀ (GroupWithZero.toDiv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Semiconj._hyg.419)) y y'))
Case conversion may be inaccurate. Consider using '#align semiconj_by.div_right SemiconjBy.div_rightₓ'. -/
theorem div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x / x') (y / y') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h.mul_right h'.inv_right₀
#align semiconj_by.div_right SemiconjBy.div_right

end SemiconjBy

