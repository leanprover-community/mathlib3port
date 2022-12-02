/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.GroupWithZero.Semiconj
import Mathbin.Algebra.Group.Commute
import Mathbin.Tactic.Nontriviality

/-!
# Lemmas about commuting elements in a `monoid_with_zero` or a `group_with_zero`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/762
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α M₀ G₀ M₀' G₀' F F' : Type _}

variable [MonoidWithZero M₀]

namespace Ring

open Classical

/- warning: ring.mul_inverse_rev' -> Ring.mul_inverse_rev' is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_2}} [_inst_1 : MonoidWithZero.{u_2} M₀] {a : M₀} {b : M₀}, (Commute.{u_2} M₀ (MulZeroClass.toHasMul.{u_2} M₀ (MulZeroOneClass.toMulZeroClass.{u_2} M₀ (MonoidWithZero.toMulZeroOneClass.{u_2} M₀ _inst_1))) a b) -> (Eq.{succ u_2} M₀ (Ring.inverse.{u_2} M₀ _inst_1 (HMul.hMul.{u_2, u_2, u_2} M₀ M₀ M₀ (instHMul.{u_2} M₀ (MulZeroClass.toHasMul.{u_2} M₀ (MulZeroOneClass.toMulZeroClass.{u_2} M₀ (MonoidWithZero.toMulZeroOneClass.{u_2} M₀ _inst_1)))) a b)) (HMul.hMul.{u_2, u_2, u_2} M₀ M₀ M₀ (instHMul.{u_2} M₀ (MulZeroClass.toHasMul.{u_2} M₀ (MulZeroOneClass.toMulZeroClass.{u_2} M₀ (MonoidWithZero.toMulZeroOneClass.{u_2} M₀ _inst_1)))) (Ring.inverse.{u_2} M₀ _inst_1 b) (Ring.inverse.{u_2} M₀ _inst_1 a)))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.40 : MonoidWithZero.{u_1} M₀] {a : M₀} {b : M₀}, (Commute.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.40))) a b) -> (Eq.{succ u_1} M₀ (Ring.inverse.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.40 (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.40)))) a b)) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.40)))) (Ring.inverse.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.40 b) (Ring.inverse.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.40 a)))
Case conversion may be inaccurate. Consider using '#align ring.mul_inverse_rev' Ring.mul_inverse_rev'ₓ'. -/
theorem mul_inverse_rev' {a b : M₀} (h : Commute a b) : inverse (a * b) = inverse b * inverse a :=
  by 
  by_cases hab : IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.is_unit_mul_iff.mp hab
    rw [← Units.val_mul, inverse_unit, inverse_unit, inverse_unit, ← Units.val_mul, mul_inv_rev]
  obtain ha | hb := not_and_distrib.mp (mt h.is_unit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]
#align ring.mul_inverse_rev' Ring.mul_inverse_rev'

/- warning: ring.mul_inverse_rev -> Ring.mul_inverse_rev is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_1}} [_inst_2 : CommMonoidWithZero.{u_1} M₀] (a : M₀) (b : M₀), Eq.{succ u_1} M₀ (Ring.inverse.{u_1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_2) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_2))))) a b)) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toHasMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_2))))) (Ring.inverse.{u_1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_2) b) (Ring.inverse.{u_1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u_1} M₀ _inst_2) a))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.228 : CommMonoidWithZero.{u_1} M₀] (a : M₀) (b : M₀), Eq.{succ u_1} M₀ (Ring.inverse.{u_1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.228) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.228))))) a b)) (HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (instHMul.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.228))))) (Ring.inverse.{u_1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.228) b) (Ring.inverse.{u_1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.228) a))
Case conversion may be inaccurate. Consider using '#align ring.mul_inverse_rev Ring.mul_inverse_revₓ'. -/
theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) :
    Ring.inverse (a * b) = inverse b * inverse a :=
  mul_inverse_rev' (Commute.all _ _)
#align ring.mul_inverse_rev Ring.mul_inverse_rev

end Ring

/- warning: commute.ring_inverse_ring_inverse -> Commute.ring_inverse_ring_inverse is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u_2}} [_inst_1 : MonoidWithZero.{u_2} M₀] {a : M₀} {b : M₀}, (Commute.{u_2} M₀ (MulZeroClass.toHasMul.{u_2} M₀ (MulZeroOneClass.toMulZeroClass.{u_2} M₀ (MonoidWithZero.toMulZeroOneClass.{u_2} M₀ _inst_1))) a b) -> (Commute.{u_2} M₀ (MulZeroClass.toHasMul.{u_2} M₀ (MulZeroOneClass.toMulZeroClass.{u_2} M₀ (MonoidWithZero.toMulZeroOneClass.{u_2} M₀ _inst_1))) (Ring.inverse.{u_2} M₀ _inst_1 a) (Ring.inverse.{u_2} M₀ _inst_1 b))
but is expected to have type
  forall {M₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.268 : MonoidWithZero.{u_1} M₀] {a : M₀} {b : M₀}, (Commute.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.268))) a b) -> (Commute.{u_1} M₀ (MulZeroClass.toMul.{u_1} M₀ (MulZeroOneClass.toMulZeroClass.{u_1} M₀ (MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.268))) (Ring.inverse.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.268 a) (Ring.inverse.{u_1} M₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.268 b))
Case conversion may be inaccurate. Consider using '#align commute.ring_inverse_ring_inverse Commute.ring_inverse_ring_inverseₓ'. -/
theorem Commute.ring_inverse_ring_inverse {a b : M₀} (h : Commute a b) :
    Commute (Ring.inverse a) (Ring.inverse b) :=
  (Ring.mul_inverse_rev' h.symm).symm.trans <|
    (congr_arg _ h.symm.Eq).trans <| Ring.mul_inverse_rev' h
#align commute.ring_inverse_ring_inverse Commute.ring_inverse_ring_inverse

namespace Commute

/- warning: commute.zero_right -> Commute.zero_right is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : MulZeroClass.{u_3} G₀] (a : G₀), Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ _inst_2) a (OfNat.ofNat.{u_3} G₀ 0 (OfNat.mk.{u_3} G₀ 0 (Zero.zero.{u_3} G₀ (MulZeroClass.toHasZero.{u_3} G₀ _inst_2))))
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.316 : MulZeroClass.{u_1} G₀] (a : G₀), Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.316) a (OfNat.ofNat.{u_1} G₀ 0 (Zero.toOfNat0.{u_1} G₀ (MulZeroClass.toZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.316)))
Case conversion may be inaccurate. Consider using '#align commute.zero_right Commute.zero_rightₓ'. -/
@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a
#align commute.zero_right Commute.zero_right

/- warning: commute.zero_left -> Commute.zero_left is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : MulZeroClass.{u_3} G₀] (a : G₀), Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ _inst_2) (OfNat.ofNat.{u_3} G₀ 0 (OfNat.mk.{u_3} G₀ 0 (Zero.zero.{u_3} G₀ (MulZeroClass.toHasZero.{u_3} G₀ _inst_2)))) a
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.337 : MulZeroClass.{u_1} G₀] (a : G₀), Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.337) (OfNat.ofNat.{u_1} G₀ 0 (Zero.toOfNat0.{u_1} G₀ (MulZeroClass.toZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.337))) a
Case conversion may be inaccurate. Consider using '#align commute.zero_left Commute.zero_leftₓ'. -/
@[simp]
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a
#align commute.zero_left Commute.zero_left

variable [GroupWithZero G₀] {a b c : G₀}

/- warning: commute.inv_left_iff₀ -> Commute.inv_left_iff₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : GroupWithZero.{u_3} G₀] {a : G₀} {b : G₀}, Iff (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) (Inv.inv.{u_3} G₀ (DivInvMonoid.toHasInv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_2)) a) b) (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) a b)
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.380 : GroupWithZero.{u_1} G₀] {a : G₀} {b : G₀}, Iff (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.380)))) (Inv.inv.{u_1} G₀ (GroupWithZero.toInv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.380) a) b) (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.380)))) a b)
Case conversion may be inaccurate. Consider using '#align commute.inv_left_iff₀ Commute.inv_left_iff₀ₓ'. -/
@[simp]
theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff₀
#align commute.inv_left_iff₀ Commute.inv_left_iff₀

/- warning: commute.inv_left₀ -> Commute.inv_left₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : GroupWithZero.{u_3} G₀] {a : G₀} {b : G₀}, (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) a b) -> (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) (Inv.inv.{u_3} G₀ (DivInvMonoid.toHasInv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_2)) a) b)
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.411 : GroupWithZero.{u_1} G₀] {a : G₀} {b : G₀}, (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.411)))) a b) -> (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.411)))) (Inv.inv.{u_1} G₀ (GroupWithZero.toInv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.411) a) b)
Case conversion may be inaccurate. Consider using '#align commute.inv_left₀ Commute.inv_left₀ₓ'. -/
theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b :=
  inv_left_iff₀.2 h
#align commute.inv_left₀ Commute.inv_left₀

/- warning: commute.inv_right_iff₀ -> Commute.inv_right_iff₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : GroupWithZero.{u_3} G₀] {a : G₀} {b : G₀}, Iff (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) a (Inv.inv.{u_3} G₀ (DivInvMonoid.toHasInv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_2)) b)) (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) a b)
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.440 : GroupWithZero.{u_1} G₀] {a : G₀} {b : G₀}, Iff (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.440)))) a (Inv.inv.{u_1} G₀ (GroupWithZero.toInv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.440) b)) (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.440)))) a b)
Case conversion may be inaccurate. Consider using '#align commute.inv_right_iff₀ Commute.inv_right_iff₀ₓ'. -/
@[simp]
theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff₀
#align commute.inv_right_iff₀ Commute.inv_right_iff₀

/- warning: commute.inv_right₀ -> Commute.inv_right₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : GroupWithZero.{u_3} G₀] {a : G₀} {b : G₀}, (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) a b) -> (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) a (Inv.inv.{u_3} G₀ (DivInvMonoid.toHasInv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_2)) b))
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.471 : GroupWithZero.{u_1} G₀] {a : G₀} {b : G₀}, (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.471)))) a b) -> (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.471)))) a (Inv.inv.{u_1} G₀ (GroupWithZero.toInv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.471) b))
Case conversion may be inaccurate. Consider using '#align commute.inv_right₀ Commute.inv_right₀ₓ'. -/
theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ :=
  inv_right_iff₀.2 h
#align commute.inv_right₀ Commute.inv_right₀

/- warning: commute.div_right -> Commute.div_right is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : GroupWithZero.{u_3} G₀] {a : G₀} {b : G₀} {c : G₀}, (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) a b) -> (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) a c) -> (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) a (HDiv.hDiv.{u_3, u_3, u_3} G₀ G₀ G₀ (instHDiv.{u_3} G₀ (DivInvMonoid.toHasDiv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_2))) b c))
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.500 : GroupWithZero.{u_1} G₀] {a : G₀} {b : G₀} {c : G₀}, (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.500)))) a b) -> (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.500)))) a c) -> (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.500)))) a (HDiv.hDiv.{u_1, u_1, u_1} G₀ G₀ G₀ (instHDiv.{u_1} G₀ (GroupWithZero.toDiv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.500)) b c))
Case conversion may be inaccurate. Consider using '#align commute.div_right Commute.div_rightₓ'. -/
@[simp]
theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  hab.div_right hac
#align commute.div_right Commute.div_right

/- warning: commute.div_left -> Commute.div_left is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : GroupWithZero.{u_3} G₀] {a : G₀} {b : G₀} {c : G₀}, (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) a c) -> (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) b c) -> (Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ (MulZeroOneClass.toMulZeroClass.{u_3} G₀ (MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (GroupWithZero.toMonoidWithZero.{u_3} G₀ _inst_2)))) (HDiv.hDiv.{u_3, u_3, u_3} G₀ G₀ G₀ (instHDiv.{u_3} G₀ (DivInvMonoid.toHasDiv.{u_3} G₀ (GroupWithZero.toDivInvMonoid.{u_3} G₀ _inst_2))) a b) c)
but is expected to have type
  forall {G₀ : Type.{u_1}} [inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.536 : GroupWithZero.{u_1} G₀] {a : G₀} {b : G₀} {c : G₀}, (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.536)))) a c) -> (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.536)))) b c) -> (Commute.{u_1} G₀ (MulZeroClass.toMul.{u_1} G₀ (MulZeroOneClass.toMulZeroClass.{u_1} G₀ (MonoidWithZero.toMulZeroOneClass.{u_1} G₀ (GroupWithZero.toMonoidWithZero.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.536)))) (HDiv.hDiv.{u_1, u_1, u_1} G₀ G₀ G₀ (instHDiv.{u_1} G₀ (GroupWithZero.toDiv.{u_1} G₀ inst._@.Mathlib.Algebra.GroupWithZero.Commute._hyg.536)) a b) c)
Case conversion may be inaccurate. Consider using '#align commute.div_left Commute.div_leftₓ'. -/
@[simp]
theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by
  rw [div_eq_mul_inv]
  exact hac.mul_left hbc.inv_left₀
#align commute.div_left Commute.div_left

end Commute

