/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes

! This file was ported from Lean 3 source module algebra.group.conj
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Semiconj
import Mathbin.Algebra.GroupWithZero.Basic
import Mathbin.Algebra.Hom.Aut
import Mathbin.Algebra.Hom.Group

/-!
# Conjugacy of group elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

See also `mul_aut.conj` and `quandle.conj`.
-/


universe u v

variable {α : Type u} {β : Type v}

section Monoid

variable [Monoid α] [Monoid β]

#print IsConj /-
/-- We say that `a` is conjugate to `b` if for some unit `c` we have `c * a * c⁻¹ = b`. -/
def IsConj (a b : α) :=
  ∃ c : αˣ, SemiconjBy (↑c) a b
#align is_conj IsConj
-/

#print IsConj.refl /-
@[refl]
theorem IsConj.refl (a : α) : IsConj a a :=
  ⟨1, SemiconjBy.one_left a⟩
#align is_conj.refl IsConj.refl
-/

#print IsConj.symm /-
@[symm]
theorem IsConj.symm {a b : α} : IsConj a b → IsConj b a
  | ⟨c, hc⟩ => ⟨c⁻¹, hc.units_inv_symm_left⟩
#align is_conj.symm IsConj.symm
-/

#print isConj_comm /-
theorem isConj_comm {g h : α} : IsConj g h ↔ IsConj h g :=
  ⟨IsConj.symm, IsConj.symm⟩
#align is_conj_comm isConj_comm
-/

#print IsConj.trans /-
@[trans]
theorem IsConj.trans {a b c : α} : IsConj a b → IsConj b c → IsConj a c
  | ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩ => ⟨c₂ * c₁, hc₂.mul_left hc₁⟩
#align is_conj.trans IsConj.trans
-/

#print isConj_iff_eq /-
@[simp]
theorem isConj_iff_eq {α : Type _} [CommMonoid α] {a b : α} : IsConj a b ↔ a = b :=
  ⟨fun ⟨c, hc⟩ =>
    by
    rw [SemiconjBy, mul_comm, ← Units.mul_inv_eq_iff_eq_mul, mul_assoc, c.mul_inv, mul_one] at hc
    exact hc, fun h => by rw [h]⟩
#align is_conj_iff_eq isConj_iff_eq
-/

/- warning: monoid_hom.map_is_conj -> MonoidHom.map_isConj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} β] (f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) {a : α} {b : α}, (IsConj.{u1} α _inst_1 a b) -> (IsConj.{u2} β _inst_2 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) f a) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) f b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} β] (f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) {a : α} {b : α}, (IsConj.{u1} α _inst_1 a b) -> (IsConj.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) a) _inst_2 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2) (MonoidHom.monoidHomClass.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)))) f a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2) (MonoidHom.monoidHomClass.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)))) f b))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_is_conj MonoidHom.map_isConjₓ'. -/
protected theorem MonoidHom.map_isConj (f : α →* β) {a b : α} : IsConj a b → IsConj (f a) (f b)
  | ⟨c, hc⟩ => ⟨Units.map f c, by rw [Units.coe_map, SemiconjBy, ← f.map_mul, hc.eq, f.map_mul]⟩
#align monoid_hom.map_is_conj MonoidHom.map_isConj

end Monoid

section CancelMonoid

variable [CancelMonoid α]

/- warning: is_conj_one_right -> isConj_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelMonoid.{u1} α] {a : α}, Iff (IsConj.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1))))))) a) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelMonoid.{u1} α] {a : α}, Iff (IsConj.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (RightCancelMonoid.toOne.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1)))) a) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (RightCancelMonoid.toOne.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align is_conj_one_right isConj_one_rightₓ'. -/
-- These lemmas hold for `right_cancel_monoid` with the current proofs, but for the sake of
-- not duplicating code (these lemmas also hold for `left_cancel_monoids`) we leave these
-- not generalised.
@[simp]
theorem isConj_one_right {a : α} : IsConj 1 a ↔ a = 1 :=
  ⟨fun ⟨c, hc⟩ => mul_right_cancel (hc.symm.trans ((mul_one _).trans (one_mul _).symm)), fun h => by
    rw [h]⟩
#align is_conj_one_right isConj_one_right

/- warning: is_conj_one_left -> isConj_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelMonoid.{u1} α] {a : α}, Iff (IsConj.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1)))))))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelMonoid.{u1} α] {a : α}, Iff (IsConj.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (RightCancelMonoid.toOne.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1))))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (RightCancelMonoid.toOne.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align is_conj_one_left isConj_one_leftₓ'. -/
@[simp]
theorem isConj_one_left {a : α} : IsConj a 1 ↔ a = 1 :=
  calc
    IsConj a 1 ↔ IsConj 1 a := ⟨IsConj.symm, IsConj.symm⟩
    _ ↔ a = 1 := isConj_one_right
    
#align is_conj_one_left isConj_one_left

end CancelMonoid

section Group

variable [Group α]

/- warning: is_conj_iff -> isConj_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Iff (IsConj.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a b) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) c)) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Iff (IsConj.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a b) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) c a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) c)) b))
Case conversion may be inaccurate. Consider using '#align is_conj_iff isConj_iffₓ'. -/
@[simp]
theorem isConj_iff {a b : α} : IsConj a b ↔ ∃ c : α, c * a * c⁻¹ = b :=
  ⟨fun ⟨c, hc⟩ => ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, fun ⟨c, hc⟩ =>
    ⟨⟨c, c⁻¹, mul_inv_self c, inv_mul_self c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩
#align is_conj_iff isConj_iff

/- warning: conj_inv -> conj_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))
Case conversion may be inaccurate. Consider using '#align conj_inv conj_invₓ'. -/
@[simp]
theorem conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ :=
  ((MulAut.conj b).map_inv a).symm
#align conj_inv conj_inv

/- warning: conj_mul -> conj_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a c)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α} {c : α}, Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b c) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a c)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))
Case conversion may be inaccurate. Consider using '#align conj_mul conj_mulₓ'. -/
@[simp]
theorem conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹ :=
  ((MulAut.conj b).map_mul a c).symm
#align conj_mul conj_mul

/- warning: conj_pow -> conj_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {i : Nat} {a : α} {b : α}, Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) i) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) b i)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {i : Nat} {a : α} {b : α}, Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) i) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) b i)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align conj_pow conj_powₓ'. -/
@[simp]
theorem conj_pow {i : ℕ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ :=
  by
  induction' i with i hi
  · simp
  · simp [pow_succ, hi]
#align conj_pow conj_pow

/- warning: conj_zpow -> conj_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {i : Int} {a : α} {b : α}, Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) i) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b i)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {i : Int} {a : α} {b : α}, Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) i) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) b i)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align conj_zpow conj_zpowₓ'. -/
@[simp]
theorem conj_zpow {i : ℤ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ :=
  by
  induction i
  · simp
  · simp [zpow_negSucc, conj_pow]
#align conj_zpow conj_zpow

/- warning: conj_injective -> conj_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {x : α}, Function.Injective.{succ u1, succ u1} α α (fun (g : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x g) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {x : α}, Function.Injective.{succ u1, succ u1} α α (fun (g : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x g) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) x))
Case conversion may be inaccurate. Consider using '#align conj_injective conj_injectiveₓ'. -/
theorem conj_injective {x : α} : Function.Injective fun g : α => x * g * x⁻¹ :=
  (MulAut.conj x).Injective
#align conj_injective conj_injective

end Group

/- warning: is_conj_iff₀ -> isConj_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] {a : α} {b : α}, Iff (IsConj.{u1} α (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) a b) (Exists.{succ u1} α (fun (c : α) => And (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) c a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) c)) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] {a : α} {b : α}, Iff (IsConj.{u1} α (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) a b) (Exists.{succ u1} α (fun (c : α) => And (Ne.{succ u1} α c (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) c a) (Inv.inv.{u1} α (GroupWithZero.toInv.{u1} α _inst_1) c)) b)))
Case conversion may be inaccurate. Consider using '#align is_conj_iff₀ isConj_iff₀ₓ'. -/
@[simp]
theorem isConj_iff₀ [GroupWithZero α] {a b : α} : IsConj a b ↔ ∃ c : α, c ≠ 0 ∧ c * a * c⁻¹ = b :=
  ⟨fun ⟨c, hc⟩ =>
    ⟨c, by
      rw [← Units.val_inv_eq_inv_val, Units.mul_inv_eq_iff_eq_mul]
      exact ⟨c.ne_zero, hc⟩⟩,
    fun ⟨c, c0, hc⟩ =>
    ⟨Units.mk0 c c0,
      by
      rw [SemiconjBy, ← Units.mul_inv_eq_iff_eq_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      exact hc⟩⟩
#align is_conj_iff₀ isConj_iff₀

namespace IsConj

#print IsConj.setoid /-
/- This small quotient API is largely copied from the API of `associates`;
where possible, try to keep them in sync -/
/-- The setoid of the relation `is_conj` iff there is a unit `u` such that `u * x = y * u` -/
protected def setoid (α : Type _) [Monoid α] : Setoid α
    where
  R := IsConj
  iseqv := ⟨IsConj.refl, fun a b => IsConj.symm, fun a b c => IsConj.trans⟩
#align is_conj.setoid IsConj.setoid
-/

end IsConj

attribute [local instance] IsConj.setoid

#print ConjClasses /-
/-- The quotient type of conjugacy classes of a group. -/
def ConjClasses (α : Type _) [Monoid α] : Type _ :=
  Quotient (IsConj.setoid α)
#align conj_classes ConjClasses
-/

namespace ConjClasses

section Monoid

variable [Monoid α] [Monoid β]

#print ConjClasses.mk /-
/-- The canonical quotient map from a monoid `α` into the `conj_classes` of `α` -/
protected def mk {α : Type _} [Monoid α] (a : α) : ConjClasses α :=
  ⟦a⟧
#align conj_classes.mk ConjClasses.mk
-/

instance : Inhabited (ConjClasses α) :=
  ⟨⟦1⟧⟩

#print ConjClasses.mk_eq_mk_iff_isConj /-
theorem mk_eq_mk_iff_isConj {a b : α} : ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b :=
  Iff.intro Quotient.exact Quot.sound
#align conj_classes.mk_eq_mk_iff_is_conj ConjClasses.mk_eq_mk_iff_isConj
-/

#print ConjClasses.quotient_mk_eq_mk /-
theorem quotient_mk_eq_mk (a : α) : ⟦a⟧ = ConjClasses.mk a :=
  rfl
#align conj_classes.quotient_mk_eq_mk ConjClasses.quotient_mk_eq_mk
-/

#print ConjClasses.quot_mk_eq_mk /-
theorem quot_mk_eq_mk (a : α) : Quot.mk Setoid.r a = ConjClasses.mk a :=
  rfl
#align conj_classes.quot_mk_eq_mk ConjClasses.quot_mk_eq_mk
-/

#print ConjClasses.forall_isConj /-
theorem forall_isConj {p : ConjClasses α → Prop} : (∀ a, p a) ↔ ∀ a, p (ConjClasses.mk a) :=
  Iff.intro (fun h a => h _) fun h a => Quotient.induction_on a h
#align conj_classes.forall_is_conj ConjClasses.forall_isConj
-/

#print ConjClasses.mk_surjective /-
theorem mk_surjective : Function.Surjective (@ConjClasses.mk α _) :=
  forall_isConj.2 fun a => ⟨a, rfl⟩
#align conj_classes.mk_surjective ConjClasses.mk_surjective
-/

instance : One (ConjClasses α) :=
  ⟨⟦1⟧⟩

/- warning: conj_classes.one_eq_mk_one -> ConjClasses.one_eq_mk_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Eq.{succ u1} (ConjClasses.{u1} α _inst_1) (OfNat.ofNat.{u1} (ConjClasses.{u1} α _inst_1) 1 (OfNat.mk.{u1} (ConjClasses.{u1} α _inst_1) 1 (One.one.{u1} (ConjClasses.{u1} α _inst_1) (ConjClasses.hasOne.{u1} α _inst_1)))) (ConjClasses.mk.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Eq.{succ u1} (ConjClasses.{u1} α _inst_1) (OfNat.ofNat.{u1} (ConjClasses.{u1} α _inst_1) 1 (One.toOfNat1.{u1} (ConjClasses.{u1} α _inst_1) (ConjClasses.instOneConjClasses.{u1} α _inst_1))) (ConjClasses.mk.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align conj_classes.one_eq_mk_one ConjClasses.one_eq_mk_oneₓ'. -/
theorem one_eq_mk_one : (1 : ConjClasses α) = ConjClasses.mk 1 :=
  rfl
#align conj_classes.one_eq_mk_one ConjClasses.one_eq_mk_one

#print ConjClasses.exists_rep /-
theorem exists_rep (a : ConjClasses α) : ∃ a0 : α, ConjClasses.mk a0 = a :=
  Quot.exists_rep a
#align conj_classes.exists_rep ConjClasses.exists_rep
-/

#print ConjClasses.map /-
/-- A `monoid_hom` maps conjugacy classes of one group to conjugacy classes of another. -/
def map (f : α →* β) : ConjClasses α → ConjClasses β :=
  Quotient.lift (ConjClasses.mk ∘ f) fun a b ab => mk_eq_mk_iff_isConj.2 (f.map_is_conj ab)
#align conj_classes.map ConjClasses.map
-/

/- warning: conj_classes.map_surjective -> ConjClasses.map_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} β] {f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) f)) -> (Function.Surjective.{succ u1, succ u2} (ConjClasses.{u1} α _inst_1) (ConjClasses.{u2} β _inst_2) (ConjClasses.map.{u1, u2} α β _inst_1 _inst_2 f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} β] {f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)}, (Function.Surjective.{succ u1, succ u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)) α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2) (MonoidHom.monoidHomClass.{u1, u2} α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)))) f)) -> (Function.Surjective.{succ u1, succ u2} (ConjClasses.{u1} α _inst_1) (ConjClasses.{u2} β _inst_2) (ConjClasses.map.{u1, u2} α β _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align conj_classes.map_surjective ConjClasses.map_surjectiveₓ'. -/
theorem map_surjective {f : α →* β} (hf : Function.Surjective f) :
    Function.Surjective (ConjClasses.map f) :=
  by
  intro b
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨ConjClasses.mk a, rfl⟩
#align conj_classes.map_surjective ConjClasses.map_surjective

library_note "slow-failing instance priority"/--
Certain instances trigger further searches when they are considered as candidate instances;
these instances should be assigned a priority lower than the default of 1000 (for example, 900).

The conditions for this rule are as follows:
 * a class `C` has instances `instT : C T` and `instT' : C T'`
 * types `T` and `T'` are both specializations of another type `S`
 * the parameters supplied to `S` to produce `T` are not (fully) determined by `instT`,
   instead they have to be found by instance search
If those conditions hold, the instance `instT` should be assigned lower priority.

For example, suppose the search for an instance of `decidable_eq (multiset α)` tries the
candidate instance `con.quotient.decidable_eq (c : con M) : decidable_eq c.quotient`.
Since `multiset` and `con.quotient` are both quotient types, unification will check
that the relations `list.perm` and `c.to_setoid.r` unify. However, `c.to_setoid` depends on
a `has_mul M` instance, so this unification triggers a search for `has_mul (list α)`;
this will traverse all subclasses of `has_mul` before failing.
On the other hand, the search for an instance of `decidable_eq (con.quotient c)` for `c : con M`
can quickly reject the candidate instance `multiset.has_decidable_eq` because the type of
`list.perm : list ?m_1 → list ?m_1 → Prop` does not unify with `M → M → Prop`.
Therefore, we should assign `con.quotient.decidable_eq` a lower priority because it fails slowly.
(In terms of the rules above, `C := decidable_eq`, `T := con.quotient`,
`instT := con.quotient.decidable_eq`, `T' := multiset`, `instT' := multiset.has_decidable_eq`,
and `S := quot`.)

If the type involved is a free variable (rather than an instantiation of some type `S`),
the instance priority should be even lower, see Note [lower instance priority].
-/


-- see Note [slow-failing instance priority]
instance (priority := 900) [DecidableRel (IsConj : α → α → Prop)] : DecidableEq (ConjClasses α) :=
  Quotient.decidableEq

end Monoid

section CommMonoid

variable [CommMonoid α]

#print ConjClasses.mk_injective /-
theorem mk_injective : Function.Injective (@ConjClasses.mk α _) := fun _ _ =>
  (mk_eq_mk_iff_isConj.trans isConj_iff_eq).1
#align conj_classes.mk_injective ConjClasses.mk_injective
-/

#print ConjClasses.mk_bijective /-
theorem mk_bijective : Function.Bijective (@ConjClasses.mk α _) :=
  ⟨mk_injective, mk_surjective⟩
#align conj_classes.mk_bijective ConjClasses.mk_bijective
-/

#print ConjClasses.mkEquiv /-
/-- The bijection between a `comm_group` and its `conj_classes`. -/
def mkEquiv : α ≃ ConjClasses α :=
  ⟨ConjClasses.mk, Quotient.lift id fun (a : α) b => isConj_iff_eq.1, Quotient.lift_mk _ _,
    by
    rw [Function.RightInverse, Function.LeftInverse, forall_is_conj]
    intro x
    rw [← quotient_mk_eq_mk, ← quotient_mk_eq_mk, Quotient.lift_mk, id.def]⟩
#align conj_classes.mk_equiv ConjClasses.mkEquiv
-/

end CommMonoid

end ConjClasses

section Monoid

variable [Monoid α]

#print conjugatesOf /-
/-- Given an element `a`, `conjugates a` is the set of conjugates. -/
def conjugatesOf (a : α) : Set α :=
  { b | IsConj a b }
#align conjugates_of conjugatesOf
-/

#print mem_conjugatesOf_self /-
theorem mem_conjugatesOf_self {a : α} : a ∈ conjugatesOf a :=
  IsConj.refl _
#align mem_conjugates_of_self mem_conjugatesOf_self
-/

#print IsConj.conjugatesOf_eq /-
theorem IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a b) : conjugatesOf a = conjugatesOf b :=
  Set.ext fun g => ⟨fun ag => ab.symm.trans ag, fun bg => ab.trans bg⟩
#align is_conj.conjugates_of_eq IsConj.conjugatesOf_eq
-/

#print isConj_iff_conjugatesOf_eq /-
theorem isConj_iff_conjugatesOf_eq {a b : α} : IsConj a b ↔ conjugatesOf a = conjugatesOf b :=
  ⟨IsConj.conjugatesOf_eq, fun h =>
    by
    have ha := mem_conjugatesOf_self
    rwa [← h] at ha⟩
#align is_conj_iff_conjugates_of_eq isConj_iff_conjugatesOf_eq
-/

end Monoid

namespace ConjClasses

variable [Monoid α]

attribute [local instance] IsConj.setoid

#print ConjClasses.carrier /-
/-- Given a conjugacy class `a`, `carrier a` is the set it represents. -/
def carrier : ConjClasses α → Set α :=
  Quotient.lift conjugatesOf fun (a : α) b ab => IsConj.conjugatesOf_eq ab
#align conj_classes.carrier ConjClasses.carrier
-/

#print ConjClasses.mem_carrier_mk /-
theorem mem_carrier_mk {a : α} : a ∈ carrier (ConjClasses.mk a) :=
  IsConj.refl _
#align conj_classes.mem_carrier_mk ConjClasses.mem_carrier_mk
-/

#print ConjClasses.mem_carrier_iff_mk_eq /-
theorem mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} : a ∈ carrier b ↔ ConjClasses.mk a = b :=
  by
  revert b
  rw [forall_is_conj]
  intro b
  rw [carrier, eq_comm, mk_eq_mk_iff_is_conj, ← quotient_mk_eq_mk, Quotient.lift_mk]
  rfl
#align conj_classes.mem_carrier_iff_mk_eq ConjClasses.mem_carrier_iff_mk_eq
-/

#print ConjClasses.carrier_eq_preimage_mk /-
theorem carrier_eq_preimage_mk {a : ConjClasses α} : a.carrier = ConjClasses.mk ⁻¹' {a} :=
  Set.ext fun x => mem_carrier_iff_mk_eq
#align conj_classes.carrier_eq_preimage_mk ConjClasses.carrier_eq_preimage_mk
-/

end ConjClasses

assert_not_exists multiset

