/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.perm.option
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Perm
import Mathbin.GroupTheory.Perm.Sign
import Mathbin.Logic.Equiv.Option

/-!
# Permutations of `option α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Equiv

/- warning: equiv.option_congr_one -> Equiv.optionCongr_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.optionCongr.{u1, u1} α α (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) 1 (OfNat.mk.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) 1 (One.one.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (MulOneClass.toHasOne.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α)))))))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.optionCongr.{u1, u1} α α (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) 1 (One.toOfNat1.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (InvOneClass.toOne.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Group.toDivisionMonoid.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))))))
Case conversion may be inaccurate. Consider using '#align equiv.option_congr_one Equiv.optionCongr_oneₓ'. -/
@[simp]
theorem Equiv.optionCongr_one {α : Type _} : (1 : Perm α).optionCongr = 1 :=
  Equiv.optionCongr_refl
#align equiv.option_congr_one Equiv.optionCongr_one

/- warning: equiv.option_congr_swap -> Equiv.optionCongr_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (x : α) (y : α), Eq.{succ u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.optionCongr.{u1, u1} α α (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y)) (Equiv.swap.{succ u1} (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Option.some.{u1} α x) (Option.some.{u1} α y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (x : α) (y : α), Eq.{succ u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.optionCongr.{u1, u1} α α (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y)) (Equiv.swap.{succ u1} (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => instDecidableEqOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Option.some.{u1} α x) (Option.some.{u1} α y))
Case conversion may be inaccurate. Consider using '#align equiv.option_congr_swap Equiv.optionCongr_swapₓ'. -/
@[simp]
theorem Equiv.optionCongr_swap {α : Type _} [DecidableEq α] (x y : α) :
    optionCongr (swap x y) = swap (some x) (some y) :=
  by
  ext (_ | i)
  · simp [swap_apply_of_ne_of_ne]
  · by_cases hx : i = x
    simp [hx, swap_apply_of_ne_of_ne]
    by_cases hy : i = y <;> simp [hx, hy, swap_apply_of_ne_of_ne]
#align equiv.option_congr_swap Equiv.optionCongr_swap

/- warning: equiv.option_congr_sign -> Equiv.optionCongr_sign is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (e : Equiv.Perm.{succ u1} α), Eq.{1} (Units.{0} Int Int.monoid) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.mulOneClass.{0} Int Int.monoid)) (fun (_x : MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.mulOneClass.{0} Int Int.monoid)) => (Equiv.Perm.{succ u1} (Option.{u1} α)) -> (Units.{0} Int Int.monoid)) (MonoidHom.hasCoeToFun.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.mulOneClass.{0} Int Int.monoid)) (Equiv.Perm.sign.{u1} (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Option.fintype.{u1} α _inst_2)) (Equiv.optionCongr.{u1, u1} α α e)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.mulOneClass.{0} Int Int.monoid)) (fun (_x : MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.mulOneClass.{0} Int Int.monoid)) => (Equiv.Perm.{succ u1} α) -> (Units.{0} Int Int.monoid)) (MonoidHom.hasCoeToFun.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.mulOneClass.{0} Int Int.monoid)) (Equiv.Perm.sign.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) e)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (e : Equiv.Perm.{succ u1} α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Equiv.Perm.{succ u1} (Option.{u1} α)) => Units.{0} Int Int.instMonoidInt) (Equiv.optionCongr.{u1, u1} α α e)) (FunLike.coe.{succ u1, succ u1, 1} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (fun (_x : Equiv.Perm.{succ u1} (Option.{u1} α)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Equiv.Perm.{succ u1} (Option.{u1} α)) => Units.{0} Int Int.instMonoidInt) _x) (MulHomClass.toFunLike.{u1, u1, 0} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α)))))) (MulOneClass.toMul.{0} (Units.{0} Int Int.instMonoidInt) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (MonoidHomClass.toMulHomClass.{u1, u1, 0} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt) (MonoidHom.monoidHomClass.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)))) (Equiv.Perm.sign.{u1} (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => instDecidableEqOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (instFintypeOption.{u1} α _inst_2)) (Equiv.optionCongr.{u1, u1} α α e)) (FunLike.coe.{succ u1, succ u1, 1} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.Perm.{succ u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Equiv.Perm.{succ u1} α) => Units.{0} Int Int.instMonoidInt) _x) (MulHomClass.toFunLike.{u1, u1, 0} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toMul.{0} (Units.{0} Int Int.instMonoidInt) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (MonoidHomClass.toMulHomClass.{u1, u1, 0} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt) (MonoidHom.monoidHomClass.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)))) (Equiv.Perm.sign.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) e)
Case conversion may be inaccurate. Consider using '#align equiv.option_congr_sign Equiv.optionCongr_signₓ'. -/
@[simp]
theorem Equiv.optionCongr_sign {α : Type _} [DecidableEq α] [Fintype α] (e : Perm α) :
    Perm.sign e.optionCongr = Perm.sign e :=
  by
  apply perm.swap_induction_on e
  · simp [perm.one_def]
  · intro f x y hne h
    simp [h, hne, perm.mul_def, ← Equiv.optionCongr_trans]
#align equiv.option_congr_sign Equiv.optionCongr_sign

/- warning: map_equiv_remove_none -> map_equiv_removeNone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (σ : Equiv.Perm.{succ u1} (Option.{u1} α)), Eq.{succ u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.optionCongr.{u1, u1} α α (Equiv.removeNone.{u1, u1} α α σ)) (HMul.hMul.{u1, u1, u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (instHMul.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (MulOneClass.toHasMul.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))))) (Equiv.swap.{succ u1} (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Option.none.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) => (Option.{u1} α) -> (Option.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) σ (Option.none.{u1} α))) σ)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (σ : Equiv.Perm.{succ u1} (Option.{u1} α)), Eq.{succ u1} (Equiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) (Equiv.optionCongr.{u1, u1} α α (Equiv.removeNone.{u1, u1} α α σ)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (instHMul.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))))) (Equiv.swap.{succ u1} (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => instDecidableEqOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Option.none.{u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Option.{u1} α) (fun (_x : Option.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Option.{u1} α) => Option.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Option.{u1} α) (Option.{u1} α)) σ (Option.none.{u1} α))) σ)
Case conversion may be inaccurate. Consider using '#align map_equiv_remove_none map_equiv_removeNoneₓ'. -/
@[simp]
theorem map_equiv_removeNone {α : Type _} [DecidableEq α] (σ : Perm (Option α)) :
    (removeNone σ).optionCongr = swap none (σ none) * σ :=
  by
  ext1 x
  have : Option.map (⇑(remove_none σ)) x = (swap none (σ none)) (σ x) :=
    by
    cases x
    · simp
    · cases h : σ (some x)
      · simp [remove_none_none _ h]
      · have hn : σ (some x) ≠ none := by simp [h]
        have hσn : σ (some x) ≠ σ none := σ.injective.ne (by simp)
        simp [remove_none_some _ ⟨_, h⟩, ← h, swap_apply_of_ne_of_ne hn hσn]
  simpa using this
#align map_equiv_remove_none map_equiv_removeNone

#print Equiv.Perm.decomposeOption /-
/-- Permutations of `option α` are equivalent to fixing an
`option α` and permuting the remaining with a `perm α`.
The fixed `option α` is swapped with `none`. -/
@[simps]
def Equiv.Perm.decomposeOption {α : Type _} [DecidableEq α] : Perm (Option α) ≃ Option α × Perm α
    where
  toFun σ := (σ none, removeNone σ)
  invFun i := swap none i.1 * i.2.optionCongr
  left_inv σ := by simp
  right_inv := fun ⟨x, σ⟩ =>
    by
    have : remove_none (swap none x * σ.option_congr) = σ :=
      Equiv.optionCongr_injective (by simp [← mul_assoc])
    simp [← perm.eq_inv_iff_eq, this]
#align equiv.perm.decompose_option Equiv.Perm.decomposeOption
-/

#print Equiv.Perm.decomposeOption_symm_of_none_apply /-
theorem Equiv.Perm.decomposeOption_symm_of_none_apply {α : Type _} [DecidableEq α] (e : Perm α)
    (i : Option α) : Equiv.Perm.decomposeOption.symm (none, e) i = i.map e := by simp
#align equiv.perm.decompose_option_symm_of_none_apply Equiv.Perm.decomposeOption_symm_of_none_apply
-/

/- warning: equiv.perm.decompose_option_symm_sign -> Equiv.Perm.decomposeOption_symm_sign is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (e : Equiv.Perm.{succ u1} α), Eq.{1} (Units.{0} Int Int.monoid) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.mulOneClass.{0} Int Int.monoid)) (fun (_x : MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.mulOneClass.{0} Int Int.monoid)) => (Equiv.Perm.{succ u1} (Option.{u1} α)) -> (Units.{0} Int Int.monoid)) (MonoidHom.hasCoeToFun.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.mulOneClass.{0} Int Int.monoid)) (Equiv.Perm.sign.{u1} (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Option.fintype.{u1} α _inst_2)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α))) (fun (_x : Equiv.{succ u1, succ u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α))) => (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) -> (Equiv.Perm.{succ u1} (Option.{u1} α))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α))) (Equiv.symm.{succ u1, succ u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.decomposeOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Prod.mk.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α) (Option.none.{u1} α) e))) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.mulOneClass.{0} Int Int.monoid)) (fun (_x : MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.mulOneClass.{0} Int Int.monoid)) => (Equiv.Perm.{succ u1} α) -> (Units.{0} Int Int.monoid)) (MonoidHom.hasCoeToFun.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.mulOneClass.{0} Int Int.monoid)) (Equiv.Perm.sign.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) e)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (e : Equiv.Perm.{succ u1} α), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Equiv.Perm.{succ u1} (Option.{u1} α)) => Units.{0} Int Int.instMonoidInt) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α))) (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (fun (a : Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) => Equiv.Perm.{succ u1} (Option.{u1} α)) a) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α))) (Equiv.symm.{succ u1, succ u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.decomposeOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Prod.mk.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α) (Option.none.{u1} α) e))) (FunLike.coe.{succ u1, succ u1, 1} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (fun (_x : Equiv.Perm.{succ u1} (Option.{u1} α)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Equiv.Perm.{succ u1} (Option.{u1} α)) => Units.{0} Int Int.instMonoidInt) _x) (MulHomClass.toFunLike.{u1, u1, 0} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α)))))) (MulOneClass.toMul.{0} (Units.{0} Int Int.instMonoidInt) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (MonoidHomClass.toMulHomClass.{u1, u1, 0} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt) (MonoidHom.monoidHomClass.{u1, 0} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.Perm.permGroup.{u1} (Option.{u1} α))))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)))) (Equiv.Perm.sign.{u1} (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => instDecidableEqOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (instFintypeOption.{u1} α _inst_2)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α))) (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (fun (_x : Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) => Equiv.Perm.{succ u1} (Option.{u1} α)) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α))) (Equiv.symm.{succ u1, succ u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.decomposeOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Prod.mk.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α) (Option.none.{u1} α) e))) (FunLike.coe.{succ u1, succ u1, 1} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.Perm.{succ u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Equiv.Perm.{succ u1} α) => Units.{0} Int Int.instMonoidInt) _x) (MulHomClass.toFunLike.{u1, u1, 0} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toMul.{0} (Units.{0} Int Int.instMonoidInt) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (MonoidHomClass.toMulHomClass.{u1, u1, 0} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt) (MonoidHom.monoidHomClass.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)))) (Equiv.Perm.sign.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) e)
Case conversion may be inaccurate. Consider using '#align equiv.perm.decompose_option_symm_sign Equiv.Perm.decomposeOption_symm_signₓ'. -/
theorem Equiv.Perm.decomposeOption_symm_sign {α : Type _} [DecidableEq α] [Fintype α] (e : Perm α) :
    Perm.sign (Equiv.Perm.decomposeOption.symm (none, e)) = Perm.sign e := by simp
#align equiv.perm.decompose_option_symm_sign Equiv.Perm.decomposeOption_symm_sign

/- warning: finset.univ_perm_option -> Finset.univ_perm_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α], Eq.{succ u1} (Finset.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α))) (Finset.univ.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.fintype.{u1, u1} (Option.{u1} α) (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (fun (a : Option.{u1} α) (b : Option.{u1} α) => Option.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Option.fintype.{u1} α _inst_2) (Option.fintype.{u1} α _inst_2))) (Finset.map.{u1, u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.toEmbedding.{succ u1, succ u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.symm.{succ u1, succ u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.decomposeOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Finset.univ.{u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Prod.fintype.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α) (Option.fintype.{u1} α _inst_2) (Equiv.fintype.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α], Eq.{succ u1} (Finset.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α))) (Finset.univ.{u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (equivFintype.{u1, u1} (Option.{u1} α) (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => instDecidableEqOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (fun (a : Option.{u1} α) (b : Option.{u1} α) => instDecidableEqOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (instFintypeOption.{u1} α _inst_2) (instFintypeOption.{u1} α _inst_2))) (Finset.map.{u1, u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.toEmbedding.{succ u1, succ u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.{succ u1} (Option.{u1} α)) (Equiv.symm.{succ u1, succ u1} (Equiv.Perm.{succ u1} (Option.{u1} α)) (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (Equiv.Perm.decomposeOption.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Finset.univ.{u1} (Prod.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α)) (instFintypeProd.{u1, u1} (Option.{u1} α) (Equiv.Perm.{succ u1} α) (instFintypeOption.{u1} α _inst_2) (equivFintype.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_2))))
Case conversion may be inaccurate. Consider using '#align finset.univ_perm_option Finset.univ_perm_optionₓ'. -/
/-- The set of all permutations of `option α` can be constructed by augmenting the set of
permutations of `α` by each element of `option α` in turn. -/
theorem Finset.univ_perm_option {α : Type _} [DecidableEq α] [Fintype α] :
    @Finset.univ (Perm <| Option α) _ =
      (Finset.univ : Finset <| Option α × Perm α).map Equiv.Perm.decomposeOption.symm.toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm
#align finset.univ_perm_option Finset.univ_perm_option

