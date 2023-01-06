/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.hom.equiv.type_tags
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Group.TypeTags

/-!
# Additive and multiplicative equivalences associated to `multiplicative` and `additive`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {G H : Type _}

/- warning: add_equiv.to_multiplicative -> AddEquiv.toMultiplicative is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : AddZeroClass.{u1} G] [_inst_2 : AddZeroClass.{u2} H], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AddEquiv.{u1, u2} G H (AddZeroClass.toHasAdd.{u1} G _inst_1) (AddZeroClass.toHasAdd.{u2} H _inst_2)) (MulEquiv.{u1, u2} (Multiplicative.{u1} G) (Multiplicative.{u2} H) (Multiplicative.hasMul.{u1} G (AddZeroClass.toHasAdd.{u1} G _inst_1)) (Multiplicative.hasMul.{u2} H (AddZeroClass.toHasAdd.{u2} H _inst_2)))
but is expected to have type
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : AddZeroClass.{u1} G] [_inst_2 : AddZeroClass.{u2} H], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (AddEquiv.{u1, u2} G H (AddZeroClass.toAdd.{u1} G _inst_1) (AddZeroClass.toAdd.{u2} H _inst_2)) (MulEquiv.{u1, u2} (Multiplicative.{u1} G) (Multiplicative.{u2} H) (Multiplicative.mul.{u1} G (AddZeroClass.toAdd.{u1} G _inst_1)) (Multiplicative.mul.{u2} H (AddZeroClass.toAdd.{u2} H _inst_2)))
Case conversion may be inaccurate. Consider using '#align add_equiv.to_multiplicative AddEquiv.toMultiplicativeₓ'. -/
/-- Reinterpret `G ≃+ H` as `multiplicative G ≃* multiplicative H`. -/
def AddEquiv.toMultiplicative [AddZeroClass G] [AddZeroClass H] :
    G ≃+ H ≃ (Multiplicative G ≃* Multiplicative H)
    where
  toFun f :=
    ⟨f.toAddMonoidHom.toMultiplicative, f.symm.toAddMonoidHom.toMultiplicative, f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
#align add_equiv.to_multiplicative AddEquiv.toMultiplicative

/- warning: mul_equiv.to_additive -> MulEquiv.toAdditive is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : MulOneClass.{u1} G] [_inst_2 : MulOneClass.{u2} H], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G _inst_1) (MulOneClass.toHasMul.{u2} H _inst_2)) (AddEquiv.{u1, u2} (Additive.{u1} G) (Additive.{u2} H) (Additive.hasAdd.{u1} G (MulOneClass.toHasMul.{u1} G _inst_1)) (Additive.hasAdd.{u2} H (MulOneClass.toHasMul.{u2} H _inst_2)))
but is expected to have type
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : MulOneClass.{u1} G] [_inst_2 : MulOneClass.{u2} H], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u1, u2} G H (MulOneClass.toMul.{u1} G _inst_1) (MulOneClass.toMul.{u2} H _inst_2)) (AddEquiv.{u1, u2} (Additive.{u1} G) (Additive.{u2} H) (Additive.add.{u1} G (MulOneClass.toMul.{u1} G _inst_1)) (Additive.add.{u2} H (MulOneClass.toMul.{u2} H _inst_2)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_additive MulEquiv.toAdditiveₓ'. -/
/-- Reinterpret `G ≃* H` as `additive G ≃+ additive H`. -/
def MulEquiv.toAdditive [MulOneClass G] [MulOneClass H] : G ≃* H ≃ (Additive G ≃+ Additive H)
    where
  toFun f := ⟨f.toMonoidHom.toAdditive, f.symm.toMonoidHom.toAdditive, f.3, f.4, f.5⟩
  invFun f := ⟨f.toAddMonoidHom, f.symm.toAddMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
#align mul_equiv.to_additive MulEquiv.toAdditive

/- warning: add_equiv.to_multiplicative' -> AddEquiv.toMultiplicative' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : MulOneClass.{u1} G] [_inst_2 : AddZeroClass.{u2} H], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AddEquiv.{u1, u2} (Additive.{u1} G) H (Additive.hasAdd.{u1} G (MulOneClass.toHasMul.{u1} G _inst_1)) (AddZeroClass.toHasAdd.{u2} H _inst_2)) (MulEquiv.{u1, u2} G (Multiplicative.{u2} H) (MulOneClass.toHasMul.{u1} G _inst_1) (Multiplicative.hasMul.{u2} H (AddZeroClass.toHasAdd.{u2} H _inst_2)))
but is expected to have type
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : MulOneClass.{u1} G] [_inst_2 : AddZeroClass.{u2} H], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (AddEquiv.{u1, u2} (Additive.{u1} G) H (Additive.add.{u1} G (MulOneClass.toMul.{u1} G _inst_1)) (AddZeroClass.toAdd.{u2} H _inst_2)) (MulEquiv.{u1, u2} G (Multiplicative.{u2} H) (MulOneClass.toMul.{u1} G _inst_1) (Multiplicative.mul.{u2} H (AddZeroClass.toAdd.{u2} H _inst_2)))
Case conversion may be inaccurate. Consider using '#align add_equiv.to_multiplicative' AddEquiv.toMultiplicative'ₓ'. -/
/-- Reinterpret `additive G ≃+ H` as `G ≃* multiplicative H`. -/
def AddEquiv.toMultiplicative' [MulOneClass G] [AddZeroClass H] :
    Additive G ≃+ H ≃ (G ≃* Multiplicative H)
    where
  toFun f :=
    ⟨f.toAddMonoidHom.toMultiplicative', f.symm.toAddMonoidHom.toMultiplicative'', f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
#align add_equiv.to_multiplicative' AddEquiv.toMultiplicative'

/- warning: mul_equiv.to_additive' -> MulEquiv.toAdditive' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : MulOneClass.{u1} G] [_inst_2 : AddZeroClass.{u2} H], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} G (Multiplicative.{u2} H) (MulOneClass.toHasMul.{u1} G _inst_1) (Multiplicative.hasMul.{u2} H (AddZeroClass.toHasAdd.{u2} H _inst_2))) (AddEquiv.{u1, u2} (Additive.{u1} G) H (Additive.hasAdd.{u1} G (MulOneClass.toHasMul.{u1} G _inst_1)) (AddZeroClass.toHasAdd.{u2} H _inst_2))
but is expected to have type
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : MulOneClass.{u1} G] [_inst_2 : AddZeroClass.{u2} H], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u1, u2} G (Multiplicative.{u2} H) (MulOneClass.toMul.{u1} G _inst_1) (Multiplicative.mul.{u2} H (AddZeroClass.toAdd.{u2} H _inst_2))) (AddEquiv.{u1, u2} (Additive.{u1} G) H (Additive.add.{u1} G (MulOneClass.toMul.{u1} G _inst_1)) (AddZeroClass.toAdd.{u2} H _inst_2))
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_additive' MulEquiv.toAdditive'ₓ'. -/
/-- Reinterpret `G ≃* multiplicative H` as `additive G ≃+ H` as. -/
def MulEquiv.toAdditive' [MulOneClass G] [AddZeroClass H] :
    G ≃* Multiplicative H ≃ (Additive G ≃+ H) :=
  AddEquiv.toMultiplicative'.symm
#align mul_equiv.to_additive' MulEquiv.toAdditive'

/- warning: add_equiv.to_multiplicative'' -> AddEquiv.toMultiplicative'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : AddZeroClass.{u1} G] [_inst_2 : MulOneClass.{u2} H], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (AddEquiv.{u1, u2} G (Additive.{u2} H) (AddZeroClass.toHasAdd.{u1} G _inst_1) (Additive.hasAdd.{u2} H (MulOneClass.toHasMul.{u2} H _inst_2))) (MulEquiv.{u1, u2} (Multiplicative.{u1} G) H (Multiplicative.hasMul.{u1} G (AddZeroClass.toHasAdd.{u1} G _inst_1)) (MulOneClass.toHasMul.{u2} H _inst_2))
but is expected to have type
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : AddZeroClass.{u1} G] [_inst_2 : MulOneClass.{u2} H], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (AddEquiv.{u1, u2} G (Additive.{u2} H) (AddZeroClass.toAdd.{u1} G _inst_1) (Additive.add.{u2} H (MulOneClass.toMul.{u2} H _inst_2))) (MulEquiv.{u1, u2} (Multiplicative.{u1} G) H (Multiplicative.mul.{u1} G (AddZeroClass.toAdd.{u1} G _inst_1)) (MulOneClass.toMul.{u2} H _inst_2))
Case conversion may be inaccurate. Consider using '#align add_equiv.to_multiplicative'' AddEquiv.toMultiplicative''ₓ'. -/
/-- Reinterpret `G ≃+ additive H` as `multiplicative G ≃* H`. -/
def AddEquiv.toMultiplicative'' [AddZeroClass G] [MulOneClass H] :
    G ≃+ Additive H ≃ (Multiplicative G ≃* H)
    where
  toFun f :=
    ⟨f.toAddMonoidHom.toMultiplicative'', f.symm.toAddMonoidHom.toMultiplicative', f.3, f.4, f.5⟩
  invFun f := ⟨f.toMonoidHom, f.symm.toMonoidHom, f.3, f.4, f.5⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
#align add_equiv.to_multiplicative'' AddEquiv.toMultiplicative''

/- warning: mul_equiv.to_additive'' -> MulEquiv.toAdditive'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : AddZeroClass.{u1} G] [_inst_2 : MulOneClass.{u2} H], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} (Multiplicative.{u1} G) H (Multiplicative.hasMul.{u1} G (AddZeroClass.toHasAdd.{u1} G _inst_1)) (MulOneClass.toHasMul.{u2} H _inst_2)) (AddEquiv.{u1, u2} G (Additive.{u2} H) (AddZeroClass.toHasAdd.{u1} G _inst_1) (Additive.hasAdd.{u2} H (MulOneClass.toHasMul.{u2} H _inst_2)))
but is expected to have type
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : AddZeroClass.{u1} G] [_inst_2 : MulOneClass.{u2} H], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u1, u2} (Multiplicative.{u1} G) H (Multiplicative.mul.{u1} G (AddZeroClass.toAdd.{u1} G _inst_1)) (MulOneClass.toMul.{u2} H _inst_2)) (AddEquiv.{u1, u2} G (Additive.{u2} H) (AddZeroClass.toAdd.{u1} G _inst_1) (Additive.add.{u2} H (MulOneClass.toMul.{u2} H _inst_2)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_additive'' MulEquiv.toAdditive''ₓ'. -/
/-- Reinterpret `multiplicative G ≃* H` as `G ≃+ additive H` as. -/
def MulEquiv.toAdditive'' [AddZeroClass G] [MulOneClass H] :
    Multiplicative G ≃* H ≃ (G ≃+ Additive H) :=
  AddEquiv.toMultiplicative''.symm
#align mul_equiv.to_additive'' MulEquiv.toAdditive''

section

variable (G) (H)

/- warning: add_equiv.additive_multiplicative -> AddEquiv.additiveMultiplicative is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : AddZeroClass.{u1} G], AddEquiv.{u1, u1} (Additive.{u1} (Multiplicative.{u1} G)) G (Additive.hasAdd.{u1} (Multiplicative.{u1} G) (Multiplicative.hasMul.{u1} G (AddZeroClass.toHasAdd.{u1} G _inst_1))) (AddZeroClass.toHasAdd.{u1} G _inst_1)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : AddZeroClass.{u1} G], AddEquiv.{u1, u1} (Additive.{u1} (Multiplicative.{u1} G)) G (Additive.add.{u1} (Multiplicative.{u1} G) (Multiplicative.mul.{u1} G (AddZeroClass.toAdd.{u1} G _inst_1))) (AddZeroClass.toAdd.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align add_equiv.additive_multiplicative AddEquiv.additiveMultiplicativeₓ'. -/
/-- `additive (multiplicative G)` is just `G`. -/
def AddEquiv.additiveMultiplicative [AddZeroClass G] : Additive (Multiplicative G) ≃+ G :=
  MulEquiv.toAdditive'' (MulEquiv.refl (Multiplicative G))
#align add_equiv.additive_multiplicative AddEquiv.additiveMultiplicative

/- warning: mul_equiv.multiplicative_additive -> MulEquiv.multiplicativeAdditive is a dubious translation:
lean 3 declaration is
  forall (H : Type.{u1}) [_inst_1 : MulOneClass.{u1} H], MulEquiv.{u1, u1} (Multiplicative.{u1} (Additive.{u1} H)) H (Multiplicative.hasMul.{u1} (Additive.{u1} H) (Additive.hasAdd.{u1} H (MulOneClass.toHasMul.{u1} H _inst_1))) (MulOneClass.toHasMul.{u1} H _inst_1)
but is expected to have type
  forall (H : Type.{u1}) [_inst_1 : MulOneClass.{u1} H], MulEquiv.{u1, u1} (Multiplicative.{u1} (Additive.{u1} H)) H (Multiplicative.mul.{u1} (Additive.{u1} H) (Additive.add.{u1} H (MulOneClass.toMul.{u1} H _inst_1))) (MulOneClass.toMul.{u1} H _inst_1)
Case conversion may be inaccurate. Consider using '#align mul_equiv.multiplicative_additive MulEquiv.multiplicativeAdditiveₓ'. -/
/-- `multiplicative (additive H)` is just `H`. -/
def MulEquiv.multiplicativeAdditive [MulOneClass H] : Multiplicative (Additive H) ≃* H :=
  AddEquiv.toMultiplicative'' (AddEquiv.refl (Additive H))
#align mul_equiv.multiplicative_additive MulEquiv.multiplicativeAdditive

end

