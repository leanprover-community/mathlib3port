/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir

! This file was ported from Lean 3 source module data.real.hyperreal
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.FilterProduct
import Mathbin.Analysis.SpecificLimits.Basic

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Filter Filter.Germ

open Topology Classical

#print Hyperreal /-
/-- Hyperreal numbers on the ultrafilter extending the cofinite filter -/
def Hyperreal : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℝ deriving LinearOrderedField, Inhabited
#align hyperreal Hyperreal
-/

namespace Hyperreal

-- mathport name: «exprℝ*»
notation "ℝ*" => Hyperreal

noncomputable instance : CoeTC ℝ ℝ* :=
  ⟨fun x => (↑x : Germ _ _)⟩

#print Hyperreal.coe_eq_coe /-
@[simp, norm_cast]
theorem coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
  Germ.const_inj
#align hyperreal.coe_eq_coe Hyperreal.coe_eq_coe
-/

#print Hyperreal.coe_ne_coe /-
theorem coe_ne_coe {x y : ℝ} : (x : ℝ*) ≠ y ↔ x ≠ y :=
  coe_eq_coe.Not
#align hyperreal.coe_ne_coe Hyperreal.coe_ne_coe
-/

/- warning: hyperreal.coe_eq_zero -> Hyperreal.coe_eq_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Hyperreal (Hyperreal.ofReal x) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_eq_zero Hyperreal.coe_eq_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : ℝ*) = 0 ↔ x = 0 :=
  coe_eq_coe
#align hyperreal.coe_eq_zero Hyperreal.coe_eq_zero

/- warning: hyperreal.coe_eq_one -> Hyperreal.coe_eq_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) (OfNat.ofNat.{0} Hyperreal 1 (OfNat.mk.{0} Hyperreal 1 (One.one.{0} Hyperreal (AddMonoidWithOne.toOne.{0} Hyperreal (AddGroupWithOne.toAddMonoidWithOne.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Hyperreal (Hyperreal.ofReal x) (OfNat.ofNat.{0} Hyperreal 1 (One.toOfNat1.{0} Hyperreal (Semiring.toOne.{0} Hyperreal (StrictOrderedSemiring.toSemiring.{0} Hyperreal (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Hyperreal (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Hyperreal (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_eq_one Hyperreal.coe_eq_oneₓ'. -/
@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : ℝ*) = 1 ↔ x = 1 :=
  coe_eq_coe
#align hyperreal.coe_eq_one Hyperreal.coe_eq_one

/- warning: hyperreal.coe_ne_zero -> Hyperreal.coe_ne_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Ne.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (Ne.{1} Hyperreal (Hyperreal.ofReal x) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_ne_zero Hyperreal.coe_ne_zeroₓ'. -/
@[norm_cast]
theorem coe_ne_zero {x : ℝ} : (x : ℝ*) ≠ 0 ↔ x ≠ 0 :=
  coe_ne_coe
#align hyperreal.coe_ne_zero Hyperreal.coe_ne_zero

/- warning: hyperreal.coe_ne_one -> Hyperreal.coe_ne_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Ne.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) (OfNat.ofNat.{0} Hyperreal 1 (OfNat.mk.{0} Hyperreal 1 (One.one.{0} Hyperreal (AddMonoidWithOne.toOne.{0} Hyperreal (AddGroupWithOne.toAddMonoidWithOne.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real}, Iff (Ne.{1} Hyperreal (Hyperreal.ofReal x) (OfNat.ofNat.{0} Hyperreal 1 (One.toOfNat1.{0} Hyperreal (Semiring.toOne.{0} Hyperreal (StrictOrderedSemiring.toSemiring.{0} Hyperreal (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Hyperreal (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Hyperreal (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))))) (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_ne_one Hyperreal.coe_ne_oneₓ'. -/
@[norm_cast]
theorem coe_ne_one {x : ℝ} : (x : ℝ*) ≠ 1 ↔ x ≠ 1 :=
  coe_ne_coe
#align hyperreal.coe_ne_one Hyperreal.coe_ne_one

/- warning: hyperreal.coe_one -> Hyperreal.coe_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Hyperreal 1 (OfNat.mk.{0} Hyperreal 1 (One.one.{0} Hyperreal (AddMonoidWithOne.toOne.{0} Hyperreal (AddGroupWithOne.toAddMonoidWithOne.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))
but is expected to have type
  Eq.{1} Hyperreal (Hyperreal.ofReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Hyperreal 1 (One.toOfNat1.{0} Hyperreal (Semiring.toOne.{0} Hyperreal (StrictOrderedSemiring.toSemiring.{0} Hyperreal (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Hyperreal (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Hyperreal (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_one Hyperreal.coe_oneₓ'. -/
@[simp, norm_cast]
theorem coe_one : ↑(1 : ℝ) = (1 : ℝ*) :=
  rfl
#align hyperreal.coe_one Hyperreal.coe_one

/- warning: hyperreal.coe_zero -> Hyperreal.coe_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))
but is expected to have type
  Eq.{1} Hyperreal (Hyperreal.ofReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_zero Hyperreal.coe_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℝ) = (0 : ℝ*) :=
  rfl
#align hyperreal.coe_zero Hyperreal.coe_zero

/- warning: hyperreal.coe_inv -> Hyperreal.coe_inv is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (Inv.inv.{0} Real Real.hasInv x)) (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x))
but is expected to have type
  forall (x : Real), Eq.{1} Hyperreal (Hyperreal.ofReal (Inv.inv.{0} Real Real.instInvReal x)) (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) (Hyperreal.ofReal x))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_inv Hyperreal.coe_invₓ'. -/
@[simp, norm_cast]
theorem coe_inv (x : ℝ) : ↑x⁻¹ = (x⁻¹ : ℝ*) :=
  rfl
#align hyperreal.coe_inv Hyperreal.coe_inv

/- warning: hyperreal.coe_neg -> Hyperreal.coe_neg is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (Neg.neg.{0} Real Real.hasNeg x)) (Neg.neg.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x))
but is expected to have type
  forall (x : Real), Eq.{1} Hyperreal (Hyperreal.ofReal (Neg.neg.{0} Real Real.instNegReal x)) (Neg.neg.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (Hyperreal.ofReal x))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_neg Hyperreal.coe_negₓ'. -/
@[simp, norm_cast]
theorem coe_neg (x : ℝ) : ↑(-x) = (-x : ℝ*) :=
  rfl
#align hyperreal.coe_neg Hyperreal.coe_neg

/- warning: hyperreal.coe_add -> Hyperreal.coe_add is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x y)) (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Hyperreal (Hyperreal.ofReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x y)) (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) (Hyperreal.ofReal x) (Hyperreal.ofReal y))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_add Hyperreal.coe_addₓ'. -/
@[simp, norm_cast]
theorem coe_add (x y : ℝ) : ↑(x + y) = (x + y : ℝ*) :=
  rfl
#align hyperreal.coe_add Hyperreal.coe_add

/- warning: hyperreal.coe_bit0 clashes with [anonymous] -> [anonymous]
warning: hyperreal.coe_bit0 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (bit0.{0} Real Real.hasAdd x)) (bit0.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x))
but is expected to have type
  forall {x : Type.{u}} {β : Type.{v}}, (Nat -> x -> β) -> Nat -> (List.{u} x) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_bit0 [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] (x : ℝ) : ↑(bit0 x) = (bit0 x : ℝ*) :=
  rfl
#align hyperreal.coe_bit0 [anonymous]

/- warning: hyperreal.coe_bit1 clashes with [anonymous] -> [anonymous]
warning: hyperreal.coe_bit1 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (bit1.{0} Real Real.hasOne Real.hasAdd x)) (bit1.{0} Hyperreal (AddMonoidWithOne.toOne.{0} Hyperreal (AddGroupWithOne.toAddMonoidWithOne.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))) (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x))
but is expected to have type
  forall {x : Type.{u}} {β : Type.{v}}, (Nat -> x -> β) -> Nat -> (List.{u} x) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_bit1 [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] (x : ℝ) : ↑(bit1 x) = (bit1 x : ℝ*) :=
  rfl
#align hyperreal.coe_bit1 [anonymous]

/- warning: hyperreal.coe_mul -> Hyperreal.coe_mul is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y)) (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Hyperreal (Hyperreal.ofReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y)) (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) (Hyperreal.ofReal x) (Hyperreal.ofReal y))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_mul Hyperreal.coe_mulₓ'. -/
@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : ↑(x * y) = (x * y : ℝ*) :=
  rfl
#align hyperreal.coe_mul Hyperreal.coe_mul

/- warning: hyperreal.coe_div -> Hyperreal.coe_div is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x y)) (HDiv.hDiv.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHDiv.{0} Hyperreal (DivInvMonoid.toHasDiv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Hyperreal (Hyperreal.ofReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x y)) (HDiv.hDiv.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHDiv.{0} Hyperreal (LinearOrderedField.toDiv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)) (Hyperreal.ofReal x) (Hyperreal.ofReal y))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_div Hyperreal.coe_divₓ'. -/
@[simp, norm_cast]
theorem coe_div (x y : ℝ) : ↑(x / y) = (x / y : ℝ*) :=
  rfl
#align hyperreal.coe_div Hyperreal.coe_div

/- warning: hyperreal.coe_sub -> Hyperreal.coe_sub is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x y)) (HSub.hSub.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHSub.{0} Hyperreal (SubNegMonoid.toHasSub.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Hyperreal (Hyperreal.ofReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x y)) (HSub.hSub.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHSub.{0} Hyperreal (Ring.toSub.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Hyperreal.ofReal x) (Hyperreal.ofReal y))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_sub Hyperreal.coe_subₓ'. -/
@[simp, norm_cast]
theorem coe_sub (x y : ℝ) : ↑(x - y) = (x - y : ℝ*) :=
  rfl
#align hyperreal.coe_sub Hyperreal.coe_sub

/- warning: hyperreal.coe_le_coe -> Hyperreal.coe_le_coe is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, Iff (LE.le.{0} Hyperreal (Preorder.toLE.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) y)) (LE.le.{0} Real Real.hasLe x y)
but is expected to have type
  forall {x : Real} {y : Real}, Iff (LE.le.{0} Hyperreal (Preorder.toLE.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Hyperreal.ofReal x) (Hyperreal.ofReal y)) (LE.le.{0} Real Real.instLEReal x y)
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_le_coe Hyperreal.coe_le_coeₓ'. -/
@[simp, norm_cast]
theorem coe_le_coe {x y : ℝ} : (x : ℝ*) ≤ y ↔ x ≤ y :=
  Germ.const_le_iff
#align hyperreal.coe_le_coe Hyperreal.coe_le_coe

/- warning: hyperreal.coe_lt_coe -> Hyperreal.coe_lt_coe is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, Iff (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) y)) (LT.lt.{0} Real Real.hasLt x y)
but is expected to have type
  forall {x : Real} {y : Real}, Iff (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Hyperreal.ofReal x) (Hyperreal.ofReal y)) (LT.lt.{0} Real Real.instLTReal x y)
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_lt_coe Hyperreal.coe_lt_coeₓ'. -/
@[simp, norm_cast]
theorem coe_lt_coe {x y : ℝ} : (x : ℝ*) < y ↔ x < y :=
  Germ.const_lt_iff
#align hyperreal.coe_lt_coe Hyperreal.coe_lt_coe

/- warning: hyperreal.coe_nonneg -> Hyperreal.coe_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} Hyperreal (Preorder.toLE.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} Hyperreal (Preorder.toLE.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) (Hyperreal.ofReal x)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_nonneg Hyperreal.coe_nonnegₓ'. -/
@[simp, norm_cast]
theorem coe_nonneg {x : ℝ} : 0 ≤ (x : ℝ*) ↔ 0 ≤ x :=
  coe_le_coe
#align hyperreal.coe_nonneg Hyperreal.coe_nonneg

/- warning: hyperreal.coe_pos -> Hyperreal.coe_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) (Hyperreal.ofReal x)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_pos Hyperreal.coe_posₓ'. -/
@[simp, norm_cast]
theorem coe_pos {x : ℝ} : 0 < (x : ℝ*) ↔ 0 < x :=
  coe_lt_coe
#align hyperreal.coe_pos Hyperreal.coe_pos

/- warning: hyperreal.coe_abs -> Hyperreal.coe_abs is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x)) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) (SemilatticeSup.toHasSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (LinearOrder.toLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x))
but is expected to have type
  forall (x : Real), Eq.{1} Hyperreal (Hyperreal.ofReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x)) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (SemilatticeSup.toSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (DistribLattice.toLattice.{0} Hyperreal (instDistribLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) (Hyperreal.ofReal x))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_abs Hyperreal.coe_absₓ'. -/
@[simp, norm_cast]
theorem coe_abs (x : ℝ) : ((|x| : ℝ) : ℝ*) = |x| :=
  const_abs x
#align hyperreal.coe_abs Hyperreal.coe_abs

/- warning: hyperreal.coe_max -> Hyperreal.coe_max is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (LinearOrder.max.{0} Real Real.linearOrder x y)) (LinearOrder.max.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Hyperreal (Hyperreal.ofReal (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) x y)) (Max.max.{0} Hyperreal (LinearOrderedRing.toMax.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))) (Hyperreal.ofReal x) (Hyperreal.ofReal y))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_max Hyperreal.coe_maxₓ'. -/
@[simp, norm_cast]
theorem coe_max (x y : ℝ) : ((max x y : ℝ) : ℝ*) = max x y :=
  Germ.const_max _ _
#align hyperreal.coe_max Hyperreal.coe_max

/- warning: hyperreal.coe_min -> Hyperreal.coe_min is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} Hyperreal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (LinearOrder.min.{0} Real Real.linearOrder x y)) (LinearOrder.min.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} Hyperreal (Hyperreal.ofReal (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) x y)) (Min.min.{0} Hyperreal (LinearOrderedRing.toMin.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))) (Hyperreal.ofReal x) (Hyperreal.ofReal y))
Case conversion may be inaccurate. Consider using '#align hyperreal.coe_min Hyperreal.coe_minₓ'. -/
@[simp, norm_cast]
theorem coe_min (x y : ℝ) : ((min x y : ℝ) : ℝ*) = min x y :=
  Germ.const_min _ _
#align hyperreal.coe_min Hyperreal.coe_min

#print Hyperreal.ofSeq /-
/-- Construct a hyperreal number from a sequence of real numbers. -/
noncomputable def ofSeq (f : ℕ → ℝ) : ℝ* :=
  (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℝ)
#align hyperreal.of_seq Hyperreal.ofSeq
-/

#print Hyperreal.epsilon /-
/-- A sample infinitesimal hyperreal-/
noncomputable def epsilon : ℝ* :=
  ofSeq fun n => n⁻¹
#align hyperreal.epsilon Hyperreal.epsilon
-/

#print Hyperreal.omega /-
/-- A sample infinite hyperreal-/
noncomputable def omega : ℝ* :=
  ofSeq coe
#align hyperreal.omega Hyperreal.omega
-/

-- mathport name: hyperreal.epsilon
scoped notation "ε" => Hyperreal.epsilon

-- mathport name: hyperreal.omega
scoped notation "ω" => Hyperreal.omega

/- warning: hyperreal.inv_omega -> Hyperreal.inv_omega is a dubious translation:
lean 3 declaration is
  Eq.{1} Hyperreal (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) Hyperreal.omega) Hyperreal.epsilon
but is expected to have type
  Eq.{1} Hyperreal (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) Hyperreal.omega) Hyperreal.epsilon
Case conversion may be inaccurate. Consider using '#align hyperreal.inv_omega Hyperreal.inv_omegaₓ'. -/
@[simp]
theorem inv_omega : ω⁻¹ = ε :=
  rfl
#align hyperreal.inv_omega Hyperreal.inv_omega

/- warning: hyperreal.inv_epsilon -> Hyperreal.inv_epsilon is a dubious translation:
lean 3 declaration is
  Eq.{1} Hyperreal (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) Hyperreal.epsilon) Hyperreal.omega
but is expected to have type
  Eq.{1} Hyperreal (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) Hyperreal.epsilon) Hyperreal.omega
Case conversion may be inaccurate. Consider using '#align hyperreal.inv_epsilon Hyperreal.inv_epsilonₓ'. -/
@[simp]
theorem inv_epsilon : ε⁻¹ = ω :=
  @inv_inv _ _ ω
#align hyperreal.inv_epsilon Hyperreal.inv_epsilon

/- warning: hyperreal.omega_pos -> Hyperreal.omega_pos is a dubious translation:
lean 3 declaration is
  LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) Hyperreal.omega
but is expected to have type
  LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) Hyperreal.omega
Case conversion may be inaccurate. Consider using '#align hyperreal.omega_pos Hyperreal.omega_posₓ'. -/
theorem omega_pos : 0 < ω :=
  Germ.coe_pos.2 <|
    mem_hyperfilter_of_finite_compl <|
      by
      convert Set.finite_singleton 0
      simp [Set.eq_singleton_iff_unique_mem]
#align hyperreal.omega_pos Hyperreal.omega_pos

/- warning: hyperreal.epsilon_pos -> Hyperreal.epsilon_pos is a dubious translation:
lean 3 declaration is
  LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) Hyperreal.epsilon
but is expected to have type
  LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) Hyperreal.epsilon
Case conversion may be inaccurate. Consider using '#align hyperreal.epsilon_pos Hyperreal.epsilon_posₓ'. -/
theorem epsilon_pos : 0 < ε :=
  inv_pos_of_pos omega_pos
#align hyperreal.epsilon_pos Hyperreal.epsilon_pos

/- warning: hyperreal.epsilon_ne_zero -> Hyperreal.epsilon_ne_zero is a dubious translation:
lean 3 declaration is
  Ne.{1} Hyperreal Hyperreal.epsilon (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))
but is expected to have type
  Ne.{1} Hyperreal Hyperreal.epsilon (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.epsilon_ne_zero Hyperreal.epsilon_ne_zeroₓ'. -/
theorem epsilon_ne_zero : ε ≠ 0 :=
  epsilon_pos.ne'
#align hyperreal.epsilon_ne_zero Hyperreal.epsilon_ne_zero

/- warning: hyperreal.omega_ne_zero -> Hyperreal.omega_ne_zero is a dubious translation:
lean 3 declaration is
  Ne.{1} Hyperreal Hyperreal.omega (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))
but is expected to have type
  Ne.{1} Hyperreal Hyperreal.omega (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.omega_ne_zero Hyperreal.omega_ne_zeroₓ'. -/
theorem omega_ne_zero : ω ≠ 0 :=
  omega_pos.ne'
#align hyperreal.omega_ne_zero Hyperreal.omega_ne_zero

/- warning: hyperreal.epsilon_mul_omega -> Hyperreal.epsilon_mul_omega is a dubious translation:
lean 3 declaration is
  Eq.{1} Hyperreal (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) Hyperreal.epsilon Hyperreal.omega) (OfNat.ofNat.{0} Hyperreal 1 (OfNat.mk.{0} Hyperreal 1 (One.one.{0} Hyperreal (AddMonoidWithOne.toOne.{0} Hyperreal (AddGroupWithOne.toAddMonoidWithOne.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))
but is expected to have type
  Eq.{1} Hyperreal (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) Hyperreal.epsilon Hyperreal.omega) (OfNat.ofNat.{0} Hyperreal 1 (One.toOfNat1.{0} Hyperreal (Semiring.toOne.{0} Hyperreal (StrictOrderedSemiring.toSemiring.{0} Hyperreal (LinearOrderedSemiring.toStrictOrderedSemiring.{0} Hyperreal (LinearOrderedCommSemiring.toLinearOrderedSemiring.{0} Hyperreal (LinearOrderedSemifield.toLinearOrderedCommSemiring.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.epsilon_mul_omega Hyperreal.epsilon_mul_omegaₓ'. -/
theorem epsilon_mul_omega : ε * ω = 1 :=
  @inv_mul_cancel _ _ ω omega_ne_zero
#align hyperreal.epsilon_mul_omega Hyperreal.epsilon_mul_omega

/- warning: hyperreal.lt_of_tendsto_zero_of_pos -> Hyperreal.lt_of_tendsto_zero_of_pos is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (Hyperreal.ofSeq f) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r)))
but is expected to have type
  forall {f : Nat -> Real}, (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Hyperreal.ofSeq f) (Hyperreal.ofReal r)))
Case conversion may be inaccurate. Consider using '#align hyperreal.lt_of_tendsto_zero_of_pos Hyperreal.lt_of_tendsto_zero_of_posₓ'. -/
theorem lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, 0 < r → ofSeq f < (r : ℝ*) :=
  by
  simp only [Metric.tendsto_atTop, Real.dist_eq, sub_zero, lt_def] at hf⊢
  intro r hr; cases' hf r hr with N hf'
  have hs : { i : ℕ | f i < r }ᶜ ⊆ { i : ℕ | i ≤ N } := fun i hi1 =>
    le_of_lt
      (by
        simp only [lt_iff_not_ge] <;>
          exact fun hi2 => hi1 (lt_of_le_of_lt (le_abs_self _) (hf' i hi2)) :
        i < N)
  exact mem_hyperfilter_of_finite_compl ((Set.finite_le_nat N).Subset hs)
#align hyperreal.lt_of_tendsto_zero_of_pos Hyperreal.lt_of_tendsto_zero_of_pos

/- warning: hyperreal.neg_lt_of_tendsto_zero_of_pos -> Hyperreal.neg_lt_of_tendsto_zero_of_pos is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (Neg.neg.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r)) (Hyperreal.ofSeq f)))
but is expected to have type
  forall {f : Nat -> Real}, (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Neg.neg.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (Hyperreal.ofReal r)) (Hyperreal.ofSeq f)))
Case conversion may be inaccurate. Consider using '#align hyperreal.neg_lt_of_tendsto_zero_of_pos Hyperreal.neg_lt_of_tendsto_zero_of_posₓ'. -/
theorem neg_lt_of_tendsto_zero_of_pos {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, 0 < r → (-r : ℝ*) < ofSeq f := fun r hr =>
  have hg := hf.neg
  neg_lt_of_neg_lt (by rw [neg_zero] at hg <;> exact lt_of_tendsto_zero_of_pos hg hr)
#align hyperreal.neg_lt_of_tendsto_zero_of_pos Hyperreal.neg_lt_of_tendsto_zero_of_pos

/- warning: hyperreal.gt_of_tendsto_zero_of_neg -> Hyperreal.gt_of_tendsto_zero_of_neg is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (forall {r : Real}, (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r) (Hyperreal.ofSeq f)))
but is expected to have type
  forall {f : Nat -> Real}, (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (forall {r : Real}, (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Hyperreal.ofReal r) (Hyperreal.ofSeq f)))
Case conversion may be inaccurate. Consider using '#align hyperreal.gt_of_tendsto_zero_of_neg Hyperreal.gt_of_tendsto_zero_of_negₓ'. -/
theorem gt_of_tendsto_zero_of_neg {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    ∀ {r : ℝ}, r < 0 → (r : ℝ*) < ofSeq f := fun r hr => by
  rw [← neg_neg r, coe_neg] <;> exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)
#align hyperreal.gt_of_tendsto_zero_of_neg Hyperreal.gt_of_tendsto_zero_of_neg

/- warning: hyperreal.epsilon_lt_pos -> Hyperreal.epsilon_lt_pos is a dubious translation:
lean 3 declaration is
  forall (x : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) Hyperreal.epsilon ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) x))
but is expected to have type
  forall (x : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) Hyperreal.epsilon (Hyperreal.ofReal x))
Case conversion may be inaccurate. Consider using '#align hyperreal.epsilon_lt_pos Hyperreal.epsilon_lt_posₓ'. -/
theorem epsilon_lt_pos (x : ℝ) : 0 < x → ε < x :=
  lt_of_tendsto_zero_of_pos tendsto_inverse_atTop_nhds_0_nat
#align hyperreal.epsilon_lt_pos Hyperreal.epsilon_lt_pos

#print Hyperreal.IsSt /-
/-- Standard part predicate -/
def IsSt (x : ℝ*) (r : ℝ) :=
  ∀ δ : ℝ, 0 < δ → (r - δ : ℝ*) < x ∧ x < r + δ
#align hyperreal.is_st Hyperreal.IsSt
-/

#print Hyperreal.st /-
/-- Standard part function: like a "round" to ℝ instead of ℤ -/
noncomputable def st : ℝ* → ℝ := fun x => if h : ∃ r, IsSt x r then Classical.choose h else 0
#align hyperreal.st Hyperreal.st
-/

#print Hyperreal.Infinitesimal /-
/-- A hyperreal number is infinitesimal if its standard part is 0 -/
def Infinitesimal (x : ℝ*) :=
  IsSt x 0
#align hyperreal.infinitesimal Hyperreal.Infinitesimal
-/

#print Hyperreal.InfinitePos /-
/-- A hyperreal number is positive infinite if it is larger than all real numbers -/
def InfinitePos (x : ℝ*) :=
  ∀ r : ℝ, ↑r < x
#align hyperreal.infinite_pos Hyperreal.InfinitePos
-/

#print Hyperreal.InfiniteNeg /-
/-- A hyperreal number is negative infinite if it is smaller than all real numbers -/
def InfiniteNeg (x : ℝ*) :=
  ∀ r : ℝ, x < r
#align hyperreal.infinite_neg Hyperreal.InfiniteNeg
-/

#print Hyperreal.Infinite /-
/-- A hyperreal number is infinite if it is infinite positive or infinite negative -/
def Infinite (x : ℝ*) :=
  InfinitePos x ∨ InfiniteNeg x
#align hyperreal.infinite Hyperreal.Infinite
-/

/-!
### Some facts about `st`
-/


private theorem is_st_unique' (x : ℝ*) (r s : ℝ) (hr : IsSt x r) (hs : IsSt x s) (hrs : r < s) :
    False := by
  have hrs' := half_pos <| sub_pos_of_lt hrs
  have hr' := (hr _ hrs').2
  have hs' := (hs _ hrs').1
  have h : s - (s - r) / 2 = r + (s - r) / 2 := by linarith
  norm_cast  at *
  rw [h] at hs'
  exact not_lt_of_lt hs' hr'
#align hyperreal.is_st_unique' hyperreal.is_st_unique'

#print Hyperreal.IsSt.unique /-
theorem Hyperreal.IsSt.unique {x : ℝ*} {r s : ℝ} (hr : IsSt x r) (hs : IsSt x s) : r = s :=
  by
  rcases lt_trichotomy r s with (h | h | h)
  · exact False.elim (is_st_unique' x r s hr hs h)
  · exact h
  · exact False.elim (is_st_unique' x s r hs hr h)
#align hyperreal.is_st_unique Hyperreal.IsSt.unique
-/

#print Hyperreal.not_infinite_of_exists_st /-
theorem not_infinite_of_exists_st {x : ℝ*} : (∃ r : ℝ, IsSt x r) → ¬Infinite x := fun he hi =>
  Exists.dcases_on he fun r hr =>
    hi.elim (fun hip => not_lt_of_lt (hr 2 zero_lt_two).2 (hip <| r + 2)) fun hin =>
      not_lt_of_lt (hr 2 zero_lt_two).1 (hin <| r - 2)
#align hyperreal.not_infinite_of_exists_st Hyperreal.not_infinite_of_exists_st
-/

/- warning: hyperreal.is_st_Sup -> Hyperreal.isSt_supₛ is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Hyperreal.IsSt x (SupSet.supₛ.{0} Real Real.hasSup (setOf.{0} Real (fun (y : Real) => LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) y) x))))
but is expected to have type
  forall {x : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Hyperreal.IsSt x (SupSet.supₛ.{0} Real Real.instSupSetReal (setOf.{0} Real (fun (y : Real) => LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Hyperreal.ofReal y) x))))
Case conversion may be inaccurate. Consider using '#align hyperreal.is_st_Sup Hyperreal.isSt_supₛₓ'. -/
theorem isSt_supₛ {x : ℝ*} (hni : ¬Infinite x) : IsSt x (supₛ { y : ℝ | (y : ℝ*) < x }) :=
  let S : Set ℝ := { y : ℝ | (y : ℝ*) < x }
  let R : _ := supₛ S
  have hnile := not_forall.mp (not_or.mp hni).1
  have hnige := not_forall.mp (not_or.mp hni).2
  Exists.dcases_on hnile <|
    Exists.dcases_on hnige fun r₁ hr₁ r₂ hr₂ =>
      have HR₁ : S.Nonempty :=
        ⟨r₁ - 1, lt_of_lt_of_le (coe_lt_coe.2 <| sub_one_lt _) (not_lt.mp hr₁)⟩
      have HR₂ : BddAbove S :=
        ⟨r₂, fun y hy => le_of_lt (coe_lt_coe.1 (lt_of_lt_of_le hy (not_lt.mp hr₂)))⟩
      fun δ hδ =>
      ⟨lt_of_not_le fun c =>
          have hc : ∀ y ∈ S, y ≤ R - δ := fun y hy =>
            coe_le_coe.1 <| le_of_lt <| lt_of_lt_of_le hy c
          not_lt_of_le (csupₛ_le HR₁ hc) <| sub_lt_self R hδ,
        lt_of_not_le fun c =>
          have hc : ↑(R + δ / 2) < x :=
            lt_of_lt_of_le (add_lt_add_left (coe_lt_coe.2 (half_lt_self hδ)) R) c
          not_lt_of_le (le_csupₛ HR₂ hc) <| (lt_add_iff_pos_right _).mpr <| half_pos hδ⟩
#align hyperreal.is_st_Sup Hyperreal.isSt_supₛ

#print Hyperreal.exists_st_of_not_infinite /-
theorem exists_st_of_not_infinite {x : ℝ*} (hni : ¬Infinite x) : ∃ r : ℝ, IsSt x r :=
  ⟨supₛ { y : ℝ | (y : ℝ*) < x }, isSt_supₛ hni⟩
#align hyperreal.exists_st_of_not_infinite Hyperreal.exists_st_of_not_infinite
-/

/- warning: hyperreal.st_eq_Sup -> Hyperreal.st_eq_supₛ is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Eq.{1} Real (Hyperreal.st x) (SupSet.supₛ.{0} Real Real.hasSup (setOf.{0} Real (fun (y : Real) => LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) y) x)))
but is expected to have type
  forall {x : Hyperreal}, Eq.{1} Real (Hyperreal.st x) (SupSet.supₛ.{0} Real Real.instSupSetReal (setOf.{0} Real (fun (y : Real) => LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Hyperreal.ofReal y) x)))
Case conversion may be inaccurate. Consider using '#align hyperreal.st_eq_Sup Hyperreal.st_eq_supₛₓ'. -/
theorem st_eq_supₛ {x : ℝ*} : st x = supₛ { y : ℝ | (y : ℝ*) < x } :=
  by
  unfold st; split_ifs
  · exact is_st_unique (Classical.choose_spec h) (is_st_Sup (not_infinite_of_exists_st h))
  · cases' not_imp_comm.mp exists_st_of_not_infinite h with H H
    · rw [(Set.ext fun i => ⟨fun hi => Set.mem_univ i, fun hi => H i⟩ :
          { y : ℝ | (y : ℝ*) < x } = Set.univ)]
      exact real.Sup_univ.symm
    · rw [(Set.ext fun i =>
            ⟨fun hi => False.elim (not_lt_of_lt (H i) hi), fun hi =>
              False.elim (Set.not_mem_empty i hi)⟩ :
          { y : ℝ | (y : ℝ*) < x } = ∅)]
      exact real.Sup_empty.symm
#align hyperreal.st_eq_Sup Hyperreal.st_eq_supₛ

#print Hyperreal.exists_st_iff_not_infinite /-
theorem exists_st_iff_not_infinite {x : ℝ*} : (∃ r : ℝ, IsSt x r) ↔ ¬Infinite x :=
  ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩
#align hyperreal.exists_st_iff_not_infinite Hyperreal.exists_st_iff_not_infinite
-/

#print Hyperreal.infinite_iff_not_exists_st /-
theorem infinite_iff_not_exists_st {x : ℝ*} : Infinite x ↔ ¬∃ r : ℝ, IsSt x r :=
  iff_not_comm.mp exists_st_iff_not_infinite
#align hyperreal.infinite_iff_not_exists_st Hyperreal.infinite_iff_not_exists_st
-/

/- warning: hyperreal.st_infinite -> Hyperreal.Infinite.st_eq is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.Infinite x) -> (Eq.{1} Real (Hyperreal.st x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.Infinite x) -> (Eq.{1} Real (Hyperreal.st x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align hyperreal.st_infinite Hyperreal.Infinite.st_eqₓ'. -/
theorem Hyperreal.Infinite.st_eq {x : ℝ*} (hi : Infinite x) : st x = 0 :=
  by
  unfold st; split_ifs
  · exact False.elim ((infinite_iff_not_exists_st.mp hi) h)
  · rfl
#align hyperreal.st_infinite Hyperreal.Infinite.st_eq

#print Hyperreal.IsSt.st_eq /-
theorem Hyperreal.IsSt.st_eq {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : st x = r :=
  by
  unfold st; split_ifs
  · exact is_st_unique (Classical.choose_spec h) hxr
  · exact False.elim (h ⟨r, hxr⟩)
#align hyperreal.st_of_is_st Hyperreal.IsSt.st_eq
-/

#print Hyperreal.IsSt.isSt_st /-
theorem Hyperreal.IsSt.isSt_st {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt x (st x) := by
  rwa [st_of_is_st hxr]
#align hyperreal.is_st_st_of_is_st Hyperreal.IsSt.isSt_st
-/

#print Hyperreal.isSt_st_of_exists_st /-
theorem isSt_st_of_exists_st {x : ℝ*} (hx : ∃ r : ℝ, IsSt x r) : IsSt x (st x) :=
  Exists.dcases_on hx fun r => Hyperreal.IsSt.isSt_st
#align hyperreal.is_st_st_of_exists_st Hyperreal.isSt_st_of_exists_st
-/

/- warning: hyperreal.is_st_st -> Hyperreal.isSt_st is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Ne.{1} Real (Hyperreal.st x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Hyperreal.IsSt x (Hyperreal.st x))
but is expected to have type
  forall {x : Hyperreal}, (Ne.{1} Real (Hyperreal.st x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Hyperreal.IsSt x (Hyperreal.st x))
Case conversion may be inaccurate. Consider using '#align hyperreal.is_st_st Hyperreal.isSt_stₓ'. -/
theorem isSt_st {x : ℝ*} (hx : st x ≠ 0) : IsSt x (st x) :=
  by
  unfold st; split_ifs
  · exact Classical.choose_spec h
  · exact False.elim (hx (by unfold st <;> split_ifs <;> rfl))
#align hyperreal.is_st_st Hyperreal.isSt_st

#print Hyperreal.isSt_st' /-
theorem isSt_st' {x : ℝ*} (hx : ¬Infinite x) : IsSt x (st x) :=
  isSt_st_of_exists_st <| exists_st_of_not_infinite hx
#align hyperreal.is_st_st' Hyperreal.isSt_st'
-/

#print Hyperreal.isSt_refl_real /-
theorem isSt_refl_real (r : ℝ) : IsSt r r := fun δ hδ =>
  ⟨sub_lt_self _ (coe_lt_coe.2 hδ), lt_add_of_pos_right _ (coe_lt_coe.2 hδ)⟩
#align hyperreal.is_st_refl_real Hyperreal.isSt_refl_real
-/

#print Hyperreal.st_id_real /-
theorem st_id_real (r : ℝ) : st r = r :=
  Hyperreal.IsSt.st_eq (isSt_refl_real r)
#align hyperreal.st_id_real Hyperreal.st_id_real
-/

#print Hyperreal.eq_of_isSt_real /-
theorem eq_of_isSt_real {r s : ℝ} : IsSt r s → r = s :=
  Hyperreal.IsSt.unique (isSt_refl_real r)
#align hyperreal.eq_of_is_st_real Hyperreal.eq_of_isSt_real
-/

#print Hyperreal.isSt_real_iff_eq /-
theorem isSt_real_iff_eq {r s : ℝ} : IsSt r s ↔ r = s :=
  ⟨eq_of_isSt_real, fun hrs => by rw [hrs] <;> exact is_st_refl_real s⟩
#align hyperreal.is_st_real_iff_eq Hyperreal.isSt_real_iff_eq
-/

#print Hyperreal.isSt_symm_real /-
theorem isSt_symm_real {r s : ℝ} : IsSt r s ↔ IsSt s r := by
  rw [is_st_real_iff_eq, is_st_real_iff_eq, eq_comm]
#align hyperreal.is_st_symm_real Hyperreal.isSt_symm_real
-/

#print Hyperreal.isSt_trans_real /-
theorem isSt_trans_real {r s t : ℝ} : IsSt r s → IsSt s t → IsSt r t := by
  rw [is_st_real_iff_eq, is_st_real_iff_eq, is_st_real_iff_eq] <;> exact Eq.trans
#align hyperreal.is_st_trans_real Hyperreal.isSt_trans_real
-/

#print Hyperreal.isSt_inj_real /-
theorem isSt_inj_real {r₁ r₂ s : ℝ} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s) : r₁ = r₂ :=
  Eq.trans (eq_of_isSt_real h1) (eq_of_isSt_real h2).symm
#align hyperreal.is_st_inj_real Hyperreal.isSt_inj_real
-/

/- warning: hyperreal.is_st_iff_abs_sub_lt_delta -> Hyperreal.isSt_iff_abs_sub_lt_delta is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {r : Real}, Iff (Hyperreal.IsSt x r) (forall (δ : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) (SemilatticeSup.toHasSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (LinearOrder.toLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (HSub.hSub.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHSub.{0} Hyperreal (SubNegMonoid.toHasSub.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) δ)))
but is expected to have type
  forall {x : Hyperreal} {r : Real}, Iff (Hyperreal.IsSt x r) (forall (δ : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (SemilatticeSup.toSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (DistribLattice.toLattice.{0} Hyperreal (instDistribLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) (HSub.hSub.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHSub.{0} Hyperreal (Ring.toSub.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (Hyperreal.ofReal r))) (Hyperreal.ofReal δ)))
Case conversion may be inaccurate. Consider using '#align hyperreal.is_st_iff_abs_sub_lt_delta Hyperreal.isSt_iff_abs_sub_lt_deltaₓ'. -/
theorem isSt_iff_abs_sub_lt_delta {x : ℝ*} {r : ℝ} : IsSt x r ↔ ∀ δ : ℝ, 0 < δ → |x - r| < δ := by
  simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, is_st, and_comm', add_comm]
#align hyperreal.is_st_iff_abs_sub_lt_delta Hyperreal.isSt_iff_abs_sub_lt_delta

/- warning: hyperreal.is_st_add -> Hyperreal.IsSt.add is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal} {r : Real} {s : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt y s) -> (Hyperreal.IsSt (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) r s))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal} {r : Real} {s : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt y s) -> (Hyperreal.IsSt (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) r s))
Case conversion may be inaccurate. Consider using '#align hyperreal.is_st_add Hyperreal.IsSt.addₓ'. -/
theorem Hyperreal.IsSt.add {x y : ℝ*} {r s : ℝ} : IsSt x r → IsSt y s → IsSt (x + y) (r + s) :=
  fun hxr hys d hd =>
  have hxr' := hxr (d / 2) (half_pos hd)
  have hys' := hys (d / 2) (half_pos hd)
  ⟨by convert add_lt_add hxr'.1 hys'.1 using 1 <;> norm_cast <;> linarith, by
    convert add_lt_add hxr'.2 hys'.2 using 1 <;> norm_cast <;> linarith⟩
#align hyperreal.is_st_add Hyperreal.IsSt.add

/- warning: hyperreal.is_st_neg -> Hyperreal.IsSt.neg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {r : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt (Neg.neg.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) x) (Neg.neg.{0} Real Real.hasNeg r))
but is expected to have type
  forall {x : Hyperreal} {r : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt (Neg.neg.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) x) (Neg.neg.{0} Real Real.instNegReal r))
Case conversion may be inaccurate. Consider using '#align hyperreal.is_st_neg Hyperreal.IsSt.negₓ'. -/
theorem Hyperreal.IsSt.neg {x : ℝ*} {r : ℝ} (hxr : IsSt x r) : IsSt (-x) (-r) := fun d hd =>
  show -(r : ℝ*) - d < -x ∧ -x < -r + d by cases hxr d hd <;> constructor <;> linarith
#align hyperreal.is_st_neg Hyperreal.IsSt.neg

/- warning: hyperreal.is_st_sub -> Hyperreal.IsSt.sub is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal} {r : Real} {s : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt y s) -> (Hyperreal.IsSt (HSub.hSub.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHSub.{0} Hyperreal (SubNegMonoid.toHasSub.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))) x y) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) r s))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal} {r : Real} {s : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt y s) -> (Hyperreal.IsSt (HSub.hSub.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHSub.{0} Hyperreal (Ring.toSub.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x y) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) r s))
Case conversion may be inaccurate. Consider using '#align hyperreal.is_st_sub Hyperreal.IsSt.subₓ'. -/
theorem Hyperreal.IsSt.sub {x y : ℝ*} {r s : ℝ} : IsSt x r → IsSt y s → IsSt (x - y) (r - s) :=
  fun hxr hys => by rw [sub_eq_add_neg, sub_eq_add_neg] <;> exact is_st_add hxr (is_st_neg hys)
#align hyperreal.is_st_sub Hyperreal.IsSt.sub

/- warning: hyperreal.lt_of_is_st_lt -> Hyperreal.IsSt.lt is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal} {r : Real} {s : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt y s) -> (LT.lt.{0} Real Real.hasLt r s) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y)
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal} {r : Real} {s : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt y s) -> (LT.lt.{0} Real Real.instLTReal r s) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x y)
Case conversion may be inaccurate. Consider using '#align hyperreal.lt_of_is_st_lt Hyperreal.IsSt.ltₓ'. -/
-- (st x < st y) → (x < y) → (x ≤ y) → (st x ≤ st y)
theorem Hyperreal.IsSt.lt {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) : r < s → x < y :=
  fun hrs => by
  have hrs' : 0 < (s - r) / 2 := half_pos (sub_pos.mpr hrs)
  have hxr' := (hxr _ hrs').2
  have hys' := (hys _ hrs').1
  have H1 : r + (s - r) / 2 = (r + s) / 2 := by linarith
  have H2 : s - (s - r) / 2 = (r + s) / 2 := by linarith
  norm_cast  at *
  rw [H1] at hxr'
  rw [H2] at hys'
  exact lt_trans hxr' hys'
#align hyperreal.lt_of_is_st_lt Hyperreal.IsSt.lt

/- warning: hyperreal.is_st_le_of_le -> Hyperreal.IsSt.le is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal} {r : Real} {s : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt y s) -> (LE.le.{0} Hyperreal (Preorder.toLE.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y) -> (LE.le.{0} Real Real.hasLe r s)
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal} {r : Real} {s : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt y s) -> (LE.le.{0} Hyperreal (Preorder.toLE.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x y) -> (LE.le.{0} Real Real.instLEReal r s)
Case conversion may be inaccurate. Consider using '#align hyperreal.is_st_le_of_le Hyperreal.IsSt.leₓ'. -/
theorem Hyperreal.IsSt.le {x y : ℝ*} {r s : ℝ} (hrx : IsSt x r) (hsy : IsSt y s) : x ≤ y → r ≤ s :=
  by rw [← not_lt, ← not_lt, not_imp_not] <;> exact lt_of_is_st_lt hsy hrx
#align hyperreal.is_st_le_of_le Hyperreal.IsSt.le

/- warning: hyperreal.st_le_of_le -> Hyperreal.st_le_of_le is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (LE.le.{0} Hyperreal (Preorder.toLE.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y) -> (LE.le.{0} Real Real.hasLe (Hyperreal.st x) (Hyperreal.st y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (LE.le.{0} Hyperreal (Preorder.toLE.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x y) -> (LE.le.{0} Real Real.instLEReal (Hyperreal.st x) (Hyperreal.st y))
Case conversion may be inaccurate. Consider using '#align hyperreal.st_le_of_le Hyperreal.st_le_of_leₓ'. -/
theorem st_le_of_le {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : x ≤ y → st x ≤ st y :=
  have hx' := isSt_st' hix
  have hy' := isSt_st' hiy
  Hyperreal.IsSt.le hx' hy'
#align hyperreal.st_le_of_le Hyperreal.st_le_of_le

/- warning: hyperreal.lt_of_st_lt -> Hyperreal.lt_of_st_lt is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (LT.lt.{0} Real Real.hasLt (Hyperreal.st x) (Hyperreal.st y)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y)
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (LT.lt.{0} Real Real.instLTReal (Hyperreal.st x) (Hyperreal.st y)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x y)
Case conversion may be inaccurate. Consider using '#align hyperreal.lt_of_st_lt Hyperreal.lt_of_st_ltₓ'. -/
theorem lt_of_st_lt {x y : ℝ*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : st x < st y → x < y :=
  have hx' := isSt_st' hix
  have hy' := isSt_st' hiy
  Hyperreal.IsSt.lt hx' hy'
#align hyperreal.lt_of_st_lt Hyperreal.lt_of_st_lt

/-!
### Basic lemmas about infinite
-/


/- warning: hyperreal.infinite_pos_def -> Hyperreal.infinitePos_def is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.InfinitePos x) (forall (r : Real), LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r) x)
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.InfinitePos x) (forall (r : Real), LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Hyperreal.ofReal r) x)
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_def Hyperreal.infinitePos_defₓ'. -/
theorem infinitePos_def {x : ℝ*} : InfinitePos x ↔ ∀ r : ℝ, ↑r < x := by rw [iff_eq_eq] <;> rfl
#align hyperreal.infinite_pos_def Hyperreal.infinitePos_def

/- warning: hyperreal.infinite_neg_def -> Hyperreal.infiniteNeg_def is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.InfiniteNeg x) (forall (r : Real), LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.InfiniteNeg x) (forall (r : Real), LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (Hyperreal.ofReal r))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_def Hyperreal.infiniteNeg_defₓ'. -/
theorem infiniteNeg_def {x : ℝ*} : InfiniteNeg x ↔ ∀ r : ℝ, x < r := by rw [iff_eq_eq] <;> rfl
#align hyperreal.infinite_neg_def Hyperreal.infiniteNeg_def

/- warning: hyperreal.ne_zero_of_infinite -> Hyperreal.Infinite.ne_zero is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.Infinite x) -> (Ne.{1} Hyperreal x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))))
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.Infinite x) -> (Ne.{1} Hyperreal x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.ne_zero_of_infinite Hyperreal.Infinite.ne_zeroₓ'. -/
theorem Hyperreal.Infinite.ne_zero {x : ℝ*} : Infinite x → x ≠ 0 := fun hI h0 =>
  Or.cases_on hI (fun hip => lt_irrefl (0 : ℝ*) ((by rwa [← h0] : InfinitePos 0) 0)) fun hin =>
    lt_irrefl (0 : ℝ*) ((by rwa [← h0] : InfiniteNeg 0) 0)
#align hyperreal.ne_zero_of_infinite Hyperreal.Infinite.ne_zero

/- warning: hyperreal.not_infinite_zero -> Hyperreal.not_infinite_zero is a dubious translation:
lean 3 declaration is
  Not (Hyperreal.Infinite (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))))
but is expected to have type
  Not (Hyperreal.Infinite (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.not_infinite_zero Hyperreal.not_infinite_zeroₓ'. -/
theorem not_infinite_zero : ¬Infinite 0 := fun hI => Hyperreal.Infinite.ne_zero hI rfl
#align hyperreal.not_infinite_zero Hyperreal.not_infinite_zero

/- warning: hyperreal.pos_of_infinite_pos -> Hyperreal.InfinitePos.pos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.InfinitePos x) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) x)
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.InfinitePos x) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) x)
Case conversion may be inaccurate. Consider using '#align hyperreal.pos_of_infinite_pos Hyperreal.InfinitePos.posₓ'. -/
theorem Hyperreal.InfinitePos.pos {x : ℝ*} : InfinitePos x → 0 < x := fun hip => hip 0
#align hyperreal.pos_of_infinite_pos Hyperreal.InfinitePos.pos

/- warning: hyperreal.neg_of_infinite_neg -> Hyperreal.InfiniteNeg.lt_zero is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))))
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.neg_of_infinite_neg Hyperreal.InfiniteNeg.lt_zeroₓ'. -/
theorem Hyperreal.InfiniteNeg.lt_zero {x : ℝ*} : InfiniteNeg x → x < 0 := fun hin => hin 0
#align hyperreal.neg_of_infinite_neg Hyperreal.InfiniteNeg.lt_zero

#print Hyperreal.InfiniteNeg.not_infinitePos /-
theorem Hyperreal.InfiniteNeg.not_infinitePos {x : ℝ*} : InfiniteNeg x → ¬InfinitePos x :=
  fun hn hp => not_lt_of_lt (hn 1) (hp 1)
#align hyperreal.not_infinite_pos_of_infinite_neg Hyperreal.InfiniteNeg.not_infinitePos
-/

#print Hyperreal.InfinitePos.not_infiniteNeg /-
theorem Hyperreal.InfinitePos.not_infiniteNeg {x : ℝ*} : InfinitePos x → ¬InfiniteNeg x :=
  imp_not_comm.mp Hyperreal.InfiniteNeg.not_infinitePos
#align hyperreal.not_infinite_neg_of_infinite_pos Hyperreal.InfinitePos.not_infiniteNeg
-/

/- warning: hyperreal.infinite_neg_neg_of_infinite_pos -> Hyperreal.InfinitePos.neg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.InfinitePos x) -> (Hyperreal.InfiniteNeg (Neg.neg.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) x))
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.InfinitePos x) -> (Hyperreal.InfiniteNeg (Neg.neg.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_neg_of_infinite_pos Hyperreal.InfinitePos.negₓ'. -/
theorem Hyperreal.InfinitePos.neg {x : ℝ*} : InfinitePos x → InfiniteNeg (-x) := fun hp r =>
  neg_lt.mp (hp (-r))
#align hyperreal.infinite_neg_neg_of_infinite_pos Hyperreal.InfinitePos.neg

/- warning: hyperreal.infinite_pos_neg_of_infinite_neg -> Hyperreal.InfiniteNeg.neg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Hyperreal.InfinitePos (Neg.neg.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) x))
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Hyperreal.InfinitePos (Neg.neg.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_neg_of_infinite_neg Hyperreal.InfiniteNeg.negₓ'. -/
theorem Hyperreal.InfiniteNeg.neg {x : ℝ*} : InfiniteNeg x → InfinitePos (-x) := fun hp r =>
  lt_neg.mp (hp (-r))
#align hyperreal.infinite_pos_neg_of_infinite_neg Hyperreal.InfiniteNeg.neg

theorem infiniteNeg_neg {x : ℝ*} : InfinitePos x ↔ InfiniteNeg (-x) :=
  ⟨Hyperreal.InfinitePos.neg, fun hin => neg_neg x ▸ Hyperreal.InfiniteNeg.neg hin⟩
#align hyperreal.infinite_pos_iff_infinite_neg_neg Hyperreal.infiniteNeg_negₓ

theorem infinitePos_neg {x : ℝ*} : InfiniteNeg x ↔ InfinitePos (-x) :=
  ⟨Hyperreal.InfiniteNeg.neg, fun hin => neg_neg x ▸ Hyperreal.InfinitePos.neg hin⟩
#align hyperreal.infinite_neg_iff_infinite_pos_neg Hyperreal.infinitePos_negₓ

theorem infinite_neg {x : ℝ*} : Infinite x ↔ Infinite (-x) :=
  ⟨fun hi =>
    Or.cases_on hi (fun hip => Or.inr (Hyperreal.InfinitePos.neg hip)) fun hin =>
      Or.inl (Hyperreal.InfiniteNeg.neg hin),
    fun hi =>
    Or.cases_on hi (fun hipn => Or.inr (infinitePos_neg.mpr hipn)) fun hinp =>
      Or.inl (infiniteNeg_neg.mpr hinp)⟩
#align hyperreal.infinite_iff_infinite_neg Hyperreal.infinite_negₓ

#print Hyperreal.Infinitesimal.not_infinite /-
theorem Hyperreal.Infinitesimal.not_infinite {x : ℝ*} : Infinitesimal x → ¬Infinite x :=
  fun hi hI =>
  have hi' := hi 2 zero_lt_two
  Or.dcases_on hI
    (fun hip =>
      have hip' := hip 2
      not_lt_of_lt hip' (by convert hi'.2 <;> exact (zero_add 2).symm))
    fun hin =>
    have hin' := hin (-2)
    not_lt_of_lt hin' (by convert hi'.1 <;> exact (zero_sub 2).symm)
#align hyperreal.not_infinite_of_infinitesimal Hyperreal.Infinitesimal.not_infinite
-/

#print Hyperreal.Infinite.not_infinitesimal /-
theorem Hyperreal.Infinite.not_infinitesimal {x : ℝ*} : Infinite x → ¬Infinitesimal x :=
  imp_not_comm.mp Hyperreal.Infinitesimal.not_infinite
#align hyperreal.not_infinitesimal_of_infinite Hyperreal.Infinite.not_infinitesimal
-/

#print Hyperreal.InfinitePos.not_infinitesimal /-
theorem Hyperreal.InfinitePos.not_infinitesimal {x : ℝ*} : InfinitePos x → ¬Infinitesimal x :=
  fun hp => Hyperreal.Infinite.not_infinitesimal (Or.inl hp)
#align hyperreal.not_infinitesimal_of_infinite_pos Hyperreal.InfinitePos.not_infinitesimal
-/

#print Hyperreal.InfiniteNeg.not_infinitesimal /-
theorem Hyperreal.InfiniteNeg.not_infinitesimal {x : ℝ*} : InfiniteNeg x → ¬Infinitesimal x :=
  fun hn => Hyperreal.Infinite.not_infinitesimal (Or.inr hn)
#align hyperreal.not_infinitesimal_of_infinite_neg Hyperreal.InfiniteNeg.not_infinitesimal
-/

/- warning: hyperreal.infinite_pos_iff_infinite_and_pos -> Hyperreal.infinitePos_iff_infinite_and_pos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.InfinitePos x) (And (Hyperreal.Infinite x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) x))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.InfinitePos x) (And (Hyperreal.Infinite x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_iff_infinite_and_pos Hyperreal.infinitePos_iff_infinite_and_posₓ'. -/
theorem infinitePos_iff_infinite_and_pos {x : ℝ*} : InfinitePos x ↔ Infinite x ∧ 0 < x :=
  ⟨fun hip => ⟨Or.inl hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hip => hip) fun hin => False.elim (not_lt_of_lt hp (hin 0))⟩
#align hyperreal.infinite_pos_iff_infinite_and_pos Hyperreal.infinitePos_iff_infinite_and_pos

/- warning: hyperreal.infinite_neg_iff_infinite_and_neg -> Hyperreal.infiniteNeg_iff_infinite_and_neg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.InfiniteNeg x) (And (Hyperreal.Infinite x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.InfiniteNeg x) (And (Hyperreal.Infinite x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_iff_infinite_and_neg Hyperreal.infiniteNeg_iff_infinite_and_negₓ'. -/
theorem infiniteNeg_iff_infinite_and_neg {x : ℝ*} : InfiniteNeg x ↔ Infinite x ∧ x < 0 :=
  ⟨fun hip => ⟨Or.inr hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hin => False.elim (not_lt_of_lt hp (hin 0))) fun hip => hip⟩
#align hyperreal.infinite_neg_iff_infinite_and_neg Hyperreal.infiniteNeg_iff_infinite_and_neg

/- warning: hyperreal.infinite_pos_iff_infinite_of_pos -> Hyperreal.infinitePos_iff_infinite_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) x) -> (Iff (Hyperreal.InfinitePos x) (Hyperreal.Infinite x))
but is expected to have type
  forall {x : Hyperreal}, (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) x) -> (Iff (Hyperreal.InfinitePos x) (Hyperreal.Infinite x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_iff_infinite_of_pos Hyperreal.infinitePos_iff_infinite_of_posₓ'. -/
theorem infinitePos_iff_infinite_of_pos {x : ℝ*} (hp : 0 < x) : InfinitePos x ↔ Infinite x := by
  rw [infinite_pos_iff_infinite_and_pos] <;> exact ⟨fun hI => hI.1, fun hI => ⟨hI, hp⟩⟩
#align hyperreal.infinite_pos_iff_infinite_of_pos Hyperreal.infinitePos_iff_infinite_of_pos

/- warning: hyperreal.infinite_pos_iff_infinite_of_nonneg -> Hyperreal.infinitePos_iff_infinite_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (LE.le.{0} Hyperreal (Preorder.toLE.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) x) -> (Iff (Hyperreal.InfinitePos x) (Hyperreal.Infinite x))
but is expected to have type
  forall {x : Hyperreal}, (LE.le.{0} Hyperreal (Preorder.toLE.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) x) -> (Iff (Hyperreal.InfinitePos x) (Hyperreal.Infinite x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_iff_infinite_of_nonneg Hyperreal.infinitePos_iff_infinite_of_nonnegₓ'. -/
theorem infinitePos_iff_infinite_of_nonneg {x : ℝ*} (hp : 0 ≤ x) : InfinitePos x ↔ Infinite x :=
  Or.cases_on (lt_or_eq_of_le hp) infinitePos_iff_infinite_of_pos fun h => by
    rw [h.symm] <;>
      exact
        ⟨fun hIP => False.elim (not_infinite_zero (Or.inl hIP)), fun hI =>
          False.elim (not_infinite_zero hI)⟩
#align hyperreal.infinite_pos_iff_infinite_of_nonneg Hyperreal.infinitePos_iff_infinite_of_nonneg

/- warning: hyperreal.infinite_neg_iff_infinite_of_neg -> Hyperreal.infiniteNeg_iff_infinite_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) -> (Iff (Hyperreal.InfiniteNeg x) (Hyperreal.Infinite x))
but is expected to have type
  forall {x : Hyperreal}, (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) -> (Iff (Hyperreal.InfiniteNeg x) (Hyperreal.Infinite x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_iff_infinite_of_neg Hyperreal.infiniteNeg_iff_infinite_of_negₓ'. -/
theorem infiniteNeg_iff_infinite_of_neg {x : ℝ*} (hn : x < 0) : InfiniteNeg x ↔ Infinite x := by
  rw [infinite_neg_iff_infinite_and_neg] <;> exact ⟨fun hI => hI.1, fun hI => ⟨hI, hn⟩⟩
#align hyperreal.infinite_neg_iff_infinite_of_neg Hyperreal.infiniteNeg_iff_infinite_of_neg

/- warning: hyperreal.infinite_pos_abs_iff_infinite_abs -> Hyperreal.infinitePos_abs_iff_infinite_abs is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.InfinitePos (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) (SemilatticeSup.toHasSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (LinearOrder.toLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x)) (Hyperreal.Infinite (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) (SemilatticeSup.toHasSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (LinearOrder.toLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.InfinitePos (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (SemilatticeSup.toSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (DistribLattice.toLattice.{0} Hyperreal (instDistribLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x)) (Hyperreal.Infinite (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (SemilatticeSup.toSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (DistribLattice.toLattice.{0} Hyperreal (instDistribLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_abs_iff_infinite_abs Hyperreal.infinitePos_abs_iff_infinite_absₓ'. -/
theorem infinitePos_abs_iff_infinite_abs {x : ℝ*} : InfinitePos (|x|) ↔ Infinite (|x|) :=
  infinitePos_iff_infinite_of_nonneg (abs_nonneg _)
#align hyperreal.infinite_pos_abs_iff_infinite_abs Hyperreal.infinitePos_abs_iff_infinite_abs

theorem infinitePos_abs_iff_infinite {x : ℝ*} : Infinite x ↔ InfinitePos (|x|) :=
  ⟨fun hi d =>
    Or.cases_on hi (fun hip => by rw [abs_of_pos (hip 0)] <;> exact hip d) fun hin => by
      rw [abs_of_neg (hin 0)] <;> exact lt_neg.mp (hin (-d)),
    fun hipa => by
    rcases lt_trichotomy x 0 with (h | h | h)
    · exact Or.inr (infinite_neg_iff_infinite_pos_neg.mpr (by rwa [abs_of_neg h] at hipa))
    · exact False.elim (ne_zero_of_infinite (Or.inl (by rw [h] <;> rwa [h, abs_zero] at hipa)) h)
    · exact Or.inl (by rwa [abs_of_pos h] at hipa)⟩
#align hyperreal.infinite_iff_infinite_pos_abs Hyperreal.infinitePos_abs_iff_infiniteₓ

theorem infinite_abs_iff {x : ℝ*} : Infinite x ↔ Infinite (|x|) := by
  rw [← infinite_pos_iff_infinite_of_nonneg (abs_nonneg _), infinite_iff_infinite_pos_abs]
#align hyperreal.infinite_iff_infinite_abs Hyperreal.infinite_abs_iffₓ

/- warning: hyperreal.infinite_iff_abs_lt_abs -> Hyperreal.infinite_iff_abs_lt_abs is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.Infinite x) (forall (r : Real), LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) (SemilatticeSup.toHasSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (LinearOrder.toLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r)) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) (SemilatticeSup.toHasSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (LinearOrder.toLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.Infinite x) (forall (r : Real), LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (SemilatticeSup.toSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (DistribLattice.toLattice.{0} Hyperreal (instDistribLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) (Hyperreal.ofReal r)) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (SemilatticeSup.toSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (DistribLattice.toLattice.{0} Hyperreal (instDistribLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_iff_abs_lt_abs Hyperreal.infinite_iff_abs_lt_absₓ'. -/
theorem infinite_iff_abs_lt_abs {x : ℝ*} : Infinite x ↔ ∀ r : ℝ, (|r| : ℝ*) < |x| :=
  ⟨fun hI r => coe_abs r ▸ infinitePos_abs_iff_infinite.mp hI (|r|), fun hR =>
    Or.cases_on (max_choice x (-x))
      (fun h => Or.inl fun r => lt_of_le_of_lt (le_abs_self _) (h ▸ hR r)) fun h =>
      Or.inr fun r => neg_lt_neg_iff.mp <| lt_of_le_of_lt (neg_le_abs_self _) (h ▸ hR r)⟩
#align hyperreal.infinite_iff_abs_lt_abs Hyperreal.infinite_iff_abs_lt_abs

/- warning: hyperreal.infinite_pos_add_not_infinite_neg -> Hyperreal.infinitePos_add_not_infiniteNeg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Not (Hyperreal.InfiniteNeg y)) -> (Hyperreal.InfinitePos (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Not (Hyperreal.InfiniteNeg y)) -> (Hyperreal.InfinitePos (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_add_not_infinite_neg Hyperreal.infinitePos_add_not_infiniteNegₓ'. -/
theorem infinitePos_add_not_infiniteNeg {x y : ℝ*} :
    InfinitePos x → ¬InfiniteNeg y → InfinitePos (x + y) :=
  by
  intro hip hnin r
  cases' not_forall.mp hnin with r₂ hr₂
  convert add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1
  simp
#align hyperreal.infinite_pos_add_not_infinite_neg Hyperreal.infinitePos_add_not_infiniteNeg

/- warning: hyperreal.not_infinite_neg_add_infinite_pos -> Hyperreal.not_infiniteNeg_add_infinitePos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.InfiniteNeg x)) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfinitePos (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.InfiniteNeg x)) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfinitePos (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.not_infinite_neg_add_infinite_pos Hyperreal.not_infiniteNeg_add_infinitePosₓ'. -/
theorem not_infiniteNeg_add_infinitePos {x y : ℝ*} :
    ¬InfiniteNeg x → InfinitePos y → InfinitePos (x + y) := fun hx hy => by
  rw [add_comm] <;> exact infinite_pos_add_not_infinite_neg hy hx
#align hyperreal.not_infinite_neg_add_infinite_pos Hyperreal.not_infiniteNeg_add_infinitePos

/- warning: hyperreal.infinite_neg_add_not_infinite_pos -> Hyperreal.infiniteNeg_add_not_infinitePos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Not (Hyperreal.InfinitePos y)) -> (Hyperreal.InfiniteNeg (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Not (Hyperreal.InfinitePos y)) -> (Hyperreal.InfiniteNeg (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_add_not_infinite_pos Hyperreal.infiniteNeg_add_not_infinitePosₓ'. -/
theorem infiniteNeg_add_not_infinitePos {x y : ℝ*} :
    InfiniteNeg x → ¬InfinitePos y → InfiniteNeg (x + y) := by
  rw [@infinite_neg_iff_infinite_pos_neg x, @infinite_pos_iff_infinite_neg_neg y,
      @infinite_neg_iff_infinite_pos_neg (x + y), neg_add] <;>
    exact infinite_pos_add_not_infinite_neg
#align hyperreal.infinite_neg_add_not_infinite_pos Hyperreal.infiniteNeg_add_not_infinitePos

/- warning: hyperreal.not_infinite_pos_add_infinite_neg -> Hyperreal.not_infinitePos_add_infiniteNeg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.InfinitePos x)) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfiniteNeg (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.InfinitePos x)) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfiniteNeg (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.not_infinite_pos_add_infinite_neg Hyperreal.not_infinitePos_add_infiniteNegₓ'. -/
theorem not_infinitePos_add_infiniteNeg {x y : ℝ*} :
    ¬InfinitePos x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy => by
  rw [add_comm] <;> exact infinite_neg_add_not_infinite_pos hy hx
#align hyperreal.not_infinite_pos_add_infinite_neg Hyperreal.not_infinitePos_add_infiniteNeg

/- warning: hyperreal.infinite_pos_add_infinite_pos -> Hyperreal.infinitePos_add_infinitePos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfinitePos (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfinitePos (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_add_infinite_pos Hyperreal.infinitePos_add_infinitePosₓ'. -/
theorem infinitePos_add_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx (Hyperreal.InfinitePos.not_infiniteNeg hy)
#align hyperreal.infinite_pos_add_infinite_pos Hyperreal.infinitePos_add_infinitePos

/- warning: hyperreal.infinite_neg_add_infinite_neg -> Hyperreal.infiniteNeg_add_infiniteNeg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfiniteNeg (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfiniteNeg (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_add_infinite_neg Hyperreal.infiniteNeg_add_infiniteNegₓ'. -/
theorem infiniteNeg_add_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx (Hyperreal.InfiniteNeg.not_infinitePos hy)
#align hyperreal.infinite_neg_add_infinite_neg Hyperreal.infiniteNeg_add_infiniteNeg

/- warning: hyperreal.infinite_pos_add_not_infinite -> Hyperreal.infinitePos_add_not_infinite is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Not (Hyperreal.Infinite y)) -> (Hyperreal.InfinitePos (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Not (Hyperreal.Infinite y)) -> (Hyperreal.InfinitePos (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_add_not_infinite Hyperreal.infinitePos_add_not_infiniteₓ'. -/
theorem infinitePos_add_not_infinite {x y : ℝ*} :
    InfinitePos x → ¬Infinite y → InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx (not_or.mp hy).2
#align hyperreal.infinite_pos_add_not_infinite Hyperreal.infinitePos_add_not_infinite

/- warning: hyperreal.infinite_neg_add_not_infinite -> Hyperreal.infiniteNeg_add_not_infinite is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Not (Hyperreal.Infinite y)) -> (Hyperreal.InfiniteNeg (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Not (Hyperreal.Infinite y)) -> (Hyperreal.InfiniteNeg (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_add_not_infinite Hyperreal.infiniteNeg_add_not_infiniteₓ'. -/
theorem infiniteNeg_add_not_infinite {x y : ℝ*} :
    InfiniteNeg x → ¬Infinite y → InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx (not_or.mp hy).1
#align hyperreal.infinite_neg_add_not_infinite Hyperreal.infiniteNeg_add_not_infinite

#print Hyperreal.infinitePos_of_tendsto_top /-
theorem infinitePos_of_tendsto_top {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    InfinitePos (ofSeq f) := fun r =>
  have hf' := tendsto_atTop_atTop.mp hf
  Exists.cases_on (hf' (r + 1)) fun i hi =>
    have hi' : ∀ a : ℕ, f a < r + 1 → a < i := fun a => by
      rw [← not_le, ← not_le] <;> exact not_imp_not.mpr (hi a)
    have hS : { a : ℕ | r < f a }ᶜ ⊆ { a : ℕ | a ≤ i } := by
      simp only [Set.compl_setOf, not_lt] <;>
        exact fun a har => le_of_lt (hi' a (lt_of_le_of_lt har (lt_add_one _)))
    Germ.coe_lt.2 <| mem_hyperfilter_of_finite_compl <| (Set.finite_le_nat _).Subset hS
#align hyperreal.infinite_pos_of_tendsto_top Hyperreal.infinitePos_of_tendsto_top
-/

#print Hyperreal.infiniteNeg_of_tendsto_bot /-
theorem infiniteNeg_of_tendsto_bot {f : ℕ → ℝ} (hf : Tendsto f atTop atBot) :
    InfiniteNeg (ofSeq f) := fun r =>
  have hf' := tendsto_atTop_atBot.mp hf
  Exists.cases_on (hf' (r - 1)) fun i hi =>
    have hi' : ∀ a : ℕ, r - 1 < f a → a < i := fun a => by
      rw [← not_le, ← not_le] <;> exact not_imp_not.mpr (hi a)
    have hS : { a : ℕ | f a < r }ᶜ ⊆ { a : ℕ | a ≤ i } := by
      simp only [Set.compl_setOf, not_lt] <;>
        exact fun a har => le_of_lt (hi' a (lt_of_lt_of_le (sub_one_lt _) har))
    Germ.coe_lt.2 <| mem_hyperfilter_of_finite_compl <| (Set.finite_le_nat _).Subset hS
#align hyperreal.infinite_neg_of_tendsto_bot Hyperreal.infiniteNeg_of_tendsto_bot
-/

/- warning: hyperreal.not_infinite_neg -> Hyperreal.not_infinite_neg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite (Neg.neg.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) x)))
but is expected to have type
  forall {x : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite (Neg.neg.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) x)))
Case conversion may be inaccurate. Consider using '#align hyperreal.not_infinite_neg Hyperreal.not_infinite_negₓ'. -/
theorem not_infinite_neg {x : ℝ*} : ¬Infinite x → ¬Infinite (-x) :=
  not_imp_not.mpr infinite_neg.mpr
#align hyperreal.not_infinite_neg Hyperreal.not_infinite_neg

/- warning: hyperreal.not_infinite_add -> Hyperreal.not_infinite_add is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (Not (Hyperreal.Infinite (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y)))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (Not (Hyperreal.Infinite (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y)))
Case conversion may be inaccurate. Consider using '#align hyperreal.not_infinite_add Hyperreal.not_infinite_addₓ'. -/
theorem not_infinite_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x + y) :=
  have hx' := exists_st_of_not_infinite hx
  have hy' := exists_st_of_not_infinite hy
  Exists.cases_on hx' <|
    Exists.cases_on hy' fun r hr s hs =>
      not_infinite_of_exists_st <| ⟨s + r, Hyperreal.IsSt.add hs hr⟩
#align hyperreal.not_infinite_add Hyperreal.not_infinite_add

/- warning: hyperreal.not_infinite_iff_exist_lt_gt -> Hyperreal.not_infinite_iff_exist_lt_gt is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Not (Hyperreal.Infinite x)) (Exists.{1} Real (fun (r : Real) => Exists.{1} Real (fun (s : Real) => And (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r) x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) s)))))
but is expected to have type
  forall {x : Hyperreal}, Iff (Not (Hyperreal.Infinite x)) (Exists.{1} Real (fun (r : Real) => Exists.{1} Real (fun (s : Real) => And (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Hyperreal.ofReal r) x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (Hyperreal.ofReal s)))))
Case conversion may be inaccurate. Consider using '#align hyperreal.not_infinite_iff_exist_lt_gt Hyperreal.not_infinite_iff_exist_lt_gtₓ'. -/
theorem not_infinite_iff_exist_lt_gt {x : ℝ*} : ¬Infinite x ↔ ∃ r s : ℝ, (r : ℝ*) < x ∧ x < s :=
  ⟨fun hni =>
    Exists.dcases_on (not_forall.mp (not_or.mp hni).1) <|
      Exists.dcases_on (not_forall.mp (not_or.mp hni).2) fun r hr s hs => by
        rw [not_lt] at hr hs <;>
          exact
            ⟨r - 1, s + 1,
              ⟨lt_of_lt_of_le (by rw [sub_eq_add_neg] <;> norm_num) hr,
                lt_of_le_of_lt hs (by norm_num)⟩⟩,
    fun hrs =>
    Exists.dcases_on hrs fun r hr =>
      Exists.dcases_on hr fun s hs =>
        not_or.mpr ⟨not_forall.mpr ⟨s, lt_asymm hs.2⟩, not_forall.mpr ⟨r, lt_asymm hs.1⟩⟩⟩
#align hyperreal.not_infinite_iff_exist_lt_gt Hyperreal.not_infinite_iff_exist_lt_gt

#print Hyperreal.not_infinite_real /-
theorem not_infinite_real (r : ℝ) : ¬Infinite r := by
  rw [not_infinite_iff_exist_lt_gt] <;>
    exact ⟨r - 1, r + 1, coe_lt_coe.2 <| sub_one_lt r, coe_lt_coe.2 <| lt_add_one r⟩
#align hyperreal.not_infinite_real Hyperreal.not_infinite_real
-/

#print Hyperreal.Infinite.ne_real /-
theorem Hyperreal.Infinite.ne_real {x : ℝ*} : Infinite x → ∀ r : ℝ, x ≠ r := fun hi r hr =>
  not_infinite_real r <| @Eq.subst _ Infinite _ _ hr hi
#align hyperreal.not_real_of_infinite Hyperreal.Infinite.ne_real
-/

/-!
### Facts about `st` that require some infinite machinery
-/


private theorem is_st_mul' {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) (hs : s ≠ 0) :
    IsSt (x * y) (r * s) :=
  have hxr' := isSt_iff_abs_sub_lt_delta.mp hxr
  have hys' := isSt_iff_abs_sub_lt_delta.mp hys
  have h :=
    not_infinite_iff_exist_lt_gt.mp <|
      not_imp_not.mpr infinite_abs_iff.mpr <| not_infinite_of_exists_st ⟨r, hxr⟩
  Exists.cases_on h fun u h' =>
    Exists.cases_on h' fun t ⟨hu, ht⟩ =>
      isSt_iff_abs_sub_lt_delta.mpr fun d hd =>
        calc
          |x * y - r * s| = |x * (y - s) + (x - r) * s| := by
            rw [mul_sub, sub_mul, add_sub, sub_add_cancel]
          _ ≤ |x * (y - s)| + |(x - r) * s| := (abs_add _ _)
          _ ≤ |x| * |y - s| + |x - r| * |s| := by simp only [abs_mul]
          _ ≤ |x| * (d / t / 2 : ℝ) + (d / |s| / 2 : ℝ) * |s| :=
            (add_le_add
              (mul_le_mul_of_nonneg_left
                  (le_of_lt <|
                    hys' _ <|
                      half_pos <| div_pos hd <| coe_pos.1 <| lt_of_le_of_lt (abs_nonneg x) ht) <|
                abs_nonneg _)
              (mul_le_mul_of_nonneg_right
                  (le_of_lt <| hxr' _ <| half_pos <| div_pos hd <| abs_pos.2 hs) <|
                abs_nonneg _))
          _ = (d / 2 * (|x| / t) + d / 2 : ℝ*) :=
            by
            push_cast [-Filter.Germ.const_div]
            -- TODO: Why wasn't `hyperreal.coe_div` used?
            have : (|s| : ℝ*) ≠ 0 := by simpa
            have : (2 : ℝ*) ≠ 0 := two_ne_zero
            field_simp [*, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm]
          _ < (d / 2 * 1 + d / 2 : ℝ*) :=
            (add_lt_add_right
              (mul_lt_mul_of_pos_left ((div_lt_one <| lt_of_le_of_lt (abs_nonneg x) ht).mpr ht) <|
                half_pos <| coe_pos.2 hd)
              _)
          _ = (d : ℝ*) := by rw [mul_one, add_halves]
          
#align hyperreal.is_st_mul' hyperreal.is_st_mul'

/- warning: hyperreal.is_st_mul -> Hyperreal.IsSt.mul is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal} {r : Real} {s : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt y s) -> (Hyperreal.IsSt (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) r s))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal} {r : Real} {s : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.IsSt y s) -> (Hyperreal.IsSt (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) r s))
Case conversion may be inaccurate. Consider using '#align hyperreal.is_st_mul Hyperreal.IsSt.mulₓ'. -/
theorem Hyperreal.IsSt.mul {x y : ℝ*} {r s : ℝ} (hxr : IsSt x r) (hys : IsSt y s) :
    IsSt (x * y) (r * s) :=
  have h :=
    not_infinite_iff_exist_lt_gt.mp <|
      not_imp_not.mpr infinite_abs_iff.mpr <| not_infinite_of_exists_st ⟨r, hxr⟩
  Exists.cases_on h fun u h' =>
    Exists.cases_on h' fun t ⟨hu, ht⟩ => by
      by_cases hs : s = 0
      · apply is_st_iff_abs_sub_lt_delta.mpr
        intro d hd
        have hys' : _ :=
          is_st_iff_abs_sub_lt_delta.mp hys (d / t)
            (div_pos hd (coe_pos.1 (lt_of_le_of_lt (abs_nonneg x) ht)))
        rw [hs, coe_zero, sub_zero] at hys'
        rw [hs, MulZeroClass.mul_zero, coe_zero, sub_zero, abs_mul, mul_comm, ←
          div_mul_cancel (d : ℝ*) (ne_of_gt (lt_of_le_of_lt (abs_nonneg x) ht)), ← coe_div]
        exact mul_lt_mul'' hys' ht (abs_nonneg _) (abs_nonneg _)
      exact is_st_mul' hxr hys hs
#align hyperreal.is_st_mul Hyperreal.IsSt.mul

/- warning: hyperreal.not_infinite_mul -> Hyperreal.not_infinite_mul is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (Not (Hyperreal.Infinite (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y)))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (Not (Hyperreal.Infinite (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y)))
Case conversion may be inaccurate. Consider using '#align hyperreal.not_infinite_mul Hyperreal.not_infinite_mulₓ'. -/
--AN INFINITE LEMMA THAT REQUIRES SOME MORE ST MACHINERY
theorem not_infinite_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x * y) :=
  have hx' := exists_st_of_not_infinite hx
  have hy' := exists_st_of_not_infinite hy
  Exists.cases_on hx' <|
    Exists.cases_on hy' fun r hr s hs =>
      not_infinite_of_exists_st <| ⟨s * r, Hyperreal.IsSt.mul hs hr⟩
#align hyperreal.not_infinite_mul Hyperreal.not_infinite_mul

/- warning: hyperreal.st_add -> Hyperreal.st_add is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (Eq.{1} Real (Hyperreal.st (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Hyperreal.st x) (Hyperreal.st y)))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (Eq.{1} Real (Hyperreal.st (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Hyperreal.st x) (Hyperreal.st y)))
Case conversion may be inaccurate. Consider using '#align hyperreal.st_add Hyperreal.st_addₓ'. -/
---
theorem st_add {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x + y) = st x + st y :=
  have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_add hx hy)
  have hxy' := Hyperreal.IsSt.add hx' hy'
  Hyperreal.IsSt.unique hxy hxy'
#align hyperreal.st_add Hyperreal.st_add

/- warning: hyperreal.st_neg -> Hyperreal.st_neg is a dubious translation:
lean 3 declaration is
  forall (x : Hyperreal), Eq.{1} Real (Hyperreal.st (Neg.neg.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) x)) (Neg.neg.{0} Real Real.hasNeg (Hyperreal.st x))
but is expected to have type
  forall (x : Hyperreal), Eq.{1} Real (Hyperreal.st (Neg.neg.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) x)) (Neg.neg.{0} Real Real.instNegReal (Hyperreal.st x))
Case conversion may be inaccurate. Consider using '#align hyperreal.st_neg Hyperreal.st_negₓ'. -/
theorem st_neg (x : ℝ*) : st (-x) = -st x :=
  if h : Infinite x then by
    rw [st_infinite h, st_infinite (infinite_iff_infinite_neg.mp h), neg_zero]
  else Hyperreal.IsSt.unique (isSt_st' (not_infinite_neg h)) (Hyperreal.IsSt.neg (isSt_st' h))
#align hyperreal.st_neg Hyperreal.st_neg

/- warning: hyperreal.st_mul -> Hyperreal.st_mul is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (Eq.{1} Real (Hyperreal.st (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Hyperreal.st x) (Hyperreal.st y)))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Not (Hyperreal.Infinite y)) -> (Eq.{1} Real (Hyperreal.st (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Hyperreal.st x) (Hyperreal.st y)))
Case conversion may be inaccurate. Consider using '#align hyperreal.st_mul Hyperreal.st_mulₓ'. -/
theorem st_mul {x y : ℝ*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x * y) = st x * st y :=
  have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_mul hx hy)
  have hxy' := Hyperreal.IsSt.mul hx' hy'
  Hyperreal.IsSt.unique hxy hxy'
#align hyperreal.st_mul Hyperreal.st_mul

/-!
### Basic lemmas about infinitesimal
-/


/- warning: hyperreal.infinitesimal_def -> Hyperreal.infinitesimal_def is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.Infinitesimal x) (forall (r : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (And (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (Neg.neg.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r)) x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r))))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.Infinitesimal x) (forall (r : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (And (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Neg.neg.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (Hyperreal.ofReal r)) x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (Hyperreal.ofReal r))))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_def Hyperreal.infinitesimal_defₓ'. -/
theorem infinitesimal_def {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, 0 < r → -(r : ℝ*) < x ∧ x < r :=
  ⟨fun hi r hr => by convert hi r hr <;> simp, fun hi d hd => by convert hi d hd <;> simp⟩
#align hyperreal.infinitesimal_def Hyperreal.infinitesimal_def

/- warning: hyperreal.lt_of_pos_of_infinitesimal -> Hyperreal.lt_of_pos_of_infinitesimal is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.Infinitesimal x) -> (forall (r : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r)))
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.Infinitesimal x) -> (forall (r : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (Hyperreal.ofReal r)))
Case conversion may be inaccurate. Consider using '#align hyperreal.lt_of_pos_of_infinitesimal Hyperreal.lt_of_pos_of_infinitesimalₓ'. -/
theorem lt_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → x < r :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).2
#align hyperreal.lt_of_pos_of_infinitesimal Hyperreal.lt_of_pos_of_infinitesimal

/- warning: hyperreal.lt_neg_of_pos_of_infinitesimal -> Hyperreal.lt_neg_of_pos_of_infinitesimal is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.Infinitesimal x) -> (forall (r : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (Neg.neg.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r)) x))
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.Infinitesimal x) -> (forall (r : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Neg.neg.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (Hyperreal.ofReal r)) x))
Case conversion may be inaccurate. Consider using '#align hyperreal.lt_neg_of_pos_of_infinitesimal Hyperreal.lt_neg_of_pos_of_infinitesimalₓ'. -/
theorem lt_neg_of_pos_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, 0 < r → -↑r < x :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).1
#align hyperreal.lt_neg_of_pos_of_infinitesimal Hyperreal.lt_neg_of_pos_of_infinitesimal

/- warning: hyperreal.gt_of_neg_of_infinitesimal -> Hyperreal.gt_of_neg_of_infinitesimal is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.Infinitesimal x) -> (forall (r : Real), (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r) x))
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.Infinitesimal x) -> (forall (r : Real), (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Hyperreal.ofReal r) x))
Case conversion may be inaccurate. Consider using '#align hyperreal.gt_of_neg_of_infinitesimal Hyperreal.gt_of_neg_of_infinitesimalₓ'. -/
theorem gt_of_neg_of_infinitesimal {x : ℝ*} : Infinitesimal x → ∀ r : ℝ, r < 0 → ↑r < x :=
  fun hi r hr => by
  convert((infinitesimal_def.mp hi) (-r) (neg_pos.mpr hr)).1 <;> exact (neg_neg ↑r).symm
#align hyperreal.gt_of_neg_of_infinitesimal Hyperreal.gt_of_neg_of_infinitesimal

/- warning: hyperreal.abs_lt_real_iff_infinitesimal -> Hyperreal.abs_lt_real_iff_infinitesimal is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.Infinitesimal x) (forall (r : Real), (Ne.{1} Real r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) (SemilatticeSup.toHasSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (LinearOrder.toLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) (SemilatticeSup.toHasSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (LinearOrder.toLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r))))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.Infinitesimal x) (forall (r : Real), (Ne.{1} Real r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (SemilatticeSup.toSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (DistribLattice.toLattice.{0} Hyperreal (instDistribLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x) (Abs.abs.{0} Hyperreal (Neg.toHasAbs.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) (SemilatticeSup.toSup.{0} Hyperreal (Lattice.toSemilatticeSup.{0} Hyperreal (DistribLattice.toLattice.{0} Hyperreal (instDistribLattice.{0} Hyperreal (LinearOrderedRing.toLinearOrder.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) (Hyperreal.ofReal r))))
Case conversion may be inaccurate. Consider using '#align hyperreal.abs_lt_real_iff_infinitesimal Hyperreal.abs_lt_real_iff_infinitesimalₓ'. -/
theorem abs_lt_real_iff_infinitesimal {x : ℝ*} : Infinitesimal x ↔ ∀ r : ℝ, r ≠ 0 → |x| < |r| :=
  ⟨fun hi r hr =>
    abs_lt.mpr (by rw [← coe_abs] <;> exact infinitesimal_def.mp hi (|r|) (abs_pos.2 hr)), fun hR =>
    infinitesimal_def.mpr fun r hr =>
      abs_lt.mp <| (abs_of_pos <| coe_pos.2 hr) ▸ hR r <| ne_of_gt hr⟩
#align hyperreal.abs_lt_real_iff_infinitesimal Hyperreal.abs_lt_real_iff_infinitesimal

/- warning: hyperreal.infinitesimal_zero -> Hyperreal.infinitesimal_zero is a dubious translation:
lean 3 declaration is
  Hyperreal.Infinitesimal (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))
but is expected to have type
  Hyperreal.Infinitesimal (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_zero Hyperreal.infinitesimal_zeroₓ'. -/
theorem infinitesimal_zero : Infinitesimal 0 :=
  isSt_refl_real 0
#align hyperreal.infinitesimal_zero Hyperreal.infinitesimal_zero

/- warning: hyperreal.zero_of_infinitesimal_real -> Hyperreal.Infinitesimal.eq_zero is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (Hyperreal.Infinitesimal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r)) -> (Eq.{1} Real r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {r : Real}, (Hyperreal.Infinitesimal (Hyperreal.ofReal r)) -> (Eq.{1} Real r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align hyperreal.zero_of_infinitesimal_real Hyperreal.Infinitesimal.eq_zeroₓ'. -/
theorem Hyperreal.Infinitesimal.eq_zero {r : ℝ} : Infinitesimal r → r = 0 :=
  eq_of_isSt_real
#align hyperreal.zero_of_infinitesimal_real Hyperreal.Infinitesimal.eq_zero

/- warning: hyperreal.zero_iff_infinitesimal_real -> Hyperreal.infinitesimal_real_iff is a dubious translation:
lean 3 declaration is
  forall {r : Real}, Iff (Hyperreal.Infinitesimal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r)) (Eq.{1} Real r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {r : Real}, Iff (Hyperreal.Infinitesimal (Hyperreal.ofReal r)) (Eq.{1} Real r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align hyperreal.zero_iff_infinitesimal_real Hyperreal.infinitesimal_real_iffₓ'. -/
theorem infinitesimal_real_iff {r : ℝ} : Infinitesimal r ↔ r = 0 :=
  ⟨Hyperreal.Infinitesimal.eq_zero, fun hr => by rw [hr] <;> exact infinitesimal_zero⟩
#align hyperreal.zero_iff_infinitesimal_real Hyperreal.infinitesimal_real_iff

/- warning: hyperreal.infinitesimal_add -> Hyperreal.Infinitesimal.add is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.Infinitesimal x) -> (Hyperreal.Infinitesimal y) -> (Hyperreal.Infinitesimal (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toHasAdd.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.Infinitesimal x) -> (Hyperreal.Infinitesimal y) -> (Hyperreal.Infinitesimal (HAdd.hAdd.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHAdd.{0} Hyperreal (Distrib.toAdd.{0} Hyperreal (NonUnitalNonAssocSemiring.toDistrib.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_add Hyperreal.Infinitesimal.addₓ'. -/
theorem Hyperreal.Infinitesimal.add {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by simpa only [add_zero] using is_st_add hx hy
#align hyperreal.infinitesimal_add Hyperreal.Infinitesimal.add

/- warning: hyperreal.infinitesimal_neg -> Hyperreal.Infinitesimal.neg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.Infinitesimal x) -> (Hyperreal.Infinitesimal (Neg.neg.{0} Hyperreal (SubNegMonoid.toHasNeg.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))) x))
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.Infinitesimal x) -> (Hyperreal.Infinitesimal (Neg.neg.{0} Hyperreal (Ring.toNeg.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))) x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_neg Hyperreal.Infinitesimal.negₓ'. -/
theorem Hyperreal.Infinitesimal.neg {x : ℝ*} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  simpa only [neg_zero] using is_st_neg hx
#align hyperreal.infinitesimal_neg Hyperreal.Infinitesimal.neg

theorem infinitesimal_neg {x : ℝ*} : Infinitesimal x ↔ Infinitesimal (-x) :=
  ⟨Hyperreal.Infinitesimal.neg, fun h => neg_neg x ▸ @Hyperreal.Infinitesimal.neg (-x) h⟩
#align hyperreal.infinitesimal_neg_iff Hyperreal.infinitesimal_negₓ

/- warning: hyperreal.infinitesimal_mul -> Hyperreal.Infinitesimal.mul is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.Infinitesimal x) -> (Hyperreal.Infinitesimal y) -> (Hyperreal.Infinitesimal (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.Infinitesimal x) -> (Hyperreal.Infinitesimal y) -> (Hyperreal.Infinitesimal (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_mul Hyperreal.Infinitesimal.mulₓ'. -/
theorem Hyperreal.Infinitesimal.mul {x y : ℝ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by simpa only [MulZeroClass.mul_zero] using is_st_mul hx hy
#align hyperreal.infinitesimal_mul Hyperreal.Infinitesimal.mul

/- warning: hyperreal.infinitesimal_of_tendsto_zero -> Hyperreal.infinitesimal_of_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Real}, (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Hyperreal.Infinitesimal (Hyperreal.ofSeq f))
but is expected to have type
  forall {f : Nat -> Real}, (Filter.Tendsto.{0, 0} Nat Real f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Hyperreal.Infinitesimal (Hyperreal.ofSeq f))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_of_tendsto_zero Hyperreal.infinitesimal_of_tendsto_zeroₓ'. -/
theorem infinitesimal_of_tendsto_zero {f : ℕ → ℝ} :
    Tendsto f atTop (𝓝 0) → Infinitesimal (ofSeq f) := fun hf d hd => by
  rw [sub_eq_add_neg, ← coe_neg, ← coe_add, ← coe_add, zero_add, zero_add] <;>
    exact ⟨neg_lt_of_tendsto_zero_of_pos hf hd, lt_of_tendsto_zero_of_pos hf hd⟩
#align hyperreal.infinitesimal_of_tendsto_zero Hyperreal.infinitesimal_of_tendsto_zero

#print Hyperreal.infinitesimal_epsilon /-
theorem infinitesimal_epsilon : Infinitesimal ε :=
  infinitesimal_of_tendsto_zero tendsto_inverse_atTop_nhds_0_nat
#align hyperreal.infinitesimal_epsilon Hyperreal.infinitesimal_epsilon
-/

/- warning: hyperreal.not_real_of_infinitesimal_ne_zero -> Hyperreal.not_real_of_infinitesimal_ne_zero is a dubious translation:
lean 3 declaration is
  forall (x : Hyperreal), (Hyperreal.Infinitesimal x) -> (Ne.{1} Hyperreal x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) -> (forall (r : Real), Ne.{1} Hyperreal x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r))
but is expected to have type
  forall (x : Hyperreal), (Hyperreal.Infinitesimal x) -> (Ne.{1} Hyperreal x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) -> (forall (r : Real), Ne.{1} Hyperreal x (Hyperreal.ofReal r))
Case conversion may be inaccurate. Consider using '#align hyperreal.not_real_of_infinitesimal_ne_zero Hyperreal.not_real_of_infinitesimal_ne_zeroₓ'. -/
theorem not_real_of_infinitesimal_ne_zero (x : ℝ*) : Infinitesimal x → x ≠ 0 → ∀ r : ℝ, x ≠ r :=
  fun hi hx r hr =>
  hx <|
    hr.trans <| coe_eq_zero.2 <| Hyperreal.IsSt.unique (hr.symm ▸ isSt_refl_real r : IsSt x r) hi
#align hyperreal.not_real_of_infinitesimal_ne_zero Hyperreal.not_real_of_infinitesimal_ne_zero

/- warning: hyperreal.infinitesimal_sub_is_st -> Hyperreal.IsSt.infinitesimal_sub is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {r : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.Infinitesimal (HSub.hSub.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHSub.{0} Hyperreal (SubNegMonoid.toHasSub.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) r)))
but is expected to have type
  forall {x : Hyperreal} {r : Real}, (Hyperreal.IsSt x r) -> (Hyperreal.Infinitesimal (HSub.hSub.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHSub.{0} Hyperreal (Ring.toSub.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (Hyperreal.ofReal r)))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_sub_is_st Hyperreal.IsSt.infinitesimal_subₓ'. -/
theorem Hyperreal.IsSt.infinitesimal_sub {x : ℝ*} {r : ℝ} (hxr : IsSt x r) :
    Infinitesimal (x - r) :=
  show IsSt (x - r) 0 by
    rw [sub_eq_add_neg, ← add_neg_self r]
    exact is_st_add hxr (is_st_refl_real (-r))
#align hyperreal.infinitesimal_sub_is_st Hyperreal.IsSt.infinitesimal_sub

/- warning: hyperreal.infinitesimal_sub_st -> Hyperreal.infinitesimal_sub_st is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Hyperreal.Infinitesimal (HSub.hSub.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHSub.{0} Hyperreal (SubNegMonoid.toHasSub.{0} Hyperreal (AddGroup.toSubNegMonoid.{0} Hyperreal (AddGroupWithOne.toAddGroup.{0} Hyperreal (AddCommGroupWithOne.toAddGroupWithOne.{0} Hyperreal (Ring.toAddCommGroupWithOne.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Hyperreal (HasLiftT.mk.{1, 1} Real Hyperreal (CoeTCₓ.coe.{1, 1} Real Hyperreal Hyperreal.hasCoeT)) (Hyperreal.st x))))
but is expected to have type
  forall {x : Hyperreal}, (Not (Hyperreal.Infinite x)) -> (Hyperreal.Infinitesimal (HSub.hSub.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHSub.{0} Hyperreal (Ring.toSub.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (Hyperreal.ofReal (Hyperreal.st x))))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_sub_st Hyperreal.infinitesimal_sub_stₓ'. -/
theorem infinitesimal_sub_st {x : ℝ*} (hx : ¬Infinite x) : Infinitesimal (x - st x) :=
  Hyperreal.IsSt.infinitesimal_sub <| isSt_st' hx
#align hyperreal.infinitesimal_sub_st Hyperreal.infinitesimal_sub_st

/- warning: hyperreal.infinite_pos_iff_infinitesimal_inv_pos -> Hyperreal.infinitePos_iff_infinitesimal_inv_pos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.InfinitePos x) (And (Hyperreal.Infinitesimal (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x)) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x)))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.InfinitePos x) (And (Hyperreal.Infinitesimal (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x)) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x)))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_iff_infinitesimal_inv_pos Hyperreal.infinitePos_iff_infinitesimal_inv_posₓ'. -/
theorem infinitePos_iff_infinitesimal_inv_pos {x : ℝ*} :
    InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹ :=
  ⟨fun hip =>
    ⟨infinitesimal_def.mpr fun r hr =>
        ⟨lt_trans (coe_lt_coe.2 (neg_neg_of_pos hr)) (inv_pos.2 (hip 0)),
          (inv_lt (coe_lt_coe.2 hr) (hip 0)).mp (by convert hip r⁻¹)⟩,
      inv_pos.2 <| hip 0⟩,
    fun ⟨hi, hp⟩ r =>
    @by_cases (r = 0) (↑r < x) (fun h => Eq.substr h (inv_pos.mp hp)) fun h =>
      lt_of_le_of_lt (coe_le_coe.2 (le_abs_self r))
        ((inv_lt_inv (inv_pos.mp hp) (coe_lt_coe.2 (abs_pos.2 h))).mp
          ((infinitesimal_def.mp hi) (|r|)⁻¹ (inv_pos.2 (abs_pos.2 h))).2)⟩
#align hyperreal.infinite_pos_iff_infinitesimal_inv_pos Hyperreal.infinitePos_iff_infinitesimal_inv_pos

/- warning: hyperreal.infinite_neg_iff_infinitesimal_inv_neg -> Hyperreal.infiniteNeg_iff_infinitesimal_inv_neg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.InfiniteNeg x) (And (Hyperreal.Infinitesimal (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x)) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.InfiniteNeg x) (And (Hyperreal.Infinitesimal (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x)) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_iff_infinitesimal_inv_neg Hyperreal.infiniteNeg_iff_infinitesimal_inv_negₓ'. -/
theorem infiniteNeg_iff_infinitesimal_inv_neg {x : ℝ*} :
    InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0 :=
  ⟨fun hin =>
    by
    have hin' := infinitePos_iff_infinitesimal_inv_pos.mp (Hyperreal.InfiniteNeg.neg hin)
    rwa [infinitesimal_neg_iff, ← neg_pos, neg_inv], fun hin => by
    rwa [← neg_pos, infinitesimal_neg_iff, neg_inv, ← infinite_pos_iff_infinitesimal_inv_pos, ←
      infinite_neg_iff_infinite_pos_neg] at hin⟩
#align hyperreal.infinite_neg_iff_infinitesimal_inv_neg Hyperreal.infiniteNeg_iff_infinitesimal_inv_neg

/- warning: hyperreal.infinitesimal_inv_of_infinite -> Hyperreal.infinitesimal_inv_of_infinite is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Hyperreal.Infinite x) -> (Hyperreal.Infinitesimal (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x))
but is expected to have type
  forall {x : Hyperreal}, (Hyperreal.Infinite x) -> (Hyperreal.Infinitesimal (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_inv_of_infinite Hyperreal.infinitesimal_inv_of_infiniteₓ'. -/
theorem infinitesimal_inv_of_infinite {x : ℝ*} : Infinite x → Infinitesimal x⁻¹ := fun hi =>
  Or.cases_on hi (fun hip => (infinitePos_iff_infinitesimal_inv_pos.mp hip).1) fun hin =>
    (infiniteNeg_iff_infinitesimal_inv_neg.mp hin).1
#align hyperreal.infinitesimal_inv_of_infinite Hyperreal.infinitesimal_inv_of_infinite

/- warning: hyperreal.infinite_of_infinitesimal_inv -> Hyperreal.infinite_of_infinitesimal_inv is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Ne.{1} Hyperreal x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) -> (Hyperreal.Infinitesimal (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x)) -> (Hyperreal.Infinite x)
but is expected to have type
  forall {x : Hyperreal}, (Ne.{1} Hyperreal x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) -> (Hyperreal.Infinitesimal (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x)) -> (Hyperreal.Infinite x)
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_of_infinitesimal_inv Hyperreal.infinite_of_infinitesimal_invₓ'. -/
theorem infinite_of_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) (hi : Infinitesimal x⁻¹) : Infinite x :=
  by
  cases' lt_or_gt_of_ne h0 with hn hp
  · exact Or.inr (infinite_neg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
  · exact Or.inl (infinite_pos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)
#align hyperreal.infinite_of_infinitesimal_inv Hyperreal.infinite_of_infinitesimal_inv

/- warning: hyperreal.infinite_iff_infinitesimal_inv -> Hyperreal.infinite_iff_infinitesimal_inv is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Ne.{1} Hyperreal x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) -> (Iff (Hyperreal.Infinite x) (Hyperreal.Infinitesimal (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x)))
but is expected to have type
  forall {x : Hyperreal}, (Ne.{1} Hyperreal x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) -> (Iff (Hyperreal.Infinite x) (Hyperreal.Infinitesimal (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x)))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_iff_infinitesimal_inv Hyperreal.infinite_iff_infinitesimal_invₓ'. -/
theorem infinite_iff_infinitesimal_inv {x : ℝ*} (h0 : x ≠ 0) : Infinite x ↔ Infinitesimal x⁻¹ :=
  ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩
#align hyperreal.infinite_iff_infinitesimal_inv Hyperreal.infinite_iff_infinitesimal_inv

/- warning: hyperreal.infinitesimal_pos_iff_infinite_pos_inv -> Hyperreal.infinitesimal_pos_iff_infinitePos_inv is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.InfinitePos (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x)) (And (Hyperreal.Infinitesimal x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) x))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.InfinitePos (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x)) (And (Hyperreal.Infinitesimal x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) x))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_pos_iff_infinite_pos_inv Hyperreal.infinitesimal_pos_iff_infinitePos_invₓ'. -/
theorem infinitesimal_pos_iff_infinitePos_inv {x : ℝ*} :
    InfinitePos x⁻¹ ↔ Infinitesimal x ∧ 0 < x := by
  convert infinite_pos_iff_infinitesimal_inv_pos <;> simp only [inv_inv]
#align hyperreal.infinitesimal_pos_iff_infinite_pos_inv Hyperreal.infinitesimal_pos_iff_infinitePos_inv

/- warning: hyperreal.infinitesimal_neg_iff_infinite_neg_inv -> Hyperreal.infinitesimal_neg_iff_infiniteNeg_inv is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, Iff (Hyperreal.InfiniteNeg (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x)) (And (Hyperreal.Infinitesimal x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))))
but is expected to have type
  forall {x : Hyperreal}, Iff (Hyperreal.InfiniteNeg (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x)) (And (Hyperreal.Infinitesimal x) (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_neg_iff_infinite_neg_inv Hyperreal.infinitesimal_neg_iff_infiniteNeg_invₓ'. -/
theorem infinitesimal_neg_iff_infiniteNeg_inv {x : ℝ*} :
    InfiniteNeg x⁻¹ ↔ Infinitesimal x ∧ x < 0 := by
  convert infinite_neg_iff_infinitesimal_inv_neg <;> simp only [inv_inv]
#align hyperreal.infinitesimal_neg_iff_infinite_neg_inv Hyperreal.infinitesimal_neg_iff_infiniteNeg_inv

/- warning: hyperreal.infinitesimal_iff_infinite_inv -> Hyperreal.infinitesimal_iff_infinite_inv is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal}, (Ne.{1} Hyperreal x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) -> (Iff (Hyperreal.Infinitesimal x) (Hyperreal.Infinite (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x)))
but is expected to have type
  forall {x : Hyperreal}, (Ne.{1} Hyperreal x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) -> (Iff (Hyperreal.Infinitesimal x) (Hyperreal.Infinite (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x)))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinitesimal_iff_infinite_inv Hyperreal.infinitesimal_iff_infinite_invₓ'. -/
theorem infinitesimal_iff_infinite_inv {x : ℝ*} (h : x ≠ 0) : Infinitesimal x ↔ Infinite x⁻¹ := by
  convert(infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm <;> simp only [inv_inv]
#align hyperreal.infinitesimal_iff_infinite_inv Hyperreal.infinitesimal_iff_infinite_inv

/-!
### `st` stuff that requires infinitesimal machinery
-/


#print Hyperreal.isSt_of_tendsto /-
theorem isSt_of_tendsto {f : ℕ → ℝ} {r : ℝ} (hf : Tendsto f atTop (𝓝 r)) : IsSt (ofSeq f) r :=
  by
  have hg : Tendsto (fun n => f n - r) atTop (𝓝 0) := sub_self r ▸ hf.sub tendsto_const_nhds
  rw [← zero_add r, ← sub_add_cancel f fun n => r] <;>
    exact is_st_add (infinitesimal_of_tendsto_zero hg) (is_st_refl_real r)
#align hyperreal.is_st_of_tendsto Hyperreal.isSt_of_tendsto
-/

/- warning: hyperreal.is_st_inv -> Hyperreal.IsSt.inv is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {r : Real}, (Not (Hyperreal.Infinitesimal x)) -> (Hyperreal.IsSt x r) -> (Hyperreal.IsSt (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x) (Inv.inv.{0} Real Real.hasInv r))
but is expected to have type
  forall {x : Hyperreal} {r : Real}, (Not (Hyperreal.Infinitesimal x)) -> (Hyperreal.IsSt x r) -> (Hyperreal.IsSt (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x) (Inv.inv.{0} Real Real.instInvReal r))
Case conversion may be inaccurate. Consider using '#align hyperreal.is_st_inv Hyperreal.IsSt.invₓ'. -/
theorem Hyperreal.IsSt.inv {x : ℝ*} {r : ℝ} (hi : ¬Infinitesimal x) : IsSt x r → IsSt x⁻¹ r⁻¹ :=
  fun hxr =>
  have h : x ≠ 0 := fun h => hi (h.symm ▸ infinitesimal_zero)
  have H := exists_st_of_not_infinite <| not_imp_not.mpr (infinitesimal_iff_infinite_inv h).mpr hi
  Exists.cases_on H fun s hs =>
    have H' : IsSt 1 (r * s) := mul_inv_cancel h ▸ Hyperreal.IsSt.mul hxr hs
    have H'' : s = r⁻¹ := one_div r ▸ eq_one_div_of_mul_eq_one_right (eq_of_isSt_real H').symm
    H'' ▸ hs
#align hyperreal.is_st_inv Hyperreal.IsSt.inv

/- warning: hyperreal.st_inv -> Hyperreal.st_inv is a dubious translation:
lean 3 declaration is
  forall (x : Hyperreal), Eq.{1} Real (Hyperreal.st (Inv.inv.{0} Hyperreal (DivInvMonoid.toHasInv.{0} Hyperreal (DivisionRing.toDivInvMonoid.{0} Hyperreal (Field.toDivisionRing.{0} Hyperreal (LinearOrderedField.toField.{0} Hyperreal Hyperreal.linearOrderedField)))) x)) (Inv.inv.{0} Real Real.hasInv (Hyperreal.st x))
but is expected to have type
  forall (x : Hyperreal), Eq.{1} Real (Hyperreal.st (Inv.inv.{0} Hyperreal (LinearOrderedField.toInv.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal) x)) (Inv.inv.{0} Real Real.instInvReal (Hyperreal.st x))
Case conversion may be inaccurate. Consider using '#align hyperreal.st_inv Hyperreal.st_invₓ'. -/
theorem st_inv (x : ℝ*) : st x⁻¹ = (st x)⁻¹ :=
  by
  by_cases h0 : x = 0
  rw [h0, inv_zero, ← coe_zero, st_id_real, inv_zero]
  by_cases h1 : infinitesimal x
  rw [st_infinite ((infinitesimal_iff_infinite_inv h0).mp h1), st_of_is_st h1, inv_zero]
  by_cases h2 : Infinite x
  rw [st_of_is_st (infinitesimal_inv_of_infinite h2), st_infinite h2, inv_zero]
  exact st_of_is_st (is_st_inv h1 (is_st_st' h2))
#align hyperreal.st_inv Hyperreal.st_inv

/-!
### Infinite stuff that requires infinitesimal machinery
-/


#print Hyperreal.infinitePos_omega /-
theorem infinitePos_omega : InfinitePos ω :=
  infinitePos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩
#align hyperreal.infinite_pos_omega Hyperreal.infinitePos_omega
-/

#print Hyperreal.infinite_omega /-
theorem infinite_omega : Infinite ω :=
  (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon
#align hyperreal.infinite_omega Hyperreal.infinite_omega
-/

/- warning: hyperreal.infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos -> Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Not (Hyperreal.Infinitesimal y)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) y) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Not (Hyperreal.Infinitesimal y)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) y) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_posₓ'. -/
theorem infinitePos_mul_of_infinitePos_not_infinitesimal_pos {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → 0 < y → InfinitePos (x * y) := fun hx hy₁ hy₂ r =>
  have hy₁' := not_forall.mp (by rw [infinitesimal_def] at hy₁ <;> exact hy₁)
  Exists.dcases_on hy₁' fun r₁ hy₁'' =>
    by
    have hyr := by rw [not_imp, ← abs_lt, not_lt, abs_of_pos hy₂] at hy₁'' <;> exact hy₁''
    rw [← div_mul_cancel r (ne_of_gt hyr.1), coe_mul] <;>
      exact mul_lt_mul (hx (r / r₁)) hyr.2 (coe_lt_coe.2 hyr.1) (le_of_lt (hx 0))
#align hyperreal.infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos Hyperreal.infinitePos_mul_of_infinitePos_not_infinitesimal_pos

/- warning: hyperreal.infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos -> Hyperreal.infinitePos_mul_of_not_infinitesimal_pos_infinitePos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinitesimal x)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) x) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinitesimal x)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) x) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos Hyperreal.infinitePos_mul_of_not_infinitesimal_pos_infinitePosₓ'. -/
theorem infinitePos_mul_of_not_infinitesimal_pos_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfinitePos y → InfinitePos (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos hy hx hp
#align hyperreal.infinite_pos_mul_of_not_infinitesimal_pos_infinite_pos Hyperreal.infinitePos_mul_of_not_infinitesimal_pos_infinitePos

/- warning: hyperreal.infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg -> Hyperreal.infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Not (Hyperreal.Infinitesimal y)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) y (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Not (Hyperreal.Infinitesimal y)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) y (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg Hyperreal.infinitePos_mul_of_infiniteNeg_not_infinitesimal_negₓ'. -/
theorem infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → y < 0 → InfinitePos (x * y) := by
  rw [infinite_neg_iff_infinite_pos_neg, ← neg_pos, ← neg_mul_neg, infinitesimal_neg_iff] <;>
    exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
#align hyperreal.infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg Hyperreal.infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg

/- warning: hyperreal.infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg -> Hyperreal.infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinitesimal x)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinitesimal x)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg Hyperreal.infinitePos_mul_of_not_infinitesimal_neg_infiniteNegₓ'. -/
theorem infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfiniteNeg y → InfinitePos (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_pos_mul_of_infinite_neg_not_infinitesimal_neg hy hx hp
#align hyperreal.infinite_pos_mul_of_not_infinitesimal_neg_infinite_neg Hyperreal.infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg

/- warning: hyperreal.infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg -> Hyperreal.infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Not (Hyperreal.Infinitesimal y)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) y (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Not (Hyperreal.Infinitesimal y)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) y (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg Hyperreal.infiniteNeg_mul_of_infinitePos_not_infinitesimal_negₓ'. -/
theorem infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg {x y : ℝ*} :
    InfinitePos x → ¬Infinitesimal y → y < 0 → InfiniteNeg (x * y) := by
  rw [infinite_neg_iff_infinite_pos_neg, ← neg_pos, neg_mul_eq_mul_neg, infinitesimal_neg_iff] <;>
    exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
#align hyperreal.infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg Hyperreal.infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg

/- warning: hyperreal.infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos -> Hyperreal.infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinitesimal x)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))))))))) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinitesimal x)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) x (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos Hyperreal.infiniteNeg_mul_of_not_infinitesimal_neg_infinitePosₓ'. -/
theorem infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos {x y : ℝ*} :
    ¬Infinitesimal x → x < 0 → InfinitePos y → InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_neg_mul_of_infinite_pos_not_infinitesimal_neg hy hx hp
#align hyperreal.infinite_neg_mul_of_not_infinitesimal_neg_infinite_pos Hyperreal.infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos

/- warning: hyperreal.infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos -> Hyperreal.infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Not (Hyperreal.Infinitesimal y)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) y) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Not (Hyperreal.Infinitesimal y)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) y) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos Hyperreal.infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_posₓ'. -/
theorem infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : ℝ*} :
    InfiniteNeg x → ¬Infinitesimal y → 0 < y → InfiniteNeg (x * y) := by
  rw [infinite_neg_iff_infinite_pos_neg, infinite_neg_iff_infinite_pos_neg, neg_mul_eq_neg_mul] <;>
    exact infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
#align hyperreal.infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos Hyperreal.infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos

/- warning: hyperreal.infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg -> Hyperreal.infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinitesimal x)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (OrderedAddCommGroup.toPartialOrder.{0} Hyperreal (StrictOrderedRing.toOrderedAddCommGroup.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) (OfNat.ofNat.{0} Hyperreal 0 (OfNat.mk.{0} Hyperreal 0 (Zero.zero.{0} Hyperreal (MulZeroClass.toHasZero.{0} Hyperreal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} Hyperreal (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField)))))))))))) x) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinitesimal x)) -> (LT.lt.{0} Hyperreal (Preorder.toLT.{0} Hyperreal (PartialOrder.toPreorder.{0} Hyperreal (StrictOrderedRing.toPartialOrder.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))) (OfNat.ofNat.{0} Hyperreal 0 (Zero.toOfNat0.{0} Hyperreal (CommMonoidWithZero.toZero.{0} Hyperreal (CommGroupWithZero.toCommMonoidWithZero.{0} Hyperreal (Semifield.toCommGroupWithZero.{0} Hyperreal (LinearOrderedSemifield.toSemifield.{0} Hyperreal (LinearOrderedField.toLinearOrderedSemifield.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal))))))) x) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg Hyperreal.infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNegₓ'. -/
theorem infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg {x y : ℝ*} :
    ¬Infinitesimal x → 0 < x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm] <;> exact infinite_neg_mul_of_infinite_neg_not_infinitesimal_pos hy hx hp
#align hyperreal.infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg Hyperreal.infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg

/- warning: hyperreal.infinite_pos_mul_infinite_pos -> Hyperreal.infinitePos_mul_infinitePos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_mul_infinite_pos Hyperreal.infinitePos_mul_infinitePosₓ'. -/
theorem infinitePos_mul_infinitePos {x y : ℝ*} :
    InfinitePos x → InfinitePos y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infinitePos_not_infinitesimal_pos hx
    (Hyperreal.InfinitePos.not_infinitesimal hy) (hy 0)
#align hyperreal.infinite_pos_mul_infinite_pos Hyperreal.infinitePos_mul_infinitePos

/- warning: hyperreal.infinite_neg_mul_infinite_neg -> Hyperreal.infiniteNeg_mul_infiniteNeg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfinitePos (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_mul_infinite_neg Hyperreal.infiniteNeg_mul_infiniteNegₓ'. -/
theorem infiniteNeg_mul_infiniteNeg {x y : ℝ*} :
    InfiniteNeg x → InfiniteNeg y → InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hx
    (Hyperreal.InfiniteNeg.not_infinitesimal hy) (hy 0)
#align hyperreal.infinite_neg_mul_infinite_neg Hyperreal.infiniteNeg_mul_infiniteNeg

/- warning: hyperreal.infinite_pos_mul_infinite_neg -> Hyperreal.infinitePos_mul_infiniteNeg is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfinitePos x) -> (Hyperreal.InfiniteNeg y) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_pos_mul_infinite_neg Hyperreal.infinitePos_mul_infiniteNegₓ'. -/
theorem infinitePos_mul_infiniteNeg {x y : ℝ*} :
    InfinitePos x → InfiniteNeg y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hx
    (Hyperreal.InfiniteNeg.not_infinitesimal hy) (hy 0)
#align hyperreal.infinite_pos_mul_infinite_neg Hyperreal.infinitePos_mul_infiniteNeg

/- warning: hyperreal.infinite_neg_mul_infinite_pos -> Hyperreal.infiniteNeg_mul_infinitePos is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.InfiniteNeg x) -> (Hyperreal.InfinitePos y) -> (Hyperreal.InfiniteNeg (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_neg_mul_infinite_pos Hyperreal.infiniteNeg_mul_infinitePosₓ'. -/
theorem infiniteNeg_mul_infinitePos {x y : ℝ*} :
    InfiniteNeg x → InfinitePos y → InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hx
    (Hyperreal.InfinitePos.not_infinitesimal hy) (hy 0)
#align hyperreal.infinite_neg_mul_infinite_pos Hyperreal.infiniteNeg_mul_infinitePos

/- warning: hyperreal.infinite_mul_of_infinite_not_infinitesimal -> Hyperreal.infinite_mul_of_infinite_not_infinitesimal is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.Infinite x) -> (Not (Hyperreal.Infinitesimal y)) -> (Hyperreal.Infinite (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.Infinite x) -> (Not (Hyperreal.Infinitesimal y)) -> (Hyperreal.Infinite (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_mul_of_infinite_not_infinitesimal Hyperreal.infinite_mul_of_infinite_not_infinitesimalₓ'. -/
theorem infinite_mul_of_infinite_not_infinitesimal {x y : ℝ*} :
    Infinite x → ¬Infinitesimal y → Infinite (x * y) := fun hx hy =>
  have h0 : y < 0 ∨ 0 < y := lt_or_gt_of_ne fun H0 => hy (Eq.substr H0 (isSt_refl_real 0))
  Or.dcases_on hx
    (Or.dcases_on h0
      (fun H0 Hx => Or.inr (infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inl (infinitePos_mul_of_infinitePos_not_infinitesimal_pos Hx hy H0))
    (Or.dcases_on h0
      (fun H0 Hx => Or.inl (infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inr (infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos Hx hy H0))
#align hyperreal.infinite_mul_of_infinite_not_infinitesimal Hyperreal.infinite_mul_of_infinite_not_infinitesimal

/- warning: hyperreal.infinite_mul_of_not_infinitesimal_infinite -> Hyperreal.infinite_mul_of_not_infinitesimal_infinite is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinitesimal x)) -> (Hyperreal.Infinite y) -> (Hyperreal.Infinite (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Not (Hyperreal.Infinitesimal x)) -> (Hyperreal.Infinite y) -> (Hyperreal.Infinite (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite_mul_of_not_infinitesimal_infinite Hyperreal.infinite_mul_of_not_infinitesimal_infiniteₓ'. -/
theorem infinite_mul_of_not_infinitesimal_infinite {x y : ℝ*} :
    ¬Infinitesimal x → Infinite y → Infinite (x * y) := fun hx hy => by
  rw [mul_comm] <;> exact infinite_mul_of_infinite_not_infinitesimal hy hx
#align hyperreal.infinite_mul_of_not_infinitesimal_infinite Hyperreal.infinite_mul_of_not_infinitesimal_infinite

/- warning: hyperreal.infinite.mul -> Hyperreal.Infinite.mul is a dubious translation:
lean 3 declaration is
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.Infinite x) -> (Hyperreal.Infinite y) -> (Hyperreal.Infinite (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (Distrib.toHasMul.{0} Hyperreal (Ring.toDistrib.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.linearOrderedField))))))) x y))
but is expected to have type
  forall {x : Hyperreal} {y : Hyperreal}, (Hyperreal.Infinite x) -> (Hyperreal.Infinite y) -> (Hyperreal.Infinite (HMul.hMul.{0, 0, 0} Hyperreal Hyperreal Hyperreal (instHMul.{0} Hyperreal (NonUnitalNonAssocRing.toMul.{0} Hyperreal (NonAssocRing.toNonUnitalNonAssocRing.{0} Hyperreal (Ring.toNonAssocRing.{0} Hyperreal (StrictOrderedRing.toRing.{0} Hyperreal (LinearOrderedRing.toStrictOrderedRing.{0} Hyperreal (LinearOrderedCommRing.toLinearOrderedRing.{0} Hyperreal (LinearOrderedField.toLinearOrderedCommRing.{0} Hyperreal Hyperreal.instLinearOrderedFieldHyperreal)))))))) x y))
Case conversion may be inaccurate. Consider using '#align hyperreal.infinite.mul Hyperreal.Infinite.mulₓ'. -/
theorem Infinite.mul {x y : ℝ*} : Infinite x → Infinite y → Infinite (x * y) := fun hx hy =>
  infinite_mul_of_infinite_not_infinitesimal hx (Hyperreal.Infinite.not_infinitesimal hy)
#align hyperreal.infinite.mul Hyperreal.Infinite.mul

end Hyperreal

namespace Tactic

open Positivity

private theorem hyperreal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : ℝ*) ≠ 0 :=
  Hyperreal.coe_ne_zero.2
#align tactic.hyperreal_coe_ne_zero tactic.hyperreal_coe_ne_zero

private theorem hyperreal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : ℝ*) :=
  Hyperreal.coe_nonneg.2
#align tactic.hyperreal_coe_nonneg tactic.hyperreal_coe_nonneg

private theorem hyperreal_coe_pos {r : ℝ} : 0 < r → 0 < (r : ℝ*) :=
  Hyperreal.coe_pos.2
#align tactic.hyperreal_coe_pos tactic.hyperreal_coe_pos

/-- Extension for the `positivity` tactic: cast from `ℝ` to `ℝ*`. -/
@[positivity]
unsafe def positivity_coe_real_hyperreal : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ Hyperreal.hasCoeT)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` hyperreal_coe_pos [p]
      | nonnegative p => nonnegative <$> mk_app `` hyperreal_coe_nonneg [p]
      | nonzero p => nonzero <$> mk_app `` hyperreal_coe_ne_zero [p]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ℝ*)` for `r : ℝ`"
#align tactic.positivity_coe_real_hyperreal tactic.positivity_coe_real_hyperreal

end Tactic

