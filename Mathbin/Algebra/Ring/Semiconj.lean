/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland

! This file was ported from Lean 3 source module algebra.ring.semiconj
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Semiconj
import Mathbin.Algebra.Ring.Defs

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

namespace SemiconjBy

/- warning: semiconj_by.add_right -> SemiconjBy.add_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R] {a : R} {x : R} {y : R} {x' : R} {y' : R}, (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R _inst_1) a x y) -> (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R _inst_1) a x' y') -> (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R _inst_1) a (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R _inst_1)) x x') (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R _inst_1)) y y'))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R] {a : R} {x : R} {y : R} {x' : R} {y' : R}, (SemiconjBy.{u1} R (Distrib.toMul.{u1} R _inst_1) a x y) -> (SemiconjBy.{u1} R (Distrib.toMul.{u1} R _inst_1) a x' y') -> (SemiconjBy.{u1} R (Distrib.toMul.{u1} R _inst_1) a (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R _inst_1)) x x') (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R _inst_1)) y y'))
Case conversion may be inaccurate. Consider using '#align semiconj_by.add_right SemiconjBy.add_rightₓ'. -/
@[simp]
theorem add_right [Distrib R] {a x y x' y' : R} (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x + x') (y + y') := by
  simp only [SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]
#align semiconj_by.add_right SemiconjBy.add_right

/- warning: semiconj_by.add_left -> SemiconjBy.add_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R] {a : R} {b : R} {x : R} {y : R}, (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R _inst_1) a x y) -> (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R _inst_1) b x y) -> (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R _inst_1)) a b) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R] {a : R} {b : R} {x : R} {y : R}, (SemiconjBy.{u1} R (Distrib.toMul.{u1} R _inst_1) a x y) -> (SemiconjBy.{u1} R (Distrib.toMul.{u1} R _inst_1) b x y) -> (SemiconjBy.{u1} R (Distrib.toMul.{u1} R _inst_1) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R _inst_1)) a b) x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.add_left SemiconjBy.add_leftₓ'. -/
@[simp]
theorem add_left [Distrib R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) :
    SemiconjBy (a + b) x y := by simp only [SemiconjBy, left_distrib, right_distrib, ha.eq, hb.eq]
#align semiconj_by.add_left SemiconjBy.add_left

section

variable [Mul R] [HasDistribNeg R] {a x y : R}

/- warning: semiconj_by.neg_right -> SemiconjBy.neg_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {x : R} {y : R}, (SemiconjBy.{u1} R _inst_1 a x y) -> (SemiconjBy.{u1} R _inst_1 a (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R _inst_1 _inst_2)) x) (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R _inst_1 _inst_2)) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {x : R} {y : R}, (SemiconjBy.{u1} R _inst_1 a x y) -> (SemiconjBy.{u1} R _inst_1 a (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R _inst_1 _inst_2)) x) (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R _inst_1 _inst_2)) y))
Case conversion may be inaccurate. Consider using '#align semiconj_by.neg_right SemiconjBy.neg_rightₓ'. -/
theorem neg_right (h : SemiconjBy a x y) : SemiconjBy a (-x) (-y) := by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]
#align semiconj_by.neg_right SemiconjBy.neg_right

/- warning: semiconj_by.neg_right_iff -> SemiconjBy.neg_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {x : R} {y : R}, Iff (SemiconjBy.{u1} R _inst_1 a (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R _inst_1 _inst_2)) x) (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R _inst_1 _inst_2)) y)) (SemiconjBy.{u1} R _inst_1 a x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {x : R} {y : R}, Iff (SemiconjBy.{u1} R _inst_1 a (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R _inst_1 _inst_2)) x) (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R _inst_1 _inst_2)) y)) (SemiconjBy.{u1} R _inst_1 a x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.neg_right_iff SemiconjBy.neg_right_iffₓ'. -/
@[simp]
theorem neg_right_iff : SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg x ▸ neg_neg y ▸ h.neg_right, SemiconjBy.neg_right⟩
#align semiconj_by.neg_right_iff SemiconjBy.neg_right_iff

/- warning: semiconj_by.neg_left -> SemiconjBy.neg_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {x : R} {y : R}, (SemiconjBy.{u1} R _inst_1 a x y) -> (SemiconjBy.{u1} R _inst_1 (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R _inst_1 _inst_2)) a) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {x : R} {y : R}, (SemiconjBy.{u1} R _inst_1 a x y) -> (SemiconjBy.{u1} R _inst_1 (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R _inst_1 _inst_2)) a) x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.neg_left SemiconjBy.neg_leftₓ'. -/
theorem neg_left (h : SemiconjBy a x y) : SemiconjBy (-a) x y := by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]
#align semiconj_by.neg_left SemiconjBy.neg_left

/- warning: semiconj_by.neg_left_iff -> SemiconjBy.neg_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {x : R} {y : R}, Iff (SemiconjBy.{u1} R _inst_1 (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R _inst_1 _inst_2)) a) x y) (SemiconjBy.{u1} R _inst_1 a x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {x : R} {y : R}, Iff (SemiconjBy.{u1} R _inst_1 (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R _inst_1 _inst_2)) a) x y) (SemiconjBy.{u1} R _inst_1 a x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.neg_left_iff SemiconjBy.neg_left_iffₓ'. -/
@[simp]
theorem neg_left_iff : SemiconjBy (-a) x y ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg a ▸ h.neg_left, SemiconjBy.neg_left⟩
#align semiconj_by.neg_left_iff SemiconjBy.neg_left_iff

end

section

variable [MulOneClass R] [HasDistribNeg R] {a x y : R}

/- warning: semiconj_by.neg_one_right -> SemiconjBy.neg_one_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : HasDistribNeg.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1)] (a : R), SemiconjBy.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) a (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R _inst_1))))) (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : HasDistribNeg.{u1} R (MulOneClass.toMul.{u1} R _inst_1)] (a : R), SemiconjBy.{u1} R (MulOneClass.toMul.{u1} R _inst_1) a (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R (MulOneClass.toMul.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (MulOneClass.toOne.{u1} R _inst_1)))) (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R (MulOneClass.toMul.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (MulOneClass.toOne.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align semiconj_by.neg_one_right SemiconjBy.neg_one_rightₓ'. -/
@[simp]
theorem neg_one_right (a : R) : SemiconjBy a (-1) (-1) :=
  (one_right a).neg_right
#align semiconj_by.neg_one_right SemiconjBy.neg_one_right

/- warning: semiconj_by.neg_one_left -> SemiconjBy.neg_one_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : HasDistribNeg.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1)] (x : R), SemiconjBy.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R _inst_1))))) x x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : HasDistribNeg.{u1} R (MulOneClass.toMul.{u1} R _inst_1)] (x : R), SemiconjBy.{u1} R (MulOneClass.toMul.{u1} R _inst_1) (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R (MulOneClass.toMul.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (MulOneClass.toOne.{u1} R _inst_1)))) x x
Case conversion may be inaccurate. Consider using '#align semiconj_by.neg_one_left SemiconjBy.neg_one_leftₓ'. -/
@[simp]
theorem neg_one_left (x : R) : SemiconjBy (-1) x x :=
  (SemiconjBy.one_left x).neg_left
#align semiconj_by.neg_one_left SemiconjBy.neg_one_left

end

section

variable [NonUnitalNonAssocRing R] {a b x y x' y' : R}

/- warning: semiconj_by.sub_right -> SemiconjBy.sub_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {x : R} {y : R} {x' : R} {y' : R}, (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a x y) -> (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a x' y') -> (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) x x') (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) y y'))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {x : R} {y : R} {x' : R} {y' : R}, (SemiconjBy.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a x y) -> (SemiconjBy.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a x' y') -> (SemiconjBy.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) x x') (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) y y'))
Case conversion may be inaccurate. Consider using '#align semiconj_by.sub_right SemiconjBy.sub_rightₓ'. -/
@[simp]
theorem sub_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x - x') (y - y') := by simpa only [sub_eq_add_neg] using h.add_right h'.neg_right
#align semiconj_by.sub_right SemiconjBy.sub_right

/- warning: semiconj_by.sub_left -> SemiconjBy.sub_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {b : R} {x : R} {y : R}, (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a x y) -> (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) b x y) -> (SemiconjBy.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) a b) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {b : R} {x : R} {y : R}, (SemiconjBy.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a x y) -> (SemiconjBy.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) b x y) -> (SemiconjBy.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) a b) x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.sub_left SemiconjBy.sub_leftₓ'. -/
@[simp]
theorem sub_left (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) : SemiconjBy (a - b) x y := by
  simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left
#align semiconj_by.sub_left SemiconjBy.sub_left

end

end SemiconjBy

