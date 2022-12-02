/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathbin.Algebra.Group.Semiconj
import Mathbin.Algebra.Ring.Defs

/-!
# Semirings and rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/751
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
  forall {R : Type.{x}} [_inst_1 : Distrib.{x} R] {a : R} {x : R} {y : R} {x' : R} {y' : R}, (SemiconjBy.{x} R (Distrib.toHasMul.{x} R _inst_1) a x y) -> (SemiconjBy.{x} R (Distrib.toHasMul.{x} R _inst_1) a x' y') -> (SemiconjBy.{x} R (Distrib.toHasMul.{x} R _inst_1) a (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R _inst_1)) x x') (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R _inst_1)) y y'))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.20 : Distrib.{x} R] {a : R} {x : R} {y : R} {x' : R} {y' : R}, (SemiconjBy.{x} R (Distrib.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.20) a x y) -> (SemiconjBy.{x} R (Distrib.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.20) a x' y') -> (SemiconjBy.{x} R (Distrib.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.20) a (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toAdd.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.20)) x x') (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toAdd.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.20)) y y'))
Case conversion may be inaccurate. Consider using '#align semiconj_by.add_right SemiconjBy.add_rightₓ'. -/
@[simp]
theorem add_right [Distrib R] {a x y x' y' : R} (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x + x') (y + y') := by
  simp only [SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]
#align semiconj_by.add_right SemiconjBy.add_right

/- warning: semiconj_by.add_left -> SemiconjBy.add_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Distrib.{x} R] {a : R} {b : R} {x : R} {y : R}, (SemiconjBy.{x} R (Distrib.toHasMul.{x} R _inst_1) a x y) -> (SemiconjBy.{x} R (Distrib.toHasMul.{x} R _inst_1) b x y) -> (SemiconjBy.{x} R (Distrib.toHasMul.{x} R _inst_1) (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R _inst_1)) a b) x y)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.64 : Distrib.{x} R] {a : R} {b : R} {x : R} {y : R}, (SemiconjBy.{x} R (Distrib.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.64) a x y) -> (SemiconjBy.{x} R (Distrib.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.64) b x y) -> (SemiconjBy.{x} R (Distrib.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.64) (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toAdd.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.64)) a b) x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.add_left SemiconjBy.add_leftₓ'. -/
@[simp]
theorem add_left [Distrib R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) :
    SemiconjBy (a + b) x y := by simp only [SemiconjBy, left_distrib, right_distrib, ha.eq, hb.eq]
#align semiconj_by.add_left SemiconjBy.add_left

section

variable [Mul R] [HasDistribNeg R] {a x y : R}

/- warning: semiconj_by.neg_right -> SemiconjBy.neg_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Mul.{x} R] [_inst_2 : HasDistribNeg.{x} R _inst_1] {a : R} {x : R} {y : R}, (SemiconjBy.{x} R _inst_1 a x y) -> (SemiconjBy.{x} R _inst_1 a (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R _inst_1 _inst_2)) x) (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R _inst_1 _inst_2)) y))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.121 : Mul.{x} R] [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.124 : HasDistribNeg.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.121] {a : R} {x : R} {y : R}, (SemiconjBy.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.121 a x y) -> (SemiconjBy.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.121 a (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.121 inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.124)) x) (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.121 inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.124)) y))
Case conversion may be inaccurate. Consider using '#align semiconj_by.neg_right SemiconjBy.neg_rightₓ'. -/
theorem neg_right (h : SemiconjBy a x y) : SemiconjBy a (-x) (-y) := by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]
#align semiconj_by.neg_right SemiconjBy.neg_right

/- warning: semiconj_by.neg_right_iff -> SemiconjBy.neg_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Mul.{x} R] [_inst_2 : HasDistribNeg.{x} R _inst_1] {a : R} {x : R} {y : R}, Iff (SemiconjBy.{x} R _inst_1 a (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R _inst_1 _inst_2)) x) (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R _inst_1 _inst_2)) y)) (SemiconjBy.{x} R _inst_1 a x y)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.159 : Mul.{x} R] [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.162 : HasDistribNeg.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.159] {a : R} {x : R} {y : R}, Iff (SemiconjBy.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.159 a (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.159 inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.162)) x) (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.159 inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.162)) y)) (SemiconjBy.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.159 a x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.neg_right_iff SemiconjBy.neg_right_iffₓ'. -/
@[simp]
theorem neg_right_iff : SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg x ▸ neg_neg y ▸ h.neg_right, SemiconjBy.neg_right⟩
#align semiconj_by.neg_right_iff SemiconjBy.neg_right_iff

/- warning: semiconj_by.neg_left -> SemiconjBy.neg_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Mul.{x} R] [_inst_2 : HasDistribNeg.{x} R _inst_1] {a : R} {x : R} {y : R}, (SemiconjBy.{x} R _inst_1 a x y) -> (SemiconjBy.{x} R _inst_1 (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R _inst_1 _inst_2)) a) x y)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.212 : Mul.{x} R] [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.215 : HasDistribNeg.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.212] {a : R} {x : R} {y : R}, (SemiconjBy.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.212 a x y) -> (SemiconjBy.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.212 (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.212 inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.215)) a) x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.neg_left SemiconjBy.neg_leftₓ'. -/
theorem neg_left (h : SemiconjBy a x y) : SemiconjBy (-a) x y := by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]
#align semiconj_by.neg_left SemiconjBy.neg_left

/- warning: semiconj_by.neg_left_iff -> SemiconjBy.neg_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Mul.{x} R] [_inst_2 : HasDistribNeg.{x} R _inst_1] {a : R} {x : R} {y : R}, Iff (SemiconjBy.{x} R _inst_1 (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R _inst_1 _inst_2)) a) x y) (SemiconjBy.{x} R _inst_1 a x y)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.245 : Mul.{x} R] [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.248 : HasDistribNeg.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.245] {a : R} {x : R} {y : R}, Iff (SemiconjBy.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.245 (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.245 inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.248)) a) x y) (SemiconjBy.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.245 a x y)
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
  forall {R : Type.{x}} [_inst_1 : MulOneClass.{x} R] [_inst_2 : HasDistribNeg.{x} R (MulOneClass.toHasMul.{x} R _inst_1)] (a : R), SemiconjBy.{x} R (MulOneClass.toHasMul.{x} R _inst_1) a (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R (MulOneClass.toHasMul.{x} R _inst_1) _inst_2)) (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (MulOneClass.toHasOne.{x} R _inst_1))))) (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R (MulOneClass.toHasMul.{x} R _inst_1) _inst_2)) (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (MulOneClass.toHasOne.{x} R _inst_1)))))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.309 : MulOneClass.{x} R] [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.312 : HasDistribNeg.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.309)] (a : R), SemiconjBy.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.309) a (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.309) inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.312)) (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (MulOneClass.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.309)))) (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.309) inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.312)) (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (MulOneClass.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.309))))
Case conversion may be inaccurate. Consider using '#align semiconj_by.neg_one_right SemiconjBy.neg_one_rightₓ'. -/
@[simp]
theorem neg_one_right (a : R) : SemiconjBy a (-1) (-1) :=
  (one_right a).neg_right
#align semiconj_by.neg_one_right SemiconjBy.neg_one_right

/- warning: semiconj_by.neg_one_left -> SemiconjBy.neg_one_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : MulOneClass.{x} R] [_inst_2 : HasDistribNeg.{x} R (MulOneClass.toHasMul.{x} R _inst_1)] (x : R), SemiconjBy.{x} R (MulOneClass.toHasMul.{x} R _inst_1) (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R (MulOneClass.toHasMul.{x} R _inst_1) _inst_2)) (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (MulOneClass.toHasOne.{x} R _inst_1))))) x x
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.344 : MulOneClass.{x} R] [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.347 : HasDistribNeg.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.344)] (x : R), SemiconjBy.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.344) (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.344) inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.347)) (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (MulOneClass.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.344)))) x x
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
  forall {R : Type.{x}} [_inst_1 : NonUnitalNonAssocRing.{x} R] {a : R} {x : R} {y : R} {x' : R} {y' : R}, (SemiconjBy.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a x y) -> (SemiconjBy.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a x' y') -> (SemiconjBy.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R _inst_1))))) x x') (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R _inst_1))))) y y'))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.397 : NonUnitalNonAssocRing.{x} R] {a : R} {x : R} {y : R} {x' : R} {y' : R}, (SemiconjBy.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.397) a x y) -> (SemiconjBy.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.397) a x' y') -> (SemiconjBy.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.397) a (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.397))))) x x') (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.397))))) y y'))
Case conversion may be inaccurate. Consider using '#align semiconj_by.sub_right SemiconjBy.sub_rightₓ'. -/
@[simp]
theorem sub_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x - x') (y - y') := by simpa only [sub_eq_add_neg] using h.add_right h'.neg_right
#align semiconj_by.sub_right SemiconjBy.sub_right

/- warning: semiconj_by.sub_left -> SemiconjBy.sub_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : NonUnitalNonAssocRing.{x} R] {a : R} {b : R} {x : R} {y : R}, (SemiconjBy.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a x y) -> (SemiconjBy.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) b x y) -> (SemiconjBy.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R _inst_1))))) a b) x y)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.467 : NonUnitalNonAssocRing.{x} R] {a : R} {b : R} {x : R} {y : R}, (SemiconjBy.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.467) a x y) -> (SemiconjBy.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.467) b x y) -> (SemiconjBy.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.467) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R inst._@.Mathlib.Algebra.Ring.Semiconj._hyg.467))))) a b) x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.sub_left SemiconjBy.sub_leftₓ'. -/
@[simp]
theorem sub_left (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) : SemiconjBy (a - b) x y := by
  simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left
#align semiconj_by.sub_left SemiconjBy.sub_left

end

end SemiconjBy

