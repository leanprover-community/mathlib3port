/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland

! This file was ported from Lean 3 source module algebra.ring.commute
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Semiconj
import Mathbin.Algebra.Ring.Units
import Mathbin.Algebra.Group.Commute

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

namespace Commute

@[simp]
theorem add_right [Distrib R] {a b c : R} : Commute a b → Commute a c → Commute a (b + c) :=
  SemiconjBy.add_right
#align commute.add_right Commute.add_rightₓ

@[simp]
theorem add_left [Distrib R] {a b c : R} : Commute a c → Commute b c → Commute (a + b) c :=
  SemiconjBy.add_left
#align commute.add_left Commute.add_leftₓ

/- warning: commute.bit0_right -> Commute.bit0_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R] {x : R} {y : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R _inst_1) x y) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R _inst_1) x (bit0.{u1} R (Distrib.toHasAdd.{u1} R _inst_1) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R] {x : R} {y : R}, (Commute.{u1} R (Distrib.toMul.{u1} R _inst_1) x y) -> (Commute.{u1} R (Distrib.toMul.{u1} R _inst_1) x (bit0.{u1} R (Distrib.toAdd.{u1} R _inst_1) y))
Case conversion may be inaccurate. Consider using '#align commute.bit0_right Commute.bit0_rightₓ'. -/
theorem bit0_right [Distrib R] {x y : R} (h : Commute x y) : Commute x (bit0 y) :=
  h.add_right h
#align commute.bit0_right Commute.bit0_right

/- warning: commute.bit0_left -> Commute.bit0_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R] {x : R} {y : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R _inst_1) x y) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R _inst_1) (bit0.{u1} R (Distrib.toHasAdd.{u1} R _inst_1) x) y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Distrib.{u1} R] {x : R} {y : R}, (Commute.{u1} R (Distrib.toMul.{u1} R _inst_1) x y) -> (Commute.{u1} R (Distrib.toMul.{u1} R _inst_1) (bit0.{u1} R (Distrib.toAdd.{u1} R _inst_1) x) y)
Case conversion may be inaccurate. Consider using '#align commute.bit0_left Commute.bit0_leftₓ'. -/
theorem bit0_left [Distrib R] {x y : R} (h : Commute x y) : Commute (bit0 x) y :=
  h.add_left h
#align commute.bit0_left Commute.bit0_left

/- warning: commute.bit1_right -> Commute.bit1_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] {x : R} {y : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) x y) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) x (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] {x : R} {y : R}, (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) x y) -> (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) x (bit1.{u1} R (NonAssocSemiring.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) y))
Case conversion may be inaccurate. Consider using '#align commute.bit1_right Commute.bit1_rightₓ'. -/
theorem bit1_right [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute x (bit1 y) :=
  h.bit0_right.add_right (Commute.one_right x)
#align commute.bit1_right Commute.bit1_right

/- warning: commute.bit1_left -> Commute.bit1_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] {x : R} {y : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) x y) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (bit1.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_1))) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) x) y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocSemiring.{u1} R] {x : R} {y : R}, (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) x y) -> (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1)) (bit1.{u1} R (NonAssocSemiring.toOne.{u1} R _inst_1) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) x) y)
Case conversion may be inaccurate. Consider using '#align commute.bit1_left Commute.bit1_leftₓ'. -/
theorem bit1_left [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute (bit1 x) y :=
  h.bit0_left.add_left (Commute.one_left y)
#align commute.bit1_left Commute.bit1_left

/- warning: commute.mul_self_sub_mul_self_eq -> Commute.mul_self_sub_mul_self_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {b : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a b) -> (Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) a a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) b b)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) a b) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) a b)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {b : R}, (Commute.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a b) -> (Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) a a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) b b)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) a b) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) a b)))
Case conversion may be inaccurate. Consider using '#align commute.mul_self_sub_mul_self_eq Commute.mul_self_sub_mul_self_eqₓ'. -/
/-- Representation of a difference of two squares of commuting elements as a product. -/
theorem mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b) := by rw [add_mul, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]
#align commute.mul_self_sub_mul_self_eq Commute.mul_self_sub_mul_self_eq

/- warning: commute.mul_self_sub_mul_self_eq' -> Commute.mul_self_sub_mul_self_eq' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {b : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a b) -> (Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) a a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) b b)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) a b) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) a b)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {b : R}, (Commute.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a b) -> (Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) a a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) b b)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) a b) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) a b)))
Case conversion may be inaccurate. Consider using '#align commute.mul_self_sub_mul_self_eq' Commute.mul_self_sub_mul_self_eq'ₓ'. -/
theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]
#align commute.mul_self_sub_mul_self_eq' Commute.mul_self_sub_mul_self_eq'

/- warning: commute.mul_self_eq_mul_self_iff -> Commute.mul_self_eq_mul_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))] {a : R} {b : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a b) -> (Iff (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) a a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))) b b)) (Or (Eq.{succ u1} R a b) (Eq.{succ u1} R a (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1)))) b))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1)))] {a : R} {b : R}, (Commute.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a b) -> (Iff (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) a a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1)) b b)) (Or (Eq.{succ u1} R a b) (Eq.{succ u1} R a (Neg.neg.{u1} R (NegZeroClass.toNeg.{u1} R (SubNegZeroMonoid.toNegZeroClass.{u1} R (SubtractionMonoid.toSubNegZeroMonoid.{u1} R (SubtractionCommMonoid.toSubtractionMonoid.{u1} R (AddCommGroup.toDivisionAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1)))))) b))))
Case conversion may be inaccurate. Consider using '#align commute.mul_self_eq_mul_self_iff Commute.mul_self_eq_mul_self_iffₓ'. -/
theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R}
    (h : Commute a b) : a * a = b * b ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm', sub_eq_zero,
    add_eq_zero_iff_eq_neg]
#align commute.mul_self_eq_mul_self_iff Commute.mul_self_eq_mul_self_iff

section

variable [Mul R] [HasDistribNeg R] {a b : R}

/- warning: commute.neg_right -> Commute.neg_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {b : R}, (Commute.{u1} R _inst_1 a b) -> (Commute.{u1} R _inst_1 a (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R _inst_1 _inst_2)) b))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {b : R}, (Commute.{u1} R _inst_1 a b) -> (Commute.{u1} R _inst_1 a (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R _inst_1 _inst_2)) b))
Case conversion may be inaccurate. Consider using '#align commute.neg_right Commute.neg_rightₓ'. -/
theorem neg_right : Commute a b → Commute a (-b) :=
  SemiconjBy.neg_right
#align commute.neg_right Commute.neg_right

/- warning: commute.neg_right_iff -> Commute.neg_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {b : R}, Iff (Commute.{u1} R _inst_1 a (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R _inst_1 _inst_2)) b)) (Commute.{u1} R _inst_1 a b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {b : R}, Iff (Commute.{u1} R _inst_1 a (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R _inst_1 _inst_2)) b)) (Commute.{u1} R _inst_1 a b)
Case conversion may be inaccurate. Consider using '#align commute.neg_right_iff Commute.neg_right_iffₓ'. -/
@[simp]
theorem neg_right_iff : Commute a (-b) ↔ Commute a b :=
  SemiconjBy.neg_right_iff
#align commute.neg_right_iff Commute.neg_right_iff

/- warning: commute.neg_left -> Commute.neg_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {b : R}, (Commute.{u1} R _inst_1 a b) -> (Commute.{u1} R _inst_1 (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R _inst_1 _inst_2)) a) b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {b : R}, (Commute.{u1} R _inst_1 a b) -> (Commute.{u1} R _inst_1 (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R _inst_1 _inst_2)) a) b)
Case conversion may be inaccurate. Consider using '#align commute.neg_left Commute.neg_leftₓ'. -/
theorem neg_left : Commute a b → Commute (-a) b :=
  SemiconjBy.neg_left
#align commute.neg_left Commute.neg_left

/- warning: commute.neg_left_iff -> Commute.neg_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {b : R}, Iff (Commute.{u1} R _inst_1 (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R _inst_1 _inst_2)) a) b) (Commute.{u1} R _inst_1 a b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Mul.{u1} R] [_inst_2 : HasDistribNeg.{u1} R _inst_1] {a : R} {b : R}, Iff (Commute.{u1} R _inst_1 (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R _inst_1 _inst_2)) a) b) (Commute.{u1} R _inst_1 a b)
Case conversion may be inaccurate. Consider using '#align commute.neg_left_iff Commute.neg_left_iffₓ'. -/
@[simp]
theorem neg_left_iff : Commute (-a) b ↔ Commute a b :=
  SemiconjBy.neg_left_iff
#align commute.neg_left_iff Commute.neg_left_iff

end

section

variable [MulOneClass R] [HasDistribNeg R] {a : R}

/- warning: commute.neg_one_right -> Commute.neg_one_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : HasDistribNeg.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1)] (a : R), Commute.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) a (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : HasDistribNeg.{u1} R (MulOneClass.toMul.{u1} R _inst_1)] (a : R), Commute.{u1} R (MulOneClass.toMul.{u1} R _inst_1) a (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R (MulOneClass.toMul.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (MulOneClass.toOne.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align commute.neg_one_right Commute.neg_one_rightₓ'. -/
@[simp]
theorem neg_one_right (a : R) : Commute a (-1) :=
  SemiconjBy.neg_one_right a
#align commute.neg_one_right Commute.neg_one_right

/- warning: commute.neg_one_left -> Commute.neg_one_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : HasDistribNeg.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1)] (a : R), Commute.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) (Neg.neg.{u1} R (InvolutiveNeg.toHasNeg.{u1} R (HasDistribNeg.toHasInvolutiveNeg.{u1} R (MulOneClass.toHasMul.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R _inst_1))))) a
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : MulOneClass.{u1} R] [_inst_2 : HasDistribNeg.{u1} R (MulOneClass.toMul.{u1} R _inst_1)] (a : R), Commute.{u1} R (MulOneClass.toMul.{u1} R _inst_1) (Neg.neg.{u1} R (InvolutiveNeg.toNeg.{u1} R (HasDistribNeg.toInvolutiveNeg.{u1} R (MulOneClass.toMul.{u1} R _inst_1) _inst_2)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (MulOneClass.toOne.{u1} R _inst_1)))) a
Case conversion may be inaccurate. Consider using '#align commute.neg_one_left Commute.neg_one_leftₓ'. -/
@[simp]
theorem neg_one_left (a : R) : Commute (-1) a :=
  SemiconjBy.neg_one_left a
#align commute.neg_one_left Commute.neg_one_left

end

section

variable [NonUnitalNonAssocRing R] {a b c : R}

/- warning: commute.sub_right -> Commute.sub_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {b : R} {c : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a b) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a c) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) b c))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {b : R} {c : R}, (Commute.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a b) -> (Commute.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a c) -> (Commute.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align commute.sub_right Commute.sub_rightₓ'. -/
@[simp]
theorem sub_right : Commute a b → Commute a c → Commute a (b - c) :=
  SemiconjBy.sub_right
#align commute.sub_right Commute.sub_right

/- warning: commute.sub_left -> Commute.sub_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {b : R} {c : R}, (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) a c) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) b c) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R _inst_1))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) a b) c)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocRing.{u1} R] {a : R} {b : R} {c : R}, (Commute.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) a c) -> (Commute.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) b c) -> (Commute.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align commute.sub_left Commute.sub_leftₓ'. -/
@[simp]
theorem sub_left : Commute a c → Commute b c → Commute (a - b) c :=
  SemiconjBy.sub_left
#align commute.sub_left Commute.sub_left

end

end Commute

/- warning: mul_self_sub_mul_self -> mul_self_sub_mul_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (a : R) (b : R), Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) a a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) b b)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) a b) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) a b))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (a : R) (b : R), Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) a a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) b b)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) a b) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align mul_self_sub_mul_self mul_self_sub_mul_selfₓ'. -/
/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self [CommRing R] (a b : R) : a * a - b * b = (a + b) * (a - b) :=
  (Commute.all a b).mul_self_sub_mul_self_eq
#align mul_self_sub_mul_self mul_self_sub_mul_self

/- warning: mul_self_sub_one -> mul_self_sub_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] (a : R), Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) a a) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) a (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))))) a (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] (a : R), Eq.{succ u1} R (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (AddGroupWithOne.toSub.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) a a) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) a (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (AddGroupWithOne.toSub.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))) a (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align mul_self_sub_one mul_self_sub_oneₓ'. -/
theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq, mul_one]
#align mul_self_sub_one mul_self_sub_one

/- warning: mul_self_eq_mul_self_iff -> mul_self_eq_mul_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))] {a : R} {b : R}, Iff (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) a a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) b b)) (Or (Eq.{succ u1} R a b) (Eq.{succ u1} R a (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) b)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))] {a : R} {b : R}, Iff (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) a a) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) b b)) (Or (Eq.{succ u1} R a b) (Eq.{succ u1} R a (Neg.neg.{u1} R (Ring.toNeg.{u1} R (CommRing.toRing.{u1} R _inst_1)) b)))
Case conversion may be inaccurate. Consider using '#align mul_self_eq_mul_self_iff mul_self_eq_mul_self_iffₓ'. -/
theorem mul_self_eq_mul_self_iff [CommRing R] [NoZeroDivisors R] {a b : R} :
    a * a = b * b ↔ a = b ∨ a = -b :=
  (Commute.all a b).mul_self_eq_mul_self_iff
#align mul_self_eq_mul_self_iff mul_self_eq_mul_self_iff

/- warning: mul_self_eq_one_iff -> mul_self_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] {a : R}, Iff (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))) a a) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))))))) (Or (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1))))))) (Eq.{succ u1} R a (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] {a : R}, Iff (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) a a) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1)))) (Or (Eq.{succ u1} R a (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1)))) (Eq.{succ u1} R a (Neg.neg.{u1} R (AddGroupWithOne.toNeg.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (NonAssocRing.toOne.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align mul_self_eq_one_iff mul_self_eq_one_iffₓ'. -/
theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} :
    a * a = 1 ↔ a = 1 ∨ a = -1 := by rw [← (Commute.one_right a).mul_self_eq_mul_self_iff, mul_one]
#align mul_self_eq_one_iff mul_self_eq_one_iff

namespace Units

/- warning: units.inv_eq_self_iff -> Units.inv_eq_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))))] (u : Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)), Iff (Eq.{succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R _inst_1)) u) u) (Or (Eq.{succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) u (OfNat.ofNat.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) 1 (OfNat.mk.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) 1 (One.one.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u1} R (Ring.toMonoid.{u1} R _inst_1))))))) (Eq.{succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) u (Neg.neg.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) (Units.hasNeg.{u1} R (Ring.toMonoid.{u1} R _inst_1) (NonUnitalNonAssocRing.toHasDistribNeg.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) 1 (OfNat.mk.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) 1 (One.one.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u1} R (Ring.toMonoid.{u1} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))] (u : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))), Iff (Eq.{succ u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Units.instInvUnits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) u) u) (Or (Eq.{succ u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) u (OfNat.ofNat.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) 1 (One.toOfNat1.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (InvOneClass.toOne.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (DivInvOneMonoid.toInvOneClass.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (DivisionMonoid.toDivInvOneMonoid.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Group.toDivisionMonoid.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Units.instGroupUnits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))))))))))) (Eq.{succ u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) u (Neg.neg.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Units.instNegUnits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (NonUnitalNonAssocRing.toHasDistribNeg.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) 1 (One.toOfNat1.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (InvOneClass.toOne.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (DivInvOneMonoid.toInvOneClass.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (DivisionMonoid.toDivInvOneMonoid.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Group.toDivisionMonoid.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))) (Units.instGroupUnits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1)))))))))))))
Case conversion may be inaccurate. Consider using '#align units.inv_eq_self_iff Units.inv_eq_self_iffₓ'. -/
/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
theorem inv_eq_self_iff [Ring R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 :=
  by
  rw [inv_eq_iff_mul_eq_one]
  simp only [ext_iff]
  push_cast
  exact mul_self_eq_one_iff
#align units.inv_eq_self_iff Units.inv_eq_self_iff

end Units

