/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathbin.Algebra.Ring.Semiconj
import Mathbin.Algebra.Ring.Units
import Mathbin.Algebra.Group.Commute

/-!
# Semirings and rings

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
  forall {R : Type.{x}} [_inst_1 : Distrib.{x} R] {x : R} {y : R}, (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) x y) -> (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) x (bit0.{x} R (Distrib.toHasAdd.{x} R _inst_1) y))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.82 : Distrib.{x} R] {x : R} {y : R}, (Commute.{x} R (Distrib.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.82) x y) -> (Commute.{x} R (Distrib.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.82) x (bit0.{x} R (Distrib.toAdd.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.82) y))
Case conversion may be inaccurate. Consider using '#align commute.bit0_right Commute.bit0_rightₓ'. -/
theorem bit0_right [Distrib R] {x y : R} (h : Commute x y) : Commute x (bit0 y) :=
  h.add_right h
#align commute.bit0_right Commute.bit0_right

/- warning: commute.bit0_left -> Commute.bit0_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Distrib.{x} R] {x : R} {y : R}, (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) x y) -> (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) (bit0.{x} R (Distrib.toHasAdd.{x} R _inst_1) x) y)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.104 : Distrib.{x} R] {x : R} {y : R}, (Commute.{x} R (Distrib.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.104) x y) -> (Commute.{x} R (Distrib.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.104) (bit0.{x} R (Distrib.toAdd.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.104) x) y)
Case conversion may be inaccurate. Consider using '#align commute.bit0_left Commute.bit0_leftₓ'. -/
theorem bit0_left [Distrib R] {x y : R} (h : Commute x y) : Commute (bit0 x) y :=
  h.add_left h
#align commute.bit0_left Commute.bit0_left

/- warning: commute.bit1_right -> Commute.bit1_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : NonAssocSemiring.{x} R] {x : R} {y : R}, (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R _inst_1))) x y) -> (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R _inst_1))) x (bit1.{x} R (AddMonoidWithOne.toOne.{x} R (AddCommMonoidWithOne.toAddMonoidWithOne.{x} R (NonAssocSemiring.toAddCommMonoidWithOne.{x} R _inst_1))) (Distrib.toHasAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R _inst_1))) y))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.126 : NonAssocSemiring.{x} R] {x : R} {y : R}, (Commute.{x} R (NonUnitalNonAssocSemiring.toMul.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.126)) x y) -> (Commute.{x} R (NonUnitalNonAssocSemiring.toMul.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.126)) x (bit1.{x} R (NonAssocSemiring.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.126) (Distrib.toAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.126))) y))
Case conversion may be inaccurate. Consider using '#align commute.bit1_right Commute.bit1_rightₓ'. -/
theorem bit1_right [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute x (bit1 y) :=
  h.bit0_right.add_right (Commute.one_right x)
#align commute.bit1_right Commute.bit1_right

/- warning: commute.bit1_left -> Commute.bit1_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : NonAssocSemiring.{x} R] {x : R} {y : R}, (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R _inst_1))) x y) -> (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R _inst_1))) (bit1.{x} R (AddMonoidWithOne.toOne.{x} R (AddCommMonoidWithOne.toAddMonoidWithOne.{x} R (NonAssocSemiring.toAddCommMonoidWithOne.{x} R _inst_1))) (Distrib.toHasAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R _inst_1))) x) y)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.151 : NonAssocSemiring.{x} R] {x : R} {y : R}, (Commute.{x} R (NonUnitalNonAssocSemiring.toMul.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.151)) x y) -> (Commute.{x} R (NonUnitalNonAssocSemiring.toMul.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.151)) (bit1.{x} R (NonAssocSemiring.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.151) (Distrib.toAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.151))) x) y)
Case conversion may be inaccurate. Consider using '#align commute.bit1_left Commute.bit1_leftₓ'. -/
theorem bit1_left [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute (bit1 x) y :=
  h.bit0_left.add_left (Commute.one_left y)
#align commute.bit1_left Commute.bit1_left

/- warning: commute.mul_self_sub_mul_self_eq -> Commute.mul_self_sub_mul_self_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : NonUnitalNonAssocRing.{x} R] {a : R} {b : R}, (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a b) -> (Eq.{succ x} R (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R _inst_1))))) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))) a a) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))) b b)) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))) (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))) a b) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R _inst_1))))) a b)))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.177 : NonUnitalNonAssocRing.{x} R] {a : R} {b : R}, (Commute.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.177) a b) -> (Eq.{succ x} R (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.177))))) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.177)) a a) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.177)) b b)) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.177)) (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.177)))) a b) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.177))))) a b)))
Case conversion may be inaccurate. Consider using '#align commute.mul_self_sub_mul_self_eq Commute.mul_self_sub_mul_self_eqₓ'. -/
/-- Representation of a difference of two squares of commuting elements as a product. -/
theorem mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b) := by rw [add_mul, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]
#align commute.mul_self_sub_mul_self_eq Commute.mul_self_sub_mul_self_eq

/- warning: commute.mul_self_sub_mul_self_eq' -> Commute.mul_self_sub_mul_self_eq' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : NonUnitalNonAssocRing.{x} R] {a : R} {b : R}, (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a b) -> (Eq.{succ x} R (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R _inst_1))))) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))) a a) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))) b b)) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R _inst_1))))) a b) (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))) a b)))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.241 : NonUnitalNonAssocRing.{x} R] {a : R} {b : R}, (Commute.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.241) a b) -> (Eq.{succ x} R (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.241))))) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.241)) a a) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.241)) b b)) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.241)) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.241))))) a b) (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.241)))) a b)))
Case conversion may be inaccurate. Consider using '#align commute.mul_self_sub_mul_self_eq' Commute.mul_self_sub_mul_self_eq'ₓ'. -/
theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]
#align commute.mul_self_sub_mul_self_eq' Commute.mul_self_sub_mul_self_eq'

/- warning: commute.mul_self_eq_mul_self_iff -> Commute.mul_self_eq_mul_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : NonUnitalNonAssocRing.{x} R] [_inst_2 : NoZeroDivisors.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) (MulZeroClass.toHasZero.{x} R (NonUnitalNonAssocSemiring.toMulZeroClass.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))] {a : R} {b : R}, (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a b) -> (Iff (Eq.{succ x} R (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))) a a) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1)))) b b)) (Or (Eq.{succ x} R a b) (Eq.{succ x} R a (Neg.neg.{x} R (SubNegMonoid.toHasNeg.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R _inst_1)))) b))))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.305 : NonUnitalNonAssocRing.{x} R] [inst._@.Mathlib.Algebra.Ring.Commute._hyg.308 : NoZeroDivisors.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.305) (MulZeroClass.toZero.{x} R (NonUnitalNonAssocSemiring.toMulZeroClass.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.305)))] {a : R} {b : R}, (Commute.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.305) a b) -> (Iff (Eq.{succ x} R (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.305)) a a) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.305)) b b)) (Or (Eq.{succ x} R a b) (Eq.{succ x} R a (Neg.neg.{x} R (NegZeroClass.toNeg.{x} R (SubNegZeroMonoid.toNegZeroClass.{x} R (SubtractionMonoid.toSubNegZeroMonoid.{x} R (SubtractionCommMonoid.toSubtractionMonoid.{x} R (AddCommGroup.toSubtractionCommMonoid.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.305)))))) b))))
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
  forall {R : Type.{x}} [_inst_1 : Mul.{x} R] [_inst_2 : HasDistribNeg.{x} R _inst_1] {a : R} {b : R}, (Commute.{x} R _inst_1 a b) -> (Commute.{x} R _inst_1 a (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R _inst_1 _inst_2)) b))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.399 : Mul.{x} R] [inst._@.Mathlib.Algebra.Ring.Commute._hyg.402 : HasDistribNeg.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.399] {a : R} {b : R}, (Commute.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.399 a b) -> (Commute.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.399 a (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.399 inst._@.Mathlib.Algebra.Ring.Commute._hyg.402)) b))
Case conversion may be inaccurate. Consider using '#align commute.neg_right Commute.neg_rightₓ'. -/
theorem neg_right : Commute a b → Commute a (-b) :=
  SemiconjBy.neg_right
#align commute.neg_right Commute.neg_right

/- warning: commute.neg_right_iff -> Commute.neg_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Mul.{x} R] [_inst_2 : HasDistribNeg.{x} R _inst_1] {a : R} {b : R}, Iff (Commute.{x} R _inst_1 a (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R _inst_1 _inst_2)) b)) (Commute.{x} R _inst_1 a b)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.426 : Mul.{x} R] [inst._@.Mathlib.Algebra.Ring.Commute._hyg.429 : HasDistribNeg.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.426] {a : R} {b : R}, Iff (Commute.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.426 a (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.426 inst._@.Mathlib.Algebra.Ring.Commute._hyg.429)) b)) (Commute.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.426 a b)
Case conversion may be inaccurate. Consider using '#align commute.neg_right_iff Commute.neg_right_iffₓ'. -/
@[simp]
theorem neg_right_iff : Commute a (-b) ↔ Commute a b :=
  SemiconjBy.neg_right_iff
#align commute.neg_right_iff Commute.neg_right_iff

/- warning: commute.neg_left -> Commute.neg_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Mul.{x} R] [_inst_2 : HasDistribNeg.{x} R _inst_1] {a : R} {b : R}, (Commute.{x} R _inst_1 a b) -> (Commute.{x} R _inst_1 (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R _inst_1 _inst_2)) a) b)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.455 : Mul.{x} R] [inst._@.Mathlib.Algebra.Ring.Commute._hyg.458 : HasDistribNeg.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.455] {a : R} {b : R}, (Commute.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.455 a b) -> (Commute.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.455 (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.455 inst._@.Mathlib.Algebra.Ring.Commute._hyg.458)) a) b)
Case conversion may be inaccurate. Consider using '#align commute.neg_left Commute.neg_leftₓ'. -/
theorem neg_left : Commute a b → Commute (-a) b :=
  SemiconjBy.neg_left
#align commute.neg_left Commute.neg_left

/- warning: commute.neg_left_iff -> Commute.neg_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Mul.{x} R] [_inst_2 : HasDistribNeg.{x} R _inst_1] {a : R} {b : R}, Iff (Commute.{x} R _inst_1 (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R _inst_1 _inst_2)) a) b) (Commute.{x} R _inst_1 a b)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.482 : Mul.{x} R] [inst._@.Mathlib.Algebra.Ring.Commute._hyg.485 : HasDistribNeg.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.482] {a : R} {b : R}, Iff (Commute.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.482 (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.482 inst._@.Mathlib.Algebra.Ring.Commute._hyg.485)) a) b) (Commute.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.482 a b)
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
  forall {R : Type.{x}} [_inst_1 : MulOneClass.{x} R] [_inst_2 : HasDistribNeg.{x} R (MulOneClass.toHasMul.{x} R _inst_1)] (a : R), Commute.{x} R (MulOneClass.toHasMul.{x} R _inst_1) a (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R (MulOneClass.toHasMul.{x} R _inst_1) _inst_2)) (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (MulOneClass.toHasOne.{x} R _inst_1)))))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.528 : MulOneClass.{x} R] [inst._@.Mathlib.Algebra.Ring.Commute._hyg.531 : HasDistribNeg.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.528)] (a : R), Commute.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.528) a (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.528) inst._@.Mathlib.Algebra.Ring.Commute._hyg.531)) (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (MulOneClass.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.528))))
Case conversion may be inaccurate. Consider using '#align commute.neg_one_right Commute.neg_one_rightₓ'. -/
@[simp]
theorem neg_one_right (a : R) : Commute a (-1) :=
  SemiconjBy.neg_one_right a
#align commute.neg_one_right Commute.neg_one_right

/- warning: commute.neg_one_left -> Commute.neg_one_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : MulOneClass.{x} R] [_inst_2 : HasDistribNeg.{x} R (MulOneClass.toHasMul.{x} R _inst_1)] (a : R), Commute.{x} R (MulOneClass.toHasMul.{x} R _inst_1) (Neg.neg.{x} R (HasInvolutiveNeg.toHasNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R (MulOneClass.toHasMul.{x} R _inst_1) _inst_2)) (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (MulOneClass.toHasOne.{x} R _inst_1))))) a
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.552 : MulOneClass.{x} R] [inst._@.Mathlib.Algebra.Ring.Commute._hyg.555 : HasDistribNeg.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.552)] (a : R), Commute.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.552) (Neg.neg.{x} R (HasInvolutiveNeg.toNeg.{x} R (HasDistribNeg.toHasInvolutiveNeg.{x} R (MulOneClass.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.552) inst._@.Mathlib.Algebra.Ring.Commute._hyg.555)) (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (MulOneClass.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.552)))) a
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
  forall {R : Type.{x}} [_inst_1 : NonUnitalNonAssocRing.{x} R] {a : R} {b : R} {c : R}, (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a b) -> (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a c) -> (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R _inst_1))))) b c))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.593 : NonUnitalNonAssocRing.{x} R] {a : R} {b : R} {c : R}, (Commute.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.593) a b) -> (Commute.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.593) a c) -> (Commute.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.593) a (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.593))))) b c))
Case conversion may be inaccurate. Consider using '#align commute.sub_right Commute.sub_rightₓ'. -/
@[simp]
theorem sub_right : Commute a b → Commute a c → Commute a (b - c) :=
  SemiconjBy.sub_right
#align commute.sub_right Commute.sub_right

/- warning: commute.sub_left -> Commute.sub_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : NonUnitalNonAssocRing.{x} R] {a : R} {b : R} {c : R}, (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) a c) -> (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) b c) -> (Commute.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R _inst_1))) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R _inst_1))))) a b) c)
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.623 : NonUnitalNonAssocRing.{x} R] {a : R} {b : R} {c : R}, (Commute.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.623) a c) -> (Commute.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.623) b c) -> (Commute.{x} R (NonUnitalNonAssocRing.toMul.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.623) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddCommGroup.toAddGroup.{x} R (NonUnitalNonAssocRing.toAddCommGroup.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.623))))) a b) c)
Case conversion may be inaccurate. Consider using '#align commute.sub_left Commute.sub_leftₓ'. -/
@[simp]
theorem sub_left : Commute a c → Commute b c → Commute (a - b) c :=
  SemiconjBy.sub_left
#align commute.sub_left Commute.sub_left

end

end Commute

/- warning: mul_self_sub_mul_self -> mul_self_sub_mul_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : CommRing.{x} R] (a : R) (b : R), Eq.{succ x} R (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddGroupWithOne.toAddGroup.{x} R (NonAssocRing.toAddGroupWithOne.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R _inst_1))))))) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (Ring.toDistrib.{x} R (CommRing.toRing.{x} R _inst_1)))) a a) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (Ring.toDistrib.{x} R (CommRing.toRing.{x} R _inst_1)))) b b)) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (Ring.toDistrib.{x} R (CommRing.toRing.{x} R _inst_1)))) (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R (Ring.toDistrib.{x} R (CommRing.toRing.{x} R _inst_1)))) a b) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddGroupWithOne.toAddGroup.{x} R (NonAssocRing.toAddGroupWithOne.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R _inst_1))))))) a b))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.655 : CommRing.{x} R] (a : R) (b : R), Eq.{succ x} R (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (Ring.toSub.{x} R (CommRing.toRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.655))) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.655))))) a a) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.655))))) b b)) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.655))))) (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.655))))))) a b) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (Ring.toSub.{x} R (CommRing.toRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.655))) a b))
Case conversion may be inaccurate. Consider using '#align mul_self_sub_mul_self mul_self_sub_mul_selfₓ'. -/
/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self [CommRing R] (a b : R) : a * a - b * b = (a + b) * (a - b) :=
  (Commute.all a b).mul_self_sub_mul_self_eq
#align mul_self_sub_mul_self mul_self_sub_mul_self

/- warning: mul_self_sub_one -> mul_self_sub_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : NonAssocRing.{x} R] (a : R), Eq.{succ x} R (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddGroupWithOne.toAddGroup.{x} R (NonAssocRing.toAddGroupWithOne.{x} R _inst_1))))) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R _inst_1))))) a a) (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (AddMonoidWithOne.toOne.{x} R (AddGroupWithOne.toAddMonoidWithOne.{x} R (NonAssocRing.toAddGroupWithOne.{x} R _inst_1))))))) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R _inst_1))))) (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R _inst_1))))) a (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (AddMonoidWithOne.toOne.{x} R (AddGroupWithOne.toAddMonoidWithOne.{x} R (NonAssocRing.toAddGroupWithOne.{x} R _inst_1))))))) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (SubNegMonoid.toHasSub.{x} R (AddGroup.toSubNegMonoid.{x} R (AddGroupWithOne.toAddGroup.{x} R (NonAssocRing.toAddGroupWithOne.{x} R _inst_1))))) a (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (AddMonoidWithOne.toOne.{x} R (AddGroupWithOne.toAddMonoidWithOne.{x} R (NonAssocRing.toAddGroupWithOne.{x} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.689 : NonAssocRing.{x} R] (a : R), Eq.{succ x} R (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (AddGroupWithOne.toSub.{x} R (NonAssocRing.toAddGroupWithOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.689))) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.689))) a a) (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (NonAssocRing.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.689)))) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.689))) (HAdd.hAdd.{x, x, x} R R R (instHAdd.{x} R (Distrib.toAdd.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.689))))) a (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (NonAssocRing.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.689)))) (HSub.hSub.{x, x, x} R R R (instHSub.{x} R (AddGroupWithOne.toSub.{x} R (NonAssocRing.toAddGroupWithOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.689))) a (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (NonAssocRing.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.689)))))
Case conversion may be inaccurate. Consider using '#align mul_self_sub_one mul_self_sub_oneₓ'. -/
theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq, mul_one]
#align mul_self_sub_one mul_self_sub_one

/- warning: mul_self_eq_mul_self_iff -> mul_self_eq_mul_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : CommRing.{x} R] [_inst_2 : NoZeroDivisors.{x} R (Distrib.toHasMul.{x} R (Ring.toDistrib.{x} R (CommRing.toRing.{x} R _inst_1))) (MulZeroClass.toHasZero.{x} R (NonUnitalNonAssocSemiring.toMulZeroClass.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R _inst_1))))))] {a : R} {b : R}, Iff (Eq.{succ x} R (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (Ring.toDistrib.{x} R (CommRing.toRing.{x} R _inst_1)))) a a) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (Ring.toDistrib.{x} R (CommRing.toRing.{x} R _inst_1)))) b b)) (Or (Eq.{succ x} R a b) (Eq.{succ x} R a (Neg.neg.{x} R (SubNegMonoid.toHasNeg.{x} R (AddGroup.toSubNegMonoid.{x} R (AddGroupWithOne.toAddGroup.{x} R (NonAssocRing.toAddGroupWithOne.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R _inst_1)))))) b)))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.748 : CommRing.{x} R] [inst._@.Mathlib.Algebra.Ring.Commute._hyg.751 : NoZeroDivisors.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.748)))) (CommMonoidWithZero.toZero.{x} R (CommSemiring.toCommMonoidWithZero.{x} R (CommRing.toCommSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.748)))] {a : R} {b : R}, Iff (Eq.{succ x} R (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.748))))) a a) (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R (CommRing.toRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.748))))) b b)) (Or (Eq.{succ x} R a b) (Eq.{succ x} R a (Neg.neg.{x} R (Ring.toNeg.{x} R (CommRing.toRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.748)) b)))
Case conversion may be inaccurate. Consider using '#align mul_self_eq_mul_self_iff mul_self_eq_mul_self_iffₓ'. -/
theorem mul_self_eq_mul_self_iff [CommRing R] [NoZeroDivisors R] {a b : R} :
    a * a = b * b ↔ a = b ∨ a = -b :=
  (Commute.all a b).mul_self_eq_mul_self_iff
#align mul_self_eq_mul_self_iff mul_self_eq_mul_self_iff

/- warning: mul_self_eq_one_iff -> mul_self_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : NonAssocRing.{x} R] [_inst_2 : NoZeroDivisors.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R _inst_1)))) (MulZeroClass.toHasZero.{x} R (NonUnitalNonAssocSemiring.toMulZeroClass.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R _inst_1))))] {a : R}, Iff (Eq.{succ x} R (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (Distrib.toHasMul.{x} R (NonUnitalNonAssocSemiring.toDistrib.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R _inst_1))))) a a) (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (AddMonoidWithOne.toOne.{x} R (AddGroupWithOne.toAddMonoidWithOne.{x} R (NonAssocRing.toAddGroupWithOne.{x} R _inst_1))))))) (Or (Eq.{succ x} R a (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (AddMonoidWithOne.toOne.{x} R (AddGroupWithOne.toAddMonoidWithOne.{x} R (NonAssocRing.toAddGroupWithOne.{x} R _inst_1))))))) (Eq.{succ x} R a (Neg.neg.{x} R (SubNegMonoid.toHasNeg.{x} R (AddGroup.toSubNegMonoid.{x} R (AddGroupWithOne.toAddGroup.{x} R (NonAssocRing.toAddGroupWithOne.{x} R _inst_1)))) (OfNat.ofNat.{x} R 1 (OfNat.mk.{x} R 1 (One.one.{x} R (AddMonoidWithOne.toOne.{x} R (AddGroupWithOne.toAddMonoidWithOne.{x} R (NonAssocRing.toAddGroupWithOne.{x} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.794 : NonAssocRing.{x} R] [inst._@.Mathlib.Algebra.Ring.Commute._hyg.797 : NoZeroDivisors.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.794)) (MulZeroOneClass.toZero.{x} R (NonAssocSemiring.toMulZeroOneClass.{x} R (NonAssocRing.toNonAssocSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.794)))] {a : R}, Iff (Eq.{succ x} R (HMul.hMul.{x, x, x} R R R (instHMul.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.794))) a a) (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (NonAssocRing.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.794)))) (Or (Eq.{succ x} R a (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (NonAssocRing.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.794)))) (Eq.{succ x} R a (Neg.neg.{x} R (AddGroupWithOne.toNeg.{x} R (NonAssocRing.toAddGroupWithOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.794)) (OfNat.ofNat.{x} R 1 (One.toOfNat1.{x} R (NonAssocRing.toOne.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.794))))))
Case conversion may be inaccurate. Consider using '#align mul_self_eq_one_iff mul_self_eq_one_iffₓ'. -/
theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} :
    a * a = 1 ↔ a = 1 ∨ a = -1 := by rw [← (Commute.one_right a).mul_self_eq_mul_self_iff, mul_one]
#align mul_self_eq_one_iff mul_self_eq_one_iff

namespace Units

/- warning: units.inv_eq_self_iff -> Units.inv_eq_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Ring.{x} R] [_inst_2 : NoZeroDivisors.{x} R (Distrib.toHasMul.{x} R (Ring.toDistrib.{x} R _inst_1)) (MulZeroClass.toHasZero.{x} R (NonUnitalNonAssocSemiring.toMulZeroClass.{x} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R _inst_1)))))] (u : Units.{x} R (Ring.toMonoid.{x} R _inst_1)), Iff (Eq.{succ x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) (Inv.inv.{x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) (Units.hasInv.{x} R (Ring.toMonoid.{x} R _inst_1)) u) u) (Or (Eq.{succ x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) u (OfNat.ofNat.{x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) 1 (OfNat.mk.{x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) 1 (One.one.{x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) (MulOneClass.toHasOne.{x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) (Units.mulOneClass.{x} R (Ring.toMonoid.{x} R _inst_1))))))) (Eq.{succ x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) u (Neg.neg.{x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) (Units.hasNeg.{x} R (Ring.toMonoid.{x} R _inst_1) (NonUnitalNonAssocRing.toHasDistribNeg.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R _inst_1)))) (OfNat.ofNat.{x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) 1 (OfNat.mk.{x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) 1 (One.one.{x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) (MulOneClass.toHasOne.{x} (Units.{x} R (Ring.toMonoid.{x} R _inst_1)) (Units.mulOneClass.{x} R (Ring.toMonoid.{x} R _inst_1)))))))))
but is expected to have type
  forall {R : Type.{x}} [inst._@.Mathlib.Algebra.Ring.Commute._hyg.865 : Ring.{x} R] [inst._@.Mathlib.Algebra.Ring.Commute._hyg.868 : NoZeroDivisors.{x} R (NonUnitalNonAssocRing.toMul.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865))) (MonoidWithZero.toZero.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))] (u : Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))), Iff (Eq.{succ x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (Inv.inv.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (Units.instInvUnits.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) u) u) (Or (Eq.{succ x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) u (OfNat.ofNat.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) 1 (One.toOfNat1.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (InvOneClass.toOne.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (DivInvOneMonoid.toInvOneClass.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (DivisionMonoid.toDivInvOneMonoid.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (Group.toDivisionMonoid.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (Units.instGroupUnits.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865))))))))))) (Eq.{succ x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) u (Neg.neg.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (Units.instNegUnits.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865))) (NonUnitalNonAssocRing.toHasDistribNeg.{x} R (NonAssocRing.toNonUnitalNonAssocRing.{x} R (Ring.toNonAssocRing.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (OfNat.ofNat.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) 1 (One.toOfNat1.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (InvOneClass.toOne.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (DivInvOneMonoid.toInvOneClass.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (DivisionMonoid.toDivInvOneMonoid.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (Group.toDivisionMonoid.{x} (Units.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))) (Units.instGroupUnits.{x} R (MonoidWithZero.toMonoid.{x} R (Semiring.toMonoidWithZero.{x} R (Ring.toSemiring.{x} R inst._@.Mathlib.Algebra.Ring.Commute._hyg.865)))))))))))))
Case conversion may be inaccurate. Consider using '#align units.inv_eq_self_iff Units.inv_eq_self_iffₓ'. -/
/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
theorem inv_eq_self_iff [Ring R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 := by
  rw [inv_eq_iff_mul_eq_one]
  simp only [ext_iff]
  push_cast
  exact mul_self_eq_one_iff
#align units.inv_eq_self_iff Units.inv_eq_self_iff

end Units

