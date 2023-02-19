/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro

! This file was ported from Lean 3 source module algebra.group.basic
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs

/-!
# Basic lemmas about semigroups, monoids, and groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`algebra/group/defs.lean`.
-/


open Function

universe u

variable {α β G : Type _}

section Associative

variable (f : α → α → α) [IsAssociative α f] (x y : α)

/-- Composing two associative operations of `f : α → α → α` on the left
is equal to an associative operation on the left.
-/
theorem comp_assoc_left : f x ∘ f y = f (f x y) :=
  by
  ext z
  rw [Function.comp_apply, @IsAssociative.assoc _ f]
#align comp_assoc_left comp_assoc_left

/-- Composing two associative operations of `f : α → α → α` on the right
is equal to an associative operation on the right.
-/
theorem comp_assoc_right : ((fun z => f z x) ∘ fun z => f z y) = fun z => f z (f y x) :=
  by
  ext z
  rw [Function.comp_apply, @IsAssociative.assoc _ f]
#align comp_assoc_right comp_assoc_right

end Associative

section Semigroup

/- warning: comp_mul_left -> comp_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] (x : α) (y : α), Eq.{succ u1} (α -> α) (Function.comp.{succ u1, succ u1, succ u1} α α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] (x : α) (y : α), Eq.{succ u1} (α -> α) (Function.comp.{succ u1, succ u1, succ u1} α α α (fun (x._@.Mathlib.Algebra.Group.Basic._hyg.30 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x x._@.Mathlib.Algebra.Group.Basic._hyg.30) (fun (x._@.Mathlib.Algebra.Group.Basic._hyg.42 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) y x._@.Mathlib.Algebra.Group.Basic._hyg.42)) (fun (x._@.Mathlib.Algebra.Group.Basic._hyg.54 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x y) x._@.Mathlib.Algebra.Group.Basic._hyg.54)
Case conversion may be inaccurate. Consider using '#align comp_mul_left comp_mul_leftₓ'. -/
/-- Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[simp,
  to_additive
      "Composing two additions on the left by `y` then `x`\nis equal to a addition on the left by `x + y`."]
theorem comp_mul_left [Semigroup α] (x y : α) : (· * ·) x ∘ (· * ·) y = (· * ·) (x * y) :=
  comp_assoc_left _ _ _
#align comp_mul_left comp_mul_left
#align comp_add_left comp_add_left

/- warning: comp_mul_right -> comp_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] (x : α) (y : α), Eq.{succ u1} (α -> α) (Function.comp.{succ u1, succ u1, succ u1} α α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) _x x) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) _x y)) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) _x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) y x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] (x : α) (y : α), Eq.{succ u1} (α -> α) (Function.comp.{succ u1, succ u1, succ u1} α α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) _x x) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) _x y)) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) _x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) y x))
Case conversion may be inaccurate. Consider using '#align comp_mul_right comp_mul_rightₓ'. -/
/-- Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[simp,
  to_additive
      "Composing two additions on the right by `y` and `x`\nis equal to a addition on the right by `y + x`."]
theorem comp_mul_right [Semigroup α] (x y : α) : (· * x) ∘ (· * y) = (· * (y * x)) :=
  comp_assoc_right _ _ _
#align comp_mul_right comp_mul_right
#align comp_add_right comp_add_right

end Semigroup

section MulOneClass

variable {M : Type u} [MulOneClass M]

/- warning: ite_mul_one -> ite_mul_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {P : Prop} [_inst_2 : Decidable P] {a : M} {b : M}, Eq.{succ u1} M (ite.{succ u1} M P _inst_2 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) a b) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (ite.{succ u1} M P _inst_2 a (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) (ite.{succ u1} M P _inst_2 b (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {P : Prop} [_inst_2 : Decidable P] {a : M} {b : M}, Eq.{succ u1} M (ite.{succ u1} M P _inst_2 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) a b) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (ite.{succ u1} M P _inst_2 a (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) (ite.{succ u1} M P _inst_2 b (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ite_mul_one ite_mul_oneₓ'. -/
@[to_additive]
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} : ite P (a * b) 1 = ite P a 1 * ite P b 1 :=
  by by_cases h : P <;> simp [h]
#align ite_mul_one ite_mul_one
#align ite_add_zero ite_add_zero

/- warning: ite_one_mul -> ite_one_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {P : Prop} [_inst_2 : Decidable P] {a : M} {b : M}, Eq.{succ u1} M (ite.{succ u1} M P _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) a b)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (ite.{succ u1} M P _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) a) (ite.{succ u1} M P _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) b))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {P : Prop} [_inst_2 : Decidable P] {a : M} {b : M}, Eq.{succ u1} M (ite.{succ u1} M P _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) a b)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) (ite.{succ u1} M P _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) a) (ite.{succ u1} M P _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) b))
Case conversion may be inaccurate. Consider using '#align ite_one_mul ite_one_mulₓ'. -/
@[to_additive]
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} : ite P 1 (a * b) = ite P 1 a * ite P 1 b :=
  by by_cases h : P <;> simp [h]
#align ite_one_mul ite_one_mul
#align ite_zero_add ite_zero_add

/- warning: eq_one_iff_eq_one_of_mul_eq_one -> eq_one_iff_eq_one_of_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {a : M} {b : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) a b) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) -> (Iff (Eq.{succ u1} M a (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) (Eq.{succ u1} M b (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {a : M} {b : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) a b) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) -> (Iff (Eq.{succ u1} M a (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) (Eq.{succ u1} M b (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align eq_one_iff_eq_one_of_mul_eq_one eq_one_iff_eq_one_of_mul_eq_oneₓ'. -/
@[to_additive]
theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  constructor <;>
    · rintro rfl
      simpa using h
#align eq_one_iff_eq_one_of_mul_eq_one eq_one_iff_eq_one_of_mul_eq_one
#align eq_zero_iff_eq_zero_of_add_eq_zero eq_zero_iff_eq_zero_of_add_eq_zero

/- warning: one_mul_eq_id -> one_mul_eq_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (M -> M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) (id.{succ u1} M)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (M -> M) ((fun (x._@.Mathlib.Algebra.Group.Basic._hyg.379 : M) (x._@.Mathlib.Algebra.Group.Basic._hyg.381 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x._@.Mathlib.Algebra.Group.Basic._hyg.379 x._@.Mathlib.Algebra.Group.Basic._hyg.381) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) (id.{succ u1} M)
Case conversion may be inaccurate. Consider using '#align one_mul_eq_id one_mul_eq_idₓ'. -/
@[to_additive]
theorem one_mul_eq_id : (· * ·) (1 : M) = id :=
  funext one_mul
#align one_mul_eq_id one_mul_eq_id
#align zero_add_eq_id zero_add_eq_id

/- warning: mul_one_eq_id -> mul_one_eq_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (M -> M) (fun (_x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) _x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) (id.{succ u1} M)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (M -> M) (fun (_x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) _x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) (id.{succ u1} M)
Case conversion may be inaccurate. Consider using '#align mul_one_eq_id mul_one_eq_idₓ'. -/
@[to_additive]
theorem mul_one_eq_id : (· * (1 : M)) = id :=
  funext mul_one
#align mul_one_eq_id mul_one_eq_id
#align add_zero_eq_id add_zero_eq_id

end MulOneClass

section CommSemigroup

variable [CommSemigroup G]

/- warning: mul_left_comm -> mul_left_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b c)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b c)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a c))
Case conversion may be inaccurate. Consider using '#align mul_left_comm mul_left_commₓ'. -/
@[no_rsimp, to_additive]
theorem mul_left_comm : ∀ a b c : G, a * (b * c) = b * (a * c) :=
  left_comm Mul.mul mul_comm mul_assoc
#align mul_left_comm mul_left_comm
#align add_left_comm add_left_comm

/- warning: mul_right_comm -> mul_right_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a b) c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a c) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a b) c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a c) b)
Case conversion may be inaccurate. Consider using '#align mul_right_comm mul_right_commₓ'. -/
@[to_additive]
theorem mul_right_comm : ∀ a b c : G, a * b * c = a * c * b :=
  right_comm Mul.mul mul_comm mul_assoc
#align mul_right_comm mul_right_comm
#align add_right_comm add_right_comm

/- warning: mul_mul_mul_comm -> mul_mul_mul_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G) (c : G) (d : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) c d)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b d))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G) (c : G) (d : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) c d)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b d))
Case conversion may be inaccurate. Consider using '#align mul_mul_mul_comm mul_mul_mul_commₓ'. -/
@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  simp only [mul_left_comm, mul_assoc]
#align mul_mul_mul_comm mul_mul_mul_comm
#align add_add_add_comm add_add_add_comm

/- warning: mul_rotate -> mul_rotate is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a b) c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b c) a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a b) c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b c) a)
Case conversion may be inaccurate. Consider using '#align mul_rotate mul_rotateₓ'. -/
@[to_additive]
theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by simp only [mul_left_comm, mul_comm]
#align mul_rotate mul_rotate
#align add_rotate add_rotate

/- warning: mul_rotate' -> mul_rotate' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b c)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toHasMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) c a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommSemigroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b c)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) b (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (Semigroup.toMul.{u1} G (CommSemigroup.toSemigroup.{u1} G _inst_1))) c a))
Case conversion may be inaccurate. Consider using '#align mul_rotate' mul_rotate'ₓ'. -/
@[to_additive]
theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by
  simp only [mul_left_comm, mul_comm]
#align mul_rotate' mul_rotate'
#align add_rotate' add_rotate'

end CommSemigroup

section AddCommSemigroup

variable {M : Type u} [AddCommSemigroup M]

/- warning: bit0_add -> bit0_add is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : AddCommSemigroup.{u1} M] (a : M) (b : M), Eq.{succ u1} M (bit0.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) a b)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) (bit0.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) a) (bit0.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) b))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : AddCommSemigroup.{u1} M] (a : M) (b : M), Eq.{succ u1} M (bit0.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) a b)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) (bit0.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) a) (bit0.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) b))
Case conversion may be inaccurate. Consider using '#align bit0_add bit0_addₓ'. -/
theorem bit0_add (a b : M) : bit0 (a + b) = bit0 a + bit0 b :=
  add_add_add_comm _ _ _ _
#align bit0_add bit0_add

/- warning: bit1_add -> bit1_add is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : AddCommSemigroup.{u1} M] [_inst_2 : One.{u1} M] (a : M) (b : M), Eq.{succ u1} M (bit1.{u1} M _inst_2 (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) a b)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) (bit0.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) a) (bit1.{u1} M _inst_2 (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) b))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : AddCommSemigroup.{u1} M] [_inst_2 : One.{u1} M] (a : M) (b : M), Eq.{succ u1} M (bit1.{u1} M _inst_2 (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) a b)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) (bit0.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) a) (bit1.{u1} M _inst_2 (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) b))
Case conversion may be inaccurate. Consider using '#align bit1_add bit1_addₓ'. -/
theorem bit1_add [One M] (a b : M) : bit1 (a + b) = bit0 a + bit1 b :=
  (congr_arg (· + (1 : M)) <| bit0_add a b : _).trans (add_assoc _ _ _)
#align bit1_add bit1_add

/- warning: bit1_add' -> bit1_add' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : AddCommSemigroup.{u1} M] [_inst_2 : One.{u1} M] (a : M) (b : M), Eq.{succ u1} M (bit1.{u1} M _inst_2 (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) a b)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) (bit1.{u1} M _inst_2 (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) a) (bit0.{u1} M (AddSemigroup.toHasAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) b))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : AddCommSemigroup.{u1} M] [_inst_2 : One.{u1} M] (a : M) (b : M), Eq.{succ u1} M (bit1.{u1} M _inst_2 (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) a b)) (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1))) (bit1.{u1} M _inst_2 (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) a) (bit0.{u1} M (AddSemigroup.toAdd.{u1} M (AddCommSemigroup.toAddSemigroup.{u1} M _inst_1)) b))
Case conversion may be inaccurate. Consider using '#align bit1_add' bit1_add'ₓ'. -/
theorem bit1_add' [One M] (a b : M) : bit1 (a + b) = bit1 a + bit0 b := by
  rw [add_comm, bit1_add, add_comm]
#align bit1_add' bit1_add'

end AddCommSemigroup

attribute [local simp] mul_assoc sub_eq_add_neg

section AddMonoid

variable {M : Type u} [AddMonoid M] {a b c : M}

/- warning: bit0_zero -> bit0_zero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : AddMonoid.{u1} M], Eq.{succ u1} M (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (bit0.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)) (Zero.zero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : AddMonoid.{u1} M], Eq.{succ u1} M (bit0.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddMonoid.toZero.{u1} M _inst_1)))) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddMonoid.toZero.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align bit0_zero bit0_zeroₓ'. -/
@[simp]
theorem bit0_zero : bit0 (0 : M) = 0 :=
  add_zero _
#align bit0_zero bit0_zero

/- warning: bit1_zero -> bit1_zero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : AddMonoid.{u1} M] [_inst_2 : One.{u1} M], Eq.{succ u1} M (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (bit1.{u1} M _inst_2 (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)) (Zero.zero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M _inst_2)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : AddMonoid.{u1} M] [_inst_2 : One.{u1} M], Eq.{succ u1} M (bit1.{u1} M _inst_2 (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddMonoid.toZero.{u1} M _inst_1)))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_2))
Case conversion may be inaccurate. Consider using '#align bit1_zero bit1_zeroₓ'. -/
@[simp]
theorem bit1_zero [One M] : bit1 (0 : M) = 1 := by rw [bit1, bit0_zero, zero_add]
#align bit1_zero bit1_zero

end AddMonoid

section CommMonoid

variable {M : Type u} [CommMonoid M] {x y z : M}

/- warning: inv_unique -> inv_unique is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {x : M} {y : M} {z : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) x y) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))))) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) x z) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))))) -> (Eq.{succ u1} M y z)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {x : M} {y : M} {z : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) x y) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) x z) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))))) -> (Eq.{succ u1} M y z)
Case conversion may be inaccurate. Consider using '#align inv_unique inv_uniqueₓ'. -/
@[to_additive]
theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
  left_inv_eq_right_inv (trans (mul_comm _ _) hy) hz
#align inv_unique inv_unique
#align neg_unique neg_unique

end CommMonoid

section LeftCancelMonoid

variable {M : Type u} [LeftCancelMonoid M] {a b : M}

/- warning: mul_right_eq_self -> mul_right_eq_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : LeftCancelMonoid.{u1} M] {a : M} {b : M}, Iff (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1)))) a b) a) (Eq.{succ u1} M b (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1)))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : LeftCancelMonoid.{u1} M] {a : M} {b : M}, Iff (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1)))) a b) a) (Eq.{succ u1} M b (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (LeftCancelMonoid.toOne.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_right_eq_self mul_right_eq_selfₓ'. -/
@[simp, to_additive]
theorem mul_right_eq_self : a * b = a ↔ b = 1 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 := mul_left_cancel_iff
    
#align mul_right_eq_self mul_right_eq_self
#align add_right_eq_self add_right_eq_self

/- warning: self_eq_mul_right -> self_eq_mul_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : LeftCancelMonoid.{u1} M] {a : M} {b : M}, Iff (Eq.{succ u1} M a (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1)))) a b)) (Eq.{succ u1} M b (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1)))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : LeftCancelMonoid.{u1} M] {a : M} {b : M}, Iff (Eq.{succ u1} M a (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (LeftCancelMonoid.toMonoid.{u1} M _inst_1)))) a b)) (Eq.{succ u1} M b (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (LeftCancelMonoid.toOne.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align self_eq_mul_right self_eq_mul_rightₓ'. -/
@[simp, to_additive]
theorem self_eq_mul_right : a = a * b ↔ b = 1 :=
  eq_comm.trans mul_right_eq_self
#align self_eq_mul_right self_eq_mul_right
#align self_eq_add_right self_eq_add_right

end LeftCancelMonoid

section RightCancelMonoid

variable {M : Type u} [RightCancelMonoid M] {a b : M}

/- warning: mul_left_eq_self -> mul_left_eq_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : RightCancelMonoid.{u1} M] {a : M} {b : M}, Iff (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M _inst_1)))) a b) b) (Eq.{succ u1} M a (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M _inst_1)))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : RightCancelMonoid.{u1} M] {a : M} {b : M}, Iff (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M _inst_1)))) a b) b) (Eq.{succ u1} M a (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_left_eq_self mul_left_eq_selfₓ'. -/
@[simp, to_additive]
theorem mul_left_eq_self : a * b = b ↔ a = 1 :=
  calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 := mul_right_cancel_iff
    
#align mul_left_eq_self mul_left_eq_self
#align add_left_eq_self add_left_eq_self

/- warning: self_eq_mul_left -> self_eq_mul_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : RightCancelMonoid.{u1} M] {a : M} {b : M}, Iff (Eq.{succ u1} M b (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M _inst_1)))) a b)) (Eq.{succ u1} M a (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M _inst_1)))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : RightCancelMonoid.{u1} M] {a : M} {b : M}, Iff (Eq.{succ u1} M b (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (RightCancelMonoid.toMonoid.{u1} M _inst_1)))) a b)) (Eq.{succ u1} M a (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align self_eq_mul_left self_eq_mul_leftₓ'. -/
@[simp, to_additive]
theorem self_eq_mul_left : b = a * b ↔ a = 1 :=
  eq_comm.trans mul_left_eq_self
#align self_eq_mul_left self_eq_mul_left
#align self_eq_add_left self_eq_add_left

end RightCancelMonoid

section InvolutiveInv

variable [InvolutiveInv G] {a b : G}

/- warning: inv_involutive -> inv_involutive is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G], Function.Involutive.{succ u1} G (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G], Function.Involutive.{succ u1} G (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align inv_involutive inv_involutiveₓ'. -/
@[simp, to_additive]
theorem inv_involutive : Function.Involutive (Inv.inv : G → G) :=
  inv_inv
#align inv_involutive inv_involutive
#align neg_involutive neg_involutive

/- warning: inv_surjective -> inv_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G], Function.Surjective.{succ u1, succ u1} G G (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G], Function.Surjective.{succ u1, succ u1} G G (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align inv_surjective inv_surjectiveₓ'. -/
@[simp, to_additive]
theorem inv_surjective : Function.Surjective (Inv.inv : G → G) :=
  inv_involutive.Surjective
#align inv_surjective inv_surjective
#align neg_surjective neg_surjective

/- warning: inv_injective -> inv_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G], Function.Injective.{succ u1, succ u1} G G (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G], Function.Injective.{succ u1, succ u1} G G (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align inv_injective inv_injectiveₓ'. -/
@[to_additive]
theorem inv_injective : Function.Injective (Inv.inv : G → G) :=
  inv_involutive.Injective
#align inv_injective inv_injective
#align neg_injective neg_injective

/- warning: inv_inj -> inv_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) a) (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) b)) (Eq.{succ u1} G a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) a) (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) b)) (Eq.{succ u1} G a b)
Case conversion may be inaccurate. Consider using '#align inv_inj inv_injₓ'. -/
@[simp, to_additive]
theorem inv_inj {a b : G} : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff
#align inv_inj inv_inj
#align neg_inj neg_inj

/- warning: eq_inv_of_eq_inv -> eq_inv_of_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G] {a : G} {b : G}, (Eq.{succ u1} G a (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) b)) -> (Eq.{succ u1} G b (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G] {a : G} {b : G}, (Eq.{succ u1} G a (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) b)) -> (Eq.{succ u1} G b (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) a))
Case conversion may be inaccurate. Consider using '#align eq_inv_of_eq_inv eq_inv_of_eq_invₓ'. -/
@[to_additive]
theorem eq_inv_of_eq_inv (h : a = b⁻¹) : b = a⁻¹ := by simp [h]
#align eq_inv_of_eq_inv eq_inv_of_eq_inv
#align eq_neg_of_eq_neg eq_neg_of_eq_neg

/- warning: eq_inv_iff_eq_inv -> eq_inv_iff_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G a (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) b)) (Eq.{succ u1} G b (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G a (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) b)) (Eq.{succ u1} G b (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) a))
Case conversion may be inaccurate. Consider using '#align eq_inv_iff_eq_inv eq_inv_iff_eq_invₓ'. -/
@[to_additive]
theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
  ⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩
#align eq_inv_iff_eq_inv eq_inv_iff_eq_inv
#align eq_neg_iff_eq_neg eq_neg_iff_eq_neg

/- warning: inv_eq_iff_inv_eq -> inv_eq_iff_inv_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) a) b) (Eq.{succ u1} G (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) b) a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) a) b) (Eq.{succ u1} G (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) b) a)
Case conversion may be inaccurate. Consider using '#align inv_eq_iff_inv_eq inv_eq_iff_inv_eqₓ'. -/
@[to_additive]
theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
  eq_comm.trans <| eq_inv_iff_eq_inv.trans eq_comm
#align inv_eq_iff_inv_eq inv_eq_iff_inv_eq
#align neg_eq_iff_neg_eq neg_eq_iff_neg_eq

variable (G)

/- warning: inv_comp_inv -> inv_comp_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : InvolutiveInv.{u1} G], Eq.{succ u1} (G -> G) (Function.comp.{succ u1, succ u1, succ u1} G G G (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1)) (Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1))) (id.{succ u1} G)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : InvolutiveInv.{u1} G], Eq.{succ u1} (G -> G) (Function.comp.{succ u1, succ u1, succ u1} G G G (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1)) (Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1))) (id.{succ u1} G)
Case conversion may be inaccurate. Consider using '#align inv_comp_inv inv_comp_invₓ'. -/
@[simp, to_additive]
theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  inv_involutive.comp_self
#align inv_comp_inv inv_comp_inv
#align neg_comp_neg neg_comp_neg

/- warning: left_inverse_inv -> leftInverse_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : InvolutiveInv.{u1} G], Function.LeftInverse.{succ u1, succ u1} G G (fun (a : G) => Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) a) (fun (a : G) => Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) a)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : InvolutiveInv.{u1} G], Function.LeftInverse.{succ u1, succ u1} G G (fun (a : G) => Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) a) (fun (a : G) => Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) a)
Case conversion may be inaccurate. Consider using '#align left_inverse_inv leftInverse_invₓ'. -/
@[to_additive]
theorem leftInverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv
#align left_inverse_inv leftInverse_inv
#align left_inverse_neg leftInverse_neg

/- warning: right_inverse_inv -> rightInverse_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : InvolutiveInv.{u1} G], Function.LeftInverse.{succ u1, succ u1} G G (fun (a : G) => Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) a) (fun (a : G) => Inv.inv.{u1} G (InvolutiveInv.toHasInv.{u1} G _inst_1) a)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : InvolutiveInv.{u1} G], Function.LeftInverse.{succ u1, succ u1} G G (fun (a : G) => Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) a) (fun (a : G) => Inv.inv.{u1} G (InvolutiveInv.toInv.{u1} G _inst_1) a)
Case conversion may be inaccurate. Consider using '#align right_inverse_inv rightInverse_invₓ'. -/
@[to_additive]
theorem rightInverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv
#align right_inverse_inv rightInverse_inv
#align right_inverse_neg rightInverse_neg

end InvolutiveInv

section DivInvMonoid

variable [DivInvMonoid G] {a b c : G}

/- warning: inv_eq_one_div -> inv_eq_one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (x : G), Eq.{succ u1} G (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G _inst_1) x) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))))) x)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (x : G), Eq.{succ u1} G (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G _inst_1) x) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) x)
Case conversion may be inaccurate. Consider using '#align inv_eq_one_div inv_eq_one_divₓ'. -/
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]
#align inv_eq_one_div inv_eq_one_div
#align neg_eq_zero_sub neg_eq_zero_sub

/- warning: mul_one_div -> mul_one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (x : G) (y : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) x (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))))) y)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) x y)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (x : G) (y : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) x (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) y)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) x y)
Case conversion may be inaccurate. Consider using '#align mul_one_div mul_one_divₓ'. -/
@[to_additive]
theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by
  rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]
#align mul_one_div mul_one_div
#align add_zero_sub add_zero_sub

/- warning: mul_div_assoc -> mul_div_assoc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a b) c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) b c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a b) c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) b c))
Case conversion may be inaccurate. Consider using '#align mul_div_assoc mul_div_assocₓ'. -/
@[to_additive]
theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]
#align mul_div_assoc mul_div_assoc
#align add_sub_assoc add_sub_assoc

/- warning: mul_div_assoc' -> mul_div_assoc' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) b c)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a b) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) b c)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_div_assoc' mul_div_assoc'ₓ'. -/
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c :=
  (mul_div_assoc _ _ _).symm
#align mul_div_assoc' mul_div_assoc'
#align add_sub_assoc' add_sub_assoc'

/- warning: one_div -> one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))))) a) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G _inst_1) a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a) (Inv.inv.{u1} G (DivInvMonoid.toInv.{u1} G _inst_1) a)
Case conversion may be inaccurate. Consider using '#align one_div one_divₓ'. -/
@[simp, to_additive]
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm
#align one_div one_div
#align zero_sub zero_sub

/- warning: mul_div -> mul_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) b c)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a b) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) b c)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_div mul_divₓ'. -/
@[to_additive]
theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]
#align mul_div mul_div
#align add_sub add_sub

/- warning: div_eq_mul_one_div -> div_eq_mul_one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))))) b))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))) b))
Case conversion may be inaccurate. Consider using '#align div_eq_mul_one_div div_eq_mul_one_divₓ'. -/
@[to_additive]
theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by rw [div_eq_mul_inv, one_div]
#align div_eq_mul_one_div div_eq_mul_one_div
#align sub_eq_add_zero_sub sub_eq_add_zero_sub

end DivInvMonoid

section DivInvOneMonoid

variable [DivInvOneMonoid G]

/- warning: div_one -> div_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvOneMonoid.{u1} G] (a : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (DivInvOneMonoid.toDivInvMonoid.{u1} G _inst_1))) a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivInvOneMonoid.toDivInvMonoid.{u1} G _inst_1)))))))) a
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvOneMonoid.{u1} G] (a : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (DivInvOneMonoid.toDivInvMonoid.{u1} G _inst_1))) a (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G _inst_1))))) a
Case conversion may be inaccurate. Consider using '#align div_one div_oneₓ'. -/
@[simp, to_additive]
theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]
#align div_one div_one
#align sub_zero sub_zero

/- warning: one_div_one -> one_div_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvOneMonoid.{u1} G], Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (DivInvOneMonoid.toDivInvMonoid.{u1} G _inst_1))) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivInvOneMonoid.toDivInvMonoid.{u1} G _inst_1))))))) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivInvOneMonoid.toDivInvMonoid.{u1} G _inst_1)))))))) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivInvOneMonoid.toDivInvMonoid.{u1} G _inst_1)))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvOneMonoid.{u1} G], Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (DivInvOneMonoid.toDivInvMonoid.{u1} G _inst_1))) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G _inst_1)))) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G _inst_1))))) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G _inst_1))))
Case conversion may be inaccurate. Consider using '#align one_div_one one_div_oneₓ'. -/
@[to_additive]
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _
#align one_div_one one_div_one
#align zero_sub_zero zero_sub_zero

end DivInvOneMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv

/- warning: inv_eq_of_mul_eq_one_left -> inv_eq_of_mul_eq_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) b) a)
Case conversion may be inaccurate. Consider using '#align inv_eq_of_mul_eq_one_left inv_eq_of_mul_eq_one_leftₓ'. -/
@[to_additive]
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by
  rw [← inv_eq_of_mul_eq_one_right h, inv_inv]
#align inv_eq_of_mul_eq_one_left inv_eq_of_mul_eq_one_left
#align neg_eq_of_add_eq_zero_left neg_eq_of_add_eq_zero_left

/- warning: eq_inv_of_mul_eq_one_left -> eq_inv_of_mul_eq_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α a (Inv.inv.{u1} α (DivInvMonoid.toInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) b))
Case conversion may be inaccurate. Consider using '#align eq_inv_of_mul_eq_one_left eq_inv_of_mul_eq_one_leftₓ'. -/
@[to_additive]
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm
#align eq_inv_of_mul_eq_one_left eq_inv_of_mul_eq_one_left
#align eq_neg_of_add_eq_zero_left eq_neg_of_add_eq_zero_left

/- warning: eq_inv_of_mul_eq_one_right -> eq_inv_of_mul_eq_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α b (Inv.inv.{u1} α (DivInvMonoid.toInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) a))
Case conversion may be inaccurate. Consider using '#align eq_inv_of_mul_eq_one_right eq_inv_of_mul_eq_one_rightₓ'. -/
@[to_additive]
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm
#align eq_inv_of_mul_eq_one_right eq_inv_of_mul_eq_one_right
#align eq_neg_of_add_eq_zero_right eq_neg_of_add_eq_zero_right

/- warning: eq_one_div_of_mul_eq_one_left -> eq_one_div_of_mul_eq_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) b a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) b a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a))
Case conversion may be inaccurate. Consider using '#align eq_one_div_of_mul_eq_one_left eq_one_div_of_mul_eq_one_leftₓ'. -/
@[to_additive]
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_left h, one_div]
#align eq_one_div_of_mul_eq_one_left eq_one_div_of_mul_eq_one_left
#align eq_zero_sub_of_add_eq_zero_left eq_zero_sub_of_add_eq_zero_left

/- warning: eq_one_div_of_mul_eq_one_right -> eq_one_div_of_mul_eq_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a))
Case conversion may be inaccurate. Consider using '#align eq_one_div_of_mul_eq_one_right eq_one_div_of_mul_eq_one_rightₓ'. -/
@[to_additive]
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_right h, one_div]
#align eq_one_div_of_mul_eq_one_right eq_one_div_of_mul_eq_one_right
#align eq_zero_sub_of_add_eq_zero_right eq_zero_sub_of_add_eq_zero_right

/- warning: eq_of_div_eq_one -> eq_of_div_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align eq_of_div_eq_one eq_of_div_eq_oneₓ'. -/
@[to_additive]
theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
  inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]
#align eq_of_div_eq_one eq_of_div_eq_one
#align eq_of_sub_eq_zero eq_of_sub_eq_zero

/- warning: div_ne_one_of_ne -> div_ne_one_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Ne.{succ u1} α a b) -> (Ne.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Ne.{succ u1} α a b) -> (Ne.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align div_ne_one_of_ne div_ne_one_of_neₓ'. -/
@[to_additive]
theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 :=
  mt eq_of_div_eq_one
#align div_ne_one_of_ne div_ne_one_of_ne
#align sub_ne_zero_of_ne sub_ne_zero_of_ne

variable (a b c)

/- warning: one_div_mul_one_div_rev -> one_div_mul_one_div_rev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) b a))
Case conversion may be inaccurate. Consider using '#align one_div_mul_one_div_rev one_div_mul_one_div_revₓ'. -/
@[to_additive]
theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp
#align one_div_mul_one_div_rev one_div_mul_one_div_rev
#align zero_sub_add_zero_sub_rev zero_sub_add_zero_sub_rev

/- warning: inv_div_left -> inv_div_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) a) b) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (Inv.inv.{u1} α (DivInvMonoid.toInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) a) b) (Inv.inv.{u1} α (DivInvMonoid.toInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) b a))
Case conversion may be inaccurate. Consider using '#align inv_div_left inv_div_leftₓ'. -/
@[to_additive]
theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp
#align inv_div_left inv_div_left
#align neg_sub_left neg_sub_left

/- warning: inv_div -> inv_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align inv_div inv_divₓ'. -/
@[simp, to_additive]
theorem inv_div : (a / b)⁻¹ = b / a := by simp
#align inv_div inv_div
#align neg_sub neg_sub

/- warning: one_div_div -> one_div_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align one_div_div one_div_divₓ'. -/
@[simp, to_additive]
theorem one_div_div : 1 / (a / b) = b / a := by simp
#align one_div_div one_div_div
#align zero_sub_sub zero_sub_sub

/- warning: one_div_one_div -> one_div_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a)) a
Case conversion may be inaccurate. Consider using '#align one_div_one_div one_div_one_divₓ'. -/
@[to_additive]
theorem one_div_one_div : 1 / (1 / a) = a := by simp
#align one_div_one_div one_div_one_div
#align zero_sub_zero_sub zero_sub_zero_sub

#print DivisionMonoid.toDivInvOneMonoid /-
@[to_additive SubtractionMonoid.toSubNegZeroMonoid]
instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
  { DivisionMonoid.toDivInvMonoid α with
    inv_one := by simpa only [one_div, inv_inv] using (inv_div (1 : α) 1).symm }
#align division_monoid.to_div_inv_one_monoid DivisionMonoid.toDivInvOneMonoid
#align subtraction_monoid.to_sub_neg_zero_monoid SubtractionMonoid.toSubNegZeroMonoid
-/

variable {a b c}

/- warning: inv_eq_one -> inv_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α}, Iff (Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α}, Iff (Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1)))))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align inv_eq_one inv_eq_oneₓ'. -/
@[simp, to_additive]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  inv_injective.eq_iff' inv_one
#align inv_eq_one inv_eq_one
#align neg_eq_zero neg_eq_zero

/- warning: one_eq_inv -> one_eq_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α}, Iff (Eq.{succ u1} α (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) a)) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α}, Iff (Eq.{succ u1} α (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))) a)) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align one_eq_inv one_eq_invₓ'. -/
@[simp, to_additive]
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  eq_comm.trans inv_eq_one
#align one_eq_inv one_eq_inv
#align zero_eq_neg zero_eq_neg

/- warning: inv_ne_one -> inv_ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α}, Iff (Ne.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))))) (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α}, Iff (Ne.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1)))))) (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align inv_ne_one inv_ne_oneₓ'. -/
@[to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  inv_eq_one.Not
#align inv_ne_one inv_ne_one
#align neg_ne_zero neg_ne_zero

/- warning: eq_of_one_div_eq_one_div -> eq_of_one_div_eq_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))) b)) -> (Eq.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {a : α} {b : α}, (Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))))) b)) -> (Eq.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align eq_of_one_div_eq_one_div eq_of_one_div_eq_one_divₓ'. -/
@[to_additive]
theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by
  rw [← one_div_one_div a, h, one_div_one_div]
#align eq_of_one_div_eq_one_div eq_of_one_div_eq_one_div
#align eq_of_zero_sub_eq_zero_sub eq_of_zero_sub_eq_zero_sub

variable (a b c)

/- warning: div_div_eq_mul_div -> div_div_eq_mul_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) b c)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) b c)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_div_eq_mul_div div_div_eq_mul_divₓ'. -/
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp
#align div_div_eq_mul_div div_div_eq_mul_div
#align sub_sub_eq_add_sub sub_sub_eq_add_sub

/- warning: div_inv_eq_mul -> div_inv_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))) b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b)
Case conversion may be inaccurate. Consider using '#align div_inv_eq_mul div_inv_eq_mulₓ'. -/
@[simp, to_additive]
theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp
#align div_inv_eq_mul div_inv_eq_mul
#align sub_neg_eq_add sub_neg_eq_add

/- warning: div_mul_eq_div_div_swap -> div_mul_eq_div_div_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) b c)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) b c)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_mul_eq_div_div_swap div_mul_eq_div_div_swapₓ'. -/
@[to_additive]
theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b := by
  simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]
#align div_mul_eq_div_div_swap div_mul_eq_div_div_swap
#align sub_add_eq_sub_sub_swap sub_add_eq_sub_sub_swap

end DivisionMonoid

/- warning: bit0_neg -> bit0_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SubtractionMonoid.{u1} α] (a : α), Eq.{succ u1} α (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)))) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)) a)) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)) (bit0.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SubtractionMonoid.{u1} α] (a : α), Eq.{succ u1} α (bit0.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)))) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α _inst_1))) a)) (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α _inst_1))) (bit0.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (SubtractionMonoid.toSubNegMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align bit0_neg bit0_negₓ'. -/
theorem bit0_neg [SubtractionMonoid α] (a : α) : bit0 (-a) = -bit0 a :=
  (neg_add_rev _ _).symm
#align bit0_neg bit0_neg

section DivisionCommMonoid

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

/- warning: mul_inv -> mul_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b))
Case conversion may be inaccurate. Consider using '#align mul_inv mul_invₓ'. -/
@[to_additive neg_add]
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp
#align mul_inv mul_inv
#align neg_add neg_add

/- warning: inv_div' -> inv_div' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b))
Case conversion may be inaccurate. Consider using '#align inv_div' inv_div'ₓ'. -/
@[to_additive]
theorem inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹ := by simp
#align inv_div' inv_div'
#align neg_sub' neg_sub'

/- warning: div_eq_inv_mul -> div_eq_inv_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b) a)
Case conversion may be inaccurate. Consider using '#align div_eq_inv_mul div_eq_inv_mulₓ'. -/
@[to_additive]
theorem div_eq_inv_mul : a / b = b⁻¹ * a := by simp
#align div_eq_inv_mul div_eq_inv_mul
#align sub_eq_neg_add sub_eq_neg_add

/- warning: inv_mul_eq_div -> inv_mul_eq_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) a) b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a) b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b a)
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_div inv_mul_eq_divₓ'. -/
@[to_additive]
theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp
#align inv_mul_eq_div inv_mul_eq_div
#align neg_add_eq_sub neg_add_eq_sub

/- warning: inv_mul' -> inv_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) a) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a) b)
Case conversion may be inaccurate. Consider using '#align inv_mul' inv_mul'ₓ'. -/
@[to_additive]
theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp
#align inv_mul' inv_mul'
#align neg_add' neg_add'

/- warning: inv_div_inv -> inv_div_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b a)
Case conversion may be inaccurate. Consider using '#align inv_div_inv inv_div_invₓ'. -/
@[simp, to_additive]
theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by simp
#align inv_div_inv inv_div_inv
#align neg_sub_neg neg_sub_neg

/- warning: inv_inv_div_inv -> inv_inv_div_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) b))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b)
Case conversion may be inaccurate. Consider using '#align inv_inv_div_inv inv_inv_div_invₓ'. -/
@[to_additive]
theorem inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b := by simp
#align inv_inv_div_inv inv_inv_div_inv
#align neg_neg_sub_neg neg_neg_sub_neg

/- warning: one_div_mul_one_div -> one_div_mul_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))))) b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align one_div_mul_one_div one_div_mul_one_divₓ'. -/
@[to_additive]
theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by simp
#align one_div_mul_one_div one_div_mul_one_div
#align zero_sub_add_zero_sub zero_sub_add_zero_sub

/- warning: div_right_comm -> div_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_right_comm div_right_commₓ'. -/
@[to_additive]
theorem div_right_comm : a / b / c = a / c / b := by simp
#align div_right_comm div_right_comm
#align sub_right_comm sub_right_comm

/- warning: div_div -> div_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_div div_divₓ'. -/
@[to_additive, field_simps]
theorem div_div : a / b / c = a / (b * c) := by simp
#align div_div div_div
#align sub_sub sub_sub

/- warning: div_mul -> div_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align div_mul div_mulₓ'. -/
@[to_additive]
theorem div_mul : a / b * c = a / (b / c) := by simp
#align div_mul div_mul
#align sub_add sub_add

/- warning: mul_div_left_comm -> mul_div_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a c))
Case conversion may be inaccurate. Consider using '#align mul_div_left_comm mul_div_left_commₓ'. -/
@[to_additive]
theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp
#align mul_div_left_comm mul_div_left_comm
#align add_sub_left_comm add_sub_left_comm

/- warning: mul_div_right_comm -> mul_div_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a b) c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a b) c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a c) b)
Case conversion may be inaccurate. Consider using '#align mul_div_right_comm mul_div_right_commₓ'. -/
@[to_additive]
theorem mul_div_right_comm : a * b / c = a / c * b := by simp
#align mul_div_right_comm mul_div_right_comm
#align add_sub_right_comm add_sub_right_comm

/- warning: div_mul_eq_div_div -> div_mul_eq_div_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b c)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b c)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c)
Case conversion may be inaccurate. Consider using '#align div_mul_eq_div_div div_mul_eq_div_divₓ'. -/
@[to_additive]
theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by simp
#align div_mul_eq_div_div div_mul_eq_div_div
#align sub_add_eq_sub_sub sub_add_eq_sub_sub

/- warning: div_mul_eq_mul_div -> div_mul_eq_mul_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a c) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_mul_eq_mul_div div_mul_eq_mul_divₓ'. -/
@[to_additive, field_simps]
theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp
#align div_mul_eq_mul_div div_mul_eq_mul_div
#align sub_add_eq_add_sub sub_add_eq_add_sub

/- warning: mul_comm_div -> mul_comm_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) c b))
Case conversion may be inaccurate. Consider using '#align mul_comm_div mul_comm_divₓ'. -/
@[to_additive]
theorem mul_comm_div : a / b * c = a * (c / b) := by simp
#align mul_comm_div mul_comm_div
#align add_comm_sub add_comm_sub

/- warning: div_mul_comm -> div_mul_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) c b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) c b) a)
Case conversion may be inaccurate. Consider using '#align div_mul_comm div_mul_commₓ'. -/
@[to_additive]
theorem div_mul_comm : a / b * c = c / b * a := by simp
#align div_mul_comm div_mul_comm
#align sub_add_comm sub_add_comm

/- warning: div_mul_eq_div_mul_one_div -> div_mul_eq_div_mul_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))))) c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) c))
Case conversion may be inaccurate. Consider using '#align div_mul_eq_div_mul_one_div div_mul_eq_div_mul_one_divₓ'. -/
@[to_additive]
theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp
#align div_mul_eq_div_mul_one_div div_mul_eq_div_mul_one_div
#align sub_add_eq_sub_add_zero_sub sub_add_eq_sub_add_zero_sub

/- warning: div_div_div_eq -> div_div_div_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) c d)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) c d)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_div_div_eq div_div_div_eqₓ'. -/
@[to_additive]
theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by simp
#align div_div_div_eq div_div_div_eq
#align sub_sub_sub_eq sub_sub_sub_eq

/- warning: div_div_div_comm -> div_div_div_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) c d)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) c d)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b d))
Case conversion may be inaccurate. Consider using '#align div_div_div_comm div_div_div_commₓ'. -/
@[to_additive]
theorem div_div_div_comm : a / b / (c / d) = a / c / (b / d) := by simp
#align div_div_div_comm div_div_div_comm
#align sub_sub_sub_comm sub_sub_sub_comm

/- warning: div_mul_div_comm -> div_mul_div_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) c d)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) c d)) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) b d))
Case conversion may be inaccurate. Consider using '#align div_mul_div_comm div_mul_div_commₓ'. -/
@[to_additive]
theorem div_mul_div_comm : a / b * (c / d) = a * c / (b * d) := by simp
#align div_mul_div_comm div_mul_div_comm
#align sub_add_sub_comm sub_add_sub_comm

/- warning: mul_div_mul_comm -> mul_div_mul_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) c d)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) c d)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) b d))
Case conversion may be inaccurate. Consider using '#align mul_div_mul_comm mul_div_mul_commₓ'. -/
@[to_additive]
theorem mul_div_mul_comm : a * b / (c * d) = a / c * (b / d) := by simp
#align mul_div_mul_comm mul_div_mul_comm
#align add_sub_add_comm add_sub_add_comm

end DivisionCommMonoid

section Group

variable [Group G] {a b c d : G}

/- warning: div_eq_inv_self -> div_eq_inv_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) (Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b)) (Eq.{succ u1} G a (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align div_eq_inv_self div_eq_inv_selfₓ'. -/
@[simp, to_additive]
theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_left_eq_self]
#align div_eq_inv_self div_eq_inv_self
#align sub_eq_neg_self sub_eq_neg_self

/- warning: mul_left_surjective -> mul_left_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Function.Surjective.{succ u1, succ u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Function.Surjective.{succ u1, succ u1} G G ((fun (x._@.Mathlib.Algebra.Group.Basic._hyg.3540 : G) (x._@.Mathlib.Algebra.Group.Basic._hyg.3542 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Group.Basic._hyg.3540 x._@.Mathlib.Algebra.Group.Basic._hyg.3542) a)
Case conversion may be inaccurate. Consider using '#align mul_left_surjective mul_left_surjectiveₓ'. -/
@[to_additive]
theorem mul_left_surjective (a : G) : Function.Surjective ((· * ·) a) := fun x =>
  ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩
#align mul_left_surjective mul_left_surjective
#align add_left_surjective add_left_surjective

/- warning: mul_right_surjective -> mul_right_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Function.Surjective.{succ u1, succ u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Function.Surjective.{succ u1, succ u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x a)
Case conversion may be inaccurate. Consider using '#align mul_right_surjective mul_right_surjectiveₓ'. -/
@[to_additive]
theorem mul_right_surjective (a : G) : Function.Surjective fun x => x * a := fun x =>
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩
#align mul_right_surjective mul_right_surjective
#align add_right_surjective add_right_surjective

/- warning: eq_mul_inv_of_mul_eq -> eq_mul_inv_of_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c) b) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) c)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c) b) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) c)))
Case conversion may be inaccurate. Consider using '#align eq_mul_inv_of_mul_eq eq_mul_inv_of_mul_eqₓ'. -/
@[to_additive]
theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ := by simp [h.symm]
#align eq_mul_inv_of_mul_eq eq_mul_inv_of_mul_eq
#align eq_add_neg_of_add_eq eq_add_neg_of_add_eq

/- warning: eq_inv_mul_of_mul_eq -> eq_inv_mul_of_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a) c) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b) c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a) c) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b) c))
Case conversion may be inaccurate. Consider using '#align eq_inv_mul_of_mul_eq eq_inv_mul_of_mul_eqₓ'. -/
@[to_additive]
theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c := by simp [h.symm]
#align eq_inv_mul_of_mul_eq eq_inv_mul_of_mul_eq
#align eq_neg_add_of_add_eq eq_neg_add_of_add_eq

/- warning: inv_mul_eq_of_eq_mul -> inv_mul_eq_of_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G b (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c)) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) b) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G b (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c)) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) b) c)
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_of_eq_mul inv_mul_eq_of_eq_mulₓ'. -/
@[to_additive]
theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c := by simp [h]
#align inv_mul_eq_of_eq_mul inv_mul_eq_of_eq_mul
#align neg_add_eq_of_eq_add neg_add_eq_of_eq_add

/- warning: mul_inv_eq_of_eq_mul -> mul_inv_eq_of_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c b)) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c b)) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b)) c)
Case conversion may be inaccurate. Consider using '#align mul_inv_eq_of_eq_mul mul_inv_eq_of_eq_mulₓ'. -/
@[to_additive]
theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c := by simp [h]
#align mul_inv_eq_of_eq_mul mul_inv_eq_of_eq_mul
#align add_neg_eq_of_eq_add add_neg_eq_of_eq_add

/- warning: eq_mul_of_mul_inv_eq -> eq_mul_of_mul_inv_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) c)) b) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) c)) b) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_mul_inv_eq eq_mul_of_mul_inv_eqₓ'. -/
@[to_additive]
theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c := by simp [h.symm]
#align eq_mul_of_mul_inv_eq eq_mul_of_mul_inv_eq
#align eq_add_of_add_neg_eq eq_add_of_add_neg_eq

/- warning: eq_mul_of_inv_mul_eq -> eq_mul_of_inv_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b) a) c) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b) a) c) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_inv_mul_eq eq_mul_of_inv_mul_eqₓ'. -/
@[to_additive]
theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by simp [h.symm, mul_inv_cancel_left]
#align eq_mul_of_inv_mul_eq eq_mul_of_inv_mul_eq
#align eq_add_of_neg_add_eq eq_add_of_neg_add_eq

/- warning: mul_eq_of_eq_inv_mul -> mul_eq_of_eq_inv_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G b (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) c)) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G b (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) c)) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_inv_mul mul_eq_of_eq_inv_mulₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by rw [h, mul_inv_cancel_left]
#align mul_eq_of_eq_inv_mul mul_eq_of_eq_inv_mul
#align add_eq_of_eq_neg_add add_eq_of_eq_neg_add

/- warning: mul_eq_of_eq_mul_inv -> mul_eq_of_eq_mul_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b))) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b))) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_mul_inv mul_eq_of_eq_mul_invₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c := by simp [h]
#align mul_eq_of_eq_mul_inv mul_eq_of_eq_mul_inv
#align add_eq_of_eq_add_neg add_eq_of_eq_add_neg

/- warning: mul_eq_one_iff_eq_inv -> mul_eq_one_iff_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))) (Eq.{succ u1} G a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))) (Eq.{succ u1} G a (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b))
Case conversion may be inaccurate. Consider using '#align mul_eq_one_iff_eq_inv mul_eq_one_iff_eq_invₓ'. -/
@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h => by rw [h, mul_left_inv]⟩
#align mul_eq_one_iff_eq_inv mul_eq_one_iff_eq_inv
#align add_eq_zero_iff_eq_neg add_eq_zero_iff_eq_neg

/- warning: mul_eq_one_iff_inv_eq -> mul_eq_one_iff_inv_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))) (Eq.{succ u1} G (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))) (Eq.{succ u1} G (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) b)
Case conversion may be inaccurate. Consider using '#align mul_eq_one_iff_inv_eq mul_eq_one_iff_inv_eqₓ'. -/
@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by
  rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]
#align mul_eq_one_iff_inv_eq mul_eq_one_iff_inv_eq
#align add_eq_zero_iff_neg_eq add_eq_zero_iff_neg_eq

/- warning: eq_inv_iff_mul_eq_one -> eq_inv_iff_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G a (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b)) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align eq_inv_iff_mul_eq_one eq_inv_iff_mul_eq_oneₓ'. -/
@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm
#align eq_inv_iff_mul_eq_one eq_inv_iff_mul_eq_one
#align eq_neg_iff_add_eq_zero eq_neg_iff_add_eq_zero

/- warning: inv_eq_iff_mul_eq_one -> inv_eq_iff_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) b) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) b) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align inv_eq_iff_mul_eq_one inv_eq_iff_mul_eq_oneₓ'. -/
@[to_additive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm
#align inv_eq_iff_mul_eq_one inv_eq_iff_mul_eq_one
#align neg_eq_iff_add_eq_zero neg_eq_iff_add_eq_zero

/- warning: eq_mul_inv_iff_mul_eq -> eq_mul_inv_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) c))) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) c))) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c) b)
Case conversion may be inaccurate. Consider using '#align eq_mul_inv_iff_mul_eq eq_mul_inv_iff_mul_eqₓ'. -/
@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩
#align eq_mul_inv_iff_mul_eq eq_mul_inv_iff_mul_eq
#align eq_add_neg_iff_add_eq eq_add_neg_iff_add_eq

/- warning: eq_inv_mul_iff_mul_eq -> eq_inv_mul_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b) c)) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b) c)) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a) c)
Case conversion may be inaccurate. Consider using '#align eq_inv_mul_iff_mul_eq eq_inv_mul_iff_mul_eqₓ'. -/
@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩
#align eq_inv_mul_iff_mul_eq eq_inv_mul_iff_mul_eq
#align eq_neg_add_iff_add_eq eq_neg_add_iff_add_eq

/- warning: inv_mul_eq_iff_eq_mul -> inv_mul_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) b) c) (Eq.{succ u1} G b (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) b) c) (Eq.{succ u1} G b (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c))
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_iff_eq_mul inv_mul_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩
#align inv_mul_eq_iff_eq_mul inv_mul_eq_iff_eq_mul
#align neg_add_eq_iff_eq_add neg_add_eq_iff_eq_add

/- warning: mul_inv_eq_iff_eq_mul -> mul_inv_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) c) (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c b))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b)) c) (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_eq_iff_eq_mul mul_inv_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩
#align mul_inv_eq_iff_eq_mul mul_inv_eq_iff_eq_mul
#align add_neg_eq_iff_eq_add add_neg_eq_iff_eq_add

/- warning: mul_inv_eq_one -> mul_inv_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))) (Eq.{succ u1} G a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b)) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))) (Eq.{succ u1} G a b)
Case conversion may be inaccurate. Consider using '#align mul_inv_eq_one mul_inv_eq_oneₓ'. -/
@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]
#align mul_inv_eq_one mul_inv_eq_one
#align add_neg_eq_zero add_neg_eq_zero

/- warning: inv_mul_eq_one -> inv_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) b) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))) (Eq.{succ u1} G a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) b) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))) (Eq.{succ u1} G a b)
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_one inv_mul_eq_oneₓ'. -/
@[to_additive]
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]
#align inv_mul_eq_one inv_mul_eq_one
#align neg_add_eq_zero neg_add_eq_zero

/- warning: div_left_injective -> div_left_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {b : G}, Function.Injective.{succ u1, succ u1} G G (fun (a : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {b : G}, Function.Injective.{succ u1, succ u1} G G (fun (a : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align div_left_injective div_left_injectiveₓ'. -/
@[to_additive]
theorem div_left_injective : Function.Injective fun a => a / b := by
  simpa only [div_eq_mul_inv] using fun a a' h => mul_left_injective b⁻¹ h
#align div_left_injective div_left_injective
#align sub_left_injective sub_left_injective

/- warning: div_right_injective -> div_right_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {b : G}, Function.Injective.{succ u1, succ u1} G G (fun (a : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {b : G}, Function.Injective.{succ u1, succ u1} G G (fun (a : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b a)
Case conversion may be inaccurate. Consider using '#align div_right_injective div_right_injectiveₓ'. -/
@[to_additive]
theorem div_right_injective : Function.Injective fun a => b / a := by
  simpa only [div_eq_mul_inv] using fun a a' h => inv_injective (mul_right_injective b h)
#align div_right_injective div_right_injective
#align sub_right_injective sub_right_injective

/- warning: div_mul_cancel' -> div_mul_cancel' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) b) a
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) b) a
Case conversion may be inaccurate. Consider using '#align div_mul_cancel' div_mul_cancel'ₓ'. -/
@[simp, to_additive sub_add_cancel]
theorem div_mul_cancel' (a b : G) : a / b * b = a := by
  rw [div_eq_mul_inv, inv_mul_cancel_right a b]
#align div_mul_cancel' div_mul_cancel'
#align sub_add_cancel sub_add_cancel

/- warning: div_self' -> div_self' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a a) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a a) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))
Case conversion may be inaccurate. Consider using '#align div_self' div_self'ₓ'. -/
@[simp, to_additive sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_right_inv a]
#align div_self' div_self'
#align sub_self sub_self

/- warning: mul_div_cancel'' -> mul_div_cancel'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) b) a
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) b) a
Case conversion may be inaccurate. Consider using '#align mul_div_cancel'' mul_div_cancel''ₓ'. -/
@[simp, to_additive add_sub_cancel]
theorem mul_div_cancel'' (a b : G) : a * b / b = a := by
  rw [div_eq_mul_inv, mul_inv_cancel_right a b]
#align mul_div_cancel'' mul_div_cancel''
#align add_sub_cancel add_sub_cancel

/- warning: mul_div_mul_right_eq_div -> mul_div_mul_right_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b c)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b c)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align mul_div_mul_right_eq_div mul_div_mul_right_eq_divₓ'. -/
@[simp, to_additive]
theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap] <;> simp only [mul_left_inj, eq_self_iff_true, mul_div_cancel'']
#align mul_div_mul_right_eq_div mul_div_mul_right_eq_div
#align add_sub_add_right_eq_sub add_sub_add_right_eq_sub

/- warning: eq_div_of_mul_eq' -> eq_div_of_mul_eq' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c) b) -> (Eq.{succ u1} G a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c) b) -> (Eq.{succ u1} G a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b c))
Case conversion may be inaccurate. Consider using '#align eq_div_of_mul_eq' eq_div_of_mul_eq'ₓ'. -/
@[to_additive eq_sub_of_add_eq]
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]
#align eq_div_of_mul_eq' eq_div_of_mul_eq'
#align eq_sub_of_add_eq eq_sub_of_add_eq

/- warning: div_eq_of_eq_mul'' -> div_eq_of_eq_mul'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c b)) -> (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c b)) -> (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) c)
Case conversion may be inaccurate. Consider using '#align div_eq_of_eq_mul'' div_eq_of_eq_mul''ₓ'. -/
@[to_additive sub_eq_of_eq_add]
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]
#align div_eq_of_eq_mul'' div_eq_of_eq_mul''
#align sub_eq_of_eq_add sub_eq_of_eq_add

/- warning: eq_mul_of_div_eq -> eq_mul_of_div_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c) b) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c) b) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_div_eq eq_mul_of_div_eqₓ'. -/
@[to_additive]
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]
#align eq_mul_of_div_eq eq_mul_of_div_eq
#align eq_add_of_sub_eq eq_add_of_sub_eq

/- warning: mul_eq_of_eq_div -> mul_eq_of_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) c b)) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) c b)) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_div mul_eq_of_eq_divₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]
#align mul_eq_of_eq_div mul_eq_of_eq_div
#align add_eq_of_eq_sub add_eq_of_eq_sub

/- warning: div_right_inj -> div_right_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c)) (Eq.{succ u1} G b c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c)) (Eq.{succ u1} G b c)
Case conversion may be inaccurate. Consider using '#align div_right_inj div_right_injₓ'. -/
@[simp, to_additive]
theorem div_right_inj : a / b = a / c ↔ b = c :=
  div_right_injective.eq_iff
#align div_right_inj div_right_inj
#align sub_right_inj sub_right_inj

/- warning: div_left_inj -> div_left_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b a) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) c a)) (Eq.{succ u1} G b c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b a) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) c a)) (Eq.{succ u1} G b c)
Case conversion may be inaccurate. Consider using '#align div_left_inj div_left_injₓ'. -/
@[simp, to_additive]
theorem div_left_inj : b / a = c / a ↔ b = c :=
  by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_left_inj _
#align div_left_inj div_left_inj
#align sub_left_inj sub_left_inj

/- warning: div_mul_div_cancel' -> div_mul_div_cancel' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b c)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b c)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c)
Case conversion may be inaccurate. Consider using '#align div_mul_div_cancel' div_mul_div_cancel'ₓ'. -/
@[simp, to_additive sub_add_sub_cancel]
theorem div_mul_div_cancel' (a b c : G) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc, div_mul_cancel']
#align div_mul_div_cancel' div_mul_div_cancel'
#align sub_add_sub_cancel sub_add_sub_cancel

/- warning: div_div_div_cancel_right' -> div_div_div_cancel_right' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b c)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a c) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b c)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align div_div_div_cancel_right' div_div_div_cancel_right'ₓ'. -/
@[simp, to_additive sub_sub_sub_cancel_right]
theorem div_div_div_cancel_right' (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel']
#align div_div_div_cancel_right' div_div_div_cancel_right'
#align sub_sub_sub_cancel_right sub_sub_sub_cancel_right

/- warning: div_eq_one -> div_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))) (Eq.{succ u1} G a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))) (Eq.{succ u1} G a b)
Case conversion may be inaccurate. Consider using '#align div_eq_one div_eq_oneₓ'. -/
@[to_additive]
theorem div_eq_one : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun h => by rw [h, div_self']⟩
#align div_eq_one div_eq_one
#align sub_eq_zero sub_eq_zero

/- warning: div_eq_one_of_eq -> div_eq_one_of_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Eq.{succ u1} G a b) -> (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Eq.{succ u1} G a b) -> (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align div_eq_one_of_eq div_eq_one_of_eqₓ'. -/
alias div_eq_one ↔ _ div_eq_one_of_eq
#align div_eq_one_of_eq div_eq_one_of_eq

/- warning: sub_eq_zero_of_eq -> sub_eq_zero_of_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : AddGroup.{u1} G] {a : G} {b : G}, (Eq.{succ u1} G a b) -> (Eq.{succ u1} G (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))) a b) (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : AddGroup.{u1} G] {a : G} {b : G}, (Eq.{succ u1} G a b) -> (Eq.{succ u1} G (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))) a b) (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align sub_eq_zero_of_eq sub_eq_zero_of_eqₓ'. -/
alias sub_eq_zero ↔ _ sub_eq_zero_of_eq
#align sub_eq_zero_of_eq sub_eq_zero_of_eq

/- warning: div_ne_one -> div_ne_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Ne.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))) (Ne.{succ u1} G a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Ne.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))) (Ne.{succ u1} G a b)
Case conversion may be inaccurate. Consider using '#align div_ne_one div_ne_oneₓ'. -/
@[to_additive]
theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b :=
  not_congr div_eq_one
#align div_ne_one div_ne_one
#align sub_ne_zero sub_ne_zero

/- warning: div_eq_self -> div_eq_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) a) (Eq.{succ u1} G b (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) a) (Eq.{succ u1} G b (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align div_eq_self div_eq_selfₓ'. -/
@[simp, to_additive]
theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_right_eq_self, inv_eq_one]
#align div_eq_self div_eq_self
#align sub_eq_self sub_eq_self

/- warning: eq_div_iff_mul_eq' -> eq_div_iff_mul_eq' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b c)) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) b c)) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a c) b)
Case conversion may be inaccurate. Consider using '#align eq_div_iff_mul_eq' eq_div_iff_mul_eq'ₓ'. -/
@[to_additive eq_sub_iff_add_eq]
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]
#align eq_div_iff_mul_eq' eq_div_iff_mul_eq'
#align eq_sub_iff_add_eq eq_sub_iff_add_eq

/- warning: div_eq_iff_eq_mul -> div_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) c) (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c b))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) c) (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c b))
Case conversion may be inaccurate. Consider using '#align div_eq_iff_eq_mul div_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]
#align div_eq_iff_eq_mul div_eq_iff_eq_mul
#align sub_eq_iff_eq_add sub_eq_iff_eq_add

/- warning: eq_iff_eq_of_div_eq_div -> eq_iff_eq_of_div_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G} {d : G}, (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) c d)) -> (Iff (Eq.{succ u1} G a b) (Eq.{succ u1} G c d))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G} {c : G} {d : G}, (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) c d)) -> (Iff (Eq.{succ u1} G a b) (Eq.{succ u1} G c d))
Case conversion may be inaccurate. Consider using '#align eq_iff_eq_of_div_eq_div eq_iff_eq_of_div_eq_divₓ'. -/
@[to_additive]
theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d := by
  rw [← div_eq_one, H, div_eq_one]
#align eq_iff_eq_of_div_eq_div eq_iff_eq_of_div_eq_div
#align eq_iff_eq_of_sub_eq_sub eq_iff_eq_of_sub_eq_sub

/- warning: left_inverse_div_mul_left -> leftInverse_div_mul_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (c : G), Function.LeftInverse.{succ u1, succ u1} G G (fun (x : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x c) (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (c : G), Function.LeftInverse.{succ u1, succ u1} G G (fun (x : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x c) (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x c)
Case conversion may be inaccurate. Consider using '#align left_inverse_div_mul_left leftInverse_div_mul_leftₓ'. -/
@[to_additive]
theorem leftInverse_div_mul_left (c : G) : Function.LeftInverse (fun x => x / c) fun x => x * c :=
  fun x => mul_div_cancel'' x c
#align left_inverse_div_mul_left leftInverse_div_mul_left
#align left_inverse_sub_add_left leftInverse_sub_add_left

/- warning: left_inverse_mul_left_div -> leftInverse_mul_left_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (c : G), Function.LeftInverse.{succ u1, succ u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x c) (fun (x : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (c : G), Function.LeftInverse.{succ u1, succ u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x c) (fun (x : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x c)
Case conversion may be inaccurate. Consider using '#align left_inverse_mul_left_div leftInverse_mul_left_divₓ'. -/
@[to_additive]
theorem leftInverse_mul_left_div (c : G) : Function.LeftInverse (fun x => x * c) fun x => x / c :=
  fun x => div_mul_cancel' x c
#align left_inverse_mul_left_div leftInverse_mul_left_div
#align left_inverse_add_left_sub leftInverse_add_left_sub

/- warning: left_inverse_mul_right_inv_mul -> leftInverse_mul_right_inv_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (c : G), Function.LeftInverse.{succ u1, succ u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c x) (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) c) x)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (c : G), Function.LeftInverse.{succ u1, succ u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c x) (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) c) x)
Case conversion may be inaccurate. Consider using '#align left_inverse_mul_right_inv_mul leftInverse_mul_right_inv_mulₓ'. -/
@[to_additive]
theorem leftInverse_mul_right_inv_mul (c : G) :
    Function.LeftInverse (fun x => c * x) fun x => c⁻¹ * x := fun x => mul_inv_cancel_left c x
#align left_inverse_mul_right_inv_mul leftInverse_mul_right_inv_mul
#align left_inverse_add_right_neg_add leftInverse_add_right_neg_add

/- warning: left_inverse_inv_mul_mul_right -> leftInverse_inv_mul_mul_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (c : G), Function.LeftInverse.{succ u1, succ u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) c) x) (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c x)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (c : G), Function.LeftInverse.{succ u1, succ u1} G G (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) c) x) (fun (x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) c x)
Case conversion may be inaccurate. Consider using '#align left_inverse_inv_mul_mul_right leftInverse_inv_mul_mul_rightₓ'. -/
@[to_additive]
theorem leftInverse_inv_mul_mul_right (c : G) :
    Function.LeftInverse (fun x => c⁻¹ * x) fun x => c * x := fun x => inv_mul_cancel_left c x
#align left_inverse_inv_mul_mul_right leftInverse_inv_mul_mul_right
#align left_inverse_neg_add_add_right leftInverse_neg_add_add_right

/- warning: exists_npow_eq_one_of_zpow_eq_one -> exists_npow_eq_one_of_zpow_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {n : Int}, (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (forall {x : G}, (Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x n) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))) -> (Exists.{1} Nat (fun (n : Nat) => And (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) (Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) x n) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {n : Int}, (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (forall {x : G}, (Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) x n) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))) -> (Exists.{1} Nat (fun (n : Nat) => And (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Nat G (instHPow.{u1, 0} G Nat (Monoid.Pow.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) x n) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))))))
Case conversion may be inaccurate. Consider using '#align exists_npow_eq_one_of_zpow_eq_one exists_npow_eq_one_of_zpow_eq_oneₓ'. -/
@[to_additive]
theorem exists_npow_eq_one_of_zpow_eq_one {n : ℤ} (hn : n ≠ 0) {x : G} (h : x ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  cases' n with n n
  · rw [zpow_ofNat] at h
    refine' ⟨n, Nat.pos_of_ne_zero fun n0 => hn _, h⟩
    rw [n0]
    rfl
  · rw [zpow_negSucc, inv_eq_one] at h
    refine' ⟨n + 1, n.succ_pos, h⟩
#align exists_npow_eq_one_of_zpow_eq_one exists_npow_eq_one_of_zpow_eq_one
#align exists_nsmul_eq_zero_of_zsmul_eq_zero exists_nsmul_eq_zero_of_zsmul_eq_zero

end Group

section CommGroup

variable [CommGroup G] {a b c d : G}

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

/- warning: div_eq_of_eq_mul' -> div_eq_of_eq_mul' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b c)) -> (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b c)) -> (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) c)
Case conversion may be inaccurate. Consider using '#align div_eq_of_eq_mul' div_eq_of_eq_mul'ₓ'. -/
@[to_additive]
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]
#align div_eq_of_eq_mul' div_eq_of_eq_mul'
#align sub_eq_of_eq_add' sub_eq_of_eq_add'

/- warning: mul_div_mul_left_eq_div -> mul_div_mul_left_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) c a) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) c b)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) c a) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) c b)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b)
Case conversion may be inaccurate. Consider using '#align mul_div_mul_left_eq_div mul_div_mul_left_eq_divₓ'. -/
@[simp, to_additive]
theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by simp
#align mul_div_mul_left_eq_div mul_div_mul_left_eq_div
#align add_sub_add_left_eq_sub add_sub_add_left_eq_sub

/- warning: eq_div_of_mul_eq'' -> eq_div_of_mul_eq'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) c a) b) -> (Eq.{succ u1} G a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) c a) b) -> (Eq.{succ u1} G a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b c))
Case conversion may be inaccurate. Consider using '#align eq_div_of_mul_eq'' eq_div_of_mul_eq''ₓ'. -/
@[to_additive eq_sub_of_add_eq']
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]
#align eq_div_of_mul_eq'' eq_div_of_mul_eq''
#align eq_sub_of_add_eq' eq_sub_of_add_eq'

/- warning: eq_mul_of_div_eq' -> eq_mul_of_div_eq' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) c) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) c) -> (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_div_eq' eq_mul_of_div_eq'ₓ'. -/
@[to_additive]
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]
#align eq_mul_of_div_eq' eq_mul_of_div_eq'
#align eq_add_of_sub_eq' eq_add_of_sub_eq'

/- warning: mul_eq_of_eq_div' -> mul_eq_of_eq_div' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G b (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c a)) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b) c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, (Eq.{succ u1} G b (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c a)) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_div' mul_eq_of_eq_div'ₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by simp [h];
  rw [mul_comm c, mul_inv_cancel_left]
#align mul_eq_of_eq_div' mul_eq_of_eq_div'
#align add_eq_of_eq_sub' add_eq_of_eq_sub'

/- warning: div_div_self' -> div_div_self' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b)) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b)) b
Case conversion may be inaccurate. Consider using '#align div_div_self' div_div_self'ₓ'. -/
@[to_additive sub_sub_self]
theorem div_div_self' (a b : G) : a / (a / b) = b := by simpa using mul_inv_cancel_left a b
#align div_div_self' div_div_self'
#align sub_sub_self sub_sub_self

/- warning: div_eq_div_mul_div -> div_eq_div_mul_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a c))
Case conversion may be inaccurate. Consider using '#align div_eq_div_mul_div div_eq_div_mul_divₓ'. -/
@[to_additive]
theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]
#align div_eq_div_mul_div div_eq_div_mul_div
#align sub_eq_sub_add_sub sub_eq_sub_add_sub

/- warning: div_div_cancel -> div_div_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b)) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b)) b
Case conversion may be inaccurate. Consider using '#align div_div_cancel div_div_cancelₓ'. -/
@[simp, to_additive]
theorem div_div_cancel (a b : G) : a / (a / b) = b :=
  div_div_self' a b
#align div_div_cancel div_div_cancel
#align sub_sub_cancel sub_sub_cancel

/- warning: div_div_cancel_left -> div_div_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) a) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) a) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) b)
Case conversion may be inaccurate. Consider using '#align div_div_cancel_left div_div_cancel_leftₓ'. -/
@[simp, to_additive]
theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp
#align div_div_cancel_left div_div_cancel_left
#align sub_sub_cancel_left sub_sub_cancel_left

/- warning: eq_div_iff_mul_eq'' -> eq_div_iff_mul_eq'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b c)) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) c a) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b c)) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) c a) b)
Case conversion may be inaccurate. Consider using '#align eq_div_iff_mul_eq'' eq_div_iff_mul_eq''ₓ'. -/
@[to_additive eq_sub_iff_add_eq']
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]
#align eq_div_iff_mul_eq'' eq_div_iff_mul_eq''
#align eq_sub_iff_add_eq' eq_sub_iff_add_eq'

/- warning: div_eq_iff_eq_mul' -> div_eq_iff_eq_mul' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) c) (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b c))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) c) (Eq.{succ u1} G a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_eq_iff_eq_mul' div_eq_iff_eq_mul'ₓ'. -/
@[to_additive]
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]
#align div_eq_iff_eq_mul' div_eq_iff_eq_mul'
#align sub_eq_iff_eq_add' sub_eq_iff_eq_add'

/- warning: mul_div_cancel''' -> mul_div_cancel''' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b) a) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b) a) b
Case conversion may be inaccurate. Consider using '#align mul_div_cancel''' mul_div_cancel'''ₓ'. -/
@[simp, to_additive add_sub_cancel']
theorem mul_div_cancel''' (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]
#align mul_div_cancel''' mul_div_cancel'''
#align add_sub_cancel' add_sub_cancel'

/- warning: mul_div_cancel'_right -> mul_div_cancel'_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b a)) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b a)) b
Case conversion may be inaccurate. Consider using '#align mul_div_cancel'_right mul_div_cancel'_rightₓ'. -/
@[simp, to_additive]
theorem mul_div_cancel'_right (a b : G) : a * (b / a) = b := by
  rw [← mul_div_assoc, mul_div_cancel''']
#align mul_div_cancel'_right mul_div_cancel'_right
#align add_sub_cancel'_right add_sub_cancel'_right

/- warning: div_mul_cancel'' -> div_mul_cancel'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b)) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b)) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) b)
Case conversion may be inaccurate. Consider using '#align div_mul_cancel'' div_mul_cancel''ₓ'. -/
@[simp, to_additive sub_add_cancel']
theorem div_mul_cancel'' (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel''']
#align div_mul_cancel'' div_mul_cancel''
#align sub_add_cancel' sub_add_cancel'

/- warning: mul_mul_inv_cancel'_right -> mul_mul_inv_cancel'_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) a))) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) a))) b
Case conversion may be inaccurate. Consider using '#align mul_mul_inv_cancel'_right mul_mul_inv_cancel'_rightₓ'. -/
-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined  in `algebra/group/commute`
@[to_additive]
theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by
  rw [← div_eq_mul_inv, mul_div_cancel'_right a b]
#align mul_mul_inv_cancel'_right mul_mul_inv_cancel'_right
#align add_add_neg_cancel'_right add_add_neg_cancel'_right

/- warning: mul_mul_div_cancel -> mul_mul_div_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a c) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b c)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a c) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b c)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align mul_mul_div_cancel mul_mul_div_cancelₓ'. -/
@[simp, to_additive]
theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by
  rw [mul_assoc, mul_div_cancel'_right]
#align mul_mul_div_cancel mul_mul_div_cancel
#align add_add_sub_cancel add_add_sub_cancel

/- warning: div_mul_mul_cancel -> div_mul_mul_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b c)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a c) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b c)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align div_mul_mul_cancel div_mul_mul_cancelₓ'. -/
@[simp, to_additive]
theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by
  rw [mul_left_comm, div_mul_cancel', mul_comm]
#align div_mul_mul_cancel div_mul_mul_cancel
#align sub_add_add_cancel sub_add_add_cancel

/- warning: div_mul_div_cancel'' -> div_mul_div_cancel'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c a)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c a)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c b)
Case conversion may be inaccurate. Consider using '#align div_mul_div_cancel'' div_mul_div_cancel''ₓ'. -/
@[simp, to_additive sub_add_sub_cancel']
theorem div_mul_div_cancel'' (a b c : G) : a / b * (c / a) = c / b := by
  rw [mul_comm] <;> apply div_mul_div_cancel'
#align div_mul_div_cancel'' div_mul_div_cancel''
#align sub_add_sub_cancel' sub_add_sub_cancel'

/- warning: mul_div_div_cancel -> mul_div_div_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a c)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b c)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a c)) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b c)
Case conversion may be inaccurate. Consider using '#align mul_div_div_cancel mul_div_div_cancelₓ'. -/
@[simp, to_additive]
theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by
  rw [← div_mul, mul_div_cancel''']
#align mul_div_div_cancel mul_div_div_cancel
#align add_sub_sub_cancel add_sub_sub_cancel

/- warning: div_div_div_cancel_left -> div_div_div_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c a) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c b)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G) (c : G), Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c a) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c b)) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b a)
Case conversion may be inaccurate. Consider using '#align div_div_div_cancel_left div_div_div_cancel_leftₓ'. -/
@[simp, to_additive]
theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c, div_inv_eq_mul, mul_comm, div_mul_div_cancel']
#align div_div_div_cancel_left div_div_div_cancel_left
#align sub_sub_sub_cancel_left sub_sub_sub_cancel_left

/- warning: div_eq_div_iff_mul_eq_mul -> div_eq_div_iff_mul_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c d)) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) c b))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c d)) (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a d) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align div_eq_div_iff_mul_eq_mul div_eq_div_iff_mul_eq_mulₓ'. -/
@[to_additive]
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b :=
  by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]
#align div_eq_div_iff_mul_eq_mul div_eq_div_iff_mul_eq_mul
#align sub_eq_sub_iff_add_eq_add sub_eq_sub_iff_add_eq_add

/- warning: div_eq_div_iff_div_eq_div -> div_eq_div_iff_div_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c d)) (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a c) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b d))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a b) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) c d)) (Eq.{succ u1} G (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) a c) (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) b d))
Case conversion may be inaccurate. Consider using '#align div_eq_div_iff_div_eq_div div_eq_div_iff_div_eq_divₓ'. -/
@[to_additive]
theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]
#align div_eq_div_iff_div_eq_div div_eq_div_iff_div_eq_div
#align sub_eq_sub_iff_sub_eq_sub sub_eq_sub_iff_sub_eq_sub

end CommGroup

section SubtractionCommMonoid

variable {M : Type u} [SubtractionCommMonoid M]

theorem bit0_sub (a b : M) : bit0 (a - b) = bit0 a - bit0 b :=
  sub_add_sub_comm _ _ _ _
#align bit0_sub bit0_sub

theorem bit1_sub [One M] (a b : M) : bit1 (a - b) = bit1 a - bit0 b :=
  (congr_arg (· + (1 : M)) <| bit0_sub a b : _).trans <| sub_add_eq_add_sub _ _ _
#align bit1_sub bit1_sub

end SubtractionCommMonoid

section Multiplicative

variable [Monoid β] (p r : α → α → Prop) [IsTotal α r] (f : α → α → β)

/- warning: multiplicative_of_symmetric_of_is_total -> multiplicative_of_symmetric_of_isTotal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] (p : α -> α -> Prop) (r : α -> α -> Prop) [_inst_2 : IsTotal.{u1} α r] (f : α -> α -> β), (Symmetric.{succ u1} α p) -> (forall {a : α} {b : α}, (p a b) -> (Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (f a b) (f b a)) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))))))) -> (forall {a : α} {b : α} {c : α}, (r a b) -> (r b c) -> (p a b) -> (p b c) -> (p a c) -> (Eq.{succ u2} β (f a c) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (f a b) (f b c)))) -> (forall {a : α} {b : α} {c : α}, (p a b) -> (p b c) -> (p a c) -> (Eq.{succ u2} β (f a c) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (f a b) (f b c))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Monoid.{u1} β] (p : α -> α -> Prop) (r : α -> α -> Prop) [_inst_2 : IsTotal.{u2} α r] (f : α -> α -> β), (Symmetric.{succ u2} α p) -> (forall {a : α} {b : α}, (p a b) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) (f a b) (f b a)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β _inst_1))))) -> (forall {a : α} {b : α} {c : α}, (r a b) -> (r b c) -> (p a b) -> (p b c) -> (p a c) -> (Eq.{succ u1} β (f a c) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) (f a b) (f b c)))) -> (forall {a : α} {b : α} {c : α}, (p a b) -> (p b c) -> (p a c) -> (Eq.{succ u1} β (f a c) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β _inst_1))) (f a b) (f b c))))
Case conversion may be inaccurate. Consider using '#align multiplicative_of_symmetric_of_is_total multiplicative_of_symmetric_of_isTotalₓ'. -/
@[to_additive additive_of_symmetric_of_isTotal]
theorem multiplicative_of_symmetric_of_isTotal (hsymm : Symmetric p)
    (hf_swap : ∀ {a b}, p a b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a b → p b c → p a c → f a c = f a b * f b c) {a b c : α}
    (pab : p a b) (pbc : p b c) (pac : p a c) : f a c = f a b * f b c :=
  by
  suffices ∀ {b c}, r b c → p a b → p b c → p a c → f a c = f a b * f b c
    by
    obtain rbc | rcb := total_of r b c
    · exact this rbc pab pbc pac
    · rw [this rcb pac (hsymm pbc) pab, mul_assoc, hf_swap (hsymm pbc), mul_one]
  intro b c rbc pab pbc pac
  obtain rab | rba := total_of r a b
  · exact hmul rab rbc pab pbc pac
  rw [← one_mul (f a c), ← hf_swap pab, mul_assoc]
  obtain rac | rca := total_of r a c
  · rw [hmul rba rac (hsymm pab) pac pbc]
  · rw [hmul rbc rca pbc (hsymm pac) (hsymm pab), mul_assoc, hf_swap (hsymm pac), mul_one]
#align multiplicative_of_symmetric_of_is_total multiplicative_of_symmetric_of_isTotal
#align additive_of_symmetric_of_is_total additive_of_symmetric_of_isTotal

/- warning: multiplicative_of_is_total -> multiplicative_of_isTotal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] (r : α -> α -> Prop) [_inst_2 : IsTotal.{u1} α r] (f : α -> α -> β) (p : α -> Prop), (forall {a : α} {b : α}, (p a) -> (p b) -> (Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (f a b) (f b a)) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))))))) -> (forall {a : α} {b : α} {c : α}, (r a b) -> (r b c) -> (p a) -> (p b) -> (p c) -> (Eq.{succ u2} β (f a c) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (f a b) (f b c)))) -> (forall {a : α} {b : α} {c : α}, (p a) -> (p b) -> (p c) -> (Eq.{succ u2} β (f a c) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (f a b) (f b c))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u2} β] (r : α -> α -> β) (_inst_2 : α -> α -> Prop) [f : IsTotal.{u1} α _inst_2], (forall (ᾰ : α) (b : α), Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (r ᾰ b) (r b ᾰ)) (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (Monoid.toOne.{u2} β _inst_1)))) -> (forall {a : α} {b : α} {ᾰ : α}, (_inst_2 a b) -> (_inst_2 b ᾰ) -> (Eq.{succ u2} β (r a ᾰ) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (r a b) (r b ᾰ)))) -> (forall (hmul : α) (a : α) (b : α), Eq.{succ u2} β (r hmul b) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_1))) (r hmul a) (r a b)))
Case conversion may be inaccurate. Consider using '#align multiplicative_of_is_total multiplicative_of_isTotalₓ'. -/
/-- If a binary function from a type equipped with a total relation `r` to a monoid is
  anti-symmetric (i.e. satisfies `f a b * f b a = 1`), in order to show it is multiplicative
  (i.e. satisfies `f a c = f a b * f b c`), we may assume `r a b` and `r b c` are satisfied.
  We allow restricting to a subset specified by a predicate `p`. -/
@[to_additive additive_of_isTotal
      "If a binary function from a type equipped with a total relation\n  `r` to an additive monoid is anti-symmetric (i.e. satisfies `f a b + f b a = 0`), in order to show\n  it is additive (i.e. satisfies `f a c = f a b + f b c`), we may assume `r a b` and `r b c`\n  are satisfied. We allow restricting to a subset specified by a predicate `p`."]
theorem multiplicative_of_isTotal (p : α → Prop) (hswap : ∀ {a b}, p a → p b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a → p b → p c → f a c = f a b * f b c) {a b c : α}
    (pa : p a) (pb : p b) (pc : p c) : f a c = f a b * f b c :=
  by
  apply multiplicative_of_symmetric_of_isTotal (fun a b => p a ∧ p b) r f fun _ _ => And.symm
  · simp_rw [and_imp]
    exact @hswap
  · exact fun a b c rab rbc pab pbc pac => hmul rab rbc pab.1 pab.2 pac.2
  exacts[⟨pa, pb⟩, ⟨pb, pc⟩, ⟨pa, pc⟩]
#align multiplicative_of_is_total multiplicative_of_isTotal
#align additive_of_is_total additive_of_isTotal

end Multiplicative

