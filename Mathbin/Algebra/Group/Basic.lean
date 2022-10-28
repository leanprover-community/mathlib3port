/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathbin.Algebra.Group.Defs

/-!
# Basic lemmas about semigroups, monoids, and groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/457
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
theorem comp_assoc_left : f x ∘ f y = f (f x y) := by
  ext z
  rw [Function.comp_apply, @IsAssociative.assoc _ f]

/-- Composing two associative operations of `f : α → α → α` on the right
is equal to an associative operation on the right.
-/
theorem comp_assoc_right : ((fun z => f z x) ∘ fun z => f z y) = fun z => f z (f y x) := by
  ext z
  rw [Function.comp_apply, @IsAssociative.assoc _ f]

end Associative

section Semigroup

/- warning: comp_mul_left -> comp_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Semigroup.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (α -> α) (Function.comp.{succ u_1 succ u_1 succ u_1} α α α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) x) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) y)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) x y))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.17 : Semigroup.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (α -> α) (Function.comp.{succ u_1 succ u_1 succ u_1} α α α (fun (a._@.Mathlib.Algebra.Group.Basic._hyg.31 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.17)) x a._@.Mathlib.Algebra.Group.Basic._hyg.31) (fun (a._@.Mathlib.Algebra.Group.Basic._hyg.42 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.17)) y a._@.Mathlib.Algebra.Group.Basic._hyg.42)) (fun (a._@.Mathlib.Algebra.Group.Basic._hyg.53 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.17)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.17)) x y) a._@.Mathlib.Algebra.Group.Basic._hyg.53)
Case conversion may be inaccurate. Consider using '#align comp_mul_left comp_mul_leftₓ'. -/
/-- Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[simp,
  to_additive "Composing two additions on the left by `y` then `x`\nis equal to a addition on the left by `x + y`."]
theorem comp_mul_left [Semigroup α] (x y : α) : (· * ·) x ∘ (· * ·) y = (· * ·) (x * y) :=
  comp_assoc_left _ _ _

/- warning: comp_mul_right -> comp_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : Semigroup.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (α -> α) (Function.comp.{succ u_1 succ u_1 succ u_1} α α α (fun (_x : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) _x x) (fun (_x : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) _x y)) (fun (_x : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) _x (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) y x))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.126 : Semigroup.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (α -> α) (Function.comp.{succ u_1 succ u_1 succ u_1} α α α (fun (a._@.Mathlib.Algebra.Group.Basic._hyg.140 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.126)) a._@.Mathlib.Algebra.Group.Basic._hyg.140 x) (fun (a._@.Mathlib.Algebra.Group.Basic._hyg.151 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.126)) a._@.Mathlib.Algebra.Group.Basic._hyg.151 y)) (fun (a._@.Mathlib.Algebra.Group.Basic._hyg.162 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.126)) a._@.Mathlib.Algebra.Group.Basic._hyg.162 (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.126)) y x))
Case conversion may be inaccurate. Consider using '#align comp_mul_right comp_mul_rightₓ'. -/
/-- Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[simp,
  to_additive "Composing two additions on the right by `y` and `x`\nis equal to a addition on the right by `y + x`."]
theorem comp_mul_right [Semigroup α] (x y : α) : (· * x) ∘ (· * y) = (· * (y * x)) :=
  comp_assoc_right _ _ _

end Semigroup

section MulOneClass

variable {M : Type u} [MulOneClass M]

/- warning: ite_mul_one -> ite_mul_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M] {P : Prop} [_inst_2 : Decidable P] {a : M} {b : M}, Eq.{succ u} M (ite.{succ u} M P _inst_2 (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) a b) (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) (ite.{succ u} M P _inst_2 a (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))) (ite.{succ u} M P _inst_2 b (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))))
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.248 : MulOneClass.{u} M] {P : Prop} [inst._@.Mathlib.Algebra.Group.Basic._hyg.252 : Decidable P] {a : M} {b : M}, Eq.{succ u} M (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.252 (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.248)) a b) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.248)))) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.248)) (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.252 a (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.248)))) (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.252 b (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.248)))))
Case conversion may be inaccurate. Consider using '#align ite_mul_one ite_mul_oneₓ'. -/
@[to_additive]
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} : ite P (a * b) 1 = ite P a 1 * ite P b 1 := by
  by_cases h:P <;> simp [h]

/- warning: ite_one_mul -> ite_one_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M] {P : Prop} [_inst_2 : Decidable P] {a : M} {b : M}, Eq.{succ u} M (ite.{succ u} M P _inst_2 (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1)) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) a b)) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) (ite.{succ u} M P _inst_2 (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1)) a) (ite.{succ u} M P _inst_2 (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1)) b))
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.324 : MulOneClass.{u} M] {P : Prop} [inst._@.Mathlib.Algebra.Group.Basic._hyg.328 : Decidable P] {a : M} {b : M}, Eq.{succ u} M (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.328 (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.324))) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.324)) a b)) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.324)) (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.328 (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.324))) a) (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.328 (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.324))) b))
Case conversion may be inaccurate. Consider using '#align ite_one_mul ite_one_mulₓ'. -/
@[to_additive]
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} : ite P 1 (a * b) = ite P 1 a * ite P 1 b := by
  by_cases h:P <;> simp [h]

/- warning: eq_one_iff_eq_one_of_mul_eq_one -> eq_one_iff_eq_one_of_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M] {a : M} {b : M}, (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) a b) (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))) -> (Iff (Eq.{succ u} M a (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))) (Eq.{succ u} M b (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))))
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.400 : MulOneClass.{u} M] {a : M} {b : M}, (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.400)) a b) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.400)))) -> (Iff (Eq.{succ u} M a (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.400)))) (Eq.{succ u} M b (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.400)))))
Case conversion may be inaccurate. Consider using '#align eq_one_iff_eq_one_of_mul_eq_one eq_one_iff_eq_one_of_mul_eq_oneₓ'. -/
@[to_additive]
theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  constructor <;>
    · rintro rfl
      simpa using h
      

/- warning: one_mul_eq_id -> one_mul_eq_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M], Eq.{succ u} (M -> M) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))) (id.{succ u} M)
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.509 : MulOneClass.{u} M], Eq.{succ u} (M -> M) ((fun (a._@.Mathlib.Algebra.Group.Basic._hyg.518 : M) (a._@.Mathlib.Algebra.Group.Basic._hyg.519 : M) => HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.509)) a._@.Mathlib.Algebra.Group.Basic._hyg.518 a._@.Mathlib.Algebra.Group.Basic._hyg.519) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.509)))) (id.{succ u} M)
Case conversion may be inaccurate. Consider using '#align one_mul_eq_id one_mul_eq_idₓ'. -/
@[to_additive]
theorem one_mul_eq_id : (· * ·) (1 : M) = id :=
  funext one_mul

/- warning: mul_one_eq_id -> mul_one_eq_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M], Eq.{succ u} (M -> M) (fun (_x : M) => HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) _x (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))) (id.{succ u} M)
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.541 : MulOneClass.{u} M], Eq.{succ u} (M -> M) (fun (a._@.Mathlib.Algebra.Group.Basic._hyg.549 : M) => HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.541)) a._@.Mathlib.Algebra.Group.Basic._hyg.549 (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.541)))) (id.{succ u} M)
Case conversion may be inaccurate. Consider using '#align mul_one_eq_id mul_one_eq_idₓ'. -/
@[to_additive]
theorem mul_one_eq_id : (· * (1 : M)) = id :=
  funext mul_one

end MulOneClass

section CommSemigroup

variable [CommSemigroup G]

/- warning: mul_left_comm -> mul_left_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommSemigroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) b c)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) b (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.579 : CommSemigroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.579))) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.579))) b c)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.579))) b (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.579))) a c))
Case conversion may be inaccurate. Consider using '#align mul_left_comm mul_left_commₓ'. -/
@[no_rsimp, to_additive]
theorem mul_left_comm : ∀ a b c : G, a * (b * c) = b * (a * c) :=
  left_comm Mul.mul mul_comm mul_assoc

/- warning: mul_right_comm -> mul_right_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommSemigroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a b) c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a c) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.610 : CommSemigroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.610))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.610))) a b) c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.610))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.610))) a c) b)
Case conversion may be inaccurate. Consider using '#align mul_right_comm mul_right_commₓ'. -/
@[to_additive]
theorem mul_right_comm : ∀ a b c : G, a * b * c = a * c * b :=
  right_comm Mul.mul mul_comm mul_assoc

/- warning: mul_mul_mul_comm -> mul_mul_mul_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommSemigroup.{u_3} G] (a : G) (b : G) (c : G) (d : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a b) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) c d)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) b d))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.641 : CommSemigroup.{u_1} G] (a : G) (b : G) (c : G) (d : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.641))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.641))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.641))) c d)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.641))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.641))) a c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.641))) b d))
Case conversion may be inaccurate. Consider using '#align mul_mul_mul_comm mul_mul_mul_commₓ'. -/
@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by simp only [mul_left_comm, mul_assoc]

/- warning: mul_rotate -> mul_rotate is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommSemigroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a b) c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) b c) a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.673 : CommSemigroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.673))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.673))) a b) c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.673))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.673))) b c) a)
Case conversion may be inaccurate. Consider using '#align mul_rotate mul_rotateₓ'. -/
@[to_additive]
theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by simp only [mul_left_comm, mul_comm]

/- warning: mul_rotate' -> mul_rotate' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommSemigroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) b c)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) b (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) c a))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.700 : CommSemigroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.700))) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.700))) b c)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.700))) b (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.700))) c a))
Case conversion may be inaccurate. Consider using '#align mul_rotate' mul_rotate'ₓ'. -/
@[to_additive]
theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by simp only [mul_left_comm, mul_comm]

end CommSemigroup

section AddCommSemigroup

variable {M : Type u} [AddCommSemigroup M]

theorem bit0_add (a b : M) : bit0 (a + b) = bit0 a + bit0 b :=
  add_add_add_comm _ _ _ _

theorem bit1_add [One M] (a b : M) : bit1 (a + b) = bit0 a + bit1 b :=
  (congr_arg (· + (1 : M)) <| bit0_add a b : _).trans (add_assoc _ _ _)

theorem bit1_add' [One M] (a b : M) : bit1 (a + b) = bit1 a + bit0 b := by rw [add_comm, bit1_add, add_comm]

end AddCommSemigroup

attribute [local simp] mul_assoc sub_eq_add_neg

section AddMonoid

variable {M : Type u} [AddMonoid M] {a b c : M}

@[simp]
theorem bit0_zero : bit0 (0 : M) = 0 :=
  add_zero _

@[simp]
theorem bit1_zero [One M] : bit1 (0 : M) = 1 := by rw [bit1, bit0_zero, zero_add]

end AddMonoid

section CommMonoid

variable {M : Type u} [CommMonoid M] {x y z : M}

/- warning: inv_unique -> inv_unique is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : CommMonoid.{u} M] {x : M} {y : M} {z : M}, (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M (CommMonoid.toMonoid.{u} M _inst_1)))) x y) (One.one.{u} M (MulOneClass.toHasOne.{u} M (Monoid.toMulOneClass.{u} M (CommMonoid.toMonoid.{u} M _inst_1))))) -> (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M (CommMonoid.toMonoid.{u} M _inst_1)))) x z) (One.one.{u} M (MulOneClass.toHasOne.{u} M (Monoid.toMulOneClass.{u} M (CommMonoid.toMonoid.{u} M _inst_1))))) -> (Eq.{succ u} M y z)
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.747 : CommMonoid.{u} M] {x : M} {y : M} {z : M}, (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (CommMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.747)))) x y) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (Monoid.toOne.{u} M (CommMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.747))))) -> (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (CommMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.747)))) x z) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (Monoid.toOne.{u} M (CommMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.747))))) -> (Eq.{succ u} M y z)
Case conversion may be inaccurate. Consider using '#align inv_unique inv_uniqueₓ'. -/
@[to_additive]
theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
  left_inv_eq_right_inv (trans (mul_comm _ _) hy) hz

end CommMonoid

section LeftCancelMonoid

variable {M : Type u} [LeftCancelMonoid M] {a b : M}

/- warning: mul_right_eq_self -> mul_right_eq_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : LeftCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M (LeftCancelMonoid.toMonoid.{u} M _inst_1)))) a b) a) (Eq.{succ u} M b (One.one.{u} M (MulOneClass.toHasOne.{u} M (Monoid.toMulOneClass.{u} M (LeftCancelMonoid.toMonoid.{u} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.804 : LeftCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (LeftCancelMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.804)))) a b) a) (Eq.{succ u} M b (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (LeftCancelMonoid.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.804))))
Case conversion may be inaccurate. Consider using '#align mul_right_eq_self mul_right_eq_selfₓ'. -/
@[simp, to_additive]
theorem mul_right_eq_self : a * b = a ↔ b = 1 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 := mul_left_cancel_iff
    

/- warning: self_eq_mul_right -> self_eq_mul_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : LeftCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M a (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M (LeftCancelMonoid.toMonoid.{u} M _inst_1)))) a b)) (Eq.{succ u} M b (One.one.{u} M (MulOneClass.toHasOne.{u} M (Monoid.toMulOneClass.{u} M (LeftCancelMonoid.toMonoid.{u} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.889 : LeftCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M a (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (LeftCancelMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.889)))) a b)) (Eq.{succ u} M b (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (LeftCancelMonoid.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.889))))
Case conversion may be inaccurate. Consider using '#align self_eq_mul_right self_eq_mul_rightₓ'. -/
@[simp, to_additive]
theorem self_eq_mul_right : a = a * b ↔ b = 1 :=
  eq_comm.trans mul_right_eq_self

end LeftCancelMonoid

section RightCancelMonoid

variable {M : Type u} [RightCancelMonoid M] {a b : M}

/- warning: mul_left_eq_self -> mul_left_eq_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : RightCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M (RightCancelMonoid.toMonoid.{u} M _inst_1)))) a b) b) (Eq.{succ u} M a (One.one.{u} M (MulOneClass.toHasOne.{u} M (Monoid.toMulOneClass.{u} M (RightCancelMonoid.toMonoid.{u} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.932 : RightCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (RightCancelMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.932)))) a b) b) (Eq.{succ u} M a (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (RightCancelMonoid.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.932))))
Case conversion may be inaccurate. Consider using '#align mul_left_eq_self mul_left_eq_selfₓ'. -/
@[simp, to_additive]
theorem mul_left_eq_self : a * b = b ↔ a = 1 :=
  calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 := mul_right_cancel_iff
    

/- warning: self_eq_mul_left -> self_eq_mul_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : RightCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M b (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M (RightCancelMonoid.toMonoid.{u} M _inst_1)))) a b)) (Eq.{succ u} M a (One.one.{u} M (MulOneClass.toHasOne.{u} M (Monoid.toMulOneClass.{u} M (RightCancelMonoid.toMonoid.{u} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1017 : RightCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M b (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (RightCancelMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.1017)))) a b)) (Eq.{succ u} M a (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (RightCancelMonoid.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.1017))))
Case conversion may be inaccurate. Consider using '#align self_eq_mul_left self_eq_mul_leftₓ'. -/
@[simp, to_additive]
theorem self_eq_mul_left : b = a * b ↔ a = 1 :=
  eq_comm.trans mul_left_eq_self

end RightCancelMonoid

section HasInvolutiveInv

variable [HasInvolutiveInv G] {a b : G}

/- warning: inv_involutive -> inv_involutive is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G], Function.Involutive.{succ u_3} G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1057 : HasInvolutiveInv.{u_1} G], Function.involutive.{succ u_1} G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1057))
Case conversion may be inaccurate. Consider using '#align inv_involutive inv_involutiveₓ'. -/
@[simp, to_additive]
theorem inv_involutive : Function.Involutive (Inv.inv : G → G) :=
  inv_inv

/- warning: inv_surjective -> inv_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G], Function.Surjective.{succ u_3 succ u_3} G G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1074 : HasInvolutiveInv.{u_1} G], Function.surjective.{succ u_1 succ u_1} G G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1074))
Case conversion may be inaccurate. Consider using '#align inv_surjective inv_surjectiveₓ'. -/
@[simp, to_additive]
theorem inv_surjective : Function.Surjective (Inv.inv : G → G) :=
  inv_involutive.Surjective

/- warning: inv_injective -> inv_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G], Function.Injective.{succ u_3 succ u_3} G G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1091 : HasInvolutiveInv.{u_1} G], Function.injective.{succ u_1 succ u_1} G G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1091))
Case conversion may be inaccurate. Consider using '#align inv_injective inv_injectiveₓ'. -/
@[to_additive]
theorem inv_injective : Function.Injective (Inv.inv : G → G) :=
  inv_involutive.Injective

/- warning: inv_inj -> inv_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a) (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) b)) (Eq.{succ u_3} G a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1108 : HasInvolutiveInv.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1108) a) (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1108) b)) (Eq.{succ u_1} G a b)
Case conversion may be inaccurate. Consider using '#align inv_inj inv_injₓ'. -/
@[simp, to_additive]
theorem inv_inj {a b : G} : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff

/- warning: eq_inv_of_eq_inv -> eq_inv_of_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G] {a : G} {b : G}, (Eq.{succ u_3} G a (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) b)) -> (Eq.{succ u_3} G b (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1141 : HasInvolutiveInv.{u_1} G] {a : G} {b : G}, (Eq.{succ u_1} G a (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1141) b)) -> (Eq.{succ u_1} G b (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1141) a))
Case conversion may be inaccurate. Consider using '#align eq_inv_of_eq_inv eq_inv_of_eq_invₓ'. -/
@[to_additive]
theorem eq_inv_of_eq_inv (h : a = b⁻¹) : b = a⁻¹ := by simp [h]

/- warning: eq_inv_iff_eq_inv -> eq_inv_iff_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G a (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) b)) (Eq.{succ u_3} G b (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1172 : HasInvolutiveInv.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G a (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1172) b)) (Eq.{succ u_1} G b (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1172) a))
Case conversion may be inaccurate. Consider using '#align eq_inv_iff_eq_inv eq_inv_iff_eq_invₓ'. -/
@[to_additive]
theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
  ⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩

/- warning: inv_eq_iff_inv_eq -> inv_eq_iff_inv_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a) b) (Eq.{succ u_3} G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) b) a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1206 : HasInvolutiveInv.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1206) a) b) (Eq.{succ u_1} G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1206) b) a)
Case conversion may be inaccurate. Consider using '#align inv_eq_iff_inv_eq inv_eq_iff_inv_eqₓ'. -/
@[to_additive]
theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
  eq_comm.trans <| eq_inv_iff_eq_inv.trans eq_comm

variable (G)

/- warning: inv_comp_inv -> inv_comp_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u_3}) [_inst_1 : HasInvolutiveInv.{u_3} G], Eq.{succ u_3} (G -> G) (Function.comp.{succ u_3 succ u_3 succ u_3} G G G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1)) (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1))) (id.{succ u_3} G)
but is expected to have type
  forall (G : Type.{u_1}) [inst._@.Mathlib.Algebra.Group.Basic._hyg.1251 : HasInvolutiveInv.{u_1} G], Eq.{succ u_1} (G -> G) (Function.comp.{succ u_1 succ u_1 succ u_1} G G G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1251)) (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1251))) (id.{succ u_1} G)
Case conversion may be inaccurate. Consider using '#align inv_comp_inv inv_comp_invₓ'. -/
@[simp, to_additive]
theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  inv_involutive.comp_self

/- warning: left_inverse_inv -> left_inverse_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u_3}) [_inst_1 : HasInvolutiveInv.{u_3} G], Function.LeftInverse.{succ u_3 succ u_3} G G (fun (a : G) => Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a) (fun (a : G) => Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a)
but is expected to have type
  forall (G : Type.{u_1}) [inst._@.Mathlib.Algebra.Group.Basic._hyg.1272 : HasInvolutiveInv.{u_1} G], Function.LeftInverse.{succ u_1 succ u_1} G G (fun (a : G) => Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1272) a) (fun (a : G) => Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1272) a)
Case conversion may be inaccurate. Consider using '#align left_inverse_inv left_inverse_invₓ'. -/
@[to_additive]
theorem left_inverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv

/- warning: right_inverse_inv -> right_inverse_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u_3}) [_inst_1 : HasInvolutiveInv.{u_3} G], Function.LeftInverse.{succ u_3 succ u_3} G G (fun (a : G) => Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a) (fun (a : G) => Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a)
but is expected to have type
  forall (G : Type.{u_1}) [inst._@.Mathlib.Algebra.Group.Basic._hyg.1301 : HasInvolutiveInv.{u_1} G], Function.LeftInverse.{succ u_1 succ u_1} G G (fun (a : G) => Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1301) a) (fun (a : G) => Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1301) a)
Case conversion may be inaccurate. Consider using '#align right_inverse_inv right_inverse_invₓ'. -/
@[to_additive]
theorem right_inverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv

end HasInvolutiveInv

section DivInvMonoid

variable [DivInvMonoid G] {a b c : G}

/- warning: inv_eq_one_div -> inv_eq_one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (x : G), Eq.{succ u_3} G (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G _inst_1) x) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) x)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1346 : DivInvMonoid.{u_1} G] (x : G), Eq.{succ u_1} G (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1346) x) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1346)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1346)))) x)
Case conversion may be inaccurate. Consider using '#align inv_eq_one_div inv_eq_one_divₓ'. -/
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]

/- warning: mul_one_div -> mul_one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (x : G) (y : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) x (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) y)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) x y)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1398 : DivInvMonoid.{u_1} G] (x : G) (y : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1398)))) x (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1398)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1398)))) y)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1398)) x y)
Case conversion may be inaccurate. Consider using '#align mul_one_div mul_one_divₓ'. -/
@[to_additive]
theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

/- warning: mul_div_assoc -> mul_div_assoc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a b) c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1452 : DivInvMonoid.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1452)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1452)))) a b) c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1452)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1452)) b c))
Case conversion may be inaccurate. Consider using '#align mul_div_assoc mul_div_assocₓ'. -/
@[to_additive]
theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]

/- warning: mul_div_assoc' -> mul_div_assoc' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) b c)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1512 : DivInvMonoid.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1512)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1512)) b c)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1512)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1512)))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_div_assoc' mul_div_assoc'ₓ'. -/
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c :=
  (mul_div_assoc _ _ _).symm

/- warning: one_div -> one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (a : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G _inst_1) a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1545 : DivInvMonoid.{u_1} G] (a : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1545)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1545)))) a) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1545) a)
Case conversion may be inaccurate. Consider using '#align one_div one_divₓ'. -/
@[simp, to_additive]
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm

/- warning: mul_div -> mul_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) b c)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1572 : DivInvMonoid.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1572)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1572)) b c)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1572)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1572)))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_div mul_divₓ'. -/
@[to_additive]
theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]

/- warning: div_eq_mul_one_div -> div_eq_mul_one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) a b) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1602 : DivInvMonoid.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1602)) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1602)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1602)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1602)))) b))
Case conversion may be inaccurate. Consider using '#align div_eq_mul_one_div div_eq_mul_one_divₓ'. -/
@[to_additive]
theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by rw [div_eq_mul_inv, one_div]

end DivInvMonoid

section DivInvOneMonoid

variable [DivInvOneMonoid G]

/- warning: div_one -> div_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvOneMonoid.{u_3} G] (a : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (DivInvOneMonoid.toDivInvMonoid.{u_3} G _inst_1))) a (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (DivInvOneMonoid.toDivInvMonoid.{u_3} G _inst_1)))))) a
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1665 : DivInvOneMonoid.{u_1} G] (a : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (DivInvOneMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1665))) a (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1665))))) a
Case conversion may be inaccurate. Consider using '#align div_one div_oneₓ'. -/
@[simp, to_additive]
theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]

/- warning: one_div_one -> one_div_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvOneMonoid.{u_3} G], Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (DivInvOneMonoid.toDivInvMonoid.{u_3} G _inst_1))) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (DivInvOneMonoid.toDivInvMonoid.{u_3} G _inst_1))))) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (DivInvOneMonoid.toDivInvMonoid.{u_3} G _inst_1)))))) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (DivInvOneMonoid.toDivInvMonoid.{u_3} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1684 : DivInvOneMonoid.{u_1} G], Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (DivInvOneMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1684))) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1684)))) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1684))))) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1684))))
Case conversion may be inaccurate. Consider using '#align one_div_one one_div_oneₓ'. -/
@[to_additive]
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _

end DivInvOneMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv

/- warning: inv_eq_of_mul_eq_one_left -> inv_eq_of_mul_eq_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1721 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1721))))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1721)))))) -> (Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1721)) b) a)
Case conversion may be inaccurate. Consider using '#align inv_eq_of_mul_eq_one_left inv_eq_of_mul_eq_one_leftₓ'. -/
@[to_additive]
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by rw [← inv_eq_of_mul_eq_one_right h, inv_inv]

/- warning: eq_inv_of_mul_eq_one_left -> eq_inv_of_mul_eq_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α a (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1778 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1778))))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1778)))))) -> (Eq.{succ u_1} α a (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1778)) b))
Case conversion may be inaccurate. Consider using '#align eq_inv_of_mul_eq_one_left eq_inv_of_mul_eq_one_leftₓ'. -/
@[to_additive]
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm

/- warning: eq_inv_of_mul_eq_one_right -> eq_inv_of_mul_eq_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α b (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1809 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1809))))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1809)))))) -> (Eq.{succ u_1} α b (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1809)) a))
Case conversion may be inaccurate. Consider using '#align eq_inv_of_mul_eq_one_right eq_inv_of_mul_eq_one_rightₓ'. -/
@[to_additive]
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm

/- warning: eq_one_div_of_mul_eq_one_left -> eq_one_div_of_mul_eq_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b a) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1840 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1840))))) b a) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1840)))))) -> (Eq.{succ u_1} α b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1840))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1840))))) a))
Case conversion may be inaccurate. Consider using '#align eq_one_div_of_mul_eq_one_left eq_one_div_of_mul_eq_one_leftₓ'. -/
@[to_additive]
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by rw [eq_inv_of_mul_eq_one_left h, one_div]

/- warning: eq_one_div_of_mul_eq_one_right -> eq_one_div_of_mul_eq_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1895 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1895))))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1895)))))) -> (Eq.{succ u_1} α b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1895))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1895))))) a))
Case conversion may be inaccurate. Consider using '#align eq_one_div_of_mul_eq_one_right eq_one_div_of_mul_eq_one_rightₓ'. -/
@[to_additive]
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by rw [eq_inv_of_mul_eq_one_right h, one_div]

/- warning: eq_of_div_eq_one -> eq_of_div_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1950 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1950))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1950)))))) -> (Eq.{succ u_1} α a b)
Case conversion may be inaccurate. Consider using '#align eq_of_div_eq_one eq_of_div_eq_oneₓ'. -/
@[to_additive]
theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
  inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]

/- warning: div_ne_one_of_ne -> div_ne_one_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Ne.{succ u_1} α a b) -> (Ne.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2015 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Ne.{succ u_1} α a b) -> (Ne.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2015))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2015))))))
Case conversion may be inaccurate. Consider using '#align div_ne_one_of_ne div_ne_one_of_neₓ'. -/
@[to_additive]
theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 :=
  mt eq_of_div_eq_one

variable (a b c)

/- warning: one_div_mul_one_div_rev -> one_div_mul_one_div_rev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2055 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2055))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2055))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2055))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2055))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2055))))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2055))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2055))))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2055))))) b a))
Case conversion may be inaccurate. Consider using '#align one_div_mul_one_div_rev one_div_mul_one_div_revₓ'. -/
@[to_additive]
theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp

/- warning: inv_div_left -> inv_div_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) a) b) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2084 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2084))) (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2084)) a) b) (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2084)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2084))))) b a))
Case conversion may be inaccurate. Consider using '#align inv_div_left inv_div_leftₓ'. -/
@[to_additive]
theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp

/- warning: inv_div -> inv_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2119 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2119)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2119))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2119))) b a)
Case conversion may be inaccurate. Consider using '#align inv_div inv_divₓ'. -/
@[simp, to_additive]
theorem inv_div : (a / b)⁻¹ = b / a := by simp

/- warning: one_div_div -> one_div_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2150 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2150))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2150))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2150))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2150))) b a)
Case conversion may be inaccurate. Consider using '#align one_div_div one_div_divₓ'. -/
@[simp, to_additive]
theorem one_div_div : 1 / (a / b) = b / a := by simp

/- warning: one_div_one_div -> one_div_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a)) a
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2175 : DivisionMonoid.{u_1} α] (a : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2175))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2175))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2175))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2175))))) a)) a
Case conversion may be inaccurate. Consider using '#align one_div_one_div one_div_one_divₓ'. -/
@[to_additive]
theorem one_div_one_div : 1 / (1 / a) = a := by simp

@[to_additive]
instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
  { DivisionMonoid.toDivInvMonoid α with inv_one := by simpa only [one_div, inv_inv] using (inv_div (1 : α) 1).symm }

variable {a b c}

/- warning: inv_eq_one -> inv_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α}, Iff (Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) a) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) (Eq.{succ u_1} α a (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2286 : DivisionMonoid.{u_1} α] {a : α}, Iff (Eq.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2286))) a) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2286)))))) (Eq.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2286))))))
Case conversion may be inaccurate. Consider using '#align inv_eq_one inv_eq_oneₓ'. -/
@[simp, to_additive]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  inv_injective.eq_iff' inv_one

/- warning: one_eq_inv -> one_eq_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α}, Iff (Eq.{succ u_1} α (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) a)) (Eq.{succ u_1} α a (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2315 : DivisionMonoid.{u_1} α] {a : α}, Iff (Eq.{succ u_1} α (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2315))))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2315))) a)) (Eq.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2315))))))
Case conversion may be inaccurate. Consider using '#align one_eq_inv one_eq_invₓ'. -/
@[simp, to_additive]
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  eq_comm.trans inv_eq_one

/- warning: inv_ne_one -> inv_ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α}, Iff (Ne.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) a) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) (Ne.{succ u_1} α a (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2344 : DivisionMonoid.{u_1} α] {a : α}, Iff (Ne.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2344))) a) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2344)))))) (Ne.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2344))))))
Case conversion may be inaccurate. Consider using '#align inv_ne_one inv_ne_oneₓ'. -/
@[to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  inv_eq_one.Not

/- warning: eq_of_one_div_eq_one_div -> eq_of_one_div_eq_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b)) -> (Eq.{succ u_1} α a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2371 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2371))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2371))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2371))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2371))))) b)) -> (Eq.{succ u_1} α a b)
Case conversion may be inaccurate. Consider using '#align eq_of_one_div_eq_one_div eq_of_one_div_eq_one_divₓ'. -/
@[to_additive]
theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by rw [← one_div_one_div a, h, one_div_one_div]

variable (a b c)

/- warning: div_div_eq_mul_div -> div_div_eq_mul_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a c) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2440 : DivisionMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2440))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2440))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2440))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2440))))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_div_eq_mul_div div_div_eq_mul_divₓ'. -/
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp

/- warning: div_inv_eq_mul -> div_inv_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) b)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2467 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2467))) a (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2467))) b)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2467))))) a b)
Case conversion may be inaccurate. Consider using '#align div_inv_eq_mul div_inv_eq_mulₓ'. -/
@[simp, to_additive]
theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp

/- warning: div_mul_eq_div_div_swap -> div_mul_eq_div_div_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a c) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2494 : DivisionMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2494))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2494))))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2494))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2494))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_mul_eq_div_div_swap div_mul_eq_div_div_swapₓ'. -/
@[to_additive]
theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b := by simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]

end DivisionMonoid

theorem bit0_neg [SubtractionMonoid α] (a : α) : bit0 (-a) = -bit0 a :=
  (neg_add_rev _ _).symm

section DivisionCommMonoid

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

/- warning: mul_inv -> mul_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a b)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2540 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2540)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2540)))))) a b)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2540)))))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2540)))) a) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2540)))) b))
Case conversion may be inaccurate. Consider using '#align mul_inv mul_invₓ'. -/
@[to_additive neg_add]
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp

/- warning: inv_div' -> inv_div' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2580 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2580)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2580)))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2580)))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2580)))) a) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2580)))) b))
Case conversion may be inaccurate. Consider using '#align inv_div' inv_div'ₓ'. -/
@[to_additive]
theorem inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹ := by simp

/- warning: div_eq_inv_mul -> div_eq_inv_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2620 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2620)))) a b) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2620)))))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2620)))) b) a)
Case conversion may be inaccurate. Consider using '#align div_eq_inv_mul div_eq_inv_mulₓ'. -/
@[to_additive]
theorem div_eq_inv_mul : a / b = b⁻¹ * a := by simp

/- warning: inv_mul_eq_div -> inv_mul_eq_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2648 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2648)))))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2648)))) a) b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2648)))) b a)
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_div inv_mul_eq_divₓ'. -/
@[to_additive]
theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp

/- warning: inv_mul' -> inv_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2676 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2676)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2676)))))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2676)))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2676)))) a) b)
Case conversion may be inaccurate. Consider using '#align inv_mul' inv_mul'ₓ'. -/
@[to_additive]
theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp

/- warning: inv_div_inv -> inv_div_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2712 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2712)))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2712)))) a) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2712)))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2712)))) b a)
Case conversion may be inaccurate. Consider using '#align inv_div_inv inv_div_invₓ'. -/
@[simp, to_additive]
theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by simp

/- warning: inv_inv_div_inv -> inv_inv_div_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) b))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2744 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2744)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2744)))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2744)))) a) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2744)))) b))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2744)))) a b)
Case conversion may be inaccurate. Consider using '#align inv_inv_div_inv inv_inv_div_invₓ'. -/
@[to_additive]
theorem inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b := by simp

/- warning: one_div_mul_one_div -> one_div_mul_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2784 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2784)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2784)))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2784)))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2784)))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2784)))))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2784)))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2784)))))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2784)))))) a b))
Case conversion may be inaccurate. Consider using '#align one_div_mul_one_div one_div_mul_one_divₓ'. -/
@[to_additive]
theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by simp

/- warning: div_right_comm -> div_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a c) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2814 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2814)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2814)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2814)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2814)))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_right_comm div_right_commₓ'. -/
@[to_additive]
theorem div_right_comm : a / b / c = a / c / b := by simp

/- warning: div_div -> div_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2842 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2842)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2842)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2842)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2842)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_div div_divₓ'. -/
@[to_additive, field_simps]
theorem div_div : a / b / c = a / (b * c) := by simp

/- warning: div_mul -> div_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2870 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2870)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2870)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2870)))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2870)))) b c))
Case conversion may be inaccurate. Consider using '#align div_mul div_mulₓ'. -/
@[to_additive]
theorem div_mul : a / b * c = a / (b / c) := by simp

/- warning: mul_div_left_comm -> mul_div_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b c)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2898 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2898)))))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2898)))) b c)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2898)))))) b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2898)))) a c))
Case conversion may be inaccurate. Consider using '#align mul_div_left_comm mul_div_left_commₓ'. -/
@[to_additive]
theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp

/- warning: mul_div_right_comm -> mul_div_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a c) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2926 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2926)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2926)))))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2926)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2926)))) a c) b)
Case conversion may be inaccurate. Consider using '#align mul_div_right_comm mul_div_right_commₓ'. -/
@[to_additive]
theorem mul_div_right_comm : a * b / c = a / c * b := by simp

/- warning: div_mul_eq_div_div -> div_mul_eq_div_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2954 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2954)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2954)))))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2954)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2954)))) a b) c)
Case conversion may be inaccurate. Consider using '#align div_mul_eq_div_div div_mul_eq_div_divₓ'. -/
@[to_additive]
theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by simp

/- warning: div_mul_eq_mul_div -> div_mul_eq_mul_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a c) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2982 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2982)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2982)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2982)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2982)))))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_mul_eq_mul_div div_mul_eq_mul_divₓ'. -/
@[to_additive, field_simps]
theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp

/- warning: mul_comm_div -> mul_comm_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) c b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3010 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3010)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3010)))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3010)))))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3010)))) c b))
Case conversion may be inaccurate. Consider using '#align mul_comm_div mul_comm_divₓ'. -/
@[to_additive]
theorem mul_comm_div : a / b * c = a * (c / b) := by simp

/- warning: div_mul_comm -> div_mul_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) c b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3038 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3038)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3038)))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3038)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3038)))) c b) a)
Case conversion may be inaccurate. Consider using '#align div_mul_comm div_mul_commₓ'. -/
@[to_additive]
theorem div_mul_comm : a / b * c = c / b * a := by simp

/- warning: div_mul_eq_div_mul_one_div -> div_mul_eq_div_mul_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b c)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3066 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3066)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3066)))))) b c)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3066)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3066)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3066)))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3066)))))) c))
Case conversion may be inaccurate. Consider using '#align div_mul_eq_div_mul_one_div div_mul_eq_div_mul_one_divₓ'. -/
@[to_additive]
theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp

/- warning: div_div_div_eq -> div_div_div_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a d) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3096 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3096)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3096)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3096)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3096)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3096)))))) a d) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3096)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_div_div_eq div_div_div_eqₓ'. -/
@[to_additive]
theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by simp

/- warning: div_div_div_comm -> div_div_div_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b d))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3128 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3128)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3128)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3128)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3128)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3128)))) a c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3128)))) b d))
Case conversion may be inaccurate. Consider using '#align div_div_div_comm div_div_div_commₓ'. -/
@[to_additive]
theorem div_div_div_comm : a / b / (c / d) = a / c / (b / d) := by simp

/- warning: div_mul_div_comm -> div_mul_div_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b d))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3160 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3160)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3160)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3160)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3160)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3160)))))) a c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3160)))))) b d))
Case conversion may be inaccurate. Consider using '#align div_mul_div_comm div_mul_div_commₓ'. -/
@[to_additive]
theorem div_mul_div_comm : a / b * (c / d) = a * c / (b * d) := by simp

/- warning: mul_div_mul_comm -> mul_div_mul_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a b) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) c d)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b d))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3192 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3192)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3192)))))) a b) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3192)))))) c d)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3192)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3192)))) a c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3192)))) b d))
Case conversion may be inaccurate. Consider using '#align mul_div_mul_comm mul_div_mul_commₓ'. -/
@[to_additive]
theorem mul_div_mul_comm : a * b / (c * d) = a / c * (b / d) := by simp

end DivisionCommMonoid

section Group

variable [Group G] {a b c d : G}

/- warning: div_eq_inv_self -> div_eq_inv_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b)) (Eq.{succ u_3} G a (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3242 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3242))) a b) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3242)))) b)) (Eq.{succ u_1} G a (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3242)))))))
Case conversion may be inaccurate. Consider using '#align div_eq_inv_self div_eq_inv_selfₓ'. -/
@[simp, to_additive]
theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_left_eq_self]

/- warning: mul_left_surjective -> mul_left_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G), Function.Surjective.{succ u_3 succ u_3} G G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3301 : Group.{u_1} G] (a : G), Function.surjective.{succ u_1 succ u_1} G G ((fun (a._@.Mathlib.Algebra.Group.Basic._hyg.3315 : G) (a._@.Mathlib.Algebra.Group.Basic._hyg.3316 : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3301))))) a._@.Mathlib.Algebra.Group.Basic._hyg.3315 a._@.Mathlib.Algebra.Group.Basic._hyg.3316) a)
Case conversion may be inaccurate. Consider using '#align mul_left_surjective mul_left_surjectiveₓ'. -/
@[to_additive]
theorem mul_left_surjective (a : G) : Function.Surjective ((· * ·) a) := fun x => ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

/- warning: mul_right_surjective -> mul_right_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G), Function.Surjective.{succ u_3 succ u_3} G G (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) x a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3348 : Group.{u_1} G] (a : G), Function.surjective.{succ u_1 succ u_1} G G (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3348))))) x a)
Case conversion may be inaccurate. Consider using '#align mul_right_surjective mul_right_surjectiveₓ'. -/
@[to_additive]
theorem mul_right_surjective (a : G) : Function.Surjective fun x => x * a := fun x =>
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

/- warning: eq_mul_inv_of_mul_eq -> eq_mul_inv_of_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c) b) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) c)))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3386 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3386))))) a c) b) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3386))))) b (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3386)))) c)))
Case conversion may be inaccurate. Consider using '#align eq_mul_inv_of_mul_eq eq_mul_inv_of_mul_eqₓ'. -/
@[to_additive]
theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ := by simp [h.symm]

/- warning: eq_inv_mul_of_mul_eq -> eq_inv_mul_of_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b a) c) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b) c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3420 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3420))))) b a) c) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3420))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3420)))) b) c))
Case conversion may be inaccurate. Consider using '#align eq_inv_mul_of_mul_eq eq_inv_mul_of_mul_eqₓ'. -/
@[to_additive]
theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c := by simp [h.symm]

/- warning: inv_mul_eq_of_eq_mul -> inv_mul_eq_of_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G b (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c)) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3454 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G b (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3454))))) a c)) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3454))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3454)))) a) b) c)
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_of_eq_mul inv_mul_eq_of_eq_mulₓ'. -/
@[to_additive]
theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c := by simp [h]

/- warning: mul_inv_eq_of_eq_mul -> mul_inv_eq_of_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c b)) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b)) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3487 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3487))))) c b)) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3487))))) a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3487)))) b)) c)
Case conversion may be inaccurate. Consider using '#align mul_inv_eq_of_eq_mul mul_inv_eq_of_eq_mulₓ'. -/
@[to_additive]
theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c := by simp [h]

/- warning: eq_mul_of_mul_inv_eq -> eq_mul_of_mul_inv_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) c)) b) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3520 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3520))))) a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3520)))) c)) b) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3520))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_mul_inv_eq eq_mul_of_mul_inv_eqₓ'. -/
@[to_additive]
theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c := by simp [h.symm]

/- warning: eq_mul_of_inv_mul_eq -> eq_mul_of_inv_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b) a) c) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3554 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3554))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3554)))) b) a) c) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3554))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_inv_mul_eq eq_mul_of_inv_mul_eqₓ'. -/
@[to_additive]
theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by simp [h.symm, mul_inv_cancel_left]

/- warning: mul_eq_of_eq_inv_mul -> mul_eq_of_eq_inv_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G b (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) c)) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3588 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G b (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3588))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3588)))) a) c)) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3588))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_inv_mul mul_eq_of_eq_inv_mulₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by rw [h, mul_inv_cancel_left]

/- warning: mul_eq_of_eq_mul_inv -> mul_eq_of_eq_mul_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b))) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3647 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3647))))) c (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3647)))) b))) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3647))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_mul_inv mul_eq_of_eq_mul_invₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c := by simp [h]

/- warning: mul_eq_one_iff_eq_inv -> mul_eq_one_iff_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Eq.{succ u_3} G a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3680 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3680))))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3680))))))) (Eq.{succ u_1} G a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3680)))) b))
Case conversion may be inaccurate. Consider using '#align mul_eq_one_iff_eq_inv mul_eq_one_iff_eq_invₓ'. -/
@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h => by rw [h, mul_left_inv]⟩

/- warning: mul_eq_one_iff_inv_eq -> mul_eq_one_iff_inv_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Eq.{succ u_3} G (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3746 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3746))))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3746))))))) (Eq.{succ u_1} G (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3746)))) a) b)
Case conversion may be inaccurate. Consider using '#align mul_eq_one_iff_inv_eq mul_eq_one_iff_inv_eqₓ'. -/
@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]

/- warning: eq_inv_iff_mul_eq_one -> eq_inv_iff_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b)) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3806 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3806)))) b)) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3806))))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3806)))))))
Case conversion may be inaccurate. Consider using '#align eq_inv_iff_mul_eq_one eq_inv_iff_mul_eq_oneₓ'. -/
@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm

/- warning: inv_eq_iff_mul_eq_one -> inv_eq_iff_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) b) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3837 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3837)))) a) b) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3837))))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3837)))))))
Case conversion may be inaccurate. Consider using '#align inv_eq_iff_mul_eq_one inv_eq_iff_mul_eq_oneₓ'. -/
@[to_additive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm

/- warning: eq_mul_inv_iff_mul_eq -> eq_mul_inv_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) c))) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3868 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3868))))) b (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3868)))) c))) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3868))))) a c) b)
Case conversion may be inaccurate. Consider using '#align eq_mul_inv_iff_mul_eq eq_mul_inv_iff_mul_eqₓ'. -/
@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

/- warning: eq_inv_mul_iff_mul_eq -> eq_inv_mul_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b) c)) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b a) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3968 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3968))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3968)))) b) c)) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3968))))) b a) c)
Case conversion may be inaccurate. Consider using '#align eq_inv_mul_iff_mul_eq eq_inv_mul_iff_mul_eqₓ'. -/
@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

/- warning: inv_mul_eq_iff_eq_mul -> inv_mul_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) b) c) (Eq.{succ u_3} G b (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4068 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4068))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4068)))) a) b) c) (Eq.{succ u_1} G b (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4068))))) a c))
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_iff_eq_mul inv_mul_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

/- warning: mul_inv_eq_iff_eq_mul -> mul_inv_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b)) c) (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4168 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4168))))) a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4168)))) b)) c) (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4168))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_eq_iff_eq_mul mul_inv_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

/- warning: mul_inv_eq_one -> mul_inv_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b)) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Eq.{succ u_3} G a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4268 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4268))))) a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4268)))) b)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4268))))))) (Eq.{succ u_1} G a b)
Case conversion may be inaccurate. Consider using '#align mul_inv_eq_one mul_inv_eq_oneₓ'. -/
@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]

/- warning: inv_mul_eq_one -> inv_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Eq.{succ u_3} G a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4327 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4327))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4327)))) a) b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4327))))))) (Eq.{succ u_1} G a b)
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_one inv_mul_eq_oneₓ'. -/
@[to_additive]
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]

/- warning: div_left_injective -> div_left_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {b : G}, Function.Injective.{succ u_3 succ u_3} G G (fun (a : G) => HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4386 : Group.{u_1} G] {b : G}, Function.injective.{succ u_1 succ u_1} G G (fun (a : G) => HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4386))) a b)
Case conversion may be inaccurate. Consider using '#align div_left_injective div_left_injectiveₓ'. -/
@[to_additive]
theorem div_left_injective : Function.Injective fun a => a / b := by
  simpa only [div_eq_mul_inv] using fun a a' h => mul_left_injective b⁻¹ h

/- warning: div_right_injective -> div_right_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {b : G}, Function.Injective.{succ u_3 succ u_3} G G (fun (a : G) => HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4422 : Group.{u_1} G] {b : G}, Function.injective.{succ u_1 succ u_1} G G (fun (a : G) => HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4422))) b a)
Case conversion may be inaccurate. Consider using '#align div_right_injective div_right_injectiveₓ'. -/
@[to_additive]
theorem div_right_injective : Function.Injective fun a => b / a := by
  simpa only [div_eq_mul_inv] using fun a a' h => inv_injective (mul_right_injective b h)

/- warning: div_mul_cancel' -> div_mul_cancel' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) b) a
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4458 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4458))))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4458))) a b) b) a
Case conversion may be inaccurate. Consider using '#align div_mul_cancel' div_mul_cancel'ₓ'. -/
@[simp, to_additive sub_add_cancel]
theorem div_mul_cancel' (a b : G) : a / b * b = a := by rw [div_eq_mul_inv, inv_mul_cancel_right a b]

/- warning: div_self' -> div_self' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a a) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4512 : Group.{u_1} G] (a : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4512))) a a) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4512))))))
Case conversion may be inaccurate. Consider using '#align div_self' div_self'ₓ'. -/
@[simp, to_additive sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_right_inv a]

/- warning: mul_div_cancel'' -> mul_div_cancel'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) b) a
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4562 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4562))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4562))))) a b) b) a
Case conversion may be inaccurate. Consider using '#align mul_div_cancel'' mul_div_cancel''ₓ'. -/
@[simp, to_additive add_sub_cancel]
theorem mul_div_cancel'' (a b : G) : a * b / b = a := by rw [div_eq_mul_inv, mul_inv_cancel_right a b]

/- warning: mul_div_mul_right_eq_div -> mul_div_mul_right_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b c)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4616 : Group.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4616))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4616))))) a c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4616))))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4616))) a b)
Case conversion may be inaccurate. Consider using '#align mul_div_mul_right_eq_div mul_div_mul_right_eq_divₓ'. -/
@[simp, to_additive]
theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap] <;> simp only [mul_left_inj, eq_self_iff_true, mul_div_cancel'']

/- warning: eq_div_of_mul_eq' -> eq_div_of_mul_eq' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c) b) -> (Eq.{succ u_3} G a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4685 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4685))))) a c) b) -> (Eq.{succ u_1} G a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4685))) b c))
Case conversion may be inaccurate. Consider using '#align eq_div_of_mul_eq' eq_div_of_mul_eq'ₓ'. -/
@[to_additive eq_sub_of_add_eq]
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]

/- warning: div_eq_of_eq_mul'' -> div_eq_of_eq_mul'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c b)) -> (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4714 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4714))))) c b)) -> (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4714))) a b) c)
Case conversion may be inaccurate. Consider using '#align div_eq_of_eq_mul'' div_eq_of_eq_mul''ₓ'. -/
@[to_additive sub_eq_of_eq_add]
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]

/- warning: eq_mul_of_div_eq -> eq_mul_of_div_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a c) b) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4743 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4743))) a c) b) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4743))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_div_eq eq_mul_of_div_eqₓ'. -/
@[to_additive]
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]

/- warning: mul_eq_of_eq_div -> mul_eq_of_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) c b)) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4772 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4772))) c b)) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4772))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_div mul_eq_of_eq_divₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]

/- warning: div_right_inj -> div_right_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a c)) (Eq.{succ u_3} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4801 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4801))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4801))) a c)) (Eq.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align div_right_inj div_right_injₓ'. -/
@[simp, to_additive]
theorem div_right_inj : a / b = a / c ↔ b = c :=
  div_right_injective.eq_iff

/- warning: div_left_inj -> div_left_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b a) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) c a)) (Eq.{succ u_3} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4830 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4830))) b a) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4830))) c a)) (Eq.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align div_left_inj div_left_injₓ'. -/
@[simp, to_additive]
theorem div_left_inj : b / a = c / a ↔ b = c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_left_inj _

/- warning: div_mul_div_cancel' -> div_mul_div_cancel' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b c)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4894 : Group.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4894))))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4894))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4894))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4894))) a c)
Case conversion may be inaccurate. Consider using '#align div_mul_div_cancel' div_mul_div_cancel'ₓ'. -/
@[simp, to_additive sub_add_sub_cancel]
theorem div_mul_div_cancel' (a b c : G) : a / b * (b / c) = a / c := by rw [← mul_div_assoc, div_mul_cancel']

/- warning: div_div_div_cancel_right' -> div_div_div_cancel_right' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a c) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b c)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4951 : Group.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4951))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4951))) a c) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4951))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4951))) a b)
Case conversion may be inaccurate. Consider using '#align div_div_div_cancel_right' div_div_div_cancel_right'ₓ'. -/
@[simp, to_additive sub_sub_sub_cancel_right]
theorem div_div_div_cancel_right' (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel']

/- warning: div_eq_one -> div_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Eq.{succ u_3} G a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5011 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5011))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5011))))))) (Eq.{succ u_1} G a b)
Case conversion may be inaccurate. Consider using '#align div_eq_one div_eq_oneₓ'. -/
@[to_additive]
theorem div_eq_one : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun h => by rw [h, div_self']⟩

alias div_eq_one ↔ _ div_eq_one_of_eq

alias sub_eq_zero ↔ _ sub_eq_zero_of_eq

/- warning: div_ne_one -> div_ne_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Ne.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Ne.{succ u_3} G a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5075 : Group.{u_1} G] {a : G} {b : G}, Iff (Ne.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5075))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5075))))))) (Ne.{succ u_1} G a b)
Case conversion may be inaccurate. Consider using '#align div_ne_one div_ne_oneₓ'. -/
@[to_additive]
theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b :=
  not_congr div_eq_one

/- warning: div_eq_self -> div_eq_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) a) (Eq.{succ u_3} G b (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5105 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5105))) a b) a) (Eq.{succ u_1} G b (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5105)))))))
Case conversion may be inaccurate. Consider using '#align div_eq_self div_eq_selfₓ'. -/
@[simp, to_additive]
theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_right_eq_self, inv_eq_one]

/- warning: eq_div_iff_mul_eq' -> eq_div_iff_mul_eq' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b c)) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5161 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5161))) b c)) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5161))))) a c) b)
Case conversion may be inaccurate. Consider using '#align eq_div_iff_mul_eq' eq_div_iff_mul_eq'ₓ'. -/
@[to_additive eq_sub_iff_add_eq]
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

/- warning: div_eq_iff_eq_mul -> div_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) c) (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5218 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5218))) a b) c) (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5218))))) c b))
Case conversion may be inaccurate. Consider using '#align div_eq_iff_eq_mul div_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]

/- warning: eq_iff_eq_of_div_eq_div -> eq_iff_eq_of_div_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G} {d : G}, (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) c d)) -> (Iff (Eq.{succ u_3} G a b) (Eq.{succ u_3} G c d))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5275 : Group.{u_1} G] {a : G} {b : G} {c : G} {d : G}, (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5275))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5275))) c d)) -> (Iff (Eq.{succ u_1} G a b) (Eq.{succ u_1} G c d))
Case conversion may be inaccurate. Consider using '#align eq_iff_eq_of_div_eq_div eq_iff_eq_of_div_eq_divₓ'. -/
@[to_additive]
theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d := by rw [← div_eq_one, H, div_eq_one]

/- warning: left_inverse_div_mul_left -> left_inverse_div_mul_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (c : G), Function.LeftInverse.{succ u_3 succ u_3} G G (fun (x : G) => HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) x c) (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) x c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5338 : Group.{u_1} G] (c : G), Function.LeftInverse.{succ u_1 succ u_1} G G (fun (x : G) => HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5338))) x c) (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5338))))) x c)
Case conversion may be inaccurate. Consider using '#align left_inverse_div_mul_left left_inverse_div_mul_leftₓ'. -/
@[to_additive]
theorem left_inverse_div_mul_left (c : G) : Function.LeftInverse (fun x => x / c) fun x => x * c := fun x =>
  mul_div_cancel'' x c

/- warning: left_inverse_mul_left_div -> left_inverse_mul_left_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (c : G), Function.LeftInverse.{succ u_3 succ u_3} G G (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) x c) (fun (x : G) => HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) x c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5375 : Group.{u_1} G] (c : G), Function.LeftInverse.{succ u_1 succ u_1} G G (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5375))))) x c) (fun (x : G) => HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5375))) x c)
Case conversion may be inaccurate. Consider using '#align left_inverse_mul_left_div left_inverse_mul_left_divₓ'. -/
@[to_additive]
theorem left_inverse_mul_left_div (c : G) : Function.LeftInverse (fun x => x * c) fun x => x / c := fun x =>
  div_mul_cancel' x c

/- warning: left_inverse_mul_right_inv_mul -> left_inverse_mul_right_inv_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (c : G), Function.LeftInverse.{succ u_3 succ u_3} G G (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c x) (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) c) x)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5412 : Group.{u_1} G] (c : G), Function.LeftInverse.{succ u_1 succ u_1} G G (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5412))))) c x) (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5412))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5412)))) c) x)
Case conversion may be inaccurate. Consider using '#align left_inverse_mul_right_inv_mul left_inverse_mul_right_inv_mulₓ'. -/
@[to_additive]
theorem left_inverse_mul_right_inv_mul (c : G) : Function.LeftInverse (fun x => c * x) fun x => c⁻¹ * x := fun x =>
  mul_inv_cancel_left c x

/- warning: left_inverse_inv_mul_mul_right -> left_inverse_inv_mul_mul_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (c : G), Function.LeftInverse.{succ u_3 succ u_3} G G (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) c) x) (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c x)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5453 : Group.{u_1} G] (c : G), Function.LeftInverse.{succ u_1 succ u_1} G G (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5453))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5453)))) c) x) (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5453))))) c x)
Case conversion may be inaccurate. Consider using '#align left_inverse_inv_mul_mul_right left_inverse_inv_mul_mul_rightₓ'. -/
@[to_additive]
theorem left_inverse_inv_mul_mul_right (c : G) : Function.LeftInverse (fun x => c⁻¹ * x) fun x => c * x := fun x =>
  inv_mul_cancel_left c x

/- warning: exists_npow_eq_one_of_zpow_eq_one -> exists_npow_eq_one_of_zpow_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {n : Int}, (Ne.{1} Int n (Zero.zero.{0} Int Int.hasZero)) -> (forall {x : G}, (Eq.{succ u_3} G (HPow.hPow.{u_3 0 u_3} G Int G (instHPow.{u_3 0} G Int (DivInvMonoid.hasPow.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) x n) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) -> (Exists.{1} Nat (fun (n : Nat) => And (LT.lt.{0} Nat Nat.hasLt (Zero.zero.{0} Nat Nat.hasZero) n) (Eq.{succ u_3} G (HPow.hPow.{u_3 0 u_3} G Nat G (instHPow.{u_3 0} G Nat (Monoid.hasPow.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))) x n) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5494 : Group.{u_1} G] {n : Int}, (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (forall {x : G}, (Eq.{succ u_1} G (HPow.hPow.{u_1 0 u_1} G Int G (instHPow.{u_1 0} G Int (DivInvMonoid.hasPow.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5494))) x n) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5494))))))) -> (Exists.{1} Nat (fun (n : Nat) => And (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (Eq.{succ u_1} G (HPow.hPow.{u_1 0 u_1} G Nat G (instHPow.{u_1 0} G Nat (Monoid.Pow.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5494)))) x n) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5494))))))))))
Case conversion may be inaccurate. Consider using '#align exists_npow_eq_one_of_zpow_eq_one exists_npow_eq_one_of_zpow_eq_oneₓ'. -/
@[to_additive]
theorem exists_npow_eq_one_of_zpow_eq_one {n : ℤ} (hn : n ≠ 0) {x : G} (h : x ^ n = 1) : ∃ n : ℕ, 0 < n ∧ x ^ n = 1 :=
  by
  cases' n with n n
  · rw [zpow_of_nat] at h
    refine' ⟨n, Nat.pos_of_ne_zero fun n0 => hn _, h⟩
    rw [n0]
    rfl
    
  · rw [zpow_neg_succ_of_nat, inv_eq_one] at h
    refine' ⟨n + 1, n.succ_pos, h⟩
    

end Group

section CommGroup

variable [CommGroup G] {a b c d : G}

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

/- warning: div_eq_of_eq_mul' -> div_eq_of_eq_mul' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b c)) -> (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5700 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5700)))))) b c)) -> (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5700)))) a b) c)
Case conversion may be inaccurate. Consider using '#align div_eq_of_eq_mul' div_eq_of_eq_mul'ₓ'. -/
@[to_additive]
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]

/- warning: mul_div_mul_left_eq_div -> mul_div_mul_left_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) c a) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) c b)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5760 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5760)))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5760)))))) c a) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5760)))))) c b)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5760)))) a b)
Case conversion may be inaccurate. Consider using '#align mul_div_mul_left_eq_div mul_div_mul_left_eq_divₓ'. -/
@[simp, to_additive]
theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by simp

/- warning: eq_div_of_mul_eq'' -> eq_div_of_mul_eq'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) c a) b) -> (Eq.{succ u_3} G a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5835 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5835)))))) c a) b) -> (Eq.{succ u_1} G a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5835)))) b c))
Case conversion may be inaccurate. Consider using '#align eq_div_of_mul_eq'' eq_div_of_mul_eq''ₓ'. -/
@[to_additive eq_sub_of_add_eq']
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]

/- warning: eq_mul_of_div_eq' -> eq_mul_of_div_eq' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) c) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5865 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5865)))) a b) c) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5865)))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_div_eq' eq_mul_of_div_eq'ₓ'. -/
@[to_additive]
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]

/- warning: mul_eq_of_eq_div' -> mul_eq_of_eq_div' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G b (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c a)) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5895 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G b (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5895)))) c a)) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5895)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_div' mul_eq_of_eq_div'ₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  simp [h]
  rw [mul_comm c, mul_inv_cancel_left]

/- warning: div_div_self' -> div_div_self' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b)) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5952 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5952)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5952)))) a b)) b
Case conversion may be inaccurate. Consider using '#align div_div_self' div_div_self'ₓ'. -/
@[to_additive sub_sub_self]
theorem div_div_self' (a b : G) : a / (a / b) = b := by simpa using mul_inv_cancel_left a b

/- warning: div_eq_div_mul_div -> div_eq_div_mul_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6006 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6006)))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6006)))))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6006)))) c b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6006)))) a c))
Case conversion may be inaccurate. Consider using '#align div_eq_div_mul_div div_eq_div_mul_divₓ'. -/
@[to_additive]
theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]

/- warning: div_div_cancel -> div_div_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b)) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6039 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6039)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6039)))) a b)) b
Case conversion may be inaccurate. Consider using '#align div_div_cancel div_div_cancelₓ'. -/
@[simp, to_additive]
theorem div_div_cancel (a b : G) : a / (a / b) = b :=
  div_div_self' a b

/- warning: div_div_cancel_left -> div_div_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) a) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1))) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6064 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6064)))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6064)))) a b) a) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (DivisionCommMonoid.toDivisionMonoid.{u_1} G (CommGroup.toDivisionCommMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6064))))) b)
Case conversion may be inaccurate. Consider using '#align div_div_cancel_left div_div_cancel_leftₓ'. -/
@[simp, to_additive]
theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp

/- warning: eq_div_iff_mul_eq'' -> eq_div_iff_mul_eq'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b c)) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) c a) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6094 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6094)))) b c)) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6094)))))) c a) b)
Case conversion may be inaccurate. Consider using '#align eq_div_iff_mul_eq'' eq_div_iff_mul_eq''ₓ'. -/
@[to_additive eq_sub_iff_add_eq']
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]

/- warning: div_eq_iff_eq_mul' -> div_eq_iff_eq_mul' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) c) (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6151 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6151)))) a b) c) (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6151)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_eq_iff_eq_mul' div_eq_iff_eq_mul'ₓ'. -/
@[to_additive]
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]

/- warning: mul_div_cancel''' -> mul_div_cancel''' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b) a) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6208 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6208)))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6208)))))) a b) a) b
Case conversion may be inaccurate. Consider using '#align mul_div_cancel''' mul_div_cancel'''ₓ'. -/
@[simp, to_additive add_sub_cancel']
theorem mul_div_cancel''' (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]

/- warning: mul_div_cancel'_right -> mul_div_cancel'_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b a)) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6260 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6260)))))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6260)))) b a)) b
Case conversion may be inaccurate. Consider using '#align mul_div_cancel'_right mul_div_cancel'_rightₓ'. -/
@[simp, to_additive]
theorem mul_div_cancel'_right (a b : G) : a * (b / a) = b := by rw [← mul_div_assoc, mul_div_cancel''']

/- warning: div_mul_cancel'' -> div_mul_cancel'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b)) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1))) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6312 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6312)))) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6312)))))) a b)) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (DivisionCommMonoid.toDivisionMonoid.{u_1} G (CommGroup.toDivisionCommMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6312))))) b)
Case conversion may be inaccurate. Consider using '#align div_mul_cancel'' div_mul_cancel''ₓ'. -/
@[simp, to_additive sub_add_cancel']
theorem div_mul_cancel'' (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel''']

/- warning: mul_mul_inv_cancel'_right -> mul_mul_inv_cancel'_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1))) a))) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6368 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6368)))))) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6368)))))) b (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (DivisionCommMonoid.toDivisionMonoid.{u_1} G (CommGroup.toDivisionCommMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6368))))) a))) b
Case conversion may be inaccurate. Consider using '#align mul_mul_inv_cancel'_right mul_mul_inv_cancel'_rightₓ'. -/
-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined  in `algebra/group/commute`
@[to_additive]
theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by rw [← div_eq_mul_inv, mul_div_cancel'_right a b]

/- warning: mul_mul_div_cancel -> mul_mul_div_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a c) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b c)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6426 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6426)))))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6426)))))) a c) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6426)))) b c)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6426)))))) a b)
Case conversion may be inaccurate. Consider using '#align mul_mul_div_cancel mul_mul_div_cancelₓ'. -/
@[simp, to_additive]
theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by rw [mul_assoc, mul_div_cancel'_right]

/- warning: div_mul_mul_cancel -> div_mul_mul_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b c)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6483 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6483)))))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6483)))) a c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6483)))))) b c)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6483)))))) a b)
Case conversion may be inaccurate. Consider using '#align div_mul_mul_cancel div_mul_mul_cancelₓ'. -/
@[simp, to_additive]
theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by rw [mul_left_comm, div_mul_cancel', mul_comm]

/- warning: div_mul_div_cancel'' -> div_mul_div_cancel'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c a)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6541 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6541)))))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6541)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6541)))) c a)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6541)))) c b)
Case conversion may be inaccurate. Consider using '#align div_mul_div_cancel'' div_mul_div_cancel''ₓ'. -/
@[simp, to_additive sub_add_sub_cancel']
theorem div_mul_div_cancel'' (a b c : G) : a / b * (c / a) = c / b := by rw [mul_comm] <;> apply div_mul_div_cancel'

/- warning: mul_div_div_cancel -> mul_div_div_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a c)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6610 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6610)))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6610)))))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6610)))) a c)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6610)))))) b c)
Case conversion may be inaccurate. Consider using '#align mul_div_div_cancel mul_div_div_cancelₓ'. -/
@[simp, to_additive]
theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by rw [← div_mul, mul_div_cancel''']

/- warning: div_div_div_cancel_left -> div_div_div_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c a) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c b)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6667 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6667)))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6667)))) c a) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6667)))) c b)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6667)))) b a)
Case conversion may be inaccurate. Consider using '#align div_div_div_cancel_left div_div_div_cancel_leftₓ'. -/
@[simp, to_additive]
theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c, div_inv_eq_mul, mul_comm, div_mul_div_cancel']

/- warning: div_eq_div_iff_mul_eq_mul -> div_eq_div_iff_mul_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c d)) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a d) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) c b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6728 : CommGroup.{u_1} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6728)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6728)))) c d)) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6728)))))) a d) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6728)))))) c b))
Case conversion may be inaccurate. Consider using '#align div_eq_div_iff_mul_eq_mul div_eq_div_iff_mul_eq_mulₓ'. -/
@[to_additive]
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]

/- warning: div_eq_div_iff_div_eq_div -> div_eq_div_iff_div_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c d)) (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a c) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b d))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6801 : CommGroup.{u_1} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6801)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6801)))) c d)) (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6801)))) a c) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6801)))) b d))
Case conversion may be inaccurate. Consider using '#align div_eq_div_iff_div_eq_div div_eq_div_iff_div_eq_divₓ'. -/
@[to_additive]
theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]

end CommGroup

section SubtractionCommMonoid

variable {M : Type u} [SubtractionCommMonoid M]

theorem bit0_sub (a b : M) : bit0 (a - b) = bit0 a - bit0 b :=
  sub_add_sub_comm _ _ _ _

theorem bit1_sub [One M] (a b : M) : bit1 (a - b) = bit1 a - bit0 b :=
  (congr_arg (· + (1 : M)) <| bit0_sub a b : _).trans <| sub_add_eq_add_sub _ _ _

end SubtractionCommMonoid

