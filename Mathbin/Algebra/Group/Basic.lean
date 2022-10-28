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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.17 : Semigroup.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (α -> α) (Function.comp.{succ u_1 succ u_1 succ u_1} α α α (fun (x._@.Mathlib.Algebra.Group.Basic._hyg.32 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.17)) x x._@.Mathlib.Algebra.Group.Basic._hyg.32) (fun (x._@.Mathlib.Algebra.Group.Basic._hyg.44 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.17)) y x._@.Mathlib.Algebra.Group.Basic._hyg.44)) (fun (x._@.Mathlib.Algebra.Group.Basic._hyg.56 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.17)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.17)) x y) x._@.Mathlib.Algebra.Group.Basic._hyg.56)
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.129 : Semigroup.{u_1} α] (x : α) (y : α), Eq.{succ u_1} (α -> α) (Function.comp.{succ u_1 succ u_1 succ u_1} α α α (fun (x._@.Mathlib.Algebra.Group.Basic._hyg.144 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.129)) x._@.Mathlib.Algebra.Group.Basic._hyg.144 x) (fun (x._@.Mathlib.Algebra.Group.Basic._hyg.156 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.129)) x._@.Mathlib.Algebra.Group.Basic._hyg.156 y)) (fun (x._@.Mathlib.Algebra.Group.Basic._hyg.168 : α) => HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.129)) x._@.Mathlib.Algebra.Group.Basic._hyg.168 (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.129)) y x))
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
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.254 : MulOneClass.{u} M] {P : Prop} [inst._@.Mathlib.Algebra.Group.Basic._hyg.258 : Decidable P] {a : M} {b : M}, Eq.{succ u} M (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.258 (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.254)) a b) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.254)))) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.254)) (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.258 a (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.254)))) (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.258 b (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.254)))))
Case conversion may be inaccurate. Consider using '#align ite_mul_one ite_mul_oneₓ'. -/
@[to_additive]
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} : ite P (a * b) 1 = ite P a 1 * ite P b 1 := by
  by_cases h:P <;> simp [h]

/- warning: ite_one_mul -> ite_one_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M] {P : Prop} [_inst_2 : Decidable P] {a : M} {b : M}, Eq.{succ u} M (ite.{succ u} M P _inst_2 (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1)) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) a b)) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) (ite.{succ u} M P _inst_2 (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1)) a) (ite.{succ u} M P _inst_2 (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1)) b))
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.330 : MulOneClass.{u} M] {P : Prop} [inst._@.Mathlib.Algebra.Group.Basic._hyg.334 : Decidable P] {a : M} {b : M}, Eq.{succ u} M (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.334 (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.330))) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.330)) a b)) (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.330)) (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.334 (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.330))) a) (ite.{succ u} M P inst._@.Mathlib.Algebra.Group.Basic._hyg.334 (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.330))) b))
Case conversion may be inaccurate. Consider using '#align ite_one_mul ite_one_mulₓ'. -/
@[to_additive]
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} : ite P 1 (a * b) = ite P 1 a * ite P 1 b := by
  by_cases h:P <;> simp [h]

/- warning: eq_one_iff_eq_one_of_mul_eq_one -> eq_one_iff_eq_one_of_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M] {a : M} {b : M}, (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) a b) (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))) -> (Iff (Eq.{succ u} M a (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))) (Eq.{succ u} M b (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))))
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.406 : MulOneClass.{u} M] {a : M} {b : M}, (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.406)) a b) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.406)))) -> (Iff (Eq.{succ u} M a (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.406)))) (Eq.{succ u} M b (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.406)))))
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
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.515 : MulOneClass.{u} M], Eq.{succ u} (M -> M) ((fun (x._@.Mathlib.Algebra.Group.Basic._hyg.525 : M) (x._@.Mathlib.Algebra.Group.Basic._hyg.527 : M) => HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.515)) x._@.Mathlib.Algebra.Group.Basic._hyg.525 x._@.Mathlib.Algebra.Group.Basic._hyg.527) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.515)))) (id.{succ u} M)
Case conversion may be inaccurate. Consider using '#align one_mul_eq_id one_mul_eq_idₓ'. -/
@[to_additive]
theorem one_mul_eq_id : (· * ·) (1 : M) = id :=
  funext one_mul

/- warning: mul_one_eq_id -> mul_one_eq_id is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M], Eq.{succ u} (M -> M) (fun (_x : M) => HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M _inst_1)) _x (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))) (id.{succ u} M)
but is expected to have type
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.549 : MulOneClass.{u} M], Eq.{succ u} (M -> M) (fun (x._@.Mathlib.Algebra.Group.Basic._hyg.558 : M) => HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.549)) x._@.Mathlib.Algebra.Group.Basic._hyg.558 (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (MulOneClass.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.549)))) (id.{succ u} M)
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
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.588 : CommSemigroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.588))) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.588))) b c)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.588))) b (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.588))) a c))
Case conversion may be inaccurate. Consider using '#align mul_left_comm mul_left_commₓ'. -/
@[no_rsimp, to_additive]
theorem mul_left_comm : ∀ a b c : G, a * (b * c) = b * (a * c) :=
  left_comm Mul.mul mul_comm mul_assoc

/- warning: mul_right_comm -> mul_right_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommSemigroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a b) c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a c) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.619 : CommSemigroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.619))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.619))) a b) c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.619))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.619))) a c) b)
Case conversion may be inaccurate. Consider using '#align mul_right_comm mul_right_commₓ'. -/
@[to_additive]
theorem mul_right_comm : ∀ a b c : G, a * b * c = a * c * b :=
  right_comm Mul.mul mul_comm mul_assoc

/- warning: mul_mul_mul_comm -> mul_mul_mul_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommSemigroup.{u_3} G] (a : G) (b : G) (c : G) (d : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a b) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) c d)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) b d))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.650 : CommSemigroup.{u_1} G] (a : G) (b : G) (c : G) (d : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.650))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.650))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.650))) c d)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.650))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.650))) a c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.650))) b d))
Case conversion may be inaccurate. Consider using '#align mul_mul_mul_comm mul_mul_mul_commₓ'. -/
@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by simp only [mul_left_comm, mul_assoc]

/- warning: mul_rotate -> mul_rotate is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommSemigroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a b) c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) b c) a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.682 : CommSemigroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.682))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.682))) a b) c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.682))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.682))) b c) a)
Case conversion may be inaccurate. Consider using '#align mul_rotate mul_rotateₓ'. -/
@[to_additive]
theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by simp only [mul_left_comm, mul_comm]

/- warning: mul_rotate' -> mul_rotate' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommSemigroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) b c)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) b (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (Semigroup.toHasMul.{u_3} G (CommSemigroup.toSemigroup.{u_3} G _inst_1))) c a))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.709 : CommSemigroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.709))) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.709))) b c)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.709))) b (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (Semigroup.toMul.{u_1} G (CommSemigroup.toSemigroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.709))) c a))
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
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.756 : CommMonoid.{u} M] {x : M} {y : M} {z : M}, (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (CommMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.756)))) x y) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (Monoid.toOne.{u} M (CommMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.756))))) -> (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (CommMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.756)))) x z) (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (Monoid.toOne.{u} M (CommMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.756))))) -> (Eq.{succ u} M y z)
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
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.813 : LeftCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (LeftCancelMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.813)))) a b) a) (Eq.{succ u} M b (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (LeftCancelMonoid.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.813))))
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
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.898 : LeftCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M a (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (LeftCancelMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.898)))) a b)) (Eq.{succ u} M b (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (LeftCancelMonoid.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.898))))
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
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.941 : RightCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (RightCancelMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.941)))) a b) b) (Eq.{succ u} M a (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (RightCancelMonoid.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.941))))
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
  forall {M : Type.{u}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1026 : RightCancelMonoid.{u} M] {a : M} {b : M}, Iff (Eq.{succ u} M b (HMul.hMul.{u u u} M M M (instHMul.{u} M (MulOneClass.toMul.{u} M (Monoid.toMulOneClass.{u} M (RightCancelMonoid.toMonoid.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.1026)))) a b)) (Eq.{succ u} M a (OfNat.ofNat.{u} M 1 (One.toOfNat1.{u} M (RightCancelMonoid.toOne.{u} M inst._@.Mathlib.Algebra.Group.Basic._hyg.1026))))
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
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1066 : HasInvolutiveInv.{u_1} G], Function.Involutive.{succ u_1} G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1066))
Case conversion may be inaccurate. Consider using '#align inv_involutive inv_involutiveₓ'. -/
@[simp, to_additive]
theorem inv_involutive : Function.Involutive (Inv.inv : G → G) :=
  inv_inv

/- warning: inv_surjective -> inv_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G], Function.Surjective.{succ u_3 succ u_3} G G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1083 : HasInvolutiveInv.{u_1} G], Function.Surjective.{succ u_1 succ u_1} G G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1083))
Case conversion may be inaccurate. Consider using '#align inv_surjective inv_surjectiveₓ'. -/
@[simp, to_additive]
theorem inv_surjective : Function.Surjective (Inv.inv : G → G) :=
  inv_involutive.Surjective

/- warning: inv_injective -> inv_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G], Function.Injective.{succ u_3 succ u_3} G G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1100 : HasInvolutiveInv.{u_1} G], Function.Injective.{succ u_1 succ u_1} G G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1100))
Case conversion may be inaccurate. Consider using '#align inv_injective inv_injectiveₓ'. -/
@[to_additive]
theorem inv_injective : Function.Injective (Inv.inv : G → G) :=
  inv_involutive.Injective

/- warning: inv_inj -> inv_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a) (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) b)) (Eq.{succ u_3} G a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1117 : HasInvolutiveInv.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1117) a) (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1117) b)) (Eq.{succ u_1} G a b)
Case conversion may be inaccurate. Consider using '#align inv_inj inv_injₓ'. -/
@[simp, to_additive]
theorem inv_inj {a b : G} : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff

/- warning: eq_inv_of_eq_inv -> eq_inv_of_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G] {a : G} {b : G}, (Eq.{succ u_3} G a (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) b)) -> (Eq.{succ u_3} G b (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1150 : HasInvolutiveInv.{u_1} G] {a : G} {b : G}, (Eq.{succ u_1} G a (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1150) b)) -> (Eq.{succ u_1} G b (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1150) a))
Case conversion may be inaccurate. Consider using '#align eq_inv_of_eq_inv eq_inv_of_eq_invₓ'. -/
@[to_additive]
theorem eq_inv_of_eq_inv (h : a = b⁻¹) : b = a⁻¹ := by simp [h]

/- warning: eq_inv_iff_eq_inv -> eq_inv_iff_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G a (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) b)) (Eq.{succ u_3} G b (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1181 : HasInvolutiveInv.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G a (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1181) b)) (Eq.{succ u_1} G b (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1181) a))
Case conversion may be inaccurate. Consider using '#align eq_inv_iff_eq_inv eq_inv_iff_eq_invₓ'. -/
@[to_additive]
theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
  ⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩

/- warning: inv_eq_iff_inv_eq -> inv_eq_iff_inv_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : HasInvolutiveInv.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a) b) (Eq.{succ u_3} G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) b) a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1215 : HasInvolutiveInv.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1215) a) b) (Eq.{succ u_1} G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1215) b) a)
Case conversion may be inaccurate. Consider using '#align inv_eq_iff_inv_eq inv_eq_iff_inv_eqₓ'. -/
@[to_additive]
theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
  eq_comm.trans <| eq_inv_iff_eq_inv.trans eq_comm

variable (G)

/- warning: inv_comp_inv -> inv_comp_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u_3}) [_inst_1 : HasInvolutiveInv.{u_3} G], Eq.{succ u_3} (G -> G) (Function.comp.{succ u_3 succ u_3 succ u_3} G G G (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1)) (Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1))) (id.{succ u_3} G)
but is expected to have type
  forall (G : Type.{u_1}) [inst._@.Mathlib.Algebra.Group.Basic._hyg.1260 : HasInvolutiveInv.{u_1} G], Eq.{succ u_1} (G -> G) (Function.comp.{succ u_1 succ u_1 succ u_1} G G G (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1260)) (Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1260))) (id.{succ u_1} G)
Case conversion may be inaccurate. Consider using '#align inv_comp_inv inv_comp_invₓ'. -/
@[simp, to_additive]
theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  inv_involutive.comp_self

/- warning: left_inverse_inv -> left_inverse_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u_3}) [_inst_1 : HasInvolutiveInv.{u_3} G], Function.LeftInverse.{succ u_3 succ u_3} G G (fun (a : G) => Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a) (fun (a : G) => Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a)
but is expected to have type
  forall (G : Type.{u_1}) [inst._@.Mathlib.Algebra.Group.Basic._hyg.1281 : HasInvolutiveInv.{u_1} G], Function.LeftInverse.{succ u_1 succ u_1} G G (fun (a : G) => Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1281) a) (fun (a : G) => Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1281) a)
Case conversion may be inaccurate. Consider using '#align left_inverse_inv left_inverse_invₓ'. -/
@[to_additive]
theorem left_inverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv

/- warning: right_inverse_inv -> right_inverse_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u_3}) [_inst_1 : HasInvolutiveInv.{u_3} G], Function.LeftInverse.{succ u_3 succ u_3} G G (fun (a : G) => Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a) (fun (a : G) => Inv.inv.{u_3} G (HasInvolutiveInv.toHasInv.{u_3} G _inst_1) a)
but is expected to have type
  forall (G : Type.{u_1}) [inst._@.Mathlib.Algebra.Group.Basic._hyg.1310 : HasInvolutiveInv.{u_1} G], Function.LeftInverse.{succ u_1 succ u_1} G G (fun (a : G) => Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1310) a) (fun (a : G) => Inv.inv.{u_1} G (HasInvolutiveInv.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1310) a)
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
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1355 : DivInvMonoid.{u_1} G] (x : G), Eq.{succ u_1} G (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1355) x) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1355)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1355)))) x)
Case conversion may be inaccurate. Consider using '#align inv_eq_one_div inv_eq_one_divₓ'. -/
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]

/- warning: mul_one_div -> mul_one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (x : G) (y : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) x (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) y)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) x y)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1407 : DivInvMonoid.{u_1} G] (x : G) (y : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1407)))) x (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1407)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1407)))) y)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1407)) x y)
Case conversion may be inaccurate. Consider using '#align mul_one_div mul_one_divₓ'. -/
@[to_additive]
theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

/- warning: mul_div_assoc -> mul_div_assoc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a b) c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1461 : DivInvMonoid.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1461)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1461)))) a b) c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1461)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1461)) b c))
Case conversion may be inaccurate. Consider using '#align mul_div_assoc mul_div_assocₓ'. -/
@[to_additive]
theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]

/- warning: mul_div_assoc' -> mul_div_assoc' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) b c)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1521 : DivInvMonoid.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1521)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1521)) b c)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1521)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1521)))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_div_assoc' mul_div_assoc'ₓ'. -/
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c :=
  (mul_div_assoc _ _ _).symm

/- warning: one_div -> one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (a : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G _inst_1) a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1554 : DivInvMonoid.{u_1} G] (a : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1554)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1554)))) a) (Inv.inv.{u_1} G (DivInvMonoid.toInv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1554) a)
Case conversion may be inaccurate. Consider using '#align one_div one_divₓ'. -/
@[simp, to_additive]
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm

/- warning: mul_div -> mul_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) b c)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1581 : DivInvMonoid.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1581)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1581)) b c)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1581)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1581)))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_div mul_divₓ'. -/
@[to_additive]
theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]

/- warning: div_eq_mul_one_div -> div_eq_mul_one_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvMonoid.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) a b) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G _inst_1)) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G _inst_1)))) b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1611 : DivInvMonoid.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1611)) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1611)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1611)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (Monoid.toOne.{u_1} G (DivInvMonoid.toMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1611)))) b))
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
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1674 : DivInvOneMonoid.{u_1} G] (a : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (DivInvOneMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1674))) a (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1674))))) a
Case conversion may be inaccurate. Consider using '#align div_one div_oneₓ'. -/
@[simp, to_additive]
theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]

/- warning: one_div_one -> one_div_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : DivInvOneMonoid.{u_3} G], Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (DivInvOneMonoid.toDivInvMonoid.{u_3} G _inst_1))) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (DivInvOneMonoid.toDivInvMonoid.{u_3} G _inst_1))))) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (DivInvOneMonoid.toDivInvMonoid.{u_3} G _inst_1)))))) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (DivInvOneMonoid.toDivInvMonoid.{u_3} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1693 : DivInvOneMonoid.{u_1} G], Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (DivInvOneMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1693))) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1693)))) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1693))))) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.1693))))
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1730 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1730))))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1730)))))) -> (Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1730)) b) a)
Case conversion may be inaccurate. Consider using '#align inv_eq_of_mul_eq_one_left inv_eq_of_mul_eq_one_leftₓ'. -/
@[to_additive]
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by rw [← inv_eq_of_mul_eq_one_right h, inv_inv]

/- warning: eq_inv_of_mul_eq_one_left -> eq_inv_of_mul_eq_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α a (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1787 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1787))))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1787)))))) -> (Eq.{succ u_1} α a (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1787)) b))
Case conversion may be inaccurate. Consider using '#align eq_inv_of_mul_eq_one_left eq_inv_of_mul_eq_one_leftₓ'. -/
@[to_additive]
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm

/- warning: eq_inv_of_mul_eq_one_right -> eq_inv_of_mul_eq_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α b (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1818 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1818))))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1818)))))) -> (Eq.{succ u_1} α b (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1818)) a))
Case conversion may be inaccurate. Consider using '#align eq_inv_of_mul_eq_one_right eq_inv_of_mul_eq_one_rightₓ'. -/
@[to_additive]
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm

/- warning: eq_one_div_of_mul_eq_one_left -> eq_one_div_of_mul_eq_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b a) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1849 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1849))))) b a) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1849)))))) -> (Eq.{succ u_1} α b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1849))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1849))))) a))
Case conversion may be inaccurate. Consider using '#align eq_one_div_of_mul_eq_one_left eq_one_div_of_mul_eq_one_leftₓ'. -/
@[to_additive]
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by rw [eq_inv_of_mul_eq_one_left h, one_div]

/- warning: eq_one_div_of_mul_eq_one_right -> eq_one_div_of_mul_eq_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1904 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1904))))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1904)))))) -> (Eq.{succ u_1} α b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1904))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1904))))) a))
Case conversion may be inaccurate. Consider using '#align eq_one_div_of_mul_eq_one_right eq_one_div_of_mul_eq_one_rightₓ'. -/
@[to_additive]
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by rw [eq_inv_of_mul_eq_one_right h, one_div]

/- warning: eq_of_div_eq_one -> eq_of_div_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) -> (Eq.{succ u_1} α a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.1959 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1959))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.1959)))))) -> (Eq.{succ u_1} α a b)
Case conversion may be inaccurate. Consider using '#align eq_of_div_eq_one eq_of_div_eq_oneₓ'. -/
@[to_additive]
theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
  inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]

/- warning: div_ne_one_of_ne -> div_ne_one_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Ne.{succ u_1} α a b) -> (Ne.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a b) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2024 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Ne.{succ u_1} α a b) -> (Ne.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2024))) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2024))))))
Case conversion may be inaccurate. Consider using '#align div_ne_one_of_ne div_ne_one_of_neₓ'. -/
@[to_additive]
theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 :=
  mt eq_of_div_eq_one

variable (a b c)

/- warning: one_div_mul_one_div_rev -> one_div_mul_one_div_rev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2064 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2064))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2064))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2064))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2064))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2064))))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2064))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2064))))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2064))))) b a))
Case conversion may be inaccurate. Consider using '#align one_div_mul_one_div_rev one_div_mul_one_div_revₓ'. -/
@[to_additive]
theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp

/- warning: inv_div_left -> inv_div_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) a) b) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2093 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2093))) (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2093)) a) b) (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2093)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2093))))) b a))
Case conversion may be inaccurate. Consider using '#align inv_div_left inv_div_leftₓ'. -/
@[to_additive]
theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp

/- warning: inv_div -> inv_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2128 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2128)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2128))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2128))) b a)
Case conversion may be inaccurate. Consider using '#align inv_div inv_divₓ'. -/
@[simp, to_additive]
theorem inv_div : (a / b)⁻¹ = b / a := by simp

/- warning: one_div_div -> one_div_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2159 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2159))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2159))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2159))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2159))) b a)
Case conversion may be inaccurate. Consider using '#align one_div_div one_div_divₓ'. -/
@[simp, to_additive]
theorem one_div_div : 1 / (a / b) = b / a := by simp

/- warning: one_div_one_div -> one_div_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a)) a
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2184 : DivisionMonoid.{u_1} α] (a : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2184))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2184))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2184))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2184))))) a)) a
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2295 : DivisionMonoid.{u_1} α] {a : α}, Iff (Eq.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2295))) a) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2295)))))) (Eq.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2295))))))
Case conversion may be inaccurate. Consider using '#align inv_eq_one inv_eq_oneₓ'. -/
@[simp, to_additive]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  inv_injective.eq_iff' inv_one

/- warning: one_eq_inv -> one_eq_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α}, Iff (Eq.{succ u_1} α (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) a)) (Eq.{succ u_1} α a (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2324 : DivisionMonoid.{u_1} α] {a : α}, Iff (Eq.{succ u_1} α (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2324))))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2324))) a)) (Eq.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2324))))))
Case conversion may be inaccurate. Consider using '#align one_eq_inv one_eq_invₓ'. -/
@[simp, to_additive]
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  eq_comm.trans inv_eq_one

/- warning: inv_ne_one -> inv_ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α}, Iff (Ne.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) a) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)))))) (Ne.{succ u_1} α a (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2353 : DivisionMonoid.{u_1} α] {a : α}, Iff (Ne.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2353))) a) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2353)))))) (Ne.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2353))))))
Case conversion may be inaccurate. Consider using '#align inv_ne_one inv_ne_oneₓ'. -/
@[to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  inv_eq_one.Not

/- warning: eq_of_one_div_eq_one_div -> eq_of_one_div_eq_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b)) -> (Eq.{succ u_1} α a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2380 : DivisionMonoid.{u_1} α] {a : α} {b : α}, (Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2380))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2380))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2380))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2380))))) b)) -> (Eq.{succ u_1} α a b)
Case conversion may be inaccurate. Consider using '#align eq_of_one_div_eq_one_div eq_of_one_div_eq_one_divₓ'. -/
@[to_additive]
theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by rw [← one_div_one_div a, h, one_div_one_div]

variable (a b c)

/- warning: div_div_eq_mul_div -> div_div_eq_mul_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a c) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2449 : DivisionMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2449))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2449))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2449))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2449))))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_div_eq_mul_div div_div_eq_mul_divₓ'. -/
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp

/- warning: div_inv_eq_mul -> div_inv_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1)) b)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2476 : DivisionMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2476))) a (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2476))) b)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2476))))) a b)
Case conversion may be inaccurate. Consider using '#align div_inv_eq_mul div_inv_eq_mulₓ'. -/
@[simp, to_additive]
theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp

/- warning: div_mul_eq_div_div_swap -> div_mul_eq_div_div_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α _inst_1))) a c) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2503 : DivisionMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2503))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2503))))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2503))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2503))) a c) b)
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2549 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2549)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2549)))))) a b)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2549)))))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2549)))) a) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2549)))) b))
Case conversion may be inaccurate. Consider using '#align mul_inv mul_invₓ'. -/
@[to_additive neg_add]
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp

/- warning: inv_div' -> inv_div' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2589 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2589)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2589)))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2589)))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2589)))) a) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2589)))) b))
Case conversion may be inaccurate. Consider using '#align inv_div' inv_div'ₓ'. -/
@[to_additive]
theorem inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹ := by simp

/- warning: div_eq_inv_mul -> div_eq_inv_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2629 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2629)))) a b) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2629)))))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2629)))) b) a)
Case conversion may be inaccurate. Consider using '#align div_eq_inv_mul div_eq_inv_mulₓ'. -/
@[to_additive]
theorem div_eq_inv_mul : a / b = b⁻¹ * a := by simp

/- warning: inv_mul_eq_div -> inv_mul_eq_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2657 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2657)))))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2657)))) a) b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2657)))) b a)
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_div inv_mul_eq_divₓ'. -/
@[to_additive]
theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp

/- warning: inv_mul' -> inv_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2685 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2685)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2685)))))) a b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2685)))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2685)))) a) b)
Case conversion may be inaccurate. Consider using '#align inv_mul' inv_mul'ₓ'. -/
@[to_additive]
theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp

/- warning: inv_div_inv -> inv_div_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2721 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2721)))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2721)))) a) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2721)))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2721)))) b a)
Case conversion may be inaccurate. Consider using '#align inv_div_inv inv_div_invₓ'. -/
@[simp, to_additive]
theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by simp

/- warning: inv_inv_div_inv -> inv_inv_div_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) a) (Inv.inv.{u_1} α (DivInvMonoid.toHasInv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1))) b))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2753 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2753)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2753)))) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2753)))) a) (Inv.inv.{u_1} α (InvOneClass.toInv.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2753)))) b))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2753)))) a b)
Case conversion may be inaccurate. Consider using '#align inv_inv_div_inv inv_inv_div_invₓ'. -/
@[to_additive]
theorem inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b := by simp

/- warning: one_div_mul_one_div -> one_div_mul_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2793 : DivisionCommMonoid.{u_1} α] (a : α) (b : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2793)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2793)))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2793)))))) a) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2793)))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2793)))))) b)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2793)))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2793)))))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2793)))))) a b))
Case conversion may be inaccurate. Consider using '#align one_div_mul_one_div one_div_mul_one_divₓ'. -/
@[to_additive]
theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by simp

/- warning: div_right_comm -> div_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a c) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2823 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2823)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2823)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2823)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2823)))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_right_comm div_right_commₓ'. -/
@[to_additive]
theorem div_right_comm : a / b / c = a / c / b := by simp

/- warning: div_div -> div_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2851 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2851)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2851)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2851)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2851)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_div div_divₓ'. -/
@[to_additive, field_simps]
theorem div_div : a / b / c = a / (b * c) := by simp

/- warning: div_mul -> div_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2879 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2879)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2879)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2879)))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2879)))) b c))
Case conversion may be inaccurate. Consider using '#align div_mul div_mulₓ'. -/
@[to_additive]
theorem div_mul : a / b * c = a / (b / c) := by simp

/- warning: mul_div_left_comm -> mul_div_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b c)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2907 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2907)))))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2907)))) b c)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2907)))))) b (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2907)))) a c))
Case conversion may be inaccurate. Consider using '#align mul_div_left_comm mul_div_left_commₓ'. -/
@[to_additive]
theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp

/- warning: mul_div_right_comm -> mul_div_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a c) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2935 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2935)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2935)))))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2935)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2935)))) a c) b)
Case conversion may be inaccurate. Consider using '#align mul_div_right_comm mul_div_right_commₓ'. -/
@[to_additive]
theorem mul_div_right_comm : a * b / c = a / c * b := by simp

/- warning: div_mul_eq_div_div -> div_mul_eq_div_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2963 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2963)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2963)))))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2963)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2963)))) a b) c)
Case conversion may be inaccurate. Consider using '#align div_mul_eq_div_div div_mul_eq_div_divₓ'. -/
@[to_additive]
theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by simp

/- warning: div_mul_eq_mul_div -> div_mul_eq_mul_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a c) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.2991 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2991)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2991)))) a b) c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2991)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.2991)))))) a c) b)
Case conversion may be inaccurate. Consider using '#align div_mul_eq_mul_div div_mul_eq_mul_divₓ'. -/
@[to_additive, field_simps]
theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp

/- warning: mul_comm_div -> mul_comm_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) c b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3019 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3019)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3019)))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3019)))))) a (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3019)))) c b))
Case conversion may be inaccurate. Consider using '#align mul_comm_div mul_comm_divₓ'. -/
@[to_additive]
theorem mul_comm_div : a / b * c = a * (c / b) := by simp

/- warning: div_mul_comm -> div_mul_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) c b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3047 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3047)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3047)))) a b) c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3047)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3047)))) c b) a)
Case conversion may be inaccurate. Consider using '#align div_mul_comm div_mul_commₓ'. -/
@[to_additive]
theorem div_mul_comm : a / b * c = c / b * a := by simp

/- warning: div_mul_eq_div_mul_one_div -> div_mul_eq_div_mul_one_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b c)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3075 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3075)))) a (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3075)))))) b c)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3075)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3075)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3075)))) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (InvOneClass.toOne.{u_1} α (DivInvOneMonoid.toInvOneClass.{u_1} α (DivisionMonoid.toDivInvOneMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3075)))))) c))
Case conversion may be inaccurate. Consider using '#align div_mul_eq_div_mul_one_div div_mul_eq_div_mul_one_divₓ'. -/
@[to_additive]
theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp

/- warning: div_div_div_eq -> div_div_div_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a d) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3105 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3105)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3105)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3105)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3105)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3105)))))) a d) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3105)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_div_div_eq div_div_div_eqₓ'. -/
@[to_additive]
theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by simp

/- warning: div_div_div_comm -> div_div_div_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b d))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3137 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3137)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3137)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3137)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3137)))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3137)))) a c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3137)))) b d))
Case conversion may be inaccurate. Consider using '#align div_div_div_comm div_div_div_commₓ'. -/
@[to_additive]
theorem div_div_div_comm : a / b / (c / d) = a / c / (b / d) := by simp

/- warning: div_mul_div_comm -> div_mul_div_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) b d))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3169 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3169)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3169)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3169)))) c d)) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3169)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3169)))))) a c) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3169)))))) b d))
Case conversion may be inaccurate. Consider using '#align div_mul_div_comm div_mul_div_commₓ'. -/
@[to_additive]
theorem div_mul_div_comm : a / b * (c / d) = a * c / (b * d) := by simp

/- warning: mul_div_mul_comm -> mul_div_mul_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) a b) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) c d)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) a c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toHasDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α _inst_1)))) b d))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3201 : DivisionCommMonoid.{u_1} α] (a : α) (b : α) (c : α) (d : α), Eq.{succ u_1} α (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3201)))) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3201)))))) a b) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3201)))))) c d)) (HMul.hMul.{u_1 u_1 u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (DivInvMonoid.toMonoid.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3201)))))) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3201)))) a c) (HDiv.hDiv.{u_1 u_1 u_1} α α α (instHDiv.{u_1} α (DivInvMonoid.toDiv.{u_1} α (DivisionMonoid.toDivInvMonoid.{u_1} α (DivisionCommMonoid.toDivisionMonoid.{u_1} α inst._@.Mathlib.Algebra.Group.Basic._hyg.3201)))) b d))
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
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3251 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3251))) a b) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3251)))) b)) (Eq.{succ u_1} G a (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3251)))))))
Case conversion may be inaccurate. Consider using '#align div_eq_inv_self div_eq_inv_selfₓ'. -/
@[simp, to_additive]
theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_left_eq_self]

/- warning: mul_left_surjective -> mul_left_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G), Function.Surjective.{succ u_3 succ u_3} G G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3310 : Group.{u_1} G] (a : G), Function.Surjective.{succ u_1 succ u_1} G G ((fun (x._@.Mathlib.Algebra.Group.Basic._hyg.3325 : G) (x._@.Mathlib.Algebra.Group.Basic._hyg.3327 : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3310))))) x._@.Mathlib.Algebra.Group.Basic._hyg.3325 x._@.Mathlib.Algebra.Group.Basic._hyg.3327) a)
Case conversion may be inaccurate. Consider using '#align mul_left_surjective mul_left_surjectiveₓ'. -/
@[to_additive]
theorem mul_left_surjective (a : G) : Function.Surjective ((· * ·) a) := fun x => ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

/- warning: mul_right_surjective -> mul_right_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G), Function.Surjective.{succ u_3 succ u_3} G G (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) x a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3359 : Group.{u_1} G] (a : G), Function.Surjective.{succ u_1 succ u_1} G G (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3359))))) x a)
Case conversion may be inaccurate. Consider using '#align mul_right_surjective mul_right_surjectiveₓ'. -/
@[to_additive]
theorem mul_right_surjective (a : G) : Function.Surjective fun x => x * a := fun x =>
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

/- warning: eq_mul_inv_of_mul_eq -> eq_mul_inv_of_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c) b) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) c)))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3397 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3397))))) a c) b) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3397))))) b (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3397)))) c)))
Case conversion may be inaccurate. Consider using '#align eq_mul_inv_of_mul_eq eq_mul_inv_of_mul_eqₓ'. -/
@[to_additive]
theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ := by simp [h.symm]

/- warning: eq_inv_mul_of_mul_eq -> eq_inv_mul_of_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b a) c) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b) c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3431 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3431))))) b a) c) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3431))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3431)))) b) c))
Case conversion may be inaccurate. Consider using '#align eq_inv_mul_of_mul_eq eq_inv_mul_of_mul_eqₓ'. -/
@[to_additive]
theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c := by simp [h.symm]

/- warning: inv_mul_eq_of_eq_mul -> inv_mul_eq_of_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G b (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c)) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3465 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G b (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3465))))) a c)) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3465))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3465)))) a) b) c)
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_of_eq_mul inv_mul_eq_of_eq_mulₓ'. -/
@[to_additive]
theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c := by simp [h]

/- warning: mul_inv_eq_of_eq_mul -> mul_inv_eq_of_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c b)) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b)) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3498 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3498))))) c b)) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3498))))) a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3498)))) b)) c)
Case conversion may be inaccurate. Consider using '#align mul_inv_eq_of_eq_mul mul_inv_eq_of_eq_mulₓ'. -/
@[to_additive]
theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c := by simp [h]

/- warning: eq_mul_of_mul_inv_eq -> eq_mul_of_mul_inv_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) c)) b) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3531 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3531))))) a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3531)))) c)) b) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3531))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_mul_inv_eq eq_mul_of_mul_inv_eqₓ'. -/
@[to_additive]
theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c := by simp [h.symm]

/- warning: eq_mul_of_inv_mul_eq -> eq_mul_of_inv_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b) a) c) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3565 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3565))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3565)))) b) a) c) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3565))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_inv_mul_eq eq_mul_of_inv_mul_eqₓ'. -/
@[to_additive]
theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by simp [h.symm, mul_inv_cancel_left]

/- warning: mul_eq_of_eq_inv_mul -> mul_eq_of_eq_inv_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G b (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) c)) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3599 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G b (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3599))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3599)))) a) c)) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3599))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_inv_mul mul_eq_of_eq_inv_mulₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by rw [h, mul_inv_cancel_left]

/- warning: mul_eq_of_eq_mul_inv -> mul_eq_of_eq_mul_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b))) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3658 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3658))))) c (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3658)))) b))) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3658))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_mul_inv mul_eq_of_eq_mul_invₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c := by simp [h]

/- warning: mul_eq_one_iff_eq_inv -> mul_eq_one_iff_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Eq.{succ u_3} G a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3691 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3691))))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3691))))))) (Eq.{succ u_1} G a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3691)))) b))
Case conversion may be inaccurate. Consider using '#align mul_eq_one_iff_eq_inv mul_eq_one_iff_eq_invₓ'. -/
@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h => by rw [h, mul_left_inv]⟩

/- warning: mul_eq_one_iff_inv_eq -> mul_eq_one_iff_inv_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Eq.{succ u_3} G (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3757 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3757))))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3757))))))) (Eq.{succ u_1} G (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3757)))) a) b)
Case conversion may be inaccurate. Consider using '#align mul_eq_one_iff_inv_eq mul_eq_one_iff_inv_eqₓ'. -/
@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]

/- warning: eq_inv_iff_mul_eq_one -> eq_inv_iff_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b)) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3817 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3817)))) b)) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3817))))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3817)))))))
Case conversion may be inaccurate. Consider using '#align eq_inv_iff_mul_eq_one eq_inv_iff_mul_eq_oneₓ'. -/
@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm

/- warning: inv_eq_iff_mul_eq_one -> inv_eq_iff_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) b) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3848 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3848)))) a) b) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3848))))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3848)))))))
Case conversion may be inaccurate. Consider using '#align inv_eq_iff_mul_eq_one inv_eq_iff_mul_eq_oneₓ'. -/
@[to_additive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm

/- warning: eq_mul_inv_iff_mul_eq -> eq_mul_inv_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) c))) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3879 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3879))))) b (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3879)))) c))) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3879))))) a c) b)
Case conversion may be inaccurate. Consider using '#align eq_mul_inv_iff_mul_eq eq_mul_inv_iff_mul_eqₓ'. -/
@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

/- warning: eq_inv_mul_iff_mul_eq -> eq_inv_mul_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b) c)) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b a) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.3979 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3979))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3979)))) b) c)) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.3979))))) b a) c)
Case conversion may be inaccurate. Consider using '#align eq_inv_mul_iff_mul_eq eq_inv_mul_iff_mul_eqₓ'. -/
@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

/- warning: inv_mul_eq_iff_eq_mul -> inv_mul_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) b) c) (Eq.{succ u_3} G b (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4079 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4079))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4079)))) a) b) c) (Eq.{succ u_1} G b (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4079))))) a c))
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_iff_eq_mul inv_mul_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩

/- warning: mul_inv_eq_iff_eq_mul -> mul_inv_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b)) c) (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4179 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4179))))) a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4179)))) b)) c) (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4179))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inv_eq_iff_eq_mul mul_inv_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

/- warning: mul_inv_eq_one -> mul_inv_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) b)) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Eq.{succ u_3} G a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4279 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4279))))) a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4279)))) b)) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4279))))))) (Eq.{succ u_1} G a b)
Case conversion may be inaccurate. Consider using '#align mul_inv_eq_one mul_inv_eq_oneₓ'. -/
@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]

/- warning: inv_mul_eq_one -> inv_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) a) b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Eq.{succ u_3} G a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4338 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4338))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4338)))) a) b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4338))))))) (Eq.{succ u_1} G a b)
Case conversion may be inaccurate. Consider using '#align inv_mul_eq_one inv_mul_eq_oneₓ'. -/
@[to_additive]
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]

/- warning: div_left_injective -> div_left_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {b : G}, Function.Injective.{succ u_3 succ u_3} G G (fun (a : G) => HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4397 : Group.{u_1} G] {b : G}, Function.Injective.{succ u_1 succ u_1} G G (fun (a : G) => HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4397))) a b)
Case conversion may be inaccurate. Consider using '#align div_left_injective div_left_injectiveₓ'. -/
@[to_additive]
theorem div_left_injective : Function.Injective fun a => a / b := by
  simpa only [div_eq_mul_inv] using fun a a' h => mul_left_injective b⁻¹ h

/- warning: div_right_injective -> div_right_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {b : G}, Function.Injective.{succ u_3 succ u_3} G G (fun (a : G) => HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4433 : Group.{u_1} G] {b : G}, Function.Injective.{succ u_1 succ u_1} G G (fun (a : G) => HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4433))) b a)
Case conversion may be inaccurate. Consider using '#align div_right_injective div_right_injectiveₓ'. -/
@[to_additive]
theorem div_right_injective : Function.Injective fun a => b / a := by
  simpa only [div_eq_mul_inv] using fun a a' h => inv_injective (mul_right_injective b h)

/- warning: div_mul_cancel' -> div_mul_cancel' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) b) a
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4469 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4469))))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4469))) a b) b) a
Case conversion may be inaccurate. Consider using '#align div_mul_cancel' div_mul_cancel'ₓ'. -/
@[simp, to_additive sub_add_cancel]
theorem div_mul_cancel' (a b : G) : a / b * b = a := by rw [div_eq_mul_inv, inv_mul_cancel_right a b]

/- warning: div_self' -> div_self' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a a) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4523 : Group.{u_1} G] (a : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4523))) a a) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4523))))))
Case conversion may be inaccurate. Consider using '#align div_self' div_self'ₓ'. -/
@[simp, to_additive sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_right_inv a]

/- warning: mul_div_cancel'' -> mul_div_cancel'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) b) a
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4573 : Group.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4573))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4573))))) a b) b) a
Case conversion may be inaccurate. Consider using '#align mul_div_cancel'' mul_div_cancel''ₓ'. -/
@[simp, to_additive add_sub_cancel]
theorem mul_div_cancel'' (a b : G) : a * b / b = a := by rw [div_eq_mul_inv, mul_inv_cancel_right a b]

/- warning: mul_div_mul_right_eq_div -> mul_div_mul_right_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b c)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4627 : Group.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4627))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4627))))) a c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4627))))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4627))) a b)
Case conversion may be inaccurate. Consider using '#align mul_div_mul_right_eq_div mul_div_mul_right_eq_divₓ'. -/
@[simp, to_additive]
theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap] <;> simp only [mul_left_inj, eq_self_iff_true, mul_div_cancel'']

/- warning: eq_div_of_mul_eq' -> eq_div_of_mul_eq' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c) b) -> (Eq.{succ u_3} G a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4696 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4696))))) a c) b) -> (Eq.{succ u_1} G a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4696))) b c))
Case conversion may be inaccurate. Consider using '#align eq_div_of_mul_eq' eq_div_of_mul_eq'ₓ'. -/
@[to_additive eq_sub_of_add_eq]
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]

/- warning: div_eq_of_eq_mul'' -> div_eq_of_eq_mul'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c b)) -> (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4725 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4725))))) c b)) -> (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4725))) a b) c)
Case conversion may be inaccurate. Consider using '#align div_eq_of_eq_mul'' div_eq_of_eq_mul''ₓ'. -/
@[to_additive sub_eq_of_eq_add]
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]

/- warning: eq_mul_of_div_eq -> eq_mul_of_div_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a c) b) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4754 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4754))) a c) b) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4754))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_div_eq eq_mul_of_div_eqₓ'. -/
@[to_additive]
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]

/- warning: mul_eq_of_eq_div -> mul_eq_of_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) c b)) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4783 : Group.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4783))) c b)) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4783))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_div mul_eq_of_eq_divₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]

/- warning: div_right_inj -> div_right_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a c)) (Eq.{succ u_3} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4812 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4812))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4812))) a c)) (Eq.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align div_right_inj div_right_injₓ'. -/
@[simp, to_additive]
theorem div_right_inj : a / b = a / c ↔ b = c :=
  div_right_injective.eq_iff

/- warning: div_left_inj -> div_left_inj is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b a) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) c a)) (Eq.{succ u_3} G b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4841 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4841))) b a) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4841))) c a)) (Eq.{succ u_1} G b c)
Case conversion may be inaccurate. Consider using '#align div_left_inj div_left_injₓ'. -/
@[simp, to_additive]
theorem div_left_inj : b / a = c / a ↔ b = c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_left_inj _

/- warning: div_mul_div_cancel' -> div_mul_div_cancel' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b c)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4905 : Group.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4905))))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4905))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4905))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4905))) a c)
Case conversion may be inaccurate. Consider using '#align div_mul_div_cancel' div_mul_div_cancel'ₓ'. -/
@[simp, to_additive sub_add_sub_cancel]
theorem div_mul_div_cancel' (a b c : G) : a / b * (b / c) = a / c := by rw [← mul_div_assoc, div_mul_cancel']

/- warning: div_div_div_cancel_right' -> div_div_div_cancel_right' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a c) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b c)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.4962 : Group.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4962))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4962))) a c) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4962))) b c)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.4962))) a b)
Case conversion may be inaccurate. Consider using '#align div_div_div_cancel_right' div_div_div_cancel_right'ₓ'. -/
@[simp, to_additive sub_sub_sub_cancel_right]
theorem div_div_div_cancel_right' (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel']

/- warning: div_eq_one -> div_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) (Eq.{succ u_3} G a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5022 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5022))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5022))))))) (Eq.{succ u_1} G a b)
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
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5086 : Group.{u_1} G] {a : G} {b : G}, Iff (Ne.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5086))) a b) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5086))))))) (Ne.{succ u_1} G a b)
Case conversion may be inaccurate. Consider using '#align div_ne_one div_ne_oneₓ'. -/
@[to_additive]
theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b :=
  not_congr div_eq_one

/- warning: div_eq_self -> div_eq_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) a) (Eq.{succ u_3} G b (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5116 : Group.{u_1} G] {a : G} {b : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5116))) a b) a) (Eq.{succ u_1} G b (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5116)))))))
Case conversion may be inaccurate. Consider using '#align div_eq_self div_eq_selfₓ'. -/
@[simp, to_additive]
theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_right_eq_self, inv_eq_one]

/- warning: eq_div_iff_mul_eq' -> eq_div_iff_mul_eq' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) b c)) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) a c) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5172 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5172))) b c)) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5172))))) a c) b)
Case conversion may be inaccurate. Consider using '#align eq_div_iff_mul_eq' eq_div_iff_mul_eq'ₓ'. -/
@[to_additive eq_sub_iff_add_eq]
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

/- warning: div_eq_iff_eq_mul -> div_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) c) (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5229 : Group.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5229))) a b) c) (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5229))))) c b))
Case conversion may be inaccurate. Consider using '#align div_eq_iff_eq_mul div_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]

/- warning: eq_iff_eq_of_div_eq_div -> eq_iff_eq_of_div_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {a : G} {b : G} {c : G} {d : G}, (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) c d)) -> (Iff (Eq.{succ u_3} G a b) (Eq.{succ u_3} G c d))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5286 : Group.{u_1} G] {a : G} {b : G} {c : G} {d : G}, (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5286))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5286))) c d)) -> (Iff (Eq.{succ u_1} G a b) (Eq.{succ u_1} G c d))
Case conversion may be inaccurate. Consider using '#align eq_iff_eq_of_div_eq_div eq_iff_eq_of_div_eq_divₓ'. -/
@[to_additive]
theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d := by rw [← div_eq_one, H, div_eq_one]

/- warning: left_inverse_div_mul_left -> left_inverse_div_mul_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (c : G), Function.LeftInverse.{succ u_3 succ u_3} G G (fun (x : G) => HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) x c) (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) x c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5349 : Group.{u_1} G] (c : G), Function.LeftInverse.{succ u_1 succ u_1} G G (fun (x : G) => HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5349))) x c) (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5349))))) x c)
Case conversion may be inaccurate. Consider using '#align left_inverse_div_mul_left left_inverse_div_mul_leftₓ'. -/
@[to_additive]
theorem left_inverse_div_mul_left (c : G) : Function.LeftInverse (fun x => x / c) fun x => x * c := fun x =>
  mul_div_cancel'' x c

/- warning: left_inverse_mul_left_div -> left_inverse_mul_left_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (c : G), Function.LeftInverse.{succ u_3 succ u_3} G G (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) x c) (fun (x : G) => HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) x c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5386 : Group.{u_1} G] (c : G), Function.LeftInverse.{succ u_1 succ u_1} G G (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5386))))) x c) (fun (x : G) => HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5386))) x c)
Case conversion may be inaccurate. Consider using '#align left_inverse_mul_left_div left_inverse_mul_left_divₓ'. -/
@[to_additive]
theorem left_inverse_mul_left_div (c : G) : Function.LeftInverse (fun x => x * c) fun x => x / c := fun x =>
  div_mul_cancel' x c

/- warning: left_inverse_mul_right_inv_mul -> left_inverse_mul_right_inv_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (c : G), Function.LeftInverse.{succ u_3 succ u_3} G G (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c x) (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) c) x)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5423 : Group.{u_1} G] (c : G), Function.LeftInverse.{succ u_1 succ u_1} G G (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5423))))) c x) (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5423))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5423)))) c) x)
Case conversion may be inaccurate. Consider using '#align left_inverse_mul_right_inv_mul left_inverse_mul_right_inv_mulₓ'. -/
@[to_additive]
theorem left_inverse_mul_right_inv_mul (c : G) : Function.LeftInverse (fun x => c * x) fun x => c⁻¹ * x := fun x =>
  mul_inv_cancel_left c x

/- warning: left_inverse_inv_mul_mul_right -> left_inverse_inv_mul_mul_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] (c : G), Function.LeftInverse.{succ u_3 succ u_3} G G (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)) c) x) (fun (x : G) => HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))))) c x)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5464 : Group.{u_1} G] (c : G), Function.LeftInverse.{succ u_1 succ u_1} G G (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5464))))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5464)))) c) x) (fun (x : G) => HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5464))))) c x)
Case conversion may be inaccurate. Consider using '#align left_inverse_inv_mul_mul_right left_inverse_inv_mul_mul_rightₓ'. -/
@[to_additive]
theorem left_inverse_inv_mul_mul_right (c : G) : Function.LeftInverse (fun x => c⁻¹ * x) fun x => c * x := fun x =>
  inv_mul_cancel_left c x

/- warning: exists_npow_eq_one_of_zpow_eq_one -> exists_npow_eq_one_of_zpow_eq_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : Group.{u_3} G] {n : Int}, (Ne.{1} Int n (Zero.zero.{0} Int Int.hasZero)) -> (forall {x : G}, (Eq.{succ u_3} G (HPow.hPow.{u_3 0 u_3} G Int G (instHPow.{u_3 0} G Int (DivInvMonoid.hasPow.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1))) x n) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))) -> (Exists.{1} Nat (fun (n : Nat) => And (LT.lt.{0} Nat Nat.hasLt (Zero.zero.{0} Nat Nat.hasZero) n) (Eq.{succ u_3} G (HPow.hPow.{u_3 0 u_3} G Nat G (instHPow.{u_3 0} G Nat (Monoid.hasPow.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))) x n) (One.one.{u_3} G (MulOneClass.toHasOne.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G _inst_1)))))))))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5505 : Group.{u_1} G] {n : Int}, (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (forall {x : G}, (Eq.{succ u_1} G (HPow.hPow.{u_1 0 u_1} G Int G (instHPow.{u_1 0} G Int (DivInvMonoid.hasPow.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5505))) x n) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5505))))))) -> (Exists.{1} Nat (fun (n : Nat) => And (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (Eq.{succ u_1} G (HPow.hPow.{u_1 0 u_1} G Nat G (instHPow.{u_1 0} G Nat (Monoid.Pow.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5505)))) x n) (OfNat.ofNat.{u_1} G 1 (One.toOfNat1.{u_1} G (InvOneClass.toOne.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5505))))))))))
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
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5711 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5711)))))) b c)) -> (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5711)))) a b) c)
Case conversion may be inaccurate. Consider using '#align div_eq_of_eq_mul' div_eq_of_eq_mul'ₓ'. -/
@[to_additive]
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]

/- warning: mul_div_mul_left_eq_div -> mul_div_mul_left_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) c a) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) c b)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5771 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5771)))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5771)))))) c a) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5771)))))) c b)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5771)))) a b)
Case conversion may be inaccurate. Consider using '#align mul_div_mul_left_eq_div mul_div_mul_left_eq_divₓ'. -/
@[simp, to_additive]
theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by simp

/- warning: eq_div_of_mul_eq'' -> eq_div_of_mul_eq'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) c a) b) -> (Eq.{succ u_3} G a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5846 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5846)))))) c a) b) -> (Eq.{succ u_1} G a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5846)))) b c))
Case conversion may be inaccurate. Consider using '#align eq_div_of_mul_eq'' eq_div_of_mul_eq''ₓ'. -/
@[to_additive eq_sub_of_add_eq']
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]

/- warning: eq_mul_of_div_eq' -> eq_mul_of_div_eq' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) c) -> (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5876 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5876)))) a b) c) -> (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5876)))))) b c))
Case conversion may be inaccurate. Consider using '#align eq_mul_of_div_eq' eq_mul_of_div_eq'ₓ'. -/
@[to_additive]
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]

/- warning: mul_eq_of_eq_div' -> mul_eq_of_eq_div' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, (Eq.{succ u_3} G b (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c a)) -> (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b) c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5906 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, (Eq.{succ u_1} G b (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5906)))) c a)) -> (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5906)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_eq_of_eq_div' mul_eq_of_eq_div'ₓ'. -/
@[to_additive]
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  simp [h]
  rw [mul_comm c, mul_inv_cancel_left]

/- warning: div_div_self' -> div_div_self' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b)) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.5963 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5963)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.5963)))) a b)) b
Case conversion may be inaccurate. Consider using '#align div_div_self' div_div_self'ₓ'. -/
@[to_additive sub_sub_self]
theorem div_div_self' (a b : G) : a / (a / b) = b := by simpa using mul_inv_cancel_left a b

/- warning: div_eq_div_mul_div -> div_eq_div_mul_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6017 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6017)))) a b) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6017)))))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6017)))) c b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6017)))) a c))
Case conversion may be inaccurate. Consider using '#align div_eq_div_mul_div div_eq_div_mul_divₓ'. -/
@[to_additive]
theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]

/- warning: div_div_cancel -> div_div_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b)) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6050 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6050)))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6050)))) a b)) b
Case conversion may be inaccurate. Consider using '#align div_div_cancel div_div_cancelₓ'. -/
@[simp, to_additive]
theorem div_div_cancel (a b : G) : a / (a / b) = b :=
  div_div_self' a b

/- warning: div_div_cancel_left -> div_div_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) a) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1))) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6075 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6075)))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6075)))) a b) a) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (DivisionCommMonoid.toDivisionMonoid.{u_1} G (CommGroup.toDivisionCommMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6075))))) b)
Case conversion may be inaccurate. Consider using '#align div_div_cancel_left div_div_cancel_leftₓ'. -/
@[simp, to_additive]
theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp

/- warning: eq_div_iff_mul_eq'' -> eq_div_iff_mul_eq'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b c)) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) c a) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6105 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6105)))) b c)) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6105)))))) c a) b)
Case conversion may be inaccurate. Consider using '#align eq_div_iff_mul_eq'' eq_div_iff_mul_eq''ₓ'. -/
@[to_additive eq_sub_iff_add_eq']
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]

/- warning: div_eq_iff_eq_mul' -> div_eq_iff_eq_mul' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) c) (Eq.{succ u_3} G a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b c))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6162 : CommGroup.{u_1} G] {a : G} {b : G} {c : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6162)))) a b) c) (Eq.{succ u_1} G a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6162)))))) b c))
Case conversion may be inaccurate. Consider using '#align div_eq_iff_eq_mul' div_eq_iff_eq_mul'ₓ'. -/
@[to_additive]
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]

/- warning: mul_div_cancel''' -> mul_div_cancel''' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b) a) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6219 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6219)))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6219)))))) a b) a) b
Case conversion may be inaccurate. Consider using '#align mul_div_cancel''' mul_div_cancel'''ₓ'. -/
@[simp, to_additive add_sub_cancel']
theorem mul_div_cancel''' (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]

/- warning: mul_div_cancel'_right -> mul_div_cancel'_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b a)) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6271 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6271)))))) a (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6271)))) b a)) b
Case conversion may be inaccurate. Consider using '#align mul_div_cancel'_right mul_div_cancel'_rightₓ'. -/
@[simp, to_additive]
theorem mul_div_cancel'_right (a b : G) : a * (b / a) = b := by rw [← mul_div_assoc, mul_div_cancel''']

/- warning: div_mul_cancel'' -> div_mul_cancel'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b)) (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1))) b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6323 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6323)))) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6323)))))) a b)) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (DivisionCommMonoid.toDivisionMonoid.{u_1} G (CommGroup.toDivisionCommMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6323))))) b)
Case conversion may be inaccurate. Consider using '#align div_mul_cancel'' div_mul_cancel''ₓ'. -/
@[simp, to_additive sub_add_cancel']
theorem div_mul_cancel'' (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel''']

/- warning: mul_mul_inv_cancel'_right -> mul_mul_inv_cancel'_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b (Inv.inv.{u_3} G (DivInvMonoid.toHasInv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1))) a))) b
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6379 : CommGroup.{u_1} G] (a : G) (b : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6379)))))) a (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6379)))))) b (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (DivisionCommMonoid.toDivisionMonoid.{u_1} G (CommGroup.toDivisionCommMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6379))))) a))) b
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
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6437 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6437)))))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6437)))))) a c) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6437)))) b c)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6437)))))) a b)
Case conversion may be inaccurate. Consider using '#align mul_mul_div_cancel mul_mul_div_cancelₓ'. -/
@[simp, to_additive]
theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by rw [mul_assoc, mul_div_cancel'_right]

/- warning: div_mul_mul_cancel -> div_mul_mul_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a c) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b c)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6494 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6494)))))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6494)))) a c) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6494)))))) b c)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6494)))))) a b)
Case conversion may be inaccurate. Consider using '#align div_mul_mul_cancel div_mul_mul_cancelₓ'. -/
@[simp, to_additive]
theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by rw [mul_left_comm, div_mul_cancel', mul_comm]

/- warning: div_mul_div_cancel'' -> div_mul_div_cancel'' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c a)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c b)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6552 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6552)))))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6552)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6552)))) c a)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6552)))) c b)
Case conversion may be inaccurate. Consider using '#align div_mul_div_cancel'' div_mul_div_cancel''ₓ'. -/
@[simp, to_additive sub_add_sub_cancel']
theorem div_mul_div_cancel'' (a b c : G) : a / b * (c / a) = c / b := by rw [mul_comm] <;> apply div_mul_div_cancel'

/- warning: mul_div_div_cancel -> mul_div_div_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a c)) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) b c)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6621 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6621)))) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6621)))))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6621)))) a c)) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6621)))))) b c)
Case conversion may be inaccurate. Consider using '#align mul_div_div_cancel mul_div_div_cancelₓ'. -/
@[simp, to_additive]
theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by rw [← div_mul, mul_div_cancel''']

/- warning: div_div_div_cancel_left -> div_div_div_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] (a : G) (b : G) (c : G), Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c a) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c b)) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b a)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6678 : CommGroup.{u_1} G] (a : G) (b : G) (c : G), Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6678)))) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6678)))) c a) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6678)))) c b)) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6678)))) b a)
Case conversion may be inaccurate. Consider using '#align div_div_div_cancel_left div_div_div_cancel_leftₓ'. -/
@[simp, to_additive]
theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c, div_inv_eq_mul, mul_comm, div_mul_div_cancel']

/- warning: div_eq_div_iff_mul_eq_mul -> div_eq_div_iff_mul_eq_mul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c d)) (Eq.{succ u_3} G (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) a d) (HMul.hMul.{u_3 u_3 u_3} G G G (instHMul.{u_3} G (MulOneClass.toHasMul.{u_3} G (Monoid.toMulOneClass.{u_3} G (DivInvMonoid.toMonoid.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))))) c b))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6739 : CommGroup.{u_1} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6739)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6739)))) c d)) (Eq.{succ u_1} G (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6739)))))) a d) (HMul.hMul.{u_1 u_1 u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6739)))))) c b))
Case conversion may be inaccurate. Consider using '#align div_eq_div_iff_mul_eq_mul div_eq_div_iff_mul_eq_mulₓ'. -/
@[to_additive]
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]

/- warning: div_eq_div_iff_div_eq_div -> div_eq_div_iff_div_eq_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_3}} [_inst_1 : CommGroup.{u_3} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a b) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) c d)) (Eq.{succ u_3} G (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) a c) (HDiv.hDiv.{u_3 u_3 u_3} G G G (instHDiv.{u_3} G (DivInvMonoid.toHasDiv.{u_3} G (Group.toDivInvMonoid.{u_3} G (CommGroup.toGroup.{u_3} G _inst_1)))) b d))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Basic._hyg.6812 : CommGroup.{u_1} G] {a : G} {b : G} {c : G} {d : G}, Iff (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6812)))) a b) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6812)))) c d)) (Eq.{succ u_1} G (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6812)))) a c) (HDiv.hDiv.{u_1 u_1 u_1} G G G (instHDiv.{u_1} G (DivInvMonoid.toDiv.{u_1} G (Group.toDivInvMonoid.{u_1} G (CommGroup.toGroup.{u_1} G inst._@.Mathlib.Algebra.Group.Basic._hyg.6812)))) b d))
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

