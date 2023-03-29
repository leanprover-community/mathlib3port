/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.min_max
! leanprover-community/mathlib commit de87d5053a9fe5cbde723172c0fb7e27e7436473
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.MinMax
import Mathbin.Algebra.Order.Monoid.Lemmas

/-!
# Lemmas about `min` and `max` in an ordered monoid.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Function

variable {α β : Type _}

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/


/- warning: fn_min_mul_fn_max -> fn_min_mul_fn_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : CommSemigroup.{u2} β] (f : α -> β) (n : α) (m : α), Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Semigroup.toHasMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2))) (f (LinearOrder.min.{u1} α _inst_1 n m)) (f (LinearOrder.max.{u1} α _inst_1 n m))) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (Semigroup.toHasMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2))) (f n) (f m))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u2} α] [_inst_2 : CommSemigroup.{u1} β] (f : α -> β) (n : α) (m : α), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Semigroup.toMul.{u1} β (CommSemigroup.toSemigroup.{u1} β _inst_2))) (f (Min.min.{u2} α (LinearOrder.toMin.{u2} α _inst_1) n m)) (f (Max.max.{u2} α (LinearOrder.toMax.{u2} α _inst_1) n m))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Semigroup.toMul.{u1} β (CommSemigroup.toSemigroup.{u1} β _inst_2))) (f n) (f m))
Case conversion may be inaccurate. Consider using '#align fn_min_mul_fn_max fn_min_mul_fn_maxₓ'. -/
@[to_additive]
theorem fn_min_mul_fn_max [LinearOrder α] [CommSemigroup β] (f : α → β) (n m : α) :
    f (min n m) * f (max n m) = f n * f m := by cases' le_total n m with h h <;> simp [h, mul_comm]
#align fn_min_mul_fn_max fn_min_mul_fn_max
#align fn_min_add_fn_max fn_min_add_fn_max

/- warning: min_mul_max -> min_mul_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : CommSemigroup.{u1} α] (n : α) (m : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) (LinearOrder.min.{u1} α _inst_1 n m) (LinearOrder.max.{u1} α _inst_1 n m)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) n m)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : CommSemigroup.{u1} α] (n : α) (m : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) n m) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) n m)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) n m)
Case conversion may be inaccurate. Consider using '#align min_mul_max min_mul_maxₓ'. -/
@[to_additive]
theorem min_mul_max [LinearOrder α] [CommSemigroup α] (n m : α) : min n m * max n m = n * m :=
  fn_min_mul_fn_max id n m
#align min_mul_max min_mul_max
#align min_add_max min_add_max

section CovariantClassMulLe

variable [LinearOrder α]

section Mul

variable [Mul α]

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

/- warning: min_mul_mul_left -> min_mul_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a (LinearOrder.min.{u1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.181 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.183 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.181 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.183) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.196 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.198 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.196 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.198)] (a : α) (b : α) (c : α), Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align min_mul_mul_left min_mul_mul_leftₓ'. -/
@[to_additive]
theorem min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
  (monotone_id.const_mul' a).map_min.symm
#align min_mul_mul_left min_mul_mul_left
#align min_add_add_left min_add_add_left

/- warning: max_mul_mul_left -> max_mul_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a (LinearOrder.max.{u1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.257 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.259 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.257 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.259) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.272 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.274 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.272 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.274)] (a : α) (b : α) (c : α), Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align max_mul_mul_left max_mul_mul_leftₓ'. -/
@[to_additive]
theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
  (monotone_id.const_mul' a).map_max.symm
#align max_mul_mul_left max_mul_mul_left
#align max_add_add_left max_add_add_left

end Left

section Right

variable [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

/- warning: min_mul_mul_right -> min_mul_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (LinearOrder.min.{u1} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.385 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.387 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.385 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.387)) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.400 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.402 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.400 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.402)] (a : α) (b : α) (c : α), Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) c)
Case conversion may be inaccurate. Consider using '#align min_mul_mul_right min_mul_mul_rightₓ'. -/
@[to_additive]
theorem min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
  (monotone_id.mul_const' c).map_min.symm
#align min_mul_mul_right min_mul_mul_right
#align min_add_add_right min_add_add_right

/- warning: max_mul_mul_right -> max_mul_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.max.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (LinearOrder.max.{u1} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.464 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.466 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.464 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.466)) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.479 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.481 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.479 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.481)] (a : α) (b : α) (c : α), Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) c)
Case conversion may be inaccurate. Consider using '#align max_mul_mul_right max_mul_mul_rightₓ'. -/
@[to_additive]
theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
  (monotone_id.mul_const' c).map_max.symm
#align max_mul_mul_right max_mul_mul_right
#align max_add_add_right max_add_add_right

end Right

#print lt_or_lt_of_mul_lt_mul /-
@[to_additive]
theorem lt_or_lt_of_mul_lt_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ < a₂ * b₂ → a₁ < a₂ ∨ b₁ < b₂ :=
  by
  contrapose!
  exact fun h => mul_le_mul' h.1 h.2
#align lt_or_lt_of_mul_lt_mul lt_or_lt_of_mul_lt_mul
#align lt_or_lt_of_add_lt_add lt_or_lt_of_add_lt_add
-/

#print le_or_lt_of_mul_le_mul /-
@[to_additive]
theorem le_or_lt_of_mul_le_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ < b₂ :=
  by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_le h.1 h.2
#align le_or_lt_of_mul_le_mul le_or_lt_of_mul_le_mul
#align le_or_lt_of_add_le_add le_or_lt_of_add_le_add
-/

#print lt_or_le_of_mul_le_mul /-
@[to_additive]
theorem lt_or_le_of_mul_le_mul [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ < a₂ ∨ b₁ ≤ b₂ :=
  by
  contrapose!
  exact fun h => mul_lt_mul_of_le_of_lt h.1 h.2
#align lt_or_le_of_mul_le_mul lt_or_le_of_mul_le_mul
#align lt_or_le_of_add_le_add lt_or_le_of_add_le_add
-/

#print le_or_le_of_mul_le_mul /-
@[to_additive]
theorem le_or_le_of_mul_le_mul [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} :
    a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ ≤ b₂ :=
  by
  contrapose!
  exact fun h => mul_lt_mul_of_lt_of_lt h.1 h.2
#align le_or_le_of_mul_le_mul le_or_le_of_mul_le_mul
#align le_or_le_of_add_le_add le_or_le_of_add_le_add
-/

#print mul_lt_mul_iff_of_le_of_le /-
@[to_additive]
theorem mul_lt_mul_iff_of_le_of_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₁ * b₁ < a₂ * b₂ ↔ a₁ < a₂ ∨ b₁ < b₂ :=
  by
  refine' ⟨lt_or_lt_of_mul_lt_mul, _⟩
  rintro (ha | hb)
  · exact mul_lt_mul_of_lt_of_le ha hb
  · exact mul_lt_mul_of_le_of_lt ha hb
#align mul_lt_mul_iff_of_le_of_le mul_lt_mul_iff_of_le_of_le
#align add_lt_add_iff_of_le_of_le add_lt_add_iff_of_le_of_le
-/

end Mul

variable [MulOneClass α]

/- warning: min_le_mul_of_one_le_right -> min_le_mul_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.min.{u1} α _inst_1 a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1296 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1298 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1296 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1298) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1311 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1313 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1311 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1313)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b))
Case conversion may be inaccurate. Consider using '#align min_le_mul_of_one_le_right min_le_mul_of_one_le_rightₓ'. -/
@[to_additive]
theorem min_le_mul_of_one_le_right [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (hb : 1 ≤ b) :
    min a b ≤ a * b :=
  min_le_iff.2 <| Or.inl <| le_mul_of_one_le_right' hb
#align min_le_mul_of_one_le_right min_le_mul_of_one_le_right
#align min_le_add_of_nonneg_right min_le_add_of_nonneg_right

/- warning: min_le_mul_of_one_le_left -> min_le_mul_of_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.min.{u1} α _inst_1 a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1368 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1370 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1368 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1370)) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1383 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1385 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1383 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1385)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b))
Case conversion may be inaccurate. Consider using '#align min_le_mul_of_one_le_left min_le_mul_of_one_le_leftₓ'. -/
@[to_additive]
theorem min_le_mul_of_one_le_left [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : 1 ≤ a) : min a b ≤ a * b :=
  min_le_iff.2 <| Or.inr <| le_mul_of_one_le_left' ha
#align min_le_mul_of_one_le_left min_le_mul_of_one_le_left
#align min_le_add_of_nonneg_left min_le_add_of_nonneg_left

/- warning: max_le_mul_of_one_le -> max_le_mul_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.max.{u1} α _inst_1 a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1437 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1439 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1437 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1439) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1452 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1454 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1452 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1454)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1474 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1476 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1474 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1476)) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1489 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1491 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1489 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1491)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b))
Case conversion may be inaccurate. Consider using '#align max_le_mul_of_one_le max_le_mul_of_one_leₓ'. -/
@[to_additive]
theorem max_le_mul_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max a b ≤ a * b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩
#align max_le_mul_of_one_le max_le_mul_of_one_le
#align max_le_add_of_nonneg max_le_add_of_nonneg

end CovariantClassMulLe

