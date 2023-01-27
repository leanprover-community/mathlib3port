/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.min_max
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
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
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.180 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.182 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.180 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.182) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.195 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.197 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.195 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.197)] (a : α) (b : α) (c : α), Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) b c))
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
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.256 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.258 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.256 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.258) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.271 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.273 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.271 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.273)] (a : α) (b : α) (c : α), Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align max_mul_mul_left max_mul_mul_leftₓ'. -/
@[to_additive]
theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
  (monotone_id.const_mul' a).map_max.symm
#align max_mul_mul_left max_mul_mul_left
#align max_add_add_left max_add_add_left

#print lt_or_lt_of_mul_lt_mul /-
@[to_additive]
theorem lt_or_lt_of_mul_lt_mul [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b m n : α}
    (h : m * n < a * b) : m < a ∨ n < b := by
  contrapose! h
  exact mul_le_mul' h.1 h.2
#align lt_or_lt_of_mul_lt_mul lt_or_lt_of_mul_lt_mul
#align lt_or_lt_of_add_lt_add lt_or_lt_of_add_lt_add
-/

#print mul_lt_mul_iff_of_le_of_le /-
@[to_additive]
theorem mul_lt_mul_iff_of_le_of_le [CovariantClass α α (Function.swap (· * ·)) (· < ·)]
    [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]
    {a b c d : α} (ac : a ≤ c) (bd : b ≤ d) : a * b < c * d ↔ a < c ∨ b < d :=
  by
  refine' ⟨lt_or_lt_of_mul_lt_mul, fun h => _⟩
  cases' h with ha hb
  · exact mul_lt_mul_of_lt_of_le ha bd
  · exact mul_lt_mul_of_le_of_lt ac hb
#align mul_lt_mul_iff_of_le_of_le mul_lt_mul_iff_of_le_of_le
#align add_lt_add_iff_of_le_of_le add_lt_add_iff_of_le_of_le
-/

end Left

section Right

variable [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

/- warning: min_mul_mul_right -> min_mul_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.min.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (LinearOrder.min.{u1} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.737 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.739 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.737 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.739)) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.752 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.754 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.752 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.754)] (a : α) (b : α) (c : α), Eq.{succ u1} α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) c)
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
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : Mul.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.816 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.818 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.816 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.818)) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.831 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.833 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.831 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.833)] (a : α) (b : α) (c : α), Eq.{succ u1} α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) b c)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_2) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) c)
Case conversion may be inaccurate. Consider using '#align max_mul_mul_right max_mul_mul_rightₓ'. -/
@[to_additive]
theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
  (monotone_id.mul_const' c).map_max.symm
#align max_mul_mul_right max_mul_mul_right
#align max_add_add_right max_add_add_right

end Right

end Mul

variable [MulOneClass α]

/- warning: min_le_mul_of_one_le_right -> min_le_mul_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (LinearOrder.min.{u1} α _inst_1 a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.904 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.906 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.904 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.906) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.919 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.921 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.919 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.921)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.976 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.978 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.976 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.978)) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.991 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.993 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.991 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.993)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1045 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1047 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1045 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1047) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1060 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1062 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1060 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1062)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1082 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1084 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1082 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1084)) (fun (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1097 : α) (x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1099 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1097 x._@.Mathlib.Algebra.Order.Monoid.MinMax._hyg.1099)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b))
Case conversion may be inaccurate. Consider using '#align max_le_mul_of_one_le max_le_mul_of_one_leₓ'. -/
@[to_additive]
theorem max_le_mul_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    max a b ≤ a * b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩
#align max_le_mul_of_one_le max_le_mul_of_one_le
#align max_le_add_of_nonneg max_le_add_of_nonneg

end CovariantClassMulLe

