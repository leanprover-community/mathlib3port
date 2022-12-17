/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa,
Yuyang Zhao

! This file was ported from Lean 3 source module algebra.order.monoid.lemmas
! leanprover-community/mathlib commit 11bb0c9152e5d14278fb0ac5e0be6d50e2c8fa05
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CovariantAndContravariant
import Mathbin.Order.MinMax

/-!
# Ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/608
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

## Remark

Almost no monoid is actually present in this file: most assumptions have been generalized to
`has_mul` or `mul_one_class`.

-/


-- TODO: If possible, uniformize lemma names, taking special care of `'`,
-- after the `ordered`-refactor is done.
open Function

variable {α β : Type _}

section Mul

variable [Mul α]

section LE

variable [LE α]

#print mul_le_mul_left' /-
/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_left]
theorem mul_le_mul_left' [CovariantClass α α (· * ·) (· ≤ ·)] {b c : α} (bc : b ≤ c) (a : α) :
    a * b ≤ a * c :=
  CovariantClass.elim _ bc
#align mul_le_mul_left' mul_le_mul_left'
-/

#print le_of_mul_le_mul_left' /-
@[to_additive le_of_add_le_add_left]
theorem le_of_mul_le_mul_left' [ContravariantClass α α (· * ·) (· ≤ ·)] {a b c : α}
    (bc : a * b ≤ a * c) : b ≤ c :=
  ContravariantClass.elim _ bc
#align le_of_mul_le_mul_left' le_of_mul_le_mul_left'
-/

#print mul_le_mul_right' /-
/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_right]
theorem mul_le_mul_right' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {b c : α} (bc : b ≤ c)
    (a : α) : b * a ≤ c * a :=
  CovariantClass.elim a bc
#align mul_le_mul_right' mul_le_mul_right'
-/

#print le_of_mul_le_mul_right' /-
@[to_additive le_of_add_le_add_right]
theorem le_of_mul_le_mul_right' [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (bc : b * a ≤ c * a) : b ≤ c :=
  ContravariantClass.elim a bc
#align le_of_mul_le_mul_right' le_of_mul_le_mul_right'
-/

#print mul_le_mul_iff_left /-
@[simp, to_additive]
theorem mul_le_mul_iff_left [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b c : α} : a * b ≤ a * c ↔ b ≤ c :=
  rel_iff_cov α α (· * ·) (· ≤ ·) a
#align mul_le_mul_iff_left mul_le_mul_iff_left
-/

#print mul_le_mul_iff_right /-
@[simp, to_additive]
theorem mul_le_mul_iff_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) {b c : α} : b * a ≤ c * a ↔ b ≤ c :=
  rel_iff_cov α α (swap (· * ·)) (· ≤ ·) a
#align mul_le_mul_iff_right mul_le_mul_iff_right
-/

end LE

section LT

variable [LT α]

#print mul_lt_mul_iff_left /-
@[simp, to_additive]
theorem mul_lt_mul_iff_left [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] (a : α) {b c : α} : a * b < a * c ↔ b < c :=
  rel_iff_cov α α (· * ·) (· < ·) a
#align mul_lt_mul_iff_left mul_lt_mul_iff_left
-/

#print mul_lt_mul_iff_right /-
@[simp, to_additive]
theorem mul_lt_mul_iff_right [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b c : α} : b * a < c * a ↔ b < c :=
  rel_iff_cov α α (swap (· * ·)) (· < ·) a
#align mul_lt_mul_iff_right mul_lt_mul_iff_right
-/

#print mul_lt_mul_left' /-
@[to_additive add_lt_add_left]
theorem mul_lt_mul_left' [CovariantClass α α (· * ·) (· < ·)] {b c : α} (bc : b < c) (a : α) :
    a * b < a * c :=
  CovariantClass.elim _ bc
#align mul_lt_mul_left' mul_lt_mul_left'
-/

#print lt_of_mul_lt_mul_left' /-
@[to_additive lt_of_add_lt_add_left]
theorem lt_of_mul_lt_mul_left' [ContravariantClass α α (· * ·) (· < ·)] {a b c : α}
    (bc : a * b < a * c) : b < c :=
  ContravariantClass.elim _ bc
#align lt_of_mul_lt_mul_left' lt_of_mul_lt_mul_left'
-/

#print mul_lt_mul_right' /-
@[to_additive add_lt_add_right]
theorem mul_lt_mul_right' [CovariantClass α α (swap (· * ·)) (· < ·)] {b c : α} (bc : b < c)
    (a : α) : b * a < c * a :=
  CovariantClass.elim a bc
#align mul_lt_mul_right' mul_lt_mul_right'
-/

#print lt_of_mul_lt_mul_right' /-
@[to_additive lt_of_add_lt_add_right]
theorem lt_of_mul_lt_mul_right' [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b c : α}
    (bc : b * a < c * a) : b < c :=
  ContravariantClass.elim a bc
#align lt_of_mul_lt_mul_right' lt_of_mul_lt_mul_right'
-/

end LT

section Preorder

variable [Preorder α]

#print mul_lt_mul_of_lt_of_lt /-
@[to_additive]
theorem mul_lt_mul_of_lt_of_lt [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  calc
    a * c < a * d := mul_lt_mul_left' h₂ a
    _ < b * d := mul_lt_mul_right' h₁ d
    
#align mul_lt_mul_of_lt_of_lt mul_lt_mul_of_lt_of_lt
-/

alias add_lt_add_of_lt_of_lt ← add_lt_add

#print mul_lt_mul_of_le_of_lt /-
@[to_additive]
theorem mul_lt_mul_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) :
    a * c < b * d :=
  (mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)
#align mul_lt_mul_of_le_of_lt mul_lt_mul_of_le_of_lt
-/

#print mul_lt_mul_of_lt_of_le /-
@[to_additive]
theorem mul_lt_mul_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) :
    a * c < b * d :=
  (mul_le_mul_left' h₂ _).trans_lt (mul_lt_mul_right' h₁ d)
#align mul_lt_mul_of_lt_of_le mul_lt_mul_of_lt_of_le
-/

#print Left.mul_lt_mul /-
/-- Only assumes left strict covariance. -/
@[to_additive "Only assumes left strict covariance"]
theorem Left.mul_lt_mul [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_le_of_lt h₁.le h₂
#align left.mul_lt_mul Left.mul_lt_mul
-/

#print Right.mul_lt_mul /-
/-- Only assumes right strict covariance. -/
@[to_additive "Only assumes right strict covariance"]
theorem Right.mul_lt_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_lt_of_le h₁ h₂.le
#align right.mul_lt_mul Right.mul_lt_mul
-/

#print mul_le_mul' /-
@[to_additive add_le_add]
theorem mul_le_mul' [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)
#align mul_le_mul' mul_le_mul'
-/

#print mul_le_mul_three /-
@[to_additive]
theorem mul_le_mul_three [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e)
    (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
  mul_le_mul' (mul_le_mul' h₁ h₂) h₃
#align mul_le_mul_three mul_le_mul_three
-/

#print mul_lt_of_mul_lt_left /-
@[to_additive]
theorem mul_lt_of_mul_lt_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a * b < c)
    (hle : d ≤ b) : a * d < c :=
  (mul_le_mul_left' hle a).trans_lt h
#align mul_lt_of_mul_lt_left mul_lt_of_mul_lt_left
-/

#print mul_le_of_mul_le_left /-
@[to_additive]
theorem mul_le_of_mul_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a * b ≤ c)
    (hle : d ≤ b) : a * d ≤ c :=
  @act_rel_of_rel_of_act_rel _ _ _ (· ≤ ·) _ ⟨fun _ _ _ => le_trans⟩ a _ _ _ hle h
#align mul_le_of_mul_le_left mul_le_of_mul_le_left
-/

#print mul_lt_of_mul_lt_right /-
@[to_additive]
theorem mul_lt_of_mul_lt_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a * b < c) (hle : d ≤ a) : d * b < c :=
  (mul_le_mul_right' hle b).trans_lt h
#align mul_lt_of_mul_lt_right mul_lt_of_mul_lt_right
-/

#print mul_le_of_mul_le_right /-
@[to_additive]
theorem mul_le_of_mul_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a * b ≤ c) (hle : d ≤ a) : d * b ≤ c :=
  (mul_le_mul_right' hle b).trans h
#align mul_le_of_mul_le_right mul_le_of_mul_le_right
-/

#print lt_mul_of_lt_mul_left /-
@[to_additive]
theorem lt_mul_of_lt_mul_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a < b * c)
    (hle : c ≤ d) : a < b * d :=
  h.trans_le (mul_le_mul_left' hle b)
#align lt_mul_of_lt_mul_left lt_mul_of_lt_mul_left
-/

#print le_mul_of_le_mul_left /-
@[to_additive]
theorem le_mul_of_le_mul_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a ≤ b * c)
    (hle : c ≤ d) : a ≤ b * d :=
  @rel_act_of_rel_of_rel_act _ _ _ (· ≤ ·) _ ⟨fun _ _ _ => le_trans⟩ b _ _ _ hle h
#align le_mul_of_le_mul_left le_mul_of_le_mul_left
-/

#print lt_mul_of_lt_mul_right /-
@[to_additive]
theorem lt_mul_of_lt_mul_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a < b * c) (hle : b ≤ d) : a < d * c :=
  h.trans_le (mul_le_mul_right' hle c)
#align lt_mul_of_lt_mul_right lt_mul_of_lt_mul_right
-/

#print le_mul_of_le_mul_right /-
@[to_additive]
theorem le_mul_of_le_mul_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a ≤ b * c) (hle : b ≤ d) : a ≤ d * c :=
  h.trans (mul_le_mul_right' hle c)
#align le_mul_of_le_mul_right le_mul_of_le_mul_right
-/

end Preorder

section PartialOrder

variable [PartialOrder α]

#print mul_left_cancel'' /-
@[to_additive]
theorem mul_left_cancel'' [ContravariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b = a * c) :
    b = c :=
  (le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.ge)
#align mul_left_cancel'' mul_left_cancel''
-/

#print mul_right_cancel'' /-
@[to_additive]
theorem mul_right_cancel'' [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b = c * b) : a = c :=
  le_antisymm (le_of_mul_le_mul_right' h.le) (le_of_mul_le_mul_right' h.ge)
#align mul_right_cancel'' mul_right_cancel''
-/

end PartialOrder

section LinearOrder

variable [LinearOrder α] {a b c d : α} [CovariantClass α α (· * ·) (· < ·)]
  [CovariantClass α α (swap (· * ·)) (· < ·)]

/- warning: min_le_max_of_mul_le_mul -> min_le_max_of_mul_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : α} {b : α} {c : α} {d : α} [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))], (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c d)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (LinearOrder.min.{u1} α _inst_2 a b) (LinearOrder.max.{u1} α _inst_2 c d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : α} {b : α} {c : α} {d : α} [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2831 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2833 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2831 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2833) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2846 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2848 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2846 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2848)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2868 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2870 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2868 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2870)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2883 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2885 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2883 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2885)], (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c d)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_2) a b) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_2) c d))
Case conversion may be inaccurate. Consider using '#align min_le_max_of_mul_le_mul min_le_max_of_mul_le_mulₓ'. -/
@[to_additive]
theorem min_le_max_of_mul_le_mul (h : a * b ≤ c * d) : min a b ≤ max c d := by
  simp_rw [min_le_iff, le_max_iff]
  contrapose! h
  exact mul_lt_mul_of_lt_of_lt h.1.1 h.2.2
#align min_le_max_of_mul_le_mul min_le_max_of_mul_le_mul

end LinearOrder

end Mul

-- using one
section MulOneClass

variable [MulOneClass α]

section LE

variable [LE α]

/- warning: le_mul_of_one_le_right' -> le_mul_of_one_le_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2981 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2983 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2981 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2983) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2996 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2998 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2996 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2998)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_right' le_mul_of_one_le_right'ₓ'. -/
@[to_additive le_add_of_nonneg_right]
theorem le_mul_of_one_le_right' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : 1 ≤ b) :
    a ≤ a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ ≤ a * b := mul_le_mul_left' h a
    
#align le_mul_of_one_le_right' le_mul_of_one_le_right'

/- warning: mul_le_of_le_one_right' -> mul_le_of_le_one_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3063 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3065 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3063 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3065) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3078 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3080 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3078 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3080)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_right' mul_le_of_le_one_right'ₓ'. -/
@[to_additive add_le_of_nonpos_right]
theorem mul_le_of_le_one_right' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : b ≤ 1) :
    a * b ≤ a :=
  calc
    a * b ≤ a * 1 := mul_le_mul_left' h a
    _ = a := mul_one a
    
#align mul_le_of_le_one_right' mul_le_of_le_one_right'

/- warning: le_mul_of_one_le_left' -> le_mul_of_one_le_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3145 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3147 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3145 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3147)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3160 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3162 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3160 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3162)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_left' le_mul_of_one_le_left'ₓ'. -/
@[to_additive le_add_of_nonneg_left]
theorem le_mul_of_one_le_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (h : 1 ≤ b) :
    a ≤ b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ ≤ b * a := mul_le_mul_right' h a
    
#align le_mul_of_one_le_left' le_mul_of_one_le_left'

/- warning: mul_le_of_le_one_left' -> mul_le_of_le_one_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3230 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3232 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3230 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3232)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3245 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3247 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3245 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3247)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) a)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_left' mul_le_of_le_one_left'ₓ'. -/
@[to_additive add_le_of_nonpos_left]
theorem mul_le_of_le_one_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (h : b ≤ 1) :
    b * a ≤ a :=
  calc
    b * a ≤ 1 * a := mul_le_mul_right' h a
    _ = a := one_mul a
    
#align mul_le_of_le_one_left' mul_le_of_le_one_left'

/- warning: one_le_of_le_mul_right -> one_le_of_le_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3309 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3311 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3309 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3311) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3324 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3326 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3324 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3326)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align one_le_of_le_mul_right one_le_of_le_mul_rightₓ'. -/
@[to_additive]
theorem one_le_of_le_mul_right [ContravariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : a ≤ a * b) :
    1 ≤ b :=
  le_of_mul_le_mul_left' <| by simpa only [mul_one]
#align one_le_of_le_mul_right one_le_of_le_mul_right

/- warning: le_one_of_mul_le_right -> le_one_of_mul_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a) -> (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3373 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3375 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3373 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3375) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3388 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3390 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3388 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3390)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) -> (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align le_one_of_mul_le_right le_one_of_mul_le_rightₓ'. -/
@[to_additive]
theorem le_one_of_mul_le_right [ContravariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : a * b ≤ a) :
    b ≤ 1 :=
  le_of_mul_le_mul_left' <| by simpa only [mul_one]
#align le_one_of_mul_le_right le_one_of_mul_le_right

/- warning: one_le_of_le_mul_left -> one_le_of_le_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3440 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3442 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3440 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3442)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3455 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3457 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3455 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3457)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align one_le_of_le_mul_left one_le_of_le_mul_leftₓ'. -/
@[to_additive]
theorem one_le_of_le_mul_left [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (h : b ≤ a * b) : 1 ≤ a :=
  le_of_mul_le_mul_right' <| by simpa only [one_mul]
#align one_le_of_le_mul_left one_le_of_le_mul_left

/- warning: le_one_of_mul_le_left -> le_one_of_mul_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) b) -> (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3507 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3509 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3507 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3509)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3522 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3524 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3522 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3524)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) -> (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align le_one_of_mul_le_left le_one_of_mul_le_leftₓ'. -/
@[to_additive]
theorem le_one_of_mul_le_left [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (h : a * b ≤ b) : a ≤ 1 :=
  le_of_mul_le_mul_right' <| by simpa only [one_mul]
#align le_one_of_mul_le_left le_one_of_mul_le_left

/- warning: le_mul_iff_one_le_right' -> le_mul_iff_one_le_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3571 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3573 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3571 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3573) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3586 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3588 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3586 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3588)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3605 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3607 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3605 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3607) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3620 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3622 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3620 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3622)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align le_mul_iff_one_le_right' le_mul_iff_one_le_right'ₓ'. -/
@[simp, to_additive le_add_iff_nonneg_right]
theorem le_mul_iff_one_le_right' [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b : α} : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)
#align le_mul_iff_one_le_right' le_mul_iff_one_le_right'

/- warning: le_mul_iff_one_le_left' -> le_mul_iff_one_le_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3703 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3705 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3703 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3705)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3718 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3720 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3718 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3720)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3740 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3742 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3740 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3742)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3755 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3757 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3755 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3757)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align le_mul_iff_one_le_left' le_mul_iff_one_le_left'ₓ'. -/
@[simp, to_additive le_add_iff_nonneg_left]
theorem le_mul_iff_one_le_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) {b : α} : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a)
#align le_mul_iff_one_le_left' le_mul_iff_one_le_left'

/- warning: mul_le_iff_le_one_right' -> mul_le_iff_le_one_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a) (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3835 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3837 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3835 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3837) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3850 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3852 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3850 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3852)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3869 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3871 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3869 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3871) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3884 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3886 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3884 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3886)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_le_iff_le_one_right' mul_le_iff_le_one_right'ₓ'. -/
@[simp, to_additive add_le_iff_nonpos_right]
theorem mul_le_iff_le_one_right' [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b : α} : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)
#align mul_le_iff_le_one_right' mul_le_iff_le_one_right'

/- warning: mul_le_iff_le_one_left' -> mul_le_iff_le_one_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) b) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3967 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3969 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3967 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3969)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3982 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3984 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3982 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3984)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4004 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4006 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4004 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4006)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4019 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4021 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4019 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4021)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_le_iff_le_one_left' mul_le_iff_le_one_left'ₓ'. -/
@[simp, to_additive add_le_iff_nonpos_left]
theorem mul_le_iff_le_one_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right b)
#align mul_le_iff_le_one_left' mul_le_iff_le_one_left'

end LE

section LT

variable [LT α]

/- warning: lt_mul_of_one_lt_right' -> lt_mul_of_one_lt_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4111 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4113 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4111 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4113) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4126 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4128 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4126 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4128)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_right' lt_mul_of_one_lt_right'ₓ'. -/
@[to_additive lt_add_of_pos_right]
theorem lt_mul_of_one_lt_right' [CovariantClass α α (· * ·) (· < ·)] (a : α) {b : α} (h : 1 < b) :
    a < a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ < a * b := mul_lt_mul_left' h a
    
#align lt_mul_of_one_lt_right' lt_mul_of_one_lt_right'

/- warning: mul_lt_of_lt_one_right' -> mul_lt_of_lt_one_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4193 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4195 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4193 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4195) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4208 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4210 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4208 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4210)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_right' mul_lt_of_lt_one_right'ₓ'. -/
@[to_additive add_lt_of_neg_right]
theorem mul_lt_of_lt_one_right' [CovariantClass α α (· * ·) (· < ·)] (a : α) {b : α} (h : b < 1) :
    a * b < a :=
  calc
    a * b < a * 1 := mul_lt_mul_left' h a
    _ = a := mul_one a
    
#align mul_lt_of_lt_one_right' mul_lt_of_lt_one_right'

/- warning: lt_mul_of_one_lt_left' -> lt_mul_of_one_lt_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4275 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4277 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4275 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4277)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4290 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4292 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4290 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4292)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_left' lt_mul_of_one_lt_left'ₓ'. -/
@[to_additive lt_add_of_pos_left]
theorem lt_mul_of_one_lt_left' [CovariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α}
    (h : 1 < b) : a < b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ < b * a := mul_lt_mul_right' h a
    
#align lt_mul_of_one_lt_left' lt_mul_of_one_lt_left'

/- warning: mul_lt_of_lt_one_left' -> mul_lt_of_lt_one_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4360 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4362 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4360 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4362)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4375 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4377 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4375 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4377)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) a)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_left' mul_lt_of_lt_one_left'ₓ'. -/
@[to_additive add_lt_of_neg_left]
theorem mul_lt_of_lt_one_left' [CovariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α}
    (h : b < 1) : b * a < a :=
  calc
    b * a < 1 * a := mul_lt_mul_right' h a
    _ = a := one_mul a
    
#align mul_lt_of_lt_one_left' mul_lt_of_lt_one_left'

/- warning: one_lt_of_lt_mul_right -> one_lt_of_lt_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4439 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4441 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4439 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4441) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4454 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4456 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4454 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4456)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align one_lt_of_lt_mul_right one_lt_of_lt_mul_rightₓ'. -/
@[to_additive]
theorem one_lt_of_lt_mul_right [ContravariantClass α α (· * ·) (· < ·)] {a b : α} (h : a < a * b) :
    1 < b :=
  lt_of_mul_lt_mul_left' <| by simpa only [mul_one]
#align one_lt_of_lt_mul_right one_lt_of_lt_mul_right

/- warning: lt_one_of_mul_lt_right -> lt_one_of_mul_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a) -> (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4503 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4505 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4503 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4505) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4518 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4520 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4518 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4520)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) -> (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align lt_one_of_mul_lt_right lt_one_of_mul_lt_rightₓ'. -/
@[to_additive]
theorem lt_one_of_mul_lt_right [ContravariantClass α α (· * ·) (· < ·)] {a b : α} (h : a * b < a) :
    b < 1 :=
  lt_of_mul_lt_mul_left' <| by simpa only [mul_one]
#align lt_one_of_mul_lt_right lt_one_of_mul_lt_right

/- warning: one_lt_of_lt_mul_left -> one_lt_of_lt_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4570 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4572 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4570 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4572)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4585 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4587 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4585 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4587)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align one_lt_of_lt_mul_left one_lt_of_lt_mul_leftₓ'. -/
@[to_additive]
theorem one_lt_of_lt_mul_left [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right' <| by simpa only [one_mul]
#align one_lt_of_lt_mul_left one_lt_of_lt_mul_left

/- warning: lt_one_of_mul_lt_left -> lt_one_of_mul_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) b) -> (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4637 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4639 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4637 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4639)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4652 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4654 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4652 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4654)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) -> (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align lt_one_of_mul_lt_left lt_one_of_mul_lt_leftₓ'. -/
@[to_additive]
theorem lt_one_of_mul_lt_left [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (h : a * b < b) : a < 1 :=
  lt_of_mul_lt_mul_right' <| by simpa only [one_mul]
#align lt_one_of_mul_lt_left lt_one_of_mul_lt_left

/- warning: lt_mul_iff_one_lt_right' -> lt_mul_iff_one_lt_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4701 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4703 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4701 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4703) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4716 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4718 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4716 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4718)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4735 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4737 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4735 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4737) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4750 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4752 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4750 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4752)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align lt_mul_iff_one_lt_right' lt_mul_iff_one_lt_right'ₓ'. -/
@[simp, to_additive lt_add_iff_pos_right]
theorem lt_mul_iff_one_lt_right' [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] (a : α) {b : α} : a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)
#align lt_mul_iff_one_lt_right' lt_mul_iff_one_lt_right'

/- warning: lt_mul_iff_one_lt_left' -> lt_mul_iff_one_lt_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4833 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4835 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4833 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4835)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4848 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4850 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4848 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4850)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4870 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4872 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4870 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4872)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4885 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4887 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4885 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4887)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align lt_mul_iff_one_lt_left' lt_mul_iff_one_lt_left'ₓ'. -/
@[simp, to_additive lt_add_iff_pos_left]
theorem lt_mul_iff_one_lt_left' [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α} : a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a)
#align lt_mul_iff_one_lt_left' lt_mul_iff_one_lt_left'

/- warning: mul_lt_iff_lt_one_left' -> mul_lt_iff_lt_one_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a) (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4965 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4967 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4965 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4967) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4980 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4982 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4980 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4982)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4999 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5001 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4999 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5001) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5014 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5016 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5014 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5016)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_iff_lt_one_left' mul_lt_iff_lt_one_left'ₓ'. -/
@[simp, to_additive add_lt_iff_neg_left]
theorem mul_lt_iff_lt_one_left' [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] {a b : α} : a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)
#align mul_lt_iff_lt_one_left' mul_lt_iff_lt_one_left'

/- warning: mul_lt_iff_lt_one_right' -> mul_lt_iff_lt_one_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] {a : α} (b : α), Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) b) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5097 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5099 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5097 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5099)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5112 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5114 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5112 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5114)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5134 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5136 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5134 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5136)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5149 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5151 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5149 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5151)] {a : α} (b : α), Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_iff_lt_one_right' mul_lt_iff_lt_one_right'ₓ'. -/
@[simp, to_additive add_lt_iff_neg_right]
theorem mul_lt_iff_lt_one_right' [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] {a : α} (b : α) : a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right b)
#align mul_lt_iff_lt_one_right' mul_lt_iff_lt_one_right'

end LT

section Preorder

variable [Preorder α]

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`,
which assume left covariance. -/


/- warning: mul_le_of_le_of_le_one -> mul_le_of_le_of_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5242 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5244 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5242 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5244) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5257 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5259 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5257 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5259)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_of_le_one mul_le_of_le_of_le_oneₓ'. -/
@[to_additive]
theorem mul_le_of_le_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b ≤ c)
    (ha : a ≤ 1) : b * a ≤ c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := mul_one b
    _ ≤ c := hbc
    
#align mul_le_of_le_of_le_one mul_le_of_le_of_le_one

/- warning: mul_lt_of_le_of_lt_one -> mul_lt_of_le_of_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5335 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5337 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5335 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5337) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5350 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5352 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5350 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5352)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_of_lt_one mul_lt_of_le_of_lt_oneₓ'. -/
@[to_additive]
theorem mul_lt_of_le_of_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b ≤ c)
    (ha : a < 1) : b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := mul_one b
    _ ≤ c := hbc
    
#align mul_lt_of_le_of_lt_one mul_lt_of_le_of_lt_one

/- warning: mul_lt_of_lt_of_le_one -> mul_lt_of_lt_of_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5428 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5430 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5428 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5430) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5443 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5445 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5443 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5445)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_le_one mul_lt_of_lt_of_le_oneₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : a ≤ 1) : b * a < c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := mul_one b
    _ < c := hbc
    
#align mul_lt_of_lt_of_le_one mul_lt_of_lt_of_le_one

/- warning: mul_lt_of_lt_of_lt_one -> mul_lt_of_lt_of_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5521 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5523 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5521 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5523) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5536 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5538 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5536 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5538)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_lt_one mul_lt_of_lt_of_lt_oneₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_of_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b < c)
    (ha : a < 1) : b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := mul_one b
    _ < c := hbc
    
#align mul_lt_of_lt_of_lt_one mul_lt_of_lt_of_lt_one

/- warning: mul_lt_of_lt_of_lt_one' -> mul_lt_of_lt_of_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5614 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5616 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5614 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5616) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5629 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5631 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5629 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5631)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_lt_one' mul_lt_of_lt_of_lt_one'ₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_of_lt_one' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : a < 1) : b * a < c :=
  mul_lt_of_lt_of_le_one hbc ha.le
#align mul_lt_of_lt_of_lt_one' mul_lt_of_lt_of_lt_one'

/- warning: left.mul_le_one -> Left.mul_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5683 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5685 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5683 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5685) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5698 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5700 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5698 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5700)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left.mul_le_one Left.mul_le_oneₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_le_one`. -/
@[to_additive
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_nonpos`."]
theorem Left.mul_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a ≤ 1) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  mul_le_of_le_of_le_one ha hb
#align left.mul_le_one Left.mul_le_one

/- warning: left.mul_lt_one_of_le_of_lt -> Left.mul_lt_one_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5754 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5756 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5754 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5756) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5769 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5771 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5769 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5771)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_one_of_le_of_lt Left.mul_lt_one_of_le_of_ltₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one_of_le_of_lt`. -/
@[to_additive Left.add_neg_of_nonpos_of_neg
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg_of_nonpos_of_neg`."]
theorem Left.mul_lt_one_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : a ≤ 1)
    (hb : b < 1) : a * b < 1 :=
  mul_lt_of_le_of_lt_one ha hb
#align left.mul_lt_one_of_le_of_lt Left.mul_lt_one_of_le_of_lt

/- warning: left.mul_lt_one_of_lt_of_le -> Left.mul_lt_one_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5825 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5827 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5825 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5827) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5840 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5842 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5840 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5842)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_one_of_lt_of_le Left.mul_lt_one_of_lt_of_leₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one_of_lt_of_le`. -/
@[to_additive Left.add_neg_of_neg_of_nonpos
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg_of_neg_of_nonpos`."]
theorem Left.mul_lt_one_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a < 1)
    (hb : b ≤ 1) : a * b < 1 :=
  mul_lt_of_lt_of_le_one ha hb
#align left.mul_lt_one_of_lt_of_le Left.mul_lt_one_of_lt_of_le

/- warning: left.mul_lt_one -> Left.mul_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5896 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5898 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5896 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5898) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5911 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5913 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5911 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5913)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_one Left.mul_lt_oneₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one`. -/
@[to_additive "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg`."]
theorem Left.mul_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one ha hb
#align left.mul_lt_one Left.mul_lt_one

/- warning: left.mul_lt_one' -> Left.mul_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5967 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5969 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5967 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5969) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5982 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5984 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5982 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5984)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_one' Left.mul_lt_one'ₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one'`. -/
@[to_additive "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg'`."]
theorem Left.mul_lt_one' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one' ha hb
#align left.mul_lt_one' Left.mul_lt_one'

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`,
which assume left covariance. -/


/- warning: le_mul_of_le_of_one_le -> le_mul_of_le_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6036 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6038 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6036 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6038) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6051 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6053 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6051 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6053)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align le_mul_of_le_of_one_le le_mul_of_le_of_one_leₓ'. -/
@[to_additive]
theorem le_mul_of_le_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b ≤ c)
    (ha : 1 ≤ a) : b ≤ c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * a := mul_le_mul_left' ha c
    
#align le_mul_of_le_of_one_le le_mul_of_le_of_one_le

/- warning: lt_mul_of_le_of_one_lt -> lt_mul_of_le_of_one_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6132 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6134 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6132 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6134) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6147 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6149 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6147 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6149)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_le_of_one_lt lt_mul_of_le_of_one_ltₓ'. -/
@[to_additive]
theorem lt_mul_of_le_of_one_lt [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b ≤ c)
    (ha : 1 < a) : b < c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_left' ha c
    
#align lt_mul_of_le_of_one_lt lt_mul_of_le_of_one_lt

/- warning: lt_mul_of_lt_of_one_le -> lt_mul_of_lt_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6228 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6230 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6228 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6230) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6243 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6245 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6243 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6245)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_le lt_mul_of_lt_of_one_leₓ'. -/
@[to_additive]
theorem lt_mul_of_lt_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : 1 ≤ a) : b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * a := mul_le_mul_left' ha c
    
#align lt_mul_of_lt_of_one_le lt_mul_of_lt_of_one_le

/- warning: lt_mul_of_lt_of_one_lt -> lt_mul_of_lt_of_one_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6324 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6326 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6324 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6326) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6339 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6341 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6339 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6341)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_lt lt_mul_of_lt_of_one_ltₓ'. -/
@[to_additive]
theorem lt_mul_of_lt_of_one_lt [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b < c)
    (ha : 1 < a) : b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_left' ha c
    
#align lt_mul_of_lt_of_one_lt lt_mul_of_lt_of_one_lt

/- warning: lt_mul_of_lt_of_one_lt' -> lt_mul_of_lt_of_one_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6420 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6422 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6420 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6422) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6435 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6437 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6435 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6437)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_lt' lt_mul_of_lt_of_one_lt'ₓ'. -/
@[to_additive]
theorem lt_mul_of_lt_of_one_lt' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : 1 < a) : b < c * a :=
  lt_mul_of_lt_of_one_le hbc ha.le
#align lt_mul_of_lt_of_one_lt' lt_mul_of_lt_of_one_lt'

/- warning: left.one_le_mul -> Left.one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6489 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6491 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6489 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6491) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6504 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6506 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6504 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6506)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_le_mul Left.one_le_mulₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_le_mul`. -/
@[to_additive Left.add_nonneg
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_nonneg`."]
theorem Left.one_le_mul [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_le_of_one_le ha hb
#align left.one_le_mul Left.one_le_mul

/- warning: left.one_lt_mul_of_le_of_lt -> Left.one_lt_mul_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6560 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6562 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6560 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6562) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6575 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6577 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6575 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6577)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_lt_mul_of_le_of_lt Left.one_lt_mul_of_le_of_ltₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul_of_le_of_lt`. -/
@[to_additive Left.add_pos_of_nonneg_of_pos
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos_of_nonneg_of_pos`."]
theorem Left.one_lt_mul_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : 1 ≤ a)
    (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_le_of_one_lt ha hb
#align left.one_lt_mul_of_le_of_lt Left.one_lt_mul_of_le_of_lt

/- warning: left.one_lt_mul_of_lt_of_le -> Left.one_lt_mul_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6631 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6633 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6631 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6633) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6646 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6648 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6646 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6648)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_lt_mul_of_lt_of_le Left.one_lt_mul_of_lt_of_leₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul_of_lt_of_le`. -/
@[to_additive Left.add_pos_of_pos_of_nonneg
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos_of_pos_of_nonneg`."]
theorem Left.one_lt_mul_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 < a)
    (hb : 1 ≤ b) : 1 < a * b :=
  lt_mul_of_lt_of_one_le ha hb
#align left.one_lt_mul_of_lt_of_le Left.one_lt_mul_of_lt_of_le

/- warning: left.one_lt_mul -> Left.one_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6702 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6704 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6702 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6704) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6717 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6719 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6717 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6719)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_lt_mul Left.one_lt_mulₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul`. -/
@[to_additive Left.add_pos
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos`."]
theorem Left.one_lt_mul [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt ha hb
#align left.one_lt_mul Left.one_lt_mul

/- warning: left.one_lt_mul' -> Left.one_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6773 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6775 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6773 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6775) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6788 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6790 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6788 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6790)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_lt_mul' Left.one_lt_mul'ₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul'`. -/
@[to_additive Left.add_pos'
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos'`."]
theorem Left.one_lt_mul' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt' ha hb
#align left.one_lt_mul' Left.one_lt_mul'

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`,
which assume right covariance. -/


/- warning: mul_le_of_le_one_of_le -> mul_le_of_le_one_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6845 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6847 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6845 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6847)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6860 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6862 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6860 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6862)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_of_le mul_le_of_le_one_of_leₓ'. -/
@[to_additive]
theorem mul_le_of_le_one_of_le [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a ≤ 1)
    (hbc : b ≤ c) : a * b ≤ c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := one_mul b
    _ ≤ c := hbc
    
#align mul_le_of_le_one_of_le mul_le_of_le_one_of_le

/- warning: mul_lt_of_lt_one_of_le -> mul_lt_of_lt_one_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6941 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6943 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6941 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6943)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6956 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6958 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6956 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6958)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_le mul_lt_of_lt_one_of_leₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_one_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : a < 1)
    (hbc : b ≤ c) : a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := one_mul b
    _ ≤ c := hbc
    
#align mul_lt_of_lt_one_of_le mul_lt_of_lt_one_of_le

/- warning: mul_lt_of_le_one_of_lt -> mul_lt_of_le_one_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7037 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7039 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7037 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7039)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7052 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7054 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7052 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7054)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_one_of_lt mul_lt_of_le_one_of_ltₓ'. -/
@[to_additive]
theorem mul_lt_of_le_one_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a ≤ 1)
    (hb : b < c) : a * b < c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := one_mul b
    _ < c := hb
    
#align mul_lt_of_le_one_of_lt mul_lt_of_le_one_of_lt

/- warning: mul_lt_of_lt_one_of_lt -> mul_lt_of_lt_one_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7133 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7135 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7133 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7135)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7148 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7150 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7148 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7150)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_lt mul_lt_of_lt_one_of_ltₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_one_of_lt [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : a < 1)
    (hb : b < c) : a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := one_mul b
    _ < c := hb
    
#align mul_lt_of_lt_one_of_lt mul_lt_of_lt_one_of_lt

/- warning: mul_lt_of_lt_one_of_lt' -> mul_lt_of_lt_one_of_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7229 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7231 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7229 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7231)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7244 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7246 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7244 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7246)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_lt' mul_lt_of_lt_one_of_lt'ₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_one_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a < 1)
    (hbc : b < c) : a * b < c :=
  mul_lt_of_le_one_of_lt ha.le hbc
#align mul_lt_of_lt_one_of_lt' mul_lt_of_lt_one_of_lt'

/- warning: right.mul_le_one -> Right.mul_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7301 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7303 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7301 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7303)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7316 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7318 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7316 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7318)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align right.mul_le_one Right.mul_le_oneₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_le_one`. -/
@[to_additive "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_nonpos`."]
theorem Right.mul_le_one [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : a ≤ 1)
    (hb : b ≤ 1) : a * b ≤ 1 :=
  mul_le_of_le_one_of_le ha hb
#align right.mul_le_one Right.mul_le_one

/- warning: right.mul_lt_one_of_lt_of_le -> Right.mul_lt_one_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7375 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7377 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7375 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7377)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7390 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7392 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7390 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7392)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_one_of_lt_of_le Right.mul_lt_one_of_lt_of_leₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one_of_lt_of_le`. -/
@[to_additive Right.add_neg_of_neg_of_nonpos
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg_of_neg_of_nonpos`."]
theorem Right.mul_lt_one_of_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
  mul_lt_of_lt_one_of_le ha hb
#align right.mul_lt_one_of_lt_of_le Right.mul_lt_one_of_lt_of_le

/- warning: right.mul_lt_one_of_le_of_lt -> Right.mul_lt_one_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7449 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7451 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7449 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7451)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7464 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7466 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7464 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7466)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_one_of_le_of_lt Right.mul_lt_one_of_le_of_ltₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one_of_le_of_lt`. -/
@[to_additive Right.add_neg_of_nonpos_of_neg
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg_of_nonpos_of_neg`."]
theorem Right.mul_lt_one_of_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
  mul_lt_of_le_one_of_lt ha hb
#align right.mul_lt_one_of_le_of_lt Right.mul_lt_one_of_le_of_lt

/- warning: right.mul_lt_one -> Right.mul_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7523 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7525 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7523 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7525)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7538 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7540 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7538 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7540)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_one Right.mul_lt_oneₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one`. -/
@[to_additive "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg`."]
theorem Right.mul_lt_one [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α} (ha : a < 1)
    (hb : b < 1) : a * b < 1 :=
  mul_lt_of_lt_one_of_lt ha hb
#align right.mul_lt_one Right.mul_lt_one

/- warning: right.mul_lt_one' -> Right.mul_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7597 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7599 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7597 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7599)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7612 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7614 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7612 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7614)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_one' Right.mul_lt_one'ₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one'`. -/
@[to_additive "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg'`."]
theorem Right.mul_lt_one' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : a < 1)
    (hb : b < 1) : a * b < 1 :=
  mul_lt_of_lt_one_of_lt' ha hb
#align right.mul_lt_one' Right.mul_lt_one'

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`,
which assume right covariance. -/


/- warning: le_mul_of_one_le_of_le -> le_mul_of_one_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7669 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7671 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7669 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7671)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7684 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7686 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7684 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7686)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_of_le le_mul_of_one_le_of_leₓ'. -/
@[to_additive]
theorem le_mul_of_one_le_of_le [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 ≤ a)
    (hbc : b ≤ c) : b ≤ a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_right' ha c
    
#align le_mul_of_one_le_of_le le_mul_of_one_le_of_le

/- warning: lt_mul_of_one_lt_of_le -> lt_mul_of_one_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7768 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7770 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7768 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7770)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7783 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7785 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7783 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7785)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_le lt_mul_of_one_lt_of_leₓ'. -/
@[to_additive]
theorem lt_mul_of_one_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : 1 < a)
    (hbc : b ≤ c) : b < a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_right' ha c
    
#align lt_mul_of_one_lt_of_le lt_mul_of_one_lt_of_le

/- warning: lt_mul_of_one_le_of_lt -> lt_mul_of_one_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7867 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7869 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7867 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7869)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7882 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7884 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7882 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7884)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_le_of_lt lt_mul_of_one_le_of_ltₓ'. -/
@[to_additive]
theorem lt_mul_of_one_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 ≤ a)
    (hbc : b < c) : b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_right' ha c
    
#align lt_mul_of_one_le_of_lt lt_mul_of_one_le_of_lt

/- warning: lt_mul_of_one_lt_of_lt -> lt_mul_of_one_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7966 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7968 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7966 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7968)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7981 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7983 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7981 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7983)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_lt lt_mul_of_one_lt_of_ltₓ'. -/
@[to_additive]
theorem lt_mul_of_one_lt_of_lt [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : 1 < a)
    (hbc : b < c) : b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_right' ha c
    
#align lt_mul_of_one_lt_of_lt lt_mul_of_one_lt_of_lt

/- warning: lt_mul_of_one_lt_of_lt' -> lt_mul_of_one_lt_of_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8065 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8067 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8065 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8067)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8080 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8082 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8080 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8082)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_lt' lt_mul_of_one_lt_of_lt'ₓ'. -/
@[to_additive]
theorem lt_mul_of_one_lt_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 < a)
    (hbc : b < c) : b < a * c :=
  lt_mul_of_one_le_of_lt ha.le hbc
#align lt_mul_of_one_lt_of_lt' lt_mul_of_one_lt_of_lt'

/- warning: right.one_le_mul -> Right.one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8137 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8139 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8137 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8139)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8152 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8154 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8152 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8154)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_le_mul Right.one_le_mulₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_le_mul`. -/
@[to_additive Right.add_nonneg
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_nonneg`."]
theorem Right.one_le_mul [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : 1 ≤ a * b :=
  le_mul_of_one_le_of_le ha hb
#align right.one_le_mul Right.one_le_mul

/- warning: right.one_lt_mul_of_lt_of_le -> Right.one_lt_mul_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8211 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8213 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8211 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8213)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8226 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8228 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8226 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8228)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul_of_lt_of_le Right.one_lt_mul_of_lt_of_leₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul_of_lt_of_le`. -/
@[to_additive Right.add_pos_of_pos_of_nonneg
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos_of_pos_of_nonneg`."]
theorem Right.one_lt_mul_of_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
  lt_mul_of_one_lt_of_le ha hb
#align right.one_lt_mul_of_lt_of_le Right.one_lt_mul_of_lt_of_le

/- warning: right.one_lt_mul_of_le_of_lt -> Right.one_lt_mul_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8285 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8287 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8285 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8287)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8300 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8302 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8300 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8302)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul_of_le_of_lt Right.one_lt_mul_of_le_of_ltₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul_of_le_of_lt`. -/
@[to_additive Right.add_pos_of_nonneg_of_pos
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos_of_nonneg_of_pos`."]
theorem Right.one_lt_mul_of_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_one_le_of_lt ha hb
#align right.one_lt_mul_of_le_of_lt Right.one_lt_mul_of_le_of_lt

/- warning: right.one_lt_mul -> Right.one_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8359 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8361 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8359 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8361)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8374 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8376 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8374 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8376)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul Right.one_lt_mulₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul`. -/
@[to_additive Right.add_pos
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos`."]
theorem Right.one_lt_mul [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α} (ha : 1 < a)
    (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_lt ha hb
#align right.one_lt_mul Right.one_lt_mul

/- warning: right.one_lt_mul' -> Right.one_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8433 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8435 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8433 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8435)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8448 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8450 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8448 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8450)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul' Right.one_lt_mul'ₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul'`. -/
@[to_additive Right.add_pos'
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos'`."]
theorem Right.one_lt_mul' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 < a)
    (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_lt' ha hb
#align right.one_lt_mul' Right.one_lt_mul'

alias Left.mul_le_one ← mul_le_one'

alias Left.mul_lt_one_of_le_of_lt ← mul_lt_one_of_le_of_lt

alias Left.mul_lt_one_of_lt_of_le ← mul_lt_one_of_lt_of_le

alias Left.mul_lt_one ← mul_lt_one

alias Left.mul_lt_one' ← mul_lt_one'

attribute [to_additive add_nonpos "**Alias** of `left.add_nonpos`."] mul_le_one'

attribute [to_additive add_neg_of_nonpos_of_neg "**Alias** of `left.add_neg_of_nonpos_of_neg`."]
  mul_lt_one_of_le_of_lt

attribute [to_additive add_neg_of_neg_of_nonpos "**Alias** of `left.add_neg_of_neg_of_nonpos`."]
  mul_lt_one_of_lt_of_le

attribute [to_additive "**Alias** of `left.add_neg`."] mul_lt_one

attribute [to_additive "**Alias** of `left.add_neg'`."] mul_lt_one'

alias Left.one_le_mul ← one_le_mul

alias Left.one_lt_mul_of_le_of_lt ← one_lt_mul_of_le_of_lt'

alias Left.one_lt_mul_of_lt_of_le ← one_lt_mul_of_lt_of_le'

alias Left.one_lt_mul ← one_lt_mul'

alias Left.one_lt_mul' ← one_lt_mul''

attribute [to_additive add_nonneg "**Alias** of `left.add_nonneg`."] one_le_mul

attribute [to_additive add_pos_of_nonneg_of_pos "**Alias** of `left.add_pos_of_nonneg_of_pos`."]
  one_lt_mul_of_le_of_lt'

attribute [to_additive add_pos_of_pos_of_nonneg "**Alias** of `left.add_pos_of_pos_of_nonneg`."]
  one_lt_mul_of_lt_of_le'

attribute [to_additive add_pos "**Alias** of `left.add_pos`."] one_lt_mul'

attribute [to_additive add_pos' "**Alias** of `left.add_pos'`."] one_lt_mul''

/- warning: lt_of_mul_lt_of_one_le_left -> lt_of_mul_lt_of_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8521 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8523 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8521 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8523) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8536 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8538 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8536 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8538)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_mul_lt_of_one_le_left lt_of_mul_lt_of_one_le_leftₓ'. -/
@[to_additive]
theorem lt_of_mul_lt_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b < c)
    (hle : 1 ≤ b) : a < c :=
  (le_mul_of_one_le_right' hle).trans_lt h
#align lt_of_mul_lt_of_one_le_left lt_of_mul_lt_of_one_le_left

/- warning: le_of_mul_le_of_one_le_left -> le_of_mul_le_of_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8590 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8592 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8590 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8592) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8605 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8607 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8605 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8607)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_left le_of_mul_le_of_one_le_leftₓ'. -/
@[to_additive]
theorem le_of_mul_le_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b ≤ c)
    (hle : 1 ≤ b) : a ≤ c :=
  (le_mul_of_one_le_right' hle).trans h
#align le_of_mul_le_of_one_le_left le_of_mul_le_of_one_le_left

/- warning: lt_of_lt_mul_of_le_one_left -> lt_of_lt_mul_of_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8659 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8661 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8659 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8661) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8674 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8676 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8674 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8676)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_left lt_of_lt_mul_of_le_one_leftₓ'. -/
@[to_additive]
theorem lt_of_lt_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a < b * c)
    (hle : c ≤ 1) : a < b :=
  h.trans_le (mul_le_of_le_one_right' hle)
#align lt_of_lt_mul_of_le_one_left lt_of_lt_mul_of_le_one_left

/- warning: le_of_le_mul_of_le_one_left -> le_of_le_mul_of_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8727 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8729 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8727 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8729) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8742 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8744 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8742 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8744)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b)
Case conversion may be inaccurate. Consider using '#align le_of_le_mul_of_le_one_left le_of_le_mul_of_le_one_leftₓ'. -/
@[to_additive]
theorem le_of_le_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a ≤ b * c)
    (hle : c ≤ 1) : a ≤ b :=
  h.trans (mul_le_of_le_one_right' hle)
#align le_of_le_mul_of_le_one_left le_of_le_mul_of_le_one_left

/- warning: lt_of_mul_lt_of_one_le_right -> lt_of_mul_lt_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8798 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8800 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8798 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8800)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8813 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8815 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8813 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8815)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c)
Case conversion may be inaccurate. Consider using '#align lt_of_mul_lt_of_one_le_right lt_of_mul_lt_of_one_le_rightₓ'. -/
@[to_additive]
theorem lt_of_mul_lt_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b < c) (hle : 1 ≤ a) : b < c :=
  (le_mul_of_one_le_left' hle).trans_lt h
#align lt_of_mul_lt_of_one_le_right lt_of_mul_lt_of_one_le_right

/- warning: le_of_mul_le_of_one_le_right -> le_of_mul_le_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8870 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8872 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8870 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8872)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8885 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8887 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8885 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8887)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_right le_of_mul_le_of_one_le_rightₓ'. -/
@[to_additive]
theorem le_of_mul_le_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
  (le_mul_of_one_le_left' hle).trans h
#align le_of_mul_le_of_one_le_right le_of_mul_le_of_one_le_right

/- warning: lt_of_lt_mul_of_le_one_right -> lt_of_lt_mul_of_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8942 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8944 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8942 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8944)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8957 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8959 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8957 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8959)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_right lt_of_lt_mul_of_le_one_rightₓ'. -/
@[to_additive]
theorem lt_of_lt_mul_of_le_one_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a < b * c) (hle : b ≤ 1) : a < c :=
  h.trans_le (mul_le_of_le_one_left' hle)
#align lt_of_lt_mul_of_le_one_right lt_of_lt_mul_of_le_one_right

/- warning: le_of_le_mul_of_le_one_right -> le_of_le_mul_of_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9013 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9015 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9013 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9015)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9028 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9030 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9028 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9030)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align le_of_le_mul_of_le_one_right le_of_le_mul_of_le_one_rightₓ'. -/
@[to_additive]
theorem le_of_le_mul_of_le_one_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a ≤ b * c) (hle : b ≤ 1) : a ≤ c :=
  h.trans (mul_le_of_le_one_left' hle)
#align le_of_le_mul_of_le_one_right le_of_le_mul_of_le_one_right

end Preorder

section PartialOrder

variable [PartialOrder α]

/- warning: mul_eq_one_iff' -> mul_eq_one_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) (And (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9093 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9095 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9093 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9095) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9108 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9110 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9108 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9110)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9130 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9132 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9130 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9132)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9145 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9147 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9145 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9147)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) (And (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align mul_eq_one_iff' mul_eq_one_iff'ₓ'. -/
@[to_additive]
theorem mul_eq_one_iff' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * b = 1 ↔ a = 1 ∧ b = 1 :=
  Iff.intro
    (fun hab : a * b = 1 =>
      have : a ≤ 1 := hab ▸ le_mul_of_le_of_one_le le_rfl hb
      have : a = 1 := le_antisymm this ha
      have : b ≤ 1 := hab ▸ le_mul_of_one_le_of_le ha le_rfl
      have : b = 1 := le_antisymm this hb
      And.intro ‹a = 1› ‹b = 1›)
    fun ⟨ha', hb'⟩ => by rw [ha', hb', mul_one]
#align mul_eq_one_iff' mul_eq_one_iff'

/- warning: mul_le_mul_iff_of_ge -> mul_le_mul_iff_of_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a₁ a₂) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b₁ b₂) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a₂ b₂) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a₁ b₁)) (And (Eq.{succ u1} α a₁ a₂) (Eq.{succ u1} α b₁ b₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9350 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9352 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9350 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9352) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9365 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9367 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9365 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9367)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9387 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9389 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9387 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9389)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9402 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9404 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9402 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9404)] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9421 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9423 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9421 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9423) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9436 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9438 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9436 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9438)] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9458 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9460 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9458 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9460)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9473 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9475 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9473 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9475)] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a₁ a₂) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b₁ b₂) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a₂ b₂) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a₁ b₁)) (And (Eq.{succ u1} α a₁ a₂) (Eq.{succ u1} α b₁ b₂)))
Case conversion may be inaccurate. Consider using '#align mul_le_mul_iff_of_ge mul_le_mul_iff_of_geₓ'. -/
@[to_additive]
theorem mul_le_mul_iff_of_ge [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₂ * b₂ ≤ a₁ * b₁ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  refine'
    ⟨fun h => _, by 
      rintro ⟨rfl, rfl⟩
      rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and_iff]
  refine' ⟨fun ha => h.not_lt _, fun hb => h.not_lt _⟩
  · exact mul_lt_mul_of_lt_of_le ha hb
  · exact mul_lt_mul_of_le_of_lt ha hb
#align mul_le_mul_iff_of_ge mul_le_mul_iff_of_ge

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α}

/- warning: eq_one_of_one_le_mul_left -> eq_one_of_one_le_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9642 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9644 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9642 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9644) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9657 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9659 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9657 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9659)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_leftₓ'. -/
@[to_additive eq_zero_of_add_nonneg_left]
theorem eq_one_of_one_le_mul_left (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : a = 1 :=
  ha.eq_of_not_lt fun h => hab.not_lt <| mul_lt_one_of_lt_of_le h hb
#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_left

/- warning: eq_one_of_mul_le_one_left -> eq_one_of_mul_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9719 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9721 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9719 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9721) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9734 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9736 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9734 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9736)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_mul_le_one_left eq_one_of_mul_le_one_leftₓ'. -/
@[to_additive]
theorem eq_one_of_mul_le_one_left (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : a = 1 :=
  ha.eq_of_not_gt fun h => hab.not_lt <| one_lt_mul_of_lt_of_le' h hb
#align eq_one_of_mul_le_one_left eq_one_of_mul_le_one_left

end Left

section Right

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}

/- warning: eq_one_of_one_le_mul_right -> eq_one_of_one_le_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9852 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9854 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9852 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9854)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9867 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9869 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9867 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9869)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_rightₓ'. -/
@[to_additive eq_zero_of_add_nonneg_right]
theorem eq_one_of_one_le_mul_right (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : b = 1 :=
  hb.eq_of_not_lt fun h => hab.not_lt <| Right.mul_lt_one_of_le_of_lt ha h
#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_right

/- warning: eq_one_of_mul_le_one_right -> eq_one_of_mul_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9932 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9934 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9932 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9934)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9947 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9949 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9947 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9949)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_mul_le_one_right eq_one_of_mul_le_one_rightₓ'. -/
@[to_additive]
theorem eq_one_of_mul_le_one_right (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : b = 1 :=
  hb.eq_of_not_gt fun h => hab.not_lt <| Right.one_lt_mul_of_le_of_lt ha h
#align eq_one_of_mul_le_one_right eq_one_of_mul_le_one_right

end Right

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/- warning: exists_square_le -> exists_square_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] (a : α), Exists.{succ u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10022 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10024 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10022 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10024) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10037 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10039 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10037 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10039)] (a : α), Exists.{succ u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b b) a)
Case conversion may be inaccurate. Consider using '#align exists_square_le exists_square_leₓ'. -/
theorem exists_square_le [CovariantClass α α (· * ·) (· < ·)] (a : α) : ∃ b : α, b * b ≤ a := by
  by_cases h : a < 1
  · use a
    have : a * a < a * 1 := mul_lt_mul_left' h a
    rw [mul_one] at this
    exact le_of_lt this
  · use 1
    push_neg  at h
    rwa [mul_one]
#align exists_square_le exists_square_le

end LinearOrder

end MulOneClass

section Semigroup

variable [Semigroup α]

section PartialOrder

variable [PartialOrder α]

/- warning: contravariant.to_left_cancel_semigroup -> Contravariant.toLeftCancelSemigroup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], LeftCancelSemigroup.{u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10305 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10307 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10305 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10307) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10320 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10322 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10320 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10322)], LeftCancelSemigroup.{u1} α
Case conversion may be inaccurate. Consider using '#align contravariant.to_left_cancel_semigroup Contravariant.toLeftCancelSemigroupₓ'. -/
/- This is not instance, since we want to have an instance from `left_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/-- A semigroup with a partial order and satisfying `left_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `left_cancel semigroup`. -/
@[to_additive
      "An additive semigroup with a partial order and satisfying `left_cancel_add_semigroup`\n(i.e. `c + a < c + b → a < b`) is a `left_cancel add_semigroup`."]
def Contravariant.toLeftCancelSemigroup [ContravariantClass α α (· * ·) (· ≤ ·)] :
    LeftCancelSemigroup α :=
  { ‹Semigroup α› with mul_left_cancel := fun a b c => mul_left_cancel'' }
#align contravariant.to_left_cancel_semigroup Contravariant.toLeftCancelSemigroup

/- warning: contravariant.to_right_cancel_semigroup -> Contravariant.toRightCancelSemigroup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], RightCancelSemigroup.{u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10388 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10390 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10388 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10390)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10403 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10405 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10403 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10405)], RightCancelSemigroup.{u1} α
Case conversion may be inaccurate. Consider using '#align contravariant.to_right_cancel_semigroup Contravariant.toRightCancelSemigroupₓ'. -/
/- This is not instance, since we want to have an instance from `right_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/-- A semigroup with a partial order and satisfying `right_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `right_cancel semigroup`. -/
@[to_additive
      "An additive semigroup with a partial order and satisfying `right_cancel_add_semigroup`\n(`a + c < b + c → a < b`) is a `right_cancel add_semigroup`."]
def Contravariant.toRightCancelSemigroup [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] :
    RightCancelSemigroup α :=
  { ‹Semigroup α› with mul_right_cancel := fun a b c => mul_right_cancel'' }
#align contravariant.to_right_cancel_semigroup Contravariant.toRightCancelSemigroup

/- warning: left.mul_eq_mul_iff_eq_and_eq -> Left.mul_eq_mul_iff_eq_and_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10468 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10470 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10468 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10470) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10483 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10485 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10483 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10485)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10505 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10507 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10505 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10507)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10520 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10522 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10520 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10522)] [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10539 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10541 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10539 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10541) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10554 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10556 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10554 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10556)] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10576 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10578 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10576 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10578)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10591 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10593 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10591 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10593)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
Case conversion may be inaccurate. Consider using '#align left.mul_eq_mul_iff_eq_and_eq Left.mul_eq_mul_iff_eq_and_eqₓ'. -/
@[to_additive]
theorem Left.mul_eq_mul_iff_eq_and_eq [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] [ContravariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) :
    a * b = c * d ↔ a = c ∧ b = d := by
  refine' ⟨fun h => _, fun h => congr_arg₂ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, mul_left_cancel'' h⟩
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  · exact ⟨mul_right_cancel'' h, rfl⟩
  exact ((Left.mul_lt_mul hac hbd).Ne h).elim
#align left.mul_eq_mul_iff_eq_and_eq Left.mul_eq_mul_iff_eq_and_eq

/- warning: right.mul_eq_mul_iff_eq_and_eq -> Right.mul_eq_mul_iff_eq_and_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10731 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10733 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10731 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10733) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10746 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10748 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10746 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10748)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10765 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10767 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10765 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10767) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10780 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10782 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10780 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10782)] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10802 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10804 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10802 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10804)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10817 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10819 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10817 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10819)] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10839 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10841 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10839 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10841)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10854 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10856 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10854 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10856)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
Case conversion may be inaccurate. Consider using '#align right.mul_eq_mul_iff_eq_and_eq Right.mul_eq_mul_iff_eq_and_eqₓ'. -/
@[to_additive]
theorem Right.mul_eq_mul_iff_eq_and_eq [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) :
    a * b = c * d ↔ a = c ∧ b = d := by
  refine' ⟨fun h => _, fun h => congr_arg₂ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, mul_left_cancel'' h⟩
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  · exact ⟨mul_right_cancel'' h, rfl⟩
  exact ((Right.mul_lt_mul hac hbd).Ne h).elim
#align right.mul_eq_mul_iff_eq_and_eq Right.mul_eq_mul_iff_eq_and_eq

alias Left.mul_eq_mul_iff_eq_and_eq ← mul_eq_mul_iff_eq_and_eq

attribute [to_additive] mul_eq_mul_iff_eq_and_eq

end PartialOrder

end Semigroup

section Mono

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

/- warning: monotone.const_mul' -> Monotone.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11036 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11038 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11036 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11038) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11051 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11053 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11051 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11053)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.const_mul' Monotone.const_mul'ₓ'. -/
@[to_additive const_add]
theorem Monotone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a
#align monotone.const_mul' Monotone.const_mul'

/- warning: monotone_on.const_mul' -> MonotoneOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11122 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11124 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11122 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11124) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11137 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11139 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11137 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11139)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.const_mul' MonotoneOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem MonotoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a
#align monotone_on.const_mul' MonotoneOn.const_mul'

/- warning: antitone.const_mul' -> Antitone.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11216 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11218 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11216 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11218) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11231 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11233 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11231 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11233)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.const_mul' Antitone.const_mul'ₓ'. -/
@[to_additive const_add]
theorem Antitone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a
#align antitone.const_mul' Antitone.const_mul'

/- warning: antitone_on.const_mul' -> AntitoneOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11302 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11304 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11302 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11304) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11317 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11319 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11317 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11319)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.const_mul' AntitoneOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem AntitoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a
#align antitone_on.const_mul' AntitoneOn.const_mul'

/- warning: monotone.mul_const' -> Monotone.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11399 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11401 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11399 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11401)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11414 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11416 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11414 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11416)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a))
Case conversion may be inaccurate. Consider using '#align monotone.mul_const' Monotone.mul_const'ₓ'. -/
@[to_additive add_const]
theorem Monotone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a
#align monotone.mul_const' Monotone.mul_const'

/- warning: monotone_on.mul_const' -> MonotoneOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11488 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11490 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11488 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11490)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11503 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11505 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11503 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11505)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.mul_const' MonotoneOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem MonotoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s)
    (a : α) : MonotoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a
#align monotone_on.mul_const' MonotoneOn.mul_const'

/- warning: antitone.mul_const' -> Antitone.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11585 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11587 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11585 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11587)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11600 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11602 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11600 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11602)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a))
Case conversion may be inaccurate. Consider using '#align antitone.mul_const' Antitone.mul_const'ₓ'. -/
@[to_additive add_const]
theorem Antitone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a
#align antitone.mul_const' Antitone.mul_const'

/- warning: antitone_on.mul_const' -> AntitoneOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11674 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11676 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11674 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11676)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11689 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11691 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11689 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11691)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.mul_const' AntitoneOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem AntitoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : AntitoneOn f s)
    (a : α) : AntitoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a
#align antitone_on.mul_const' AntitoneOn.mul_const'

/- warning: monotone.mul' -> Monotone.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (Monotone.{u2, u1} β α _inst_3 _inst_2 g) -> (Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11768 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11770 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11768 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11770) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11783 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11785 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11783 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11785)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11805 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11807 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11805 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11807)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11820 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11822 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11820 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11822)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (Monotone.{u1, u2} β α _inst_3 _inst_2 g) -> (Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.mul' Monotone.mul'ₓ'. -/
/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem Monotone.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x * g x := fun x y h => mul_le_mul' (hf h) (hg h)
#align monotone.mul' Monotone.mul'

/- warning: monotone_on.mul' -> MonotoneOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11896 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11898 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11896 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11898) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11911 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11913 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11911 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11913)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11933 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11935 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11933 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11935)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11948 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11950 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11948 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11950)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.mul' MonotoneOn.mul'ₓ'. -/
/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem MonotoneOn.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x * g x) s := fun x hx y hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)
#align monotone_on.mul' MonotoneOn.mul'

/- warning: antitone.mul' -> Antitone.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (Antitone.{u2, u1} β α _inst_3 _inst_2 g) -> (Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12035 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12037 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12035 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12037) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12050 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12052 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12050 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12052)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12072 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12074 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12072 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12074)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12087 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12089 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12087 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12089)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (Antitone.{u1, u2} β α _inst_3 _inst_2 g) -> (Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.mul' Antitone.mul'ₓ'. -/
/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem Antitone.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x * g x := fun x y h => mul_le_mul' (hf h) (hg h)
#align antitone.mul' Antitone.mul'

/- warning: antitone_on.mul' -> AntitoneOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12163 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12165 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12163 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12165) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12178 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12180 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12178 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12180)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12200 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12202 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12200 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12202)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12215 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12217 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12215 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12217)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.mul' AntitoneOn.mul'ₓ'. -/
/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem AntitoneOn.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x * g x) s := fun x hx y hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)
#align antitone_on.mul' AntitoneOn.mul'

section Left

variable [CovariantClass α α (· * ·) (· < ·)]

#print StrictMono.const_mul' /-
@[to_additive const_add]
theorem StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c * f x :=
  fun a b ab => mul_lt_mul_left' (hf ab) c
#align strict_mono.const_mul' StrictMono.const_mul'
-/

#print StrictMonoOn.const_mul' /-
@[to_additive const_add]
theorem StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => c * f x) s := fun a ha b hb ab => mul_lt_mul_left' (hf ha hb ab) c
#align strict_mono_on.const_mul' StrictMonoOn.const_mul'
-/

#print StrictAnti.const_mul' /-
@[to_additive const_add]
theorem StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c * f x :=
  fun a b ab => mul_lt_mul_left' (hf ab) c
#align strict_anti.const_mul' StrictAnti.const_mul'
-/

#print StrictAntiOn.const_mul' /-
@[to_additive const_add]
theorem StrictAntiOn.const_mul' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => c * f x) s := fun a ha b hb ab => mul_lt_mul_left' (hf ha hb ab) c
#align strict_anti_on.const_mul' StrictAntiOn.const_mul'
-/

end Left

section Right

variable [CovariantClass α α (swap (· * ·)) (· < ·)]

#print StrictMono.mul_const' /-
@[to_additive add_const]
theorem StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f x * c :=
  fun a b ab => mul_lt_mul_right' (hf ab) c
#align strict_mono.mul_const' StrictMono.mul_const'
-/

#print StrictMonoOn.mul_const' /-
@[to_additive add_const]
theorem StrictMonoOn.mul_const' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => f x * c) s := fun a ha b hb ab => mul_lt_mul_right' (hf ha hb ab) c
#align strict_mono_on.mul_const' StrictMonoOn.mul_const'
-/

#print StrictAnti.mul_const' /-
@[to_additive add_const]
theorem StrictAnti.mul_const' (hf : StrictAnti f) (c : α) : StrictAnti fun x => f x * c :=
  fun a b ab => mul_lt_mul_right' (hf ab) c
#align strict_anti.mul_const' StrictAnti.mul_const'
-/

#print StrictAntiOn.mul_const' /-
@[to_additive add_const]
theorem StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => f x * c) s := fun a ha b hb ab => mul_lt_mul_right' (hf ha hb ab) c
#align strict_anti_on.mul_const' StrictAntiOn.mul_const'
-/

end Right

/- warning: strict_mono.mul' -> StrictMono.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))], (StrictMono.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13151 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13153 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13151 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13153) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13166 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13168 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13166 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13168)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13188 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13190 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13188 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13190)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13203 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13205 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13203 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13205)], (StrictMono.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align strict_mono.mul' StrictMono.mul'ₓ'. -/
/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMono.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono fun x => f x * g x := fun a b ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)
#align strict_mono.mul' StrictMono.mul'

/- warning: strict_mono_on.mul' -> StrictMonoOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))], (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13279 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13281 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13279 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13281) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13294 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13296 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13294 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13296)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13316 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13318 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13316 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13318)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13331 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13333 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13331 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13333)], (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.mul' StrictMonoOn.mul'ₓ'. -/
/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMonoOn.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictMonoOn f s) (hg : StrictMonoOn g s) :
    StrictMonoOn (fun x => f x * g x) s := fun a ha b hb ab =>
  mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)
#align strict_mono_on.mul' StrictMonoOn.mul'

/- warning: strict_anti.mul' -> StrictAnti.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))], (StrictAnti.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13418 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13420 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13418 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13420) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13433 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13435 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13433 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13435)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13455 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13457 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13455 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13457)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13470 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13472 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13470 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13472)], (StrictAnti.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align strict_anti.mul' StrictAnti.mul'ₓ'. -/
/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAnti.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictAnti f) (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x := fun a b ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)
#align strict_anti.mul' StrictAnti.mul'

/- warning: strict_anti_on.mul' -> StrictAntiOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))], (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13546 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13548 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13546 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13548) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13561 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13563 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13561 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13563)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13583 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13585 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13583 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13585)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13598 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13600 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13598 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13600)], (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.mul' StrictAntiOn.mul'ₓ'. -/
/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAntiOn.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictAntiOn f s) (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x * g x) s := fun a ha b hb ab =>
  mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)
#align strict_anti_on.mul' StrictAntiOn.mul'

/- warning: monotone.mul_strict_mono' -> Monotone.mul_strict_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13685 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13687 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13685 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13687) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13700 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13702 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13700 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13702)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13722 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13724 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13722 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13724)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13737 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13739 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13737 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13739)] {f : β -> α} {g : β -> α}, (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.mul_strict_mono' Monotone.mul_strict_mono'ₓ'. -/
/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strict_mono
      "The sum of a monotone function and a strictly monotone function is strictly monotone."]
theorem Monotone.mul_strict_mono' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : Monotone f)
    (hg : StrictMono g) : StrictMono fun x => f x * g x := fun x y h =>
  mul_lt_mul_of_le_of_lt (hf h.le) (hg h)
#align monotone.mul_strict_mono' Monotone.mul_strict_mono'

/- warning: monotone_on.mul_strict_mono' -> MonotoneOn.mul_strict_mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13819 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13821 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13819 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13821) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13834 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13836 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13834 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13836)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13856 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13858 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13856 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13858)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13871 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13873 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13871 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13873)] {f : β -> α} {g : β -> α}, (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.mul_strict_mono' MonotoneOn.mul_strict_mono'ₓ'. -/
/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strict_mono
      "The sum of a monotone function and a strictly monotone function is strictly monotone."]
theorem MonotoneOn.mul_strict_mono' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : MonotoneOn f s)
    (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)
#align monotone_on.mul_strict_mono' MonotoneOn.mul_strict_mono'

/- warning: antitone.mul_strict_anti' -> Antitone.mul_strict_anti' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13964 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13966 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13964 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13966) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13979 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13981 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13979 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13981)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14001 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14003 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14001 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14003)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14016 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14018 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14016 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14018)] {f : β -> α} {g : β -> α}, (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.mul_strict_anti' Antitone.mul_strict_anti'ₓ'. -/
/-- The product of a antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strict_anti
      "The sum of a antitone function and a strictly antitone function is strictly antitone."]
theorem Antitone.mul_strict_anti' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : Antitone f)
    (hg : StrictAnti g) : StrictAnti fun x => f x * g x := fun x y h =>
  mul_lt_mul_of_le_of_lt (hf h.le) (hg h)
#align antitone.mul_strict_anti' Antitone.mul_strict_anti'

/- warning: antitone_on.mul_strict_anti' -> AntitoneOn.mul_strict_anti' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14098 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14100 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14098 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14100) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14113 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14115 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14113 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14115)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14135 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14137 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14135 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14137)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14150 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14152 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14150 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14152)] {f : β -> α} {g : β -> α}, (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.mul_strict_anti' AntitoneOn.mul_strict_anti'ₓ'. -/
/-- The product of a antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strict_anti
      "The sum of a antitone function and a strictly antitone function is strictly antitone."]
theorem AntitoneOn.mul_strict_anti' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : AntitoneOn f s)
    (hg : StrictAntiOn g s) : StrictAntiOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)
#align antitone_on.mul_strict_anti' AntitoneOn.mul_strict_anti'

variable [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]

#print StrictMono.mul_monotone' /-
/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone
      "The sum of a strictly monotone function and a monotone function is strictly monotone."]
theorem StrictMono.mul_monotone' (hf : StrictMono f) (hg : Monotone g) :
    StrictMono fun x => f x * g x := fun x y h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)
#align strict_mono.mul_monotone' StrictMono.mul_monotone'
-/

#print StrictMonoOn.mul_monotone' /-
/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone
      "The sum of a strictly monotone function and a monotone function is strictly monotone."]
theorem StrictMonoOn.mul_monotone' (hf : StrictMonoOn f s) (hg : MonotoneOn g s) :
    StrictMonoOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)
#align strict_mono_on.mul_monotone' StrictMonoOn.mul_monotone'
-/

#print StrictAnti.mul_antitone' /-
/-- The product of a strictly antitone function and a antitone function is strictly antitone. -/
@[to_additive add_antitone
      "The sum of a strictly antitone function and a antitone function is strictly antitone."]
theorem StrictAnti.mul_antitone' (hf : StrictAnti f) (hg : Antitone g) :
    StrictAnti fun x => f x * g x := fun x y h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)
#align strict_anti.mul_antitone' StrictAnti.mul_antitone'
-/

#print StrictAntiOn.mul_antitone' /-
/-- The product of a strictly antitone function and a antitone function is strictly antitone. -/
@[to_additive add_antitone
      "The sum of a strictly antitone function and a antitone function is strictly antitone."]
theorem StrictAntiOn.mul_antitone' (hf : StrictAntiOn f s) (hg : AntitoneOn g s) :
    StrictAntiOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)
#align strict_anti_on.mul_antitone' StrictAntiOn.mul_antitone'
-/

#print cmp_mul_left' /-
@[simp, to_additive cmp_add_left]
theorem cmp_mul_left' {α : Type _} [Mul α] [LinearOrder α] [CovariantClass α α (· * ·) (· < ·)]
    (a b c : α) : cmp (a * b) (a * c) = cmp b c :=
  (strictMono_id.const_mul' a).cmp_map_eq b c
#align cmp_mul_left' cmp_mul_left'
-/

#print cmp_mul_right' /-
@[simp, to_additive cmp_add_right]
theorem cmp_mul_right' {α : Type _} [Mul α] [LinearOrder α]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (a b c : α) : cmp (a * c) (b * c) = cmp a b :=
  (strictMono_id.mul_const' c).cmp_map_eq a b
#align cmp_mul_right' cmp_mul_right'
-/

end Mono

#print MulLECancellable /-
/-- An element `a : α` is `mul_le_cancellable` if `x ↦ a * x` is order-reflecting.
We will make a separate version of many lemmas that require `[contravariant_class α α (*) (≤)]` with
`mul_le_cancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ennreal`, where we can replace the assumption `add_le_cancellable x` by `x ≠ ∞`.
-/
@[to_additive
      " An element `a : α` is `add_le_cancellable` if `x ↦ a + x` is order-reflecting.\nWe will make a separate version of many lemmas that require `[contravariant_class α α (+) (≤)]` with\n`mul_le_cancellable` assumptions instead. These lemmas can then be instantiated to specific types,\nlike `ennreal`, where we can replace the assumption `add_le_cancellable x` by `x ≠ ∞`. "]
def MulLECancellable [Mul α] [LE α] (a : α) : Prop :=
  ∀ ⦃b c⦄, a * b ≤ a * c → b ≤ c
#align mul_le_cancellable MulLECancellable
-/

#print Contravariant.MulLECancellable /-
@[to_additive]
theorem Contravariant.MulLECancellable [Mul α] [LE α] [ContravariantClass α α (· * ·) (· ≤ ·)]
    {a : α} : MulLECancellable a := fun b c => le_of_mul_le_mul_left'
#align contravariant.mul_le_cancellable Contravariant.MulLECancellable
-/

/- warning: mul_le_cancellable_one -> mulLECancellable_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : LE.{u1} α], MulLECancellable.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : LE.{u1} α], MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable_one mulLECancellable_oneₓ'. -/
@[to_additive]
theorem mulLECancellable_one [Monoid α] [LE α] : MulLECancellable (1 : α) := fun a b => by
  simpa only [one_mul] using id
#align mul_le_cancellable_one mulLECancellable_one

namespace MulLECancellable

#print MulLECancellable.Injective /-
@[to_additive]
protected theorem Injective [Mul α] [PartialOrder α] {a : α} (ha : MulLECancellable a) :
    Injective ((· * ·) a) := fun b c h => le_antisymm (ha h.le) (ha h.ge)
#align mul_le_cancellable.injective MulLECancellable.Injective
-/

#print MulLECancellable.inj /-
@[to_additive]
protected theorem inj [Mul α] [PartialOrder α] {a b c : α} (ha : MulLECancellable a) :
    a * b = a * c ↔ b = c :=
  ha.Injective.eq_iff
#align mul_le_cancellable.inj MulLECancellable.inj
-/

/- warning: mul_le_cancellable.injective_left -> MulLECancellable.injective_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] {a : α}, (MulLECancellable.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a) -> (Function.Injective.{succ u1, succ u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) _x a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] {a : α}, (MulLECancellable.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a) -> (Function.Injective.{succ u1, succ u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) _x a))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.injective_left MulLECancellable.injective_leftₓ'. -/
@[to_additive]
protected theorem injective_left [CommSemigroup α] [PartialOrder α] {a : α}
    (ha : MulLECancellable a) : Injective (· * a) := fun b c h =>
  ha.Injective <| by rwa [mul_comm a, mul_comm a]
#align mul_le_cancellable.injective_left MulLECancellable.injective_left

/- warning: mul_le_cancellable.inj_left -> MulLECancellable.inj_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) c) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) b c)) (Eq.{succ u1} α a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) c) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) b c)) (Eq.{succ u1} α a b))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.inj_left MulLECancellable.inj_leftₓ'. -/
@[to_additive]
protected theorem inj_left [CommSemigroup α] [PartialOrder α] {a b c : α}
    (hc : MulLECancellable c) : a * c = b * c ↔ a = b :=
  hc.injective_left.eq_iff
#align mul_le_cancellable.inj_left MulLECancellable.inj_left

variable [LE α]

#print MulLECancellable.mul_le_mul_iff_left /-
@[to_additive]
protected theorem mul_le_mul_iff_left [Mul α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α}
    (ha : MulLECancellable a) : a * b ≤ a * c ↔ b ≤ c :=
  ⟨fun h => ha h, fun h => mul_le_mul_left' h a⟩
#align mul_le_cancellable.mul_le_mul_iff_left MulLECancellable.mul_le_mul_iff_left
-/

/- warning: mul_le_cancellable.mul_le_mul_iff_right -> MulLECancellable.mul_le_mul_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommSemigroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α _inst_1)] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) b a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) c a)) (LE.le.{u1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommSemigroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15587 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15589 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15587 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15589) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15602 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15604 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15602 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15604)] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) b a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) c a)) (LE.le.{u1} α _inst_1 b c))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.mul_le_mul_iff_right MulLECancellable.mul_le_mul_iff_rightₓ'. -/
@[to_additive]
protected theorem mul_le_mul_iff_right [CommSemigroup α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b c : α} (ha : MulLECancellable a) : b * a ≤ c * a ↔ b ≤ c := by
  rw [mul_comm b, mul_comm c, ha.mul_le_mul_iff_left]
#align mul_le_cancellable.mul_le_mul_iff_right MulLECancellable.mul_le_mul_iff_right

/- warning: mul_le_cancellable.le_mul_iff_one_le_right -> MulLECancellable.le_mul_iff_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2))) (LE.le.{u1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15686 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15688 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15686 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15688) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15701 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15703 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15701 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15703)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) b))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.le_mul_iff_one_le_right MulLECancellable.le_mul_iff_one_le_rightₓ'. -/
@[to_additive]
protected theorem le_mul_iff_one_le_right [MulOneClass α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left
#align mul_le_cancellable.le_mul_iff_one_le_right MulLECancellable.le_mul_iff_one_le_right

/- warning: mul_le_cancellable.mul_le_iff_le_one_right -> MulLECancellable.mul_le_iff_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2))) (LE.le.{u1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15782 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15784 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15782 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15784) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15797 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15799 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15797 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15799)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2)))))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.mul_le_iff_le_one_right MulLECancellable.mul_le_iff_le_one_rightₓ'. -/
@[to_additive]
protected theorem mul_le_iff_le_one_right [MulOneClass α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left
#align mul_le_cancellable.mul_le_iff_le_one_right MulLECancellable.mul_le_iff_le_one_right

/- warning: mul_le_cancellable.le_mul_iff_one_le_left -> MulLECancellable.le_mul_iff_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))))) (LE.le.{u1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15878 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15880 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15878 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15880) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15893 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15895 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15893 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15895)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.le_mul_iff_one_le_left MulLECancellable.le_mul_iff_one_le_leftₓ'. -/
@[to_additive]
protected theorem le_mul_iff_one_le_left [CommMonoid α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : a ≤ b * a ↔ 1 ≤ b := by
  rw [mul_comm, ha.le_mul_iff_one_le_right]
#align mul_le_cancellable.le_mul_iff_one_le_left MulLECancellable.le_mul_iff_one_le_left

/- warning: mul_le_cancellable.mul_le_iff_le_one_left -> MulLECancellable.mul_le_iff_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))))) (LE.le.{u1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15971 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15973 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15971 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15973) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15986 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15988 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15986 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15988)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))))))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.mul_le_iff_le_one_left MulLECancellable.mul_le_iff_le_one_leftₓ'. -/
@[to_additive]
protected theorem mul_le_iff_le_one_left [CommMonoid α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : b * a ≤ a ↔ b ≤ 1 := by
  rw [mul_comm, ha.mul_le_iff_le_one_right]
#align mul_le_cancellable.mul_le_iff_le_one_left MulLECancellable.mul_le_iff_le_one_left

end MulLECancellable

section Bit

variable [Add α] [Preorder α]

#print bit0_mono /-
theorem bit0_mono [CovariantClass α α (· + ·) (· ≤ ·)] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    Monotone (bit0 : α → α) := fun a b h => add_le_add h h
#align bit0_mono bit0_mono
-/

#print bit0_strict_mono /-
theorem bit0_strict_mono [CovariantClass α α (· + ·) (· < ·)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] : StrictMono (bit0 : α → α) := fun a b h =>
  add_lt_add h h
#align bit0_strict_mono bit0_strict_mono
-/

end Bit

