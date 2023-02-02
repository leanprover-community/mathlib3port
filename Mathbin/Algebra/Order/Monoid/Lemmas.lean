/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa,
Yuyang Zhao

! This file was ported from Lean 3 source module algebra.order.monoid.lemmas
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CovariantAndContravariant
import Mathbin.Order.MinMax

/-!
# Ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
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
#align add_le_add_left add_le_add_left
-/

#print le_of_mul_le_mul_left' /-
@[to_additive le_of_add_le_add_left]
theorem le_of_mul_le_mul_left' [ContravariantClass α α (· * ·) (· ≤ ·)] {a b c : α}
    (bc : a * b ≤ a * c) : b ≤ c :=
  ContravariantClass.elim _ bc
#align le_of_mul_le_mul_left' le_of_mul_le_mul_left'
#align le_of_add_le_add_left le_of_add_le_add_left
-/

#print mul_le_mul_right' /-
/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_right]
theorem mul_le_mul_right' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {b c : α} (bc : b ≤ c)
    (a : α) : b * a ≤ c * a :=
  CovariantClass.elim a bc
#align mul_le_mul_right' mul_le_mul_right'
#align add_le_add_right add_le_add_right
-/

#print le_of_mul_le_mul_right' /-
@[to_additive le_of_add_le_add_right]
theorem le_of_mul_le_mul_right' [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (bc : b * a ≤ c * a) : b ≤ c :=
  ContravariantClass.elim a bc
#align le_of_mul_le_mul_right' le_of_mul_le_mul_right'
#align le_of_add_le_add_right le_of_add_le_add_right
-/

#print mul_le_mul_iff_left /-
@[simp, to_additive]
theorem mul_le_mul_iff_left [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b c : α} : a * b ≤ a * c ↔ b ≤ c :=
  rel_iff_cov α α (· * ·) (· ≤ ·) a
#align mul_le_mul_iff_left mul_le_mul_iff_left
#align add_le_add_iff_left add_le_add_iff_left
-/

#print mul_le_mul_iff_right /-
@[simp, to_additive]
theorem mul_le_mul_iff_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) {b c : α} : b * a ≤ c * a ↔ b ≤ c :=
  rel_iff_cov α α (swap (· * ·)) (· ≤ ·) a
#align mul_le_mul_iff_right mul_le_mul_iff_right
#align add_le_add_iff_right add_le_add_iff_right
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
#align add_lt_add_iff_left add_lt_add_iff_left
-/

#print mul_lt_mul_iff_right /-
@[simp, to_additive]
theorem mul_lt_mul_iff_right [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b c : α} : b * a < c * a ↔ b < c :=
  rel_iff_cov α α (swap (· * ·)) (· < ·) a
#align mul_lt_mul_iff_right mul_lt_mul_iff_right
#align add_lt_add_iff_right add_lt_add_iff_right
-/

#print mul_lt_mul_left' /-
@[to_additive add_lt_add_left]
theorem mul_lt_mul_left' [CovariantClass α α (· * ·) (· < ·)] {b c : α} (bc : b < c) (a : α) :
    a * b < a * c :=
  CovariantClass.elim _ bc
#align mul_lt_mul_left' mul_lt_mul_left'
#align add_lt_add_left add_lt_add_left
-/

#print lt_of_mul_lt_mul_left' /-
@[to_additive lt_of_add_lt_add_left]
theorem lt_of_mul_lt_mul_left' [ContravariantClass α α (· * ·) (· < ·)] {a b c : α}
    (bc : a * b < a * c) : b < c :=
  ContravariantClass.elim _ bc
#align lt_of_mul_lt_mul_left' lt_of_mul_lt_mul_left'
#align lt_of_add_lt_add_left lt_of_add_lt_add_left
-/

#print mul_lt_mul_right' /-
@[to_additive add_lt_add_right]
theorem mul_lt_mul_right' [CovariantClass α α (swap (· * ·)) (· < ·)] {b c : α} (bc : b < c)
    (a : α) : b * a < c * a :=
  CovariantClass.elim a bc
#align mul_lt_mul_right' mul_lt_mul_right'
#align add_lt_add_right add_lt_add_right
-/

#print lt_of_mul_lt_mul_right' /-
@[to_additive lt_of_add_lt_add_right]
theorem lt_of_mul_lt_mul_right' [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b c : α}
    (bc : b * a < c * a) : b < c :=
  ContravariantClass.elim a bc
#align lt_of_mul_lt_mul_right' lt_of_mul_lt_mul_right'
#align lt_of_add_lt_add_right lt_of_add_lt_add_right
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
#align add_lt_add_of_lt_of_lt add_lt_add_of_lt_of_lt
-/

alias add_lt_add_of_lt_of_lt ← add_lt_add
#align add_lt_add add_lt_add

#print mul_lt_mul_of_le_of_lt /-
@[to_additive]
theorem mul_lt_mul_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) :
    a * c < b * d :=
  (mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)
#align mul_lt_mul_of_le_of_lt mul_lt_mul_of_le_of_lt
#align add_lt_add_of_le_of_lt add_lt_add_of_le_of_lt
-/

#print mul_lt_mul_of_lt_of_le /-
@[to_additive]
theorem mul_lt_mul_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) :
    a * c < b * d :=
  (mul_le_mul_left' h₂ _).trans_lt (mul_lt_mul_right' h₁ d)
#align mul_lt_mul_of_lt_of_le mul_lt_mul_of_lt_of_le
#align add_lt_add_of_lt_of_le add_lt_add_of_lt_of_le
-/

#print Left.mul_lt_mul /-
/-- Only assumes left strict covariance. -/
@[to_additive "Only assumes left strict covariance"]
theorem Left.mul_lt_mul [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_le_of_lt h₁.le h₂
#align left.mul_lt_mul Left.mul_lt_mul
#align left.add_lt_add Left.add_lt_add
-/

#print Right.mul_lt_mul /-
/-- Only assumes right strict covariance. -/
@[to_additive "Only assumes right strict covariance"]
theorem Right.mul_lt_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_lt_of_le h₁ h₂.le
#align right.mul_lt_mul Right.mul_lt_mul
#align right.add_lt_add Right.add_lt_add
-/

#print mul_le_mul' /-
@[to_additive add_le_add]
theorem mul_le_mul' [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)
#align mul_le_mul' mul_le_mul'
#align add_le_add add_le_add
-/

#print mul_le_mul_three /-
@[to_additive]
theorem mul_le_mul_three [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e)
    (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
  mul_le_mul' (mul_le_mul' h₁ h₂) h₃
#align mul_le_mul_three mul_le_mul_three
#align add_le_add_three add_le_add_three
-/

#print mul_lt_of_mul_lt_left /-
@[to_additive]
theorem mul_lt_of_mul_lt_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a * b < c)
    (hle : d ≤ b) : a * d < c :=
  (mul_le_mul_left' hle a).trans_lt h
#align mul_lt_of_mul_lt_left mul_lt_of_mul_lt_left
#align add_lt_of_add_lt_left add_lt_of_add_lt_left
-/

#print mul_le_of_mul_le_left /-
@[to_additive]
theorem mul_le_of_mul_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a * b ≤ c)
    (hle : d ≤ b) : a * d ≤ c :=
  @act_rel_of_rel_of_act_rel _ _ _ (· ≤ ·) _ ⟨fun _ _ _ => le_trans⟩ a _ _ _ hle h
#align mul_le_of_mul_le_left mul_le_of_mul_le_left
#align add_le_of_add_le_left add_le_of_add_le_left
-/

#print mul_lt_of_mul_lt_right /-
@[to_additive]
theorem mul_lt_of_mul_lt_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a * b < c) (hle : d ≤ a) : d * b < c :=
  (mul_le_mul_right' hle b).trans_lt h
#align mul_lt_of_mul_lt_right mul_lt_of_mul_lt_right
#align add_lt_of_add_lt_right add_lt_of_add_lt_right
-/

#print mul_le_of_mul_le_right /-
@[to_additive]
theorem mul_le_of_mul_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a * b ≤ c) (hle : d ≤ a) : d * b ≤ c :=
  (mul_le_mul_right' hle b).trans h
#align mul_le_of_mul_le_right mul_le_of_mul_le_right
#align add_le_of_add_le_right add_le_of_add_le_right
-/

#print lt_mul_of_lt_mul_left /-
@[to_additive]
theorem lt_mul_of_lt_mul_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a < b * c)
    (hle : c ≤ d) : a < b * d :=
  h.trans_le (mul_le_mul_left' hle b)
#align lt_mul_of_lt_mul_left lt_mul_of_lt_mul_left
#align lt_add_of_lt_add_left lt_add_of_lt_add_left
-/

#print le_mul_of_le_mul_left /-
@[to_additive]
theorem le_mul_of_le_mul_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a ≤ b * c)
    (hle : c ≤ d) : a ≤ b * d :=
  @rel_act_of_rel_of_rel_act _ _ _ (· ≤ ·) _ ⟨fun _ _ _ => le_trans⟩ b _ _ _ hle h
#align le_mul_of_le_mul_left le_mul_of_le_mul_left
#align le_add_of_le_add_left le_add_of_le_add_left
-/

#print lt_mul_of_lt_mul_right /-
@[to_additive]
theorem lt_mul_of_lt_mul_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a < b * c) (hle : b ≤ d) : a < d * c :=
  h.trans_le (mul_le_mul_right' hle c)
#align lt_mul_of_lt_mul_right lt_mul_of_lt_mul_right
#align lt_add_of_lt_add_right lt_add_of_lt_add_right
-/

#print le_mul_of_le_mul_right /-
@[to_additive]
theorem le_mul_of_le_mul_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a ≤ b * c) (hle : b ≤ d) : a ≤ d * c :=
  h.trans (mul_le_mul_right' hle c)
#align le_mul_of_le_mul_right le_mul_of_le_mul_right
#align le_add_of_le_add_right le_add_of_le_add_right
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
#align add_left_cancel'' add_left_cancel''
-/

#print mul_right_cancel'' /-
@[to_additive]
theorem mul_right_cancel'' [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b = c * b) : a = c :=
  le_antisymm (le_of_mul_le_mul_right' h.le) (le_of_mul_le_mul_right' h.ge)
#align mul_right_cancel'' mul_right_cancel''
#align add_right_cancel'' add_right_cancel''
-/

end PartialOrder

section LinearOrder

variable [LinearOrder α] {a b c d : α} [CovariantClass α α (· * ·) (· < ·)]
  [CovariantClass α α (swap (· * ·)) (· < ·)]

/- warning: min_le_max_of_mul_le_mul -> min_le_max_of_mul_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : α} {b : α} {c : α} {d : α} [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))], (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c d)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (LinearOrder.min.{u1} α _inst_2 a b) (LinearOrder.max.{u1} α _inst_2 c d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : α} {b : α} {c : α} {d : α} [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2880 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2882 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2880 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2882) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2895 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2897 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2895 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2897)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2917 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2919 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2917 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2919)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2932 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2934 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2932 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2934)], (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c d)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_2) a b) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_2) c d))
Case conversion may be inaccurate. Consider using '#align min_le_max_of_mul_le_mul min_le_max_of_mul_le_mulₓ'. -/
@[to_additive]
theorem min_le_max_of_mul_le_mul (h : a * b ≤ c * d) : min a b ≤ max c d :=
  by
  simp_rw [min_le_iff, le_max_iff]
  contrapose! h
  exact mul_lt_mul_of_lt_of_lt h.1.1 h.2.2
#align min_le_max_of_mul_le_mul min_le_max_of_mul_le_mul
#align min_le_max_of_add_le_add min_le_max_of_add_le_add

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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3032 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3034 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3032 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3034) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3047 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3049 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3047 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3049)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_right' le_mul_of_one_le_right'ₓ'. -/
@[to_additive le_add_of_nonneg_right]
theorem le_mul_of_one_le_right' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : 1 ≤ b) :
    a ≤ a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ ≤ a * b := mul_le_mul_left' h a
    
#align le_mul_of_one_le_right' le_mul_of_one_le_right'
#align le_add_of_nonneg_right le_add_of_nonneg_right

/- warning: mul_le_of_le_one_right' -> mul_le_of_le_one_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3122 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3124 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3122 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3124) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3137 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3139 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3137 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3139)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_right' mul_le_of_le_one_right'ₓ'. -/
@[to_additive add_le_of_nonpos_right]
theorem mul_le_of_le_one_right' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : b ≤ 1) :
    a * b ≤ a :=
  calc
    a * b ≤ a * 1 := mul_le_mul_left' h a
    _ = a := mul_one a
    
#align mul_le_of_le_one_right' mul_le_of_le_one_right'
#align add_le_of_nonpos_right add_le_of_nonpos_right

/- warning: le_mul_of_one_le_left' -> le_mul_of_one_le_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3212 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3214 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3212 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3214)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3227 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3229 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3227 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3229)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_left' le_mul_of_one_le_left'ₓ'. -/
@[to_additive le_add_of_nonneg_left]
theorem le_mul_of_one_le_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (h : 1 ≤ b) :
    a ≤ b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ ≤ b * a := mul_le_mul_right' h a
    
#align le_mul_of_one_le_left' le_mul_of_one_le_left'
#align le_add_of_nonneg_left le_add_of_nonneg_left

/- warning: mul_le_of_le_one_left' -> mul_le_of_le_one_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3305 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3307 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3305 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3307)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3320 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3322 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3320 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3322)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) a)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_left' mul_le_of_le_one_left'ₓ'. -/
@[to_additive add_le_of_nonpos_left]
theorem mul_le_of_le_one_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (h : b ≤ 1) :
    b * a ≤ a :=
  calc
    b * a ≤ 1 * a := mul_le_mul_right' h a
    _ = a := one_mul a
    
#align mul_le_of_le_one_left' mul_le_of_le_one_left'
#align add_le_of_nonpos_left add_le_of_nonpos_left

/- warning: one_le_of_le_mul_right -> one_le_of_le_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3392 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3394 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3392 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3394) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3407 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3409 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3407 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3409)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align one_le_of_le_mul_right one_le_of_le_mul_rightₓ'. -/
@[to_additive]
theorem one_le_of_le_mul_right [ContravariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : a ≤ a * b) :
    1 ≤ b :=
  le_of_mul_le_mul_left' <| by simpa only [mul_one]
#align one_le_of_le_mul_right one_le_of_le_mul_right
#align nonneg_of_le_add_right nonneg_of_le_add_right

/- warning: le_one_of_mul_le_right -> le_one_of_mul_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a) -> (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3458 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3460 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3458 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3460) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3473 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3475 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3473 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3475)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) -> (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align le_one_of_mul_le_right le_one_of_mul_le_rightₓ'. -/
@[to_additive]
theorem le_one_of_mul_le_right [ContravariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : a * b ≤ a) :
    b ≤ 1 :=
  le_of_mul_le_mul_left' <| by simpa only [mul_one]
#align le_one_of_mul_le_right le_one_of_mul_le_right
#align nonpos_of_add_le_right nonpos_of_add_le_right

/- warning: one_le_of_le_mul_left -> one_le_of_le_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3527 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3529 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3527 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3529)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3542 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3544 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3542 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3544)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align one_le_of_le_mul_left one_le_of_le_mul_leftₓ'. -/
@[to_additive]
theorem one_le_of_le_mul_left [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (h : b ≤ a * b) : 1 ≤ a :=
  le_of_mul_le_mul_right' <| by simpa only [one_mul]
#align one_le_of_le_mul_left one_le_of_le_mul_left
#align nonneg_of_le_add_left nonneg_of_le_add_left

/- warning: le_one_of_mul_le_left -> le_one_of_mul_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) b) -> (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3596 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3598 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3596 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3598)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3611 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3613 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3611 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3613)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) -> (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align le_one_of_mul_le_left le_one_of_mul_le_leftₓ'. -/
@[to_additive]
theorem le_one_of_mul_le_left [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (h : a * b ≤ b) : a ≤ 1 :=
  le_of_mul_le_mul_right' <| by simpa only [one_mul]
#align le_one_of_mul_le_left le_one_of_mul_le_left
#align nonpos_of_add_le_left nonpos_of_add_le_left

/- warning: le_mul_iff_one_le_right' -> le_mul_iff_one_le_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3662 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3664 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3662 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3664) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3677 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3679 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3677 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3679)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3696 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3698 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3696 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3698) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3711 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3713 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3711 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3713)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align le_mul_iff_one_le_right' le_mul_iff_one_le_right'ₓ'. -/
@[simp, to_additive le_add_iff_nonneg_right]
theorem le_mul_iff_one_le_right' [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b : α} : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)
#align le_mul_iff_one_le_right' le_mul_iff_one_le_right'
#align le_add_iff_nonneg_right le_add_iff_nonneg_right

/- warning: le_mul_iff_one_le_left' -> le_mul_iff_one_le_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3796 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3798 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3796 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3798)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3811 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3813 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3811 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3813)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3833 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3835 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3833 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3835)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3848 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3850 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3848 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3850)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align le_mul_iff_one_le_left' le_mul_iff_one_le_left'ₓ'. -/
@[simp, to_additive le_add_iff_nonneg_left]
theorem le_mul_iff_one_le_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) {b : α} : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a)
#align le_mul_iff_one_le_left' le_mul_iff_one_le_left'
#align le_add_iff_nonneg_left le_add_iff_nonneg_left

/- warning: mul_le_iff_le_one_right' -> mul_le_iff_le_one_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a) (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3930 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3932 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3930 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3932) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3945 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3947 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3945 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3947)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3964 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3966 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3964 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3966) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3979 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3981 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3979 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3981)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_le_iff_le_one_right' mul_le_iff_le_one_right'ₓ'. -/
@[simp, to_additive add_le_iff_nonpos_right]
theorem mul_le_iff_le_one_right' [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b : α} : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)
#align mul_le_iff_le_one_right' mul_le_iff_le_one_right'
#align add_le_iff_nonpos_right add_le_iff_nonpos_right

/- warning: mul_le_iff_le_one_left' -> mul_le_iff_le_one_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) b) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4064 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4066 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4064 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4066)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4079 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4081 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4079 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4081)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4101 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4103 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4101 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4103)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4116 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4118 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4116 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4118)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_le_iff_le_one_left' mul_le_iff_le_one_left'ₓ'. -/
@[simp, to_additive add_le_iff_nonpos_left]
theorem mul_le_iff_le_one_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right b)
#align mul_le_iff_le_one_left' mul_le_iff_le_one_left'
#align add_le_iff_nonpos_left add_le_iff_nonpos_left

end LE

section LT

variable [LT α]

/- warning: lt_mul_of_one_lt_right' -> lt_mul_of_one_lt_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4210 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4212 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4210 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4212) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4225 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4227 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4225 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4227)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_right' lt_mul_of_one_lt_right'ₓ'. -/
@[to_additive lt_add_of_pos_right]
theorem lt_mul_of_one_lt_right' [CovariantClass α α (· * ·) (· < ·)] (a : α) {b : α} (h : 1 < b) :
    a < a * b :=
  calc
    a = a * 1 := (mul_one a).symm
    _ < a * b := mul_lt_mul_left' h a
    
#align lt_mul_of_one_lt_right' lt_mul_of_one_lt_right'
#align lt_add_of_pos_right lt_add_of_pos_right

/- warning: mul_lt_of_lt_one_right' -> mul_lt_of_lt_one_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4300 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4302 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4300 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4302) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4315 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4317 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4315 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4317)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_right' mul_lt_of_lt_one_right'ₓ'. -/
@[to_additive add_lt_of_neg_right]
theorem mul_lt_of_lt_one_right' [CovariantClass α α (· * ·) (· < ·)] (a : α) {b : α} (h : b < 1) :
    a * b < a :=
  calc
    a * b < a * 1 := mul_lt_mul_left' h a
    _ = a := mul_one a
    
#align mul_lt_of_lt_one_right' mul_lt_of_lt_one_right'
#align add_lt_of_neg_right add_lt_of_neg_right

/- warning: lt_mul_of_one_lt_left' -> lt_mul_of_one_lt_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4390 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4392 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4390 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4392)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4405 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4407 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4405 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4407)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_left' lt_mul_of_one_lt_left'ₓ'. -/
@[to_additive lt_add_of_pos_left]
theorem lt_mul_of_one_lt_left' [CovariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α}
    (h : 1 < b) : a < b * a :=
  calc
    a = 1 * a := (one_mul a).symm
    _ < b * a := mul_lt_mul_right' h a
    
#align lt_mul_of_one_lt_left' lt_mul_of_one_lt_left'
#align lt_add_of_pos_left lt_add_of_pos_left

/- warning: mul_lt_of_lt_one_left' -> mul_lt_of_lt_one_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4483 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4485 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4483 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4485)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4498 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4500 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4498 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4500)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) a)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_left' mul_lt_of_lt_one_left'ₓ'. -/
@[to_additive add_lt_of_neg_left]
theorem mul_lt_of_lt_one_left' [CovariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α}
    (h : b < 1) : b * a < a :=
  calc
    b * a < 1 * a := mul_lt_mul_right' h a
    _ = a := one_mul a
    
#align mul_lt_of_lt_one_left' mul_lt_of_lt_one_left'
#align add_lt_of_neg_left add_lt_of_neg_left

/- warning: one_lt_of_lt_mul_right -> one_lt_of_lt_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4570 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4572 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4570 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4572) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4585 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4587 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4585 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4587)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align one_lt_of_lt_mul_right one_lt_of_lt_mul_rightₓ'. -/
@[to_additive]
theorem one_lt_of_lt_mul_right [ContravariantClass α α (· * ·) (· < ·)] {a b : α} (h : a < a * b) :
    1 < b :=
  lt_of_mul_lt_mul_left' <| by simpa only [mul_one]
#align one_lt_of_lt_mul_right one_lt_of_lt_mul_right
#align pos_of_lt_add_right pos_of_lt_add_right

/- warning: lt_one_of_mul_lt_right -> lt_one_of_mul_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a) -> (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4636 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4638 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4636 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4638) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4651 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4653 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4651 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4653)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) -> (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align lt_one_of_mul_lt_right lt_one_of_mul_lt_rightₓ'. -/
@[to_additive]
theorem lt_one_of_mul_lt_right [ContravariantClass α α (· * ·) (· < ·)] {a b : α} (h : a * b < a) :
    b < 1 :=
  lt_of_mul_lt_mul_left' <| by simpa only [mul_one]
#align lt_one_of_mul_lt_right lt_one_of_mul_lt_right
#align neg_of_add_lt_right neg_of_add_lt_right

/- warning: one_lt_of_lt_mul_left -> one_lt_of_lt_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4705 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4707 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4705 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4707)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4720 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4722 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4720 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4722)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align one_lt_of_lt_mul_left one_lt_of_lt_mul_leftₓ'. -/
@[to_additive]
theorem one_lt_of_lt_mul_left [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right' <| by simpa only [one_mul]
#align one_lt_of_lt_mul_left one_lt_of_lt_mul_left
#align pos_of_lt_add_left pos_of_lt_add_left

/- warning: lt_one_of_mul_lt_left -> lt_one_of_mul_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) b) -> (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4774 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4776 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4774 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4776)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4789 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4791 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4789 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4791)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) -> (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align lt_one_of_mul_lt_left lt_one_of_mul_lt_leftₓ'. -/
@[to_additive]
theorem lt_one_of_mul_lt_left [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (h : a * b < b) : a < 1 :=
  lt_of_mul_lt_mul_right' <| by simpa only [one_mul]
#align lt_one_of_mul_lt_left lt_one_of_mul_lt_left
#align neg_of_add_lt_left neg_of_add_lt_left

/- warning: lt_mul_iff_one_lt_right' -> lt_mul_iff_one_lt_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4840 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4842 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4840 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4842) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4855 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4857 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4855 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4857)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4874 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4876 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4874 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4876) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4889 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4891 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4889 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4891)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align lt_mul_iff_one_lt_right' lt_mul_iff_one_lt_right'ₓ'. -/
@[simp, to_additive lt_add_iff_pos_right]
theorem lt_mul_iff_one_lt_right' [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] (a : α) {b : α} : a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)
#align lt_mul_iff_one_lt_right' lt_mul_iff_one_lt_right'
#align lt_add_iff_pos_right lt_add_iff_pos_right

/- warning: lt_mul_iff_one_lt_left' -> lt_mul_iff_one_lt_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4974 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4976 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4974 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4976)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4989 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4991 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4989 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4991)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5011 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5013 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5011 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5013)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5026 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5028 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5026 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5028)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
Case conversion may be inaccurate. Consider using '#align lt_mul_iff_one_lt_left' lt_mul_iff_one_lt_left'ₓ'. -/
@[simp, to_additive lt_add_iff_pos_left]
theorem lt_mul_iff_one_lt_left' [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α} : a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a)
#align lt_mul_iff_one_lt_left' lt_mul_iff_one_lt_left'
#align lt_add_iff_pos_left lt_add_iff_pos_left

/- warning: mul_lt_iff_lt_one_left' -> mul_lt_iff_lt_one_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) a) (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5108 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5110 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5108 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5110) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5123 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5125 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5123 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5125)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5142 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5144 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5142 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5144) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5157 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5159 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5157 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5159)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_iff_lt_one_left' mul_lt_iff_lt_one_left'ₓ'. -/
@[simp, to_additive add_lt_iff_neg_left]
theorem mul_lt_iff_lt_one_left' [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] {a b : α} : a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)
#align mul_lt_iff_lt_one_left' mul_lt_iff_lt_one_left'
#align add_lt_iff_neg_left add_lt_iff_neg_left

/- warning: mul_lt_iff_lt_one_right' -> mul_lt_iff_lt_one_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α _inst_2)] {a : α} (b : α), Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) b) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5242 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5244 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5242 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5244)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5257 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5259 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5257 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5259)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5279 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5281 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5279 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5281)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5294 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5296 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5294 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5296)] {a : α} (b : α), Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_iff_lt_one_right' mul_lt_iff_lt_one_right'ₓ'. -/
@[simp, to_additive add_lt_iff_neg_right]
theorem mul_lt_iff_lt_one_right' [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] {a : α} (b : α) : a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right b)
#align mul_lt_iff_lt_one_right' mul_lt_iff_lt_one_right'
#align add_lt_iff_neg_right add_lt_iff_neg_right

end LT

section Preorder

variable [Preorder α]

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`,
which assume left covariance. -/


/- warning: mul_le_of_le_of_le_one -> mul_le_of_le_of_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5389 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5391 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5389 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5391) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5404 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5406 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5404 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5406)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_of_le_one mul_le_of_le_of_le_oneₓ'. -/
@[to_additive]
theorem mul_le_of_le_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b ≤ c)
    (ha : a ≤ 1) : b * a ≤ c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := mul_one b
    _ ≤ c := hbc
    
#align mul_le_of_le_of_le_one mul_le_of_le_of_le_one
#align add_le_of_le_of_nonpos add_le_of_le_of_nonpos

/- warning: mul_lt_of_le_of_lt_one -> mul_lt_of_le_of_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5496 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5498 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5496 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5498) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5511 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5513 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5511 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5513)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_of_lt_one mul_lt_of_le_of_lt_oneₓ'. -/
@[to_additive]
theorem mul_lt_of_le_of_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b ≤ c)
    (ha : a < 1) : b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := mul_one b
    _ ≤ c := hbc
    
#align mul_lt_of_le_of_lt_one mul_lt_of_le_of_lt_one
#align add_lt_of_le_of_neg add_lt_of_le_of_neg

/- warning: mul_lt_of_lt_of_le_one -> mul_lt_of_lt_of_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5603 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5605 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5603 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5605) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5618 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5620 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5618 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5620)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_le_one mul_lt_of_lt_of_le_oneₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : a ≤ 1) : b * a < c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := mul_one b
    _ < c := hbc
    
#align mul_lt_of_lt_of_le_one mul_lt_of_lt_of_le_one
#align add_lt_of_lt_of_nonpos add_lt_of_lt_of_nonpos

/- warning: mul_lt_of_lt_of_lt_one -> mul_lt_of_lt_of_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5710 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5712 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5710 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5712) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5725 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5727 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5725 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5727)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_lt_one mul_lt_of_lt_of_lt_oneₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_of_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b < c)
    (ha : a < 1) : b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := mul_one b
    _ < c := hbc
    
#align mul_lt_of_lt_of_lt_one mul_lt_of_lt_of_lt_one
#align add_lt_of_lt_of_neg add_lt_of_lt_of_neg

/- warning: mul_lt_of_lt_of_lt_one' -> mul_lt_of_lt_of_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5817 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5819 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5817 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5819) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5832 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5834 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5832 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5834)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_lt_one' mul_lt_of_lt_of_lt_one'ₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_of_lt_one' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : a < 1) : b * a < c :=
  mul_lt_of_lt_of_le_one hbc ha.le
#align mul_lt_of_lt_of_lt_one' mul_lt_of_lt_of_lt_one'
#align add_lt_of_lt_of_neg' add_lt_of_lt_of_neg'

/- warning: left.mul_le_one -> Left.mul_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5888 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5890 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5888 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5890) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5903 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5905 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5903 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5905)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left.mul_le_one Left.mul_le_oneₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_le_one`. -/
@[to_additive
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_nonpos`."]
theorem Left.mul_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a ≤ 1) (hb : b ≤ 1) :
    a * b ≤ 1 :=
  mul_le_of_le_of_le_one ha hb
#align left.mul_le_one Left.mul_le_one
#align left.add_nonpos Left.add_nonpos

/- warning: left.mul_lt_one_of_le_of_lt -> Left.mul_lt_one_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5959 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5961 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5959 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5961) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5974 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5976 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5974 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5976)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_one_of_le_of_lt Left.mul_lt_one_of_le_of_ltₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one_of_le_of_lt`. -/
@[to_additive Left.add_neg_of_nonpos_of_neg
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg_of_nonpos_of_neg`."]
theorem Left.mul_lt_one_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : a ≤ 1)
    (hb : b < 1) : a * b < 1 :=
  mul_lt_of_le_of_lt_one ha hb
#align left.mul_lt_one_of_le_of_lt Left.mul_lt_one_of_le_of_lt
#align left.add_neg_of_nonpos_of_neg Left.add_neg_of_nonpos_of_neg

/- warning: left.mul_lt_one_of_lt_of_le -> Left.mul_lt_one_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6030 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6032 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6030 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6032) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6045 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6047 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6045 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6047)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_one_of_lt_of_le Left.mul_lt_one_of_lt_of_leₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one_of_lt_of_le`. -/
@[to_additive Left.add_neg_of_neg_of_nonpos
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg_of_neg_of_nonpos`."]
theorem Left.mul_lt_one_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a < 1)
    (hb : b ≤ 1) : a * b < 1 :=
  mul_lt_of_lt_of_le_one ha hb
#align left.mul_lt_one_of_lt_of_le Left.mul_lt_one_of_lt_of_le
#align left.add_neg_of_neg_of_nonpos Left.add_neg_of_neg_of_nonpos

/- warning: left.mul_lt_one -> Left.mul_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6101 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6103 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6101 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6103) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6116 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6118 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6116 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6118)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_one Left.mul_lt_oneₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one`. -/
@[to_additive "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg`."]
theorem Left.mul_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one ha hb
#align left.mul_lt_one Left.mul_lt_one
#align left.add_neg Left.add_neg

/- warning: left.mul_lt_one' -> Left.mul_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6172 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6174 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6172 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6174) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6187 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6189 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6187 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6189)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_one' Left.mul_lt_one'ₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one'`. -/
@[to_additive "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg'`."]
theorem Left.mul_lt_one' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_lt_one' ha hb
#align left.mul_lt_one' Left.mul_lt_one'
#align left.add_neg' Left.add_neg'

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`,
which assume left covariance. -/


/- warning: le_mul_of_le_of_one_le -> le_mul_of_le_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6241 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6243 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6241 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6243) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6256 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6258 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6256 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6258)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align le_mul_of_le_of_one_le le_mul_of_le_of_one_leₓ'. -/
@[to_additive]
theorem le_mul_of_le_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b ≤ c)
    (ha : 1 ≤ a) : b ≤ c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * a := mul_le_mul_left' ha c
    
#align le_mul_of_le_of_one_le le_mul_of_le_of_one_le
#align le_add_of_le_of_nonneg le_add_of_le_of_nonneg

/- warning: lt_mul_of_le_of_one_lt -> lt_mul_of_le_of_one_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6351 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6353 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6351 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6353) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6366 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6368 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6366 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6368)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_le_of_one_lt lt_mul_of_le_of_one_ltₓ'. -/
@[to_additive]
theorem lt_mul_of_le_of_one_lt [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b ≤ c)
    (ha : 1 < a) : b < c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_left' ha c
    
#align lt_mul_of_le_of_one_lt lt_mul_of_le_of_one_lt
#align lt_add_of_le_of_pos lt_add_of_le_of_pos

/- warning: lt_mul_of_lt_of_one_le -> lt_mul_of_lt_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6461 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6463 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6461 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6463) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6476 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6478 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6476 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6478)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_le lt_mul_of_lt_of_one_leₓ'. -/
@[to_additive]
theorem lt_mul_of_lt_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : 1 ≤ a) : b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ ≤ c * a := mul_le_mul_left' ha c
    
#align lt_mul_of_lt_of_one_le lt_mul_of_lt_of_one_le
#align lt_add_of_lt_of_nonneg lt_add_of_lt_of_nonneg

/- warning: lt_mul_of_lt_of_one_lt -> lt_mul_of_lt_of_one_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6571 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6573 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6571 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6573) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6586 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6588 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6586 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6588)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_lt lt_mul_of_lt_of_one_ltₓ'. -/
@[to_additive]
theorem lt_mul_of_lt_of_one_lt [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b < c)
    (ha : 1 < a) : b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_left' ha c
    
#align lt_mul_of_lt_of_one_lt lt_mul_of_lt_of_one_lt
#align lt_add_of_lt_of_pos lt_add_of_lt_of_pos

/- warning: lt_mul_of_lt_of_one_lt' -> lt_mul_of_lt_of_one_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6681 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6683 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6681 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6683) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6696 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6698 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6696 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6698)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_lt' lt_mul_of_lt_of_one_lt'ₓ'. -/
@[to_additive]
theorem lt_mul_of_lt_of_one_lt' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : 1 < a) : b < c * a :=
  lt_mul_of_lt_of_one_le hbc ha.le
#align lt_mul_of_lt_of_one_lt' lt_mul_of_lt_of_one_lt'
#align lt_add_of_lt_of_pos' lt_add_of_lt_of_pos'

/- warning: left.one_le_mul -> Left.one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6752 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6754 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6752 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6754) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6767 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6769 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6767 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6769)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_le_mul Left.one_le_mulₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_le_mul`. -/
@[to_additive Left.add_nonneg
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_nonneg`."]
theorem Left.one_le_mul [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_le_of_one_le ha hb
#align left.one_le_mul Left.one_le_mul
#align left.add_nonneg Left.add_nonneg

/- warning: left.one_lt_mul_of_le_of_lt -> Left.one_lt_mul_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6823 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6825 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6823 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6825) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6838 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6840 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6838 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6840)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_lt_mul_of_le_of_lt Left.one_lt_mul_of_le_of_ltₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul_of_le_of_lt`. -/
@[to_additive Left.add_pos_of_nonneg_of_pos
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos_of_nonneg_of_pos`."]
theorem Left.one_lt_mul_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : 1 ≤ a)
    (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_le_of_one_lt ha hb
#align left.one_lt_mul_of_le_of_lt Left.one_lt_mul_of_le_of_lt
#align left.add_pos_of_nonneg_of_pos Left.add_pos_of_nonneg_of_pos

/- warning: left.one_lt_mul_of_lt_of_le -> Left.one_lt_mul_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6894 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6896 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6894 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6896) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6909 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6911 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6909 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6911)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_lt_mul_of_lt_of_le Left.one_lt_mul_of_lt_of_leₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul_of_lt_of_le`. -/
@[to_additive Left.add_pos_of_pos_of_nonneg
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos_of_pos_of_nonneg`."]
theorem Left.one_lt_mul_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 < a)
    (hb : 1 ≤ b) : 1 < a * b :=
  lt_mul_of_lt_of_one_le ha hb
#align left.one_lt_mul_of_lt_of_le Left.one_lt_mul_of_lt_of_le
#align left.add_pos_of_pos_of_nonneg Left.add_pos_of_pos_of_nonneg

/- warning: left.one_lt_mul -> Left.one_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6965 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6967 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6965 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6967) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6980 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6982 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6980 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6982)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_lt_mul Left.one_lt_mulₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul`. -/
@[to_additive Left.add_pos
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos`."]
theorem Left.one_lt_mul [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt ha hb
#align left.one_lt_mul Left.one_lt_mul
#align left.add_pos Left.add_pos

/- warning: left.one_lt_mul' -> Left.one_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7036 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7038 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7036 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7038) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7051 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7053 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7051 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7053)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_lt_mul' Left.one_lt_mul'ₓ'. -/
/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul'`. -/
@[to_additive Left.add_pos'
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos'`."]
theorem Left.one_lt_mul' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 < a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_lt' ha hb
#align left.one_lt_mul' Left.one_lt_mul'
#align left.add_pos' Left.add_pos'

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`,
which assume right covariance. -/


/- warning: mul_le_of_le_one_of_le -> mul_le_of_le_one_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7108 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7110 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7108 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7110)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7123 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7125 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7123 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7125)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_of_le mul_le_of_le_one_of_leₓ'. -/
@[to_additive]
theorem mul_le_of_le_one_of_le [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a ≤ 1)
    (hbc : b ≤ c) : a * b ≤ c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := one_mul b
    _ ≤ c := hbc
    
#align mul_le_of_le_one_of_le mul_le_of_le_one_of_le
#align add_le_of_nonpos_of_le add_le_of_nonpos_of_le

/- warning: mul_lt_of_lt_one_of_le -> mul_lt_of_lt_one_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7218 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7220 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7218 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7220)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7233 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7235 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7233 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7235)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_le mul_lt_of_lt_one_of_leₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_one_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : a < 1)
    (hbc : b ≤ c) : a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := one_mul b
    _ ≤ c := hbc
    
#align mul_lt_of_lt_one_of_le mul_lt_of_lt_one_of_le
#align add_lt_of_neg_of_le add_lt_of_neg_of_le

/- warning: mul_lt_of_le_one_of_lt -> mul_lt_of_le_one_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7328 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7330 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7328 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7330)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7343 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7345 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7343 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7345)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_one_of_lt mul_lt_of_le_one_of_ltₓ'. -/
@[to_additive]
theorem mul_lt_of_le_one_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a ≤ 1)
    (hb : b < c) : a * b < c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := one_mul b
    _ < c := hb
    
#align mul_lt_of_le_one_of_lt mul_lt_of_le_one_of_lt
#align add_lt_of_nonpos_of_lt add_lt_of_nonpos_of_lt

/- warning: mul_lt_of_lt_one_of_lt -> mul_lt_of_lt_one_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7438 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7440 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7438 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7440)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7453 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7455 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7453 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7455)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_lt mul_lt_of_lt_one_of_ltₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_one_of_lt [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : a < 1)
    (hb : b < c) : a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := one_mul b
    _ < c := hb
    
#align mul_lt_of_lt_one_of_lt mul_lt_of_lt_one_of_lt
#align add_lt_of_neg_of_lt add_lt_of_neg_of_lt

/- warning: mul_lt_of_lt_one_of_lt' -> mul_lt_of_lt_one_of_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7548 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7550 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7548 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7550)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7563 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7565 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7563 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7565)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_lt' mul_lt_of_lt_one_of_lt'ₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_one_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a < 1)
    (hbc : b < c) : a * b < c :=
  mul_lt_of_le_one_of_lt ha.le hbc
#align mul_lt_of_lt_one_of_lt' mul_lt_of_lt_one_of_lt'
#align add_lt_of_neg_of_lt' add_lt_of_neg_of_lt'

/- warning: right.mul_le_one -> Right.mul_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7622 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7624 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7622 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7624)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7637 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7639 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7637 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7639)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align right.mul_le_one Right.mul_le_oneₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_le_one`. -/
@[to_additive "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_nonpos`."]
theorem Right.mul_le_one [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : a ≤ 1)
    (hb : b ≤ 1) : a * b ≤ 1 :=
  mul_le_of_le_one_of_le ha hb
#align right.mul_le_one Right.mul_le_one
#align right.add_nonpos Right.add_nonpos

/- warning: right.mul_lt_one_of_lt_of_le -> Right.mul_lt_one_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7696 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7698 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7696 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7698)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7711 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7713 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7711 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7713)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_one_of_lt_of_le Right.mul_lt_one_of_lt_of_leₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one_of_lt_of_le`. -/
@[to_additive Right.add_neg_of_neg_of_nonpos
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg_of_neg_of_nonpos`."]
theorem Right.mul_lt_one_of_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
  mul_lt_of_lt_one_of_le ha hb
#align right.mul_lt_one_of_lt_of_le Right.mul_lt_one_of_lt_of_le
#align right.add_neg_of_neg_of_nonpos Right.add_neg_of_neg_of_nonpos

/- warning: right.mul_lt_one_of_le_of_lt -> Right.mul_lt_one_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7770 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7772 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7770 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7772)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7785 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7787 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7785 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7787)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_one_of_le_of_lt Right.mul_lt_one_of_le_of_ltₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one_of_le_of_lt`. -/
@[to_additive Right.add_neg_of_nonpos_of_neg
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg_of_nonpos_of_neg`."]
theorem Right.mul_lt_one_of_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
  mul_lt_of_le_one_of_lt ha hb
#align right.mul_lt_one_of_le_of_lt Right.mul_lt_one_of_le_of_lt
#align right.add_neg_of_nonpos_of_neg Right.add_neg_of_nonpos_of_neg

/- warning: right.mul_lt_one -> Right.mul_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7844 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7846 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7844 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7846)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7859 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7861 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7859 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7861)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_one Right.mul_lt_oneₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one`. -/
@[to_additive "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg`."]
theorem Right.mul_lt_one [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α} (ha : a < 1)
    (hb : b < 1) : a * b < 1 :=
  mul_lt_of_lt_one_of_lt ha hb
#align right.mul_lt_one Right.mul_lt_one
#align right.add_neg Right.add_neg

/- warning: right.mul_lt_one' -> Right.mul_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7918 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7920 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7918 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7920)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7933 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7935 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7933 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7935)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_one' Right.mul_lt_one'ₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one'`. -/
@[to_additive "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg'`."]
theorem Right.mul_lt_one' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : a < 1)
    (hb : b < 1) : a * b < 1 :=
  mul_lt_of_lt_one_of_lt' ha hb
#align right.mul_lt_one' Right.mul_lt_one'
#align right.add_neg' Right.add_neg'

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`,
which assume right covariance. -/


/- warning: le_mul_of_one_le_of_le -> le_mul_of_one_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7990 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7992 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7990 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7992)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8005 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8007 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8005 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8007)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_of_le le_mul_of_one_le_of_leₓ'. -/
@[to_additive]
theorem le_mul_of_one_le_of_le [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 ≤ a)
    (hbc : b ≤ c) : b ≤ a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_right' ha c
    
#align le_mul_of_one_le_of_le le_mul_of_one_le_of_le
#align le_add_of_nonneg_of_le le_add_of_nonneg_of_le

/- warning: lt_mul_of_one_lt_of_le -> lt_mul_of_one_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8103 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8105 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8103 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8105)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8118 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8120 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8118 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8120)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_le lt_mul_of_one_lt_of_leₓ'. -/
@[to_additive]
theorem lt_mul_of_one_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : 1 < a)
    (hbc : b ≤ c) : b < a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_right' ha c
    
#align lt_mul_of_one_lt_of_le lt_mul_of_one_lt_of_le
#align lt_add_of_pos_of_le lt_add_of_pos_of_le

/- warning: lt_mul_of_one_le_of_lt -> lt_mul_of_one_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8216 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8218 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8216 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8218)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8231 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8233 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8231 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8233)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_le_of_lt lt_mul_of_one_le_of_ltₓ'. -/
@[to_additive]
theorem lt_mul_of_one_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 ≤ a)
    (hbc : b < c) : b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ ≤ a * c := mul_le_mul_right' ha c
    
#align lt_mul_of_one_le_of_lt lt_mul_of_one_le_of_lt
#align lt_add_of_nonneg_of_lt lt_add_of_nonneg_of_lt

/- warning: lt_mul_of_one_lt_of_lt -> lt_mul_of_one_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8329 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8331 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8329 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8331)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8344 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8346 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8344 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8346)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_lt lt_mul_of_one_lt_of_ltₓ'. -/
@[to_additive]
theorem lt_mul_of_one_lt_of_lt [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : 1 < a)
    (hbc : b < c) : b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_right' ha c
    
#align lt_mul_of_one_lt_of_lt lt_mul_of_one_lt_of_lt
#align lt_add_of_pos_of_lt lt_add_of_pos_of_lt

/- warning: lt_mul_of_one_lt_of_lt' -> lt_mul_of_one_lt_of_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8442 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8444 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8442 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8444)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8457 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8459 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8457 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8459)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_lt' lt_mul_of_one_lt_of_lt'ₓ'. -/
@[to_additive]
theorem lt_mul_of_one_lt_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 < a)
    (hbc : b < c) : b < a * c :=
  lt_mul_of_one_le_of_lt ha.le hbc
#align lt_mul_of_one_lt_of_lt' lt_mul_of_one_lt_of_lt'
#align lt_add_of_pos_of_lt' lt_add_of_pos_of_lt'

/- warning: right.one_le_mul -> Right.one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8516 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8518 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8516 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8518)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8531 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8533 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8531 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8533)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_le_mul Right.one_le_mulₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_le_mul`. -/
@[to_additive Right.add_nonneg
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_nonneg`."]
theorem Right.one_le_mul [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : 1 ≤ a * b :=
  le_mul_of_one_le_of_le ha hb
#align right.one_le_mul Right.one_le_mul
#align right.add_nonneg Right.add_nonneg

/- warning: right.one_lt_mul_of_lt_of_le -> Right.one_lt_mul_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8590 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8592 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8590 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8592)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8605 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8607 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8605 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8607)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul_of_lt_of_le Right.one_lt_mul_of_lt_of_leₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul_of_lt_of_le`. -/
@[to_additive Right.add_pos_of_pos_of_nonneg
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos_of_pos_of_nonneg`."]
theorem Right.one_lt_mul_of_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
  lt_mul_of_one_lt_of_le ha hb
#align right.one_lt_mul_of_lt_of_le Right.one_lt_mul_of_lt_of_le
#align right.add_pos_of_pos_of_nonneg Right.add_pos_of_pos_of_nonneg

/- warning: right.one_lt_mul_of_le_of_lt -> Right.one_lt_mul_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8664 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8666 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8664 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8666)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8679 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8681 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8679 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8681)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul_of_le_of_lt Right.one_lt_mul_of_le_of_ltₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul_of_le_of_lt`. -/
@[to_additive Right.add_pos_of_nonneg_of_pos
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos_of_nonneg_of_pos`."]
theorem Right.one_lt_mul_of_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_one_le_of_lt ha hb
#align right.one_lt_mul_of_le_of_lt Right.one_lt_mul_of_le_of_lt
#align right.add_pos_of_nonneg_of_pos Right.add_pos_of_nonneg_of_pos

/- warning: right.one_lt_mul -> Right.one_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8738 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8740 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8738 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8740)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8753 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8755 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8753 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8755)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul Right.one_lt_mulₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul`. -/
@[to_additive Right.add_pos
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos`."]
theorem Right.one_lt_mul [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α} (ha : 1 < a)
    (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_lt ha hb
#align right.one_lt_mul Right.one_lt_mul
#align right.add_pos Right.add_pos

/- warning: right.one_lt_mul' -> Right.one_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8812 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8814 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8812 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8814)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8827 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8829 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8827 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8829)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul' Right.one_lt_mul'ₓ'. -/
/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul'`. -/
@[to_additive Right.add_pos'
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos'`."]
theorem Right.one_lt_mul' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 < a)
    (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_lt' ha hb
#align right.one_lt_mul' Right.one_lt_mul'
#align right.add_pos' Right.add_pos'

/- warning: mul_le_one' -> mul_le_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5888 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5890 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5888 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5890) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5903 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5905 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5903 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5905)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_le_one' mul_le_one'ₓ'. -/
alias Left.mul_le_one ← mul_le_one'
#align mul_le_one' mul_le_one'

/- warning: mul_lt_one_of_le_of_lt -> mul_lt_one_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5959 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5961 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5959 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5961) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5974 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5976 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5974 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5976)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_one_of_le_of_lt mul_lt_one_of_le_of_ltₓ'. -/
alias Left.mul_lt_one_of_le_of_lt ← mul_lt_one_of_le_of_lt
#align mul_lt_one_of_le_of_lt mul_lt_one_of_le_of_lt

/- warning: mul_lt_one_of_lt_of_le -> mul_lt_one_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6030 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6032 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6030 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6032) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6045 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6047 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6045 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6047)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_one_of_lt_of_le mul_lt_one_of_lt_of_leₓ'. -/
alias Left.mul_lt_one_of_lt_of_le ← mul_lt_one_of_lt_of_le
#align mul_lt_one_of_lt_of_le mul_lt_one_of_lt_of_le

/- warning: mul_lt_one -> mul_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6101 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6103 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6101 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6103) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6116 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6118 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6116 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6118)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_one mul_lt_oneₓ'. -/
alias Left.mul_lt_one ← mul_lt_one
#align mul_lt_one mul_lt_one

/- warning: mul_lt_one' -> mul_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6172 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6174 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6172 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6174) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6187 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6189 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6187 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6189)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_one' mul_lt_one'ₓ'. -/
alias Left.mul_lt_one' ← mul_lt_one'
#align mul_lt_one' mul_lt_one'

attribute [to_additive add_nonpos "**Alias** of `left.add_nonpos`."] mul_le_one'

attribute [to_additive add_neg_of_nonpos_of_neg "**Alias** of `left.add_neg_of_nonpos_of_neg`."]
  mul_lt_one_of_le_of_lt

attribute [to_additive add_neg_of_neg_of_nonpos "**Alias** of `left.add_neg_of_neg_of_nonpos`."]
  mul_lt_one_of_lt_of_le

attribute [to_additive "**Alias** of `left.add_neg`."] mul_lt_one

attribute [to_additive "**Alias** of `left.add_neg'`."] mul_lt_one'

/- warning: one_le_mul -> one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6752 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6754 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6752 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6754) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6767 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6769 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6767 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6769)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align one_le_mul one_le_mulₓ'. -/
alias Left.one_le_mul ← one_le_mul
#align one_le_mul one_le_mul

/- warning: one_lt_mul_of_le_of_lt' -> one_lt_mul_of_le_of_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6823 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6825 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6823 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6825) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6838 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6840 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6838 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6840)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align one_lt_mul_of_le_of_lt' one_lt_mul_of_le_of_lt'ₓ'. -/
alias Left.one_lt_mul_of_le_of_lt ← one_lt_mul_of_le_of_lt'
#align one_lt_mul_of_le_of_lt' one_lt_mul_of_le_of_lt'

/- warning: one_lt_mul_of_lt_of_le' -> one_lt_mul_of_lt_of_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6894 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6896 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6894 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6896) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6909 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6911 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6909 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6911)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align one_lt_mul_of_lt_of_le' one_lt_mul_of_lt_of_le'ₓ'. -/
alias Left.one_lt_mul_of_lt_of_le ← one_lt_mul_of_lt_of_le'
#align one_lt_mul_of_lt_of_le' one_lt_mul_of_lt_of_le'

/- warning: one_lt_mul' -> one_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6965 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6967 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6965 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6967) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6980 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6982 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6980 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6982)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align one_lt_mul' one_lt_mul'ₓ'. -/
alias Left.one_lt_mul ← one_lt_mul'
#align one_lt_mul' one_lt_mul'

/- warning: one_lt_mul'' -> one_lt_mul'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7036 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7038 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7036 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7038) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7051 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7053 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7051 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7053)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align one_lt_mul'' one_lt_mul''ₓ'. -/
alias Left.one_lt_mul' ← one_lt_mul''
#align one_lt_mul'' one_lt_mul''

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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8920 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8922 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8920 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8922) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8935 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8937 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8935 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8937)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_mul_lt_of_one_le_left lt_of_mul_lt_of_one_le_leftₓ'. -/
@[to_additive]
theorem lt_of_mul_lt_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b < c)
    (hle : 1 ≤ b) : a < c :=
  (le_mul_of_one_le_right' hle).trans_lt h
#align lt_of_mul_lt_of_one_le_left lt_of_mul_lt_of_one_le_left
#align lt_of_add_lt_of_nonneg_left lt_of_add_lt_of_nonneg_left

/- warning: le_of_mul_le_of_one_le_left -> le_of_mul_le_of_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8991 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8993 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8991 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8993) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9006 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9008 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9006 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9008)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_left le_of_mul_le_of_one_le_leftₓ'. -/
@[to_additive]
theorem le_of_mul_le_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b ≤ c)
    (hle : 1 ≤ b) : a ≤ c :=
  (le_mul_of_one_le_right' hle).trans h
#align le_of_mul_le_of_one_le_left le_of_mul_le_of_one_le_left
#align le_of_add_le_of_nonneg_left le_of_add_le_of_nonneg_left

/- warning: lt_of_lt_mul_of_le_one_left -> lt_of_lt_mul_of_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9062 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9064 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9062 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9064) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9077 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9079 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9077 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9079)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_left lt_of_lt_mul_of_le_one_leftₓ'. -/
@[to_additive]
theorem lt_of_lt_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a < b * c)
    (hle : c ≤ 1) : a < b :=
  h.trans_le (mul_le_of_le_one_right' hle)
#align lt_of_lt_mul_of_le_one_left lt_of_lt_mul_of_le_one_left
#align lt_of_lt_add_of_nonpos_left lt_of_lt_add_of_nonpos_left

/- warning: le_of_le_mul_of_le_one_left -> le_of_le_mul_of_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9132 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9134 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9132 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9134) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9147 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9149 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9147 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9149)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b)
Case conversion may be inaccurate. Consider using '#align le_of_le_mul_of_le_one_left le_of_le_mul_of_le_one_leftₓ'. -/
@[to_additive]
theorem le_of_le_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a ≤ b * c)
    (hle : c ≤ 1) : a ≤ b :=
  h.trans (mul_le_of_le_one_right' hle)
#align le_of_le_mul_of_le_one_left le_of_le_mul_of_le_one_left
#align le_of_le_add_of_nonpos_left le_of_le_add_of_nonpos_left

/- warning: lt_of_mul_lt_of_one_le_right -> lt_of_mul_lt_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9205 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9207 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9205 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9207)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9220 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9222 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9220 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9222)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c)
Case conversion may be inaccurate. Consider using '#align lt_of_mul_lt_of_one_le_right lt_of_mul_lt_of_one_le_rightₓ'. -/
@[to_additive]
theorem lt_of_mul_lt_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b < c) (hle : 1 ≤ a) : b < c :=
  (le_mul_of_one_le_left' hle).trans_lt h
#align lt_of_mul_lt_of_one_le_right lt_of_mul_lt_of_one_le_right
#align lt_of_add_lt_of_nonneg_right lt_of_add_lt_of_nonneg_right

/- warning: le_of_mul_le_of_one_le_right -> le_of_mul_le_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9279 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9281 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9279 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9281)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9294 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9296 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9294 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9296)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_right le_of_mul_le_of_one_le_rightₓ'. -/
@[to_additive]
theorem le_of_mul_le_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
  (le_mul_of_one_le_left' hle).trans h
#align le_of_mul_le_of_one_le_right le_of_mul_le_of_one_le_right
#align le_of_add_le_of_nonneg_right le_of_add_le_of_nonneg_right

/- warning: lt_of_lt_mul_of_le_one_right -> lt_of_lt_mul_of_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9353 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9355 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9353 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9355)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9368 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9370 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9368 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9370)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_right lt_of_lt_mul_of_le_one_rightₓ'. -/
@[to_additive]
theorem lt_of_lt_mul_of_le_one_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a < b * c) (hle : b ≤ 1) : a < c :=
  h.trans_le (mul_le_of_le_one_left' hle)
#align lt_of_lt_mul_of_le_one_right lt_of_lt_mul_of_le_one_right
#align lt_of_lt_add_of_nonpos_right lt_of_lt_add_of_nonpos_right

/- warning: le_of_le_mul_of_le_one_right -> le_of_le_mul_of_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9426 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9428 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9426 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9428)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9441 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9443 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9441 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9443)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align le_of_le_mul_of_le_one_right le_of_le_mul_of_le_one_rightₓ'. -/
@[to_additive]
theorem le_of_le_mul_of_le_one_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a ≤ b * c) (hle : b ≤ 1) : a ≤ c :=
  h.trans (mul_le_of_le_one_left' hle)
#align le_of_le_mul_of_le_one_right le_of_le_mul_of_le_one_right
#align le_of_le_add_of_nonpos_right le_of_le_add_of_nonpos_right

end Preorder

section PartialOrder

variable [PartialOrder α]

/- warning: mul_eq_one_iff' -> mul_eq_one_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) (And (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9508 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9510 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9508 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9510) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9523 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9525 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9523 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9525)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9545 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9547 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9545 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9547)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9560 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9562 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9560 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9562)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) (And (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))))
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
#align add_eq_zero_iff' add_eq_zero_iff'

/- warning: mul_le_mul_iff_of_ge -> mul_le_mul_iff_of_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a₁ a₂) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b₁ b₂) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a₂ b₂) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a₁ b₁)) (And (Eq.{succ u1} α a₁ a₂) (Eq.{succ u1} α b₁ b₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9767 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9769 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9767 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9769) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9782 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9784 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9782 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9784)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9804 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9806 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9804 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9806)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9819 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9821 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9819 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9821)] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9838 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9840 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9838 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9840) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9853 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9855 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9853 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9855)] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9875 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9877 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9875 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9877)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9890 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9892 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9890 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9892)] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a₁ a₂) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b₁ b₂) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a₂ b₂) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a₁ b₁)) (And (Eq.{succ u1} α a₁ a₂) (Eq.{succ u1} α b₁ b₂)))
Case conversion may be inaccurate. Consider using '#align mul_le_mul_iff_of_ge mul_le_mul_iff_of_geₓ'. -/
@[to_additive]
theorem mul_le_mul_iff_of_ge [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    a₂ * b₂ ≤ a₁ * b₁ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  by
  refine'
    ⟨fun h => _, by
      rintro ⟨rfl, rfl⟩
      rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and_iff]
  refine' ⟨fun ha => h.not_lt _, fun hb => h.not_lt _⟩
  · exact mul_lt_mul_of_lt_of_le ha hb
  · exact mul_lt_mul_of_le_of_lt ha hb
#align mul_le_mul_iff_of_ge mul_le_mul_iff_of_ge
#align add_le_add_iff_of_ge add_le_add_iff_of_ge

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α}

/- warning: eq_one_of_one_le_mul_left -> eq_one_of_one_le_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10055 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10057 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10055 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10057) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10070 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10072 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10070 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10072)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_leftₓ'. -/
@[to_additive eq_zero_of_add_nonneg_left]
theorem eq_one_of_one_le_mul_left (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : a = 1 :=
  ha.eq_of_not_lt fun h => hab.not_lt <| mul_lt_one_of_lt_of_le h hb
#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_left
#align eq_zero_of_add_nonneg_left eq_zero_of_add_nonneg_left

/- warning: eq_one_of_mul_le_one_left -> eq_one_of_mul_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10134 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10136 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10134 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10136) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10149 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10151 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10149 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10151)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_mul_le_one_left eq_one_of_mul_le_one_leftₓ'. -/
@[to_additive]
theorem eq_one_of_mul_le_one_left (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : a = 1 :=
  ha.eq_of_not_gt fun h => hab.not_lt <| one_lt_mul_of_lt_of_le' h hb
#align eq_one_of_mul_le_one_left eq_one_of_mul_le_one_left
#align eq_zero_of_add_nonpos_left eq_zero_of_add_nonpos_left

end Left

section Right

variable [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}

/- warning: eq_one_of_one_le_mul_right -> eq_one_of_one_le_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10269 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10271 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10269 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10271)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10284 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10286 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10284 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10286)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_rightₓ'. -/
@[to_additive eq_zero_of_add_nonneg_right]
theorem eq_one_of_one_le_mul_right (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : b = 1 :=
  hb.eq_of_not_lt fun h => hab.not_lt <| Right.mul_lt_one_of_le_of_lt ha h
#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_right
#align eq_zero_of_add_nonneg_right eq_zero_of_add_nonneg_right

/- warning: eq_one_of_mul_le_one_right -> eq_one_of_mul_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10351 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10353 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10351 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10353)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10366 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10368 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10366 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10368)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_mul_le_one_right eq_one_of_mul_le_one_rightₓ'. -/
@[to_additive]
theorem eq_one_of_mul_le_one_right (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ 1) : b = 1 :=
  hb.eq_of_not_gt fun h => hab.not_lt <| Right.one_lt_mul_of_le_of_lt ha h
#align eq_one_of_mul_le_one_right eq_one_of_mul_le_one_right
#align eq_zero_of_add_nonpos_right eq_zero_of_add_nonpos_right

end Right

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/- warning: exists_square_le -> exists_square_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] (a : α), Exists.{succ u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10443 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10445 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10443 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10445) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10458 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10460 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10458 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10460)] (a : α), Exists.{succ u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b b) a)
Case conversion may be inaccurate. Consider using '#align exists_square_le exists_square_leₓ'. -/
theorem exists_square_le [CovariantClass α α (· * ·) (· < ·)] (a : α) : ∃ b : α, b * b ≤ a :=
  by
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
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10713 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10715 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10713 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10715) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10728 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10730 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10728 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10730)], LeftCancelSemigroup.{u1} α
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
#align contravariant.to_left_cancel_add_semigroup Contravariant.toAddLeftCancelSemigroup

/- warning: contravariant.to_right_cancel_semigroup -> Contravariant.toRightCancelSemigroup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], RightCancelSemigroup.{u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10796 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10798 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10796 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10798)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10811 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10813 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10811 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10813)], RightCancelSemigroup.{u1} α
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
#align contravariant.to_right_cancel_add_semigroup Contravariant.toAddRightCancelSemigroup

/- warning: left.mul_eq_mul_iff_eq_and_eq -> Left.mul_eq_mul_iff_eq_and_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10876 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10878 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10876 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10878) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10891 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10893 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10891 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10893)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10913 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10915 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10913 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10915)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10928 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10930 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10928 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10930)] [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10947 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10949 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10947 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10949) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10962 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10964 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10962 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10964)] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10984 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10986 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10984 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10986)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10999 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11001 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10999 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11001)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
Case conversion may be inaccurate. Consider using '#align left.mul_eq_mul_iff_eq_and_eq Left.mul_eq_mul_iff_eq_and_eqₓ'. -/
@[to_additive]
theorem Left.mul_eq_mul_iff_eq_and_eq [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] [ContravariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) :
    a * b = c * d ↔ a = c ∧ b = d :=
  by
  refine' ⟨fun h => _, fun h => congr_arg₂ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, mul_left_cancel'' h⟩
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  · exact ⟨mul_right_cancel'' h, rfl⟩
  exact ((Left.mul_lt_mul hac hbd).Ne h).elim
#align left.mul_eq_mul_iff_eq_and_eq Left.mul_eq_mul_iff_eq_and_eq
#align left.add_eq_add_iff_eq_and_eq Left.add_eq_add_iff_eq_and_eq

/- warning: right.mul_eq_mul_iff_eq_and_eq -> Right.mul_eq_mul_iff_eq_and_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11139 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11141 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11139 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11141) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11154 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11156 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11154 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11156)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11173 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11175 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11173 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11175) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11188 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11190 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11188 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11190)] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11210 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11212 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11210 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11212)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11225 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11227 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11225 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11227)] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11247 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11249 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11247 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11249)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11262 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11264 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11262 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11264)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
Case conversion may be inaccurate. Consider using '#align right.mul_eq_mul_iff_eq_and_eq Right.mul_eq_mul_iff_eq_and_eqₓ'. -/
@[to_additive]
theorem Right.mul_eq_mul_iff_eq_and_eq [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) :
    a * b = c * d ↔ a = c ∧ b = d :=
  by
  refine' ⟨fun h => _, fun h => congr_arg₂ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, mul_left_cancel'' h⟩
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  · exact ⟨mul_right_cancel'' h, rfl⟩
  exact ((Right.mul_lt_mul hac hbd).Ne h).elim
#align right.mul_eq_mul_iff_eq_and_eq Right.mul_eq_mul_iff_eq_and_eq
#align right.add_eq_add_iff_eq_and_eq Right.add_eq_add_iff_eq_and_eq

/- warning: mul_eq_mul_iff_eq_and_eq -> mul_eq_mul_iff_eq_and_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10876 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10878 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10876 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10878) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10891 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10893 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10891 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10893)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10913 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10915 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10913 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10915)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10928 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10930 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10928 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10930)] [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10947 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10949 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10947 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10949) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10962 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10964 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10962 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10964)] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10984 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10986 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10984 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10986)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10999 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11001 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10999 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11001)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
Case conversion may be inaccurate. Consider using '#align mul_eq_mul_iff_eq_and_eq mul_eq_mul_iff_eq_and_eqₓ'. -/
alias Left.mul_eq_mul_iff_eq_and_eq ← mul_eq_mul_iff_eq_and_eq
#align mul_eq_mul_iff_eq_and_eq mul_eq_mul_iff_eq_and_eq

attribute [to_additive] mul_eq_mul_iff_eq_and_eq

end PartialOrder

end Semigroup

section Mono

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

/- warning: monotone.const_mul' -> Monotone.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11446 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11448 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11446 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11448) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11461 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11463 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11461 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11463)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.const_mul' Monotone.const_mul'ₓ'. -/
@[to_additive const_add]
theorem Monotone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a
#align monotone.const_mul' Monotone.const_mul'
#align monotone.const_add Monotone.const_add

/- warning: monotone_on.const_mul' -> MonotoneOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11532 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11534 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11532 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11534) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11547 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11549 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11547 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11549)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.const_mul' MonotoneOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem MonotoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a
#align monotone_on.const_mul' MonotoneOn.const_mul'
#align monotone_on.const_add MonotoneOn.const_add

/- warning: antitone.const_mul' -> Antitone.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11626 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11628 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11626 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11628) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11641 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11643 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11641 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11643)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.const_mul' Antitone.const_mul'ₓ'. -/
@[to_additive const_add]
theorem Antitone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a
#align antitone.const_mul' Antitone.const_mul'
#align antitone.const_add Antitone.const_add

/- warning: antitone_on.const_mul' -> AntitoneOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11712 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11714 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11712 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11714) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11727 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11729 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11727 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11729)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.const_mul' AntitoneOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem AntitoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a
#align antitone_on.const_mul' AntitoneOn.const_mul'
#align antitone_on.const_add AntitoneOn.const_add

/- warning: monotone.mul_const' -> Monotone.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11809 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11811 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11809 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11811)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11824 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11826 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11824 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11826)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a))
Case conversion may be inaccurate. Consider using '#align monotone.mul_const' Monotone.mul_const'ₓ'. -/
@[to_additive add_const]
theorem Monotone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a
#align monotone.mul_const' Monotone.mul_const'
#align monotone.add_const Monotone.add_const

/- warning: monotone_on.mul_const' -> MonotoneOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11898 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11900 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11898 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11900)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11913 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11915 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11913 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11915)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.mul_const' MonotoneOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem MonotoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s)
    (a : α) : MonotoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a
#align monotone_on.mul_const' MonotoneOn.mul_const'
#align monotone_on.add_const MonotoneOn.add_const

/- warning: antitone.mul_const' -> Antitone.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11995 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11997 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11995 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11997)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12010 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12012 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12010 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12012)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a))
Case conversion may be inaccurate. Consider using '#align antitone.mul_const' Antitone.mul_const'ₓ'. -/
@[to_additive add_const]
theorem Antitone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a
#align antitone.mul_const' Antitone.mul_const'
#align antitone.add_const Antitone.add_const

/- warning: antitone_on.mul_const' -> AntitoneOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12084 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12086 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12084 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12086)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12099 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12101 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12099 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12101)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.mul_const' AntitoneOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem AntitoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : AntitoneOn f s)
    (a : α) : AntitoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a
#align antitone_on.mul_const' AntitoneOn.mul_const'
#align antitone_on.add_const AntitoneOn.add_const

/- warning: monotone.mul' -> Monotone.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (Monotone.{u2, u1} β α _inst_3 _inst_2 g) -> (Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12178 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12180 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12178 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12180) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12193 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12195 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12193 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12195)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12215 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12217 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12215 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12217)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12230 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12232 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12230 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12232)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (Monotone.{u1, u2} β α _inst_3 _inst_2 g) -> (Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.mul' Monotone.mul'ₓ'. -/
/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem Monotone.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x * g x := fun x y h => mul_le_mul' (hf h) (hg h)
#align monotone.mul' Monotone.mul'
#align monotone.add Monotone.add

/- warning: monotone_on.mul' -> MonotoneOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12306 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12308 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12306 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12308) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12321 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12323 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12321 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12323)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12343 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12345 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12343 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12345)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12358 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12360 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12358 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12360)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.mul' MonotoneOn.mul'ₓ'. -/
/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem MonotoneOn.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x * g x) s := fun x hx y hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)
#align monotone_on.mul' MonotoneOn.mul'
#align monotone_on.add MonotoneOn.add

/- warning: antitone.mul' -> Antitone.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (Antitone.{u2, u1} β α _inst_3 _inst_2 g) -> (Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12445 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12447 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12445 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12447) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12460 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12462 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12460 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12462)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12482 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12484 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12482 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12484)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12497 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12499 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12497 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12499)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (Antitone.{u1, u2} β α _inst_3 _inst_2 g) -> (Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.mul' Antitone.mul'ₓ'. -/
/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem Antitone.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x * g x := fun x y h => mul_le_mul' (hf h) (hg h)
#align antitone.mul' Antitone.mul'
#align antitone.add Antitone.add

/- warning: antitone_on.mul' -> AntitoneOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12573 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12575 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12573 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12575) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12588 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12590 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12588 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12590)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12610 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12612 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12610 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12612)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12625 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12627 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12625 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12627)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.mul' AntitoneOn.mul'ₓ'. -/
/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem AntitoneOn.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x * g x) s := fun x hx y hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)
#align antitone_on.mul' AntitoneOn.mul'
#align antitone_on.add AntitoneOn.add

section Left

variable [CovariantClass α α (· * ·) (· < ·)]

#print StrictMono.const_mul' /-
@[to_additive const_add]
theorem StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c * f x :=
  fun a b ab => mul_lt_mul_left' (hf ab) c
#align strict_mono.const_mul' StrictMono.const_mul'
#align strict_mono.const_add StrictMono.const_add
-/

#print StrictMonoOn.const_mul' /-
@[to_additive const_add]
theorem StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => c * f x) s := fun a ha b hb ab => mul_lt_mul_left' (hf ha hb ab) c
#align strict_mono_on.const_mul' StrictMonoOn.const_mul'
#align strict_mono_on.const_add StrictMonoOn.const_add
-/

#print StrictAnti.const_mul' /-
@[to_additive const_add]
theorem StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c * f x :=
  fun a b ab => mul_lt_mul_left' (hf ab) c
#align strict_anti.const_mul' StrictAnti.const_mul'
#align strict_anti.const_add StrictAnti.const_add
-/

#print StrictAntiOn.const_mul' /-
@[to_additive const_add]
theorem StrictAntiOn.const_mul' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => c * f x) s := fun a ha b hb ab => mul_lt_mul_left' (hf ha hb ab) c
#align strict_anti_on.const_mul' StrictAntiOn.const_mul'
#align strict_anti_on.const_add StrictAntiOn.const_add
-/

end Left

section Right

variable [CovariantClass α α (swap (· * ·)) (· < ·)]

#print StrictMono.mul_const' /-
@[to_additive add_const]
theorem StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f x * c :=
  fun a b ab => mul_lt_mul_right' (hf ab) c
#align strict_mono.mul_const' StrictMono.mul_const'
#align strict_mono.add_const StrictMono.add_const
-/

#print StrictMonoOn.mul_const' /-
@[to_additive add_const]
theorem StrictMonoOn.mul_const' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => f x * c) s := fun a ha b hb ab => mul_lt_mul_right' (hf ha hb ab) c
#align strict_mono_on.mul_const' StrictMonoOn.mul_const'
#align strict_mono_on.add_const StrictMonoOn.add_const
-/

#print StrictAnti.mul_const' /-
@[to_additive add_const]
theorem StrictAnti.mul_const' (hf : StrictAnti f) (c : α) : StrictAnti fun x => f x * c :=
  fun a b ab => mul_lt_mul_right' (hf ab) c
#align strict_anti.mul_const' StrictAnti.mul_const'
#align strict_anti.add_const StrictAnti.add_const
-/

#print StrictAntiOn.mul_const' /-
@[to_additive add_const]
theorem StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => f x * c) s := fun a ha b hb ab => mul_lt_mul_right' (hf ha hb ab) c
#align strict_anti_on.mul_const' StrictAntiOn.mul_const'
#align strict_anti_on.add_const StrictAntiOn.add_const
-/

end Right

/- warning: strict_mono.mul' -> StrictMono.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))], (StrictMono.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13561 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13563 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13561 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13563) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13576 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13578 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13576 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13578)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13598 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13600 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13598 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13600)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13613 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13615 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13613 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13615)], (StrictMono.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align strict_mono.mul' StrictMono.mul'ₓ'. -/
/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMono.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono fun x => f x * g x := fun a b ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)
#align strict_mono.mul' StrictMono.mul'
#align strict_mono.add StrictMono.add

/- warning: strict_mono_on.mul' -> StrictMonoOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))], (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13689 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13691 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13689 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13691) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13704 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13706 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13704 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13706)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13726 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13728 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13726 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13728)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13741 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13743 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13741 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13743)], (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.mul' StrictMonoOn.mul'ₓ'. -/
/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMonoOn.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictMonoOn f s) (hg : StrictMonoOn g s) :
    StrictMonoOn (fun x => f x * g x) s := fun a ha b hb ab =>
  mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)
#align strict_mono_on.mul' StrictMonoOn.mul'
#align strict_mono_on.add StrictMonoOn.add

/- warning: strict_anti.mul' -> StrictAnti.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))], (StrictAnti.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13828 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13830 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13828 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13830) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13843 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13845 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13843 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13845)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13865 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13867 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13865 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13867)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13880 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13882 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13880 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13882)], (StrictAnti.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align strict_anti.mul' StrictAnti.mul'ₓ'. -/
/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAnti.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictAnti f) (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x := fun a b ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)
#align strict_anti.mul' StrictAnti.mul'
#align strict_anti.add StrictAnti.add

/- warning: strict_anti_on.mul' -> StrictAntiOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))], (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13956 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13958 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13956 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13958) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13971 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13973 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13971 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13973)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13993 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13995 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13993 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13995)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14008 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14010 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14008 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14010)], (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.mul' StrictAntiOn.mul'ₓ'. -/
/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAntiOn.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictAntiOn f s) (hg : StrictAntiOn g s) :
    StrictAntiOn (fun x => f x * g x) s := fun a ha b hb ab =>
  mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)
#align strict_anti_on.mul' StrictAntiOn.mul'
#align strict_anti_on.add StrictAntiOn.add

/- warning: monotone.mul_strict_mono' -> Monotone.mul_strictMono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14095 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14097 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14095 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14097) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14110 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14112 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14110 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14112)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14132 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14134 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14132 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14134)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14147 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14149 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14147 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14149)] {f : β -> α} {g : β -> α}, (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.mul_strict_mono' Monotone.mul_strictMono'ₓ'. -/
/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strict_mono
      "The sum of a monotone function and a strictly monotone function is strictly monotone."]
theorem Monotone.mul_strictMono' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : Monotone f)
    (hg : StrictMono g) : StrictMono fun x => f x * g x := fun x y h =>
  mul_lt_mul_of_le_of_lt (hf h.le) (hg h)
#align monotone.mul_strict_mono' Monotone.mul_strictMono'
#align monotone.add_strict_mono Monotone.add_strictMono

/- warning: monotone_on.mul_strict_mono' -> MonotoneOn.mul_strictMono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14229 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14231 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14229 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14231) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14244 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14246 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14244 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14246)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14266 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14268 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14266 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14268)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14281 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14283 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14281 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14283)] {f : β -> α} {g : β -> α}, (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.mul_strict_mono' MonotoneOn.mul_strictMono'ₓ'. -/
/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strict_mono
      "The sum of a monotone function and a strictly monotone function is strictly monotone."]
theorem MonotoneOn.mul_strictMono' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : MonotoneOn f s)
    (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)
#align monotone_on.mul_strict_mono' MonotoneOn.mul_strictMono'
#align monotone_on.add_strict_mono MonotoneOn.add_strictMono

/- warning: antitone.mul_strict_anti' -> Antitone.mul_strictAnti' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14374 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14376 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14374 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14376) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14389 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14391 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14389 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14391)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14411 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14413 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14411 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14413)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14426 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14428 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14426 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14428)] {f : β -> α} {g : β -> α}, (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.mul_strict_anti' Antitone.mul_strictAnti'ₓ'. -/
/-- The product of a antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strict_anti
      "The sum of a antitone function and a strictly antitone function is strictly antitone."]
theorem Antitone.mul_strictAnti' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : Antitone f)
    (hg : StrictAnti g) : StrictAnti fun x => f x * g x := fun x y h =>
  mul_lt_mul_of_le_of_lt (hf h.le) (hg h)
#align antitone.mul_strict_anti' Antitone.mul_strictAnti'
#align antitone.add_strict_anti Antitone.add_strictAnti

/- warning: antitone_on.mul_strict_anti' -> AntitoneOn.mul_strictAnti' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14508 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14510 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14508 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14510) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14523 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14525 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14523 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14525)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14545 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14547 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14545 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14547)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14560 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14562 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14560 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14562)] {f : β -> α} {g : β -> α}, (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.mul_strict_anti' AntitoneOn.mul_strictAnti'ₓ'. -/
/-- The product of a antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strict_anti
      "The sum of a antitone function and a strictly antitone function is strictly antitone."]
theorem AntitoneOn.mul_strictAnti' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {f g : β → α} (hf : AntitoneOn f s)
    (hg : StrictAntiOn g s) : StrictAntiOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)
#align antitone_on.mul_strict_anti' AntitoneOn.mul_strictAnti'
#align antitone_on.add_strict_anti AntitoneOn.add_strictAnti

variable [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]

#print StrictMono.mul_monotone' /-
/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone
      "The sum of a strictly monotone function and a monotone function is strictly monotone."]
theorem StrictMono.mul_monotone' (hf : StrictMono f) (hg : Monotone g) :
    StrictMono fun x => f x * g x := fun x y h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)
#align strict_mono.mul_monotone' StrictMono.mul_monotone'
#align strict_mono.add_monotone StrictMono.add_monotone
-/

#print StrictMonoOn.mul_monotone' /-
/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone
      "The sum of a strictly monotone function and a monotone function is strictly monotone."]
theorem StrictMonoOn.mul_monotone' (hf : StrictMonoOn f s) (hg : MonotoneOn g s) :
    StrictMonoOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)
#align strict_mono_on.mul_monotone' StrictMonoOn.mul_monotone'
#align strict_mono_on.add_monotone StrictMonoOn.add_monotone
-/

#print StrictAnti.mul_antitone' /-
/-- The product of a strictly antitone function and a antitone function is strictly antitone. -/
@[to_additive add_antitone
      "The sum of a strictly antitone function and a antitone function is strictly antitone."]
theorem StrictAnti.mul_antitone' (hf : StrictAnti f) (hg : Antitone g) :
    StrictAnti fun x => f x * g x := fun x y h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)
#align strict_anti.mul_antitone' StrictAnti.mul_antitone'
#align strict_anti.add_antitone StrictAnti.add_antitone
-/

#print StrictAntiOn.mul_antitone' /-
/-- The product of a strictly antitone function and a antitone function is strictly antitone. -/
@[to_additive add_antitone
      "The sum of a strictly antitone function and a antitone function is strictly antitone."]
theorem StrictAntiOn.mul_antitone' (hf : StrictAntiOn f s) (hg : AntitoneOn g s) :
    StrictAntiOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)
#align strict_anti_on.mul_antitone' StrictAntiOn.mul_antitone'
#align strict_anti_on.add_antitone StrictAntiOn.add_antitone
-/

#print cmp_mul_left' /-
@[simp, to_additive cmp_add_left]
theorem cmp_mul_left' {α : Type _} [Mul α] [LinearOrder α] [CovariantClass α α (· * ·) (· < ·)]
    (a b c : α) : cmp (a * b) (a * c) = cmp b c :=
  (strictMono_id.const_mul' a).cmp_map_eq b c
#align cmp_mul_left' cmp_mul_left'
#align cmp_add_left cmp_add_left
-/

#print cmp_mul_right' /-
@[simp, to_additive cmp_add_right]
theorem cmp_mul_right' {α : Type _} [Mul α] [LinearOrder α]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (a b c : α) : cmp (a * c) (b * c) = cmp a b :=
  (strictMono_id.mul_const' c).cmp_map_eq a b
#align cmp_mul_right' cmp_mul_right'
#align cmp_add_right cmp_add_right
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
#align add_le_cancellable AddLECancellable
-/

#print Contravariant.MulLECancellable /-
@[to_additive]
theorem Contravariant.MulLECancellable [Mul α] [LE α] [ContravariantClass α α (· * ·) (· ≤ ·)]
    {a : α} : MulLECancellable a := fun b c => le_of_mul_le_mul_left'
#align contravariant.mul_le_cancellable Contravariant.MulLECancellable
#align contravariant.add_le_cancellable Contravariant.AddLECancellable
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
#align add_le_cancellable_zero addLECancellable_zero

namespace MulLECancellable

#print MulLECancellable.Injective /-
@[to_additive]
protected theorem Injective [Mul α] [PartialOrder α] {a : α} (ha : MulLECancellable a) :
    Injective ((· * ·) a) := fun b c h => le_antisymm (ha h.le) (ha h.ge)
#align mul_le_cancellable.injective MulLECancellable.Injective
#align add_le_cancellable.injective AddLECancellable.Injective
-/

#print MulLECancellable.inj /-
@[to_additive]
protected theorem inj [Mul α] [PartialOrder α] {a b c : α} (ha : MulLECancellable a) :
    a * b = a * c ↔ b = c :=
  ha.Injective.eq_iff
#align mul_le_cancellable.inj MulLECancellable.inj
#align add_le_cancellable.inj AddLECancellable.inj
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
#align add_le_cancellable.injective_left AddLECancellable.injective_left

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
#align add_le_cancellable.inj_left AddLECancellable.inj_left

variable [LE α]

#print MulLECancellable.mul_le_mul_iff_left /-
@[to_additive]
protected theorem mul_le_mul_iff_left [Mul α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α}
    (ha : MulLECancellable a) : a * b ≤ a * c ↔ b ≤ c :=
  ⟨fun h => ha h, fun h => mul_le_mul_left' h a⟩
#align mul_le_cancellable.mul_le_mul_iff_left MulLECancellable.mul_le_mul_iff_left
#align add_le_cancellable.add_le_add_iff_left AddLECancellable.add_le_add_iff_left
-/

/- warning: mul_le_cancellable.mul_le_mul_iff_right -> MulLECancellable.mul_le_mul_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommSemigroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)))) (LE.le.{u1} α _inst_1)] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) b a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) c a)) (LE.le.{u1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommSemigroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16001 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16003 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16001 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16003) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16016 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16018 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16016 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16018)] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) b a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) c a)) (LE.le.{u1} α _inst_1 b c))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.mul_le_mul_iff_right MulLECancellable.mul_le_mul_iff_rightₓ'. -/
@[to_additive]
protected theorem mul_le_mul_iff_right [CommSemigroup α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b c : α} (ha : MulLECancellable a) : b * a ≤ c * a ↔ b ≤ c := by
  rw [mul_comm b, mul_comm c, ha.mul_le_mul_iff_left]
#align mul_le_cancellable.mul_le_mul_iff_right MulLECancellable.mul_le_mul_iff_right
#align add_le_cancellable.add_le_add_iff_right AddLECancellable.add_le_add_iff_right

/- warning: mul_le_cancellable.le_mul_iff_one_le_right -> MulLECancellable.le_mul_iff_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2))) (LE.le.{u1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2)))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16100 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16102 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16100 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16102) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16115 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16117 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16115 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16117)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) b))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.le_mul_iff_one_le_right MulLECancellable.le_mul_iff_one_le_rightₓ'. -/
@[to_additive]
protected theorem le_mul_iff_one_le_right [MulOneClass α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left
#align mul_le_cancellable.le_mul_iff_one_le_right MulLECancellable.le_mul_iff_one_le_right
#align add_le_cancellable.le_add_iff_nonneg_right AddLECancellable.le_add_iff_nonneg_right

/- warning: mul_le_cancellable.mul_le_iff_le_one_right -> MulLECancellable.mul_le_iff_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2))) (LE.le.{u1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_2)) a b) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_2))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16196 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16198 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16196 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16198) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16211 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16213 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16211 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16213)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2)))))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.mul_le_iff_le_one_right MulLECancellable.mul_le_iff_le_one_rightₓ'. -/
@[to_additive]
protected theorem mul_le_iff_le_one_right [MulOneClass α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left
#align mul_le_cancellable.mul_le_iff_le_one_right MulLECancellable.mul_le_iff_le_one_right
#align add_le_cancellable.add_le_iff_nonpos_right AddLECancellable.add_le_iff_nonpos_right

/- warning: mul_le_cancellable.le_mul_iff_one_le_left -> MulLECancellable.le_mul_iff_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))))) (LE.le.{u1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16292 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16294 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16292 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16294) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16307 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16309 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16307 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16309)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.le_mul_iff_one_le_left MulLECancellable.le_mul_iff_one_le_leftₓ'. -/
@[to_additive]
protected theorem le_mul_iff_one_le_left [CommMonoid α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : a ≤ b * a ↔ 1 ≤ b := by
  rw [mul_comm, ha.le_mul_iff_one_le_right]
#align mul_le_cancellable.le_mul_iff_one_le_left MulLECancellable.le_mul_iff_one_le_left
#align add_le_cancellable.le_add_iff_nonneg_left AddLECancellable.le_add_iff_nonneg_left

/- warning: mul_le_cancellable.mul_le_iff_le_one_left -> MulLECancellable.mul_le_iff_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))))) (LE.le.{u1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16385 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16387 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16385 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16387) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16400 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16402 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16400 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16402)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))))))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.mul_le_iff_le_one_left MulLECancellable.mul_le_iff_le_one_leftₓ'. -/
@[to_additive]
protected theorem mul_le_iff_le_one_left [CommMonoid α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : b * a ≤ a ↔ b ≤ 1 := by
  rw [mul_comm, ha.mul_le_iff_le_one_right]
#align mul_le_cancellable.mul_le_iff_le_one_left MulLECancellable.mul_le_iff_le_one_left
#align add_le_cancellable.add_le_iff_nonpos_left AddLECancellable.add_le_iff_nonpos_left

end MulLECancellable

section Bit

variable [Add α] [Preorder α]

#print bit0_mono /-
theorem bit0_mono [CovariantClass α α (· + ·) (· ≤ ·)] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    Monotone (bit0 : α → α) := fun a b h => add_le_add h h
#align bit0_mono bit0_mono
-/

#print bit0_strictMono /-
theorem bit0_strictMono [CovariantClass α α (· + ·) (· < ·)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] : StrictMono (bit0 : α → α) := fun a b h =>
  add_lt_add h h
#align bit0_strict_mono bit0_strictMono
-/

end Bit

