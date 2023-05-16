/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa,
Yuyang Zhao

! This file was ported from Lean 3 source module algebra.order.monoid.lemmas
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
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

/- warning: mul_lt_mul_of_lt_of_lt -> mul_lt_mul_of_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1146 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1148 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1146 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1148) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1161 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1163 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1161 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1163)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1183 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1185 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1183 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1185)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1198 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1200 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1198 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1200)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align mul_lt_mul_of_lt_of_lt mul_lt_mul_of_lt_of_ltₓ'. -/
@[to_additive]
theorem mul_lt_mul_of_lt_of_lt [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  calc
    a * c < a * d := mul_lt_mul_left' h₂ a
    _ < b * d := mul_lt_mul_right' h₁ d
    
#align mul_lt_mul_of_lt_of_lt mul_lt_mul_of_lt_of_lt
#align add_lt_add_of_lt_of_lt add_lt_add_of_lt_of_lt

/- warning: add_lt_add -> add_lt_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1146 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1148 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1146 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1148) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1161 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1163 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1161 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1163)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1183 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1185 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1183 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1185)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1198 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1200 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1198 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1200)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) a c) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align add_lt_add add_lt_addₓ'. -/
alias add_lt_add_of_lt_of_lt ← add_lt_add
#align add_lt_add add_lt_add

/- warning: mul_lt_mul_of_le_of_lt -> mul_lt_mul_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1286 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1288 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1286 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1288) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1301 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1303 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1301 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1303)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1323 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1325 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1323 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1325)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1338 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1340 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1338 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1340)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align mul_lt_mul_of_le_of_lt mul_lt_mul_of_le_of_ltₓ'. -/
@[to_additive]
theorem mul_lt_mul_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) :
    a * c < b * d :=
  (mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)
#align mul_lt_mul_of_le_of_lt mul_lt_mul_of_le_of_lt
#align add_lt_add_of_le_of_lt add_lt_add_of_le_of_lt

/- warning: mul_lt_mul_of_lt_of_le -> mul_lt_mul_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1402 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1404 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1402 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1404) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1417 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1419 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1417 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1419)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1439 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1441 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1439 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1441)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1454 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1456 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1454 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1456)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align mul_lt_mul_of_lt_of_le mul_lt_mul_of_lt_of_leₓ'. -/
@[to_additive]
theorem mul_lt_mul_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) :
    a * c < b * d :=
  (mul_le_mul_left' h₂ _).trans_lt (mul_lt_mul_right' h₁ d)
#align mul_lt_mul_of_lt_of_le mul_lt_mul_of_lt_of_le
#align add_lt_add_of_lt_of_le add_lt_add_of_lt_of_le

/- warning: left.mul_lt_mul -> Left.mul_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1521 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1523 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1521 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1523) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1536 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1538 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1536 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1538)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1558 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1560 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1558 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1560)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1573 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1575 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1573 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1575)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_mul Left.mul_lt_mulₓ'. -/
/-- Only assumes left strict covariance. -/
@[to_additive "Only assumes left strict covariance"]
theorem Left.mul_lt_mul [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_le_of_lt h₁.le h₂
#align left.mul_lt_mul Left.mul_lt_mul
#align left.add_lt_add Left.add_lt_add

/- warning: right.mul_lt_mul -> Right.mul_lt_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1633 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1635 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1633 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1635) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1648 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1650 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1648 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1650)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1670 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1672 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1670 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1672)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1685 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1687 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1685 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1687)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_mul Right.mul_lt_mulₓ'. -/
/-- Only assumes right strict covariance. -/
@[to_additive "Only assumes right strict covariance"]
theorem Right.mul_lt_mul [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α} (h₁ : a < b) (h₂ : c < d) :
    a * c < b * d :=
  mul_lt_mul_of_lt_of_le h₁ h₂.le
#align right.mul_lt_mul Right.mul_lt_mul
#align right.add_lt_add Right.add_lt_add

/- warning: mul_le_mul' -> mul_le_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) c d) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1742 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1744 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1742 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1744) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1757 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1759 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1757 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1759)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1779 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1781 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1779 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1781)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1794 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1796 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1794 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1796)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align mul_le_mul' mul_le_mul'ₓ'. -/
@[to_additive add_le_add]
theorem mul_le_mul' [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)
#align mul_le_mul' mul_le_mul'
#align add_le_add add_le_add

/- warning: mul_le_mul_three -> mul_le_mul_three is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α} {e : α} {f : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a d) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b e) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) c f) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) d e) f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1858 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1860 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1858 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1860) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1873 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1875 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1873 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1875)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1895 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1897 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1895 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1897)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1910 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1912 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1910 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1912)] {a : α} {b : α} {c : α} {d : α} {e : α} {f : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b e) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c f) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) d e) f))
Case conversion may be inaccurate. Consider using '#align mul_le_mul_three mul_le_mul_threeₓ'. -/
@[to_additive]
theorem mul_le_mul_three [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e)
    (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
  mul_le_mul' (mul_le_mul' h₁ h₂) h₃
#align mul_le_mul_three mul_le_mul_three
#align add_le_add_three add_le_add_three

/- warning: mul_lt_of_mul_lt_left -> mul_lt_of_mul_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) d b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a d) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1981 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1983 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1981 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1983) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1996 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1998 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1996 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.1998)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) d b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a d) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_mul_lt_left mul_lt_of_mul_lt_leftₓ'. -/
@[to_additive]
theorem mul_lt_of_mul_lt_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a * b < c)
    (hle : d ≤ b) : a * d < c :=
  (mul_le_mul_left' hle a).trans_lt h
#align mul_lt_of_mul_lt_left mul_lt_of_mul_lt_left
#align add_lt_of_add_lt_left add_lt_of_add_lt_left

/- warning: mul_le_of_mul_le_left -> mul_le_of_mul_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) d b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a d) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2056 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2058 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2056 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2058) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2071 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2073 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2071 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2073)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) d b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a d) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_mul_le_left mul_le_of_mul_le_leftₓ'. -/
@[to_additive]
theorem mul_le_of_mul_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a * b ≤ c)
    (hle : d ≤ b) : a * d ≤ c :=
  @act_rel_of_rel_of_act_rel _ _ _ (· ≤ ·) _ ⟨fun _ _ _ => le_trans⟩ a _ _ _ hle h
#align mul_le_of_mul_le_left mul_le_of_mul_le_left
#align add_le_of_add_le_left add_le_of_add_le_left

/- warning: mul_lt_of_mul_lt_right -> mul_lt_of_mul_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) d a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) d b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2152 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2154 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2152 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2154)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2167 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2169 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2167 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2169)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) d a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) d b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_mul_lt_right mul_lt_of_mul_lt_rightₓ'. -/
@[to_additive]
theorem mul_lt_of_mul_lt_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a * b < c) (hle : d ≤ a) : d * b < c :=
  (mul_le_mul_right' hle b).trans_lt h
#align mul_lt_of_mul_lt_right mul_lt_of_mul_lt_right
#align add_lt_of_add_lt_right add_lt_of_add_lt_right

/- warning: mul_le_of_mul_le_right -> mul_le_of_mul_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) d a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) d b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2230 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2232 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2230 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2232)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2245 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2247 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2245 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2247)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) d a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) d b) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_mul_le_right mul_le_of_mul_le_rightₓ'. -/
@[to_additive]
theorem mul_le_of_mul_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a * b ≤ c) (hle : d ≤ a) : d * b ≤ c :=
  (mul_le_mul_right' hle b).trans h
#align mul_le_of_mul_le_right mul_le_of_mul_le_right
#align add_le_of_add_le_right add_le_of_add_le_right

/- warning: lt_mul_of_lt_mul_left -> lt_mul_of_lt_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b c)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2305 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2307 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2305 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2307) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2320 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2322 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2320 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2322)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_mul_left lt_mul_of_lt_mul_leftₓ'. -/
@[to_additive]
theorem lt_mul_of_lt_mul_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a < b * c)
    (hle : c ≤ d) : a < b * d :=
  h.trans_le (mul_le_mul_left' hle b)
#align lt_mul_of_lt_mul_left lt_mul_of_lt_mul_left
#align lt_add_of_lt_add_left lt_add_of_lt_add_left

/- warning: le_mul_of_le_mul_left -> le_mul_of_le_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b c)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) c d) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2379 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2381 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2379 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2381) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2394 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2396 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2394 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2396)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b d))
Case conversion may be inaccurate. Consider using '#align le_mul_of_le_mul_left le_mul_of_le_mul_leftₓ'. -/
@[to_additive]
theorem le_mul_of_le_mul_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a ≤ b * c)
    (hle : c ≤ d) : a ≤ b * d :=
  @rel_act_of_rel_of_rel_act _ _ _ (· ≤ ·) _ ⟨fun _ _ _ => le_trans⟩ b _ _ _ hle h
#align le_mul_of_le_mul_left le_mul_of_le_mul_left
#align le_add_of_le_add_left le_add_of_le_add_left

/- warning: lt_mul_of_lt_mul_right -> lt_mul_of_lt_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b c)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b d) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) d c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2475 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2477 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2475 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2477)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2490 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2492 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2490 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2492)] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b d) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) d c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_mul_right lt_mul_of_lt_mul_rightₓ'. -/
@[to_additive]
theorem lt_mul_of_lt_mul_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a < b * c) (hle : b ≤ d) : a < d * c :=
  h.trans_le (mul_le_mul_right' hle c)
#align lt_mul_of_lt_mul_right lt_mul_of_lt_mul_right
#align lt_add_of_lt_add_right lt_add_of_lt_add_right

/- warning: le_mul_of_le_mul_right -> le_mul_of_le_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b c)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b d) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) d c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2552 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2554 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2552 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2554)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2567 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2569 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2567 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2569)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b d) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) d c))
Case conversion may be inaccurate. Consider using '#align le_mul_of_le_mul_right le_mul_of_le_mul_rightₓ'. -/
@[to_additive]
theorem le_mul_of_le_mul_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h : a ≤ b * c) (hle : b ≤ d) : a ≤ d * c :=
  h.trans (mul_le_mul_right' hle c)
#align le_mul_of_le_mul_right le_mul_of_le_mul_right
#align le_add_of_le_add_right le_add_of_le_add_right

end Preorder

section PartialOrder

variable [PartialOrder α]

/- warning: mul_left_cancel'' -> mul_left_cancel'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α} {c : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c)) -> (Eq.{succ u1} α b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2638 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2640 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2638 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2640) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2653 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2655 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2653 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2655)] {a : α} {b : α} {c : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c)) -> (Eq.{succ u1} α b c)
Case conversion may be inaccurate. Consider using '#align mul_left_cancel'' mul_left_cancel''ₓ'. -/
@[to_additive]
theorem mul_left_cancel'' [ContravariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b = a * c) :
    b = c :=
  (le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.ge)
#align mul_left_cancel'' mul_left_cancel''
#align add_left_cancel'' add_left_cancel''

/- warning: mul_right_cancel'' -> mul_right_cancel'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α} {c : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c b)) -> (Eq.{succ u1} α a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2712 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2714 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2712 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2714)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2727 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2729 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2727 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2729)] {a : α} {b : α} {c : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c b)) -> (Eq.{succ u1} α a c)
Case conversion may be inaccurate. Consider using '#align mul_right_cancel'' mul_right_cancel''ₓ'. -/
@[to_additive]
theorem mul_right_cancel'' [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b = c * b) : a = c :=
  le_antisymm (le_of_mul_le_mul_right' h.le) (le_of_mul_le_mul_right' h.ge)
#align mul_right_cancel'' mul_right_cancel''
#align add_right_cancel'' add_right_cancel''

end PartialOrder

section LinearOrder

variable [LinearOrder α] {a b c d : α} [CovariantClass α α (· * ·) (· < ·)]
  [CovariantClass α α (swap (· * ·)) (· < ·)]

/- warning: min_le_max_of_mul_le_mul -> min_le_max_of_mul_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : α} {b : α} {c : α} {d : α} [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))], (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c d)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (LinearOrder.min.{u1} α _inst_2 a b) (LinearOrder.max.{u1} α _inst_2 c d))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : LinearOrder.{u1} α] {a : α} {b : α} {c : α} {d : α} [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2882 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2884 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2882 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2884) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2897 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2899 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2897 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2899)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2919 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2921 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2919 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2921)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2934 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2936 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2934 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2936)], (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c d)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_2) a b) (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_2) c d))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3124 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3126 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3124 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3126) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3139 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3141 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3139 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3141)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3216 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3218 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3216 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3218)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3231 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3233 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3231 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3233)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3311 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3313 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3311 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3313)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3326 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3328 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3326 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3328)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3400 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3402 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3400 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3402) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3415 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3417 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3415 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3417)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3466 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3468 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3466 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3468) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3481 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3483 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3481 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3483)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) -> (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3535 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3537 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3535 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3537)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3550 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3552 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3550 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3552)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3604 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3606 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3604 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3606)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3619 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3621 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3619 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3621)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) -> (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3670 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3672 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3670 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3672) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3685 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3687 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3685 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3687)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3704 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3706 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3704 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3706) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3719 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3721 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3719 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3721)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3804 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3806 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3804 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3806)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3819 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3821 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3819 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3821)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3841 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3843 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3841 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3843)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3856 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3858 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3856 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3858)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3938 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3940 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3938 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3940) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3953 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3955 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3953 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3955)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3972 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3974 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3972 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3974) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3987 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3989 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3987 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3989)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4072 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4074 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4072 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4074)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4087 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4089 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4087 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4089)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4109 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4111 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4109 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4111)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4124 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4126 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4124 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4126)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4218 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4220 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4218 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4220) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4233 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4235 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4233 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4235)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4310 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4312 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4310 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4312) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4325 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4327 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4325 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4327)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4402 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4404 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4402 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4404)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4417 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4419 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4417 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4419)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4497 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4499 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4497 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4499)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4512 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4514 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4512 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4514)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4586 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4588 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4586 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4588) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4601 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4603 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4601 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4603)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4652 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4654 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4652 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4654) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4667 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4669 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4667 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4669)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) -> (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4721 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4723 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4721 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4723)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4736 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4738 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4736 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4738)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4790 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4792 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4790 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4792)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4805 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4807 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4805 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4807)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) -> (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4856 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4858 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4856 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4858) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4871 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4873 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4871 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4873)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4890 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4892 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4890 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4892) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4905 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4907 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4905 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4907)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4990 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4992 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4990 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4992)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5005 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5007 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5005 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5007)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5027 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5029 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5027 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5029)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5042 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5044 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5042 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5044)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5124 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5126 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5124 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5126) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5139 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5141 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5139 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5141)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5158 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5160 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5158 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5160) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5173 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5175 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5173 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5175)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5258 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5260 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5258 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5260)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5273 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5275 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5273 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5275)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5295 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5297 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5295 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5297)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5310 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5312 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5310 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5312)] {a : α} (b : α), Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5405 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5407 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5405 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5407) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5420 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5422 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5420 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5422)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_of_le_one mul_le_of_le_of_le_oneₓ'. -/
@[to_additive]
theorem mul_le_of_le_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b ≤ c)
    (ha : a ≤ 1) : b * a ≤ c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := (mul_one b)
    _ ≤ c := hbc
    
#align mul_le_of_le_of_le_one mul_le_of_le_of_le_one
#align add_le_of_le_of_nonpos add_le_of_le_of_nonpos

/- warning: mul_lt_of_le_of_lt_one -> mul_lt_of_le_of_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5515 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5517 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5515 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5517) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5530 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5532 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5530 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5532)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_of_lt_one mul_lt_of_le_of_lt_oneₓ'. -/
@[to_additive]
theorem mul_lt_of_le_of_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b ≤ c)
    (ha : a < 1) : b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := (mul_one b)
    _ ≤ c := hbc
    
#align mul_lt_of_le_of_lt_one mul_lt_of_le_of_lt_one
#align add_lt_of_le_of_neg add_lt_of_le_of_neg

/- warning: mul_lt_of_lt_of_le_one -> mul_lt_of_lt_of_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5625 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5627 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5625 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5627) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5640 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5642 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5640 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5642)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_le_one mul_lt_of_lt_of_le_oneₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : a ≤ 1) : b * a < c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := (mul_one b)
    _ < c := hbc
    
#align mul_lt_of_lt_of_le_one mul_lt_of_lt_of_le_one
#align add_lt_of_lt_of_nonpos add_lt_of_lt_of_nonpos

/- warning: mul_lt_of_lt_of_lt_one -> mul_lt_of_lt_of_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5735 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5737 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5735 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5737) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5750 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5752 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5750 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5752)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_lt_one mul_lt_of_lt_of_lt_oneₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_of_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b < c)
    (ha : a < 1) : b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := (mul_one b)
    _ < c := hbc
    
#align mul_lt_of_lt_of_lt_one mul_lt_of_lt_of_lt_one
#align add_lt_of_lt_of_neg add_lt_of_lt_of_neg

/- warning: mul_lt_of_lt_of_lt_one' -> mul_lt_of_lt_of_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5845 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5847 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5845 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5847) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5860 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5862 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5860 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5862)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_lt_one' mul_lt_of_lt_of_lt_one'ₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_of_lt_one' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : a < 1) : b * a < c :=
  mul_lt_of_lt_of_le_one hbc ha.le
#align mul_lt_of_lt_of_lt_one' mul_lt_of_lt_of_lt_one'
#align add_lt_of_lt_of_neg' add_lt_of_lt_of_neg'

/- warning: left.mul_le_one -> Left.mul_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5916 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5918 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5916 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5918) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5931 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5933 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5931 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5933)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5987 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5989 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5987 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5989) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6002 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6004 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6002 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6004)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6058 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6060 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6058 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6060) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6073 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6075 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6073 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6075)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6129 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6131 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6129 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6131) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6144 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6146 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6144 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6146)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6200 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6202 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6200 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6202) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6215 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6217 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6215 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6217)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6269 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6271 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6269 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6271) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6284 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6286 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6284 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6286)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6382 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6384 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6382 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6384) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6397 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6399 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6397 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6399)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6495 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6497 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6495 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6497) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6510 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6512 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6510 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6512)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6608 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6610 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6608 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6610) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6623 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6625 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6623 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6625)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6721 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6723 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6721 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6723) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6736 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6738 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6736 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6738)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_lt' lt_mul_of_lt_of_one_lt'ₓ'. -/
@[to_additive]
theorem lt_mul_of_lt_of_one_lt' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : 1 < a) : b < c * a :=
  lt_mul_of_lt_of_one_le hbc ha.le
#align lt_mul_of_lt_of_one_lt' lt_mul_of_lt_of_one_lt'
#align lt_add_of_lt_of_pos' lt_add_of_lt_of_pos'

/- warning: left.one_le_mul -> Left.one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6792 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6794 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6792 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6794) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6807 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6809 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6807 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6809)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6863 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6865 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6863 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6865) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6878 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6880 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6878 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6880)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6934 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6936 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6934 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6936) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6949 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6951 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6949 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6951)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7005 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7007 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7005 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7007) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7020 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7022 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7020 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7022)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7076 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7078 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7076 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7078) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7091 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7093 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7091 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7093)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7148 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7150 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7148 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7150)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7163 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7165 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7163 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7165)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_of_le mul_le_of_le_one_of_leₓ'. -/
@[to_additive]
theorem mul_le_of_le_one_of_le [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a ≤ 1)
    (hbc : b ≤ c) : a * b ≤ c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := (one_mul b)
    _ ≤ c := hbc
    
#align mul_le_of_le_one_of_le mul_le_of_le_one_of_le
#align add_le_of_nonpos_of_le add_le_of_nonpos_of_le

/- warning: mul_lt_of_lt_one_of_le -> mul_lt_of_lt_one_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7261 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7263 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7261 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7263)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7276 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7278 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7276 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7278)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_le mul_lt_of_lt_one_of_leₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_one_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : a < 1)
    (hbc : b ≤ c) : a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := (one_mul b)
    _ ≤ c := hbc
    
#align mul_lt_of_lt_one_of_le mul_lt_of_lt_one_of_le
#align add_lt_of_neg_of_le add_lt_of_neg_of_le

/- warning: mul_lt_of_le_one_of_lt -> mul_lt_of_le_one_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7374 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7376 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7374 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7376)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7389 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7391 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7389 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7391)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_one_of_lt mul_lt_of_le_one_of_ltₓ'. -/
@[to_additive]
theorem mul_lt_of_le_one_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a ≤ 1)
    (hb : b < c) : a * b < c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := (one_mul b)
    _ < c := hb
    
#align mul_lt_of_le_one_of_lt mul_lt_of_le_one_of_lt
#align add_lt_of_nonpos_of_lt add_lt_of_nonpos_of_lt

/- warning: mul_lt_of_lt_one_of_lt -> mul_lt_of_lt_one_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7487 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7489 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7487 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7489)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7502 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7504 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7502 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7504)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_lt mul_lt_of_lt_one_of_ltₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_one_of_lt [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : a < 1)
    (hb : b < c) : a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := (one_mul b)
    _ < c := hb
    
#align mul_lt_of_lt_one_of_lt mul_lt_of_lt_one_of_lt
#align add_lt_of_neg_of_lt add_lt_of_neg_of_lt

/- warning: mul_lt_of_lt_one_of_lt' -> mul_lt_of_lt_one_of_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7600 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7602 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7600 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7602)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7615 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7617 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7615 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7617)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_lt' mul_lt_of_lt_one_of_lt'ₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_one_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a < 1)
    (hbc : b < c) : a * b < c :=
  mul_lt_of_le_one_of_lt ha.le hbc
#align mul_lt_of_lt_one_of_lt' mul_lt_of_lt_one_of_lt'
#align add_lt_of_neg_of_lt' add_lt_of_neg_of_lt'

/- warning: right.mul_le_one -> Right.mul_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7674 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7676 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7674 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7676)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7689 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7691 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7689 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7691)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7748 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7750 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7748 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7750)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7763 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7765 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7763 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7765)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7822 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7824 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7822 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7824)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7837 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7839 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7837 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7839)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7896 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7898 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7896 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7898)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7911 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7913 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7911 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7913)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7970 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7972 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7970 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7972)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7985 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7987 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7985 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7987)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8042 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8044 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8042 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8044)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8057 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8059 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8057 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8059)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8158 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8160 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8158 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8160)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8173 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8175 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8173 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8175)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8274 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8276 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8274 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8276)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8289 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8291 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8289 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8291)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8390 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8392 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8390 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8392)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8405 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8407 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8405 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8407)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8506 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8508 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8506 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8508)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8521 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8523 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8521 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8523)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_lt' lt_mul_of_one_lt_of_lt'ₓ'. -/
@[to_additive]
theorem lt_mul_of_one_lt_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 < a)
    (hbc : b < c) : b < a * c :=
  lt_mul_of_one_le_of_lt ha.le hbc
#align lt_mul_of_one_lt_of_lt' lt_mul_of_one_lt_of_lt'
#align lt_add_of_pos_of_lt' lt_add_of_pos_of_lt'

/- warning: right.one_le_mul -> Right.one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8580 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8582 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8580 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8582)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8595 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8597 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8595 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8597)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8654 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8656 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8654 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8656)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8669 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8671 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8669 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8671)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8728 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8730 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8728 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8730)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8743 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8745 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8743 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8745)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8802 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8804 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8802 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8804)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8817 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8819 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8817 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8819)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8876 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8878 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8876 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8878)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8891 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8893 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8891 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8893)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5916 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5918 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5916 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5918) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5931 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5933 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5931 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5933)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_le_one' mul_le_one'ₓ'. -/
alias Left.mul_le_one ← mul_le_one'
#align mul_le_one' mul_le_one'

/- warning: mul_lt_one_of_le_of_lt -> mul_lt_one_of_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5987 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5989 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5987 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5989) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6002 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6004 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6002 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6004)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_one_of_le_of_lt mul_lt_one_of_le_of_ltₓ'. -/
alias Left.mul_lt_one_of_le_of_lt ← mul_lt_one_of_le_of_lt
#align mul_lt_one_of_le_of_lt mul_lt_one_of_le_of_lt

/- warning: mul_lt_one_of_lt_of_le -> mul_lt_one_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6058 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6060 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6058 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6060) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6073 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6075 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6073 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6075)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_one_of_lt_of_le mul_lt_one_of_lt_of_leₓ'. -/
alias Left.mul_lt_one_of_lt_of_le ← mul_lt_one_of_lt_of_le
#align mul_lt_one_of_lt_of_le mul_lt_one_of_lt_of_le

/- warning: mul_lt_one -> mul_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6129 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6131 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6129 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6131) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6144 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6146 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6144 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6146)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_lt_one mul_lt_oneₓ'. -/
alias Left.mul_lt_one ← mul_lt_one
#align mul_lt_one mul_lt_one

/- warning: mul_lt_one' -> mul_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6200 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6202 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6200 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6202) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6215 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6217 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6215 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6217)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6792 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6794 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6792 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6794) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6807 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6809 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6807 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6809)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align one_le_mul one_le_mulₓ'. -/
alias Left.one_le_mul ← one_le_mul
#align one_le_mul one_le_mul

/- warning: one_lt_mul_of_le_of_lt' -> one_lt_mul_of_le_of_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6863 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6865 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6863 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6865) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6878 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6880 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6878 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6880)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align one_lt_mul_of_le_of_lt' one_lt_mul_of_le_of_lt'ₓ'. -/
alias Left.one_lt_mul_of_le_of_lt ← one_lt_mul_of_le_of_lt'
#align one_lt_mul_of_le_of_lt' one_lt_mul_of_le_of_lt'

/- warning: one_lt_mul_of_lt_of_le' -> one_lt_mul_of_lt_of_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6934 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6936 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6934 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6936) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6949 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6951 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6949 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6951)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align one_lt_mul_of_lt_of_le' one_lt_mul_of_lt_of_le'ₓ'. -/
alias Left.one_lt_mul_of_lt_of_le ← one_lt_mul_of_lt_of_le'
#align one_lt_mul_of_lt_of_le' one_lt_mul_of_lt_of_le'

/- warning: one_lt_mul' -> one_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7005 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7007 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7005 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7007) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7020 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7022 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7020 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7022)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align one_lt_mul' one_lt_mul'ₓ'. -/
alias Left.one_lt_mul ← one_lt_mul'
#align one_lt_mul' one_lt_mul'

/- warning: one_lt_mul'' -> one_lt_mul'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7076 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7078 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7076 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7078) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7091 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7093 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7091 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7093)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8984 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8986 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8984 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8986) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8999 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9001 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8999 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9001)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_mul_lt_of_one_le_left lt_of_mul_lt_of_one_le_leftₓ'. -/
@[to_additive]
theorem lt_of_mul_lt_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b < c)
    (hle : 1 ≤ b) : a < c :=
  (le_mul_of_one_le_right' hle).trans_lt h
#align lt_of_mul_lt_of_one_le_left lt_of_mul_lt_of_one_le_left
#align lt_of_add_lt_of_nonneg_left lt_of_add_lt_of_nonneg_left

/- warning: le_of_mul_le_of_one_le_left -> le_of_mul_le_of_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9055 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9057 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9055 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9057) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9070 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9072 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9070 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9072)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_left le_of_mul_le_of_one_le_leftₓ'. -/
@[to_additive]
theorem le_of_mul_le_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b ≤ c)
    (hle : 1 ≤ b) : a ≤ c :=
  (le_mul_of_one_le_right' hle).trans h
#align le_of_mul_le_of_one_le_left le_of_mul_le_of_one_le_left
#align le_of_add_le_of_nonneg_left le_of_add_le_of_nonneg_left

/- warning: lt_of_lt_mul_of_le_one_left -> lt_of_lt_mul_of_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9126 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9128 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9126 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9128) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9141 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9143 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9141 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9143)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_left lt_of_lt_mul_of_le_one_leftₓ'. -/
@[to_additive]
theorem lt_of_lt_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a < b * c)
    (hle : c ≤ 1) : a < b :=
  h.trans_le (mul_le_of_le_one_right' hle)
#align lt_of_lt_mul_of_le_one_left lt_of_lt_mul_of_le_one_left
#align lt_of_lt_add_of_nonpos_left lt_of_lt_add_of_nonpos_left

/- warning: le_of_le_mul_of_le_one_left -> le_of_le_mul_of_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9196 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9198 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9196 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9198) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9211 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9213 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9211 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9213)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b)
Case conversion may be inaccurate. Consider using '#align le_of_le_mul_of_le_one_left le_of_le_mul_of_le_one_leftₓ'. -/
@[to_additive]
theorem le_of_le_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a ≤ b * c)
    (hle : c ≤ 1) : a ≤ b :=
  h.trans (mul_le_of_le_one_right' hle)
#align le_of_le_mul_of_le_one_left le_of_le_mul_of_le_one_left
#align le_of_le_add_of_nonpos_left le_of_le_add_of_nonpos_left

/- warning: lt_of_mul_lt_of_one_le_right -> lt_of_mul_lt_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9269 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9271 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9269 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9271)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9284 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9286 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9284 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9286)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c)
Case conversion may be inaccurate. Consider using '#align lt_of_mul_lt_of_one_le_right lt_of_mul_lt_of_one_le_rightₓ'. -/
@[to_additive]
theorem lt_of_mul_lt_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b < c) (hle : 1 ≤ a) : b < c :=
  (le_mul_of_one_le_left' hle).trans_lt h
#align lt_of_mul_lt_of_one_le_right lt_of_mul_lt_of_one_le_right
#align lt_of_add_lt_of_nonneg_right lt_of_add_lt_of_nonneg_right

/- warning: le_of_mul_le_of_one_le_right -> le_of_mul_le_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9343 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9345 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9343 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9345)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9358 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9360 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9358 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9360)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_right le_of_mul_le_of_one_le_rightₓ'. -/
@[to_additive]
theorem le_of_mul_le_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
  (le_mul_of_one_le_left' hle).trans h
#align le_of_mul_le_of_one_le_right le_of_mul_le_of_one_le_right
#align le_of_add_le_of_nonneg_right le_of_add_le_of_nonneg_right

/- warning: lt_of_lt_mul_of_le_one_right -> lt_of_lt_mul_of_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9417 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9419 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9417 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9419)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9432 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9434 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9432 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9434)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_right lt_of_lt_mul_of_le_one_rightₓ'. -/
@[to_additive]
theorem lt_of_lt_mul_of_le_one_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a < b * c) (hle : b ≤ 1) : a < c :=
  h.trans_le (mul_le_of_le_one_left' hle)
#align lt_of_lt_mul_of_le_one_right lt_of_lt_mul_of_le_one_right
#align lt_of_lt_add_of_nonpos_right lt_of_lt_add_of_nonpos_right

/- warning: le_of_le_mul_of_le_one_right -> le_of_le_mul_of_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9490 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9492 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9490 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9492)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9505 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9507 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9505 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9507)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) (And (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9572 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9574 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9572 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9574) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9587 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9589 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9587 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9589)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9609 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9611 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9609 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9611)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9624 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9626 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9624 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9626)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) (And (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a₁ a₂) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b₁ b₂) -> (Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a₂ b₂) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a₁ b₁)) (And (Eq.{succ u1} α a₁ a₂) (Eq.{succ u1} α b₁ b₂)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9831 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9833 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9831 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9833) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9846 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9848 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9846 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9848)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9868 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9870 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9868 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9870)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9883 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9885 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9883 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9885)] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9902 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9904 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9902 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9904) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9917 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9919 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9917 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9919)] [_inst_6 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9939 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9941 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9939 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9941)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9954 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9956 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9954 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9956)] {a₁ : α} {a₂ : α} {b₁ : α} {b₂ : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a₁ a₂) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b₁ b₂) -> (Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a₂ b₂) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a₁ b₁)) (And (Eq.{succ u1} α a₁ a₂) (Eq.{succ u1} α b₁ b₂)))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10119 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10121 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10119 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10121) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10134 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10136 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10134 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10136)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_leftₓ'. -/
@[to_additive eq_zero_of_add_nonneg_left]
theorem eq_one_of_one_le_mul_left (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : a = 1 :=
  ha.eq_of_not_lt fun h => hab.not_lt <| mul_lt_one_of_lt_of_le h hb
#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_left
#align eq_zero_of_add_nonneg_left eq_zero_of_add_nonneg_left

/- warning: eq_one_of_mul_le_one_left -> eq_one_of_mul_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10198 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10200 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10198 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10200) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10213 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10215 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10213 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10215)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10333 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10335 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10333 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10335)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10348 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10350 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10348 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10350)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_rightₓ'. -/
@[to_additive eq_zero_of_add_nonneg_right]
theorem eq_one_of_one_le_mul_right (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : b = 1 :=
  hb.eq_of_not_lt fun h => hab.not_lt <| Right.mul_lt_one_of_le_of_lt ha h
#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_right
#align eq_zero_of_add_nonneg_right eq_zero_of_add_nonneg_right

/- warning: eq_one_of_mul_le_one_right -> eq_one_of_mul_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10415 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10417 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10415 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10417)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10430 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10432 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10430 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10432)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))))] (a : α), Exists.{succ u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10507 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10509 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10507 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10509) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10522 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10524 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10522 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10524)] (a : α), Exists.{succ u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b b) a)
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
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], LeftCancelSemigroup.{u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10777 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10779 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10777 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10779) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10792 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10794 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10792 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10794)], LeftCancelSemigroup.{u1} α
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
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], RightCancelSemigroup.{u1} α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10860 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10862 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10860 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10862)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10875 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10877 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10875 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10877)], RightCancelSemigroup.{u1} α
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
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10940 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10942 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10940 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10942) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10955 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10957 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10955 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10957)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10977 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10979 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10977 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10979)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10992 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10994 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10992 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10994)] [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11011 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11013 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11011 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11013) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11026 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11028 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11026 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11028)] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11048 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11050 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11048 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11050)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11063 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11065 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11063 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11065)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
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
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11203 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11205 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11203 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11205) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11218 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11220 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11218 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11220)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11237 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11239 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11237 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11239) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11252 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11254 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11252 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11254)] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11274 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11276 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11274 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11276)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11289 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11291 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11289 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11291)] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11311 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11313 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11311 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11313)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11326 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11328 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11326 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11328)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
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
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_5 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10940 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10942 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10940 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10942) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10955 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10957 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10955 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10957)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10977 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10979 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10977 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10979)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10992 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10994 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10992 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10994)] [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11011 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11013 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11011 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11013) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11026 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11028 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11026 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11028)] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11048 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11050 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11048 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11050)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11063 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11065 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11063 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11065)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11510 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11512 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11510 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11512) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11525 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11527 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11525 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11527)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.const_mul' Monotone.const_mul'ₓ'. -/
@[to_additive const_add]
theorem Monotone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a
#align monotone.const_mul' Monotone.const_mul'
#align monotone.const_add Monotone.const_add

/- warning: monotone_on.const_mul' -> MonotoneOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11596 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11598 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11596 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11598) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11611 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11613 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11611 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11613)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.const_mul' MonotoneOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem MonotoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a
#align monotone_on.const_mul' MonotoneOn.const_mul'
#align monotone_on.const_add MonotoneOn.const_add

/- warning: antitone.const_mul' -> Antitone.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11690 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11692 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11690 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11692) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11705 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11707 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11705 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11707)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.const_mul' Antitone.const_mul'ₓ'. -/
@[to_additive const_add]
theorem Antitone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a
#align antitone.const_mul' Antitone.const_mul'
#align antitone.const_add Antitone.const_add

/- warning: antitone_on.const_mul' -> AntitoneOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11776 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11778 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11776 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11778) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11791 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11793 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11791 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11793)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.const_mul' AntitoneOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem AntitoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a
#align antitone_on.const_mul' AntitoneOn.const_mul'
#align antitone_on.const_add AntitoneOn.const_add

/- warning: monotone.mul_const' -> Monotone.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11873 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11875 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11873 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11875)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11888 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11890 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11888 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11890)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a))
Case conversion may be inaccurate. Consider using '#align monotone.mul_const' Monotone.mul_const'ₓ'. -/
@[to_additive add_const]
theorem Monotone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a
#align monotone.mul_const' Monotone.mul_const'
#align monotone.add_const Monotone.add_const

/- warning: monotone_on.mul_const' -> MonotoneOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11962 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11964 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11962 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11964)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11977 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11979 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11977 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11979)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.mul_const' MonotoneOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem MonotoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s)
    (a : α) : MonotoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a
#align monotone_on.mul_const' MonotoneOn.mul_const'
#align monotone_on.add_const MonotoneOn.add_const

/- warning: antitone.mul_const' -> Antitone.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12059 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12061 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12059 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12061)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12074 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12076 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12074 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12076)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a))
Case conversion may be inaccurate. Consider using '#align antitone.mul_const' Antitone.mul_const'ₓ'. -/
@[to_additive add_const]
theorem Antitone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a
#align antitone.mul_const' Antitone.mul_const'
#align antitone.add_const Antitone.add_const

/- warning: antitone_on.mul_const' -> AntitoneOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12148 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12150 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12148 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12150)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12163 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12165 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12163 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12165)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.mul_const' AntitoneOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem AntitoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : AntitoneOn f s)
    (a : α) : AntitoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a
#align antitone_on.mul_const' AntitoneOn.mul_const'
#align antitone_on.add_const AntitoneOn.add_const

/- warning: monotone.mul' -> Monotone.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (Monotone.{u2, u1} β α _inst_3 _inst_2 g) -> (Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12242 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12244 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12242 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12244) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12257 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12259 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12257 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12259)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12279 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12281 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12279 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12281)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12294 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12296 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12294 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12296)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (Monotone.{u1, u2} β α _inst_3 _inst_2 g) -> (Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12370 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12372 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12370 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12372) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12385 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12387 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12385 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12387)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12407 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12409 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12407 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12409)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12422 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12424 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12422 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12424)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (Antitone.{u2, u1} β α _inst_3 _inst_2 g) -> (Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12509 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12511 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12509 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12511) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12524 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12526 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12524 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12526)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12546 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12548 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12546 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12548)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12561 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12563 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12561 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12563)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (Antitone.{u1, u2} β α _inst_3 _inst_2 g) -> (Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12637 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12639 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12637 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12639) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12652 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12654 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12652 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12654)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12674 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12676 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12674 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12676)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12689 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12691 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12689 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12691)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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

/- warning: strict_mono.const_mul' -> StrictMono.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictMono.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (c : α), StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c (f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12832 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12834 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12832 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12834) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12847 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12849 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12847 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12849)], (StrictMono.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (c : α), StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c (f x)))
Case conversion may be inaccurate. Consider using '#align strict_mono.const_mul' StrictMono.const_mul'ₓ'. -/
@[to_additive const_add]
theorem StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c * f x :=
  fun a b ab => mul_lt_mul_left' (hf ab) c
#align strict_mono.const_mul' StrictMono.const_mul'
#align strict_mono.const_add StrictMono.const_add

/- warning: strict_mono_on.const_mul' -> StrictMonoOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (c : α), StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c (f x)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12918 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12920 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12918 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12920) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12933 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12935 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12933 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12935)], (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (c : α), StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c (f x)) s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.const_mul' StrictMonoOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => c * f x) s := fun a ha b hb ab => mul_lt_mul_left' (hf ha hb ab) c
#align strict_mono_on.const_mul' StrictMonoOn.const_mul'
#align strict_mono_on.const_add StrictMonoOn.const_add

/- warning: strict_anti.const_mul' -> StrictAnti.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictAnti.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (c : α), StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c (f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13012 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13014 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13012 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13014) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13027 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13029 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13027 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13029)], (StrictAnti.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (c : α), StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c (f x)))
Case conversion may be inaccurate. Consider using '#align strict_anti.const_mul' StrictAnti.const_mul'ₓ'. -/
@[to_additive const_add]
theorem StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c * f x :=
  fun a b ab => mul_lt_mul_left' (hf ab) c
#align strict_anti.const_mul' StrictAnti.const_mul'
#align strict_anti.const_add StrictAnti.const_add

/- warning: strict_anti_on.const_mul' -> StrictAntiOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (c : α), StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c (f x)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13098 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13100 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13098 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13100) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13113 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13115 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13113 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13115)], (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (c : α), StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) c (f x)) s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.const_mul' StrictAntiOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem StrictAntiOn.const_mul' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => c * f x) s := fun a ha b hb ab => mul_lt_mul_left' (hf ha hb ab) c
#align strict_anti_on.const_mul' StrictAntiOn.const_mul'
#align strict_anti_on.const_add StrictAntiOn.const_add

end Left

section Right

variable [CovariantClass α α (swap (· * ·)) (· < ·)]

/- warning: strict_mono.mul_const' -> StrictMono.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictMono.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (c : α), StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) c))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13255 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13257 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13255 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13257)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13270 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13272 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13270 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13272)], (StrictMono.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (c : α), StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) c))
Case conversion may be inaccurate. Consider using '#align strict_mono.mul_const' StrictMono.mul_const'ₓ'. -/
@[to_additive add_const]
theorem StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f x * c :=
  fun a b ab => mul_lt_mul_right' (hf ab) c
#align strict_mono.mul_const' StrictMono.mul_const'
#align strict_mono.add_const StrictMono.add_const

/- warning: strict_mono_on.mul_const' -> StrictMonoOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (c : α), StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) c) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13344 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13346 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13344 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13346)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13359 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13361 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13359 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13361)], (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (c : α), StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) c) s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.mul_const' StrictMonoOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem StrictMonoOn.mul_const' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => f x * c) s := fun a ha b hb ab => mul_lt_mul_right' (hf ha hb ab) c
#align strict_mono_on.mul_const' StrictMonoOn.mul_const'
#align strict_mono_on.add_const StrictMonoOn.add_const

/- warning: strict_anti.mul_const' -> StrictAnti.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictAnti.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (c : α), StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) c))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13441 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13443 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13441 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13443)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13456 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13458 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13456 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13458)], (StrictAnti.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (c : α), StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) c))
Case conversion may be inaccurate. Consider using '#align strict_anti.mul_const' StrictAnti.mul_const'ₓ'. -/
@[to_additive add_const]
theorem StrictAnti.mul_const' (hf : StrictAnti f) (c : α) : StrictAnti fun x => f x * c :=
  fun a b ab => mul_lt_mul_right' (hf ab) c
#align strict_anti.mul_const' StrictAnti.mul_const'
#align strict_anti.add_const StrictAnti.add_const

/- warning: strict_anti_on.mul_const' -> StrictAntiOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (c : α), StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) c) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13530 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13532 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13530 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13532)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13545 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13547 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13545 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13547)], (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (c : α), StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) c) s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.mul_const' StrictAntiOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => f x * c) s := fun a ha b hb ab => mul_lt_mul_right' (hf ha hb ab) c
#align strict_anti_on.mul_const' StrictAntiOn.mul_const'
#align strict_anti_on.add_const StrictAntiOn.add_const

end Right

/- warning: strict_mono.mul' -> StrictMono.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictMono.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13625 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13627 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13625 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13627) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13640 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13642 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13640 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13642)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13662 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13664 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13662 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13664)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13677 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13679 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13677 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13679)], (StrictMono.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13753 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13755 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13753 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13755) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13768 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13770 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13768 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13770)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13790 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13792 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13790 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13792)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13805 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13807 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13805 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13807)], (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictAnti.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13892 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13894 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13892 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13894) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13907 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13909 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13907 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13909)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13929 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13931 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13929 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13931)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13944 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13946 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13944 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13946)], (StrictAnti.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14020 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14022 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14020 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14022) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14035 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14037 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14035 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14037)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14057 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14059 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14057 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14059)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14072 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14074 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14072 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14074)], (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14159 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14161 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14159 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14161) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14174 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14176 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14174 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14176)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14196 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14198 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14196 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14198)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14211 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14213 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14211 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14213)] {f : β -> α} {g : β -> α}, (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14293 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14295 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14293 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14295) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14308 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14310 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14308 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14310)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14330 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14332 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14330 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14332)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14345 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14347 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14345 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14347)] {f : β -> α} {g : β -> α}, (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14438 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14440 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14438 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14440) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14453 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14455 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14453 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14455)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14475 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14477 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14475 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14477)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14490 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14492 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14490 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14492)] {f : β -> α} {g : β -> α}, (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] {f : β -> α} {g : β -> α}, (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14572 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14574 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14572 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14574) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14587 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14589 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14587 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14589)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14609 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14611 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14609 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14611)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14624 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14626 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14624 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14626)] {f : β -> α} {g : β -> α}, (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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

/- warning: strict_mono.mul_monotone' -> StrictMono.mul_monotone' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictMono.{u2, u1} β α _inst_3 _inst_2 f) -> (Monotone.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14810 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14812 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14810 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14812) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14825 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14827 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14825 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14827)] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14847 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14849 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14847 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14849)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14862 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14864 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14862 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14864)], (StrictMono.{u2, u1} β α _inst_3 _inst_2 f) -> (Monotone.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictMono.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align strict_mono.mul_monotone' StrictMono.mul_monotone'ₓ'. -/
/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone
      "The sum of a strictly monotone function and a monotone function is strictly monotone."]
theorem StrictMono.mul_monotone' (hf : StrictMono f) (hg : Monotone g) :
    StrictMono fun x => f x * g x := fun x y h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)
#align strict_mono.mul_monotone' StrictMono.mul_monotone'
#align strict_mono.add_monotone StrictMono.add_monotone

/- warning: strict_mono_on.mul_monotone' -> StrictMonoOn.mul_monotone' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14938 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14940 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14938 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14940) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14953 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14955 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14953 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14955)] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14975 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14977 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14975 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14977)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14990 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14992 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14990 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14992)], (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align strict_mono_on.mul_monotone' StrictMonoOn.mul_monotone'ₓ'. -/
/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone
      "The sum of a strictly monotone function and a monotone function is strictly monotone."]
theorem StrictMonoOn.mul_monotone' (hf : StrictMonoOn f s) (hg : MonotoneOn g s) :
    StrictMonoOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)
#align strict_mono_on.mul_monotone' StrictMonoOn.mul_monotone'
#align strict_mono_on.add_monotone StrictMonoOn.add_monotone

/- warning: strict_anti.mul_antitone' -> StrictAnti.mul_antitone' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictAnti.{u2, u1} β α _inst_3 _inst_2 f) -> (Antitone.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15077 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15079 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15077 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15079) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15092 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15094 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15092 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15094)] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15114 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15116 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15114 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15116)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15129 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15131 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15129 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15131)], (StrictAnti.{u2, u1} β α _inst_3 _inst_2 f) -> (Antitone.{u2, u1} β α _inst_3 _inst_2 g) -> (StrictAnti.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align strict_anti.mul_antitone' StrictAnti.mul_antitone'ₓ'. -/
/-- The product of a strictly antitone function and a antitone function is strictly antitone. -/
@[to_additive add_antitone
      "The sum of a strictly antitone function and a antitone function is strictly antitone."]
theorem StrictAnti.mul_antitone' (hf : StrictAnti f) (hg : Antitone g) :
    StrictAnti fun x => f x * g x := fun x y h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)
#align strict_anti.mul_antitone' StrictAnti.mul_antitone'
#align strict_anti.add_antitone StrictAnti.add_antitone

/- warning: strict_anti_on.mul_antitone' -> StrictAntiOn.mul_antitone' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15205 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15207 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15205 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15207) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15220 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15222 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15220 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15222)] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15242 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15244 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15242 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15244)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15257 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15259 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15257 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15259)], (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align strict_anti_on.mul_antitone' StrictAntiOn.mul_antitone'ₓ'. -/
/-- The product of a strictly antitone function and a antitone function is strictly antitone. -/
@[to_additive add_antitone
      "The sum of a strictly antitone function and a antitone function is strictly antitone."]
theorem StrictAntiOn.mul_antitone' (hf : StrictAntiOn f s) (hg : AntitoneOn g s) :
    StrictAntiOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)
#align strict_anti_on.mul_antitone' StrictAntiOn.mul_antitone'
#align strict_anti_on.add_antitone StrictAntiOn.add_antitone

/- warning: cmp_mul_left' -> cmp_mul_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_6 : Mul.{u1} α] [_inst_7 : LinearOrder.{u1} α] [_inst_8 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_7))))))] (a : α) (b : α) (c : α), Eq.{1} Ordering (cmp.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_7))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_7 a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6) a c)) (cmp.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_7))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_7 a b) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_6 : Mul.{u1} α] [_inst_7 : LinearOrder.{u1} α] [_inst_8 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15419 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15421 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15419 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15421) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15434 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15436 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_7)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15434 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15436)] (a : α) (b : α) (c : α), Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_7)))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_7 a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6) a c)) (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_7)))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_7 a b) b c)
Case conversion may be inaccurate. Consider using '#align cmp_mul_left' cmp_mul_left'ₓ'. -/
@[simp, to_additive cmp_add_left]
theorem cmp_mul_left' {α : Type _} [Mul α] [LinearOrder α] [CovariantClass α α (· * ·) (· < ·)]
    (a b c : α) : cmp (a * b) (a * c) = cmp b c :=
  (strictMono_id.const_mul' a).cmp_map_eq b c
#align cmp_mul_left' cmp_mul_left'
#align cmp_add_left cmp_add_left

/- warning: cmp_mul_right' -> cmp_mul_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_6 : Mul.{u1} α] [_inst_7 : LinearOrder.{u1} α] [_inst_8 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_7))))))] (a : α) (b : α) (c : α), Eq.{1} Ordering (cmp.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_7))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_7 a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6) b c)) (cmp.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_7))))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_7 a b) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_6 : Mul.{u1} α] [_inst_7 : LinearOrder.{u1} α] [_inst_8 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15587 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15589 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15587 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15589)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15602 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15604 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_7)))))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15602 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15604)] (a : α) (b : α) (c : α), Eq.{1} Ordering (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_7)))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_7 a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_6) b c)) (cmp.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_7)))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_7 a b) a b)
Case conversion may be inaccurate. Consider using '#align cmp_mul_right' cmp_mul_right'ₓ'. -/
@[simp, to_additive cmp_add_right]
theorem cmp_mul_right' {α : Type _} [Mul α] [LinearOrder α]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (a b c : α) : cmp (a * c) (b * c) = cmp a b :=
  (strictMono_id.mul_const' c).cmp_map_eq a b
#align cmp_mul_right' cmp_mul_right'
#align cmp_add_right cmp_add_right

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

/- warning: mul_le_cancellable.injective -> MulLECancellable.Injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : PartialOrder.{u1} α] {a : α}, (MulLECancellable.{u1} α _inst_1 (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a) -> (Function.Injective.{succ u1, succ u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : PartialOrder.{u1} α] {a : α}, (MulLECancellable.{u1} α _inst_1 (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a) -> (Function.Injective.{succ u1, succ u1} α α ((fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15787 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15789 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15787 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15789) a))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.injective MulLECancellable.Injectiveₓ'. -/
@[to_additive]
protected theorem Injective [Mul α] [PartialOrder α] {a : α} (ha : MulLECancellable a) :
    Injective ((· * ·) a) := fun b c h => le_antisymm (ha h.le) (ha h.ge)
#align mul_le_cancellable.injective MulLECancellable.Injective
#align add_le_cancellable.injective AddLECancellable.Injective

/- warning: mul_le_cancellable.inj -> MulLECancellable.inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : PartialOrder.{u1} α] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α _inst_1 (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c)) (Eq.{succ u1} α b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : PartialOrder.{u1} α] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α _inst_1 (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a c)) (Eq.{succ u1} α b c))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.inj MulLECancellable.injₓ'. -/
@[to_additive]
protected theorem inj [Mul α] [PartialOrder α] {a b c : α} (ha : MulLECancellable a) :
    a * b = a * c ↔ b = c :=
  ha.Injective.eq_iff
#align mul_le_cancellable.inj MulLECancellable.inj
#align add_le_cancellable.inj AddLECancellable.inj

/- warning: mul_le_cancellable.injective_left -> MulLECancellable.injective_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] {a : α}, (MulLECancellable.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a) -> (Function.Injective.{succ u1, succ u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) _x a))
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
  forall {α : Type.{u1}} [_inst_1 : CommSemigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)) (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) c) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) b c)) (Eq.{succ u1} α a b))
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
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommSemigroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16065 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16067 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16065 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16067) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16080 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16082 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16080 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16082)] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) b a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) c a)) (LE.le.{u1} α _inst_1 b c))
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
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16164 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16166 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16164 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16166) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16179 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16181 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16179 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16181)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) b))
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
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16260 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16262 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16260 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16262) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16275 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16277 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16275 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16277)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2)))))
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
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16356 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16358 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16356 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16358) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16371 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16373 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16371 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16373)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b))
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
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16449 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16451 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16449 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16451) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16464 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16466 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16464 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16466)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))))))
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

/- warning: bit0_mono -> bit0_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_2))], Monotone.{u1, u1} α α _inst_2 _inst_2 (bit0.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16556 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16558 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16556 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16558) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16571 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16573 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16571 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16573)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16593 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16595 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16593 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16595)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16608 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16610 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16608 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16610)], Monotone.{u1, u1} α α _inst_2 _inst_2 (bit0.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align bit0_mono bit0_monoₓ'. -/
theorem bit0_mono [CovariantClass α α (· + ·) (· ≤ ·)] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    Monotone (bit0 : α → α) := fun a b h => add_le_add h h
#align bit0_mono bit0_mono

/- warning: bit0_strict_mono -> bit0_strictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toHasLt.{u1} α _inst_2))], StrictMono.{u1, u1} α α _inst_2 _inst_2 (bit0.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16654 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16656 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16654 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16656) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16669 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16671 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16669 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16671)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16691 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16693 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16691 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16693)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16706 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16708 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16706 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.16708)], StrictMono.{u1, u1} α α _inst_2 _inst_2 (bit0.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align bit0_strict_mono bit0_strictMonoₓ'. -/
theorem bit0_strictMono [CovariantClass α α (· + ·) (· < ·)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] : StrictMono (bit0 : α → α) := fun a b h =>
  add_lt_add h h
#align bit0_strict_mono bit0_strictMono

end Bit

