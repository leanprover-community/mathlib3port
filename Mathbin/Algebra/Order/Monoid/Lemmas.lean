/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa,
Yuyang Zhao
-/
import Mathbin.Algebra.CovariantAndContravariant

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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2753 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2755 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2753 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2755) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2768 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2770 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2768 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2770)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2835 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2837 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2835 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2837) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2850 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2852 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2850 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2852)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2917 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2919 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2917 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2919)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2932 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2934 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2932 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2934)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3002 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3004 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3002 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3004)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3017 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3019 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3017 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3019)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3081 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3083 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3081 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3083) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3096 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3098 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3096 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3098)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3158 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3160 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3158 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3160) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3173 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3175 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3173 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3175)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) -> (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3238 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3240 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3238 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3240)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3253 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3255 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3253 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3255)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3318 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3320 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3318 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3320)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3333 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3335 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3333 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3335)] {a : α} {b : α}, (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) -> (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3395 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3397 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3395 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3397) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3410 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3412 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3410 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3412)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3429 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3431 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3429 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3431) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3444 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3446 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3444 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3446)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3527 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3529 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3527 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3529)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3542 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3544 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3542 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3544)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3564 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3566 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3564 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3566)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3579 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3581 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3579 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3581)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a)) (LE.le.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3659 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3661 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3659 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3661) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3674 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3676 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3674 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3676)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3693 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3695 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3693 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3695) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3708 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3710 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3708 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3710)] (a : α) {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) (LE.le.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LE.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3791 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3793 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3791 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3793)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3806 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3808 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3806 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3808)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3828 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3830 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3828 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3830)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3843 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3845 : α) => LE.le.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3843 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3845)] {a : α} {b : α}, Iff (LE.le.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) (LE.le.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3935 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3937 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3935 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3937) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3950 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3952 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3950 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3952)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4017 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4019 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4017 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4019) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4032 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4034 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4032 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4034)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4099 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4101 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4099 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4101)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4114 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4116 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4114 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4116)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4184 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4186 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4184 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4186)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4199 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4201 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4199 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4201)] (a : α) {b : α}, (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4263 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4265 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4263 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4265) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4278 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4280 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4278 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4280)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4340 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4342 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4340 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4342) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4355 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4357 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4355 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4357)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) -> (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4420 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4422 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4420 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4422)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4435 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4437 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4435 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4437)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4500 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4502 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4500 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4502)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4515 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4517 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4515 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4517)] {a : α} {b : α}, (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) -> (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4577 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4579 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4577 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4579) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4592 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4594 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4592 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4594)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4611 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4613 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4611 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4613) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4626 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4628 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4626 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4628)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4709 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4711 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4709 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4711)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4724 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4726 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4724 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4726)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4746 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4748 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4746 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4748)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4761 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4763 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4761 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4763)] (a : α) {b : α}, Iff (LT.lt.{u1} α _inst_2 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a)) (LT.lt.{u1} α _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4841 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4843 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4841 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4843) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4856 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4858 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4856 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4858)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4875 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4877 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4875 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4877) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4890 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4892 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4890 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4892)] {a : α} {b : α}, Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) a) (LT.lt.{u1} α _inst_2 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LT.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4973 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4975 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4973 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4975)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4988 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4990 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4988 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4990)] [_inst_4 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5010 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5012 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5010 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5012)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5025 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5027 : α) => LT.lt.{u1} α _inst_2 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5025 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5027)] {a : α} (b : α), Iff (LT.lt.{u1} α _inst_2 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) b) (LT.lt.{u1} α _inst_2 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5118 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5120 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5118 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5120) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5133 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5135 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5133 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5135)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5211 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5213 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5211 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5213) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5226 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5228 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5226 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5228)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5304 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5306 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5304 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5306) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5319 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5321 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5319 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5321)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5397 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5399 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5397 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5399) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5412 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5414 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5412 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5414)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5490 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5492 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5490 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5492) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5505 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5507 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5505 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5507)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b a) c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5559 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5561 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5559 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5561) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5574 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5576 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5574 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5576)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5630 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5632 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5630 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5632) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5645 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5647 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5645 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5647)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5701 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5703 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5701 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5703) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5716 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5718 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5716 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5718)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5772 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5774 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5772 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5774) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5787 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5789 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5787 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5789)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5843 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5845 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5843 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5845) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5858 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5860 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5858 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5860)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5912 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5914 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5912 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5914) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5927 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5929 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5927 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5929)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6008 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6010 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6008 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6010) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6023 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6025 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6023 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6025)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6104 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6106 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6104 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6106) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6119 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6121 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6119 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6121)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6200 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6202 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6200 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6202) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6215 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6217 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6215 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6217)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6296 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6298 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6296 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6298) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6311 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6313 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6311 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6313)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) c a))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6365 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6367 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6365 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6367) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6380 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6382 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6380 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6382)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6436 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6438 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6436 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6438) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6451 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6453 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6451 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6453)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6507 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6509 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6507 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6509) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6522 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6524 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6522 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6524)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6578 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6580 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6578 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6580) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6593 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6595 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6593 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6595)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6649 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6651 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6649 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6651) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6664 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6666 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6664 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6666)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6721 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6723 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6721 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6723)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6736 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6738 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6736 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6738)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6817 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6819 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6817 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6819)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6832 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6834 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6832 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6834)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6913 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6915 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6913 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6915)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6928 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6930 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6928 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6930)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7009 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7011 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7009 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7011)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7024 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7026 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7024 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7026)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7105 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7107 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7105 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7107)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7120 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7122 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7120 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7122)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7177 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7179 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7177 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7179)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7192 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7194 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7192 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7194)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7251 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7253 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7251 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7253)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7266 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7268 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7266 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7268)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7325 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7327 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7325 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7327)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7340 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7342 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7340 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7342)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7399 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7401 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7399 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7401)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7414 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7416 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7414 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7416)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7473 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7475 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7473 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7475)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7488 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7490 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7488 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7490)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7545 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7547 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7545 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7547)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7560 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7562 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7560 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7562)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7644 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7646 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7644 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7646)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7659 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7661 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7659 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7661)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7743 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7745 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7743 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7745)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7758 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7760 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7758 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7760)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7842 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7844 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7842 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7844)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7857 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7859 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7857 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7859)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7941 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7943 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7941 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7943)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7956 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7958 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7956 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7958)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8013 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8015 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8013 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8015)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8028 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8030 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8028 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8030)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8087 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8089 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8087 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8089)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8102 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8104 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8102 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8104)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8161 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8163 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8161 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8163)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8176 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8178 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8176 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8178)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8235 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8237 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8235 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8237)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8250 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8252 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8250 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8252)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8309 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8311 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8309 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8311)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8324 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8326 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8324 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8326)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8397 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8399 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8397 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8399) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8412 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8414 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8412 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8414)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8466 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8468 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8466 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8468) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8481 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8483 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8481 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8483)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8535 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8537 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8535 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8537) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8550 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8552 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8550 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8552)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8603 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8605 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8603 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8605) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8618 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8620 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8618 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8620)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) c (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a b)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8674 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8676 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8674 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8676)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8689 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8691 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8689 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8691)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) b c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8746 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8748 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8746 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8748)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8761 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8763 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8761 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8763)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8818 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8820 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8818 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8820)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8833 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8835 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8833 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8835)] {a : α} {b : α} {c : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8889 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8891 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8889 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8891)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8904 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8906 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8904 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8906)] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b c)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2) a c)
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8969 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8971 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8969 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8971) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8984 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8986 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8984 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8986)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9006 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9008 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9006 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9008)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9021 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9023 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9021 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9023)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) (And (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9273 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9275 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9273 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9275) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9288 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9290 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9288 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9290)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_leftₓ'. -/
@[to_additive eq_zero_of_add_nonneg_left]
theorem eq_one_of_one_le_mul_left (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : a = 1 :=
  ha.eq_of_not_lt fun h => hab.not_lt <| mul_lt_one_of_lt_of_le h hb
#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_left

/- warning: eq_one_of_mul_le_one_left -> eq_one_of_mul_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9350 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9352 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9350 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9352) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9365 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9367 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9365 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9367)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9483 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9485 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9483 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9485)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9498 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9500 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9498 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9500)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b)) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_rightₓ'. -/
@[to_additive eq_zero_of_add_nonneg_right]
theorem eq_one_of_one_le_mul_right (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : b = 1 :=
  hb.eq_of_not_lt fun h => hab.not_lt <| Right.mul_lt_one_of_le_of_lt ha h
#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_right

/- warning: eq_one_of_mul_le_one_right -> eq_one_of_mul_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1))))) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9563 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9565 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9563 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9565)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9578 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9580 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9578 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9580)] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))))
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
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_2))))] (a : α), Exists.{succ u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_2))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) b b) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9653 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9655 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9653 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9655) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9668 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9670 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9668 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9670)] (a : α), Exists.{succ u1} α (fun (b : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (LinearOrder.toPartialOrder.{u1} α _inst_2))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) b b) a)
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
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9936 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9938 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9936 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9938) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9951 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9953 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9951 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9953)], LeftCancelSemigroup.{u1} α
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
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10019 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10021 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10019 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10021)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10034 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10036 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10034 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10036)], RightCancelSemigroup.{u1} α
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
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10099 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10101 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10099 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10101) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10114 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10116 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10114 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10116)] [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10136 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10138 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10136 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10138)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10151 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10153 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10151 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10153)] [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10170 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10172 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10170 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10172) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10185 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10187 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10185 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10187)] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10207 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10209 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10207 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10209)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10222 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10224 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10222 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10224)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
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
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10362 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10364 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10362 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10364) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10377 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10379 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10377 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10379)] [_inst_4 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10396 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10398 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10396 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10398) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10411 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10413 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10411 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10413)] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10433 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10435 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10433 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10435)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10448 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10450 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10448 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10450)] [_inst_6 : ContravariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10470 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10472 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10470 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10472)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10485 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10487 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10485 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10487)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) b d) -> (Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) c d)) (And (Eq.{succ u1} α a c) (Eq.{succ u1} α b d)))
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10667 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10669 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10667 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10669) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10682 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10684 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10682 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10684)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.const_mul' Monotone.const_mul'ₓ'. -/
@[to_additive const_add]
theorem Monotone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a
#align monotone.const_mul' Monotone.const_mul'

/- warning: monotone_on.const_mul' -> MonotoneOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10753 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10755 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10753 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10755) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10768 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10770 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10768 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10770)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.const_mul' MonotoneOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem MonotoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a
#align monotone_on.const_mul' MonotoneOn.const_mul'

/- warning: antitone.const_mul' -> Antitone.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10847 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10849 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10847 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10849) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10862 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10864 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10862 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10864)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.const_mul' Antitone.const_mul'ₓ'. -/
@[to_additive const_add]
theorem Antitone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a
#align antitone.const_mul' Antitone.const_mul'

/- warning: antitone_on.const_mul' -> AntitoneOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) a (f x)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10933 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10935 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10933 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10935) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10948 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10950 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10948 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10950)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) a (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.const_mul' AntitoneOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem AntitoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a
#align antitone_on.const_mul' AntitoneOn.const_mul'

/- warning: monotone.mul_const' -> Monotone.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11030 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11032 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11030 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11032)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11045 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11047 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11045 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11047)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a))
Case conversion may be inaccurate. Consider using '#align monotone.mul_const' Monotone.mul_const'ₓ'. -/
@[to_additive add_const]
theorem Monotone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a
#align monotone.mul_const' Monotone.mul_const'

/- warning: monotone_on.mul_const' -> MonotoneOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (MonotoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11119 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11121 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11119 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11121)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11134 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11136 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11134 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11136)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.mul_const' MonotoneOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem MonotoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s)
    (a : α) : MonotoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a
#align monotone_on.mul_const' MonotoneOn.mul_const'

/- warning: antitone.mul_const' -> Antitone.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Antitone.{u2, u1} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11216 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11218 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11216 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11218)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11231 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11233 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11231 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11233)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a))
Case conversion may be inaccurate. Consider using '#align antitone.mul_const' Antitone.mul_const'ₓ'. -/
@[to_additive add_const]
theorem Antitone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a
#align antitone.mul_const' Antitone.mul_const'

/- warning: antitone_on.mul_const' -> AntitoneOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {s : Set.{u2} β} [_inst_4 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (AntitoneOn.{u2, u1} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) a) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11305 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11307 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11305 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11307)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11320 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11322 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11320 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11322)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) a) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.mul_const' AntitoneOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem AntitoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : AntitoneOn f s)
    (a : α) : AntitoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a
#align antitone_on.mul_const' AntitoneOn.mul_const'

/- warning: monotone.mul' -> Monotone.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : Preorder.{u2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))] [_inst_5 : CovariantClass.{u1, u1} α α (Function.swap.{succ u1, succ u1, succ u1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1))) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_2))], (Monotone.{u2, u1} β α _inst_3 _inst_2 f) -> (Monotone.{u2, u1} β α _inst_3 _inst_2 g) -> (Monotone.{u2, u1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11399 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11401 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11399 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11401) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11414 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11416 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11414 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11416)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11436 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11438 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11436 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11438)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11451 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11453 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11451 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11453)], (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (Monotone.{u1, u2} β α _inst_3 _inst_2 g) -> (Monotone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11527 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11529 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11527 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11529) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11542 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11544 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11542 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11544)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11564 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11566 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11564 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11566)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11579 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11581 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11579 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11581)], (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11666 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11668 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11666 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11668) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11681 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11683 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11681 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11683)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11703 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11705 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11703 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11705)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11718 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11720 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11718 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11720)], (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (Antitone.{u1, u2} β α _inst_3 _inst_2 g) -> (Antitone.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11794 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11796 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11794 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11796) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11809 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11811 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11809 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11811)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11831 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11833 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11831 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11833)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11846 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11848 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11846 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11848)], (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12782 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12784 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12782 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12784) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12797 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12799 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12797 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12799)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12819 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12821 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12819 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12821)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12834 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12836 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12834 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12836)], (StrictMono.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12910 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12912 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12910 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12912) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12925 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12927 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12925 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12927)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12947 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12949 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12947 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12949)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12962 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12964 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12962 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12964)], (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13049 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13051 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13049 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13051) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13064 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13066 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13064 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13066)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13086 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13088 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13086 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13088)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13101 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13103 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13101 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13103)], (StrictAnti.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {f : β -> α} {g : β -> α} {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13177 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13179 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13177 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13179) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13192 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13194 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13192 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13194)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13214 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13216 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13214 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13216)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13229 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13231 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13229 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13231)], (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13316 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13318 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13316 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13318) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13331 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13333 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13331 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13333)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13353 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13355 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13353 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13355)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13368 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13370 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13368 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13370)] {f : β -> α} {g : β -> α}, (Monotone.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictMono.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13450 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13452 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13450 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13452) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13465 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13467 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13465 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13467)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13487 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13489 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13487 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13489)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13502 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13504 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13502 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13504)] {f : β -> α} {g : β -> α}, (MonotoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13595 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13597 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13595 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13597) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13610 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13612 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13610 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13612)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13632 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13634 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13632 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13634)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13647 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13649 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13647 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13649)] {f : β -> α} {g : β -> α}, (Antitone.{u1, u2} β α _inst_3 _inst_2 f) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 g) -> (StrictAnti.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)))
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Mul.{u2} α] [_inst_2 : Preorder.{u2} α] [_inst_3 : Preorder.{u1} β] {s : Set.{u1} β} [_inst_4 : CovariantClass.{u2, u2} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13729 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13731 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13729 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13731) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13744 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13746 : α) => LT.lt.{u2} α (Preorder.toLT.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13744 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13746)] [_inst_5 : CovariantClass.{u2, u2} α α (Function.swap.{succ u2, succ u2, succ u2} α α (fun (ᾰ : α) (ᾰ : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13766 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13768 : α) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13766 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13768)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13781 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13783 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13781 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13783)] {f : β -> α} {g : β -> α}, (AntitoneOn.{u1, u2} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u1, u2} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α _inst_1) (f x) (g x)) s)
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
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommSemigroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15240 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15242 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15240 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15242) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15255 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15257 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15255 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15257)] {a : α} {b : α} {c : α}, (MulLECancellable.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2)) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) b a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_2))) c a)) (LE.le.{u1} α _inst_1 b c))
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
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15339 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15341 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15339 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15341) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15354 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15356 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15354 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15356)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2))) b))
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
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : MulOneClass.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15435 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15437 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15435 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15437) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15450 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15452 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15450 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15452)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_2)) a b) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_2)))))
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
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15531 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15533 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15531 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15533) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15546 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15548 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15546 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15548)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a)) (LE.le.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b))
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
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] [_inst_2 : CommMonoid.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15624 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15626 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15624 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15626) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15639 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15641 : α) => LE.le.{u1} α _inst_1 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15639 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15641)] {a : α} {b : α}, (MulLECancellable.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))) b a) a) (LE.le.{u1} α _inst_1 b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2))))))
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

