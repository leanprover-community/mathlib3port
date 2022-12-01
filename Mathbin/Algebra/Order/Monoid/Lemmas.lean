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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α _inst_2)] {a : α} {b : α}, (LE.le.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α _inst_2 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2740 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2743 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2746 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2753 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2755 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2740)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2753 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2755) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2768 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2770 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2743 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2768 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2770)] {a : α} {b : α}, (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2743 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2740))) b) -> (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2743 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2740)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α _inst_2)] {a : α} {b : α}, (LE.le.{u_1} α _inst_2 b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2822 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2825 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2828 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2835 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2837 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2822)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2835 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2837) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2850 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2852 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2825 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2850 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2852)] {a : α} {b : α}, (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2825 b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2822)))) -> (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2825 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2822)) a b) a)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α _inst_2)] {a : α} {b : α}, (LE.le.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α _inst_2 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2901 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2904 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2907 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2917 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2919 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2901)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2917 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2919)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2932 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2934 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2904 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2932 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2934)] {a : α} {b : α}, (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2904 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2901))) b) -> (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2904 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2901)) b a))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α _inst_2)] {a : α} {b : α}, (LE.le.{u_1} α _inst_2 b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2986 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2989 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2992 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3002 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3004 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2986)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3002 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3004)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3017 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3019 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2989 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3017 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3019)] {a : α} {b : α}, (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2989 b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2986)))) -> (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2989 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.2986)) b a) a)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α _inst_2)] {a : α} {b : α}, (LE.le.{u_1} α _inst_2 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) -> (LE.le.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3068 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3071 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3074 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3081 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3083 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3068)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3081 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3083) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3096 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3098 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3071 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3096 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3098)] {a : α} {b : α}, (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3071 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3068)) a b)) -> (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3071 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3068))) b)
Case conversion may be inaccurate. Consider using '#align one_le_of_le_mul_right one_le_of_le_mul_rightₓ'. -/
@[to_additive]
theorem one_le_of_le_mul_right [ContravariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : a ≤ a * b) :
    1 ≤ b :=
  le_of_mul_le_mul_left' <| by simpa only [mul_one]
#align one_le_of_le_mul_right one_le_of_le_mul_right

/- warning: le_one_of_mul_le_right -> le_one_of_mul_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α _inst_2)] {a : α} {b : α}, (LE.le.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a) -> (LE.le.{u_1} α _inst_2 b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3145 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3148 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3151 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3158 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3160 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3145)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3158 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3160) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3173 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3175 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3148 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3173 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3175)] {a : α} {b : α}, (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3148 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3145)) a b) a) -> (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3148 b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3145))))
Case conversion may be inaccurate. Consider using '#align le_one_of_mul_le_right le_one_of_mul_le_rightₓ'. -/
@[to_additive]
theorem le_one_of_mul_le_right [ContravariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : a * b ≤ a) :
    b ≤ 1 :=
  le_of_mul_le_mul_left' <| by simpa only [mul_one]
#align le_one_of_mul_le_right le_one_of_mul_le_right

/- warning: one_le_of_le_mul_left -> one_le_of_le_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α _inst_2)] {a : α} {b : α}, (LE.le.{u_1} α _inst_2 b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) -> (LE.le.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3222 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3225 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3228 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3238 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3240 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3222)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3238 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3240)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3253 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3255 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3225 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3253 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3255)] {a : α} {b : α}, (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3225 b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3222)) a b)) -> (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3225 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3222))) a)
Case conversion may be inaccurate. Consider using '#align one_le_of_le_mul_left one_le_of_le_mul_leftₓ'. -/
@[to_additive]
theorem one_le_of_le_mul_left [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (h : b ≤ a * b) : 1 ≤ a :=
  le_of_mul_le_mul_right' <| by simpa only [one_mul]
#align one_le_of_le_mul_left one_le_of_le_mul_left

/- warning: le_one_of_mul_le_left -> le_one_of_mul_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α _inst_2)] {a : α} {b : α}, (LE.le.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) b) -> (LE.le.{u_1} α _inst_2 a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3302 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3305 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3308 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3318 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3320 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3302)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3318 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3320)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3333 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3335 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3305 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3333 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3335)] {a : α} {b : α}, (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3305 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3302)) a b) b) -> (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3305 a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3302))))
Case conversion may be inaccurate. Consider using '#align le_one_of_mul_le_left le_one_of_mul_le_leftₓ'. -/
@[to_additive]
theorem le_one_of_mul_le_left [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (h : a * b ≤ b) : a ≤ 1 :=
  le_of_mul_le_mul_right' <| by simpa only [one_mul]
#align le_one_of_mul_le_left le_one_of_mul_le_left

/- warning: le_mul_iff_one_le_right' -> le_mul_iff_one_le_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α _inst_2)] [_inst_4 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u_1} α _inst_2 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) (LE.le.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3382 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3385 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3388 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3395 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3397 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3382)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3395 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3397) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3410 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3412 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3385 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3410 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3412)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3422 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3429 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3431 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3382)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3429 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3431) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3444 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3446 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3385 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3444 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3446)] (a : α) {b : α}, Iff (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3385 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3382)) a b)) (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3385 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3382))) b)
Case conversion may be inaccurate. Consider using '#align le_mul_iff_one_le_right' le_mul_iff_one_le_right'ₓ'. -/
@[simp, to_additive le_add_iff_nonneg_right]
theorem le_mul_iff_one_le_right' [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b : α} : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)
#align le_mul_iff_one_le_right' le_mul_iff_one_le_right'

/- warning: le_mul_iff_one_le_left' -> le_mul_iff_one_le_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α _inst_2)] [_inst_4 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u_1} α _inst_2 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a)) (LE.le.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3511 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3514 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3517 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3527 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3529 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3511)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3527 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3529)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3542 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3544 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3514 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3542 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3544)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3554 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3564 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3566 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3511)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3564 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3566)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3579 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3581 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3514 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3579 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3581)] (a : α) {b : α}, Iff (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3514 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3511)) b a)) (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3514 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3511))) b)
Case conversion may be inaccurate. Consider using '#align le_mul_iff_one_le_left' le_mul_iff_one_le_left'ₓ'. -/
@[simp, to_additive le_add_iff_nonneg_left]
theorem le_mul_iff_one_le_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) {b : α} : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a)
#align le_mul_iff_one_le_left' le_mul_iff_one_le_left'

/- warning: mul_le_iff_le_one_right' -> mul_le_iff_le_one_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α _inst_2)] [_inst_4 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α _inst_2)] (a : α) {b : α}, Iff (LE.le.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a) (LE.le.{u_1} α _inst_2 b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3646 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3649 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3652 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3659 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3661 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3646)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3659 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3661) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3674 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3676 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3649 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3674 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3676)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3686 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3693 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3695 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3646)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3693 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3695) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3708 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3710 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3649 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3708 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3710)] (a : α) {b : α}, Iff (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3649 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3646)) a b) a) (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3649 b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3646))))
Case conversion may be inaccurate. Consider using '#align mul_le_iff_le_one_right' mul_le_iff_le_one_right'ₓ'. -/
@[simp, to_additive add_le_iff_nonpos_right]
theorem mul_le_iff_le_one_right' [CovariantClass α α (· * ·) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α) {b : α} : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)
#align mul_le_iff_le_one_right' mul_le_iff_le_one_right'

/- warning: mul_le_iff_le_one_left' -> mul_le_iff_le_one_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LE.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α _inst_2)] [_inst_4 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α _inst_2)] {a : α} {b : α}, Iff (LE.le.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) b) (LE.le.{u_1} α _inst_2 a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3775 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3778 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3781 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3791 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3793 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3775)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3791 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3793)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3806 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3808 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3778 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3806 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3808)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3818 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3828 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3830 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3775)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3828 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3830)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3843 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3845 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3778 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3843 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3845)] {a : α} {b : α}, Iff (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3778 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3775)) a b) b) (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3778 a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3775))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α _inst_2 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3922 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3925 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3928 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3935 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3937 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3922)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3935 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3937) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3950 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3952 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3925 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3950 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3952)] (a : α) {b : α}, (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3925 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3922))) b) -> (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3925 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.3922)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u_1} α _inst_2 b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4004 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4007 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4010 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4017 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4019 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4004)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4017 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4019) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4032 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4034 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4007 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4032 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4034)] (a : α) {b : α}, (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4007 b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4004)))) -> (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4007 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4004)) a b) a)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α _inst_2 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4083 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4086 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4089 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4099 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4101 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4083)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4099 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4101)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4114 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4116 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4086 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4114 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4116)] (a : α) {b : α}, (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4086 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4083))) b) -> (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4086 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4083)) b a))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α _inst_2)] (a : α) {b : α}, (LT.lt.{u_1} α _inst_2 b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4168 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4171 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4174 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4184 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4186 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4168)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4184 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4186)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4199 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4201 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4171 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4199 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4201)] (a : α) {b : α}, (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4171 b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4168)))) -> (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4171 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4168)) b a) a)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u_1} α _inst_2 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) -> (LT.lt.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4250 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4253 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4256 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4263 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4265 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4250)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4263 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4265) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4278 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4280 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4253 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4278 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4280)] {a : α} {b : α}, (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4253 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4250)) a b)) -> (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4253 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4250))) b)
Case conversion may be inaccurate. Consider using '#align one_lt_of_lt_mul_right one_lt_of_lt_mul_rightₓ'. -/
@[to_additive]
theorem one_lt_of_lt_mul_right [ContravariantClass α α (· * ·) (· < ·)] {a b : α} (h : a < a * b) :
    1 < b :=
  lt_of_mul_lt_mul_left' <| by simpa only [mul_one]
#align one_lt_of_lt_mul_right one_lt_of_lt_mul_right

/- warning: lt_one_of_mul_lt_right -> lt_one_of_mul_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a) -> (LT.lt.{u_1} α _inst_2 b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4327 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4330 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4333 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4340 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4342 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4327)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4340 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4342) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4355 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4357 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4330 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4355 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4357)] {a : α} {b : α}, (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4330 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4327)) a b) a) -> (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4330 b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4327))))
Case conversion may be inaccurate. Consider using '#align lt_one_of_mul_lt_right lt_one_of_mul_lt_rightₓ'. -/
@[to_additive]
theorem lt_one_of_mul_lt_right [ContravariantClass α α (· * ·) (· < ·)] {a b : α} (h : a * b < a) :
    b < 1 :=
  lt_of_mul_lt_mul_left' <| by simpa only [mul_one]
#align lt_one_of_mul_lt_right lt_one_of_mul_lt_right

/- warning: one_lt_of_lt_mul_left -> one_lt_of_lt_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u_1} α _inst_2 b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) -> (LT.lt.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4404 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4407 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4410 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4420 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4422 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4404)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4420 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4422)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4435 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4437 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4407 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4435 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4437)] {a : α} {b : α}, (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4407 b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4404)) a b)) -> (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4407 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4404))) a)
Case conversion may be inaccurate. Consider using '#align one_lt_of_lt_mul_left one_lt_of_lt_mul_leftₓ'. -/
@[to_additive]
theorem one_lt_of_lt_mul_left [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right' <| by simpa only [one_mul]
#align one_lt_of_lt_mul_left one_lt_of_lt_mul_left

/- warning: lt_one_of_mul_lt_left -> lt_one_of_mul_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) b) -> (LT.lt.{u_1} α _inst_2 a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4484 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4487 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4490 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4500 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4502 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4484)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4500 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4502)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4515 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4517 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4487 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4515 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4517)] {a : α} {b : α}, (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4487 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4484)) a b) b) -> (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4487 a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4484))))
Case conversion may be inaccurate. Consider using '#align lt_one_of_mul_lt_left lt_one_of_mul_lt_leftₓ'. -/
@[to_additive]
theorem lt_one_of_mul_lt_left [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b : α}
    (h : a * b < b) : a < 1 :=
  lt_of_mul_lt_mul_right' <| by simpa only [one_mul]
#align lt_one_of_mul_lt_left lt_one_of_mul_lt_left

/- warning: lt_mul_iff_one_lt_right' -> lt_mul_iff_one_lt_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α _inst_2)] [_inst_4 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α _inst_2)] (a : α) {b : α}, Iff (LT.lt.{u_1} α _inst_2 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) (LT.lt.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4564 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4567 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4570 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4577 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4579 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4564)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4577 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4579) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4592 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4594 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4567 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4592 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4594)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4604 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4611 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4613 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4564)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4611 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4613) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4626 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4628 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4567 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4626 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4628)] (a : α) {b : α}, Iff (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4567 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4564)) a b)) (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4567 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4564))) b)
Case conversion may be inaccurate. Consider using '#align lt_mul_iff_one_lt_right' lt_mul_iff_one_lt_right'ₓ'. -/
@[simp, to_additive lt_add_iff_pos_right]
theorem lt_mul_iff_one_lt_right' [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] (a : α) {b : α} : a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)
#align lt_mul_iff_one_lt_right' lt_mul_iff_one_lt_right'

/- warning: lt_mul_iff_one_lt_left' -> lt_mul_iff_one_lt_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α _inst_2)] [_inst_4 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α _inst_2)] (a : α) {b : α}, Iff (LT.lt.{u_1} α _inst_2 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a)) (LT.lt.{u_1} α _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4693 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4696 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4699 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4709 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4711 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4693)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4709 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4711)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4724 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4726 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4696 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4724 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4726)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4736 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4746 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4748 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4693)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4746 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4748)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4761 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4763 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4696 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4761 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4763)] (a : α) {b : α}, Iff (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4696 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4693)) b a)) (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4696 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4693))) b)
Case conversion may be inaccurate. Consider using '#align lt_mul_iff_one_lt_left' lt_mul_iff_one_lt_left'ₓ'. -/
@[simp, to_additive lt_add_iff_pos_left]
theorem lt_mul_iff_one_lt_left' [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α} : a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a)
#align lt_mul_iff_one_lt_left' lt_mul_iff_one_lt_left'

/- warning: mul_lt_iff_lt_one_left' -> mul_lt_iff_lt_one_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α _inst_2)] [_inst_4 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α _inst_2)] {a : α} {b : α}, Iff (LT.lt.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a) (LT.lt.{u_1} α _inst_2 b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4828 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4831 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4834 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4841 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4843 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4828)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4841 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4843) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4856 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4858 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4831 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4856 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4858)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4868 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4875 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4877 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4828)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4875 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4877) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4890 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4892 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4831 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4890 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4892)] {a : α} {b : α}, Iff (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4831 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4828)) a b) a) (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4831 b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4828))))
Case conversion may be inaccurate. Consider using '#align mul_lt_iff_lt_one_left' mul_lt_iff_lt_one_left'ₓ'. -/
@[simp, to_additive add_lt_iff_neg_left]
theorem mul_lt_iff_lt_one_left' [CovariantClass α α (· * ·) (· < ·)]
    [ContravariantClass α α (· * ·) (· < ·)] {a b : α} : a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)
#align mul_lt_iff_lt_one_left' mul_lt_iff_lt_one_left'

/- warning: mul_lt_iff_lt_one_right' -> mul_lt_iff_lt_one_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LT.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α _inst_2)] [_inst_4 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α _inst_2)] {a : α} (b : α), Iff (LT.lt.{u_1} α _inst_2 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) b) (LT.lt.{u_1} α _inst_2 a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4957 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4960 : LT.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4963 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4973 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4975 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4957)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4973 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4975)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4988 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4990 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4960 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4988 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4990)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5000 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5010 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5012 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4957)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5010 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5012)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5025 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5027 : α) => LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4960 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5025 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5027)] {a : α} (b : α), Iff (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4960 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4957)) a b) b) (LT.lt.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4960 a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.4957))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5105 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5108 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5111 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5118 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5120 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5105)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5118 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5120) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5133 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5135 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5108) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5133 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5135)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5108) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5108) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5105)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5108) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5105)) b a) c)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5198 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5201 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5204 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5211 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5213 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5198)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5211 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5213) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5226 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5228 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5201) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5226 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5228)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5201) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5201) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5198)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5201) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5198)) b a) c)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5291 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5294 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5297 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5304 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5306 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5291)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5304 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5306) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5319 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5321 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5294) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5319 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5321)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5294) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5294) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5291)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5294) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5291)) b a) c)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5384 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5387 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5390 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5397 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5399 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5384)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5397 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5399) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5412 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5414 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5387) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5412 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5414)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5387) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5387) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5384)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5387) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5384)) b a) c)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5477 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5480 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5483 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5490 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5492 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5477)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5490 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5492) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5505 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5507 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5480) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5505 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5507)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5480) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5480) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5477)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5480) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5477)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_lt_one' mul_lt_of_lt_of_lt_one'ₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_of_lt_one' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : a < 1) : b * a < c :=
  mul_lt_of_lt_of_le_one hbc ha.le
#align mul_lt_of_lt_of_lt_one' mul_lt_of_lt_of_lt_one'

/- warning: left.mul_le_one -> Left.mul_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5546 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5549 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5552 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5559 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5561 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5546)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5559 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5561) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5574 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5576 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5549) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5574 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5576)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5549) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5546)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5549) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5546)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5549) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5546)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5546))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5617 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5620 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5623 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5630 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5632 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5617)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5630 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5632) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5645 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5647 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5620) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5645 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5647)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5620) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5617)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5620) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5617)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5620) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5617)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5617))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5688 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5691 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5694 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5701 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5703 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5688)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5701 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5703) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5716 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5718 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5691) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5716 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5718)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5691) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5688)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5691) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5688)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5691) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5688)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5688))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5759 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5762 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5765 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5772 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5774 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5759)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5772 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5774) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5787 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5789 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5762) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5787 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5789)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5762) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5759)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5762) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5759)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5762) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5759)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5759))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5830 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5833 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5836 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5843 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5845 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5830)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5843 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5845) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5858 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5860 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5833) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5858 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5860)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5833) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5830)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5833) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5830)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5833) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5830)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5830))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5899 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5902 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5905 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5912 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5914 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5899)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5912 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5914) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5927 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5929 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5902) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5927 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5929)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5902) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5902) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5899))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5902) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5899)) c a))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5995 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5998 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6001 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6008 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6010 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5995)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6008 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6010) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6023 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6025 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5998) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6023 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6025)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5998) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5998) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5995))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5998) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.5995)) c a))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6091 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6094 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6097 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6104 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6106 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6091)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6104 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6106) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6119 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6121 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6094) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6119 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6121)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6094) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6094) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6091))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6094) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6091)) c a))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6187 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6190 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6193 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6200 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6202 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6187)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6200 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6202) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6215 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6217 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6190) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6215 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6217)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6190) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6190) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6187))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6190) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6187)) c a))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6283 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6286 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6289 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6296 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6298 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6283)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6296 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6298) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6311 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6313 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6286) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6311 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6313)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6286) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6286) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6283))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6286) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6283)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_lt' lt_mul_of_lt_of_one_lt'ₓ'. -/
@[to_additive]
theorem lt_mul_of_lt_of_one_lt' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c)
    (ha : 1 < a) : b < c * a :=
  lt_mul_of_lt_of_one_le hbc ha.le
#align lt_mul_of_lt_of_one_lt' lt_mul_of_lt_of_one_lt'

/- warning: left.one_le_mul -> Left.one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6352 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6355 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6358 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6365 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6367 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6352)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6365 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6367) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6380 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6382 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6355) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6380 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6382)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6355) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6352))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6355) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6352))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6355) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6352))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6352)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6423 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6426 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6429 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6436 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6438 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6423)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6436 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6438) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6451 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6453 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6426) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6451 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6453)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6426) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6423))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6426) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6423))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6426) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6423))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6423)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6494 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6497 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6500 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6507 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6509 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6494)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6507 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6509) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6522 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6524 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6497) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6522 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6524)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6497) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6494))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6497) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6494))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6497) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6494))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6494)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6565 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6568 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6571 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6578 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6580 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6565)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6578 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6580) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6593 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6595 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6568) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6593 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6595)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6568) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6565))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6568) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6565))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6568) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6565))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6565)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6636 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6639 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6642 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6649 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6651 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6636)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6649 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6651) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6664 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6666 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6639) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6664 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6666)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6639) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6636))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6639) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6636))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6639) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6636))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6636)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6705 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6708 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6711 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6721 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6723 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6705)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6721 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6723)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6736 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6738 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6708) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6736 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6738)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6708) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6705)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6708) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6708) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6705)) a b) c)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6801 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6804 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6807 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6817 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6819 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6801)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6817 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6819)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6832 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6834 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6804) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6832 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6834)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6804) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6801)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6804) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6804) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6801)) a b) c)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6897 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6900 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6903 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6913 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6915 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6897)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6913 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6915)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6928 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6930 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6900) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6928 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6930)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6900) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6897)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6900) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6900) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6897)) a b) c)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6993 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6996 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6999 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7009 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7011 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6993)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7009 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7011)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7024 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7026 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6996) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7024 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7026)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6996) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6993)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6996) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6996) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.6993)) a b) c)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7089 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7092 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7095 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7105 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7107 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7089)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7105 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7107)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7120 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7122 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7092) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7120 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7122)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7092) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7089)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7092) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7092) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7089)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_lt' mul_lt_of_lt_one_of_lt'ₓ'. -/
@[to_additive]
theorem mul_lt_of_lt_one_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a < 1)
    (hbc : b < c) : a * b < c :=
  mul_lt_of_le_one_of_lt ha.le hbc
#align mul_lt_of_lt_one_of_lt' mul_lt_of_lt_one_of_lt'

/- warning: right.mul_le_one -> Right.mul_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7161 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7164 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7167 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7177 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7179 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7161)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7177 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7179)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7192 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7194 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7164) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7192 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7194)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7164) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7161)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7164) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7161)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7164) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7161)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7161))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7235 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7238 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7241 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7251 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7253 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7235)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7251 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7253)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7266 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7268 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7238) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7266 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7268)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7238) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7235)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7238) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7235)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7238) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7235)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7235))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7309 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7312 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7315 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7325 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7327 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7309)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7325 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7327)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7340 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7342 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7312) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7340 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7342)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7312) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7309)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7312) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7309)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7312) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7309)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7309))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7383 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7386 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7389 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7399 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7401 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7383)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7399 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7401)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7414 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7416 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7386) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7414 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7416)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7386) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7383)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7386) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7383)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7386) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7383)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7383))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7457 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7460 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7463 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7473 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7475 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7457)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7473 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7475)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7488 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7490 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7460) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7488 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7490)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7460) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7457)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7460) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7457)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7460) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7457)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7457))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7529 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7532 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7535 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7545 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7547 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7529)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7545 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7547)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7560 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7562 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7532) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7560 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7562)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7532) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7529))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7532) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7532) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7529)) a c))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7628 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7631 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7634 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7644 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7646 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7628)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7644 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7646)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7659 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7661 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7631) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7659 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7661)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7631) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7628))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7631) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7631) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7628)) a c))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7727 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7730 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7733 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7743 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7745 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7727)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7743 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7745)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7758 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7760 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7730) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7758 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7760)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7730) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7727))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7730) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7730) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7727)) a c))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7826 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7829 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7832 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7842 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7844 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7826)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7842 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7844)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7857 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7859 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7829) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7857 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7859)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7829) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7826))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7829) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7829) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7826)) a c))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7925 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7928 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7931 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7941 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7943 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7925)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7941 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7943)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7956 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7958 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7928) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7956 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7958)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7928) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7925))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7928) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7928) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7925)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_lt' lt_mul_of_one_lt_of_lt'ₓ'. -/
@[to_additive]
theorem lt_mul_of_one_lt_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 < a)
    (hbc : b < c) : b < a * c :=
  lt_mul_of_one_le_of_lt ha.le hbc
#align lt_mul_of_one_lt_of_lt' lt_mul_of_one_lt_of_lt'

/- warning: right.one_le_mul -> Right.one_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7997 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8000 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8003 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8013 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8015 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7997)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8013 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8015)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8028 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8030 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8000) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8028 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8030)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8000) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7997))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8000) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7997))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8000) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7997))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.7997)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8071 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8074 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8077 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8087 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8089 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8071)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8087 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8089)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8102 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8104 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8074) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8102 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8104)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8074) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8071))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8074) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8071))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8074) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8071))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8071)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8145 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8148 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8151 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8161 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8163 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8145)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8161 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8163)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8176 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8178 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8148) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8176 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8178)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8148) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8145))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8148) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8145))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8148) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8145))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8145)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8219 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8222 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8225 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8235 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8237 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8219)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8235 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8237)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8250 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8252 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8222) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8250 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8252)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8222) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8219))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8222) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8219))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8222) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8219))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8219)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8293 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8296 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8299 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8309 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8311 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8293)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8309 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8311)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8324 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8326 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8296) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8324 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8326)] {a : α} {b : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8296) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8293))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8296) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8293))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8296) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8293))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8293)) a b))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8384 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8387 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8390 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8397 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8399 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8384)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8397 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8399) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8412 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8414 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8387) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8412 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8414)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8387) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8384)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8387) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8384))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8387) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_mul_lt_of_one_le_left lt_of_mul_lt_of_one_le_leftₓ'. -/
@[to_additive]
theorem lt_of_mul_lt_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b < c)
    (hle : 1 ≤ b) : a < c :=
  (le_mul_of_one_le_right' hle).trans_lt h
#align lt_of_mul_lt_of_one_le_left lt_of_mul_lt_of_one_le_left

/- warning: le_of_mul_le_of_one_le_left -> le_of_mul_le_of_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8453 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8456 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8459 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8466 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8468 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8453)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8466 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8468) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8481 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8483 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8456) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8481 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8483)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8456) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8453)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8456) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8453))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8456) a c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_left le_of_mul_le_of_one_le_leftₓ'. -/
@[to_additive]
theorem le_of_mul_le_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b ≤ c)
    (hle : 1 ≤ b) : a ≤ c :=
  (le_mul_of_one_le_right' hle).trans h
#align le_of_mul_le_of_one_le_left le_of_mul_le_of_one_le_left

/- warning: lt_of_lt_mul_of_le_one_left -> lt_of_lt_mul_of_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) c (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8522 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8525 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8528 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8535 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8537 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8522)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8535 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8537) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8550 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8552 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8525) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8550 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8552)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8525) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8522)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8525) c (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8522)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8525) a b)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_left lt_of_lt_mul_of_le_one_leftₓ'. -/
@[to_additive]
theorem lt_of_lt_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a < b * c)
    (hle : c ≤ 1) : a < b :=
  h.trans_le (mul_le_of_le_one_right' hle)
#align lt_of_lt_mul_of_le_one_left lt_of_lt_mul_of_le_one_left

/- warning: le_of_le_mul_of_le_one_left -> le_of_le_mul_of_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) c (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a b)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8590 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8593 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8596 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8603 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8605 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8590)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8603 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8605) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8618 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8620 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8593) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8618 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8620)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8593) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8590)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8593) c (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8590)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8593) a b)
Case conversion may be inaccurate. Consider using '#align le_of_le_mul_of_le_one_left le_of_le_mul_of_le_one_leftₓ'. -/
@[to_additive]
theorem le_of_le_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a ≤ b * c)
    (hle : c ≤ 1) : a ≤ b :=
  h.trans (mul_le_of_le_one_right' hle)
#align le_of_le_mul_of_le_one_left le_of_le_mul_of_le_one_left

/- warning: lt_of_mul_lt_of_one_le_right -> lt_of_mul_lt_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8658 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8661 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8664 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8674 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8676 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8658)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8674 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8676)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8689 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8691 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8661) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8689 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8691)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8661) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8658)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8661) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8658))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8661) b c)
Case conversion may be inaccurate. Consider using '#align lt_of_mul_lt_of_one_le_right lt_of_mul_lt_of_one_le_rightₓ'. -/
@[to_additive]
theorem lt_of_mul_lt_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b < c) (hle : 1 ≤ a) : b < c :=
  (le_mul_of_one_le_left' hle).trans_lt h
#align lt_of_mul_lt_of_one_le_right lt_of_mul_lt_of_one_le_right

/- warning: le_of_mul_le_of_one_le_right -> le_of_mul_le_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8730 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8733 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8736 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8746 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8748 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8730)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8746 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8748)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8761 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8763 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8733) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8761 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8763)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8733) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8730)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8733) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8730))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8733) b c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_right le_of_mul_le_of_one_le_rightₓ'. -/
@[to_additive]
theorem le_of_mul_le_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
  (le_mul_of_one_le_left' hle).trans h
#align le_of_mul_le_of_one_le_right le_of_mul_le_of_one_le_right

/- warning: lt_of_lt_mul_of_le_one_right -> lt_of_lt_mul_of_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8802 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8805 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8808 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8818 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8820 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8802)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8818 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8820)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8833 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8835 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8805) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8833 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8835)] {a : α} {b : α} {c : α}, (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8805) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8802)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8805) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8802)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8805) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_right lt_of_lt_mul_of_le_one_rightₓ'. -/
@[to_additive]
theorem lt_of_lt_mul_of_le_one_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α}
    (h : a < b * c) (hle : b ≤ 1) : a < c :=
  h.trans_le (mul_le_of_le_one_left' hle)
#align lt_of_lt_mul_of_le_one_right lt_of_lt_mul_of_le_one_right

/- warning: le_of_le_mul_of_le_one_right -> le_of_le_mul_of_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a c)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8873 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8876 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8879 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8889 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8891 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8873)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8889 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8891)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8904 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8906 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8876) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8904 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8906)] {a : α} {b : α} {c : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8876) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8873)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8876) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8873)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8876) a c)
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] [_inst_4 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) (And (Eq.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) (Eq.{succ u_1} α b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8956 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8959 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8962 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8969 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8971 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8956)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8969 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8971) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8984 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8986 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8959)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8984 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8986)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8996 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9006 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9008 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8956)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9006 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9008)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9021 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9023 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8959)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9021 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9023)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8959)) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8956))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8959)) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8956))) b) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8956)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8956)))) (And (Eq.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8956)))) (Eq.{succ u_1} α b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.8956))))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) -> (Eq.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9260 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9263 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9266 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9273 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9275 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9260)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9273 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9275) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9288 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9290 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9263)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9288 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9290)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9263)) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9260)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9263)) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9260)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9263)) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9260))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9260)) a b)) -> (Eq.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9260))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_leftₓ'. -/
@[to_additive eq_zero_of_add_nonneg_left]
theorem eq_one_of_one_le_mul_left (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : a = 1 :=
  ha.eq_of_not_lt fun h => hab.not_lt <| mul_lt_one_of_lt_of_le h hb
#align eq_one_of_one_le_mul_left eq_one_of_one_le_mul_left

/- warning: eq_one_of_mul_le_one_left -> eq_one_of_mul_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (Eq.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9337 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9340 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9343 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9350 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9352 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9337)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9350 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9352) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9365 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9367 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9340)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9365 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9367)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9340)) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9337))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9340)) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9337))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9340)) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9337)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9337)))) -> (Eq.{succ u_1} α a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9337))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) -> (Eq.{succ u_1} α b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9467 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9470 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9473 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9483 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9485 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9467)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9483 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9485)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9498 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9500 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9470)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9498 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9500)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9470)) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9467)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9470)) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9467)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9470)) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9467))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9467)) a b)) -> (Eq.{succ u_1} α b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9467))))
Case conversion may be inaccurate. Consider using '#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_rightₓ'. -/
@[to_additive eq_zero_of_add_nonneg_right]
theorem eq_one_of_one_le_mul_right (ha : a ≤ 1) (hb : b ≤ 1) (hab : 1 ≤ a * b) : b = 1 :=
  hb.eq_of_not_lt fun h => hab.not_lt <| Right.mul_lt_one_of_le_of_lt ha h
#align eq_one_of_one_le_mul_right eq_one_of_one_le_mul_right

/- warning: eq_one_of_mul_le_one_right -> eq_one_of_mul_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (Eq.{succ u_1} α b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9547 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9550 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9553 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9563 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9565 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9547)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9563 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9565)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9578 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9580 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9550)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9578 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9580)] {a : α} {b : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9550)) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9547))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9550)) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9547))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9550)) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9547)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9547)))) -> (Eq.{succ u_1} α b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9547))))
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
  forall {α : Type.{u_1}} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))))] (a : α), Exists.{succ u_1} α (fun (b : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b b) a)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9640 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9643 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9646 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9653 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9655 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9640)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9653 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9655) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9668 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9670 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9643))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9668 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9670)] (a : α), Exists.{succ u_1} α (fun (b : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9643))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9640)) b b) a)
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
  forall {α : Type.{u_1}} [_inst_1 : Semigroup.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))], LeftCancelSemigroup.{u_1} α
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9923 : Semigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9926 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9929 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9936 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9938 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9923)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9936 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9938) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9951 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9953 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9926)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9951 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.9953)], LeftCancelSemigroup.{u_1} α
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
  forall {α : Type.{u_1}} [_inst_1 : Semigroup.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))], RightCancelSemigroup.{u_1} α
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10003 : Semigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10006 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10009 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10019 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10021 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10003)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10019 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10021)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10034 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10036 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10006)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10034 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10036)], RightCancelSemigroup.{u_1} α
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
  forall {α : Type.{u_1}} [_inst_1 : Semigroup.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] [_inst_4 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] [_inst_5 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] [_inst_6 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) a c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) b d) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) c d)) (And (Eq.{succ u_1} α a c) (Eq.{succ u_1} α b d)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10086 : Semigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10089 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10092 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10099 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10101 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10086)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10099 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10101) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10114 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10116 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10089)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10114 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10116)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10126 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10136 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10138 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10086)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10136 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10138)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10151 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10153 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10089)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10151 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10153)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10163 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10170 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10172 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10086)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10170 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10172) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10185 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10187 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10089)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10185 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10187)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10197 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10207 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10209 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10086)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10207 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10209)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10222 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10224 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10089)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10222 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10224)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10089)) a c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10089)) b d) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10086)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10086)) c d)) (And (Eq.{succ u_1} α a c) (Eq.{succ u_1} α b d)))
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
  forall {α : Type.{u_1}} [_inst_1 : Semigroup.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] [_inst_4 : ContravariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] [_inst_6 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)))] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) a c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) b d) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α _inst_1)) c d)) (And (Eq.{succ u_1} α a c) (Eq.{succ u_1} α b d)))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10349 : Semigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10352 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10355 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10362 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10364 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10349)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10362 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10364) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10377 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10379 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10352)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10377 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10379)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10389 : ContravariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10396 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10398 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10349)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10396 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10398) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10411 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10413 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10352)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10411 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10413)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10423 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10433 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10435 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10349)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10433 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10435)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10448 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10450 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10352)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10448 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10450)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10460 : ContravariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.141 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.139 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10470 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10472 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10349)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10470 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10472)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10485 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10487 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10352)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10485 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10487)] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10352)) a c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10352)) b d) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10349)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10349)) c d)) (And (Eq.{succ u_1} α a c) (Eq.{succ u_1} α b d)))
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
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (Monotone.{u_2, u_1} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) a (f x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10643 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10646 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10649 : Preorder.{u_2} β] {f : β -> α} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10660 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10667 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10669 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10643) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10667 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10669) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10682 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10684 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10646) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10682 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10684)], (Monotone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10649 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10646 f) -> (forall (a : α), Monotone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10649 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10646 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10643) a (f x)))
Case conversion may be inaccurate. Consider using '#align monotone.const_mul' Monotone.const_mul'ₓ'. -/
@[to_additive const_add]
theorem Monotone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a
#align monotone.const_mul' Monotone.const_mul'

/- warning: monotone_on.const_mul' -> MonotoneOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {s : Set.{u_2} β} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (MonotoneOn.{u_2, u_1} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) a (f x)) s)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10729 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10732 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10735 : Preorder.{u_2} β] {f : β -> α} {s : Set.{u_2} β} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10746 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10753 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10755 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10729) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10753 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10755) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10768 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10770 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10732) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10768 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10770)], (MonotoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10735 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10732 f s) -> (forall (a : α), MonotoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10735 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10732 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10729) a (f x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.const_mul' MonotoneOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem MonotoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a
#align monotone_on.const_mul' MonotoneOn.const_mul'

/- warning: antitone.const_mul' -> Antitone.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (Antitone.{u_2, u_1} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) a (f x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10823 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10826 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10829 : Preorder.{u_2} β] {f : β -> α} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10840 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10847 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10849 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10823) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10847 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10849) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10862 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10864 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10826) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10862 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10864)], (Antitone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10829 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10826 f) -> (forall (a : α), Antitone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10829 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10826 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10823) a (f x)))
Case conversion may be inaccurate. Consider using '#align antitone.const_mul' Antitone.const_mul'ₓ'. -/
@[to_additive const_add]
theorem Antitone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a
#align antitone.const_mul' Antitone.const_mul'

/- warning: antitone_on.const_mul' -> AntitoneOn.const_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {s : Set.{u_2} β} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (AntitoneOn.{u_2, u_1} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) a (f x)) s)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10909 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10912 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10915 : Preorder.{u_2} β] {f : β -> α} {s : Set.{u_2} β} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10926 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10933 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10935 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10909) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10933 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10935) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10948 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10950 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10912) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10948 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10950)], (AntitoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10915 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10912 f s) -> (forall (a : α), AntitoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10915 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10912 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.10909) a (f x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.const_mul' AntitoneOn.const_mul'ₓ'. -/
@[to_additive const_add]
theorem AntitoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a
#align antitone_on.const_mul' AntitoneOn.const_mul'

/- warning: monotone.mul_const' -> Monotone.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} [_inst_4 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (Monotone.{u_2, u_1} β α _inst_3 _inst_2 f) -> (forall (a : α), Monotone.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) a))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11003 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11006 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11009 : Preorder.{u_2} β] {f : β -> α} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11020 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11030 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11032 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11003) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11030 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11032)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11045 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11047 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11006) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11045 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11047)], (Monotone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11009 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11006 f) -> (forall (a : α), Monotone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11009 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11006 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11003) (f x) a))
Case conversion may be inaccurate. Consider using '#align monotone.mul_const' Monotone.mul_const'ₓ'. -/
@[to_additive add_const]
theorem Monotone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a
#align monotone.mul_const' Monotone.mul_const'

/- warning: monotone_on.mul_const' -> MonotoneOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {s : Set.{u_2} β} [_inst_4 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (MonotoneOn.{u_2, u_1} β α _inst_3 _inst_2 f s) -> (forall (a : α), MonotoneOn.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) a) s)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11092 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11095 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11098 : Preorder.{u_2} β] {f : β -> α} {s : Set.{u_2} β} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11109 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11119 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11121 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11092) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11119 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11121)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11134 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11136 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11095) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11134 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11136)], (MonotoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11098 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11095 f s) -> (forall (a : α), MonotoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11098 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11095 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11092) (f x) a) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.mul_const' MonotoneOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem MonotoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s)
    (a : α) : MonotoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a
#align monotone_on.mul_const' MonotoneOn.mul_const'

/- warning: antitone.mul_const' -> Antitone.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} [_inst_4 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (Antitone.{u_2, u_1} β α _inst_3 _inst_2 f) -> (forall (a : α), Antitone.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) a))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11189 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11192 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11195 : Preorder.{u_2} β] {f : β -> α} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11206 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11216 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11218 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11189) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11216 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11218)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11231 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11233 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11192) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11231 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11233)], (Antitone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11195 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11192 f) -> (forall (a : α), Antitone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11195 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11192 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11189) (f x) a))
Case conversion may be inaccurate. Consider using '#align antitone.mul_const' Antitone.mul_const'ₓ'. -/
@[to_additive add_const]
theorem Antitone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a
#align antitone.mul_const' Antitone.mul_const'

/- warning: antitone_on.mul_const' -> AntitoneOn.mul_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {s : Set.{u_2} β} [_inst_4 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (AntitoneOn.{u_2, u_1} β α _inst_3 _inst_2 f s) -> (forall (a : α), AntitoneOn.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) a) s)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11278 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11281 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11284 : Preorder.{u_2} β] {f : β -> α} {s : Set.{u_2} β} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11295 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11305 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11307 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11278) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11305 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11307)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11320 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11322 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11281) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11320 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11322)], (AntitoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11284 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11281 f s) -> (forall (a : α), AntitoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11284 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11281 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11278) (f x) a) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.mul_const' AntitoneOn.mul_const'ₓ'. -/
@[to_additive add_const]
theorem AntitoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : AntitoneOn f s)
    (a : α) : AntitoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a
#align antitone_on.mul_const' AntitoneOn.mul_const'

/- warning: monotone.mul' -> Monotone.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (Monotone.{u_2, u_1} β α _inst_3 _inst_2 f) -> (Monotone.{u_2, u_1} β α _inst_3 _inst_2 g) -> (Monotone.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11375 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11378 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11381 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11392 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11399 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11401 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11375) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11399 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11401) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11414 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11416 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11378) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11414 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11416)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11426 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11436 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11438 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11375) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11436 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11438)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11451 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11453 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11378) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11451 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11453)], (Monotone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11381 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11378 f) -> (Monotone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11381 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11378 g) -> (Monotone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11381 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11378 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11375) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.mul' Monotone.mul'ₓ'. -/
/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem Monotone.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x * g x := fun x y h => mul_le_mul' (hf h) (hg h)
#align monotone.mul' Monotone.mul'

/- warning: monotone_on.mul' -> MonotoneOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} {s : Set.{u_2} β} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (MonotoneOn.{u_2, u_1} β α _inst_3 _inst_2 f s) -> (MonotoneOn.{u_2, u_1} β α _inst_3 _inst_2 g s) -> (MonotoneOn.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11503 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11506 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11509 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} {s : Set.{u_2} β} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11520 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11527 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11529 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11503) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11527 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11529) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11542 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11544 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11506) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11542 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11544)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11554 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11564 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11566 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11503) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11564 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11566)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11579 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11581 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11506) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11579 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11581)], (MonotoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11509 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11506 f s) -> (MonotoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11509 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11506 g s) -> (MonotoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11509 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11506 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11503) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.mul' MonotoneOn.mul'ₓ'. -/
/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem MonotoneOn.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x * g x) s := fun x hx y hy h => mul_le_mul' (hf hx hy h) (hg hx hy h)
#align monotone_on.mul' MonotoneOn.mul'

/- warning: antitone.mul' -> Antitone.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (Antitone.{u_2, u_1} β α _inst_3 _inst_2 f) -> (Antitone.{u_2, u_1} β α _inst_3 _inst_2 g) -> (Antitone.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11642 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11645 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11648 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11659 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11666 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11668 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11642) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11666 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11668) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11681 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11683 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11645) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11681 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11683)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11693 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11703 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11705 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11642) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11703 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11705)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11718 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11720 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11645) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11718 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11720)], (Antitone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11648 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11645 f) -> (Antitone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11648 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11645 g) -> (Antitone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11648 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11645 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11642) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.mul' Antitone.mul'ₓ'. -/
/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem Antitone.mul' [CovariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x * g x := fun x y h => mul_le_mul' (hf h) (hg h)
#align antitone.mul' Antitone.mul'

/- warning: antitone_on.mul' -> AntitoneOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} {s : Set.{u_2} β} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))], (AntitoneOn.{u_2, u_1} β α _inst_3 _inst_2 f s) -> (AntitoneOn.{u_2, u_1} β α _inst_3 _inst_2 g s) -> (AntitoneOn.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11770 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11773 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11776 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} {s : Set.{u_2} β} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11787 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11794 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11796 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11770) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11794 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11796) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11809 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11811 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11773) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11809 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11811)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11821 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11831 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11833 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11770) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11831 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11833)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11846 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11848 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11773) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11846 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11848)], (AntitoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11776 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11773 f s) -> (AntitoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11776 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11773 g s) -> (AntitoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11776 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11773 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.11770) (f x) (g x)) s)
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
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))], (StrictMono.{u_2, u_1} β α _inst_3 _inst_2 f) -> (StrictMono.{u_2, u_1} β α _inst_3 _inst_2 g) -> (StrictMono.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12758 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12761 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12764 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12775 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12782 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12784 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12758) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12782 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12784) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12797 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12799 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12761) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12797 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12799)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12809 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12819 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12821 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12758) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12819 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12821)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12834 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12836 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12761) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12834 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12836)], (StrictMono.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12764 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12761 f) -> (StrictMono.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12764 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12761 g) -> (StrictMono.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12764 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12761 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12758) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align strict_mono.mul' StrictMono.mul'ₓ'. -/
/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMono.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono fun x => f x * g x := fun a b ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)
#align strict_mono.mul' StrictMono.mul'

/- warning: strict_mono_on.mul' -> StrictMonoOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} {s : Set.{u_2} β} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))], (StrictMonoOn.{u_2, u_1} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u_2, u_1} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12886 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12889 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12892 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} {s : Set.{u_2} β} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12903 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12910 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12912 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12886) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12910 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12912) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12925 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12927 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12889) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12925 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12927)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12937 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12947 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12949 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12886) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12947 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12949)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12962 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12964 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12889) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12962 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12964)], (StrictMonoOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12892 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12889 f s) -> (StrictMonoOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12892 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12889 g s) -> (StrictMonoOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12892 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12889 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.12886) (f x) (g x)) s)
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
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))], (StrictAnti.{u_2, u_1} β α _inst_3 _inst_2 f) -> (StrictAnti.{u_2, u_1} β α _inst_3 _inst_2 g) -> (StrictAnti.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13025 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13028 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13031 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13042 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13049 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13051 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13025) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13049 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13051) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13064 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13066 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13028) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13064 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13066)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13076 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13086 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13088 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13025) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13086 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13088)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13101 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13103 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13028) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13101 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13103)], (StrictAnti.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13031 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13028 f) -> (StrictAnti.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13031 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13028 g) -> (StrictAnti.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13031 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13028 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13025) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align strict_anti.mul' StrictAnti.mul'ₓ'. -/
/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAnti.mul' [CovariantClass α α (· * ·) (· < ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (hf : StrictAnti f) (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x := fun a b ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)
#align strict_anti.mul' StrictAnti.mul'

/- warning: strict_anti_on.mul' -> StrictAntiOn.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} {s : Set.{u_2} β} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))], (StrictAntiOn.{u_2, u_1} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u_2, u_1} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13153 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13156 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13159 : Preorder.{u_2} β] {f : β -> α} {g : β -> α} {s : Set.{u_2} β} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13170 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13177 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13179 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13153) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13177 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13179) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13192 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13194 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13156) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13192 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13194)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13204 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13214 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13216 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13153) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13214 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13216)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13229 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13231 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13156) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13229 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13231)], (StrictAntiOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13159 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13156 f s) -> (StrictAntiOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13159 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13156 g s) -> (StrictAntiOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13159 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13156 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13153) (f x) (g x)) s)
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
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {f : β -> α} {g : β -> α}, (Monotone.{u_2, u_1} β α _inst_3 _inst_2 f) -> (StrictMono.{u_2, u_1} β α _inst_3 _inst_2 g) -> (StrictMono.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13292 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13295 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13298 : Preorder.{u_2} β] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13309 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13316 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13318 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13292) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13316 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13318) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13331 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13333 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13295) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13331 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13333)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13343 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13353 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13355 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13292) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13353 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13355)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13368 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13370 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13295) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13368 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13370)] {f : β -> α} {g : β -> α}, (Monotone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13298 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13295 f) -> (StrictMono.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13298 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13295 g) -> (StrictMono.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13298 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13295 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13292) (f x) (g x)))
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
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {s : Set.{u_2} β} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {f : β -> α} {g : β -> α}, (MonotoneOn.{u_2, u_1} β α _inst_3 _inst_2 f s) -> (StrictMonoOn.{u_2, u_1} β α _inst_3 _inst_2 g s) -> (StrictMonoOn.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13426 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13429 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13432 : Preorder.{u_2} β] {s : Set.{u_2} β} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13443 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13450 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13452 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13426) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13450 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13452) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13465 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13467 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13429) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13465 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13467)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13477 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13487 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13489 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13426) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13487 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13489)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13502 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13504 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13429) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13502 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13504)] {f : β -> α} {g : β -> α}, (MonotoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13432 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13429 f s) -> (StrictMonoOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13432 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13429 g s) -> (StrictMonoOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13432 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13429 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13426) (f x) (g x)) s)
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
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {f : β -> α} {g : β -> α}, (Antitone.{u_2, u_1} β α _inst_3 _inst_2 f) -> (StrictAnti.{u_2, u_1} β α _inst_3 _inst_2 g) -> (StrictAnti.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13571 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13574 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13577 : Preorder.{u_2} β] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13588 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13595 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13597 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13571) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13595 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13597) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13610 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13612 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13574) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13610 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13612)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13622 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13632 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13634 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13571) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13632 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13634)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13647 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13649 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13574) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13647 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13649)] {f : β -> α} {g : β -> α}, (Antitone.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13577 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13574 f) -> (StrictAnti.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13577 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13574 g) -> (StrictAnti.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13577 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13574 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13571) (f x) (g x)))
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
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : Mul.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : Preorder.{u_2} β] {s : Set.{u_2} β} [_inst_4 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2))] [_inst_5 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (ᾰ : α) (ᾰ : α) => α) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1))) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2))] {f : β -> α} {g : β -> α}, (AntitoneOn.{u_2, u_1} β α _inst_3 _inst_2 f s) -> (StrictAntiOn.{u_2, u_1} β α _inst_3 _inst_2 g s) -> (StrictAntiOn.{u_2, u_1} β α _inst_3 _inst_2 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α _inst_1) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u_1}} {β : Type.{u_2}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13705 : Mul.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13708 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13711 : Preorder.{u_2} β] {s : Set.{u_2} β} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13722 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13729 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13731 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13705) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13729 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13731) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13744 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13746 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13708) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13744 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13746)] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13756 : CovariantClass.{u_1, u_1} α α (Function.swap.{succ u_1, succ u_1, succ u_1} α α (fun (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.110 : α) (a._@.Mathlib.Algebra.CovariantAndContravariant._hyg.108 : α) => α) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13766 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13768 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13705) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13766 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13768)) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13781 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13783 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13708) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13781 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13783)] {f : β -> α} {g : β -> α}, (AntitoneOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13711 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13708 f s) -> (StrictAntiOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13711 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13708 g s) -> (StrictAntiOn.{u_2, u_1} β α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13711 inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13708 (fun (x : β) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.13705) (f x) (g x)) s)
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
  forall {α : Type.{u_1}} [_inst_1 : Monoid.{u_1} α] [_inst_2 : LE.{u_1} α], MulLECancellable.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α _inst_1)) _inst_2 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14895 : Monoid.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14898 : LE.{u_1} α], MulLECancellable.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14895)) inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14898 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.14895)))
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
  forall {α : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] {a : α}, (MulLECancellable.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) a) -> (Function.Injective.{succ u_1, succ u_1} α α (fun (_x : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1))) _x a))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15030 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15033 : PartialOrder.{u_1} α] {a : α}, (MulLECancellable.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15030)) (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15033)) a) -> (Function.Injective.{succ u_1, succ u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15043 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15030))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15043 a))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.injective_left MulLECancellable.injective_leftₓ'. -/
@[to_additive]
protected theorem injective_left [CommSemigroup α] [PartialOrder α] {a : α}
    (ha : MulLECancellable a) : Injective (· * a) := fun b c h =>
  ha.Injective <| by rwa [mul_comm a, mul_comm a]
#align mul_le_cancellable.injective_left MulLECancellable.injective_left

/- warning: mul_le_cancellable.inj_left -> MulLECancellable.inj_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] {a : α} {b : α} {c : α}, (MulLECancellable.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) c) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1))) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1))) b c)) (Eq.{succ u_1} α a b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15106 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15109 : PartialOrder.{u_1} α] {a : α} {b : α} {c : α}, (MulLECancellable.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15106)) (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15109)) c) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15106))) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15106))) b c)) (Eq.{succ u_1} α a b))
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
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] [_inst_2 : CommSemigroup.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_2)))) (LE.le.{u_1} α _inst_1)] {a : α} {b : α} {c : α}, (MulLECancellable.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_2)) _inst_1 a) -> (Iff (LE.le.{u_1} α _inst_1 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_2))) b a) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_2))) c a)) (LE.le.{u_1} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15227 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15230 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15233 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15240 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15242 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15230))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15240 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15242) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15255 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15257 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15227 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15255 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15257)] {a : α} {b : α} {c : α}, (MulLECancellable.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15230)) inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15227 a) -> (Iff (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15227 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15230))) b a) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15230))) c a)) (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15227 b c))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.mul_le_mul_iff_right MulLECancellable.mul_le_mul_iff_rightₓ'. -/
@[to_additive]
protected theorem mul_le_mul_iff_right [CommSemigroup α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b c : α} (ha : MulLECancellable a) : b * a ≤ c * a ↔ b ≤ c := by
  rw [mul_comm b, mul_comm c, ha.mul_le_mul_iff_left]
#align mul_le_cancellable.mul_le_mul_iff_right MulLECancellable.mul_le_mul_iff_right

/- warning: mul_le_cancellable.le_mul_iff_one_le_right -> MulLECancellable.le_mul_iff_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] [_inst_2 : MulOneClass.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_2))) (LE.le.{u_1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u_1} α _inst_1 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_2)) a b)) (LE.le.{u_1} α _inst_1 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_2)))) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15326 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15329 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15332 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15339 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15341 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15329)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15339 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15341) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15354 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15356 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15326 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15354 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15356)] {a : α} {b : α}, (MulLECancellable.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15329) inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15326 a) -> (Iff (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15326 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15329)) a b)) (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15326 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15329))) b))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.le_mul_iff_one_le_right MulLECancellable.le_mul_iff_one_le_rightₓ'. -/
@[to_additive]
protected theorem le_mul_iff_one_le_right [MulOneClass α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left
#align mul_le_cancellable.le_mul_iff_one_le_right MulLECancellable.le_mul_iff_one_le_right

/- warning: mul_le_cancellable.mul_le_iff_le_one_right -> MulLECancellable.mul_le_iff_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] [_inst_2 : MulOneClass.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_2))) (LE.le.{u_1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_2) _inst_1 a) -> (Iff (LE.le.{u_1} α _inst_1 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_2)) a b) a) (LE.le.{u_1} α _inst_1 b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_2))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15422 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15425 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15428 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15435 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15437 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15425)) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15435 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15437) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15450 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15452 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15422 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15450 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15452)] {a : α} {b : α}, (MulLECancellable.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15425) inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15422 a) -> (Iff (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15422 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15425)) a b) a) (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15422 b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15425)))))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.mul_le_iff_le_one_right MulLECancellable.mul_le_iff_le_one_rightₓ'. -/
@[to_additive]
protected theorem mul_le_iff_le_one_right [MulOneClass α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left
#align mul_le_cancellable.mul_le_iff_le_one_right MulLECancellable.mul_le_iff_le_one_right

/- warning: mul_le_cancellable.le_mul_iff_one_le_left -> MulLECancellable.le_mul_iff_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] [_inst_2 : CommMonoid.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α _inst_2))))) (LE.le.{u_1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u_1} α _inst_1 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α _inst_2)))) b a)) (LE.le.{u_1} α _inst_1 (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α _inst_2)))))) b))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15518 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15521 : CommMonoid.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15524 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15531 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15533 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15521)))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15531 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15533) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15546 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15548 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15518 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15546 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15548)] {a : α} {b : α}, (MulLECancellable.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15521))) inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15518 a) -> (Iff (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15518 a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15521)))) b a)) (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15518 (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (CommMonoid.toMonoid.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15521)))) b))
Case conversion may be inaccurate. Consider using '#align mul_le_cancellable.le_mul_iff_one_le_left MulLECancellable.le_mul_iff_one_le_leftₓ'. -/
@[to_additive]
protected theorem le_mul_iff_one_le_left [CommMonoid α] [CovariantClass α α (· * ·) (· ≤ ·)]
    {a b : α} (ha : MulLECancellable a) : a ≤ b * a ↔ 1 ≤ b := by
  rw [mul_comm, ha.le_mul_iff_one_le_right]
#align mul_le_cancellable.le_mul_iff_one_le_left MulLECancellable.le_mul_iff_one_le_left

/- warning: mul_le_cancellable.mul_le_iff_le_one_left -> MulLECancellable.mul_le_iff_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : LE.{u_1} α] [_inst_2 : CommMonoid.{u_1} α] [_inst_3 : CovariantClass.{u_1, u_1} α α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α _inst_2))))) (LE.le.{u_1} α _inst_1)] {a : α} {b : α}, (MulLECancellable.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α _inst_2))) _inst_1 a) -> (Iff (LE.le.{u_1} α _inst_1 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α _inst_2)))) b a) a) (LE.le.{u_1} α _inst_1 b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15611 : LE.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15614 : CommMonoid.{u_1} α] [inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15617 : CovariantClass.{u_1, u_1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15624 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15626 : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15614)))) x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15624 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15626) (fun (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15639 : α) (x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15641 : α) => LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15611 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15639 x._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15641)] {a : α} {b : α}, (MulLECancellable.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15614))) inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15611 a) -> (Iff (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15611 (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α (Monoid.toMulOneClass.{u_1} α (CommMonoid.toMonoid.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15614)))) b a) a) (LE.le.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15611 b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (Monoid.toOne.{u_1} α (CommMonoid.toMonoid.{u_1} α inst._@.Mathlib.Algebra.Order.Monoid.Lemmas._hyg.15614))))))
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

