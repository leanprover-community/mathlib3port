/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Algebra.CharZero.Defs
import Mathbin.Algebra.Order.Group
import Mathbin.Algebra.Order.MonoidLemmasZeroLt
import Mathbin.Algebra.Order.Sub
import Mathbin.Algebra.Hom.Ring
import Mathbin.Data.Set.Intervals.Basic

/-!
# Ordered rings and semirings

This file develops the basics of ordered (semi)rings.

Each typeclass here comprises
* an algebraic class (`semiring`, `comm_semiring`, `ring`, `comm_ring`)
* an order class (`partial_order`, `linear_order`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses

* `ordered_semiring`: Semiring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `ordered_comm_semiring`: Commutative semiring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `ordered_ring`: Ring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `ordered_comm_ring`: Commutative ring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `linear_ordered_semiring`: Semiring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `linear_ordered_ring`: Ring with a linear order such that `+` respects `≤` and `*` respects `<`.
* `linear_ordered_comm_ring`: Commutative ring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `canonically_ordered_comm_semiring`: Commutative semiring with a partial order such that `+`
  respects `≤`, `*` respects `<`, and `a ≤ b ↔ ∃ c, b = a + c`.

and some typeclasses to define ordered rings by specifying their nonegative elements:
* `nonneg_ring`: To define `ordered_ring`s.
* `linear_nonneg_ring`: To define `linear_ordered_ring`s.

## Hierarchy

The hardest part of proving order lemmas might be to figure out the correct generality and its
corresponding typeclass. Here's an attempt at demystifying it. For each typeclass, we list its
immediate predecessors and what conditions are added to each of them.

* `ordered_semiring`
  - `ordered_cancel_add_comm_monoid` & multiplication & `*` respects `<`
  - `semiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `ordered_comm_semiring`
  - `ordered_semiring` & commutativity of multiplication
  - `comm_semiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `ordered_ring`
  - `ordered_semiring` & additive inverses
  - `ordered_add_comm_group` & multiplication & `*` respects `<`
  - `ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `ordered_comm_ring`
  - `ordered_ring` & commutativity of multiplication
  - `ordered_comm_semiring` & additive inverses
  - `comm_ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `linear_ordered_semiring`
  - `ordered_semiring` & totality of the order & nontriviality
  - `linear_ordered_add_comm_monoid` & multiplication & nontriviality & `*` respects `<`
* `linear_ordered_ring`
  - `ordered_ring` & totality of the order & nontriviality
  - `linear_ordered_semiring` & additive inverses
  - `linear_ordered_add_comm_group` & multiplication & `*` respects `<`
  - `domain` & linear order structure
* `linear_ordered_comm_ring`
  - `ordered_comm_ring` & totality of the order & nontriviality
  - `linear_ordered_ring` & commutativity of multiplication
  - `is_domain` & linear order structure
* `canonically_ordered_comm_semiring`
  - `canonically_ordered_add_monoid` & multiplication & `*` respects `<` & no zero divisors
  - `comm_semiring` & `a ≤ b ↔ ∃ c, b = a + c` & no zero divisors

## TODO

We're still missing some typeclasses, like
* `linear_ordered_comm_semiring`
* `canonically_ordered_semiring`
They have yet to come up in practice.
-/


universe u

variable {α : Type u}

/-! Note that `order_dual` does not satisfy any of the ordered ring typeclasses due to the
`zero_le_one` field. -/


theorem add_one_le_two_mul [LE α] [Semiringₓ α] [CovariantClass α α (· + ·) (· ≤ ·)] {a : α} (a1 : 1 ≤ a) :
    a + 1 ≤ 2 * a :=
  calc
    a + 1 ≤ a + a := add_le_add_left a1 a
    _ = 2 * a := (two_mul _).symm
    

/-- An `ordered_semiring α` is a semiring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class OrderedSemiring (α : Type u) extends Semiringₓ α, OrderedCancelAddCommMonoid α where
  zero_le_one : (0 : α) ≤ 1
  mul_lt_mul_of_pos_left : ∀ a b c : α, a < b → 0 < c → c * a < c * b
  mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c

section OrderedSemiring

variable [OrderedSemiring α] {a b c d : α}

theorem mul_lt_mul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
  OrderedSemiring.mul_lt_mul_of_pos_left a b c h₁ h₂

theorem mul_lt_mul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
  OrderedSemiring.mul_lt_mul_of_pos_right a b c h₁ h₂

-- see Note [lower instance priority]
instance (priority := 100) OrderedSemiring.zeroLeOneClass : ZeroLeOneClass α :=
  { ‹OrderedSemiring α› with }

-- see Note [lower instance priority]
instance (priority := 200) OrderedSemiring.pos_mul_strict_mono : ZeroLt.PosMulStrictMono α :=
  ⟨fun x a b h => mul_lt_mul_of_pos_left h x.Prop⟩

-- see Note [lower instance priority]
instance (priority := 200) OrderedSemiring.mul_pos_strict_mono : ZeroLt.MulPosStrictMono α :=
  ⟨fun x a b h => mul_lt_mul_of_pos_right h x.Prop⟩

section Nontrivial

variable [Nontrivial α]

@[simp]
theorem zero_lt_one : 0 < (1 : α) :=
  lt_of_le_of_neₓ zero_le_one zero_ne_one

theorem zero_lt_two : 0 < (2 : α) :=
  add_pos zero_lt_one zero_lt_one

@[field_simps]
theorem two_ne_zero : (2 : α) ≠ 0 :=
  zero_lt_two.ne'

theorem one_lt_two : 1 < (2 : α) :=
  calc
    (2 : α) = 1 + 1 := one_add_one_eq_two
    _ > 1 + 0 := add_lt_add_left zero_lt_one _
    _ = 1 := add_zeroₓ 1
    

theorem zero_lt_three : 0 < (3 : α) :=
  add_pos zero_lt_two zero_lt_one

@[field_simps]
theorem three_ne_zero : (3 : α) ≠ 0 :=
  zero_lt_three.ne'

theorem zero_lt_four : 0 < (4 : α) :=
  add_pos zero_lt_two zero_lt_two

@[field_simps]
theorem four_ne_zero : (4 : α) ≠ 0 :=
  zero_lt_four.ne'

alias zero_lt_one ← one_pos

alias zero_lt_two ← two_pos

alias zero_lt_three ← three_pos

alias zero_lt_four ← four_pos

end Nontrivial

-- See Note [decidable namespace]
protected theorem Decidable.mul_le_mul_of_nonneg_left [@DecidableRel α (· ≤ ·)] (h₁ : a ≤ b) (h₂ : 0 ≤ c) :
    c * a ≤ c * b := by
  by_cases' ba : b ≤ a
  · simp [ba.antisymm h₁]
    
  by_cases' c0 : c ≤ 0
  · simp [c0.antisymm h₂]
    
  exact (mul_lt_mul_of_pos_left (h₁.lt_of_not_le ba) (h₂.lt_of_not_le c0)).le

-- See Note [decidable namespace]
protected theorem Decidable.mul_le_mul_of_nonneg_right [@DecidableRel α (· ≤ ·)] (h₁ : a ≤ b) (h₂ : 0 ≤ c) :
    a * c ≤ b * c := by
  by_cases' ba : b ≤ a
  · simp [ba.antisymm h₁]
    
  by_cases' c0 : c ≤ 0
  · simp [c0.antisymm h₂]
    
  exact (mul_lt_mul_of_pos_right (h₁.lt_of_not_le ba) (h₂.lt_of_not_le c0)).le

-- TODO: there are four variations, depending on which variables we assume to be nonneg
-- See Note [decidable namespace]
protected theorem Decidable.mul_le_mul [@DecidableRel α (· ≤ ·)] (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b)
    (nn_c : 0 ≤ c) : a * b ≤ c * d :=
  calc
    a * b ≤ c * b := Decidable.mul_le_mul_of_nonneg_right hac nn_b
    _ ≤ c * d := Decidable.mul_le_mul_of_nonneg_left hbd nn_c
    

-- See Note [decidable namespace]
protected theorem Decidable.mul_nonneg_le_one_le {α : Type _} [OrderedSemiring α] [@DecidableRel α (· ≤ ·)] {a b c : α}
    (h₁ : 0 ≤ c) (h₂ : a ≤ c) (h₃ : 0 ≤ b) (h₄ : b ≤ 1) : a * b ≤ c := by
  simpa only [mul_oneₓ] using Decidable.mul_le_mul h₂ h₄ h₃ h₁

-- See Note [decidable namespace]
protected theorem Decidable.mul_nonneg [@DecidableRel α (· ≤ ·)] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have h : 0 * b ≤ a * b := Decidable.mul_le_mul_of_nonneg_right ha hb
  rwa [zero_mul] at h

@[simp]
theorem pow_nonneg (H : 0 ≤ a) : ∀ n : ℕ, 0 ≤ a ^ n
  | 0 => by
    rw [pow_zeroₓ]
    exact zero_le_one
  | n + 1 => by
    rw [pow_succₓ]
    exact mul_nonneg H (pow_nonneg _)

-- See Note [decidable namespace]
protected theorem Decidable.mul_nonpos_of_nonneg_of_nonpos [@DecidableRel α (· ≤ ·)] (ha : 0 ≤ a) (hb : b ≤ 0) :
    a * b ≤ 0 := by
  have h : a * b ≤ a * 0 := Decidable.mul_le_mul_of_nonneg_left hb ha
  rwa [mul_zero] at h

-- See Note [decidable namespace]
protected theorem Decidable.mul_nonpos_of_nonpos_of_nonneg [@DecidableRel α (· ≤ ·)] (ha : a ≤ 0) (hb : 0 ≤ b) :
    a * b ≤ 0 := by
  have h : a * b ≤ 0 * b := Decidable.mul_le_mul_of_nonneg_right ha hb
  rwa [zero_mul] at h

-- See Note [decidable namespace]
protected theorem Decidable.mul_lt_mul [@DecidableRel α (· ≤ ·)] (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b)
    (nn_c : 0 ≤ c) : a * b < c * d :=
  calc
    a * b < c * b := mul_lt_mul_of_pos_right hac pos_b
    _ ≤ c * d := Decidable.mul_le_mul_of_nonneg_left hbd nn_c
    

theorem mul_lt_mul : a < c → b ≤ d → 0 < b → 0 ≤ c → a * b < c * d := by
  classical <;> exact Decidable.mul_lt_mul

-- See Note [decidable namespace]
protected theorem Decidable.mul_lt_mul' [@DecidableRel α (· ≤ ·)] (h1 : a ≤ c) (h2 : b < d) (h3 : 0 ≤ b) (h4 : 0 < c) :
    a * b < c * d :=
  calc
    a * b ≤ c * b := Decidable.mul_le_mul_of_nonneg_right h1 h3
    _ < c * d := mul_lt_mul_of_pos_left h2 h4
    

theorem mul_lt_mul' : a ≤ c → b < d → 0 ≤ b → 0 < c → a * b < c * d := by
  classical <;> exact Decidable.mul_lt_mul'

@[simp]
theorem pow_pos (H : 0 < a) : ∀ n : ℕ, 0 < a ^ n
  | 0 => by
    nontriviality
    rw [pow_zeroₓ]
    exact zero_lt_one
  | n + 1 => by
    rw [pow_succₓ]
    exact mul_pos H (pow_pos _)

-- See Note [decidable namespace]
protected theorem Decidable.mul_self_lt_mul_self [@DecidableRel α (· ≤ ·)] (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  Decidable.mul_lt_mul' h2.le h2 h1 <| h1.trans_lt h2

theorem mul_self_lt_mul_self (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
  mul_lt_mul' h2.le h2 h1 <| h1.trans_lt h2

-- See Note [decidable namespace]
protected theorem Decidable.strict_mono_on_mul_self [@DecidableRel α (· ≤ ·)] :
    StrictMonoOn (fun x : α => x * x) (Set.Ici 0) := fun x hx y hy hxy => Decidable.mul_self_lt_mul_self hx hxy

theorem strict_mono_on_mul_self : StrictMonoOn (fun x : α => x * x) (Set.Ici 0) := fun x hx y hy hxy =>
  mul_self_lt_mul_self hx hxy

-- See Note [decidable namespace]
protected theorem Decidable.mul_self_le_mul_self [@DecidableRel α (· ≤ ·)] (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
  Decidable.mul_le_mul h2 h2 h1 <| h1.trans h2

theorem mul_self_le_mul_self (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
  mul_le_mul h2 h2 h1 <| h1.trans h2

-- See Note [decidable namespace]
protected theorem Decidable.mul_lt_mul'' [@DecidableRel α (· ≤ ·)] (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) :
    a * b < c * d :=
  h4.lt_or_eq_dec.elim (fun b0 => Decidable.mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 => by
    rw [← b0, mul_zero] <;> exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)

theorem mul_lt_mul'' : a < c → b < d → 0 ≤ a → 0 ≤ b → a * b < c * d := by
  classical <;> exact Decidable.mul_lt_mul''

-- See Note [decidable namespace]
protected theorem Decidable.le_mul_of_one_le_right [@DecidableRel α (· ≤ ·)] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ b * a :=
  suffices b * 1 ≤ b * a by
    rwa [mul_oneₓ] at this
  Decidable.mul_le_mul_of_nonneg_left h hb

-- See Note [decidable namespace]
protected theorem Decidable.le_mul_of_one_le_left [@DecidableRel α (· ≤ ·)] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b :=
  suffices 1 * b ≤ a * b by
    rwa [one_mulₓ] at this
  Decidable.mul_le_mul_of_nonneg_right h hb

-- See Note [decidable namespace]
protected theorem Decidable.lt_mul_of_one_lt_right [@DecidableRel α (· ≤ ·)] (hb : 0 < b) (h : 1 < a) : b < b * a :=
  suffices b * 1 < b * a by
    rwa [mul_oneₓ] at this
  Decidable.mul_lt_mul' le_rflₓ h zero_le_one hb

-- See Note [decidable namespace]
protected theorem Decidable.lt_mul_of_one_lt_left [@DecidableRel α (· ≤ ·)] (hb : 0 < b) (h : 1 < a) : b < a * b :=
  suffices 1 * b < a * b by
    rwa [one_mulₓ] at this
  Decidable.mul_lt_mul h le_rflₓ hb (zero_le_one.trans h.le)

theorem lt_two_mul_self (ha : 0 < a) : a < 2 * a :=
  lt_mul_of_one_lt_left ha (@one_lt_two α _ (nontrivial_of_ne 0 a ha.Ne))

theorem lt_mul_self (hn : 1 < a) : a < a * a :=
  lt_mul_of_one_lt_left (hn.trans_le' zero_le_one) hn

-- See Note [decidable namespace]
protected theorem Decidable.add_le_mul_two_add [@DecidableRel α (· ≤ ·)] {a b : α} (a2 : 2 ≤ a) (b0 : 0 ≤ b) :
    a + (2 + b) ≤ a * (2 + b) :=
  calc
    a + (2 + b) ≤ a + (a + a * b) :=
      add_le_add_left (add_le_add a2 (Decidable.le_mul_of_one_le_left b0 (one_le_two.trans a2))) a
    _ ≤ a * (2 + b) := by
      rw [mul_addₓ, mul_two, add_assocₓ]
    

theorem add_le_mul_two_add {a b : α} : 2 ≤ a → 0 ≤ b → a + (2 + b) ≤ a * (2 + b) := by
  classical <;> exact Decidable.add_le_mul_two_add

-- See Note [decidable namespace]
protected theorem Decidable.one_le_mul_of_one_le_of_one_le [@DecidableRel α (· ≤ ·)] {a b : α} (a1 : 1 ≤ a)
    (b1 : 1 ≤ b) : (1 : α) ≤ a * b :=
  (mul_oneₓ (1 : α)).symm.le.trans (Decidable.mul_le_mul a1 b1 zero_le_one (zero_le_one.trans a1))

theorem one_le_mul_of_one_le_of_one_le {a b : α} : 1 ≤ a → 1 ≤ b → (1 : α) ≤ a * b := by
  classical <;> exact Decidable.one_le_mul_of_one_le_of_one_le

namespace Decidable

variable {β : Type _} [@DecidableRel α (· ≤ ·)] [Preorderₓ β] {f g : β → α}

theorem monotone_mul_left_of_nonneg (ha : 0 ≤ a) : Monotone fun x => a * x := fun b c b_le_c =>
  Decidable.mul_le_mul_of_nonneg_left b_le_c ha

theorem monotone_mul_right_of_nonneg (ha : 0 ≤ a) : Monotone fun x => x * a := fun b c b_le_c =>
  Decidable.mul_le_mul_of_nonneg_right b_le_c ha

theorem monotone_mul {β : Type _} [Preorderₓ β] {f g : β → α} (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 ≤ g x) : Monotone fun x => f x * g x := fun x y h =>
  Decidable.mul_le_mul (hf h) (hg h) (hg0 x) (hf0 y)

theorem strict_mono_mul_monotone (hf : StrictMono f) (hg : Monotone g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 < g x) :
    StrictMono fun x => f x * g x := fun x y h => Decidable.mul_lt_mul (hf h) (hg h.le) (hg0 x) (hf0 y)

theorem monotone_mul_strict_mono (hf : Monotone f) (hg : StrictMono g) (hf0 : ∀ x, 0 < f x) (hg0 : ∀ x, 0 ≤ g x) :
    StrictMono fun x => f x * g x := fun x y h => Decidable.mul_lt_mul' (hf h.le) (hg h) (hg0 x) (hf0 y)

theorem strict_mono_mul (hf : StrictMono f) (hg : StrictMono g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    StrictMono fun x => f x * g x := fun x y h => Decidable.mul_lt_mul'' (hf h) (hg h) (hf0 x) (hg0 x)

end Decidable

section Mono

open Classical

variable {β : Type _} [Preorderₓ β] {f g : β → α}

theorem monotone_mul_left_of_nonneg (ha : 0 ≤ a) : Monotone fun x => a * x :=
  Decidable.monotone_mul_left_of_nonneg ha

theorem monotone_mul_right_of_nonneg (ha : 0 ≤ a) : Monotone fun x => x * a :=
  Decidable.monotone_mul_right_of_nonneg ha

theorem Monotone.mul_const (hf : Monotone f) (ha : 0 ≤ a) : Monotone fun x => f x * a :=
  (monotone_mul_right_of_nonneg ha).comp hf

theorem Monotone.const_mul (hf : Monotone f) (ha : 0 ≤ a) : Monotone fun x => a * f x :=
  (monotone_mul_left_of_nonneg ha).comp hf

theorem Monotone.mul (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    Monotone fun x => f x * g x :=
  Decidable.monotone_mul hf hg hf0 hg0

theorem strict_mono_mul_left_of_pos (ha : 0 < a) : StrictMono fun x => a * x := fun b c b_lt_c =>
  mul_lt_mul_of_pos_left b_lt_c ha

theorem strict_mono_mul_right_of_pos (ha : 0 < a) : StrictMono fun x => x * a := fun b c b_lt_c =>
  mul_lt_mul_of_pos_right b_lt_c ha

theorem StrictMono.mul_const (hf : StrictMono f) (ha : 0 < a) : StrictMono fun x => f x * a :=
  (strict_mono_mul_right_of_pos ha).comp hf

theorem StrictMono.const_mul (hf : StrictMono f) (ha : 0 < a) : StrictMono fun x => a * f x :=
  (strict_mono_mul_left_of_pos ha).comp hf

theorem StrictMono.mul_monotone (hf : StrictMono f) (hg : Monotone g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 < g x) :
    StrictMono fun x => f x * g x :=
  Decidable.strict_mono_mul_monotone hf hg hf0 hg0

theorem Monotone.mul_strict_mono (hf : Monotone f) (hg : StrictMono g) (hf0 : ∀ x, 0 < f x) (hg0 : ∀ x, 0 ≤ g x) :
    StrictMono fun x => f x * g x :=
  Decidable.monotone_mul_strict_mono hf hg hf0 hg0

theorem StrictMono.mul (hf : StrictMono f) (hg : StrictMono g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    StrictMono fun x => f x * g x :=
  Decidable.strict_mono_mul hf hg hf0 hg0

end Mono

/-- Pullback an `ordered_semiring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def Function.Injective.orderedSemiring {β : Type _} [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ] [HasSmul ℕ β]
    [HasNatCast β] (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : OrderedSemiring β :=
  { hf.OrderedCancelAddCommMonoid f zero add nsmul, hf.Semiring f zero one add mul nsmul npow nat_cast with
    zero_le_one :=
      show f 0 ≤ f 1 by
        simp only [zero, one, zero_le_one],
    mul_lt_mul_of_pos_left := fun a b c ab c0 =>
      show f (c * a) < f (c * b) by
        rw [mul, mul]
        refine' mul_lt_mul_of_pos_left ab _
        rwa [← zero],
    mul_lt_mul_of_pos_right := fun a b c ab c0 =>
      show f (a * c) < f (b * c) by
        rw [mul, mul]
        refine' mul_lt_mul_of_pos_right ab _
        rwa [← zero] }

section

variable [Nontrivial α]

theorem bit1_pos (h : 0 ≤ a) : 0 < bit1 a :=
  lt_add_of_le_of_pos (add_nonneg h h) zero_lt_one

theorem lt_add_one (a : α) : a < a + 1 :=
  lt_add_of_le_of_pos le_rflₓ zero_lt_one

theorem lt_one_add (a : α) : a < 1 + a := by
  rw [add_commₓ]
  apply lt_add_one

end

theorem bit1_pos' (h : 0 < a) : 0 < bit1 a := by
  nontriviality
  exact bit1_pos h.le

-- See Note [decidable namespace]
protected theorem Decidable.one_lt_mul [@DecidableRel α (· ≤ ·)] (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b := by
  nontriviality
  exact one_mulₓ (1 : α) ▸ Decidable.mul_lt_mul' ha hb zero_le_one (zero_lt_one.trans_le ha)

theorem one_lt_mul : 1 ≤ a → 1 < b → 1 < a * b := by
  classical <;> exact Decidable.one_lt_mul

-- See Note [decidable namespace]
protected theorem Decidable.mul_le_one [@DecidableRel α (· ≤ ·)] (ha : a ≤ 1) (hb' : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  one_mulₓ (1 : α) ▸ Decidable.mul_le_mul ha hb hb' zero_le_one

theorem mul_le_one : a ≤ 1 → 0 ≤ b → b ≤ 1 → a * b ≤ 1 := by
  classical <;> exact Decidable.mul_le_one

-- See Note [decidable namespace]
protected theorem Decidable.one_lt_mul_of_le_of_lt [@DecidableRel α (· ≤ ·)] (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b := by
  nontriviality
  calc
    1 = 1 * 1 := by
      rw [one_mulₓ]
    _ < a * b := Decidable.mul_lt_mul' ha hb zero_le_one (zero_lt_one.trans_le ha)
    

theorem one_lt_mul_of_le_of_lt : 1 ≤ a → 1 < b → 1 < a * b := by
  classical <;> exact Decidable.one_lt_mul_of_le_of_lt

-- See Note [decidable namespace]
protected theorem Decidable.one_lt_mul_of_lt_of_le [@DecidableRel α (· ≤ ·)] (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b := by
  nontriviality
  calc
    1 = 1 * 1 := by
      rw [one_mulₓ]
    _ < a * b := Decidable.mul_lt_mul ha hb zero_lt_one <| zero_le_one.trans ha.le
    

theorem one_lt_mul_of_lt_of_le : 1 < a → 1 ≤ b → 1 < a * b := by
  classical <;> exact Decidable.one_lt_mul_of_lt_of_le

-- See Note [decidable namespace]
protected theorem Decidable.mul_le_of_le_one_right [@DecidableRel α (· ≤ ·)] (ha : 0 ≤ a) (hb1 : b ≤ 1) : a * b ≤ a :=
  calc
    a * b ≤ a * 1 := Decidable.mul_le_mul_of_nonneg_left hb1 ha
    _ = a := mul_oneₓ a
    

-- See Note [decidable namespace]
protected theorem Decidable.mul_le_of_le_one_left [@DecidableRel α (· ≤ ·)] (hb : 0 ≤ b) (ha1 : a ≤ 1) : a * b ≤ b :=
  calc
    a * b ≤ 1 * b := Decidable.mul_le_mul ha1 le_rflₓ hb zero_le_one
    _ = b := one_mulₓ b
    

-- See Note [decidable namespace]
protected theorem Decidable.mul_lt_one_of_nonneg_of_lt_one_left [@DecidableRel α (· ≤ ·)] (ha0 : 0 ≤ a) (ha : a < 1)
    (hb : b ≤ 1) : a * b < 1 :=
  calc
    a * b ≤ a := Decidable.mul_le_of_le_one_right ha0 hb
    _ < 1 := ha
    

theorem mul_lt_one_of_nonneg_of_lt_one_left : 0 ≤ a → a < 1 → b ≤ 1 → a * b < 1 := by
  classical <;> exact Decidable.mul_lt_one_of_nonneg_of_lt_one_left

-- See Note [decidable namespace]
protected theorem Decidable.mul_lt_one_of_nonneg_of_lt_one_right [@DecidableRel α (· ≤ ·)] (ha : a ≤ 1) (hb0 : 0 ≤ b)
    (hb : b < 1) : a * b < 1 :=
  calc
    a * b ≤ b := Decidable.mul_le_of_le_one_left hb0 ha
    _ < 1 := hb
    

theorem mul_lt_one_of_nonneg_of_lt_one_right : a ≤ 1 → 0 ≤ b → b < 1 → a * b < 1 := by
  classical <;> exact Decidable.mul_lt_one_of_nonneg_of_lt_one_right

theorem Nat.strict_mono_cast [Nontrivial α] : StrictMono (coe : ℕ → α) :=
  strict_mono_nat_of_lt_succ fun n => by
    rw [Nat.cast_succₓ] <;> apply lt_add_one

/-- Note this is not an instance as `char_zero` implies `nontrivial`,
and this would risk forming a loop. -/
theorem OrderedSemiring.to_char_zero [Nontrivial α] : CharZero α :=
  ⟨Nat.strict_mono_cast.Injective⟩

section HasExistsAddOfLe

variable [HasExistsAddOfLe α]

/-- Binary **rearrangement inequality**. -/
theorem mul_add_mul_le_mul_add_mul (hab : a ≤ b) (hcd : c ≤ d) : a * d + b * c ≤ a * c + b * d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd
  rw [mul_addₓ, add_right_commₓ, mul_addₓ, ← add_assocₓ]
  exact add_le_add_left (mul_le_mul_of_nonneg_right hab <| (le_add_iff_nonneg_right _).1 hcd) _

/-- Binary **rearrangement inequality**. -/
theorem mul_add_mul_le_mul_add_mul' (hba : b ≤ a) (hdc : d ≤ c) : a • d + b • c ≤ a • c + b • d := by
  rw [add_commₓ (a • d), add_commₓ (a • c)]
  exact mul_add_mul_le_mul_add_mul hba hdc

/-- Binary strict **rearrangement inequality**. -/
theorem mul_add_mul_lt_mul_add_mul (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab.le
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd.le
  rw [mul_addₓ, add_right_commₓ, mul_addₓ, ← add_assocₓ]
  exact add_lt_add_left (mul_lt_mul_of_pos_right hab <| (lt_add_iff_pos_right _).1 hcd) _

/-- Binary **rearrangement inequality**. -/
theorem mul_add_mul_lt_mul_add_mul' (hba : b < a) (hdc : d < c) : a • d + b • c < a • c + b • d := by
  rw [add_commₓ (a • d), add_commₓ (a • c)]
  exact mul_add_mul_lt_mul_add_mul hba hdc

end HasExistsAddOfLe

end OrderedSemiring

section OrderedCommSemiring

/-- An `ordered_comm_semiring α` is a commutative semiring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class OrderedCommSemiring (α : Type u) extends OrderedSemiring α, CommSemiringₓ α

/-- Pullback an `ordered_comm_semiring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def Function.Injective.orderedCommSemiring [OrderedCommSemiring α] {β : Type _} [AddMonoidWithOneₓ β] [Mul β] [Pow β ℕ]
    (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) : OrderedCommSemiring β :=
  { hf.CommSemiring f zero one add mul nsmul npow nat_cast,
    hf.OrderedSemiring f zero one add mul nsmul npow nat_cast with }

end OrderedCommSemiring

-- It's not entirely clear we should assume `nontrivial` at this point;
-- it would be reasonable to explore changing this,
-- but be warned that the instances involving `domain` may cause
-- typeclass search loops.
/-- A `linear_ordered_semiring α` is a nontrivial semiring `α` with a linear order
such that addition is monotone and multiplication by a positive number is strictly monotone.
-/
@[protect_proj]
class LinearOrderedSemiring (α : Type u) extends OrderedSemiring α, LinearOrderedAddCommMonoid α, Nontrivial α

section LinearOrderedSemiring

variable [LinearOrderedSemiring α] {a b c d : α}

attribute [local instance] LinearOrderedSemiring.decidableLe

-- `norm_num` expects the lemma stating `0 < 1` to have a single typeclass argument
-- (see `norm_num.prove_pos_nat`).
-- Rather than working out how to relax that assumption,
-- we provide a synonym for `zero_lt_one` (which needs both `ordered_semiring α` and `nontrivial α`)
-- with only a `linear_ordered_semiring` typeclass argument.
theorem zero_lt_one' : 0 < (1 : α) :=
  zero_lt_one

theorem le_of_mul_le_mul_left (h : c * a ≤ c * b) (hc : 0 < c) : a ≤ b :=
  (strict_mono_mul_left_of_pos hc).le_iff_le.1 h

theorem le_of_mul_le_mul_right (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
  (strict_mono_mul_right_of_pos hc).le_iff_le.1 h

theorem nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg (hab : 0 ≤ a * b) : 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  refine' Decidable.or_iff_not_and_not.2 _
  simp only [not_and, not_leₓ]
  intro ab nab
  apply not_lt_of_leₓ hab _
  rcases lt_trichotomyₓ 0 a with (ha | rfl | ha)
  exacts[mul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rflₓ).asymm (nab le_rflₓ)).elim,
    mul_neg_of_neg_of_pos ha (nab ha.le)]

theorem nonneg_of_mul_nonneg_left (h : 0 ≤ a * b) (hb : 0 < b) : 0 ≤ a :=
  le_of_not_gtₓ fun ha => (mul_neg_of_neg_of_pos ha hb).not_le h

theorem nonneg_of_mul_nonneg_right (h : 0 ≤ a * b) (ha : 0 < a) : 0 ≤ b :=
  le_of_not_gtₓ fun hb => (mul_neg_of_pos_of_neg ha hb).not_le h

theorem neg_of_mul_neg_left (h : a * b < 0) (hb : 0 ≤ b) : a < 0 :=
  lt_of_not_geₓ fun ha => (Decidable.mul_nonneg ha hb).not_lt h

theorem neg_of_mul_neg_right (h : a * b < 0) (ha : 0 ≤ a) : b < 0 :=
  lt_of_not_geₓ fun hb => (Decidable.mul_nonneg ha hb).not_lt h

theorem nonpos_of_mul_nonpos_left (h : a * b ≤ 0) (hb : 0 < b) : a ≤ 0 :=
  le_of_not_gtₓ fun ha : a > 0 => (mul_pos ha hb).not_le h

theorem nonpos_of_mul_nonpos_right (h : a * b ≤ 0) (ha : 0 < a) : b ≤ 0 :=
  le_of_not_gtₓ fun hb : b > 0 => (mul_pos ha hb).not_le h

@[simp]
theorem zero_le_mul_left (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b := by
  convert mul_le_mul_left h
  simp

@[simp]
theorem zero_le_mul_right (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b := by
  convert mul_le_mul_right h
  simp

theorem add_le_mul_of_left_le_right (a2 : 2 ≤ a) (ab : a ≤ b) : a + b ≤ a * b :=
  have : 0 < b :=
    calc
      0 < 2 := zero_lt_two
      _ ≤ a := a2
      _ ≤ b := ab
      
  calc
    a + b ≤ b + b := add_le_add_right ab b
    _ = 2 * b := (two_mul b).symm
    _ ≤ a * b := (mul_le_mul_right this).mpr a2
    

theorem add_le_mul_of_right_le_left (b2 : 2 ≤ b) (ba : b ≤ a) : a + b ≤ a * b :=
  have : 0 < a :=
    calc
      0 < 2 := zero_lt_two
      _ ≤ b := b2
      _ ≤ a := ba
      
  calc
    a + b ≤ a + a := add_le_add_left ba a
    _ = a * 2 := (mul_two a).symm
    _ ≤ a * b := (mul_le_mul_left this).mpr b2
    

theorem add_le_mul (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b :=
  if hab : a ≤ b then add_le_mul_of_left_le_right a2 hab else add_le_mul_of_right_le_left b2 (le_of_not_leₓ hab)

theorem add_le_mul' (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ b * a :=
  (le_of_eqₓ (add_commₓ _ _)).trans (add_le_mul b2 a2)

section

@[simp]
theorem bit0_le_bit0 : bit0 a ≤ bit0 b ↔ a ≤ b := by
  rw [bit0, bit0, ← two_mul, ← two_mul, mul_le_mul_left (zero_lt_two : 0 < (2 : α))]

@[simp]
theorem bit0_lt_bit0 : bit0 a < bit0 b ↔ a < b := by
  rw [bit0, bit0, ← two_mul, ← two_mul, mul_lt_mul_left (zero_lt_two : 0 < (2 : α))]

@[simp]
theorem bit1_le_bit1 : bit1 a ≤ bit1 b ↔ a ≤ b :=
  (add_le_add_iff_right 1).trans bit0_le_bit0

@[simp]
theorem bit1_lt_bit1 : bit1 a < bit1 b ↔ a < b :=
  (add_lt_add_iff_right 1).trans bit0_lt_bit0

@[simp]
theorem one_le_bit1 : (1 : α) ≤ bit1 a ↔ 0 ≤ a := by
  rw [bit1, le_add_iff_nonneg_left, bit0, ← two_mul, zero_le_mul_left (zero_lt_two : 0 < (2 : α))]

@[simp]
theorem one_lt_bit1 : (1 : α) < bit1 a ↔ 0 < a := by
  rw [bit1, lt_add_iff_pos_left, bit0, ← two_mul, zero_lt_mul_left (zero_lt_two : 0 < (2 : α))]

@[simp]
theorem zero_le_bit0 : (0 : α) ≤ bit0 a ↔ 0 ≤ a := by
  rw [bit0, ← two_mul, zero_le_mul_left (zero_lt_two : 0 < (2 : α))]

@[simp]
theorem zero_lt_bit0 : (0 : α) < bit0 a ↔ 0 < a := by
  rw [bit0, ← two_mul, zero_lt_mul_left (zero_lt_two : 0 < (2 : α))]

end

theorem mul_nonneg_iff_right_nonneg_of_pos (ha : 0 < a) : 0 ≤ a * b ↔ 0 ≤ b :=
  haveI := @LinearOrderₓ.decidableLe α _
  ⟨fun h => nonneg_of_mul_nonneg_right h ha, fun h => Decidable.mul_nonneg ha.le h⟩

theorem mul_nonneg_iff_left_nonneg_of_pos (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a :=
  haveI := @LinearOrderₓ.decidableLe α _
  ⟨fun h => nonneg_of_mul_nonneg_left h hb, fun h => Decidable.mul_nonneg h hb.le⟩

theorem nonpos_of_mul_nonneg_left (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
  le_of_not_gtₓ fun ha => absurd h (mul_neg_of_pos_of_neg ha hb).not_le

theorem nonpos_of_mul_nonneg_right (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
  le_of_not_gtₓ fun hb => absurd h (mul_neg_of_neg_of_pos ha hb).not_le

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedSemiring.to_no_max_order {α : Type _} [LinearOrderedSemiring α] :
    NoMaxOrder α :=
  ⟨fun a => ⟨a + 1, lt_add_of_pos_right _ zero_lt_one⟩⟩

/-- Pullback a `linear_ordered_semiring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def Function.Injective.linearOrderedSemiring {β : Type _} [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ] [HasSmul ℕ β]
    [HasNatCast β] [HasSup β] [HasInf β] (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (hsup : ∀ x y, f (x⊔y) = max (f x) (f y)) (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) :
    LinearOrderedSemiring β :=
  { LinearOrderₓ.lift f hf hsup hinf, pullback_nonzero f zero one,
    hf.OrderedSemiring f zero one add mul nsmul npow nat_cast with }

@[simp]
theorem Units.inv_pos {u : αˣ} : (0 : α) < ↑u⁻¹ ↔ (0 : α) < u :=
  have : ∀ {u : αˣ}, (0 : α) < u → (0 : α) < ↑u⁻¹ := fun u h => (zero_lt_mul_left h).mp <| u.mul_inv.symm ▸ zero_lt_one
  ⟨this, this⟩

@[simp]
theorem Units.inv_neg {u : αˣ} : ↑u⁻¹ < (0 : α) ↔ ↑u < (0 : α) :=
  have : ∀ {u : αˣ}, ↑u < (0 : α) → ↑u⁻¹ < (0 : α) := fun u h =>
    neg_of_mul_pos_right (u.mul_inv.symm ▸ zero_lt_one) h.le
  ⟨this, this⟩

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedSemiring.to_char_zero : CharZero α :=
  OrderedSemiring.to_char_zero

end LinearOrderedSemiring

section Mono

variable [LinearOrderedSemiring α] {a : α}

attribute [local instance] LinearOrderedSemiring.decidableLt

theorem cmp_mul_pos_left (ha : 0 < a) (b c : α) : cmp (a * b) (a * c) = cmp b c :=
  (strict_mono_mul_left_of_pos ha).cmp_map_eq b c

theorem cmp_mul_pos_right (ha : 0 < a) (b c : α) : cmp (b * a) (c * a) = cmp b c :=
  (strict_mono_mul_right_of_pos ha).cmp_map_eq b c

end Mono

section LinearOrderedSemiring

variable [LinearOrderedSemiring α] {a b c : α}

theorem mul_max_of_nonneg (b c : α) (ha : 0 ≤ a) : a * max b c = max (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_max

theorem mul_min_of_nonneg (b c : α) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) :=
  (monotone_mul_left_of_nonneg ha).map_min

theorem max_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_max

theorem min_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) :=
  (monotone_mul_right_of_nonneg hc).map_min

end LinearOrderedSemiring

/-- An `ordered_ring α` is a ring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class OrderedRing (α : Type u) extends Ringₓ α, OrderedAddCommGroup α where
  zero_le_one : 0 ≤ (1 : α)
  mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b

section OrderedRing

variable [OrderedRing α] {a b c : α}

-- See Note [decidable namespace]
protected theorem Decidable.OrderedRing.mul_nonneg [@DecidableRel α (· ≤ ·)] {a b : α} (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) :
    0 ≤ a * b := by
  by_cases' ha : a ≤ 0
  · simp [le_antisymmₓ ha h₁]
    
  by_cases' hb : b ≤ 0
  · simp [le_antisymmₓ hb h₂]
    
  exact (le_not_le_of_ltₓ (OrderedRing.mul_pos a b (h₁.lt_of_not_le ha) (h₂.lt_of_not_le hb))).1

theorem OrderedRing.mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by
  classical <;> exact Decidable.OrderedRing.mul_nonneg

-- See Note [decidable namespace]
protected theorem Decidable.OrderedRing.mul_le_mul_of_nonneg_left [@DecidableRel α (· ≤ ·)] (h₁ : a ≤ b) (h₂ : 0 ≤ c) :
    c * a ≤ c * b := by
  rw [← sub_nonneg, ← mul_sub]
  exact Decidable.OrderedRing.mul_nonneg h₂ (sub_nonneg.2 h₁)

theorem OrderedRing.mul_le_mul_of_nonneg_left : a ≤ b → 0 ≤ c → c * a ≤ c * b := by
  classical <;> exact Decidable.OrderedRing.mul_le_mul_of_nonneg_left

-- See Note [decidable namespace]
protected theorem Decidable.OrderedRing.mul_le_mul_of_nonneg_right [@DecidableRel α (· ≤ ·)] (h₁ : a ≤ b) (h₂ : 0 ≤ c) :
    a * c ≤ b * c := by
  rw [← sub_nonneg, ← sub_mul]
  exact Decidable.OrderedRing.mul_nonneg (sub_nonneg.2 h₁) h₂

theorem OrderedRing.mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c := by
  classical <;> exact Decidable.OrderedRing.mul_le_mul_of_nonneg_right

theorem OrderedRing.mul_lt_mul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b := by
  rw [← sub_pos, ← mul_sub]
  exact OrderedRing.mul_pos _ _ h₂ (sub_pos.2 h₁)

theorem OrderedRing.mul_lt_mul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c := by
  rw [← sub_pos, ← sub_mul]
  exact OrderedRing.mul_pos _ _ (sub_pos.2 h₁) h₂

-- see Note [lower instance priority]
instance (priority := 100) OrderedRing.toOrderedSemiring : OrderedSemiring α :=
  { ‹OrderedRing α› with mul_zero := mul_zero, zero_mul := zero_mul, add_left_cancel := @add_left_cancelₓ α _,
    le_of_add_le_add_left := @le_of_add_le_add_left α _ _ _,
    mul_lt_mul_of_pos_left := @OrderedRing.mul_lt_mul_of_pos_left α _,
    mul_lt_mul_of_pos_right := @OrderedRing.mul_lt_mul_of_pos_right α _ }

-- See Note [decidable namespace]
protected theorem Decidable.mul_le_mul_of_nonpos_left [@DecidableRel α (· ≤ ·)] {a b c : α} (h : b ≤ a) (hc : c ≤ 0) :
    c * a ≤ c * b :=
  have : -c ≥ 0 := neg_nonneg_of_nonpos hc
  have : -c * b ≤ -c * a := Decidable.mul_le_mul_of_nonneg_left h this
  have : -(c * b) ≤ -(c * a) := by
    rwa [neg_mul, neg_mul] at this
  le_of_neg_le_neg this

theorem mul_le_mul_of_nonpos_left {a b c : α} : b ≤ a → c ≤ 0 → c * a ≤ c * b := by
  classical <;> exact Decidable.mul_le_mul_of_nonpos_left

-- See Note [decidable namespace]
protected theorem Decidable.mul_le_mul_of_nonpos_right [@DecidableRel α (· ≤ ·)] {a b c : α} (h : b ≤ a) (hc : c ≤ 0) :
    a * c ≤ b * c :=
  have : -c ≥ 0 := neg_nonneg_of_nonpos hc
  have : b * -c ≤ a * -c := Decidable.mul_le_mul_of_nonneg_right h this
  have : -(b * c) ≤ -(a * c) := by
    rwa [mul_neg, mul_neg] at this
  le_of_neg_le_neg this

theorem mul_le_mul_of_nonpos_right {a b c : α} : b ≤ a → c ≤ 0 → a * c ≤ b * c := by
  classical <;> exact Decidable.mul_le_mul_of_nonpos_right

-- See Note [decidable namespace]
protected theorem Decidable.mul_nonneg_of_nonpos_of_nonpos [@DecidableRel α (· ≤ ·)] {a b : α} (ha : a ≤ 0)
    (hb : b ≤ 0) : 0 ≤ a * b := by
  have : 0 * b ≤ a * b := Decidable.mul_le_mul_of_nonpos_right ha hb
  rwa [zero_mul] at this

theorem mul_nonneg_of_nonpos_of_nonpos {a b : α} : a ≤ 0 → b ≤ 0 → 0 ≤ a * b := by
  classical <;> exact Decidable.mul_nonneg_of_nonpos_of_nonpos

theorem mul_lt_mul_of_neg_left {a b c : α} (h : b < a) (hc : c < 0) : c * a < c * b :=
  have : -c > 0 := neg_pos_of_neg hc
  have : -c * b < -c * a := mul_lt_mul_of_pos_left h this
  have : -(c * b) < -(c * a) := by
    rwa [neg_mul, neg_mul] at this
  lt_of_neg_lt_neg this

theorem mul_lt_mul_of_neg_right {a b c : α} (h : b < a) (hc : c < 0) : a * c < b * c :=
  have : -c > 0 := neg_pos_of_neg hc
  have : b * -c < a * -c := mul_lt_mul_of_pos_right h this
  have : -(b * c) < -(a * c) := by
    rwa [mul_neg, mul_neg] at this
  lt_of_neg_lt_neg this

theorem mul_pos_of_neg_of_neg {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  have : 0 * b < a * b := mul_lt_mul_of_neg_right ha hb
  rwa [zero_mul] at this

theorem Decidable.antitone_mul_left [@DecidableRel α (· ≤ ·)] {a : α} (ha : a ≤ 0) : Antitone ((· * ·) a) :=
  fun b c b_le_c => Decidable.mul_le_mul_of_nonpos_left b_le_c ha

theorem antitone_mul_left {a : α} (ha : a ≤ 0) : Antitone ((· * ·) a) := fun b c b_le_c =>
  mul_le_mul_of_nonpos_left b_le_c ha

theorem Decidable.antitone_mul_right [@DecidableRel α (· ≤ ·)] {a : α} (ha : a ≤ 0) : Antitone fun x => x * a :=
  fun b c b_le_c => Decidable.mul_le_mul_of_nonpos_right b_le_c ha

theorem antitone_mul_right {a : α} (ha : a ≤ 0) : Antitone fun x => x * a := fun b c b_le_c =>
  mul_le_mul_of_nonpos_right b_le_c ha

theorem strict_anti_mul_left {a : α} (ha : a < 0) : StrictAnti ((· * ·) a) := fun b c b_lt_c =>
  mul_lt_mul_of_neg_left b_lt_c ha

theorem strict_anti_mul_right {a : α} (ha : a < 0) : StrictAnti fun x => x * a := fun b c b_lt_c =>
  mul_lt_mul_of_neg_right b_lt_c ha

/-- Pullback an `ordered_ring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def Function.Injective.orderedRing {β : Type _} [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] [Pow β ℕ] [HasNatCast β] [HasIntCast β] (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : OrderedRing β :=
  { hf.OrderedSemiring f zero one add mul nsmul npow nat_cast,
    hf.Ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with
    mul_pos := fun a b a0 b0 =>
      show f 0 < f (a * b) by
        rw [zero, mul]
        apply mul_pos <;> rwa [← zero] }

theorem le_iff_exists_nonneg_add (a b : α) : a ≤ b ↔ ∃ c ≥ 0, b = a + c :=
  ⟨fun h =>
    ⟨b - a, sub_nonneg.mpr h, by
      simp ⟩,
    fun ⟨c, hc, h⟩ => by
    rw [h, le_add_iff_nonneg_right]
    exact hc⟩

end OrderedRing

section OrderedCommRing

/-- An `ordered_comm_ring α` is a commutative ring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class OrderedCommRing (α : Type u) extends OrderedRing α, CommRingₓ α

-- See note [lower instance priority]
instance (priority := 100) OrderedCommRing.toOrderedCommSemiring {α : Type u} [OrderedCommRing α] :
    OrderedCommSemiring α :=
  { (by
      infer_instance : OrderedSemiring α),
    ‹OrderedCommRing α› with }

/-- Pullback an `ordered_comm_ring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def Function.Injective.orderedCommRing [OrderedCommRing α] {β : Type _} [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β]
    [Pow β ℕ] [HasSmul ℕ β] [HasSmul ℤ β] [HasNatCast β] [HasIntCast β] (f : β → α) (hf : Function.Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : OrderedCommRing β :=
  { hf.OrderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast,
    hf.CommRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with }

end OrderedCommRing

/-- A `linear_ordered_ring α` is a ring `α` with a linear order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class LinearOrderedRing (α : Type u) extends OrderedRing α, LinearOrderₓ α, Nontrivial α

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedRing.toLinearOrderedAddCommGroup [s : LinearOrderedRing α] :
    LinearOrderedAddCommGroup α :=
  { s with }

section LinearOrderedSemiring

variable [LinearOrderedSemiring α] {a b c : α}

attribute [local instance] LinearOrderedSemiring.decidableLe

theorem le_of_mul_le_of_one_le {a b c : α} (h : a * c ≤ b) (hb : 0 ≤ b) (hc : 1 ≤ c) : a ≤ b :=
  have h' : a * c ≤ b * c :=
    calc
      a * c ≤ b := h
      _ = b * 1 := by
        rw [mul_oneₓ]
      _ ≤ b * c := Decidable.mul_le_mul_of_nonneg_left hc hb
      
  le_of_mul_le_mul_right h' (zero_lt_one.trans_le hc)

theorem nonneg_le_nonneg_of_sq_le_sq {a b : α} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b :=
  le_of_not_gtₓ fun hab => (Decidable.mul_self_lt_mul_self hb hab).not_le h

theorem mul_self_le_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b :=
  ⟨Decidable.mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩

theorem mul_self_lt_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b :=
  ((@Decidable.strict_mono_on_mul_self α _ _).lt_iff_lt h1 h2).symm

theorem mul_self_inj {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a * a = b * b ↔ a = b :=
  (@Decidable.strict_mono_on_mul_self α _ _).InjOn.eq_iff h1 h2

end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing α] {a b c : α}

attribute [local instance] LinearOrderedRing.decidableLe LinearOrderedRing.decidableLt

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedRing.toLinearOrderedSemiring : LinearOrderedSemiring α :=
  { ‹LinearOrderedRing α› with mul_zero := mul_zero, zero_mul := zero_mul, add_left_cancel := @add_left_cancelₓ α _,
    le_of_add_le_add_left := @le_of_add_le_add_left α _ _ _, mul_lt_mul_of_pos_left := @mul_lt_mul_of_pos_left α _,
    mul_lt_mul_of_pos_right := @mul_lt_mul_of_pos_right α _, le_total := LinearOrderedRing.le_total }

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedRing.is_domain : IsDomain α :=
  { ‹LinearOrderedRing α› with
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      intro a b hab
      refine' Decidable.or_iff_not_and_not.2 fun h => _
      revert hab
      cases' lt_or_gt_of_neₓ h.1 with ha ha <;> cases' lt_or_gt_of_neₓ h.2 with hb hb
      exacts[(mul_pos_of_neg_of_neg ha hb).Ne.symm, (mul_neg_of_neg_of_pos ha hb).Ne, (mul_neg_of_pos_of_neg ha hb).Ne,
        (mul_pos ha hb).Ne.symm] }

@[simp]
theorem abs_one : abs (1 : α) = 1 :=
  abs_of_pos zero_lt_one

@[simp]
theorem abs_two : abs (2 : α) = 2 :=
  abs_of_pos zero_lt_two

theorem abs_mul (a b : α) : abs (a * b) = abs a * abs b := by
  haveI := @LinearOrderₓ.decidableLe α _
  rw [abs_eq (Decidable.mul_nonneg (abs_nonneg a) (abs_nonneg b))]
  cases' le_totalₓ a 0 with ha ha <;>
    cases' le_totalₓ b 0 with hb hb <;>
      simp only [abs_of_nonpos, abs_of_nonneg, true_orₓ, or_trueₓ, eq_self_iff_true, neg_mul, mul_neg, neg_negₓ, *]

/-- `abs` as a `monoid_with_zero_hom`. -/
def absHom : α →*₀ α :=
  ⟨abs, abs_zero, abs_one, abs_mul⟩

@[simp]
theorem abs_mul_abs_self (a : α) : abs a * abs a = a * a :=
  abs_by_cases (fun x => x * x = a * a) rfl (neg_mul_neg a a)

@[simp]
theorem abs_mul_self (a : α) : abs (a * a) = a * a := by
  rw [abs_mul, abs_mul_abs_self]

theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
  ⟨pos_and_pos_or_neg_and_neg_of_mul_pos, fun h => h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩

theorem mul_neg_iff : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← neg_pos, neg_mul_eq_mul_neg, mul_pos_iff, neg_pos, neg_lt_zero]

theorem mul_nonneg_iff : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
  haveI := @LinearOrderₓ.decidableLe α _
  ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg, fun h =>
    h.elim (and_imp.2 Decidable.mul_nonneg) (and_imp.2 Decidable.mul_nonneg_of_nonpos_of_nonpos)⟩

/-- Out of three elements of a `linear_ordered_ring`, two must have the same sign. -/
theorem mul_nonneg_of_three (a b c : α) : 0 ≤ a * b ∨ 0 ≤ b * c ∨ 0 ≤ c * a := by
  iterate 3 
      rw [mul_nonneg_iff] <;>
    have := le_totalₓ 0 a <;> have := le_totalₓ 0 b <;> have := le_totalₓ 0 c <;> itauto

theorem mul_nonpos_iff : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← neg_nonneg, neg_mul_eq_mul_neg, mul_nonneg_iff, neg_nonneg, neg_nonpos]

theorem mul_self_nonneg (a : α) : 0 ≤ a * a :=
  abs_mul_self a ▸ abs_nonneg _

@[simp]
theorem neg_le_self_iff : -a ≤ a ↔ 0 ≤ a := by
  simp [neg_le_iff_add_nonneg, ← two_mul, mul_nonneg_iff, zero_le_one, (@zero_lt_two α _ _).not_le]

@[simp]
theorem neg_lt_self_iff : -a < a ↔ 0 < a := by
  simp [neg_lt_iff_pos_add, ← two_mul, mul_pos_iff, zero_lt_one, (@zero_lt_two α _ _).not_lt]

@[simp]
theorem le_neg_self_iff : a ≤ -a ↔ a ≤ 0 :=
  calc
    a ≤ -a ↔ - -a ≤ -a := by
      rw [neg_negₓ]
    _ ↔ 0 ≤ -a := neg_le_self_iff
    _ ↔ a ≤ 0 := neg_nonneg
    

@[simp]
theorem lt_neg_self_iff : a < -a ↔ a < 0 :=
  calc
    a < -a ↔ - -a < -a := by
      rw [neg_negₓ]
    _ ↔ 0 < -a := neg_lt_self_iff
    _ ↔ a < 0 := neg_pos
    

@[simp]
theorem abs_eq_self : abs a = a ↔ 0 ≤ a := by
  simp [abs_eq_max_neg]

@[simp]
theorem abs_eq_neg_self : abs a = -a ↔ a ≤ 0 := by
  simp [abs_eq_max_neg]

/-- For an element `a` of a linear ordered ring, either `abs a = a` and `0 ≤ a`,
    or `abs a = -a` and `a < 0`.
    Use cases on this lemma to automate linarith in inequalities -/
theorem abs_cases (a : α) : abs a = a ∧ 0 ≤ a ∨ abs a = -a ∧ a < 0 := by
  by_cases' 0 ≤ a
  · left
    exact ⟨abs_eq_self.mpr h, h⟩
    
  · right
    push_neg  at h
    exact ⟨abs_eq_neg_self.mpr (le_of_ltₓ h), h⟩
    

@[simp]
theorem max_zero_add_max_neg_zero_eq_abs_self (a : α) : max a 0 + max (-a) 0 = abs a := by
  symm
  rcases le_totalₓ 0 a with (ha | ha) <;> simp [ha]

theorem gt_of_mul_lt_mul_neg_left (h : c * a < c * b) (hc : c ≤ 0) : b < a :=
  have nhc : 0 ≤ -c := neg_nonneg_of_nonpos hc
  have h2 : -(c * b) < -(c * a) := neg_lt_neg h
  have h3 : -c * b < -c * a :=
    calc
      -c * b = -(c * b) := by
        rw [neg_mul_eq_neg_mulₓ]
      _ < -(c * a) := h2
      _ = -c * a := by
        rw [neg_mul_eq_neg_mulₓ]
      
  lt_of_mul_lt_mul_left h3 nhc

theorem neg_one_lt_zero : -1 < (0 : α) :=
  neg_lt_zero.2 zero_lt_one

@[simp]
theorem mul_le_mul_left_of_neg {a b c : α} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
  (strict_anti_mul_left h).le_iff_le

@[simp]
theorem mul_le_mul_right_of_neg {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
  (strict_anti_mul_right h).le_iff_le

@[simp]
theorem mul_lt_mul_left_of_neg {a b c : α} (h : c < 0) : c * a < c * b ↔ b < a :=
  (strict_anti_mul_left h).lt_iff_lt

@[simp]
theorem mul_lt_mul_right_of_neg {a b c : α} (h : c < 0) : a * c < b * c ↔ b < a :=
  (strict_anti_mul_right h).lt_iff_lt

theorem cmp_mul_neg_left {a : α} (ha : a < 0) (b c : α) : cmp (a * b) (a * c) = cmp c b :=
  (strict_anti_mul_left ha).cmp_map_eq b c

theorem cmp_mul_neg_right {a : α} (ha : a < 0) (b c : α) : cmp (b * a) (c * a) = cmp c b :=
  (strict_anti_mul_right ha).cmp_map_eq b c

theorem sub_one_lt (a : α) : a - 1 < a :=
  sub_lt_iff_lt_add.2 (lt_add_one a)

@[simp]
theorem mul_self_pos {a : α} : 0 < a * a ↔ a ≠ 0 := by
  constructor
  · rintro h rfl
    rw [mul_zero] at h
    exact h.false
    
  · intro h
    cases' h.lt_or_lt with h h
    exacts[mul_pos_of_neg_of_neg h h, mul_pos h h]
    

theorem mul_self_le_mul_self_of_le_of_neg_le {x y : α} (h₁ : x ≤ y) (h₂ : -x ≤ y) : x * x ≤ y * y := by
  haveI := @LinearOrderₓ.decidableLe α _
  rw [← abs_mul_abs_self x]
  exact Decidable.mul_self_le_mul_self (abs_nonneg x) (abs_le.2 ⟨neg_le.2 h₂, h₁⟩)

theorem nonneg_of_mul_nonpos_left {a b : α} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
  le_of_not_gtₓ fun ha => absurd h (mul_pos_of_neg_of_neg ha hb).not_le

theorem nonneg_of_mul_nonpos_right {a b : α} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
  le_of_not_gtₓ fun hb => absurd h (mul_pos_of_neg_of_neg ha hb).not_le

theorem pos_of_mul_neg_left {a b : α} (h : a * b < 0) (hb : b ≤ 0) : 0 < a :=
  haveI := @LinearOrderₓ.decidableLe α _
  lt_of_not_geₓ fun ha => absurd h (Decidable.mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt

theorem pos_of_mul_neg_right {a b : α} (h : a * b < 0) (ha : a ≤ 0) : 0 < b :=
  haveI := @LinearOrderₓ.decidableLe α _
  lt_of_not_geₓ fun hb => absurd h (Decidable.mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt

theorem neg_iff_pos_of_mul_neg (hab : a * b < 0) : a < 0 ↔ 0 < b :=
  ⟨pos_of_mul_neg_right hab ∘ le_of_ltₓ, neg_of_mul_neg_left hab ∘ le_of_ltₓ⟩

theorem pos_iff_neg_of_mul_neg (hab : a * b < 0) : 0 < a ↔ b < 0 :=
  ⟨neg_of_mul_neg_right hab ∘ le_of_ltₓ, pos_of_mul_neg_left hab ∘ le_of_ltₓ⟩

/-- The sum of two squares is zero iff both elements are zero. -/
theorem mul_self_add_mul_self_eq_zero {x y : α} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 := by
  rw [add_eq_zero_iff', mul_self_eq_zero, mul_self_eq_zero] <;> apply mul_self_nonneg

theorem eq_zero_of_mul_self_add_mul_self_eq_zero (h : a * a + b * b = 0) : a = 0 :=
  (mul_self_add_mul_self_eq_zero.mp h).left

theorem abs_eq_iff_mul_self_eq : abs a = abs b ↔ a * a = b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact (mul_self_inj (abs_nonneg a) (abs_nonneg b)).symm

theorem abs_lt_iff_mul_self_lt : abs a < abs b ↔ a * a < b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)

theorem abs_le_iff_mul_self_le : abs a ≤ abs b ↔ a * a ≤ b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)

theorem abs_le_one_iff_mul_self_le_one : abs a ≤ 1 ↔ a * a ≤ 1 := by
  simpa only [abs_one, one_mulₓ] using @abs_le_iff_mul_self_le α _ a 1

/-- Pullback a `linear_ordered_ring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def Function.Injective.linearOrderedRing {β : Type _} [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] [Pow β ℕ] [HasNatCast β] [HasIntCast β] [HasSup β] [HasInf β] (f : β → α) (hf : Function.Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (hsup : ∀ x y, f (x⊔y) = max (f x) (f y))
    (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) : LinearOrderedRing β :=
  { LinearOrderₓ.lift f hf hsup hinf, pullback_nonzero f zero one,
    hf.OrderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with }

end LinearOrderedRing

/-- A `linear_ordered_comm_ring α` is a commutative ring `α` with a linear order
such that addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class LinearOrderedCommRing (α : Type u) extends LinearOrderedRing α, CommMonoidₓ α

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedCommRing.toOrderedCommRing [d : LinearOrderedCommRing α] : OrderedCommRing α :=
  { d with }

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedCommRing.toLinearOrderedSemiring [d : LinearOrderedCommRing α] :
    LinearOrderedSemiring α :=
  { d, LinearOrderedRing.toLinearOrderedSemiring with }

section LinearOrderedCommRing

variable [LinearOrderedCommRing α] {a b c d : α}

theorem max_mul_mul_le_max_mul_max (b c : α) (ha : 0 ≤ a) (hd : 0 ≤ d) : max (a * b) (d * c) ≤ max a c * max d b :=
  haveI := @LinearOrderₓ.decidableLe α _
  have ba : b * a ≤ max d b * max c a :=
    Decidable.mul_le_mul (le_max_rightₓ d b) (le_max_rightₓ c a) ha (le_transₓ hd (le_max_leftₓ d b))
  have cd : c * d ≤ max a c * max b d :=
    Decidable.mul_le_mul (le_max_rightₓ a c) (le_max_rightₓ b d) hd (le_transₓ ha (le_max_leftₓ a c))
  max_leₓ
    (by
      simpa [mul_comm, max_commₓ] using ba)
    (by
      simpa [mul_comm, max_commₓ] using cd)

theorem abs_sub_sq (a b : α) : abs (a - b) * abs (a - b) = a * a + b * b - (1 + 1) * a * b := by
  rw [abs_mul_abs_self]
  simp only [mul_addₓ, add_commₓ, add_left_commₓ, mul_comm, sub_eq_add_neg, mul_oneₓ, mul_neg, neg_add_rev, neg_negₓ]

end LinearOrderedCommRing

section

variable [Ringₓ α] [LinearOrderₓ α] {a b : α}

@[simp]
theorem abs_dvd (a b : α) : abs a ∣ b ↔ a ∣ b := by
  cases' abs_choice a with h h <;> simp only [h, neg_dvd]

theorem abs_dvd_self (a : α) : abs a ∣ a :=
  (abs_dvd a a).mpr (dvd_refl a)

@[simp]
theorem dvd_abs (a b : α) : a ∣ abs b ↔ a ∣ b := by
  cases' abs_choice b with h h <;> simp only [h, dvd_neg]

theorem self_dvd_abs (a : α) : a ∣ abs a :=
  (dvd_abs a a).mpr (dvd_refl a)

theorem abs_dvd_abs (a b : α) : abs a ∣ abs b ↔ a ∣ b :=
  (abs_dvd _ _).trans (dvd_abs _ _)

end

section LinearOrderedCommRing

variable [LinearOrderedCommRing α]

/-- Pullback a `linear_ordered_comm_ring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def Function.Injective.linearOrderedCommRing {β : Type _} [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [Pow β ℕ]
    [HasSmul ℕ β] [HasSmul ℤ β] [HasNatCast β] [HasIntCast β] [HasSup β] [HasInf β] (f : β → α)
    (hf : Function.Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n)
    (hsup : ∀ x y, f (x⊔y) = max (f x) (f y)) (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) : LinearOrderedCommRing β :=
  { LinearOrderₓ.lift f hf hsup hinf, pullback_nonzero f zero one,
    hf.OrderedCommRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with }

end LinearOrderedCommRing

namespace Ringₓ

/-- A positive cone in a ring consists of a positive cone in underlying `add_comm_group`,
which contains `1` and such that the positive elements are closed under multiplication. -/
@[nolint has_nonempty_instance]
structure PositiveCone (α : Type _) [Ringₓ α] extends AddCommGroupₓ.PositiveCone α where
  one_nonneg : nonneg 1
  mul_pos : ∀ a b, Pos a → Pos b → Pos (a * b)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Command.lean:665:43: in add_decl_doc #[[ident positive_cone.to_positive_cone]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- A positive cone in a ring induces a linear order if `1` is a positive element. -/
@[nolint has_nonempty_instance]
structure TotalPositiveCone (α : Type _) [Ringₓ α] extends PositiveCone α, AddCommGroupₓ.TotalPositiveCone α where
  one_pos : Pos 1

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Command.lean:665:43: in add_decl_doc #[[ident total_positive_cone.to_positive_cone]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Command.lean:665:43: in add_decl_doc #[[ident total_positive_cone.to_total_positive_cone]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
end Ringₓ

namespace OrderedRing

open Ringₓ

/-- Construct an `ordered_ring` by
designating a positive cone in an existing `ring`. -/
def mkOfPositiveCone {α : Type _} [Ringₓ α] (C : PositiveCone α) : OrderedRing α :=
  { ‹Ringₓ α›, OrderedAddCommGroup.mkOfPositiveCone C.toPositiveCone with
    zero_le_one := by
      change C.nonneg (1 - 0)
      convert C.one_nonneg
      simp ,
    mul_pos := fun x y xp yp => by
      change C.pos (x * y - 0)
      convert
        C.mul_pos x y
          (by
            convert xp
            simp )
          (by
            convert yp
            simp )
      simp }

end OrderedRing

namespace LinearOrderedRing

open Ringₓ

/-- Construct a `linear_ordered_ring` by
designating a positive cone in an existing `ring`. -/
def mkOfPositiveCone {α : Type _} [Ringₓ α] (C : TotalPositiveCone α) : LinearOrderedRing α :=
  { OrderedRing.mkOfPositiveCone C.toPositiveCone, LinearOrderedAddCommGroup.mkOfPositiveCone C.toTotalPositiveCone with
    exists_pair_ne :=
      ⟨0, 1, by
        intro h
        have one_pos := C.one_pos
        rw [← h, C.pos_iff] at one_pos
        simpa using one_pos⟩ }

end LinearOrderedRing

/-- A canonically ordered commutative semiring is an ordered, commutative semiring
in which `a ≤ b` iff there exists `c` with `b = a + c`. This is satisfied by the
natural numbers, for example, but not the integers or other ordered groups. -/
@[protect_proj]
class CanonicallyOrderedCommSemiring (α : Type _) extends CanonicallyOrderedAddMonoid α, CommSemiringₓ α where
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0

namespace CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring α] {a b : α}

-- see Note [lower instance priority]
instance (priority := 100) to_no_zero_divisors : NoZeroDivisors α :=
  ⟨CanonicallyOrderedCommSemiring.eq_zero_or_eq_zero_of_mul_eq_zero⟩

-- see Note [lower instance priority]
instance (priority := 100) to_covariant_mul_le : CovariantClass α α (· * ·) (· ≤ ·) := by
  refine' ⟨fun a b c h => _⟩
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [mul_addₓ]
  apply self_le_add_right

-- see Note [lower instance priority]
instance (priority := 200) CanonicallyOrderedCommSemiring.pos_mul_mono : ZeroLt.PosMulMono α :=
  ⟨fun x a b h => by
    obtain ⟨d, rfl⟩ := exists_add_of_le h
    simp_rw [left_distrib, le_self_add]⟩

-- see Note [lower instance priority]
instance (priority := 200) CanonicallyOrderedCommSemiring.mul_pos_mono : ZeroLt.MulPosMono α :=
  ⟨fun x a b h => by
    obtain ⟨d, rfl⟩ := exists_add_of_le h
    simp_rw [right_distrib, le_self_add]⟩

/-- A version of `zero_lt_one : 0 < 1` for a `canonically_ordered_comm_semiring`. -/
theorem zero_lt_one [Nontrivial α] : (0 : α) < 1 :=
  (zero_le 1).lt_of_ne zero_ne_one

@[simp]
theorem mul_pos : 0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, Ne.def, mul_eq_zero, not_or_distrib]

end CanonicallyOrderedCommSemiring

section Sub

variable [CanonicallyOrderedCommSemiring α] {a b c : α}

variable [Sub α] [HasOrderedSub α]

variable [IsTotal α (· ≤ ·)]

namespace AddLeCancellable

protected theorem mul_tsub (h : AddLeCancellable (a * c)) : a * (b - c) = a * b - a * c := by
  cases' total_of (· ≤ ·) b c with hbc hcb
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_left' hbc a)]
    
  · apply h.eq_tsub_of_add_eq
    rw [← mul_addₓ, tsub_add_cancel_of_le hcb]
    

protected theorem tsub_mul (h : AddLeCancellable (b * c)) : (a - b) * c = a * c - b * c := by
  simp only [mul_comm _ c] at *
  exact h.mul_tsub

end AddLeCancellable

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem mul_tsub (a b c : α) : a * (b - c) = a * b - a * c :=
  Contravariant.add_le_cancellable.mul_tsub

theorem tsub_mul (a b c : α) : (a - b) * c = a * c - b * c :=
  Contravariant.add_le_cancellable.tsub_mul

end Sub

/-! ### Structures involving `*` and `0` on `with_top` and `with_bot`

The main results of this section are `with_top.canonically_ordered_comm_semiring` and
`with_bot.comm_monoid_with_zero`.
-/


namespace WithTop

instance [Nonempty α] : Nontrivial (WithTop α) :=
  Option.nontrivial

variable [DecidableEq α]

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClassₓ (WithTop α) where
  zero := 0
  mul := fun m n => if m = 0 ∨ n = 0 then 0 else m.bind fun a => n.bind fun b => ↑(a * b)
  zero_mul := fun a => if_pos <| Or.inl rfl
  mul_zero := fun a => if_pos <| Or.inr rfl

theorem mul_def {a b : WithTop α} : a * b = if a = 0 ∨ b = 0 then 0 else a.bind fun a => b.bind fun b => ↑(a * b) :=
  rfl

@[simp]
theorem mul_top {a : WithTop α} (h : a ≠ 0) : a * ⊤ = ⊤ := by
  cases a <;> simp [mul_def, h] <;> rfl

@[simp]
theorem top_mul {a : WithTop α} (h : a ≠ 0) : ⊤ * a = ⊤ := by
  cases a <;> simp [mul_def, h] <;> rfl

@[simp]
theorem top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ :=
  top_mul top_ne_zero

end Mul

section MulZeroClassₓ

variable [MulZeroClassₓ α]

@[norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithTop α) = a * b :=
  (Decidable.byCases fun this : a = 0 => by
      simp [this])
    fun ha =>
    (Decidable.byCases fun this : b = 0 => by
        simp [this])
      fun hb => by
      simp [*, mul_def]
      rfl

theorem mul_coe {b : α} (hb : b ≠ 0) : ∀ {a : WithTop α}, a * b = a.bind fun a : α => ↑(a * b)
  | none =>
    show (if (⊤ : WithTop α) = 0 ∨ (b : WithTop α) = 0 then 0 else ⊤ : WithTop α) = ⊤ by
      simp [hb]
  | some a => show ↑a * ↑b = ↑(a * b) from coe_mul.symm

@[simp]
theorem mul_eq_top_iff {a b : WithTop α} : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := by
  cases a <;> cases b <;> simp only [none_eq_top, some_eq_coe]
  · simp [← coe_mul]
    
  · suffices ⊤ * (b : WithTop α) = ⊤ ↔ b ≠ 0 by
      simpa
    by_cases' hb : b = 0 <;> simp [hb]
    
  · suffices (a : WithTop α) * ⊤ = ⊤ ↔ a ≠ 0 by
      simpa
    by_cases' ha : a = 0 <;> simp [ha]
    
  · simp [← coe_mul]
    

theorem mul_lt_top [Preorderₓ α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b < ⊤ := by
  lift a to α using ha
  lift b to α using hb
  simp only [← coe_mul, coe_lt_top]

@[simp]
theorem untop'_zero_mul (a b : WithTop α) : (a * b).untop' 0 = a.untop' 0 * b.untop' 0 := by
  by_cases' ha : a = 0
  · rw [ha, zero_mul, ← coe_zero, untop'_coe, zero_mul]
    
  by_cases' hb : b = 0
  · rw [hb, mul_zero, ← coe_zero, untop'_coe, mul_zero]
    
  induction a using WithTop.recTopCoe
  · rw [top_mul hb, untop'_top, zero_mul]
    
  induction b using WithTop.recTopCoe
  · rw [mul_top ha, untop'_top, mul_zero]
    
  rw [← coe_mul, untop'_coe, untop'_coe, untop'_coe]

end MulZeroClassₓ

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `= 0 * ⊤ = 0`. -/
instance [MulZeroOneClassₓ α] [Nontrivial α] : MulZeroOneClassₓ (WithTop α) :=
  { WithTop.mulZeroClass with mul := (· * ·), one := 1, zero := 0,
    one_mul := fun a =>
      match a with
      | none =>
        show ((1 : α) : WithTop α) * ⊤ = ⊤ by
          simp [-WithTop.coe_one]
      | some a =>
        show ((1 : α) : WithTop α) * a = a by
          simp [coe_mul.symm, -WithTop.coe_one],
    mul_one := fun a =>
      match a with
      | none =>
        show ⊤ * ((1 : α) : WithTop α) = ⊤ by
          simp [-WithTop.coe_one]
      | some a =>
        show ↑a * ((1 : α) : WithTop α) = a by
          simp [coe_mul.symm, -WithTop.coe_one] }

/-- A version of `with_top.map` for `monoid_with_zero_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def _root_.monoid_with_zero_hom.with_top_map {R S : Type _} [MulZeroOneClassₓ R] [DecidableEq R]
    [Nontrivial R] [MulZeroOneClassₓ S] [DecidableEq S] [Nontrivial S] (f : R →*₀ S) (hf : Function.Injective f) :
    WithTop R →*₀ WithTop S :=
  { f.toZeroHom.with_top_map, f.toMonoidHom.toOneHom.with_top_map with toFun := WithTop.map f,
    map_mul' := fun x y => by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z => (Option.map_injective hf).eq_iff' f.to_zero_hom.with_top_map.map_zero
      rcases eq_or_ne x 0 with (rfl | hx)
      · simp
        
      rcases eq_or_ne y 0 with (rfl | hy)
      · simp
        
      induction x using WithTop.recTopCoe
      · simp [hy, this]
        
      induction y using WithTop.recTopCoe
      · have : (f x : WithTop S) ≠ 0 := by
          simpa [hf.eq_iff' (map_zero f)] using hx
        simp [hx, this]
        
      simp [← coe_mul] }

instance [MulZeroClassₓ α] [NoZeroDivisors α] : NoZeroDivisors (WithTop α) :=
  ⟨fun a b => by
    cases a <;> cases b <;> dsimp' [mul_def] <;> split_ifs <;> simp_all [none_eq_top, some_eq_coe, mul_eq_zero]⟩

instance [SemigroupWithZeroₓ α] [NoZeroDivisors α] : SemigroupWithZeroₓ (WithTop α) :=
  { WithTop.mulZeroClass with mul := (· * ·), zero := 0,
    mul_assoc := fun a b c => by
      cases a
      · by_cases' hb : b = 0 <;> by_cases' hc : c = 0 <;> simp [*, none_eq_top]
        
      cases b
      · by_cases' ha : a = 0 <;> by_cases' hc : c = 0 <;> simp [*, none_eq_top, some_eq_coe]
        
      cases c
      · by_cases' ha : a = 0 <;> by_cases' hb : b = 0 <;> simp [*, none_eq_top, some_eq_coe]
        
      simp [some_eq_coe, coe_mul.symm, mul_assoc] }

instance [MonoidWithZeroₓ α] [NoZeroDivisors α] [Nontrivial α] : MonoidWithZeroₓ (WithTop α) :=
  { WithTop.mulZeroOneClass, WithTop.semigroupWithZero with }

instance [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] : CommMonoidWithZero (WithTop α) :=
  { WithTop.monoidWithZero with mul := (· * ·), zero := 0,
    mul_comm := fun a b => by
      by_cases' ha : a = 0
      · simp [ha]
        
      by_cases' hb : b = 0
      · simp [hb]
        
      simp [ha, hb, mul_def, Option.bind_comm a b, mul_comm] }

variable [CanonicallyOrderedCommSemiring α]

private theorem distrib' (a b c : WithTop α) : (a + b) * c = a * c + b * c := by
  cases c
  · show (a + b) * ⊤ = a * ⊤ + b * ⊤
    by_cases' ha : a = 0 <;> simp [ha]
    
  · show (a + b) * c = a * c + b * c
    by_cases' hc : c = 0
    · simp [hc]
      
    simp [mul_coe hc]
    cases a <;> cases b
    repeat'
      first |
        rfl|
        exact congr_arg some (add_mulₓ _ _ _)
    

/-- This instance requires `canonically_ordered_comm_semiring` as it is the smallest class
that derives from both `non_assoc_non_unital_semiring` and `canonically_ordered_add_monoid`, both
of which are required for distributivity. -/
instance [Nontrivial α] : CommSemiringₓ (WithTop α) :=
  { WithTop.addCommMonoidWithOne, WithTop.commMonoidWithZero with right_distrib := distrib',
    left_distrib := fun a b c => by
      rw [mul_comm, distrib', mul_comm b, mul_comm c]
      rfl }

instance [Nontrivial α] : CanonicallyOrderedCommSemiring (WithTop α) :=
  { WithTop.commSemiring, WithTop.canonicallyOrderedAddMonoid, WithTop.no_zero_divisors with }

/-- A version of `with_top.map` for `ring_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def _root_.ring_hom.with_top_map {R S : Type _} [CanonicallyOrderedCommSemiring R] [DecidableEq R]
    [Nontrivial R] [CanonicallyOrderedCommSemiring S] [DecidableEq S] [Nontrivial S] (f : R →+* S)
    (hf : Function.Injective f) : WithTop R →+* WithTop S :=
  { f.toMonoidWithZeroHom.with_top_map hf, f.toAddMonoidHom.with_top_map with toFun := WithTop.map f }

end WithTop

namespace WithBot

instance [Nonempty α] : Nontrivial (WithBot α) :=
  Option.nontrivial

variable [DecidableEq α]

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClassₓ (WithBot α) :=
  WithTop.mulZeroClass

theorem mul_def {a b : WithBot α} : a * b = if a = 0 ∨ b = 0 then 0 else a.bind fun a => b.bind fun b => ↑(a * b) :=
  rfl

@[simp]
theorem mul_bot {a : WithBot α} (h : a ≠ 0) : a * ⊥ = ⊥ :=
  WithTop.mul_top h

@[simp]
theorem bot_mul {a : WithBot α} (h : a ≠ 0) : ⊥ * a = ⊥ :=
  WithTop.top_mul h

@[simp]
theorem bot_mul_bot : (⊥ * ⊥ : WithBot α) = ⊥ :=
  WithTop.top_mul_top

end Mul

section MulZeroClassₓ

variable [MulZeroClassₓ α]

@[norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithBot α) = a * b :=
  (Decidable.byCases fun this : a = 0 => by
      simp [this])
    fun ha =>
    (Decidable.byCases fun this : b = 0 => by
        simp [this])
      fun hb => by
      simp [*, mul_def]
      rfl

theorem mul_coe {b : α} (hb : b ≠ 0) {a : WithBot α} : a * b = a.bind fun a : α => ↑(a * b) :=
  WithTop.mul_coe hb

@[simp]
theorem mul_eq_bot_iff {a b : WithBot α} : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff

theorem bot_lt_mul [Preorderₓ α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b := by
  lift a to α using ne_bot_of_gt ha
  lift b to α using ne_bot_of_gt hb
  simp only [← coe_mul, bot_lt_coe]

end MulZeroClassₓ

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥ = 0`. -/
instance [MulZeroOneClassₓ α] [Nontrivial α] : MulZeroOneClassₓ (WithBot α) :=
  WithTop.mulZeroOneClass

instance [MulZeroClassₓ α] [NoZeroDivisors α] : NoZeroDivisors (WithBot α) :=
  WithTop.no_zero_divisors

instance [SemigroupWithZeroₓ α] [NoZeroDivisors α] : SemigroupWithZeroₓ (WithBot α) :=
  WithTop.semigroupWithZero

instance [MonoidWithZeroₓ α] [NoZeroDivisors α] [Nontrivial α] : MonoidWithZeroₓ (WithBot α) :=
  WithTop.monoidWithZero

instance [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] : CommMonoidWithZero (WithBot α) :=
  WithTop.commMonoidWithZero

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : CommSemiringₓ (WithBot α) :=
  WithTop.commSemiring

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : ZeroLt.PosMulMono (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h
    simp only [Subtype.coe_mk]
    induction x using WithBot.recBotCoe
    · have := bot_lt_coe (0 : α)
      rw [coe_zero] at this
      exact absurd x0.le this.not_le
      
    · induction a using WithBot.recBotCoe
      · simp_rw [mul_bot x0.ne.symm, bot_le]
        
      induction b using WithBot.recBotCoe
      · exact absurd h (bot_lt_coe a).not_le
        
      · simp only [← coe_mul, coe_le_coe] at *
        exact mul_le_mul_left' h x
        
      ⟩

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : ZeroLt.MulPosMono (WithBot α) :=
  ZeroLt.pos_mul_mono_iff_mul_pos_mono.mp ZeroLt.pos_mul_mono

end WithBot

