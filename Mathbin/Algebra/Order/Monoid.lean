/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Group.WithOne
import Mathbin.Algebra.Group.TypeTags
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Order.MonoidLemmas
import Mathbin.Data.Equiv.MulAdd
import Mathbin.Order.BoundedOrder
import Mathbin.Order.MinMax
import Mathbin.Order.Hom.Basic

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/


open Function

universe u

variable {α : Type u}

/-- An ordered commutative monoid is a commutative monoid
with a partial order such that `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
-/
@[protect_proj, ancestor CommMonoidₓ PartialOrderₓ]
class OrderedCommMonoid (α : Type _) extends CommMonoidₓ α, PartialOrderₓ α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone)
-/
@[protect_proj, ancestor AddCommMonoidₓ PartialOrderₓ]
class OrderedAddCommMonoid (α : Type _) extends AddCommMonoidₓ α, PartialOrderₓ α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

attribute [to_additive] OrderedCommMonoid

section OrderedInstances

@[to_additive]
instance OrderedCommMonoid.to_covariant_class_left (M : Type _) [OrderedCommMonoid M] :
    CovariantClass M M (· * ·) (· ≤ ·) where
  elim := fun a b c bc => OrderedCommMonoid.mul_le_mul_left _ _ bc a

/- This instance can be proven with `by apply_instance`.  However, `with_bot ℕ` does not
pick up a `covariant_class M M (function.swap (*)) (≤)` instance without it (see PR #7940). -/
@[to_additive]
instance OrderedCommMonoid.to_covariant_class_right (M : Type _) [OrderedCommMonoid M] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  covariant_swap_mul_le_of_covariant_mul_le M

/- This is not an instance, to avoid creating a loop in the type-class system: in a
`left_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (*) (≤)`
implies `covariant_class M M (*) (<)` . -/
@[to_additive]
theorem Mul.to_covariant_class_left (M : Type _) [Mul M] [LinearOrderₓ M] [CovariantClass M M (· * ·) (· < ·)] :
    CovariantClass M M (· * ·) (· ≤ ·) :=
  { elim := fun a b c bc => by
      rcases eq_or_lt_of_le bc with (rfl | bc)
      · exact rfl.le
        
      · exact (mul_lt_mul_left' bc a).le
         }

/- This is not an instance, to avoid creating a loop in the type-class system: in a
`right_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (swap (*)) (<)`
implies `covariant_class M M (swap (*)) (≤)` . -/
@[to_additive]
theorem Mul.to_covariant_class_right (M : Type _) [Mul M] [LinearOrderₓ M] [CovariantClass M M (swap (· * ·)) (· < ·)] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  { elim := fun a b c bc => by
      rcases eq_or_lt_of_le bc with (rfl | bc)
      · exact rfl.le
        
      · exact (mul_lt_mul_right' bc a).le
         }

end OrderedInstances

/-- An `ordered_comm_monoid` with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_monoid`. -/
class HasExistsMulOfLe (α : Type u) [OrderedCommMonoid α] : Prop where
  exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a * c

/-- An `ordered_add_comm_monoid` with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_add_monoid`. -/
class HasExistsAddOfLe (α : Type u) [OrderedAddCommMonoid α] : Prop where
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a + c

attribute [to_additive] HasExistsMulOfLe

export HasExistsMulOfLe (exists_mul_of_le)

export HasExistsAddOfLe (exists_add_of_le)

/-- A linearly ordered additive commutative monoid. -/
@[protect_proj, ancestor LinearOrderₓ OrderedAddCommMonoid]
class LinearOrderedAddCommMonoid (α : Type _) extends LinearOrderₓ α, OrderedAddCommMonoid α

/-- A linearly ordered commutative monoid. -/
@[protect_proj, ancestor LinearOrderₓ OrderedCommMonoid, to_additive]
class LinearOrderedCommMonoid (α : Type _) extends LinearOrderₓ α, OrderedCommMonoid α

/-- A linearly ordered commutative monoid with a zero element. -/
class LinearOrderedCommMonoidWithZero (α : Type _) extends LinearOrderedCommMonoid α, CommMonoidWithZero α where
  zero_le_one : (0 : α) ≤ 1

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj, ancestor LinearOrderedAddCommMonoid HasTop]
class LinearOrderedAddCommMonoidWithTop (α : Type _) extends LinearOrderedAddCommMonoid α, HasTop α where
  le_top : ∀ x : α, x ≤ ⊤
  top_add' : ∀ x : α, ⊤ + x = ⊤

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedAddCommMonoidWithTop.toOrderTop (α : Type u)
    [h : LinearOrderedAddCommMonoidWithTop α] : OrderTop α :=
  { h with }

section LinearOrderedAddCommMonoidWithTop

variable [LinearOrderedAddCommMonoidWithTop α] {a b : α}

@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  trans (add_commₓ _ _) (top_add _)

end LinearOrderedAddCommMonoidWithTop

/-- Pullback an `ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.orderedAddCommMonoid "Pullback an `ordered_add_comm_monoid` under an injective map."]
def Function.Injective.orderedCommMonoid [OrderedCommMonoid α] {β : Type _} [One β] [Mul β] (f : β → α)
    (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : OrderedCommMonoid β :=
  { PartialOrderₓ.lift f hf, hf.CommMonoid f one mul with
    mul_le_mul_left := fun a b ab c =>
      show f (c * a) ≤ f (c * b) by
        rw [mul, mul]
        apply mul_le_mul_left'
        exact ab }

/-- Pullback a `linear_ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedAddCommMonoid
      "Pullback an `ordered_add_comm_monoid` under an injective map."]
def Function.Injective.linearOrderedCommMonoid [LinearOrderedCommMonoid α] {β : Type _} [One β] [Mul β] (f : β → α)
    (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : LinearOrderedCommMonoid β :=
  { hf.OrderedCommMonoid f one mul, LinearOrderₓ.lift f hf with }

theorem bit0_pos [OrderedAddCommMonoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
  add_pos h h

namespace Units

@[to_additive]
instance [Monoidₓ α] [Preorderₓ α] : Preorderₓ αˣ :=
  Preorderₓ.lift (coe : αˣ → α)

@[simp, norm_cast, to_additive]
theorem coe_le_coe [Monoidₓ α] [Preorderₓ α] {a b : αˣ} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl

@[simp, norm_cast, to_additive]
theorem coe_lt_coe [Monoidₓ α] [Preorderₓ α] {a b : αˣ} : (a : α) < b ↔ a < b :=
  Iff.rfl

@[to_additive]
instance [Monoidₓ α] [PartialOrderₓ α] : PartialOrderₓ αˣ :=
  PartialOrderₓ.lift coe Units.ext

@[to_additive]
instance [Monoidₓ α] [LinearOrderₓ α] : LinearOrderₓ αˣ :=
  LinearOrderₓ.lift coe Units.ext

@[simp, norm_cast, to_additive]
theorem max_coe [Monoidₓ α] [LinearOrderₓ α] {a b : αˣ} : (↑(max a b) : α) = max a b := by
  by_cases' b ≤ a <;> simp [max_def, h]

@[simp, norm_cast, to_additive]
theorem min_coe [Monoidₓ α] [LinearOrderₓ α] {a b : αˣ} : (↑(min a b) : α) = min a b := by
  by_cases' a ≤ b <;> simp [min_def, h]

end Units

namespace WithZero

attribute [local semireducible] WithZero

instance [Preorderₓ α] : Preorderₓ (WithZero α) :=
  WithBot.preorder

instance [PartialOrderₓ α] : PartialOrderₓ (WithZero α) :=
  WithBot.partialOrder

instance [PartialOrderₓ α] : OrderBot (WithZero α) :=
  WithBot.orderBot

theorem zero_le [PartialOrderₓ α] (a : WithZero α) : 0 ≤ a :=
  OrderBot.bot_le a

theorem zero_lt_coe [Preorderₓ α] (a : α) : (0 : WithZero α) < a :=
  WithBot.bot_lt_coe a

@[simp, norm_cast]
theorem coe_lt_coe [PartialOrderₓ α] {a b : α} : (a : WithZero α) < b ↔ a < b :=
  WithBot.coe_lt_coe

@[simp, norm_cast]
theorem coe_le_coe [PartialOrderₓ α] {a b : α} : (a : WithZero α) ≤ b ↔ a ≤ b :=
  WithBot.coe_le_coe

instance [Lattice α] : Lattice (WithZero α) :=
  WithBot.lattice

instance [LinearOrderₓ α] : LinearOrderₓ (WithZero α) :=
  WithBot.linearOrder

theorem mul_le_mul_left {α : Type u} [Mul α] [Preorderₓ α] [CovariantClass α α (· * ·) (· ≤ ·)] :
    ∀ a b : WithZero α, a ≤ b → ∀ c : WithZero α, c * a ≤ c * b := by
  rintro (_ | a) (_ | b) h (_ | c) <;>
    try
      exact fun f hf => Option.noConfusion hf
  · exact False.elim (not_lt_of_le h (WithZero.zero_lt_coe a))
    
  · simp_rw [some_eq_coe]  at h⊢
    norm_cast  at h⊢
    exact CovariantClass.elim _ h
    

theorem lt_of_mul_lt_mul_left {α : Type u} [Mul α] [PartialOrderₓ α] [ContravariantClass α α (· * ·) (· < ·)] :
    ∀ a b c : WithZero α, a * b < a * c → b < c := by
  rintro (_ | a) (_ | b) (_ | c) h <;>
    try
      exact False.elim (lt_irreflₓ none h)
  · exact WithZero.zero_lt_coe c
    
  · exact False.elim (not_le_of_lt h (WithZero.zero_le _))
    
  · simp_rw [some_eq_coe]  at h⊢
    norm_cast  at h⊢
    apply lt_of_mul_lt_mul_left' h
    

instance [OrderedCommMonoid α] : OrderedCommMonoid (WithZero α) :=
  { WithZero.commMonoidWithZero, WithZero.partialOrder with mul_le_mul_left := WithZero.mul_le_mul_left }

/-- If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
-/
/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/
protected def orderedAddCommMonoid [OrderedAddCommMonoid α] (zero_le : ∀ a : α, 0 ≤ a) :
    OrderedAddCommMonoid (WithZero α) := by
  suffices
  refine' { WithZero.partialOrder, WithZero.addCommMonoid with add_le_add_left := this, .. }
  · intro a b h c ca h₂
    cases' b with b
    · rw [le_antisymmₓ h bot_le] at h₂
      exact ⟨_, h₂, le_rfl⟩
      
    cases' a with a
    · change c + 0 = some ca at h₂
      simp at h₂
      simp [h₂]
      exact
        ⟨_, rfl, by
          simpa using add_le_add_left (zero_le b) _⟩
      
    · simp at h
      cases' c with c <;> change some _ = _ at h₂ <;> simp [-add_commₓ] at h₂ <;> subst ca <;> refine' ⟨_, rfl, _⟩
      · exact h
        
      · exact add_le_add_left h _
        
      
    

end WithZero

namespace WithTop

section One

variable [One α]

@[to_additive]
instance : One (WithTop α) :=
  ⟨(1 : α)⟩

@[simp, norm_cast, to_additive]
theorem coe_one : ((1 : α) : WithTop α) = 1 :=
  rfl

@[simp, norm_cast, to_additive]
theorem coe_eq_one {a : α} : (a : WithTop α) = 1 ↔ a = 1 :=
  coe_eq_coe

@[simp, norm_cast, to_additive]
theorem one_eq_coe {a : α} : 1 = (a : WithTop α) ↔ a = 1 :=
  trans eq_comm coe_eq_one

@[simp, to_additive]
theorem top_ne_one : ⊤ ≠ (1 : WithTop α) :=
  fun.

@[simp, to_additive]
theorem one_ne_top : (1 : WithTop α) ≠ ⊤ :=
  fun.

end One

instance [Add α] : Add (WithTop α) :=
  ⟨fun o₁ o₂ => o₁.bind fun a => o₂.map fun b => a + b⟩

@[norm_cast]
theorem coe_add [Add α] {a b : α} : ((a + b : α) : WithTop α) = a + b :=
  rfl

@[norm_cast]
theorem coe_bit0 [Add α] {a : α} : ((bit0 a : α) : WithTop α) = bit0 a :=
  rfl

@[norm_cast]
theorem coe_bit1 [Add α] [One α] {a : α} : ((bit1 a : α) : WithTop α) = bit1 a :=
  rfl

@[simp]
theorem add_top [Add α] : ∀ {a : WithTop α}, a + ⊤ = ⊤
  | none => rfl
  | some a => rfl

@[simp]
theorem top_add [Add α] {a : WithTop α} : ⊤ + a = ⊤ :=
  rfl

theorem add_eq_top [Add α] {a b : WithTop α} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  cases a <;> cases b <;> simp [none_eq_top, some_eq_coe, ← WithTop.coe_add, ← WithZero.coe_add]

theorem add_lt_top [Add α] [PartialOrderₓ α] {a b : WithTop α} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by
  simp [lt_top_iff_ne_top, add_eq_top, not_or_distrib]

theorem add_eq_coe [Add α] : ∀ {a b : WithTop α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | none, b, c => by
    simp [none_eq_top]
  | some a, none, c => by
    simp [none_eq_top]
  | some a, some b, c => by
    simp only [some_eq_coe, ← coe_add, coe_eq_coe, exists_and_distrib_left, exists_eq_left]

@[simp]
theorem add_coe_eq_top_iff [Add α] {x : WithTop α} {y : α} : x + y = ⊤ ↔ x = ⊤ := by
  induction x using WithTop.recTopCoe <;> simp [← coe_add, -WithZero.coe_add]

@[simp]
theorem coe_add_eq_top_iff [Add α] {x : α} {y : WithTop α} : ↑x + y = ⊤ ↔ y = ⊤ := by
  induction y using WithTop.recTopCoe <;> simp [← coe_add, -WithZero.coe_add]

instance [AddSemigroupₓ α] : AddSemigroupₓ (WithTop α) :=
  { WithTop.hasAdd with
    add_assoc := by
      repeat'
          refine' WithTop.recTopCoe _ _ <;>
            try
              intro <;>
        simp [← WithTop.coe_add, add_assocₓ] }

instance [AddCommSemigroupₓ α] : AddCommSemigroupₓ (WithTop α) :=
  { WithTop.addSemigroup with
    add_comm := by
      repeat'
          refine' WithTop.recTopCoe _ _ <;>
            try
              intro <;>
        simp [← WithTop.coe_add, add_commₓ] }

instance [AddZeroClass α] : AddZeroClass (WithTop α) :=
  { WithTop.hasZero, WithTop.hasAdd with
    zero_add := by
      refine' WithTop.recTopCoe _ _
      · simp
        
      · intro
        rw [← WithTop.coe_zero, ← WithTop.coe_add, zero_addₓ]
        ,
    add_zero := by
      refine' WithTop.recTopCoe _ _
      · simp
        
      · intro
        rw [← WithTop.coe_zero, ← WithTop.coe_add, add_zeroₓ]
         }

instance [AddMonoidₓ α] : AddMonoidₓ (WithTop α) :=
  { WithTop.addZeroClass, WithTop.hasZero, WithTop.addSemigroup with }

instance [AddCommMonoidₓ α] : AddCommMonoidₓ (WithTop α) :=
  { WithTop.addMonoid, WithTop.addCommSemigroup with }

instance [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithTop α) :=
  { WithTop.partialOrder, WithTop.addCommMonoid with
    add_le_add_left := by
      rintro a b h (_ | c)
      · simp [none_eq_top]
        
      rcases b with (_ | b)
      · simp [none_eq_top]
        
      rcases le_coe_iff.1 h with ⟨a, rfl, h⟩
      simp only [some_eq_coe, ← coe_add, coe_le_coe] at h⊢
      exact add_le_add_left h c }

instance [LinearOrderedAddCommMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) :=
  { WithTop.orderTop, WithTop.linearOrder, WithTop.orderedAddCommMonoid, Option.nontrivial with
    top_add' := fun x => WithTop.top_add }

/-- Coercion from `α` to `with_top α` as an `add_monoid_hom`. -/
def coeAddHom [AddMonoidₓ α] : α →+ WithTop α :=
  ⟨coe, rfl, fun _ _ => rfl⟩

@[simp]
theorem coe_coe_add_hom [AddMonoidₓ α] : ⇑(coeAddHom : α →+ WithTop α) = coe :=
  rfl

@[simp]
theorem zero_lt_top [OrderedAddCommMonoid α] : (0 : WithTop α) < ⊤ :=
  coe_lt_top 0

@[simp, norm_cast]
theorem zero_lt_coe [OrderedAddCommMonoid α] (a : α) : (0 : WithTop α) < a ↔ 0 < a :=
  coe_lt_coe

end WithTop

namespace WithBot

instance [Zero α] : Zero (WithBot α) :=
  WithTop.hasZero

instance [One α] : One (WithBot α) :=
  WithTop.hasOne

instance [Add α] : Add (WithBot α) :=
  WithTop.hasAdd

instance [AddSemigroupₓ α] : AddSemigroupₓ (WithBot α) :=
  WithTop.addSemigroup

instance [AddCommSemigroupₓ α] : AddCommSemigroupₓ (WithBot α) :=
  WithTop.addCommSemigroup

instance [AddZeroClass α] : AddZeroClass (WithBot α) :=
  WithTop.addZeroClass

instance [AddMonoidₓ α] : AddMonoidₓ (WithBot α) :=
  WithTop.addMonoid

instance [AddCommMonoidₓ α] : AddCommMonoidₓ (WithBot α) :=
  WithTop.addCommMonoid

instance [OrderedAddCommMonoid α] : OrderedAddCommMonoid (WithBot α) := by
  suffices
  refine' { WithBot.partialOrder, WithBot.addCommMonoid with add_le_add_left := this, .. }
  · intro a b h c ca h₂
    cases' c with c
    · cases h₂
      
    cases' a with a <;> cases h₂
    cases' b with b
    · cases le_antisymmₓ h bot_le
      
    simp at h
    exact ⟨_, rfl, add_le_add_left h _⟩
    

instance [LinearOrderedAddCommMonoid α] : LinearOrderedAddCommMonoid (WithBot α) :=
  { WithBot.linearOrder, WithBot.orderedAddCommMonoid with }

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
theorem coe_zero [Zero α] : ((0 : α) : WithBot α) = 0 :=
  rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
theorem coe_one [One α] : ((1 : α) : WithBot α) = 1 :=
  rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
theorem coe_eq_zero {α : Type _} [AddMonoidₓ α] {a : α} : (a : WithBot α) = 0 ↔ a = 0 := by
  norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
theorem coe_add [AddSemigroupₓ α] (a b : α) : ((a + b : α) : WithBot α) = a + b := by
  norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
theorem coe_bit0 [AddSemigroupₓ α] {a : α} : ((bit0 a : α) : WithBot α) = bit0 a := by
  norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
theorem coe_bit1 [AddSemigroupₓ α] [One α] {a : α} : ((bit1 a : α) : WithBot α) = bit1 a := by
  norm_cast

@[simp]
theorem bot_add [AddSemigroupₓ α] (a : WithBot α) : ⊥ + a = ⊥ :=
  rfl

@[simp]
theorem add_bot [AddSemigroupₓ α] (a : WithBot α) : a + ⊥ = ⊥ := by
  cases a <;> rfl

@[simp]
theorem add_eq_bot [AddSemigroupₓ α] {m n : WithBot α} : m + n = ⊥ ↔ m = ⊥ ∨ n = ⊥ :=
  WithTop.add_eq_top

end WithBot

namespace WithZero

attribute [local semireducible] WithZero

variable [Add α]

/-- Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative. -/
def toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α) :=
  MulEquiv.refl _

@[simp]
theorem to_mul_bot_zero : toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥ :=
  rfl

@[simp]
theorem to_mul_bot_coe (x : Multiplicative α) : toMulBot ↑x = Multiplicative.ofAdd (x.toAdd : WithBot α) :=
  rfl

@[simp]
theorem to_mul_bot_symm_bot : toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0 :=
  rfl

@[simp]
theorem to_mul_bot_coe_of_add (x : α) : toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x :=
  rfl

end WithZero

/-- A canonically ordered additive monoid is an ordered commutative additive monoid
  in which the ordering coincides with the subtractibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other nontrivial `ordered_add_comm_group`s. -/
@[protect_proj, ancestor OrderedAddCommMonoid HasBot]
class CanonicallyOrderedAddMonoid (α : Type _) extends OrderedAddCommMonoid α, HasBot α where
  bot_le : ∀ x : α, ⊥ ≤ x
  le_iff_exists_add : ∀ a b : α, a ≤ b ↔ ∃ c, b = a + c

-- see Note [lower instance priority]
instance (priority := 100) CanonicallyOrderedAddMonoid.toOrderBot (α : Type u) [h : CanonicallyOrderedAddMonoid α] :
    OrderBot α :=
  { h with }

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Examples seem rare; it seems more likely that the `order_dual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1).
-/
@[protect_proj, ancestor OrderedCommMonoid HasBot, to_additive]
class CanonicallyOrderedMonoid (α : Type _) extends OrderedCommMonoid α, HasBot α where
  bot_le : ∀ x : α, ⊥ ≤ x
  le_iff_exists_mul : ∀ a b : α, a ≤ b ↔ ∃ c, b = a * c

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CanonicallyOrderedMonoid.toOrderBot (α : Type u) [h : CanonicallyOrderedMonoid α] :
    OrderBot α :=
  { h with }

section CanonicallyOrderedMonoid

variable [CanonicallyOrderedMonoid α] {a b c d : α}

@[to_additive]
theorem le_iff_exists_mul : a ≤ b ↔ ∃ c, b = a * c :=
  CanonicallyOrderedMonoid.le_iff_exists_mul a b

@[to_additive]
theorem self_le_mul_right (a b : α) : a ≤ a * b :=
  le_iff_exists_mul.mpr ⟨b, rfl⟩

@[to_additive]
theorem self_le_mul_left (a b : α) : a ≤ b * a := by
  rw [mul_comm]
  exact self_le_mul_right a b

@[simp, to_additive zero_le]
theorem one_le (a : α) : 1 ≤ a :=
  le_iff_exists_mul.mpr ⟨a, (one_mulₓ _).symm⟩

@[simp, to_additive]
theorem bot_eq_one : (⊥ : α) = 1 :=
  le_antisymmₓ bot_le (one_le ⊥)

@[simp, to_additive]
theorem mul_eq_one_iff : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  mul_eq_one_iff' (one_le _) (one_le _)

@[simp, to_additive]
theorem le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
  Iff.intro (fun h => le_antisymmₓ h (one_le a)) fun h => h ▸ le_reflₓ a

@[to_additive]
theorem one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
  (Iff.intro ne_of_gtₓ) fun hne => lt_of_le_of_neₓ (one_le _) hne.symm

@[to_additive]
theorem exists_pos_mul_of_lt (h : a < b) : ∃ c > 1, a * c = b := by
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le
  refine' ⟨c, one_lt_iff_ne_one.2 _, hc.symm⟩
  rintro rfl
  simpa [hc, lt_irreflₓ] using h

@[to_additive]
theorem le_mul_left (h : a ≤ c) : a ≤ b * c :=
  calc
    a = 1 * a := by
      simp
    _ ≤ b * c := mul_le_mul' (one_le _) h
    

@[to_additive]
theorem le_mul_self : a ≤ b * a :=
  le_mul_left (le_reflₓ a)

@[to_additive]
theorem le_mul_right (h : a ≤ b) : a ≤ b * c :=
  calc
    a = a * 1 := by
      simp
    _ ≤ b * c := mul_le_mul' h (one_le _)
    

@[to_additive]
theorem le_self_mul : a ≤ a * c :=
  le_mul_right (le_reflₓ a)

@[to_additive]
theorem lt_iff_exists_mul [CovariantClass α α (· * ·) (· < ·)] : a < b ↔ ∃ c > 1, b = a * c := by
  simp_rw [lt_iff_le_and_ne, and_comm, le_iff_exists_mul, ← exists_and_distrib_left, exists_prop]
  apply exists_congr
  intro c
  rw [And.congr_left_iff, gt_iff_lt]
  rintro rfl
  constructor
  · rw [one_lt_iff_ne_one]
    apply mt
    rintro rfl
    rw [mul_oneₓ]
    
  · rw [← (self_le_mul_right a c).lt_iff_ne]
    apply lt_mul_of_one_lt_right'
    

/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
-- This instance looks absurd: a monoid already has a zero
instance WithZero.canonicallyOrderedAddMonoid {α : Type u} [CanonicallyOrderedAddMonoid α] :
    CanonicallyOrderedAddMonoid (WithZero α) :=
  { WithZero.orderBot, WithZero.orderedAddCommMonoid zero_le with
    le_iff_exists_add := fun a b => by
      apply WithZero.cases_on a
      · exact iff_of_true bot_le ⟨b, (zero_addₓ b).symm⟩
        
      apply WithZero.cases_on b
      · intro b'
        refine'
          iff_of_false
            (mt (le_antisymmₓ bot_le)
              (by
                simp ))
            (not_exists.mpr fun c => _)
        apply WithZero.cases_on c <;> simp [← WithZero.coe_add]
        
      · simp only [le_iff_exists_add, WithZero.coe_le_coe]
        intros
        constructor <;> rintro ⟨c, h⟩
        · exact ⟨c, congr_argₓ coe h⟩
          
        · induction c using WithZero.cases_on
          · refine' ⟨0, _⟩
            simpa using h
            
          · refine' ⟨c, _⟩
            simpa [← WithZero.coe_add] using h
            
          
         }

instance WithTop.canonicallyOrderedAddMonoid {α : Type u} [CanonicallyOrderedAddMonoid α] :
    CanonicallyOrderedAddMonoid (WithTop α) :=
  { WithTop.orderBot, WithTop.orderedAddCommMonoid with
    le_iff_exists_add := fun a b =>
      match a, b with
      | a, none =>
        show a ≤ ⊤ ↔ ∃ c, ⊤ = a + c by
          simp <;> refine' ⟨⊤, _⟩ <;> cases a <;> rfl
      | some a, some b =>
        show (a : WithTop α) ≤ ↑b ↔ ∃ c : WithTop α, ↑b = ↑a + c by
          simp [CanonicallyOrderedAddMonoid.le_iff_exists_add, -add_commₓ]
          constructor
          · rintro ⟨c, rfl⟩
            refine' ⟨c, _⟩
            norm_cast
            
          · exact fun h =>
              match b, h with
              | _, ⟨some c, rfl⟩ => ⟨_, rfl⟩
            
      | none, some b =>
        show (⊤ : WithTop α) ≤ b ↔ ∃ c : WithTop α, ↑b = ⊤ + c by
          simp }

@[to_additive]
instance (priority := 100) CanonicallyOrderedMonoid.has_exists_mul_of_le (α : Type u) [CanonicallyOrderedMonoid α] :
    HasExistsMulOfLe α where
  exists_mul_of_le := fun a b hab => le_iff_exists_mul.mp hab

end CanonicallyOrderedMonoid

theorem pos_of_gt {M : Type _} [CanonicallyOrderedAddMonoid M] {n m : M} (h : n < m) : 0 < m :=
  lt_of_le_of_ltₓ (zero_le _) h

/-- A canonically linear-ordered additive monoid is a canonically ordered additive monoid
    whose ordering is a linear order. -/
@[protect_proj, ancestor CanonicallyOrderedAddMonoid LinearOrderₓ]
class CanonicallyLinearOrderedAddMonoid (α : Type _) extends CanonicallyOrderedAddMonoid α, LinearOrderₓ α

/-- A canonically linear-ordered monoid is a canonically ordered monoid
    whose ordering is a linear order. -/
@[protect_proj, ancestor CanonicallyOrderedMonoid LinearOrderₓ, to_additive]
class CanonicallyLinearOrderedMonoid (α : Type _) extends CanonicallyOrderedMonoid α, LinearOrderₓ α

section CanonicallyLinearOrderedMonoid

variable [CanonicallyLinearOrderedMonoid α]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CanonicallyLinearOrderedMonoid.semilatticeSup : SemilatticeSup α :=
  { LinearOrderₓ.toLattice with }

instance WithTop.canonicallyLinearOrderedAddMonoid (α : Type _) [CanonicallyLinearOrderedAddMonoid α] :
    CanonicallyLinearOrderedAddMonoid (WithTop α) :=
  { (inferInstance : CanonicallyOrderedAddMonoid (WithTop α)), (inferInstance : LinearOrderₓ (WithTop α)) with }

@[to_additive]
theorem min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c) := by
  cases' le_totalₓ a b with hb hb
  · simp [hb, le_mul_right]
    
  · cases' le_totalₓ a c with hc hc
    · simp [hc, le_mul_left]
      
    · simp [hb, hc]
      
    

@[to_additive]
theorem min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c := by
  simpa [min_commₓ _ c] using min_mul_distrib c a b

@[simp, to_additive]
theorem one_min (a : α) : min 1 a = 1 :=
  min_eq_leftₓ (one_le a)

@[simp, to_additive]
theorem min_one (a : α) : min a 1 = 1 :=
  min_eq_rightₓ (one_le a)

end CanonicallyLinearOrderedMonoid

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor AddCancelCommMonoid PartialOrderₓ]
class OrderedCancelAddCommMonoid (α : Type u) extends AddCancelCommMonoid α, PartialOrderₓ α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor CancelCommMonoid PartialOrderₓ, to_additive]
class OrderedCancelCommMonoid (α : Type u) extends CancelCommMonoid α, PartialOrderₓ α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] {a b c d : α}

@[to_additive]
theorem OrderedCancelCommMonoid.lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c := fun a b c h =>
  lt_of_le_not_leₓ (OrderedCancelCommMonoid.le_of_mul_le_mul_left a b c h.le) <|
    mt (fun h => OrderedCancelCommMonoid.mul_le_mul_left _ _ h _) (not_le_of_gtₓ h)

@[to_additive]
instance OrderedCancelCommMonoid.to_contravariant_class_left (M : Type _) [OrderedCancelCommMonoid M] :
    ContravariantClass M M (· * ·) (· < ·) where
  elim := fun a b c => OrderedCancelCommMonoid.lt_of_mul_lt_mul_left _ _ _

/- This instance can be proven with `by apply_instance`.  However, by analogy with the
instance `ordered_cancel_comm_monoid.to_covariant_class_right` above, I imagine that without
this instance, some Type would not have a `contravariant_class M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance OrderedCancelCommMonoid.to_contravariant_class_right (M : Type _) [OrderedCancelCommMonoid M] :
    ContravariantClass M M (swap (· * ·)) (· < ·) :=
  contravariant_swap_mul_lt_of_contravariant_mul_lt M

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toOrderedCommMonoid : OrderedCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with }

/-- Pullback an `ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.orderedCancelAddCommMonoid
      "Pullback an `ordered_cancel_add_comm_monoid` under an injective map."]
def Function.Injective.orderedCancelCommMonoid {β : Type _} [One β] [Mul β] (f : β → α) (hf : Function.Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) : OrderedCancelCommMonoid β :=
  { hf.LeftCancelSemigroup f mul, hf.OrderedCommMonoid f one mul with
    le_of_mul_le_mul_left := fun bc : f (a * b) ≤ f (a * c) =>
      (mul_le_mul_iff_left (f a)).mp
        (by
          rwa [← mul, ← mul]) }

end OrderedCancelCommMonoid

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/


@[to_additive]
theorem fn_min_mul_fn_max {β} [LinearOrderₓ α] [CommSemigroupₓ β] (f : α → β) (n m : α) :
    f (min n m) * f (max n m) = f n * f m := by
  cases' le_totalₓ n m with h h <;> simp [h, mul_comm]

@[to_additive]
theorem min_mul_max [LinearOrderₓ α] [CommSemigroupₓ α] (n m : α) : min n m * max n m = n * m :=
  fn_min_mul_fn_max id n m

/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor OrderedCancelAddCommMonoid LinearOrderedAddCommMonoid]
class LinearOrderedCancelAddCommMonoid (α : Type u) extends OrderedCancelAddCommMonoid α, LinearOrderedAddCommMonoid α

/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor OrderedCancelCommMonoid LinearOrderedCommMonoid, to_additive]
class LinearOrderedCancelCommMonoid (α : Type u) extends OrderedCancelCommMonoid α, LinearOrderedCommMonoid α

section CovariantClassMulLe

variable [LinearOrderₓ α]

section Mul

variable [Mul α]

section Left

variable [CovariantClass α α (· * ·) (· ≤ ·)]

@[to_additive]
theorem min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
  (monotone_id.const_mul' a).map_min.symm

@[to_additive]
theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
  (monotone_id.const_mul' a).map_max.symm

end Left

section Right

variable [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]

@[to_additive]
theorem min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
  (monotone_id.mul_const' c).map_min.symm

@[to_additive]
theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
  (monotone_id.mul_const' c).map_max.symm

end Right

end Mul

variable [Monoidₓ α]

@[to_additive]
theorem min_le_mul_of_one_le_right [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (hb : 1 ≤ b) : min a b ≤ a * b :=
  min_le_iff.2 <| Or.inl <| le_mul_of_one_le_right' hb

@[to_additive]
theorem min_le_mul_of_one_le_left [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) :
    min a b ≤ a * b :=
  min_le_iff.2 <| Or.inr <| le_mul_of_one_le_left' ha

@[to_additive]
theorem max_le_mul_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (Function.swap (· * ·)) (· ≤ ·)]
    {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : max a b ≤ a * b :=
  max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

end CovariantClassMulLe

section LinearOrderedCancelCommMonoid

variable [LinearOrderedCancelCommMonoid α]

/-- Pullback a `linear_ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedCancelAddCommMonoid
      "Pullback a `linear_ordered_cancel_add_comm_monoid` under an injective map."]
def Function.Injective.linearOrderedCancelCommMonoid {β : Type _} [One β] [Mul β] (f : β → α)
    (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
    LinearOrderedCancelCommMonoid β :=
  { hf.LinearOrderedCommMonoid f one mul, hf.OrderedCancelCommMonoid f one mul with }

end LinearOrderedCancelCommMonoid

namespace OrderDual

@[to_additive]
instance [h : Mul α] : Mul (OrderDual α) :=
  h

@[to_additive]
instance [h : One α] : One (OrderDual α) :=
  h

@[to_additive]
instance [h : Monoidₓ α] : Monoidₓ (OrderDual α) :=
  h

@[to_additive]
instance [h : CommMonoidₓ α] : CommMonoidₓ (OrderDual α) :=
  h

@[to_additive]
instance [h : CancelCommMonoid α] : CancelCommMonoid (OrderDual α) :=
  h

@[to_additive]
instance contravariant_class_mul_le [LE α] [Mul α] [c : ContravariantClass α α (· * ·) (· ≤ ·)] :
    ContravariantClass (OrderDual α) (OrderDual α) (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariant_class_mul_le [LE α] [Mul α] [c : CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass (OrderDual α) (OrderDual α) (· * ·) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance contravariant_class_swap_mul_le [LE α] [Mul α] [c : ContravariantClass α α (swap (· * ·)) (· ≤ ·)] :
    ContravariantClass (OrderDual α) (OrderDual α) (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariant_class_swap_mul_le [LE α] [Mul α] [c : CovariantClass α α (swap (· * ·)) (· ≤ ·)] :
    CovariantClass (OrderDual α) (OrderDual α) (swap (· * ·)) (· ≤ ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance contravariant_class_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass (OrderDual α) (OrderDual α) (· * ·) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariant_class_mul_lt [LT α] [Mul α] [c : CovariantClass α α (· * ·) (· < ·)] :
    CovariantClass (OrderDual α) (OrderDual α) (· * ·) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance contravariant_class_swap_mul_lt [LT α] [Mul α] [c : ContravariantClass α α (swap (· * ·)) (· < ·)] :
    ContravariantClass (OrderDual α) (OrderDual α) (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance covariant_class_swap_mul_lt [LT α] [Mul α] [c : CovariantClass α α (swap (· * ·)) (· < ·)] :
    CovariantClass (OrderDual α) (OrderDual α) (swap (· * ·)) (· < ·) :=
  ⟨c.1.flip⟩

@[to_additive]
instance [OrderedCommMonoid α] : OrderedCommMonoid (OrderDual α) :=
  { OrderDual.partialOrder α, OrderDual.commMonoid with mul_le_mul_left := fun a b h c => mul_le_mul_left' h c }

@[to_additive OrderedCancelAddCommMonoid.to_contravariant_class]
instance OrderedCancelCommMonoid.to_contravariant_class [OrderedCancelCommMonoid α] :
    ContravariantClass (OrderDual α) (OrderDual α) Mul.mul LE.le where
  elim := fun a b c bc => OrderedCancelCommMonoid.le_of_mul_le_mul_left a c b (dual_le.mp bc)

@[to_additive]
instance [OrderedCancelCommMonoid α] : OrderedCancelCommMonoid (OrderDual α) :=
  { OrderDual.orderedCommMonoid, OrderDual.cancelCommMonoid with
    le_of_mul_le_mul_left := fun a b c : α => le_of_mul_le_mul_left' }

@[to_additive]
instance [LinearOrderedCancelCommMonoid α] : LinearOrderedCancelCommMonoid (OrderDual α) :=
  { OrderDual.linearOrder α, OrderDual.orderedCancelCommMonoid with }

@[to_additive]
instance [LinearOrderedCommMonoid α] : LinearOrderedCommMonoid (OrderDual α) :=
  { OrderDual.linearOrder α, OrderDual.orderedCommMonoid with }

end OrderDual

section LinearOrderedCancelAddCommMonoid

variable [LinearOrderedCancelAddCommMonoid α]

theorem lt_or_lt_of_add_lt_add {a b m n : α} (h : m + n < a + b) : m < a ∨ n < b := by
  contrapose! h
  exact add_le_add h.1 h.2

end LinearOrderedCancelAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid α]

namespace WithTop

theorem add_lt_add_iff_left {a b c : WithTop α} (ha : a ≠ ⊤) : a + b < a + c ↔ b < c := by
  lift a to α using ha
  cases b <;> cases c
  · simp [none_eq_top]
    
  · simp [some_eq_coe, none_eq_top, coe_lt_top]
    
  · simp [some_eq_coe, none_eq_top, ← coe_add, coe_lt_top]
    
  · simp [some_eq_coe, ← coe_add, coe_lt_coe]
    

theorem add_lt_add_iff_right {a b c : WithTop α} (ha : a ≠ ⊤) : c + a < b + a ↔ c < b := by
  simp only [← add_commₓ a, add_lt_add_iff_left ha]

instance contravariant_class_add_lt : ContravariantClass (WithTop α) (WithTop α) (· + ·) (· < ·) := by
  refine' ⟨fun a b c h => _⟩
  cases a
  · rw [none_eq_top, top_add, top_add] at h
    exact (lt_irreflₓ ⊤ h).elim
    
  · exact (add_lt_add_iff_left coe_ne_top).1 h
    

end WithTop

namespace WithBot

theorem add_lt_add_iff_left {a b c : WithBot α} (ha : a ≠ ⊥) : a + b < a + c ↔ b < c :=
  @WithTop.add_lt_add_iff_left (OrderDual α) _ a c b ha

theorem add_lt_add_iff_right {a b c : WithBot α} (ha : a ≠ ⊥) : b + a < c + a ↔ b < c :=
  @WithTop.add_lt_add_iff_right (OrderDual α) _ _ _ _ ha

instance contravariant_class_add_lt : ContravariantClass (WithBot α) (WithBot α) (· + ·) (· < ·) :=
  @OrderDual.contravariant_class_add_lt (WithTop <| OrderDual α) _ _ _

end WithBot

end OrderedCancelAddCommMonoid

namespace Prod

variable {M N : Type _}

@[to_additive]
instance [OrderedCancelCommMonoid M] [OrderedCancelCommMonoid N] : OrderedCancelCommMonoid (M × N) :=
  { Prod.cancelCommMonoid, Prod.partialOrder M N with
    mul_le_mul_left := fun a b h c => ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩,
    le_of_mul_le_mul_left := fun a b c h => ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

end Prod

section TypeTags

instance : ∀ [Preorderₓ α], Preorderₓ (Multiplicative α) :=
  id

instance : ∀ [Preorderₓ α], Preorderₓ (Additive α) :=
  id

instance : ∀ [PartialOrderₓ α], PartialOrderₓ (Multiplicative α) :=
  id

instance : ∀ [PartialOrderₓ α], PartialOrderₓ (Additive α) :=
  id

instance : ∀ [LinearOrderₓ α], LinearOrderₓ (Multiplicative α) :=
  id

instance : ∀ [LinearOrderₓ α], LinearOrderₓ (Additive α) :=
  id

instance [OrderedAddCommMonoid α] : OrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.partialOrder, Multiplicative.commMonoid with
    mul_le_mul_left := @OrderedAddCommMonoid.add_le_add_left α _ }

instance [OrderedCommMonoid α] : OrderedAddCommMonoid (Additive α) :=
  { Additive.partialOrder, Additive.addCommMonoid with add_le_add_left := @OrderedCommMonoid.mul_le_mul_left α _ }

instance [OrderedCancelAddCommMonoid α] : OrderedCancelCommMonoid (Multiplicative α) :=
  { Multiplicative.leftCancelSemigroup, Multiplicative.orderedCommMonoid with
    le_of_mul_le_mul_left := @OrderedCancelAddCommMonoid.le_of_add_le_add_left α _ }

instance [OrderedCancelCommMonoid α] : OrderedCancelAddCommMonoid (Additive α) :=
  { Additive.addLeftCancelSemigroup, Additive.orderedAddCommMonoid with
    le_of_add_le_add_left := @OrderedCancelCommMonoid.le_of_mul_le_mul_left α _ }

instance [LinearOrderedAddCommMonoid α] : LinearOrderedCommMonoid (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommMonoid with }

instance [LinearOrderedCommMonoid α] : LinearOrderedAddCommMonoid (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommMonoid with }

theorem WithZero.to_mul_bot_strict_mono [Add α] [Preorderₓ α] : StrictMono (@WithZero.toMulBot α _) := fun x y => id

@[simp]
theorem WithZero.to_mul_bot_le [Add α] [Preorderₓ α] (a b : WithZero (Multiplicative α)) :
    WithZero.toMulBot a ≤ WithZero.toMulBot b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem WithZero.to_mul_bot_lt [Add α] [Preorderₓ α] (a b : WithZero (Multiplicative α)) :
    WithZero.toMulBot a < WithZero.toMulBot b ↔ a < b :=
  Iff.rfl

namespace Additive

variable [Preorderₓ α]

@[simp]
theorem of_mul_le {a b : α} : ofMul a ≤ ofMul b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem of_mul_lt {a b : α} : ofMul a < ofMul b ↔ a < b :=
  Iff.rfl

@[simp]
theorem to_mul_le {a b : Additive α} : toMul a ≤ toMul b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem to_mul_lt {a b : Additive α} : toMul a < toMul b ↔ a < b :=
  Iff.rfl

end Additive

namespace Multiplicative

variable [Preorderₓ α]

@[simp]
theorem of_add_le {a b : α} : ofAdd a ≤ ofAdd b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem of_add_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b :=
  Iff.rfl

@[simp]
theorem to_add_le {a b : Multiplicative α} : toAdd a ≤ toAdd b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem to_add_lt {a b : Multiplicative α} : toAdd a < toAdd b ↔ a < b :=
  Iff.rfl

end Multiplicative

end TypeTags

/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `order_iso.mul_left` when working in an ordered group. -/
@[to_additive
      "The order embedding sending `b` to `a + b`, for some fixed `a`.\n  See also `order_iso.add_left` when working in an additive ordered group.",
  simps]
def OrderEmbedding.mulLeft {α : Type _} [Mul α] [LinearOrderₓ α] [CovariantClass α α (· * ·) (· < ·)] (m : α) :
    α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) fun a b w => mul_lt_mul_left' w m

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `order_iso.mul_right` when working in an ordered group. -/
@[to_additive
      "The order embedding sending `b` to `b + a`, for some fixed `a`.\n  See also `order_iso.add_right` when working in an additive ordered group.",
  simps]
def OrderEmbedding.mulRight {α : Type _} [Mul α] [LinearOrderₓ α] [CovariantClass α α (swap (· * ·)) (· < ·)] (m : α) :
    α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) fun a b w => mul_lt_mul_right' w m

