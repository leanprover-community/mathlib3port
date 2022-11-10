/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Monoid.Canonical.Defs
import Mathbin.Algebra.Group.WithOne

/-!
# Adjoining a zero element to an ordered monoid.
-/


universe u

variable {α : Type u}

namespace WithZero

attribute [local semireducible] WithZero

instance [Preorder α] : Preorder (WithZero α) :=
  WithBot.preorder

instance [PartialOrder α] : PartialOrder (WithZero α) :=
  WithBot.partialOrder

instance [Preorder α] : OrderBot (WithZero α) :=
  WithBot.orderBot

theorem zero_le [Preorder α] (a : WithZero α) : 0 ≤ a :=
  bot_le

theorem zero_lt_coe [Preorder α] (a : α) : (0 : WithZero α) < a :=
  WithBot.bot_lt_coe a

theorem zero_eq_bot [Preorder α] : (0 : WithZero α) = ⊥ :=
  rfl

@[simp, norm_cast]
theorem coe_lt_coe [Preorder α] {a b : α} : (a : WithZero α) < b ↔ a < b :=
  WithBot.coe_lt_coe

@[simp, norm_cast]
theorem coe_le_coe [Preorder α] {a b : α} : (a : WithZero α) ≤ b ↔ a ≤ b :=
  WithBot.coe_le_coe

instance [Lattice α] : Lattice (WithZero α) :=
  WithBot.lattice

instance [LinearOrder α] : LinearOrder (WithZero α) :=
  WithBot.linearOrder

instance covariant_class_mul_le {α : Type u} [Mul α] [Preorder α] [CovariantClass α α (· * ·) (· ≤ ·)] :
    CovariantClass (WithZero α) (WithZero α) (· * ·) (· ≤ ·) := by
  refine' ⟨fun a b c hbc => _⟩
  induction a using WithZero.recZeroCoe
  · exact zero_le _
    
  induction b using WithZero.recZeroCoe
  · exact zero_le _
    
  rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
  rw [← coe_mul, ← coe_mul, coe_le_coe]
  exact mul_le_mul_left' hbc' a

instance contravariant_class_mul_lt {α : Type u} [Mul α] [PartialOrder α] [ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass (WithZero α) (WithZero α) (· * ·) (· < ·) := by
  refine' ⟨fun a b c h => _⟩
  have := ((zero_le _).trans_lt h).ne'
  lift a to α using left_ne_zero_of_mul this
  lift c to α using right_ne_zero_of_mul this
  induction b using WithZero.recZeroCoe
  exacts[zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]

@[simp]
theorem le_max_iff [LinearOrder α] {a b c : α} : (a : WithZero α) ≤ max b c ↔ a ≤ max b c := by
  simp only [WithZero.coe_le_coe, le_max_iff]

@[simp]
theorem min_le_iff [LinearOrder α] {a b c : α} : min (a : WithZero α) b ≤ c ↔ min a b ≤ c := by
  simp only [WithZero.coe_le_coe, min_le_iff]

instance [OrderedCommMonoid α] : OrderedCommMonoid (WithZero α) :=
  { WithZero.commMonoidWithZero, WithZero.partialOrder with mul_le_mul_left := fun _ _ => mul_le_mul_left' }

protected theorem covariant_class_add_le [AddZeroClass α] [Preorder α] [CovariantClass α α (· + ·) (· ≤ ·)]
    (h : ∀ a : α, 0 ≤ a) : CovariantClass (WithZero α) (WithZero α) (· + ·) (· ≤ ·) := by
  refine' ⟨fun a b c hbc => _⟩
  induction a using WithZero.recZeroCoe
  · rwa [zero_add, zero_add]
    
  induction b using WithZero.recZeroCoe
  · rw [add_zero]
    induction c using WithZero.recZeroCoe
    · rw [add_zero]
      exact le_rfl
      
    · rw [← coe_add, coe_le_coe]
      exact le_add_of_nonneg_right (h _)
      
    
  · rcases WithBot.coe_le_iff.1 hbc with ⟨c, rfl, hbc'⟩
    rw [← coe_add, ← coe_add, coe_le_coe]
    exact add_le_add_left hbc' a
    

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/
/-- If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
See note [reducible non-instances].
-/
@[reducible]
protected def orderedAddCommMonoid [OrderedAddCommMonoid α] (zero_le : ∀ a : α, 0 ≤ a) :
    OrderedAddCommMonoid (WithZero α) :=
  { WithZero.partialOrder, WithZero.addCommMonoid with
    add_le_add_left := @add_le_add_left _ _ _ (WithZero.covariant_class_add_le zero_le).. }

end WithZero

section CanonicallyOrderedMonoid

instance WithZero.has_exists_add_of_le {α} [Add α] [Preorder α] [HasExistsAddOfLe α] : HasExistsAddOfLe (WithZero α) :=
  ⟨fun a b => by
    apply WithZero.cases_on a
    · exact fun _ => ⟨b, (zero_add b).symm⟩
      
    apply WithZero.cases_on b
    · exact fun b' h => (WithBot.not_coe_le_bot _ h).elim
      
    rintro a' b' h
    obtain ⟨c, rfl⟩ := exists_add_of_le (WithZero.coe_le_coe.1 h)
    exact ⟨c, rfl⟩⟩

-- This instance looks absurd: a monoid already has a zero
/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance WithZero.canonicallyOrderedAddMonoid {α : Type u} [CanonicallyOrderedAddMonoid α] :
    CanonicallyOrderedAddMonoid (WithZero α) :=
  { WithZero.orderBot, WithZero.orderedAddCommMonoid zero_le, WithZero.has_exists_add_of_le with
    le_self_add := fun a b => by
      apply WithZero.cases_on a
      · exact bot_le
        
      apply WithZero.cases_on b
      · exact fun b' => le_rfl
        
      · exact fun a' b' => WithZero.coe_le_coe.2 le_self_add
         }

end CanonicallyOrderedMonoid

section CanonicallyLinearOrderedMonoid

instance WithZero.canonicallyLinearOrderedAddMonoid (α : Type _) [CanonicallyLinearOrderedAddMonoid α] :
    CanonicallyLinearOrderedAddMonoid (WithZero α) :=
  { WithZero.canonicallyOrderedAddMonoid, WithZero.linearOrder with }

end CanonicallyLinearOrderedMonoid

