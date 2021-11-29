import Mathbin.Data.Equiv.Basic 
import Mathbin.Logic.Nontrivial 
import Mathbin.Order.Basic

/-!
# Initial lemmas to work with the `order_dual`

## Definitions
`to_dual` and `of_dual` the order reversing identity maps, bundled as equivalences.

## Basic Lemmas to convert between an order and its dual

This file is similar to algebra/group/type_tags.lean
-/


open Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

namespace OrderDual

instance [Nontrivial α] : Nontrivial (OrderDual α) :=
  by 
    delta' OrderDual <;> assumption

/-- `to_dual` is the identity function to the `order_dual` of a linear order.  -/
def to_dual : α ≃ OrderDual α :=
  ⟨id, id, fun h => rfl, fun h => rfl⟩

/-- `of_dual` is the identity function from the `order_dual` of a linear order.  -/
def of_dual : OrderDual α ≃ α :=
  to_dual.symm

@[simp]
theorem to_dual_symm_eq : (@to_dual α).symm = of_dual :=
  rfl

@[simp]
theorem of_dual_symm_eq : (@of_dual α).symm = to_dual :=
  rfl

@[simp]
theorem to_dual_of_dual (a : OrderDual α) : to_dual (of_dual a) = a :=
  rfl

@[simp]
theorem of_dual_to_dual (a : α) : of_dual (to_dual a) = a :=
  rfl

@[simp]
theorem to_dual_inj {a b : α} : to_dual a = to_dual b ↔ a = b :=
  Iff.rfl

@[simp]
theorem to_dual_le_to_dual [LE α] {a b : α} : to_dual a ≤ to_dual b ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem to_dual_lt_to_dual [LT α] {a b : α} : to_dual a < to_dual b ↔ b < a :=
  Iff.rfl

@[simp]
theorem of_dual_inj {a b : OrderDual α} : of_dual a = of_dual b ↔ a = b :=
  Iff.rfl

@[simp]
theorem of_dual_le_of_dual [LE α] {a b : OrderDual α} : of_dual a ≤ of_dual b ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem of_dual_lt_of_dual [LT α] {a b : OrderDual α} : of_dual a < of_dual b ↔ b < a :=
  Iff.rfl

theorem le_to_dual [LE α] {a : OrderDual α} {b : α} : a ≤ to_dual b ↔ b ≤ of_dual a :=
  Iff.rfl

theorem lt_to_dual [LT α] {a : OrderDual α} {b : α} : a < to_dual b ↔ b < of_dual a :=
  Iff.rfl

theorem to_dual_le [LE α] {a : α} {b : OrderDual α} : to_dual a ≤ b ↔ of_dual b ≤ a :=
  Iff.rfl

theorem to_dual_lt [LT α] {a : α} {b : OrderDual α} : to_dual a < b ↔ of_dual b < a :=
  Iff.rfl

/-- Recursor for `order_dual α`. -/
@[elab_as_eliminator]
protected def rec {C : OrderDual α → Sort _} (h₂ : ∀ a : α, C (to_dual a)) : ∀ a : OrderDual α, C a :=
  h₂

@[simp]
protected theorem forall {p : OrderDual α → Prop} : (∀ a, p a) ↔ ∀ a, p (to_dual a) :=
  Iff.rfl

@[simp]
protected theorem exists {p : OrderDual α → Prop} : (∃ a, p a) ↔ ∃ a, p (to_dual a) :=
  Iff.rfl

end OrderDual

alias OrderDual.to_dual_lt_to_dual ↔ _ LT.lt.dual

alias OrderDual.to_dual_le_to_dual ↔ _ LE.le.dual

