/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa
-/
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

instance [Nontrivial α] : Nontrivial (OrderDual α) := by
  delta' OrderDual <;> assumption

/-- `to_dual` is the identity function to the `order_dual` of a linear order.  -/
def toDual : α ≃ OrderDual α :=
  ⟨id, id, fun h => rfl, fun h => rfl⟩

/-- `of_dual` is the identity function from the `order_dual` of a linear order.  -/
def ofDual : OrderDual α ≃ α :=
  toDual.symm

@[simp]
theorem to_dual_symm_eq : (@toDual α).symm = of_dual :=
  rfl

@[simp]
theorem of_dual_symm_eq : (@ofDual α).symm = to_dual :=
  rfl

@[simp]
theorem to_dual_of_dual (a : OrderDual α) : toDual (ofDual a) = a :=
  rfl

@[simp]
theorem of_dual_to_dual (a : α) : ofDual (toDual a) = a :=
  rfl

@[simp]
theorem to_dual_inj {a b : α} : toDual a = toDual b ↔ a = b :=
  Iff.rfl

@[simp]
theorem to_dual_le_to_dual [LE α] {a b : α} : toDual a ≤ toDual b ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem to_dual_lt_to_dual [LT α] {a b : α} : toDual a < toDual b ↔ b < a :=
  Iff.rfl

@[simp]
theorem of_dual_inj {a b : OrderDual α} : ofDual a = ofDual b ↔ a = b :=
  Iff.rfl

@[simp]
theorem of_dual_le_of_dual [LE α] {a b : OrderDual α} : ofDual a ≤ ofDual b ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem of_dual_lt_of_dual [LT α] {a b : OrderDual α} : ofDual a < ofDual b ↔ b < a :=
  Iff.rfl

theorem le_to_dual [LE α] {a : OrderDual α} {b : α} : a ≤ toDual b ↔ b ≤ ofDual a :=
  Iff.rfl

theorem lt_to_dual [LT α] {a : OrderDual α} {b : α} : a < toDual b ↔ b < ofDual a :=
  Iff.rfl

theorem to_dual_le [LE α] {a : α} {b : OrderDual α} : toDual a ≤ b ↔ ofDual b ≤ a :=
  Iff.rfl

theorem to_dual_lt [LT α] {a : α} {b : OrderDual α} : toDual a < b ↔ ofDual b < a :=
  Iff.rfl

/-- Recursor for `order_dual α`. -/
@[elab_as_eliminator]
protected def rec {C : OrderDual α → Sort _} (h₂ : ∀ a : α, C (toDual a)) : ∀ a : OrderDual α, C a :=
  h₂

@[simp]
protected theorem forall {p : OrderDual α → Prop} : (∀ a, p a) ↔ ∀ a, p (toDual a) :=
  Iff.rfl

@[simp]
protected theorem exists {p : OrderDual α → Prop} : (∃ a, p a) ↔ ∃ a, p (toDual a) :=
  Iff.rfl

end OrderDual

alias OrderDual.to_dual_le_to_dual ↔ _ LE.le.dual

alias OrderDual.to_dual_lt_to_dual ↔ _ LT.lt.dual

alias OrderDual.of_dual_le_of_dual ↔ _ LE.le.of_dual

alias OrderDual.of_dual_lt_of_dual ↔ _ LT.lt.of_dual

