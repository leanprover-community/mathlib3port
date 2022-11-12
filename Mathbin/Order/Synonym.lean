/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Yaël Dillies
-/
import Mathbin.Logic.Equiv.Defs
import Mathbin.Logic.Nontrivial
import Mathbin.Order.Basic

/-!
# Type synonyms

This file provides two type synonyms for order theory:
* `order_dual α`: Type synonym of `α` to equip it with the dual order (`a ≤ b` becomes `b ≤ a`).
* `lex α`: Type synonym of `α` to equip it with its lexicographic order. The precise meaning depends
  on the type we take the lex of. Examples include `prod`, `sigma`, `list`, `finset`.

## Notation

`αᵒᵈ` is notation for `order_dual α`.

The general rule for notation of `lex` types is to append `ₗ` to the usual notation.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`/`lex α`. Instead, explicit
coercions should be inserted:
* `order_dual`: `order_dual.to_dual : α → αᵒᵈ` and `order_dual.of_dual : αᵒᵈ → α`
* `lex`: `to_lex : α → lex α` and `of_lex : lex α → α`.

In fact, those are bundled as `equiv`s to put goals in the right syntactic form for rewriting with
the `equiv` API (`⇑to_lex a` where `⇑` is `coe_fn : (α ≃ lex α) → α → lex α`, instead of a bare
`to_lex a`).

## See also

This file is similar to `algebra.group.type_tags`.
-/


variable {α β γ : Type _}

/-! ### Order dual -/


namespace OrderDual

instance [h : Nontrivial α] : Nontrivial αᵒᵈ :=
  h

/-- `to_dual` is the identity function to the `order_dual` of a linear order.  -/
def toDual : α ≃ αᵒᵈ :=
  Equiv.refl _
#align order_dual.to_dual OrderDual.toDual

/-- `of_dual` is the identity function from the `order_dual` of a linear order.  -/
def ofDual : αᵒᵈ ≃ α :=
  Equiv.refl _
#align order_dual.of_dual OrderDual.ofDual

@[simp]
theorem to_dual_symm_eq : (@toDual α).symm = of_dual :=
  rfl
#align order_dual.to_dual_symm_eq OrderDual.to_dual_symm_eq

@[simp]
theorem of_dual_symm_eq : (@ofDual α).symm = to_dual :=
  rfl
#align order_dual.of_dual_symm_eq OrderDual.of_dual_symm_eq

@[simp]
theorem to_dual_of_dual (a : αᵒᵈ) : toDual (ofDual a) = a :=
  rfl
#align order_dual.to_dual_of_dual OrderDual.to_dual_of_dual

@[simp]
theorem of_dual_to_dual (a : α) : ofDual (toDual a) = a :=
  rfl
#align order_dual.of_dual_to_dual OrderDual.of_dual_to_dual

@[simp]
theorem to_dual_inj {a b : α} : toDual a = toDual b ↔ a = b :=
  Iff.rfl
#align order_dual.to_dual_inj OrderDual.to_dual_inj

@[simp]
theorem of_dual_inj {a b : αᵒᵈ} : ofDual a = ofDual b ↔ a = b :=
  Iff.rfl
#align order_dual.of_dual_inj OrderDual.of_dual_inj

@[simp]
theorem to_dual_le_to_dual [LE α] {a b : α} : toDual a ≤ toDual b ↔ b ≤ a :=
  Iff.rfl
#align order_dual.to_dual_le_to_dual OrderDual.to_dual_le_to_dual

@[simp]
theorem to_dual_lt_to_dual [LT α] {a b : α} : toDual a < toDual b ↔ b < a :=
  Iff.rfl
#align order_dual.to_dual_lt_to_dual OrderDual.to_dual_lt_to_dual

@[simp]
theorem of_dual_le_of_dual [LE α] {a b : αᵒᵈ} : ofDual a ≤ ofDual b ↔ b ≤ a :=
  Iff.rfl
#align order_dual.of_dual_le_of_dual OrderDual.of_dual_le_of_dual

@[simp]
theorem of_dual_lt_of_dual [LT α] {a b : αᵒᵈ} : ofDual a < ofDual b ↔ b < a :=
  Iff.rfl
#align order_dual.of_dual_lt_of_dual OrderDual.of_dual_lt_of_dual

theorem le_to_dual [LE α] {a : αᵒᵈ} {b : α} : a ≤ toDual b ↔ b ≤ ofDual a :=
  Iff.rfl
#align order_dual.le_to_dual OrderDual.le_to_dual

theorem lt_to_dual [LT α] {a : αᵒᵈ} {b : α} : a < toDual b ↔ b < ofDual a :=
  Iff.rfl
#align order_dual.lt_to_dual OrderDual.lt_to_dual

theorem to_dual_le [LE α] {a : α} {b : αᵒᵈ} : toDual a ≤ b ↔ ofDual b ≤ a :=
  Iff.rfl
#align order_dual.to_dual_le OrderDual.to_dual_le

theorem to_dual_lt [LT α] {a : α} {b : αᵒᵈ} : toDual a < b ↔ ofDual b < a :=
  Iff.rfl
#align order_dual.to_dual_lt OrderDual.to_dual_lt

/-- Recursor for `αᵒᵈ`. -/
@[elab_as_elim]
protected def rec {C : αᵒᵈ → Sort _} (h₂ : ∀ a : α, C (toDual a)) : ∀ a : αᵒᵈ, C a :=
  h₂
#align order_dual.rec OrderDual.rec

@[simp]
protected theorem forall {p : αᵒᵈ → Prop} : (∀ a, p a) ↔ ∀ a, p (toDual a) :=
  Iff.rfl
#align order_dual.forall OrderDual.forall

@[simp]
protected theorem exists {p : αᵒᵈ → Prop} : (∃ a, p a) ↔ ∃ a, p (toDual a) :=
  Iff.rfl
#align order_dual.exists OrderDual.exists

alias to_dual_le_to_dual ↔ _ _root_.has_le.le.dual

alias to_dual_lt_to_dual ↔ _ _root_.has_lt.lt.dual

alias of_dual_le_of_dual ↔ _ _root_.has_le.le.of_dual

alias of_dual_lt_of_dual ↔ _ _root_.has_lt.lt.of_dual

end OrderDual

/-! ### Lexicographic order -/


/-- A type synonym to equip a type with its lexicographic order. -/
def Lex (α : Type _) :=
  α
#align lex Lex

/-- `to_lex` is the identity function to the `lex` of a type.  -/
@[match_pattern]
def toLex : α ≃ Lex α :=
  Equiv.refl _
#align to_lex toLex

/-- `of_lex` is the identity function from the `lex` of a type.  -/
@[match_pattern]
def ofLex : Lex α ≃ α :=
  Equiv.refl _
#align of_lex ofLex

@[simp]
theorem to_lex_symm_eq : (@toLex α).symm = ofLex :=
  rfl
#align to_lex_symm_eq to_lex_symm_eq

@[simp]
theorem of_lex_symm_eq : (@ofLex α).symm = toLex :=
  rfl
#align of_lex_symm_eq of_lex_symm_eq

@[simp]
theorem to_lex_of_lex (a : Lex α) : toLex (ofLex a) = a :=
  rfl
#align to_lex_of_lex to_lex_of_lex

@[simp]
theorem of_lex_to_lex (a : α) : ofLex (toLex a) = a :=
  rfl
#align of_lex_to_lex of_lex_to_lex

@[simp]
theorem to_lex_inj {a b : α} : toLex a = toLex b ↔ a = b :=
  Iff.rfl
#align to_lex_inj to_lex_inj

@[simp]
theorem of_lex_inj {a b : Lex α} : ofLex a = ofLex b ↔ a = b :=
  Iff.rfl
#align of_lex_inj of_lex_inj

/-- A recursor for `lex`. Use as `induction x using lex.rec`. -/
protected def Lex.rec {β : Lex α → Sort _} (h : ∀ a, β (toLex a)) : ∀ a, β a := fun a => h (ofLex a)
#align lex.rec Lex.rec

