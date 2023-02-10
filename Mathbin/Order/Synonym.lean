/-
Copyright (c) 2020 Johan Commelin, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Damiano Testa, Yaël Dillies

! This file was ported from Lean 3 source module order.synonym
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Defs
import Mathbin.Logic.Nontrivial
import Mathbin.Order.Basic

/-!
# Type synonyms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print OrderDual.toDual /-
/-- `to_dual` is the identity function to the `order_dual` of a linear order.  -/
def toDual : α ≃ αᵒᵈ :=
  Equiv.refl _
#align order_dual.to_dual OrderDual.toDual
-/

#print OrderDual.ofDual /-
/-- `of_dual` is the identity function from the `order_dual` of a linear order.  -/
def ofDual : αᵒᵈ ≃ α :=
  Equiv.refl _
#align order_dual.of_dual OrderDual.ofDual
-/

#print OrderDual.toDual_symm_eq /-
@[simp]
theorem toDual_symm_eq : (@toDual α).symm = ofDual :=
  rfl
#align order_dual.to_dual_symm_eq OrderDual.toDual_symm_eq
-/

#print OrderDual.ofDual_symm_eq /-
@[simp]
theorem ofDual_symm_eq : (@ofDual α).symm = toDual :=
  rfl
#align order_dual.of_dual_symm_eq OrderDual.ofDual_symm_eq
-/

#print OrderDual.toDual_ofDual /-
@[simp]
theorem toDual_ofDual (a : αᵒᵈ) : toDual (ofDual a) = a :=
  rfl
#align order_dual.to_dual_of_dual OrderDual.toDual_ofDual
-/

#print OrderDual.ofDual_toDual /-
@[simp]
theorem ofDual_toDual (a : α) : ofDual (toDual a) = a :=
  rfl
#align order_dual.of_dual_to_dual OrderDual.ofDual_toDual
-/

#print OrderDual.toDual_inj /-
@[simp]
theorem toDual_inj {a b : α} : toDual a = toDual b ↔ a = b :=
  Iff.rfl
#align order_dual.to_dual_inj OrderDual.toDual_inj
-/

#print OrderDual.ofDual_inj /-
@[simp]
theorem ofDual_inj {a b : αᵒᵈ} : ofDual a = ofDual b ↔ a = b :=
  Iff.rfl
#align order_dual.of_dual_inj OrderDual.ofDual_inj
-/

#print OrderDual.toDual_le_toDual /-
@[simp]
theorem toDual_le_toDual [LE α] {a b : α} : toDual a ≤ toDual b ↔ b ≤ a :=
  Iff.rfl
#align order_dual.to_dual_le_to_dual OrderDual.toDual_le_toDual
-/

#print OrderDual.toDual_lt_toDual /-
@[simp]
theorem toDual_lt_toDual [LT α] {a b : α} : toDual a < toDual b ↔ b < a :=
  Iff.rfl
#align order_dual.to_dual_lt_to_dual OrderDual.toDual_lt_toDual
-/

#print OrderDual.ofDual_le_ofDual /-
@[simp]
theorem ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual a ≤ ofDual b ↔ b ≤ a :=
  Iff.rfl
#align order_dual.of_dual_le_of_dual OrderDual.ofDual_le_ofDual
-/

#print OrderDual.ofDual_lt_ofDual /-
@[simp]
theorem ofDual_lt_ofDual [LT α] {a b : αᵒᵈ} : ofDual a < ofDual b ↔ b < a :=
  Iff.rfl
#align order_dual.of_dual_lt_of_dual OrderDual.ofDual_lt_ofDual
-/

#print OrderDual.le_toDual /-
theorem le_toDual [LE α] {a : αᵒᵈ} {b : α} : a ≤ toDual b ↔ b ≤ ofDual a :=
  Iff.rfl
#align order_dual.le_to_dual OrderDual.le_toDual
-/

#print OrderDual.lt_toDual /-
theorem lt_toDual [LT α] {a : αᵒᵈ} {b : α} : a < toDual b ↔ b < ofDual a :=
  Iff.rfl
#align order_dual.lt_to_dual OrderDual.lt_toDual
-/

#print OrderDual.toDual_le /-
theorem toDual_le [LE α] {a : α} {b : αᵒᵈ} : toDual a ≤ b ↔ ofDual b ≤ a :=
  Iff.rfl
#align order_dual.to_dual_le OrderDual.toDual_le
-/

#print OrderDual.toDual_lt /-
theorem toDual_lt [LT α] {a : α} {b : αᵒᵈ} : toDual a < b ↔ ofDual b < a :=
  Iff.rfl
#align order_dual.to_dual_lt OrderDual.toDual_lt
-/

#print OrderDual.rec /-
/-- Recursor for `αᵒᵈ`. -/
@[elab_as_elim]
protected def rec {C : αᵒᵈ → Sort _} (h₂ : ∀ a : α, C (toDual a)) : ∀ a : αᵒᵈ, C a :=
  h₂
#align order_dual.rec OrderDual.rec
-/

#print OrderDual.forall /-
@[simp]
protected theorem forall {p : αᵒᵈ → Prop} : (∀ a, p a) ↔ ∀ a, p (toDual a) :=
  Iff.rfl
#align order_dual.forall OrderDual.forall
-/

#print OrderDual.exists /-
@[simp]
protected theorem exists {p : αᵒᵈ → Prop} : (∃ a, p a) ↔ ∃ a, p (toDual a) :=
  Iff.rfl
#align order_dual.exists OrderDual.exists
-/

alias to_dual_le_to_dual ↔ _ _root_.has_le.le.dual
#align has_le.le.dual LE.le.dual

alias to_dual_lt_to_dual ↔ _ _root_.has_lt.lt.dual
#align has_lt.lt.dual LT.lt.dual

alias of_dual_le_of_dual ↔ _ _root_.has_le.le.of_dual
#align has_le.le.of_dual LE.le.ofDual

alias of_dual_lt_of_dual ↔ _ _root_.has_lt.lt.of_dual
#align has_lt.lt.of_dual LT.lt.ofDual

end OrderDual

/-! ### Lexicographic order -/


#print Lex /-
/-- A type synonym to equip a type with its lexicographic order. -/
def Lex (α : Type _) :=
  α
#align lex Lex
-/

#print toLex /-
/-- `to_lex` is the identity function to the `lex` of a type.  -/
@[match_pattern]
def toLex : α ≃ Lex α :=
  Equiv.refl _
#align to_lex toLex
-/

#print ofLex /-
/-- `of_lex` is the identity function from the `lex` of a type.  -/
@[match_pattern]
def ofLex : Lex α ≃ α :=
  Equiv.refl _
#align of_lex ofLex
-/

#print toLex_symm_eq /-
@[simp]
theorem toLex_symm_eq : (@toLex α).symm = ofLex :=
  rfl
#align to_lex_symm_eq toLex_symm_eq
-/

#print ofLex_symm_eq /-
@[simp]
theorem ofLex_symm_eq : (@ofLex α).symm = toLex :=
  rfl
#align of_lex_symm_eq ofLex_symm_eq
-/

#print toLex_ofLex /-
@[simp]
theorem toLex_ofLex (a : Lex α) : toLex (ofLex a) = a :=
  rfl
#align to_lex_of_lex toLex_ofLex
-/

#print ofLex_toLex /-
@[simp]
theorem ofLex_toLex (a : α) : ofLex (toLex a) = a :=
  rfl
#align of_lex_to_lex ofLex_toLex
-/

#print toLex_inj /-
@[simp]
theorem toLex_inj {a b : α} : toLex a = toLex b ↔ a = b :=
  Iff.rfl
#align to_lex_inj toLex_inj
-/

#print ofLex_inj /-
@[simp]
theorem ofLex_inj {a b : Lex α} : ofLex a = ofLex b ↔ a = b :=
  Iff.rfl
#align of_lex_inj ofLex_inj
-/

#print Lex.rec /-
/-- A recursor for `lex`. Use as `induction x using lex.rec`. -/
protected def Lex.rec {β : Lex α → Sort _} (h : ∀ a, β (toLex a)) : ∀ a, β a := fun a => h (ofLex a)
#align lex.rec Lex.rec
-/

