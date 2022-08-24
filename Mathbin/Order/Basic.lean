/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import Mathbin.Data.Prod.Basic
import Mathbin.Data.Subtype

/-!
# Basic definitions about `≤` and `<`

This file proves basic results about orders, provides extensive dot notation, defines useful order
classes and allows to transfer order instances.

## Type synonyms

* `order_dual α` : A type synonym reversing the meaning of all inequalities, with notation `αᵒᵈ`.
* `as_linear_order α`: A type synonym to promote `partial_order α` to `linear_order α` using
  `is_total α (≤)`.

### Transfering orders

- `order.preimage`, `preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `partial_order.lift`, `linear_order.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra class

* `has_sup`: type class for the `⊔` notation
* `has_inf`: type class for the `⊓` notation
* `has_compl`: type class for the `ᶜ` notation
* `densely_ordered`: An order with no gap, i.e. for any two elements `a < b` there exists `c` such
  that `a < c < b`.

## Notes

`≤` and `<` are highly favored over `≥` and `>` in mathlib. The reason is that we can formulate all
lemmas using `≤`/`<`, and `rw` has trouble unifying `≤` and `≥`. Hence choosing one direction spares
us useless duplication. This is enforced by a linter. See Note [nolint_ge] for more infos.

Dot notation is particularly useful on `≤` (`has_le.le`) and `<` (`has_lt.lt`). To that end, we
provide many aliases to dot notation-less lemmas. For example, `le_trans` is aliased with
`has_le.le.trans` and can be used to construct `hab.trans hbc : a ≤ c` when `hab : a ≤ b`,
`hbc : b ≤ c`, `lt_of_le_of_lt` is aliased as `has_le.le.trans_lt` and can be used to construct
`hab.trans hbc : a < c` when `hab : a ≤ b`, `hbc : b < c`.

## TODO

- expand module docs
- automatic construction of dual definitions / theorems

## Tags

preorder, order, partial order, poset, linear order, chain
-/


open Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

section Preorderₓ

variable [Preorderₓ α] {a b c : α}

theorem le_trans'ₓ : b ≤ c → a ≤ b → a ≤ c :=
  flip le_transₓ

theorem lt_trans'ₓ : b < c → a < b → a < c :=
  flip lt_transₓ

theorem lt_of_le_of_lt'ₓ : b ≤ c → a < b → a < c :=
  flip lt_of_lt_of_leₓ

theorem lt_of_lt_of_le'ₓ : b < c → a ≤ b → a < c :=
  flip lt_of_le_of_ltₓ

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] {a b : α}

theorem ge_antisymmₓ : a ≤ b → b ≤ a → b = a :=
  flip le_antisymmₓ

theorem lt_of_le_of_ne'ₓ : a ≤ b → b ≠ a → a < b := fun h₁ h₂ => lt_of_le_of_neₓ h₁ h₂.symm

theorem Ne.lt_of_le : a ≠ b → a ≤ b → a < b :=
  flip lt_of_le_of_neₓ

theorem Ne.lt_of_le' : b ≠ a → a ≤ b → a < b :=
  flip lt_of_le_of_ne'ₓ

end PartialOrderₓ

attribute [simp] le_reflₓ

attribute [ext] LE

alias le_transₓ ← LE.le.transₓ

alias le_trans'ₓ ← LE.le.trans'ₓ

alias lt_of_le_of_ltₓ ← LE.le.trans_ltₓ

alias lt_of_le_of_lt'ₓ ← LE.le.trans_lt'ₓ

alias le_antisymmₓ ← LE.le.antisymmₓ

alias ge_antisymmₓ ← LE.le.antisymm'ₓ

alias lt_of_le_of_neₓ ← LE.le.lt_of_neₓ

alias lt_of_le_of_ne'ₓ ← LE.le.lt_of_ne'ₓ

alias lt_of_le_not_leₓ ← LE.le.lt_of_not_leₓ

alias lt_or_eq_of_leₓ ← LE.le.lt_or_eqₓ

alias Decidable.lt_or_eq_of_leₓ ← LE.le.lt_or_eq_decₓ

alias le_of_ltₓ ← LT.lt.leₓ

alias lt_transₓ ← LT.lt.transₓ

alias lt_trans'ₓ ← LT.lt.trans'ₓ

alias lt_of_lt_of_leₓ ← LT.lt.trans_leₓ

alias lt_of_lt_of_le'ₓ ← LT.lt.trans_le'ₓ

alias ne_of_ltₓ ← LT.lt.neₓ

alias lt_asymmₓ ← LT.lt.asymmₓ LT.lt.not_ltₓ

alias le_of_eqₓ ← Eq.leₓ

attribute [nolint decidable_classical] LE.le.lt_or_eq_decₓ

section

variable [Preorderₓ α] {a b c : α}

/-- A version of `le_refl` where the argument is implicit -/
theorem le_rflₓ : a ≤ a :=
  le_reflₓ a

@[simp]
theorem lt_self_iff_falseₓ (x : α) : x < x ↔ False :=
  ⟨lt_irreflₓ x, False.elim⟩

theorem le_of_le_of_eqₓ (hab : a ≤ b) (hbc : b = c) : a ≤ c :=
  hab.trans hbc.le

theorem le_of_eq_of_leₓ (hab : a = b) (hbc : b ≤ c) : a ≤ c :=
  hab.le.trans hbc

theorem lt_of_lt_of_eqₓ (hab : a < b) (hbc : b = c) : a < c :=
  hab.trans_le hbc.le

theorem lt_of_eq_of_ltₓ (hab : a = b) (hbc : b < c) : a < c :=
  hab.le.trans_lt hbc

theorem le_of_le_of_eq'ₓ : b ≤ c → a = b → a ≤ c :=
  flip le_of_eq_of_leₓ

theorem le_of_eq_of_le'ₓ : b = c → a ≤ b → a ≤ c :=
  flip le_of_le_of_eqₓ

theorem lt_of_lt_of_eq'ₓ : b < c → a = b → a < c :=
  flip lt_of_eq_of_ltₓ

theorem lt_of_eq_of_lt'ₓ : b = c → a < b → a < c :=
  flip lt_of_lt_of_eqₓ

alias le_of_le_of_eqₓ ← LE.le.trans_eqₓ

alias le_of_le_of_eq'ₓ ← LE.le.trans_eq'ₓ

alias lt_of_lt_of_eqₓ ← LT.lt.trans_eqₓ

alias lt_of_lt_of_eq'ₓ ← LT.lt.trans_eq'ₓ

alias le_of_eq_of_leₓ ← Eq.trans_leₓ

alias le_of_eq_of_le'ₓ ← Eq.trans_geₓ

alias lt_of_eq_of_ltₓ ← Eq.trans_ltₓ

alias lt_of_eq_of_lt'ₓ ← Eq.trans_gtₓ

end

namespace Eq

variable [Preorderₓ α] {x y z : α}

/-- If `x = y` then `y ≤ x`. Note: this lemma uses `y ≤ x` instead of `x ≥ y`, because `le` is used
almost exclusively in mathlib. -/
protected theorem geₓ (h : x = y) : y ≤ x :=
  h.symm.le

theorem not_ltₓ (h : x = y) : ¬x < y := fun h' => h'.Ne h

theorem not_gtₓ (h : x = y) : ¬y < x :=
  h.symm.not_lt

end Eq

namespace LE.le

-- see Note [nolint_ge]
@[nolint ge_or_gt]
protected theorem ge [LE α] {x y : α} (h : x ≤ y) : y ≥ x :=
  h

theorem lt_iff_neₓ [PartialOrderₓ α] {x y : α} (h : x ≤ y) : x < y ↔ x ≠ y :=
  ⟨fun h => h.Ne, h.lt_of_ne⟩

theorem le_iff_eqₓ [PartialOrderₓ α] {x y : α} (h : x ≤ y) : y ≤ x ↔ y = x :=
  ⟨fun h' => h'.antisymm h, Eq.leₓ⟩

theorem lt_or_leₓ [LinearOrderₓ α] {a b : α} (h : a ≤ b) (c : α) : a < c ∨ c ≤ b :=
  ((lt_or_geₓ a c).imp id) fun hc => le_transₓ hc h

theorem le_or_ltₓ [LinearOrderₓ α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c < b :=
  ((le_or_gtₓ a c).imp id) fun hc => lt_of_lt_of_leₓ hc h

theorem le_or_leₓ [LinearOrderₓ α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c ≤ b :=
  (h.le_or_lt c).elim Or.inl fun h => Or.inr <| le_of_ltₓ h

end LE.le

namespace LT.lt

-- see Note [nolint_ge]
@[nolint ge_or_gt]
protected theorem gt [LT α] {x y : α} (h : x < y) : y > x :=
  h

protected theorem falseₓ [Preorderₓ α] {x : α} : x < x → False :=
  lt_irreflₓ x

theorem ne'ₓ [Preorderₓ α] {x y : α} (h : x < y) : y ≠ x :=
  h.Ne.symm

theorem lt_or_ltₓ [LinearOrderₓ α] {x y : α} (h : x < y) (z : α) : x < z ∨ z < y :=
  (lt_or_geₓ z y).elim Or.inr fun hz => Or.inl <| h.trans_le hz

end LT.lt

-- see Note [nolint_ge]
@[nolint ge_or_gt]
protected theorem Ge.le [LE α] {x y : α} (h : x ≥ y) : y ≤ x :=
  h

-- see Note [nolint_ge]
@[nolint ge_or_gt]
protected theorem Gt.lt [LT α] {x y : α} (h : x > y) : y < x :=
  h

-- see Note [nolint_ge]
@[nolint ge_or_gt]
theorem ge_of_eqₓ [Preorderₓ α] {a b : α} (h : a = b) : a ≥ b :=
  h.Ge

-- see Note [nolint_ge]
@[simp, nolint ge_or_gt]
theorem ge_iff_leₓ [LE α] {a b : α} : a ≥ b ↔ b ≤ a :=
  Iff.rfl

-- see Note [nolint_ge]
@[simp, nolint ge_or_gt]
theorem gt_iff_ltₓ [LT α] {a b : α} : a > b ↔ b < a :=
  Iff.rfl

theorem not_le_of_ltₓ [Preorderₓ α] {a b : α} (h : a < b) : ¬b ≤ a :=
  (le_not_le_of_ltₓ h).right

alias not_le_of_ltₓ ← LT.lt.not_leₓ

theorem not_lt_of_leₓ [Preorderₓ α] {a b : α} (h : a ≤ b) : ¬b < a := fun hba => hba.not_le h

alias not_lt_of_leₓ ← LE.le.not_ltₓ

theorem ne_of_not_le [Preorderₓ α] {a b : α} (h : ¬a ≤ b) : a ≠ b := fun hab => h (le_of_eqₓ hab)

-- See Note [decidable namespace]
protected theorem Decidable.le_iff_eq_or_ltₓ [PartialOrderₓ α] [@DecidableRel α (· ≤ ·)] {a b : α} :
    a ≤ b ↔ a = b ∨ a < b :=
  Decidable.le_iff_lt_or_eqₓ.trans Or.comm

theorem le_iff_eq_or_ltₓ [PartialOrderₓ α] {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
  le_iff_lt_or_eqₓ.trans Or.comm

theorem lt_iff_le_and_neₓ [PartialOrderₓ α] {a b : α} : a < b ↔ a ≤ b ∧ a ≠ b :=
  ⟨fun h => ⟨le_of_ltₓ h, ne_of_ltₓ h⟩, fun ⟨h1, h2⟩ => h1.lt_of_ne h2⟩

-- See Note [decidable namespace]
protected theorem Decidable.eq_iff_le_not_ltₓ [PartialOrderₓ α] [@DecidableRel α (· ≤ ·)] {a b : α} :
    a = b ↔ a ≤ b ∧ ¬a < b :=
  ⟨fun h => ⟨h.le, h ▸ lt_irreflₓ _⟩, fun ⟨h₁, h₂⟩ =>
    h₁.antisymm <| Decidable.by_contradiction fun h₃ => h₂ (h₁.lt_of_not_le h₃)⟩

theorem eq_iff_le_not_ltₓ [PartialOrderₓ α] {a b : α} : a = b ↔ a ≤ b ∧ ¬a < b :=
  haveI := Classical.dec
  Decidable.eq_iff_le_not_ltₓ

theorem eq_or_lt_of_leₓ [PartialOrderₓ α] {a b : α} (h : a ≤ b) : a = b ∨ a < b :=
  h.lt_or_eq.symm

theorem eq_or_gt_of_le [PartialOrderₓ α] {a b : α} (h : a ≤ b) : b = a ∨ a < b :=
  h.lt_or_eq.symm.imp Eq.symm id

alias Decidable.eq_or_lt_of_leₓ ← LE.le.eq_or_lt_decₓ

alias eq_or_lt_of_leₓ ← LE.le.eq_or_ltₓ

alias eq_or_gt_of_le ← LE.le.eq_or_gt

attribute [nolint decidable_classical] LE.le.eq_or_lt_decₓ

theorem eq_of_le_of_not_lt [PartialOrderₓ α] {a b : α} (hab : a ≤ b) (hba : ¬a < b) : a = b :=
  hab.eq_or_lt.resolve_right hba

theorem eq_of_ge_of_not_gt [PartialOrderₓ α] {a b : α} (hab : a ≤ b) (hba : ¬a < b) : b = a :=
  (hab.eq_or_lt.resolve_right hba).symm

alias eq_of_le_of_not_lt ← LE.le.eq_of_not_lt

alias eq_of_ge_of_not_gt ← LE.le.eq_of_not_gt

theorem Ne.le_iff_lt [PartialOrderₓ α] {a b : α} (h : a ≠ b) : a ≤ b ↔ a < b :=
  ⟨fun h' => lt_of_le_of_neₓ h' h, fun h => h.le⟩

theorem Ne.not_le_or_not_le [PartialOrderₓ α] {a b : α} (h : a ≠ b) : ¬a ≤ b ∨ ¬b ≤ a :=
  not_and_distrib.1 <| le_antisymm_iffₓ.Not.1 h

-- See Note [decidable namespace]
protected theorem Decidable.ne_iff_lt_iff_leₓ [PartialOrderₓ α] [DecidableEq α] {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
  ⟨fun h => Decidable.byCases le_of_eqₓ (le_of_ltₓ ∘ h.mp), fun h => ⟨lt_of_le_of_neₓ h, ne_of_ltₓ⟩⟩

@[simp]
theorem ne_iff_lt_iff_leₓ [PartialOrderₓ α] {a b : α} : (a ≠ b ↔ a < b) ↔ a ≤ b :=
  haveI := Classical.dec
  Decidable.ne_iff_lt_iff_leₓ

theorem lt_of_not_le [LinearOrderₓ α] {a b : α} (h : ¬b ≤ a) : a < b :=
  ((le_totalₓ _ _).resolve_right h).lt_of_not_le h

theorem lt_iff_not_le [LinearOrderₓ α] {x y : α} : x < y ↔ ¬y ≤ x :=
  ⟨not_le_of_ltₓ, lt_of_not_le⟩

theorem Ne.lt_or_lt [LinearOrderₓ α] {x y : α} (h : x ≠ y) : x < y ∨ y < x :=
  lt_or_gt_of_neₓ h

/-- A version of `ne_iff_lt_or_gt` with LHS and RHS reversed. -/
@[simp]
theorem lt_or_lt_iff_ne [LinearOrderₓ α] {x y : α} : x < y ∨ y < x ↔ x ≠ y :=
  ne_iff_lt_or_gtₓ.symm

theorem not_lt_iff_eq_or_ltₓ [LinearOrderₓ α] {a b : α} : ¬a < b ↔ a = b ∨ b < a :=
  not_ltₓ.trans <| Decidable.le_iff_eq_or_ltₓ.trans <| or_congr eq_comm Iff.rfl

theorem exists_ge_of_linearₓ [LinearOrderₓ α] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
  match le_totalₓ a b with
  | Or.inl h => ⟨_, h, le_rflₓ⟩
  | Or.inr h => ⟨_, le_rflₓ, h⟩

theorem lt_imp_lt_of_le_imp_leₓ {β} [LinearOrderₓ α] [Preorderₓ β] {a b : α} {c d : β} (H : a ≤ b → c ≤ d) (h : d < c) :
    b < a :=
  lt_of_not_le fun h' => (H h').not_lt h

theorem le_imp_le_iff_lt_imp_ltₓ {β} [LinearOrderₓ α] [LinearOrderₓ β] {a b : α} {c d : β} :
    a ≤ b → c ≤ d ↔ d < c → b < a :=
  ⟨lt_imp_lt_of_le_imp_leₓ, le_imp_le_of_lt_imp_ltₓ⟩

theorem lt_iff_lt_of_le_iff_le'ₓ {β} [Preorderₓ α] [Preorderₓ β] {a b : α} {c d : β} (H : a ≤ b ↔ c ≤ d)
    (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
  lt_iff_le_not_leₓ.trans <| (and_congr H' (not_congr H)).trans lt_iff_le_not_leₓ.symm

theorem lt_iff_lt_of_le_iff_leₓ {β} [LinearOrderₓ α] [LinearOrderₓ β] {a b : α} {c d : β} (H : a ≤ b ↔ c ≤ d) :
    b < a ↔ d < c :=
  not_leₓ.symm.trans <| (not_congr H).trans <| not_leₓ

theorem le_iff_le_iff_lt_iff_ltₓ {β} [LinearOrderₓ α] [LinearOrderₓ β] {a b : α} {c d : β} :
    (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
  ⟨lt_iff_lt_of_le_iff_leₓ, fun H => not_ltₓ.symm.trans <| (not_congr H).trans <| not_ltₓ⟩

theorem eq_of_forall_le_iffₓ [PartialOrderₓ α] {a b : α} (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
  ((H _).1 le_rflₓ).antisymm ((H _).2 le_rflₓ)

theorem le_of_forall_leₓ [Preorderₓ α] {a b : α} (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b :=
  H _ le_rflₓ

theorem le_of_forall_le'ₓ [Preorderₓ α] {a b : α} (H : ∀ c, a ≤ c → b ≤ c) : b ≤ a :=
  H _ le_rflₓ

theorem le_of_forall_ltₓ [LinearOrderₓ α] {a b : α} (H : ∀ c, c < a → c < b) : a ≤ b :=
  le_of_not_ltₓ fun h => lt_irreflₓ _ (H _ h)

theorem forall_lt_iff_leₓ [LinearOrderₓ α] {a b : α} : (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
  ⟨le_of_forall_ltₓ, fun h c hca => lt_of_lt_of_leₓ hca h⟩

theorem le_of_forall_lt'ₓ [LinearOrderₓ α] {a b : α} (H : ∀ c, a < c → b < c) : b ≤ a :=
  le_of_not_ltₓ fun h => lt_irreflₓ _ (H _ h)

theorem forall_lt_iff_le'ₓ [LinearOrderₓ α] {a b : α} : (∀ ⦃c⦄, a < c → b < c) ↔ b ≤ a :=
  ⟨le_of_forall_lt'ₓ, fun h c hac => lt_of_le_of_ltₓ h hac⟩

theorem eq_of_forall_ge_iffₓ [PartialOrderₓ α] {a b : α} (H : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
  ((H _).2 le_rflₓ).antisymm ((H _).1 le_rflₓ)

/-- A symmetric relation implies two values are equal, when it implies they're less-equal.  -/
theorem rel_imp_eq_of_rel_imp_le [PartialOrderₓ β] (r : α → α → Prop) [IsSymm α r] {f : α → β}
    (h : ∀ a b, r a b → f a ≤ f b) {a b : α} : r a b → f a = f b := fun hab =>
  le_antisymmₓ (h a b hab) (h b a <| symm hab)

/-- monotonicity of `≤` with respect to `→` -/
theorem le_implies_le_of_le_of_leₓ {a b c d : α} [Preorderₓ α] (hca : c ≤ a) (hbd : b ≤ d) : a ≤ b → c ≤ d := fun hab =>
  (hca.trans hab).trans hbd

@[ext]
theorem Preorderₓ.to_has_le_injective {α : Type _} : Function.Injective (@Preorderₓ.toHasLe α) := fun A B h => by
  cases A
  cases B
  injection h with h_le
  have : A_lt = B_lt := by
    funext a b
    dsimp' [(· ≤ ·)]  at A_lt_iff_le_not_le B_lt_iff_le_not_le h_le
    simp [A_lt_iff_le_not_le, B_lt_iff_le_not_le, h_le]
  congr

@[ext]
theorem PartialOrderₓ.to_preorder_injective {α : Type _} : Function.Injective (@PartialOrderₓ.toPreorder α) :=
  fun A B h => by
  cases A
  cases B
  injection h
  congr

@[ext]
theorem LinearOrderₓ.to_partial_order_injective {α : Type _} : Function.Injective (@LinearOrderₓ.toPartialOrder α) := by
  intro A B h
  cases A
  cases B
  injection h
  obtain rfl : A_le = B_le := ‹_›
  obtain rfl : A_lt = B_lt := ‹_›
  obtain rfl : A_decidable_le = B_decidable_le := Subsingleton.elimₓ _ _
  obtain rfl : A_max = B_max := A_max_def.trans B_max_def.symm
  obtain rfl : A_min = B_min := A_min_def.trans B_min_def.symm
  congr

theorem Preorderₓ.ext {α} {A B : Preorderₓ α}
    (H :
      ∀ x y : α,
        (haveI := A
          x ≤ y) ↔
          x ≤ y) :
    A = B := by
  ext x y
  exact H x y

theorem PartialOrderₓ.ext {α} {A B : PartialOrderₓ α}
    (H :
      ∀ x y : α,
        (haveI := A
          x ≤ y) ↔
          x ≤ y) :
    A = B := by
  ext x y
  exact H x y

theorem LinearOrderₓ.ext {α} {A B : LinearOrderₓ α}
    (H :
      ∀ x y : α,
        (haveI := A
          x ≤ y) ↔
          x ≤ y) :
    A = B := by
  ext x y
  exact H x y

/-- Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `rel_embedding` (assuming `f`
is injective). -/
@[simp]
def Order.Preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) : Prop :=
  s (f x) (f y)

-- mathport name: «expr ⁻¹'o »
infixl:80 " ⁻¹'o " => Order.Preimage

/-- The preimage of a decidable order is decidable. -/
instance Order.Preimage.decidable {α β} (f : α → β) (s : β → β → Prop) [H : DecidableRel s] : DecidableRel (f ⁻¹'o s) :=
  fun x y => H _ _

/-! ### Order dual -/


/-- Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>`. `αᵒᵈ` is
notation for `order_dual α`. -/
def OrderDual (α : Type _) : Type _ :=
  α

-- mathport name: «expr ᵒᵈ»
notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

instance (α : Type _) [h : Nonempty α] : Nonempty αᵒᵈ :=
  h

instance (α : Type _) [h : Subsingleton α] : Subsingleton αᵒᵈ :=
  h

instance (α : Type _) [LE α] : LE αᵒᵈ :=
  ⟨fun x y : α => y ≤ x⟩

instance (α : Type _) [LT α] : LT αᵒᵈ :=
  ⟨fun x y : α => y < x⟩

instance (α : Type _) [Preorderₓ α] : Preorderₓ αᵒᵈ :=
  { OrderDual.hasLe α, OrderDual.hasLt α with le_refl := le_reflₓ, le_trans := fun a b c hab hbc => hbc.trans hab,
    lt_iff_le_not_le := fun _ _ => lt_iff_le_not_leₓ }

instance (α : Type _) [PartialOrderₓ α] : PartialOrderₓ αᵒᵈ :=
  { OrderDual.preorder α with le_antisymm := fun a b hab hba => @le_antisymmₓ α _ a b hba hab }

instance (α : Type _) [LinearOrderₓ α] : LinearOrderₓ αᵒᵈ :=
  { OrderDual.partialOrder α with le_total := fun a b : α => le_totalₓ b a,
    decidableLe := (inferInstance : DecidableRel fun a b : α => b ≤ a),
    decidableLt := (inferInstance : DecidableRel fun a b : α => b < a), min := @max α _, max := @min α _,
    min_def := @LinearOrderₓ.max_def α _, max_def := @LinearOrderₓ.min_def α _ }

instance : ∀ [Inhabited α], Inhabited αᵒᵈ :=
  id

theorem preorder.dual_dual (α : Type _) [H : Preorderₓ α] : OrderDual.preorder αᵒᵈ = H :=
  Preorderₓ.ext fun _ _ => Iff.rfl

theorem partialOrder.dual_dual (α : Type _) [H : PartialOrderₓ α] : OrderDual.partialOrder αᵒᵈ = H :=
  PartialOrderₓ.ext fun _ _ => Iff.rfl

theorem linearOrder.dual_dual (α : Type _) [H : LinearOrderₓ α] : OrderDual.linearOrder αᵒᵈ = H :=
  LinearOrderₓ.ext fun _ _ => Iff.rfl

end OrderDual

/-! ### `has_compl` -/


-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Command.lean:96:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Set / lattice complement -/
@[«./././Mathport/Syntax/Translate/Command.lean:96:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg»]
class HasCompl (α : Type _) where
  compl : α → α

export HasCompl (compl)

-- ./././Mathport/Syntax/Translate/Command.lean:405:9: unsupported: advanced prec syntax «expr + »(max, 1)
-- mathport name: «expr ᶜ»
postfix:999 "ᶜ" => compl

instance Prop.hasCompl : HasCompl Prop :=
  ⟨Not⟩

instance Pi.hasCompl {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] : HasCompl (∀ i, α i) :=
  ⟨fun x i => x iᶜ⟩

theorem Pi.compl_defₓ {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] (x : ∀ i, α i) : xᶜ = fun i => x iᶜ :=
  rfl

@[simp]
theorem Pi.compl_applyₓ {ι : Type u} {α : ι → Type v} [∀ i, HasCompl (α i)] (x : ∀ i, α i) (i : ι) : (xᶜ) i = x iᶜ :=
  rfl

instance IsIrrefl.compl (r) [IsIrrefl α r] : IsRefl α (rᶜ) :=
  ⟨@irrefl α r _⟩

instance IsRefl.compl (r) [IsRefl α r] : IsIrrefl α (rᶜ) :=
  ⟨fun a => not_not_intro (refl a)⟩

/-! ### Order instances on the function space -/


instance Pi.hasLe {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] : LE (∀ i, α i) where le := fun x y => ∀ i, x i ≤ y i

theorem Pi.le_def {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] {x y : ∀ i, α i} : x ≤ y ↔ ∀ i, x i ≤ y i :=
  Iff.rfl

instance Pi.preorderₓ {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] : Preorderₓ (∀ i, α i) :=
  { Pi.hasLe with le_refl := fun a i => le_reflₓ (a i), le_trans := fun a b c h₁ h₂ i => le_transₓ (h₁ i) (h₂ i) }

theorem Pi.lt_defₓ {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] {x y : ∀ i, α i} :
    x < y ↔ x ≤ y ∧ ∃ i, x i < y i := by
  simp (config := { contextual := true })[lt_iff_le_not_leₓ, Pi.le_def]

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (j «expr ≠ » i)
theorem le_update_iffₓ {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] [DecidableEq ι] {x y : ∀ i, α i} {i : ι}
    {a : α i} : x ≤ Function.update y i a ↔ x i ≤ a ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z => x j ≤ z

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (j «expr ≠ » i)
theorem update_le_iffₓ {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] [DecidableEq ι] {x y : ∀ i, α i} {i : ι}
    {a : α i} : Function.update x i a ≤ y ↔ a ≤ y i ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j :=
  Function.forall_update_iff _ fun j z => z ≤ y j

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (j «expr ≠ » i)
theorem update_le_update_iffₓ {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] [DecidableEq ι] {x y : ∀ i, α i}
    {i : ι} {a b : α i} : Function.update x i a ≤ Function.update y i b ↔ a ≤ b ∧ ∀ (j) (_ : j ≠ i), x j ≤ y j := by
  simp (config := { contextual := true })[update_le_iffₓ]

instance Pi.partialOrder {ι : Type u} {α : ι → Type v} [∀ i, PartialOrderₓ (α i)] : PartialOrderₓ (∀ i, α i) :=
  { Pi.preorderₓ with le_antisymm := fun f g h1 h2 => funext fun b => (h1 b).antisymm (h2 b) }

instance Pi.hasSdiff {ι : Type u} {α : ι → Type v} [∀ i, Sdiff (α i)] : Sdiff (∀ i, α i) :=
  ⟨fun x y i => x i \ y i⟩

theorem Pi.sdiff_def {ι : Type u} {α : ι → Type v} [∀ i, Sdiff (α i)] (x y : ∀ i, α i) : x \ y = fun i => x i \ y i :=
  rfl

@[simp]
theorem Pi.sdiff_apply {ι : Type u} {α : ι → Type v} [∀ i, Sdiff (α i)] (x y : ∀ i, α i) (i : ι) :
    (x \ y) i = x i \ y i :=
  rfl

/-! ### `min`/`max` recursors -/


section MinMaxRec

variable [LinearOrderₓ α] {p : α → Prop} {x y : α}

theorem min_rec (hx : x ≤ y → p x) (hy : y ≤ x → p y) : p (min x y) :=
  (le_totalₓ x y).rec (fun h => (min_eq_leftₓ h).symm.subst (hx h)) fun h => (min_eq_rightₓ h).symm.subst (hy h)

theorem max_rec (hx : y ≤ x → p x) (hy : x ≤ y → p y) : p (max x y) :=
  @min_rec αᵒᵈ _ _ _ _ hx hy

theorem min_rec' (p : α → Prop) (hx : p x) (hy : p y) : p (min x y) :=
  min_rec (fun _ => hx) fun _ => hy

theorem max_rec' (p : α → Prop) (hx : p x) (hy : p y) : p (max x y) :=
  max_rec (fun _ => hx) fun _ => hy

end MinMaxRec

/-! ### `has_sup` and `has_inf` -/


-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Command.lean:96:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Typeclass for the `⊔` (`\lub`) notation -/
@[«./././Mathport/Syntax/Translate/Command.lean:96:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg»]
class HasSup (α : Type u) where
  sup : α → α → α

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Command.lean:96:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Typeclass for the `⊓` (`\glb`) notation -/
@[«./././Mathport/Syntax/Translate/Command.lean:96:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg»]
class HasInf (α : Type u) where
  inf : α → α → α

-- mathport name: «expr ⊔ »
infixl:68 "⊔" => HasSup.sup

-- mathport name: «expr ⊓ »
infixl:69 "⊓" => HasInf.inf

/-! ### Lifts of order instances -/


/-- Transfer a `preorder` on `β` to a `preorder` on `α` using a function `f : α → β`.
See note [reducible non-instances]. -/
@[reducible]
def Preorderₓ.lift {α β} [Preorderₓ β] (f : α → β) : Preorderₓ α where
  le := fun x y => f x ≤ f y
  le_refl := fun a => le_rflₓ
  le_trans := fun a b c => le_transₓ
  lt := fun x y => f x < f y
  lt_iff_le_not_le := fun a b => lt_iff_le_not_leₓ

/-- Transfer a `partial_order` on `β` to a `partial_order` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible]
def PartialOrderₓ.lift {α β} [PartialOrderₓ β] (f : α → β) (inj : Injective f) : PartialOrderₓ α :=
  { Preorderₓ.lift f with le_antisymm := fun a b h₁ h₂ => inj (h₁.antisymm h₂) }

/-- Transfer a `linear_order` on `β` to a `linear_order` on `α` using an injective
function `f : α → β`. This version takes `[has_sup α]` and `[has_inf α]` as arguments, then uses
them for `max` and `min` fields. See `linear_order.lift'` for a version that autogenerates `min` and
`max` fields. See note [reducible non-instances]. -/
@[reducible]
def LinearOrderₓ.lift {α β} [LinearOrderₓ β] [HasSup α] [HasInf α] (f : α → β) (inj : Injective f)
    (hsup : ∀ x y, f (x⊔y) = max (f x) (f y)) (hinf : ∀ x y, f (x⊓y) = min (f x) (f y)) : LinearOrderₓ α :=
  { PartialOrderₓ.lift f inj with le_total := fun x y => le_totalₓ (f x) (f y),
    decidableLe := fun x y => (inferInstance : Decidable (f x ≤ f y)),
    decidableLt := fun x y => (inferInstance : Decidable (f x < f y)),
    DecidableEq := fun x y => decidableOfIff (f x = f y) inj.eq_iff, min := (·⊓·), max := (·⊔·),
    min_def := by
      ext x y
      apply inj
      rw [hinf, min_def, minDefault, apply_ite f]
      rfl,
    max_def := by
      ext x y
      apply inj
      rw [hsup, max_def, maxDefault, apply_ite f]
      rfl }

/-- Transfer a `linear_order` on `β` to a `linear_order` on `α` using an injective
function `f : α → β`. This version autogenerates `min` and `max` fields. See `linear_order.lift`
for a version that takes `[has_sup α]` and `[has_inf α]`, then uses them as `max` and `min`.
See note [reducible non-instances]. -/
@[reducible]
def LinearOrderₓ.lift' {α β} [LinearOrderₓ β] (f : α → β) (inj : Injective f) : LinearOrderₓ α :=
  @LinearOrderₓ.lift α β _ ⟨fun x y => if f y ≤ f x then x else y⟩ ⟨fun x y => if f x ≤ f y then x else y⟩ f inj
    (fun x y => (apply_ite f _ _ _).trans (max_def _ _).symm) fun x y => (apply_ite f _ _ _).trans (min_def _ _).symm

/-! ### Subtype of an order -/


namespace Subtype

instance [LE α] {p : α → Prop} : LE (Subtype p) :=
  ⟨fun x y => (x : α) ≤ y⟩

instance [LT α] {p : α → Prop} : LT (Subtype p) :=
  ⟨fun x y => (x : α) < y⟩

@[simp]
theorem mk_le_mk [LE α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} : (⟨x, hx⟩ : Subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
  Iff.rfl

@[simp]
theorem mk_lt_mk [LT α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} : (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_le_coe [LE α] {p : α → Prop} {x y : Subtype p} : (x : α) ≤ y ↔ x ≤ y :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_lt_coe [LT α] {p : α → Prop} {x y : Subtype p} : (x : α) < y ↔ x < y :=
  Iff.rfl

instance [Preorderₓ α] (p : α → Prop) : Preorderₓ (Subtype p) :=
  Preorderₓ.lift (coe : Subtype p → α)

instance partialOrder [PartialOrderₓ α] (p : α → Prop) : PartialOrderₓ (Subtype p) :=
  PartialOrderₓ.lift coe Subtype.coe_injective

instance decidableLe [Preorderₓ α] [h : @DecidableRel α (· ≤ ·)] {p : α → Prop} : @DecidableRel (Subtype p) (· ≤ ·) :=
  fun a b => h a b

instance decidableLt [Preorderₓ α] [h : @DecidableRel α (· < ·)] {p : α → Prop} : @DecidableRel (Subtype p) (· < ·) :=
  fun a b => h a b

/-- A subtype of a linear order is a linear order. We explicitly give the proofs of decidable
equality and decidable order in order to ensure the decidability instances are all definitionally
equal. -/
instance [LinearOrderₓ α] (p : α → Prop) : LinearOrderₓ (Subtype p) :=
  @LinearOrderₓ.lift (Subtype p) _ _ ⟨fun x y => ⟨max x y, max_rec' _ x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' _ x.2 y.2⟩⟩ coe Subtype.coe_injective (fun _ _ => rfl) fun _ _ => rfl

end Subtype

/-!
### Pointwise order on `α × β`

The lexicographic order is defined in `data.prod.lex`, and the instances are available via the
type synonym `α ×ₗ β = α × β`.
-/


namespace Prod

instance (α : Type u) (β : Type v) [LE α] [LE β] : LE (α × β) :=
  ⟨fun p q => p.1 ≤ q.1 ∧ p.2 ≤ q.2⟩

theorem le_def [LE α] [LE β] {x y : α × β} : x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 :=
  Iff.rfl

@[simp]
theorem mk_le_mk [LE α] [LE β] {x₁ x₂ : α} {y₁ y₂ : β} : (x₁, y₁) ≤ (x₂, y₂) ↔ x₁ ≤ x₂ ∧ y₁ ≤ y₂ :=
  Iff.rfl

@[simp]
theorem swap_le_swap [LE α] [LE β] {x y : α × β} : x.swap ≤ y.swap ↔ x ≤ y :=
  and_comm _ _

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

instance (α : Type u) (β : Type v) [Preorderₓ α] [Preorderₓ β] : Preorderₓ (α × β) :=
  { Prod.hasLe α β with le_refl := fun ⟨a, b⟩ => ⟨le_reflₓ a, le_reflₓ b⟩,
    le_trans := fun ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ => ⟨le_transₓ hac hce, le_transₓ hbd hdf⟩ }

@[simp]
theorem swap_lt_swapₓ : x.swap < y.swap ↔ x < y :=
  and_congr swap_le_swap (not_congr swap_le_swap)

theorem mk_le_mk_iff_leftₓ : (a₁, b) ≤ (a₂, b) ↔ a₁ ≤ a₂ :=
  and_iff_left le_rflₓ

theorem mk_le_mk_iff_rightₓ : (a, b₁) ≤ (a, b₂) ↔ b₁ ≤ b₂ :=
  and_iff_right le_rflₓ

theorem mk_lt_mk_iff_leftₓ : (a₁, b) < (a₂, b) ↔ a₁ < a₂ :=
  lt_iff_lt_of_le_iff_le'ₓ mk_le_mk_iff_leftₓ mk_le_mk_iff_leftₓ

theorem mk_lt_mk_iff_rightₓ : (a, b₁) < (a, b₂) ↔ b₁ < b₂ :=
  lt_iff_lt_of_le_iff_le'ₓ mk_le_mk_iff_rightₓ mk_le_mk_iff_rightₓ

theorem lt_iffₓ : x < y ↔ x.1 < y.1 ∧ x.2 ≤ y.2 ∨ x.1 ≤ y.1 ∧ x.2 < y.2 := by
  refine' ⟨fun h => _, _⟩
  · by_cases' h₁ : y.1 ≤ x.1
    · exact Or.inr ⟨h.1.1, h.1.2.lt_of_not_le fun h₂ => h.2 ⟨h₁, h₂⟩⟩
      
    · exact Or.inl ⟨h.1.1.lt_of_not_le h₁, h.1.2⟩
      
    
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨h₁.le, h₂⟩, fun h => h₁.not_le h.1⟩
      
    · exact ⟨⟨h₁, h₂.le⟩, fun h => h₂.not_le h.2⟩
      
    

@[simp]
theorem mk_lt_mkₓ : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ ≤ b₂ ∨ a₁ ≤ a₂ ∧ b₁ < b₂ :=
  lt_iff

end Preorderₓ

/-- The pointwise partial order on a product.
    (The lexicographic ordering is defined in order/lexicographic.lean, and the instances are
    available via the type synonym `α ×ₗ β = α × β`.) -/
instance (α : Type u) (β : Type v) [PartialOrderₓ α] [PartialOrderₓ β] : PartialOrderₓ (α × β) :=
  { Prod.preorder α β with
    le_antisymm := fun ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ ⟨hca, hdb⟩ => Prod.extₓ (hac.antisymm hca) (hbd.antisymm hdb) }

end Prod

/-! ### Additional order classes -/


/-- An order is dense if there is an element between any pair of distinct elements. -/
class DenselyOrdered (α : Type u) [LT α] : Prop where
  dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂

theorem exists_between [LT α] [DenselyOrdered α] : ∀ {a₁ a₂ : α}, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
  DenselyOrdered.dense

instance OrderDual.densely_ordered (α : Type u) [LT α] [DenselyOrdered α] : DenselyOrdered αᵒᵈ :=
  ⟨fun a₁ a₂ ha => (@exists_between α _ _ _ _ ha).imp fun a => And.symm⟩

theorem le_of_forall_le_of_denseₓ [LinearOrderₓ α] [DenselyOrdered α] {a₁ a₂ : α} (h : ∀ a, a₂ < a → a₁ ≤ a) :
    a₁ ≤ a₂ :=
  le_of_not_gtₓ fun ha =>
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irreflₓ a <| lt_of_lt_of_leₓ ‹a < a₁› (h _ ‹a₂ < a›)

theorem eq_of_le_of_forall_le_of_denseₓ [LinearOrderₓ α] [DenselyOrdered α] {a₁ a₂ : α} (h₁ : a₂ ≤ a₁)
    (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
  le_antisymmₓ (le_of_forall_le_of_denseₓ h₂) h₁

theorem le_of_forall_ge_of_denseₓ [LinearOrderₓ α] [DenselyOrdered α] {a₁ a₂ : α} (h : ∀ a₃ < a₁, a₃ ≤ a₂) : a₁ ≤ a₂ :=
  le_of_not_gtₓ fun ha =>
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
    lt_irreflₓ a <| lt_of_le_of_ltₓ (h _ ‹a < a₁›) ‹a₂ < a›

theorem eq_of_le_of_forall_ge_of_denseₓ [LinearOrderₓ α] [DenselyOrdered α] {a₁ a₂ : α} (h₁ : a₂ ≤ a₁)
    (h₂ : ∀ a₃ < a₁, a₃ ≤ a₂) : a₁ = a₂ :=
  (le_of_forall_ge_of_denseₓ h₂).antisymm h₁

theorem dense_or_discreteₓ [LinearOrderₓ α] (a₁ a₂ : α) :
    (∃ a, a₁ < a ∧ a < a₂) ∨ (∀ a, a₁ < a → a₂ ≤ a) ∧ ∀ a < a₂, a ≤ a₁ :=
  or_iff_not_imp_left.2 fun h =>
    ⟨fun a ha₁ => le_of_not_gtₓ fun ha₂ => h ⟨a, ha₁, ha₂⟩, fun a ha₂ => le_of_not_gtₓ fun ha₁ => h ⟨a, ha₁, ha₂⟩⟩

namespace PUnit

variable (a b : PUnit.{u + 1})

instance : LinearOrderₓ PUnit := by
  refine_struct
      { le := fun _ _ => True, lt := fun _ _ => False, max := fun _ _ => star, min := fun _ _ => star,
        DecidableEq := PUnit.decidableEq, decidableLe := fun _ _ => Decidable.true,
        decidableLt := fun _ _ => Decidable.false } <;>
    intros <;>
      first |
        trivial|
        simp only [eq_iff_true_of_subsingleton, not_true, and_falseₓ]|
        exact Or.inl trivialₓ

theorem max_eq : max a b = star :=
  rfl

theorem min_eq : min a b = star :=
  rfl

@[simp]
protected theorem le : a ≤ b :=
  trivialₓ

@[simp]
theorem not_lt : ¬a < b :=
  not_false

instance : DenselyOrdered PUnit :=
  ⟨fun _ _ => False.elim⟩

end PUnit

section Prop

-- ./././Mathport/Syntax/Translate/Expr.lean:219:4: warning: unsupported binary notation `«->»
/-- Propositions form a complete boolean algebra, where the `≤` relation is given by implication. -/
instance Prop.hasLe : LE Prop :=
  ⟨(«->» · ·)⟩

-- ./././Mathport/Syntax/Translate/Expr.lean:219:4: warning: unsupported binary notation `«->»
@[simp]
theorem le_Prop_eq : ((· ≤ ·) : Prop → Prop → Prop) = («->» · ·) :=
  rfl

theorem subrelation_iff_le {r s : α → α → Prop} : Subrelation r s ↔ r ≤ s :=
  Iff.rfl

instance Prop.partialOrder : PartialOrderₓ Prop :=
  { Prop.hasLe with le_refl := fun _ => id, le_trans := fun a b c f g => g ∘ f,
    le_antisymm := fun a b Hab Hba => propext ⟨Hab, Hba⟩ }

end Prop

variable {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Linear order from a total partial order -/


/-- Type synonym to create an instance of `linear_order` from a `partial_order` and
`is_total α (≤)` -/
def AsLinearOrder (α : Type u) :=
  α

instance {α} [Inhabited α] : Inhabited (AsLinearOrder α) :=
  ⟨(default : α)⟩

noncomputable instance AsLinearOrder.linearOrder {α} [PartialOrderₓ α] [IsTotal α (· ≤ ·)] :
    LinearOrderₓ (AsLinearOrder α) :=
  { (_ : PartialOrderₓ α) with le_total := @total_of α (· ≤ ·) _, decidableLe := Classical.decRel _ }

