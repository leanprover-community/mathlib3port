/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
import Mathbin.Order.Compare
import Mathbin.Order.Max
import Mathbin.Order.RelClasses

/-!
# Monotonicity

This file defines (strictly) monotone/antitone functions. Contrary to standard mathematical usage,
"monotone"/"mono" here means "increasing", not "increasing or decreasing". We use "antitone"/"anti"
to mean "decreasing".

## Definitions

* `monotone f`: A function `f` between two preorders is monotone if `a ≤ b` implies `f a ≤ f b`.
* `antitone f`: A function `f` between two preorders is antitone if `a ≤ b` implies `f b ≤ f a`.
* `monotone_on f s`: Same as `monotone f`, but for all `a, b ∈ s`.
* `antitone_on f s`: Same as `antitone f`, but for all `a, b ∈ s`.
* `strict_mono f` : A function `f` between two preorders is strictly monotone if `a < b` implies
  `f a < f b`.
* `strict_anti f` : A function `f` between two preorders is strictly antitone if `a < b` implies
  `f b < f a`.
* `strict_mono_on f s`: Same as `strict_mono f`, but for all `a, b ∈ s`.
* `strict_anti_on f s`: Same as `strict_anti f`, but for all `a, b ∈ s`.

## Main theorems

* `monotone_nat_of_le_succ`, `monotone_int_of_le_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n ≤ f (n + 1)` for all `n`, then `f` is monotone.
* `antitone_nat_of_succ_le`, `antitone_int_of_succ_le`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) ≤ f n` for all `n`, then `f` is antitone.
* `strict_mono_nat_of_lt_succ`, `strict_mono_int_of_lt_succ`: If `f : ℕ → α` or `f : ℤ → α` and
  `f n < f (n + 1)` for all `n`, then `f` is strictly monotone.
* `strict_anti_nat_of_succ_lt`, `strict_anti_int_of_succ_lt`: If `f : ℕ → α` or `f : ℤ → α` and
  `f (n + 1) < f n` for all `n`, then `f` is strictly antitone.

## Implementation notes

Some of these definitions used to only require `has_le α` or `has_lt α`. The advantage of this is
unclear and it led to slight elaboration issues. Now, everything requires `preorder α` and seems to
work fine. Related Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Order.20diamond/near/254353352.

## TODO

The above theorems are also true in `ℕ+`, `fin n`... To make that work, we need `succ_order α`
and `succ_archimedean α`.

## Tags

monotone, strictly monotone, antitone, strictly antitone, increasing, strictly increasing,
decreasing, strictly decreasing
-/


open Function OrderDual

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type _} {r : α → α → Prop}

section MonotoneDef

variable [Preorderₓ α] [Preorderₓ β]

/-- A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`. -/
def Monotoneₓ (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

/-- A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`. -/
def Antitoneₓ (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

/-- A function `f` is monotone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f a ≤ f b`. -/
def MonotoneOnₓ (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a ≤ b → f a ≤ f b

/-- A function `f` is antitone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f b ≤ f a`. -/
def AntitoneOnₓ (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a ≤ b → f b ≤ f a

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def StrictMonoₓ (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b

/-- A function `f` is strictly antitone if `a < b` implies `f b < f a`. -/
def StrictAntiₓ (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f b < f a

/-- A function `f` is strictly monotone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f a < f b`. -/
def StrictMonoOnₓ (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f a < f b

/-- A function `f` is strictly antitone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f b < f a`. -/
def StrictAntiOnₓ (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f b < f a

end MonotoneDef

/-! ### Monotonicity on the dual order

Strictly, many of the `*_on.dual` lemmas in this section should use `of_dual ⁻¹' s` instead of `s`,
but right now this is not possible as `set.preimage` is not defined yet, and importing it creates
an import cycle.

Often, you should not need the rewriting lemmas. Instead, you probably want to add `.dual`,
`.dual_left` or `.dual_right` to your `monotone`/`antitone` hypothesis.
-/


section OrderDual

variable [Preorderₓ α] [Preorderₓ β] {f : α → β} {s : Set α}

@[simp]
theorem monotone_comp_of_dual_iff : Monotoneₓ (f ∘ of_dual) ↔ Antitoneₓ f :=
  forall_swap

@[simp]
theorem antitone_comp_of_dual_iff : Antitoneₓ (f ∘ of_dual) ↔ Monotoneₓ f :=
  forall_swap

@[simp]
theorem monotone_to_dual_comp_iff : Monotoneₓ (to_dual ∘ f) ↔ Antitoneₓ f :=
  Iff.rfl

@[simp]
theorem antitone_to_dual_comp_iff : Antitoneₓ (to_dual ∘ f) ↔ Monotoneₓ f :=
  Iff.rfl

@[simp]
theorem monotone_on_comp_of_dual_iff : MonotoneOnₓ (f ∘ of_dual) s ↔ AntitoneOnₓ f s :=
  forall₂_swap

@[simp]
theorem antitone_on_comp_of_dual_iff : AntitoneOnₓ (f ∘ of_dual) s ↔ MonotoneOnₓ f s :=
  forall₂_swap

@[simp]
theorem monotone_on_to_dual_comp_iff : MonotoneOnₓ (to_dual ∘ f) s ↔ AntitoneOnₓ f s :=
  Iff.rfl

@[simp]
theorem antitone_on_to_dual_comp_iff : AntitoneOnₓ (to_dual ∘ f) s ↔ MonotoneOnₓ f s :=
  Iff.rfl

@[simp]
theorem strict_mono_comp_of_dual_iff : StrictMonoₓ (f ∘ of_dual) ↔ StrictAntiₓ f :=
  forall_swap

@[simp]
theorem strict_anti_comp_of_dual_iff : StrictAntiₓ (f ∘ of_dual) ↔ StrictMonoₓ f :=
  forall_swap

@[simp]
theorem strict_mono_to_dual_comp_iff : StrictMonoₓ (to_dual ∘ f) ↔ StrictAntiₓ f :=
  Iff.rfl

@[simp]
theorem strict_anti_to_dual_comp_iff : StrictAntiₓ (to_dual ∘ f) ↔ StrictMonoₓ f :=
  Iff.rfl

@[simp]
theorem strict_mono_on_comp_of_dual_iff : StrictMonoOnₓ (f ∘ of_dual) s ↔ StrictAntiOnₓ f s :=
  forall₂_swap

@[simp]
theorem strict_anti_on_comp_of_dual_iff : StrictAntiOnₓ (f ∘ of_dual) s ↔ StrictMonoOnₓ f s :=
  forall₂_swap

@[simp]
theorem strict_mono_on_to_dual_comp_iff : StrictMonoOnₓ (to_dual ∘ f) s ↔ StrictAntiOnₓ f s :=
  Iff.rfl

@[simp]
theorem strict_anti_on_to_dual_comp_iff : StrictAntiOnₓ (to_dual ∘ f) s ↔ StrictMonoOnₓ f s :=
  Iff.rfl

protected theorem Monotoneₓ.dual (hf : Monotoneₓ f) : Monotoneₓ (to_dual ∘ f ∘ of_dual) :=
  swap hf

protected theorem Antitoneₓ.dual (hf : Antitoneₓ f) : Antitoneₓ (to_dual ∘ f ∘ of_dual) :=
  swap hf

protected theorem MonotoneOnₓ.dual (hf : MonotoneOnₓ f s) : MonotoneOnₓ (to_dual ∘ f ∘ of_dual) s :=
  swap₂ hf

protected theorem AntitoneOnₓ.dual (hf : AntitoneOnₓ f s) : AntitoneOnₓ (to_dual ∘ f ∘ of_dual) s :=
  swap₂ hf

protected theorem StrictMonoₓ.dual (hf : StrictMonoₓ f) : StrictMonoₓ (to_dual ∘ f ∘ of_dual) :=
  swap hf

protected theorem StrictAntiₓ.dual (hf : StrictAntiₓ f) : StrictAntiₓ (to_dual ∘ f ∘ of_dual) :=
  swap hf

protected theorem StrictMonoOnₓ.dual (hf : StrictMonoOnₓ f s) : StrictMonoOnₓ (to_dual ∘ f ∘ of_dual) s :=
  swap₂ hf

protected theorem StrictAntiOnₓ.dual (hf : StrictAntiOnₓ f s) : StrictAntiOnₓ (to_dual ∘ f ∘ of_dual) s :=
  swap₂ hf

alias antitone_comp_of_dual_iff ↔ _ Monotoneₓ.dual_left

alias monotone_comp_of_dual_iff ↔ _ Antitoneₓ.dual_left

alias antitone_to_dual_comp_iff ↔ _ Monotoneₓ.dual_right

alias monotone_to_dual_comp_iff ↔ _ Antitoneₓ.dual_right

alias antitone_on_comp_of_dual_iff ↔ _ MonotoneOnₓ.dual_left

alias monotone_on_comp_of_dual_iff ↔ _ AntitoneOnₓ.dual_left

alias antitone_on_to_dual_comp_iff ↔ _ MonotoneOnₓ.dual_right

alias monotone_on_to_dual_comp_iff ↔ _ AntitoneOnₓ.dual_right

alias strict_anti_comp_of_dual_iff ↔ _ StrictMonoₓ.dual_left

alias strict_mono_comp_of_dual_iff ↔ _ StrictAntiₓ.dual_left

alias strict_anti_to_dual_comp_iff ↔ _ StrictMonoₓ.dual_right

alias strict_mono_to_dual_comp_iff ↔ _ StrictAntiₓ.dual_right

alias strict_anti_on_comp_of_dual_iff ↔ _ StrictMonoOnₓ.dual_left

alias strict_mono_on_comp_of_dual_iff ↔ _ StrictAntiOnₓ.dual_left

alias strict_anti_on_to_dual_comp_iff ↔ _ StrictMonoOnₓ.dual_right

alias strict_mono_on_to_dual_comp_iff ↔ _ StrictAntiOnₓ.dual_right

end OrderDual

/-! ### Monotonicity in function spaces -/


section Preorderₓ

variable [Preorderₓ α]

theorem Monotoneₓ.comp_le_comp_left [Preorderₓ β] {f : β → α} {g h : γ → β} (hf : Monotoneₓ f) (le_gh : g ≤ h) :
    LE.le.{max w u} (f ∘ g) (f ∘ h) := fun x => hf (le_gh x)

variable [Preorderₓ γ]

theorem monotone_lamₓ {f : α → β → γ} (hf : ∀ b, Monotoneₓ fun a => f a b) : Monotoneₓ f := fun a a' h b => hf b h

theorem monotone_appₓ (f : β → α → γ) (b : β) (hf : Monotoneₓ fun a b => f b a) : Monotoneₓ (f b) := fun a a' h =>
  hf h b

theorem antitone_lamₓ {f : α → β → γ} (hf : ∀ b, Antitoneₓ fun a => f a b) : Antitoneₓ f := fun a a' h b => hf b h

theorem antitone_appₓ (f : β → α → γ) (b : β) (hf : Antitoneₓ fun a b => f b a) : Antitoneₓ (f b) := fun a a' h =>
  hf h b

end Preorderₓ

theorem Function.monotone_evalₓ {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] (i : ι) :
    Monotoneₓ (Function.eval i : (∀ i, α i) → α i) := fun f g H => H i

/-! ### Monotonicity hierarchy -/


section Preorderₓ

variable [Preorderₓ α]

section Preorderₓ

variable [Preorderₓ β] {f : α → β} {a b : α}

/-!
These four lemmas are there to strip off the semi-implicit arguments `⦃a b : α⦄`. This is useful
when you do not want to apply a `monotone` assumption (i.e. your goal is `a ≤ b → f a ≤ f b`).
However if you find yourself writing `hf.imp h`, then you should have written `hf h` instead.
-/


theorem Monotoneₓ.imp (hf : Monotoneₓ f) (h : a ≤ b) : f a ≤ f b :=
  hf h

theorem Antitoneₓ.imp (hf : Antitoneₓ f) (h : a ≤ b) : f b ≤ f a :=
  hf h

theorem StrictMonoₓ.imp (hf : StrictMonoₓ f) (h : a < b) : f a < f b :=
  hf h

theorem StrictAntiₓ.imp (hf : StrictAntiₓ f) (h : a < b) : f b < f a :=
  hf h

protected theorem Monotoneₓ.monotone_on (hf : Monotoneₓ f) (s : Set α) : MonotoneOnₓ f s := fun a _ b _ => hf.imp

protected theorem Antitoneₓ.antitone_on (hf : Antitoneₓ f) (s : Set α) : AntitoneOnₓ f s := fun a _ b _ => hf.imp

theorem monotone_on_univ : MonotoneOnₓ f Set.Univ ↔ Monotoneₓ f :=
  ⟨fun h a b => h trivialₓ trivialₓ, fun h => h.MonotoneOn _⟩

theorem antitone_on_univ : AntitoneOnₓ f Set.Univ ↔ Antitoneₓ f :=
  ⟨fun h a b => h trivialₓ trivialₓ, fun h => h.AntitoneOn _⟩

protected theorem StrictMonoₓ.strict_mono_on (hf : StrictMonoₓ f) (s : Set α) : StrictMonoOnₓ f s := fun a _ b _ =>
  hf.imp

protected theorem StrictAntiₓ.strict_anti_on (hf : StrictAntiₓ f) (s : Set α) : StrictAntiOnₓ f s := fun a _ b _ =>
  hf.imp

theorem strict_mono_on_univ : StrictMonoOnₓ f Set.Univ ↔ StrictMonoₓ f :=
  ⟨fun h a b => h trivialₓ trivialₓ, fun h => h.StrictMonoOn _⟩

theorem strict_anti_on_univ : StrictAntiOnₓ f Set.Univ ↔ StrictAntiₓ f :=
  ⟨fun h a b => h trivialₓ trivialₓ, fun h => h.StrictAntiOn _⟩

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ β] {f : α → β}

theorem Monotoneₓ.strict_mono_of_injective (h₁ : Monotoneₓ f) (h₂ : Injective f) : StrictMonoₓ f := fun a b h =>
  (h₁ h.le).lt_of_ne fun H => h.Ne <| h₂ H

theorem Antitoneₓ.strict_anti_of_injective (h₁ : Antitoneₓ f) (h₂ : Injective f) : StrictAntiₓ f := fun a b h =>
  (h₁ h.le).lt_of_ne fun H => h.Ne <| h₂ H.symm

end PartialOrderₓ

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [Preorderₓ β] {f : α → β} {s : Set α}

theorem monotone_iff_forall_ltₓ : Monotoneₓ f ↔ ∀ ⦃a b⦄, a < b → f a ≤ f b :=
  forall₂_congrₓ fun a b => ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) hf⟩

theorem antitone_iff_forall_ltₓ : Antitoneₓ f ↔ ∀ ⦃a b⦄, a < b → f b ≤ f a :=
  forall₂_congrₓ fun a b => ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_arg _ H).Ge) hf⟩

theorem monotone_on_iff_forall_ltₓ : MonotoneOnₓ f s ↔ ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f a ≤ f b :=
  ⟨fun hf a ha b hb h => hf ha hb h.le, fun hf a ha b hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).le) (hf ha hb)⟩

theorem antitone_on_iff_forall_ltₓ : AntitoneOnₓ f s ↔ ∀ ⦃a⦄ (ha : a ∈ s) ⦃b⦄ (hb : b ∈ s), a < b → f b ≤ f a :=
  ⟨fun hf a ha b hb h => hf ha hb h.le, fun hf a ha b hb h => h.eq_or_lt.elim (fun H => (congr_arg _ H).Ge) (hf ha hb)⟩

-- `preorder α` isn't strong enough: if the preorder on `α` is an equivalence relation,
-- then `strict_mono f` is vacuously true.
protected theorem StrictMonoOnₓ.monotone_on (hf : StrictMonoOnₓ f s) : MonotoneOnₓ f s :=
  monotone_on_iff_forall_ltₓ.2 fun a ha b hb h => (hf ha hb h).le

protected theorem StrictAntiOnₓ.antitone_on (hf : StrictAntiOnₓ f s) : AntitoneOnₓ f s :=
  antitone_on_iff_forall_ltₓ.2 fun a ha b hb h => (hf ha hb h).le

protected theorem StrictMonoₓ.monotone (hf : StrictMonoₓ f) : Monotoneₓ f :=
  monotone_iff_forall_ltₓ.2 fun a b h => (hf h).le

protected theorem StrictAntiₓ.antitone (hf : StrictAntiₓ f) : Antitoneₓ f :=
  antitone_iff_forall_ltₓ.2 fun a b h => (hf h).le

end PartialOrderₓ

/-! ### Monotonicity from and to subsingletons -/


namespace Subsingleton

variable [Preorderₓ α] [Preorderₓ β]

protected theorem monotoneₓ [Subsingleton α] (f : α → β) : Monotoneₓ f := fun a b _ =>
  (congr_arg _ <| Subsingleton.elim _ _).le

protected theorem antitoneₓ [Subsingleton α] (f : α → β) : Antitoneₓ f := fun a b _ =>
  (congr_arg _ <| Subsingleton.elim _ _).le

theorem monotone'ₓ [Subsingleton β] (f : α → β) : Monotoneₓ f := fun a b _ => (Subsingleton.elim _ _).le

theorem antitone'ₓ [Subsingleton β] (f : α → β) : Antitoneₓ f := fun a b _ => (Subsingleton.elim _ _).le

protected theorem strict_monoₓ [Subsingleton α] (f : α → β) : StrictMonoₓ f := fun a b h =>
  (h.Ne <| Subsingleton.elim _ _).elim

protected theorem strict_antiₓ [Subsingleton α] (f : α → β) : StrictAntiₓ f := fun a b h =>
  (h.Ne <| Subsingleton.elim _ _).elim

end Subsingleton

/-! ### Miscellaneous monotonicity results -/


theorem monotone_idₓ [Preorderₓ α] : Monotoneₓ (id : α → α) := fun a b => id

theorem monotone_on_idₓ [Preorderₓ α] {s : Set α} : MonotoneOnₓ id s := fun a ha b hb => id

theorem strict_mono_idₓ [Preorderₓ α] : StrictMonoₓ (id : α → α) := fun a b => id

theorem strict_mono_on_idₓ [Preorderₓ α] {s : Set α} : StrictMonoOnₓ id s := fun a ha b hb => id

theorem monotone_constₓ [Preorderₓ α] [Preorderₓ β] {c : β} : Monotoneₓ fun a : α => c := fun a b _ => le_rflₓ

theorem monotone_on_constₓ [Preorderₓ α] [Preorderₓ β] {c : β} {s : Set α} : MonotoneOnₓ (fun a : α => c) s :=
  fun a _ b _ _ => le_rflₓ

theorem antitone_constₓ [Preorderₓ α] [Preorderₓ β] {c : β} : Antitoneₓ fun a : α => c := fun a b _ => le_reflₓ c

theorem antitone_on_constₓ [Preorderₓ α] [Preorderₓ β] {c : β} {s : Set α} : AntitoneOnₓ (fun a : α => c) s :=
  fun a _ b _ _ => le_rflₓ

theorem strict_mono_of_le_iff_le [Preorderₓ α] [Preorderₓ β] {f : α → β} (h : ∀ x y, x ≤ y ↔ f x ≤ f y) :
    StrictMonoₓ f := fun a b => (lt_iff_lt_of_le_iff_le'ₓ (h _ _) (h _ _)).1

theorem strict_anti_of_le_iff_le [Preorderₓ α] [Preorderₓ β] {f : α → β} (h : ∀ x y, x ≤ y ↔ f y ≤ f x) :
    StrictAntiₓ f := fun a b => (lt_iff_lt_of_le_iff_le'ₓ (h _ _) (h _ _)).1

theorem injective_of_lt_imp_ne [LinearOrderₓ α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) : Injective f := by
  intro x y hxy
  contrapose hxy
  cases' Ne.lt_or_lt hxy with hxy hxy
  exacts[h _ _ hxy, (h _ _ hxy).symm]

theorem injective_of_le_imp_leₓ [PartialOrderₓ α] [Preorderₓ β] (f : α → β) (h : ∀ {x y}, f x ≤ f y → x ≤ y) :
    Injective f := fun x y hxy => (h hxy.le).antisymm (h hxy.Ge)

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] {f g : α → β} {a : α}

theorem StrictMonoₓ.is_max_of_apply (hf : StrictMonoₓ f) (ha : IsMax (f a)) : IsMax a :=
  of_not_not fun h =>
    let ⟨b, hb⟩ := not_is_max_iff.1 h
    (hf hb).not_is_max ha

theorem StrictMonoₓ.is_min_of_apply (hf : StrictMonoₓ f) (ha : IsMin (f a)) : IsMin a :=
  of_not_not fun h =>
    let ⟨b, hb⟩ := not_is_min_iff.1 h
    (hf hb).not_is_min ha

theorem StrictAntiₓ.is_max_of_apply (hf : StrictAntiₓ f) (ha : IsMin (f a)) : IsMax a :=
  of_not_not fun h =>
    let ⟨b, hb⟩ := not_is_max_iff.1 h
    (hf hb).not_is_min ha

theorem StrictAntiₓ.is_min_of_apply (hf : StrictAntiₓ f) (ha : IsMax (f a)) : IsMin a :=
  of_not_not fun h =>
    let ⟨b, hb⟩ := not_is_min_iff.1 h
    (hf hb).not_is_max ha

protected theorem StrictMonoₓ.ite' (hf : StrictMonoₓ f) (hg : StrictMonoₓ g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → f x < g y) :
    StrictMonoₓ fun x => if p x then f x else g x := by
  intro x y h
  by_cases hy:p y
  · have hx : p x := hp h hy
    simpa [hx, hy] using hf h
    
  by_cases hx:p x
  · simpa [hx, hy] using hfg hx hy h
    
  · simpa [hx, hy] using hg h
    

protected theorem StrictMonoₓ.ite (hf : StrictMonoₓ f) (hg : StrictMonoₓ g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, f x ≤ g x) : StrictMonoₓ fun x => if p x then f x else g x :=
  (hf.ite' hg hp) fun x y hx hy h => (hf h).trans_le (hfg y)

protected theorem StrictAntiₓ.ite' (hf : StrictAntiₓ f) (hg : StrictAntiₓ g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → g y < f x) :
    StrictAntiₓ fun x => if p x then f x else g x :=
  (StrictMonoₓ.ite' hf.dual_right hg.dual_right hp hfg).dual_right

protected theorem StrictAntiₓ.ite (hf : StrictAntiₓ f) (hg : StrictAntiₓ g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, g x ≤ f x) : StrictAntiₓ fun x => if p x then f x else g x :=
  (hf.ite' hg hp) fun x y hx hy h => (hfg y).trans_lt (hf h)

end Preorderₓ

/-! ### Monotonicity under composition -/


section Composition

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β} {s : Set α}

protected theorem Monotoneₓ.comp (hg : Monotoneₓ g) (hf : Monotoneₓ f) : Monotoneₓ (g ∘ f) := fun a b h => hg (hf h)

theorem Monotoneₓ.comp_antitone (hg : Monotoneₓ g) (hf : Antitoneₓ f) : Antitoneₓ (g ∘ f) := fun a b h => hg (hf h)

protected theorem Antitoneₓ.comp (hg : Antitoneₓ g) (hf : Antitoneₓ f) : Monotoneₓ (g ∘ f) := fun a b h => hg (hf h)

theorem Antitoneₓ.comp_monotone (hg : Antitoneₓ g) (hf : Monotoneₓ f) : Antitoneₓ (g ∘ f) := fun a b h => hg (hf h)

protected theorem Monotoneₓ.iterate {f : α → α} (hf : Monotoneₓ f) (n : ℕ) : Monotoneₓ (f^[n]) :=
  Nat.recOn n monotone_idₓ fun n h => h.comp hf

protected theorem Monotoneₓ.comp_monotone_on (hg : Monotoneₓ g) (hf : MonotoneOnₓ f s) : MonotoneOnₓ (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

theorem Monotoneₓ.comp_antitone_on (hg : Monotoneₓ g) (hf : AntitoneOnₓ f s) : AntitoneOnₓ (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

protected theorem Antitoneₓ.comp_antitone_on (hg : Antitoneₓ g) (hf : AntitoneOnₓ f s) : MonotoneOnₓ (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

theorem Antitoneₓ.comp_monotone_on (hg : Antitoneₓ g) (hf : MonotoneOnₓ f s) : AntitoneOnₓ (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

protected theorem StrictMonoₓ.comp (hg : StrictMonoₓ g) (hf : StrictMonoₓ f) : StrictMonoₓ (g ∘ f) := fun a b h =>
  hg (hf h)

theorem StrictMonoₓ.comp_strict_anti (hg : StrictMonoₓ g) (hf : StrictAntiₓ f) : StrictAntiₓ (g ∘ f) := fun a b h =>
  hg (hf h)

protected theorem StrictAntiₓ.comp (hg : StrictAntiₓ g) (hf : StrictAntiₓ f) : StrictMonoₓ (g ∘ f) := fun a b h =>
  hg (hf h)

theorem StrictAntiₓ.comp_strict_mono (hg : StrictAntiₓ g) (hf : StrictMonoₓ f) : StrictAntiₓ (g ∘ f) := fun a b h =>
  hg (hf h)

protected theorem StrictMonoₓ.iterate {f : α → α} (hf : StrictMonoₓ f) (n : ℕ) : StrictMonoₓ (f^[n]) :=
  Nat.recOn n strict_mono_idₓ fun n h => h.comp hf

protected theorem StrictMonoₓ.comp_strict_mono_on (hg : StrictMonoₓ g) (hf : StrictMonoOnₓ f s) :
    StrictMonoOnₓ (g ∘ f) s := fun a ha b hb h => hg (hf ha hb h)

theorem StrictMonoₓ.comp_strict_anti_on (hg : StrictMonoₓ g) (hf : StrictAntiOnₓ f s) : StrictAntiOnₓ (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

protected theorem StrictAntiₓ.comp_strict_anti_on (hg : StrictAntiₓ g) (hf : StrictAntiOnₓ f s) :
    StrictMonoOnₓ (g ∘ f) s := fun a ha b hb h => hg (hf ha hb h)

theorem StrictAntiₓ.comp_strict_mono_on (hg : StrictAntiₓ g) (hf : StrictMonoOnₓ f s) : StrictAntiOnₓ (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

end Composition

namespace List

section Fold

theorem foldl_monotone [Preorderₓ α] {f : α → β → α} (H : ∀ b, Monotoneₓ fun a => f a b) (l : List β) :
    Monotoneₓ fun a => l.foldl f a :=
  List.recOn l (fun _ _ => id) fun i l hl _ _ h => hl (H _ h)

theorem foldr_monotone [Preorderₓ β] {f : α → β → β} (H : ∀ a, Monotoneₓ (f a)) (l : List α) :
    Monotoneₓ fun b => l.foldr f b := fun _ _ h => List.recOn l h fun i l hl => H i hl

theorem foldl_strict_mono [Preorderₓ α] {f : α → β → α} (H : ∀ b, StrictMonoₓ fun a => f a b) (l : List β) :
    StrictMonoₓ fun a => l.foldl f a :=
  List.recOn l (fun _ _ => id) fun i l hl _ _ h => hl (H _ h)

theorem foldr_strict_mono [Preorderₓ β] {f : α → β → β} (H : ∀ a, StrictMonoₓ (f a)) (l : List α) :
    StrictMonoₓ fun b => l.foldr f b := fun _ _ h => List.recOn l h fun i l hl => H i hl

end Fold

end List

/-! ### Monotonicity in linear orders  -/


section LinearOrderₓ

variable [LinearOrderₓ α]

section Preorderₓ

variable [Preorderₓ β] {f : α → β} {s : Set α}

open Ordering

theorem Monotoneₓ.reflect_lt (hf : Monotoneₓ f) {a b : α} (h : f a < f b) : a < b :=
  lt_of_not_geₓ fun h' => h.not_le (hf h')

theorem Antitoneₓ.reflect_lt (hf : Antitoneₓ f) {a b : α} (h : f a < f b) : b < a :=
  lt_of_not_geₓ fun h' => h.not_le (hf h')

theorem MonotoneOnₓ.reflect_lt (hf : MonotoneOnₓ f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : f a < f b) : a < b :=
  lt_of_not_geₓ fun h' => h.not_le <| hf hb ha h'

theorem AntitoneOnₓ.reflect_lt (hf : AntitoneOnₓ f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : f a < f b) : b < a :=
  lt_of_not_geₓ fun h' => h.not_le <| hf ha hb h'

theorem StrictMonoOnₓ.le_iff_le (hf : StrictMonoOnₓ f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a ≤ f b ↔ a ≤ b :=
  ⟨fun h => le_of_not_gtₓ fun h' => (hf hb ha h').not_le h, fun h =>
    h.lt_or_eq_dec.elim (fun h' => (hf ha hb h').le) fun h' => h' ▸ le_rflₓ⟩

theorem StrictAntiOnₓ.le_iff_le (hf : StrictAntiOnₓ f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a ≤ f b ↔ b ≤ a :=
  hf.dual_right.le_iff_le hb ha

theorem StrictMonoOnₓ.lt_iff_lt (hf : StrictMonoOnₓ f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ a < b := by
  rw [lt_iff_le_not_leₓ, lt_iff_le_not_leₓ, hf.le_iff_le ha hb, hf.le_iff_le hb ha]

theorem StrictAntiOnₓ.lt_iff_lt (hf : StrictAntiOnₓ f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ b < a :=
  hf.dual_right.lt_iff_lt hb ha

theorem StrictMonoₓ.le_iff_le (hf : StrictMonoₓ f) {a b : α} : f a ≤ f b ↔ a ≤ b :=
  (hf.StrictMonoOn Set.Univ).le_iff_le trivialₓ trivialₓ

theorem StrictAntiₓ.le_iff_le (hf : StrictAntiₓ f) {a b : α} : f a ≤ f b ↔ b ≤ a :=
  (hf.StrictAntiOn Set.Univ).le_iff_le trivialₓ trivialₓ

theorem StrictMonoₓ.lt_iff_lt (hf : StrictMonoₓ f) {a b : α} : f a < f b ↔ a < b :=
  (hf.StrictMonoOn Set.Univ).lt_iff_lt trivialₓ trivialₓ

theorem StrictAntiₓ.lt_iff_lt (hf : StrictAntiₓ f) {a b : α} : f a < f b ↔ b < a :=
  (hf.StrictAntiOn Set.Univ).lt_iff_lt trivialₓ trivialₓ

protected theorem StrictMonoOnₓ.compares (hf : StrictMonoOnₓ f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    ∀ {o : Ordering}, o.Compares (f a) (f b) ↔ o.Compares a b
  | Ordering.lt => hf.lt_iff_lt ha hb
  | Ordering.eq => ⟨fun h => ((hf.le_iff_le ha hb).1 h.le).antisymm ((hf.le_iff_le hb ha).1 h.symm.le), congr_arg _⟩
  | Ordering.gt => hf.lt_iff_lt hb ha

protected theorem StrictAntiOnₓ.compares (hf : StrictAntiOnₓ f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares b a :=
  to_dual_compares_to_dual.trans <| hf.dual_right.Compares hb ha

protected theorem StrictMonoₓ.compares (hf : StrictMonoₓ f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares a b :=
  (hf.StrictMonoOn Set.Univ).Compares trivialₓ trivialₓ

protected theorem StrictAntiₓ.compares (hf : StrictAntiₓ f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares b a :=
  (hf.StrictAntiOn Set.Univ).Compares trivialₓ trivialₓ

theorem StrictMonoₓ.injective (hf : StrictMonoₓ f) : Injective f := fun x y h =>
  show Compares Eq x y from hf.Compares.1 h

theorem StrictAntiₓ.injective (hf : StrictAntiₓ f) : Injective f := fun x y h =>
  show Compares Eq x y from hf.Compares.1 h.symm

theorem StrictMonoₓ.maximal_of_maximal_image (hf : StrictMonoₓ f) {a} (hmax : ∀ p, p ≤ f a) (x : α) : x ≤ a :=
  hf.le_iff_le.mp (hmax (f x))

theorem StrictMonoₓ.minimal_of_minimal_image (hf : StrictMonoₓ f) {a} (hmin : ∀ p, f a ≤ p) (x : α) : a ≤ x :=
  hf.le_iff_le.mp (hmin (f x))

theorem StrictAntiₓ.minimal_of_maximal_image (hf : StrictAntiₓ f) {a} (hmax : ∀ p, p ≤ f a) (x : α) : a ≤ x :=
  hf.le_iff_le.mp (hmax (f x))

theorem StrictAntiₓ.maximal_of_minimal_image (hf : StrictAntiₓ f) {a} (hmin : ∀ p, f a ≤ p) (x : α) : x ≤ a :=
  hf.le_iff_le.mp (hmin (f x))

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ β] {f : α → β}

theorem Monotoneₓ.strict_mono_iff_injective (hf : Monotoneₓ f) : StrictMonoₓ f ↔ Injective f :=
  ⟨fun h => h.Injective, hf.strict_mono_of_injective⟩

theorem Antitoneₓ.strict_anti_iff_injective (hf : Antitoneₓ f) : StrictAntiₓ f ↔ Injective f :=
  ⟨fun h => h.Injective, hf.strict_anti_of_injective⟩

end PartialOrderₓ

/-!
### Strictly monotone functions and `cmp`
-/


variable [LinearOrderₓ β] {f : α → β} {s : Set α} {x y : α}

theorem StrictMonoOnₓ.cmp_map_eq (hf : StrictMonoOnₓ f s) (hx : x ∈ s) (hy : y ∈ s) : cmp (f x) (f y) = cmp x y :=
  ((hf.Compares hx hy).2 (cmp_compares x y)).cmp_eq

theorem StrictMonoₓ.cmp_map_eq (hf : StrictMonoₓ f) (x y : α) : cmp (f x) (f y) = cmp x y :=
  (hf.StrictMonoOn Set.Univ).cmp_map_eq trivialₓ trivialₓ

theorem StrictAntiOnₓ.cmp_map_eq (hf : StrictAntiOnₓ f s) (hx : x ∈ s) (hy : y ∈ s) : cmp (f x) (f y) = cmp y x :=
  hf.dual_right.cmp_map_eq hy hx

theorem StrictAntiₓ.cmp_map_eq (hf : StrictAntiₓ f) (x y : α) : cmp (f x) (f y) = cmp y x :=
  (hf.StrictAntiOn Set.Univ).cmp_map_eq trivialₓ trivialₓ

end LinearOrderₓ

/-! ### Monotonicity in `ℕ` and `ℤ` -/


section Preorderₓ

variable [Preorderₓ α]

theorem Nat.rel_of_forall_rel_succ_of_le_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℕ → β} {a : ℕ}
    (h : ∀ n, a ≤ n → r (f n) (f (n + 1))) ⦃b c : ℕ⦄ (hab : a ≤ b) (hbc : b < c) : r (f b) (f c) := by
  induction' hbc with k b_lt_k r_b_k
  exacts[h _ hab, trans r_b_k (h _ (hab.trans_lt b_lt_k).le)]

theorem Nat.rel_of_forall_rel_succ_of_le_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℕ → β} {a : ℕ}
    (h : ∀ n, a ≤ n → r (f n) (f (n + 1))) ⦃b c : ℕ⦄ (hab : a ≤ b) (hbc : b ≤ c) : r (f b) (f c) :=
  hbc.eq_or_lt.elim (fun h => h ▸ refl _) (Nat.rel_of_forall_rel_succ_of_le_of_lt r h hab)

theorem Nat.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℕ → β} (h : ∀ n, r (f n) (f (n + 1)))
    ⦃a b : ℕ⦄ (hab : a < b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_lt r (fun n _ => h n) le_rflₓ hab

theorem Nat.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℕ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_le r (fun n _ => h n) le_rflₓ hab

theorem monotone_nat_of_le_succ {f : ℕ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotoneₓ f :=
  Nat.rel_of_forall_rel_succ_of_le (· ≤ ·) hf

theorem antitone_nat_of_succ_le {f : ℕ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitoneₓ f :=
  @monotone_nat_of_le_succ αᵒᵈ _ _ hf

theorem strict_mono_nat_of_lt_succ {f : ℕ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMonoₓ f :=
  Nat.rel_of_forall_rel_succ_of_lt (· < ·) hf

theorem strict_anti_nat_of_succ_lt {f : ℕ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAntiₓ f :=
  @strict_mono_nat_of_lt_succ αᵒᵈ _ f hf

namespace Nat

/-- If `α` is a preorder with no maximal elements, then there exists a strictly monotone function
`ℕ → α` with any prescribed value of `f 0`. -/
theorem exists_strict_mono' [NoMaxOrder α] (a : α) : ∃ f : ℕ → α, StrictMonoₓ f ∧ f 0 = a := by
  have := fun x : α => exists_gt x
  choose g hg
  exact ⟨fun n => Nat.recOn n a fun _ => g, strict_mono_nat_of_lt_succ fun n => hg _, rfl⟩

/-- If `α` is a preorder with no maximal elements, then there exists a strictly antitone function
`ℕ → α` with any prescribed value of `f 0`. -/
theorem exists_strict_anti' [NoMinOrder α] (a : α) : ∃ f : ℕ → α, StrictAntiₓ f ∧ f 0 = a :=
  exists_strict_mono' (OrderDual.toDual a)

variable (α)

/-- If `α` is a nonempty preorder with no maximal elements, then there exists a strictly monotone
function `ℕ → α`. -/
theorem exists_strict_mono [Nonempty α] [NoMaxOrder α] : ∃ f : ℕ → α, StrictMonoₓ f :=
  let ⟨a⟩ := ‹Nonempty α›
  let ⟨f, hf, hfa⟩ := exists_strict_mono' a
  ⟨f, hf⟩

/-- If `α` is a nonempty preorder with no minimal elements, then there exists a strictly antitone
function `ℕ → α`. -/
theorem exists_strict_anti [Nonempty α] [NoMinOrder α] : ∃ f : ℕ → α, StrictAntiₓ f :=
  exists_strict_mono αᵒᵈ

end Nat

theorem Int.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℤ → β} (h : ∀ n, r (f n) (f (n + 1)))
    ⦃a b : ℤ⦄ (hab : a < b) : r (f a) (f b) := by
  rcases hab.dest with ⟨n, rfl⟩
  clear hab
  induction' n with n ihn
  · rw [Int.coe_nat_one]
    apply h
    
  · rw [Int.coe_nat_succ, ← Int.add_assoc]
    exact trans ihn (h _)
    

theorem Int.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℤ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  hab.eq_or_lt.elim (fun h => h ▸ refl _) fun h' => Int.rel_of_forall_rel_succ_of_lt r h h'

theorem monotone_int_of_le_succ {f : ℤ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotoneₓ f :=
  Int.rel_of_forall_rel_succ_of_le (· ≤ ·) hf

theorem antitone_int_of_succ_le {f : ℤ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitoneₓ f :=
  Int.rel_of_forall_rel_succ_of_le (· ≥ ·) hf

theorem strict_mono_int_of_lt_succ {f : ℤ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMonoₓ f :=
  Int.rel_of_forall_rel_succ_of_lt (· < ·) hf

theorem strict_anti_int_of_succ_lt {f : ℤ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAntiₓ f :=
  Int.rel_of_forall_rel_succ_of_lt (· > ·) hf

namespace Int

variable (α) [Nonempty α] [NoMinOrder α] [NoMaxOrder α]

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
monotone function `f : ℤ → α`. -/
theorem exists_strict_mono : ∃ f : ℤ → α, StrictMonoₓ f := by
  inhabit α
  rcases Nat.exists_strict_mono' (default : α) with ⟨f, hf, hf₀⟩
  rcases Nat.exists_strict_anti' (default : α) with ⟨g, hg, hg₀⟩
  refine' ⟨fun n => Int.casesOn n f fun n => g (n + 1), strict_mono_int_of_lt_succ _⟩
  rintro (n | _ | n)
  · exact hf n.lt_succ_self
    
  · show g 1 < f 0
    rw [hf₀, ← hg₀]
    exact hg Nat.zero_lt_oneₓ
    
  · exact hg (Nat.lt_succ_selfₓ _)
    

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
antitone function `f : ℤ → α`. -/
theorem exists_strict_anti : ∃ f : ℤ → α, StrictAntiₓ f :=
  exists_strict_mono αᵒᵈ

end Int

-- TODO@Yael: Generalize the following four to succ orders
/-- If `f` is a monotone function from `ℕ` to a preorder such that `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
theorem Monotoneₓ.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Monotoneₓ f) (n : ℕ) {x : α} (h1 : f n < x) (h2 : x < f (n + 1))
    (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_le (Nat.le_of_lt_succₓ <| hf.reflect_lt h2)

/-- If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitoneₓ.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Antitoneₓ f) (n : ℕ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n)
    (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_le (Nat.le_of_lt_succₓ <| hf.reflect_lt h1)

/-- If `f` is a monotone function from `ℤ` to a preorder and `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
theorem Monotoneₓ.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Monotoneₓ f) (n : ℤ) {x : α} (h1 : f n < x) (h2 : x < f (n + 1))
    (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_le (Int.le_of_lt_add_oneₓ <| hf.reflect_lt h2)

/-- If `f` is an antitone function from `ℤ` to a preorder and `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitoneₓ.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Antitoneₓ f) (n : ℤ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n)
    (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_le (Int.le_of_lt_add_oneₓ <| hf.reflect_lt h1)

theorem StrictMonoₓ.id_le {φ : ℕ → ℕ} (h : StrictMonoₓ φ) : ∀ n, n ≤ φ n := fun n =>
  Nat.recOn n (Nat.zero_leₓ _) fun n hn => Nat.succ_le_of_ltₓ (hn.trans_lt <| h <| Nat.lt_succ_selfₓ n)

end Preorderₓ

theorem Subtype.mono_coe [Preorderₓ α] (t : Set α) : Monotoneₓ (coe : Subtype t → α) := fun x y => id

theorem Subtype.strict_mono_coe [Preorderₓ α] (t : Set α) : StrictMonoₓ (coe : Subtype t → α) := fun x y => id

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] [Preorderₓ δ] {f : α → γ} {g : β → δ} {a b : α}

theorem monotone_fst : Monotoneₓ (@Prod.fst α β) := fun a b => And.left

theorem monotone_snd : Monotoneₓ (@Prod.snd α β) := fun a b => And.right

theorem Monotoneₓ.prod_map (hf : Monotoneₓ f) (hg : Monotoneₓ g) : Monotoneₓ (Prod.map f g) := fun a b h =>
  ⟨hf h.1, hg h.2⟩

theorem Antitoneₓ.prod_map (hf : Antitoneₓ f) (hg : Antitoneₓ g) : Antitoneₓ (Prod.map f g) := fun a b h =>
  ⟨hf h.1, hg h.2⟩

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [PartialOrderₓ β] [Preorderₓ γ] [Preorderₓ δ] {f : α → γ} {g : β → δ}

theorem StrictMonoₓ.prod_map (hf : StrictMonoₓ f) (hg : StrictMonoₓ g) : StrictMonoₓ (Prod.map f g) := fun a b => by
  simp_rw [Prod.lt_iffₓ]
  exact Or.impₓ (And.impₓ hf.imp hg.monotone.imp) (And.impₓ hf.monotone.imp hg.imp)

theorem StrictAntiₓ.prod_map (hf : StrictAntiₓ f) (hg : StrictAntiₓ g) : StrictAntiₓ (Prod.map f g) := fun a b => by
  simp_rw [Prod.lt_iffₓ]
  exact Or.impₓ (And.impₓ hf.imp hg.antitone.imp) (And.impₓ hf.antitone.imp hg.imp)

end PartialOrderₓ

