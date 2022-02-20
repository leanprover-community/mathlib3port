/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yaël Dillies
-/
import Mathbin.Order.Compare
import Mathbin.Order.OrderDual
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


open Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

section MonotoneDef

variable [Preorderₓ α] [Preorderₓ β]

/-- A function `f` is monotone if `a ≤ b` implies `f a ≤ f b`. -/
def Monotone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

/-- A function `f` is antitone if `a ≤ b` implies `f b ≤ f a`. -/
def Antitone (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

/-- A function `f` is monotone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f a ≤ f b`. -/
def MonotoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ ha : a ∈ s ⦃b⦄ hb : b ∈ s, a ≤ b → f a ≤ f b

/-- A function `f` is antitone on `s` if, for all `a, b ∈ s`, `a ≤ b` implies `f b ≤ f a`. -/
def AntitoneOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ ha : a ∈ s ⦃b⦄ hb : b ∈ s, a ≤ b → f b ≤ f a

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def StrictMono (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f a < f b

/-- A function `f` is strictly antitone if `a < b` implies `f b < f a`. -/
def StrictAnti (f : α → β) : Prop :=
  ∀ ⦃a b⦄, a < b → f b < f a

/-- A function `f` is strictly monotone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f a < f b`. -/
def StrictMonoOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ ha : a ∈ s ⦃b⦄ hb : b ∈ s, a < b → f a < f b

/-- A function `f` is strictly antitone on `s` if, for all `a, b ∈ s`, `a < b` implies
`f b < f a`. -/
def StrictAntiOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃a⦄ ha : a ∈ s ⦃b⦄ hb : b ∈ s, a < b → f b < f a

end MonotoneDef

/-! ### Monotonicity on the dual order

Strictly many of the `*_on.dual` lemmas in this section should use `of_dual ⁻¹' s` instead of `s`,
but right now this is not possible as `set.preimage` is not defined yet, and importing it creates
an import cycle.
-/


section OrderDual

open OrderDual

variable [Preorderₓ α] [Preorderₓ β] {f : α → β} {s : Set α}

protected theorem Monotone.dual (hf : Monotone f) : Monotone (to_dual ∘ f ∘ of_dual) := fun a b h => hf h

protected theorem Monotone.dual_left (hf : Monotone f) : Antitone (f ∘ of_dual) := fun a b h => hf h

protected theorem Monotone.dual_right (hf : Monotone f) : Antitone (to_dual ∘ f) := fun a b h => hf h

protected theorem Antitone.dual (hf : Antitone f) : Antitone (to_dual ∘ f ∘ of_dual) := fun a b h => hf h

protected theorem Antitone.dual_left (hf : Antitone f) : Monotone (f ∘ of_dual) := fun a b h => hf h

protected theorem Antitone.dual_right (hf : Antitone f) : Monotone (to_dual ∘ f) := fun a b h => hf h

protected theorem MonotoneOn.dual (hf : MonotoneOn f s) : MonotoneOn (to_dual ∘ f ∘ of_dual) s := fun a ha b hb =>
  hf hb ha

protected theorem MonotoneOn.dual_left (hf : MonotoneOn f s) : AntitoneOn (f ∘ of_dual) s := fun a ha b hb => hf hb ha

protected theorem MonotoneOn.dual_right (hf : MonotoneOn f s) : AntitoneOn (to_dual ∘ f) s := fun a ha b hb => hf ha hb

protected theorem AntitoneOn.dual (hf : AntitoneOn f s) : AntitoneOn (to_dual ∘ f ∘ of_dual) s := fun a ha b hb =>
  hf hb ha

protected theorem AntitoneOn.dual_left (hf : AntitoneOn f s) : MonotoneOn (f ∘ of_dual) s := fun a ha b hb => hf hb ha

protected theorem AntitoneOn.dual_right (hf : AntitoneOn f s) : MonotoneOn (to_dual ∘ f) s := fun a ha b hb => hf ha hb

protected theorem StrictMono.dual (hf : StrictMono f) : StrictMono (to_dual ∘ f ∘ of_dual) := fun a b h => hf h

protected theorem StrictMono.dual_left (hf : StrictMono f) : StrictAnti (f ∘ of_dual) := fun a b h => hf h

protected theorem StrictMono.dual_right (hf : StrictMono f) : StrictAnti (to_dual ∘ f) := fun a b h => hf h

protected theorem StrictAnti.dual (hf : StrictAnti f) : StrictAnti (to_dual ∘ f ∘ of_dual) := fun a b h => hf h

protected theorem StrictAnti.dual_left (hf : StrictAnti f) : StrictMono (f ∘ of_dual) := fun a b h => hf h

protected theorem StrictAnti.dual_right (hf : StrictAnti f) : StrictMono (to_dual ∘ f) := fun a b h => hf h

protected theorem StrictMonoOn.dual (hf : StrictMonoOn f s) : StrictMonoOn (to_dual ∘ f ∘ of_dual) s := fun a ha b hb =>
  hf hb ha

protected theorem StrictMonoOn.dual_left (hf : StrictMonoOn f s) : StrictAntiOn (f ∘ of_dual) s := fun a ha b hb =>
  hf hb ha

protected theorem StrictMonoOn.dual_right (hf : StrictMonoOn f s) : StrictAntiOn (to_dual ∘ f) s := fun a ha b hb =>
  hf ha hb

protected theorem StrictAntiOn.dual (hf : StrictAntiOn f s) : StrictAntiOn (to_dual ∘ f ∘ of_dual) s := fun a ha b hb =>
  hf hb ha

protected theorem StrictAntiOn.dual_left (hf : StrictAntiOn f s) : StrictMonoOn (f ∘ of_dual) s := fun a ha b hb =>
  hf hb ha

protected theorem StrictAntiOn.dual_right (hf : StrictAntiOn f s) : StrictMonoOn (to_dual ∘ f) s := fun a ha b hb =>
  hf ha hb

end OrderDual

/-! ### Monotonicity in function spaces -/


section Preorderₓ

variable [Preorderₓ α]

theorem Monotone.comp_le_comp_left [Preorderₓ β] {f : β → α} {g h : γ → β} (hf : Monotone f) (le_gh : g ≤ h) :
    LE.le.{max w u} (f ∘ g) (f ∘ h) := fun x => hf (le_gh x)

variable [Preorderₓ γ]

theorem monotone_lam {f : α → β → γ} (hf : ∀ b, Monotone fun a => f a b) : Monotone f := fun a a' h b => hf b h

theorem monotone_app (f : β → α → γ) (b : β) (hf : Monotone fun a b => f b a) : Monotone (f b) := fun a a' h => hf h b

theorem antitone_lam {f : α → β → γ} (hf : ∀ b, Antitone fun a => f a b) : Antitone f := fun a a' h b => hf b h

theorem antitone_app (f : β → α → γ) (b : β) (hf : Antitone fun a b => f b a) : Antitone (f b) := fun a a' h => hf h b

end Preorderₓ

theorem Function.monotone_eval {ι : Type u} {α : ι → Type v} [∀ i, Preorderₓ (α i)] (i : ι) :
    Monotone (Function.eval i : (∀ i, α i) → α i) := fun f g H => H i

/-! ### Monotonicity hierarchy -/


section Preorderₓ

variable [Preorderₓ α]

section Preorderₓ

variable [Preorderₓ β] {f : α → β}

protected theorem Monotone.monotone_on (hf : Monotone f) (s : Set α) : MonotoneOn f s := fun a _ b _ h => hf h

protected theorem Antitone.antitone_on (hf : Antitone f) (s : Set α) : AntitoneOn f s := fun a _ b _ h => hf h

theorem monotone_on_univ : MonotoneOn f Set.Univ ↔ Monotone f :=
  ⟨fun h a b => h trivialₓ trivialₓ, fun h => h.MonotoneOn _⟩

theorem antitone_on_univ : AntitoneOn f Set.Univ ↔ Antitone f :=
  ⟨fun h a b => h trivialₓ trivialₓ, fun h => h.AntitoneOn _⟩

protected theorem StrictMono.strict_mono_on (hf : StrictMono f) (s : Set α) : StrictMonoOn f s := fun a _ b _ h => hf h

protected theorem StrictAnti.strict_anti_on (hf : StrictAnti f) (s : Set α) : StrictAntiOn f s := fun a _ b _ h => hf h

theorem strict_mono_on_univ : StrictMonoOn f Set.Univ ↔ StrictMono f :=
  ⟨fun h a b => h trivialₓ trivialₓ, fun h => h.StrictMonoOn _⟩

theorem strict_anti_on_univ : StrictAntiOn f Set.Univ ↔ StrictAnti f :=
  ⟨fun h a b => h trivialₓ trivialₓ, fun h => h.StrictAntiOn _⟩

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ β] {f : α → β}

theorem Monotone.strict_mono_of_injective (h₁ : Monotone f) (h₂ : Injective f) : StrictMono f := fun a b h =>
  (h₁ h.le).lt_of_ne fun H => h.Ne <| h₂ H

theorem Antitone.strict_anti_of_injective (h₁ : Antitone f) (h₂ : Injective f) : StrictAnti f := fun a b h =>
  (h₁ h.le).lt_of_ne fun H => h.Ne <| h₂ H.symm

end PartialOrderₓ

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [Preorderₓ β] {f : α → β} {s : Set α}

theorem monotone_iff_forall_lt : Monotone f ↔ ∀ ⦃a b⦄, a < b → f a ≤ f b :=
  forall₂_congrₓ fun a b => ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_argₓ _ H).le) hf⟩

theorem antitone_iff_forall_lt : Antitone f ↔ ∀ ⦃a b⦄, a < b → f b ≤ f a :=
  forall₂_congrₓ fun a b => ⟨fun hf h => hf h.le, fun hf h => h.eq_or_lt.elim (fun H => (congr_argₓ _ H).Ge) hf⟩

theorem monotone_on_iff_forall_lt : MonotoneOn f s ↔ ∀ ⦃a⦄ ha : a ∈ s ⦃b⦄ hb : b ∈ s, a < b → f a ≤ f b :=
  ⟨fun hf a ha b hb h => hf ha hb h.le, fun hf a ha b hb h => h.eq_or_lt.elim (fun H => (congr_argₓ _ H).le) (hf ha hb)⟩

theorem antitone_on_iff_forall_lt : AntitoneOn f s ↔ ∀ ⦃a⦄ ha : a ∈ s ⦃b⦄ hb : b ∈ s, a < b → f b ≤ f a :=
  ⟨fun hf a ha b hb h => hf ha hb h.le, fun hf a ha b hb h => h.eq_or_lt.elim (fun H => (congr_argₓ _ H).Ge) (hf ha hb)⟩

-- `preorder α` isn't strong enough: if the preorder on `α` is an equivalence relation,
-- then `strict_mono f` is vacuously true.
protected theorem StrictMonoOn.monotone_on (hf : StrictMonoOn f s) : MonotoneOn f s :=
  monotone_on_iff_forall_lt.2 fun a ha b hb h => (hf ha hb h).le

protected theorem StrictAntiOn.antitone_on (hf : StrictAntiOn f s) : AntitoneOn f s :=
  antitone_on_iff_forall_lt.2 fun a ha b hb h => (hf ha hb h).le

protected theorem StrictMono.monotone (hf : StrictMono f) : Monotone f :=
  monotone_iff_forall_lt.2 fun a b h => (hf h).le

protected theorem StrictAnti.antitone (hf : StrictAnti f) : Antitone f :=
  antitone_iff_forall_lt.2 fun a b h => (hf h).le

end PartialOrderₓ

/-! ### Monotonicity from and to subsingletons -/


namespace Subsingleton

variable [Preorderₓ α] [Preorderₓ β]

protected theorem monotone [Subsingleton α] (f : α → β) : Monotone f := fun a b _ =>
  (congr_argₓ _ <| Subsingleton.elimₓ _ _).le

protected theorem antitone [Subsingleton α] (f : α → β) : Antitone f := fun a b _ =>
  (congr_argₓ _ <| Subsingleton.elimₓ _ _).le

theorem monotone' [Subsingleton β] (f : α → β) : Monotone f := fun a b _ => (Subsingleton.elimₓ _ _).le

theorem antitone' [Subsingleton β] (f : α → β) : Antitone f := fun a b _ => (Subsingleton.elimₓ _ _).le

protected theorem strict_mono [Subsingleton α] (f : α → β) : StrictMono f := fun a b h =>
  (h.Ne <| Subsingleton.elimₓ _ _).elim

protected theorem strict_anti [Subsingleton α] (f : α → β) : StrictAnti f := fun a b h =>
  (h.Ne <| Subsingleton.elimₓ _ _).elim

end Subsingleton

/-! ### Miscellaneous monotonicity results -/


theorem monotone_id [Preorderₓ α] : Monotone (id : α → α) := fun a b => id

theorem strict_mono_id [Preorderₓ α] : StrictMono (id : α → α) := fun a b => id

theorem monotone_const [Preorderₓ α] [Preorderₓ β] {c : β} : Monotone fun a : α => c := fun a b _ => le_reflₓ c

theorem antitone_const [Preorderₓ α] [Preorderₓ β] {c : β} : Antitone fun a : α => c := fun a b _ => le_reflₓ c

theorem strict_mono_of_le_iff_le [Preorderₓ α] [Preorderₓ β] {f : α → β} (h : ∀ x y, x ≤ y ↔ f x ≤ f y) :
    StrictMono f := fun a b => (lt_iff_lt_of_le_iff_le' (h _ _) (h _ _)).1

theorem injective_of_lt_imp_ne [LinearOrderₓ α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) : Injective f := by
  intro x y hxy
  contrapose hxy
  cases' Ne.lt_or_lt hxy with hxy hxy
  exacts[h _ _ hxy, (h _ _ hxy).symm]

theorem injective_of_le_imp_le [PartialOrderₓ α] [Preorderₓ β] (f : α → β) (h : ∀ {x y}, f x ≤ f y → x ≤ y) :
    Injective f := fun x y hxy => (h hxy.le).antisymm (h hxy.Ge)

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β] {f g : α → β}

protected theorem StrictMono.ite' (hf : StrictMono f) (hg : StrictMono g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → f x < g y) :
    StrictMono fun x => if p x then f x else g x := by
  intro x y h
  by_cases' hy : p y
  · have hx : p x := hp h hy
    simpa [hx, hy] using hf h
    
  by_cases' hx : p x
  · simpa [hx, hy] using hfg hx hy h
    
  · simpa [hx, hy] using hg h
    

protected theorem StrictMono.ite (hf : StrictMono f) (hg : StrictMono g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, f x ≤ g x) : StrictMono fun x => if p x then f x else g x :=
  (hf.ite' hg hp) fun x y hx hy h => (hf h).trans_le (hfg y)

protected theorem StrictAnti.ite' (hf : StrictAnti f) (hg : StrictAnti g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → g y < f x) :
    StrictAnti fun x => if p x then f x else g x :=
  (StrictMono.ite' hf.dual_right hg.dual_right hp hfg).dual_right

protected theorem StrictAnti.ite (hf : StrictAnti f) (hg : StrictAnti g) {p : α → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y⦄, x < y → p y → p x) (hfg : ∀ x, g x ≤ f x) : StrictAnti fun x => if p x then f x else g x :=
  (hf.ite' hg hp) fun x y hx hy h => (hfg y).trans_lt (hf h)

end Preorderₓ

/-! ### Monotonicity under composition -/


section Composition

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] {g : β → γ} {f : α → β} {s : Set α}

protected theorem Monotone.comp (hg : Monotone g) (hf : Monotone f) : Monotone (g ∘ f) := fun a b h => hg (hf h)

theorem Monotone.comp_antitone (hg : Monotone g) (hf : Antitone f) : Antitone (g ∘ f) := fun a b h => hg (hf h)

protected theorem Antitone.comp (hg : Antitone g) (hf : Antitone f) : Monotone (g ∘ f) := fun a b h => hg (hf h)

theorem Antitone.comp_monotone (hg : Antitone g) (hf : Monotone f) : Antitone (g ∘ f) := fun a b h => hg (hf h)

protected theorem Monotone.iterate {f : α → α} (hf : Monotone f) (n : ℕ) : Monotone (f^[n]) :=
  Nat.recOn n monotone_id fun n h => h.comp hf

protected theorem Monotone.comp_monotone_on (hg : Monotone g) (hf : MonotoneOn f s) : MonotoneOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

theorem Monotone.comp_antitone_on (hg : Monotone g) (hf : AntitoneOn f s) : AntitoneOn (g ∘ f) s := fun a ha b hb h =>
  hg (hf ha hb h)

protected theorem Antitone.comp_antitone_on (hg : Antitone g) (hf : AntitoneOn f s) : MonotoneOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

theorem Antitone.comp_monotone_on (hg : Antitone g) (hf : MonotoneOn f s) : AntitoneOn (g ∘ f) s := fun a ha b hb h =>
  hg (hf ha hb h)

protected theorem StrictMono.comp (hg : StrictMono g) (hf : StrictMono f) : StrictMono (g ∘ f) := fun a b h => hg (hf h)

theorem StrictMono.comp_strict_anti (hg : StrictMono g) (hf : StrictAnti f) : StrictAnti (g ∘ f) := fun a b h =>
  hg (hf h)

protected theorem StrictAnti.comp (hg : StrictAnti g) (hf : StrictAnti f) : StrictMono (g ∘ f) := fun a b h => hg (hf h)

theorem StrictAnti.comp_strict_mono (hg : StrictAnti g) (hf : StrictMono f) : StrictAnti (g ∘ f) := fun a b h =>
  hg (hf h)

protected theorem StrictMono.iterate {f : α → α} (hf : StrictMono f) (n : ℕ) : StrictMono (f^[n]) :=
  Nat.recOn n strict_mono_id fun n h => h.comp hf

protected theorem StrictMono.comp_strict_mono_on (hg : StrictMono g) (hf : StrictMonoOn f s) : StrictMonoOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

theorem StrictMono.comp_strict_anti_on (hg : StrictMono g) (hf : StrictAntiOn f s) : StrictAntiOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

protected theorem StrictAnti.comp_strict_anti_on (hg : StrictAnti g) (hf : StrictAntiOn f s) : StrictMonoOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

theorem StrictAnti.comp_strict_mono_on (hg : StrictAnti g) (hf : StrictMonoOn f s) : StrictAntiOn (g ∘ f) s :=
  fun a ha b hb h => hg (hf ha hb h)

end Composition

/-! ### Monotonicity in linear orders  -/


section LinearOrderₓ

variable [LinearOrderₓ α]

section Preorderₓ

variable [Preorderₓ β] {f : α → β} {s : Set α}

open Ordering

theorem Monotone.reflect_lt (hf : Monotone f) {a b : α} (h : f a < f b) : a < b :=
  lt_of_not_geₓ fun h' => h.not_le (hf h')

theorem Antitone.reflect_lt (hf : Antitone f) {a b : α} (h : f a < f b) : b < a :=
  lt_of_not_geₓ fun h' => h.not_le (hf h')

theorem MonotoneOn.reflect_lt (hf : MonotoneOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : f a < f b) : a < b :=
  lt_of_not_geₓ fun h' => h.not_le <| hf hb ha h'

theorem AntitoneOn.reflect_lt (hf : AntitoneOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : f a < f b) : b < a :=
  lt_of_not_geₓ fun h' => h.not_le <| hf ha hb h'

theorem StrictMonoOn.le_iff_le (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a ≤ f b ↔ a ≤ b :=
  ⟨fun h => le_of_not_gtₓ fun h' => (hf hb ha h').not_le h, fun h =>
    h.lt_or_eq_dec.elim (fun h' => (hf ha hb h').le) fun h' => h' ▸ le_rfl⟩

theorem StrictAntiOn.le_iff_le (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a ≤ f b ↔ b ≤ a :=
  hf.dual_right.le_iff_le hb ha

theorem StrictMonoOn.lt_iff_lt (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ a < b := by
  rw [lt_iff_le_not_leₓ, lt_iff_le_not_leₓ, hf.le_iff_le ha hb, hf.le_iff_le hb ha]

theorem StrictAntiOn.lt_iff_lt (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : f a < f b ↔ b < a :=
  hf.dual_right.lt_iff_lt hb ha

theorem StrictMono.le_iff_le (hf : StrictMono f) {a b : α} : f a ≤ f b ↔ a ≤ b :=
  (hf.StrictMonoOn Set.Univ).le_iff_le trivialₓ trivialₓ

theorem StrictAnti.le_iff_le (hf : StrictAnti f) {a b : α} : f a ≤ f b ↔ b ≤ a :=
  (hf.StrictAntiOn Set.Univ).le_iff_le trivialₓ trivialₓ

theorem StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α} : f a < f b ↔ a < b :=
  (hf.StrictMonoOn Set.Univ).lt_iff_lt trivialₓ trivialₓ

theorem StrictAnti.lt_iff_lt (hf : StrictAnti f) {a b : α} : f a < f b ↔ b < a :=
  (hf.StrictAntiOn Set.Univ).lt_iff_lt trivialₓ trivialₓ

protected theorem StrictMonoOn.compares (hf : StrictMonoOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    ∀ {o : Ordering}, o.Compares (f a) (f b) ↔ o.Compares a b
  | Ordering.lt => hf.lt_iff_lt ha hb
  | Ordering.eq => ⟨fun h => ((hf.le_iff_le ha hb).1 h.le).antisymm ((hf.le_iff_le hb ha).1 h.symm.le), congr_argₓ _⟩
  | Ordering.gt => hf.lt_iff_lt hb ha

protected theorem StrictAntiOn.compares (hf : StrictAntiOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares b a :=
  OrderDual.dual_compares.trans <| hf.dual_right.Compares hb ha

protected theorem StrictMono.compares (hf : StrictMono f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares a b :=
  (hf.StrictMonoOn Set.Univ).Compares trivialₓ trivialₓ

protected theorem StrictAnti.compares (hf : StrictAnti f) {a b : α} {o : Ordering} :
    o.Compares (f a) (f b) ↔ o.Compares b a :=
  (hf.StrictAntiOn Set.Univ).Compares trivialₓ trivialₓ

theorem StrictMono.injective (hf : StrictMono f) : Injective f := fun x y h => show Compares Eq x y from hf.Compares.1 h

theorem StrictAnti.injective (hf : StrictAnti f) : Injective f := fun x y h =>
  show Compares Eq x y from hf.Compares.1 h.symm

theorem StrictMono.maximal_of_maximal_image (hf : StrictMono f) {a} (hmax : ∀ p, p ≤ f a) (x : α) : x ≤ a :=
  hf.le_iff_le.mp (hmax (f x))

theorem StrictMono.minimal_of_minimal_image (hf : StrictMono f) {a} (hmin : ∀ p, f a ≤ p) (x : α) : a ≤ x :=
  hf.le_iff_le.mp (hmin (f x))

theorem StrictAnti.minimal_of_maximal_image (hf : StrictAnti f) {a} (hmax : ∀ p, p ≤ f a) (x : α) : a ≤ x :=
  hf.le_iff_le.mp (hmax (f x))

theorem StrictAnti.maximal_of_minimal_image (hf : StrictAnti f) {a} (hmin : ∀ p, f a ≤ p) (x : α) : x ≤ a :=
  hf.le_iff_le.mp (hmin (f x))

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ β] {f : α → β}

theorem Monotone.strict_mono_iff_injective (hf : Monotone f) : StrictMono f ↔ Injective f :=
  ⟨fun h => h.Injective, hf.strict_mono_of_injective⟩

theorem Antitone.strict_anti_iff_injective (hf : Antitone f) : StrictAnti f ↔ Injective f :=
  ⟨fun h => h.Injective, hf.strict_anti_of_injective⟩

end PartialOrderₓ

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
  Nat.rel_of_forall_rel_succ_of_le_of_lt r (fun n _ => h n) le_rfl hab

theorem Nat.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℕ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_le r (fun n _ => h n) le_rfl hab

theorem monotone_nat_of_le_succ {f : ℕ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  Nat.rel_of_forall_rel_succ_of_le (· ≤ ·) hf

theorem antitone_nat_of_succ_le {f : ℕ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitone f :=
  @monotone_nat_of_le_succ (OrderDual α) _ _ hf

theorem strict_mono_nat_of_lt_succ {f : ℕ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMono f :=
  Nat.rel_of_forall_rel_succ_of_lt (· < ·) hf

theorem strict_anti_nat_of_succ_lt {f : ℕ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  @strict_mono_nat_of_lt_succ (OrderDual α) _ f hf

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

theorem monotone_int_of_le_succ {f : ℤ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  Int.rel_of_forall_rel_succ_of_le (· ≤ ·) hf

theorem antitone_int_of_succ_le {f : ℤ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitone f :=
  Int.rel_of_forall_rel_succ_of_le (· ≥ ·) hf

theorem strict_mono_int_of_lt_succ {f : ℤ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMono f :=
  Int.rel_of_forall_rel_succ_of_lt (· < ·) hf

theorem strict_anti_int_of_succ_lt {f : ℤ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  Int.rel_of_forall_rel_succ_of_lt (· > ·) hf

/-- If `f` is a monotone function from `ℕ` to a preorder such that `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
-- TODO@Yael: Generalize the following four to succ orders
theorem Monotone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Monotone f) (n : ℕ) {x : α} (h1 : f n < x) (h2 : x < f (n + 1))
    (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_le (Nat.le_of_lt_succₓ <| hf.reflect_lt h2)

/-- If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Antitone f) (n : ℕ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n)
    (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_le (Nat.le_of_lt_succₓ <| hf.reflect_lt h1)

/-- If `f` is a monotone function from `ℤ` to a preorder and `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
theorem Monotone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Monotone f) (n : ℤ) {x : α} (h1 : f n < x) (h2 : x < f (n + 1))
    (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_le (Int.le_of_lt_add_oneₓ <| hf.reflect_lt h2)

/-- If `f` is an antitone function from `ℤ` to a preorder and `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Antitone f) (n : ℤ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n)
    (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_le (Int.le_of_lt_add_oneₓ <| hf.reflect_lt h1)

theorem StrictMono.id_le {φ : ℕ → ℕ} (h : StrictMono φ) : ∀ n, n ≤ φ n := fun n =>
  Nat.recOn n (Nat.zero_leₓ _) fun n hn => Nat.succ_le_of_ltₓ (hn.trans_lt <| h <| Nat.lt_succ_selfₓ n)

end Preorderₓ

theorem Subtype.mono_coe [Preorderₓ α] (t : Set α) : Monotone (coe : Subtype t → α) := fun x y => id

theorem Subtype.strict_mono_coe [Preorderₓ α] (t : Set α) : StrictMono (coe : Subtype t → α) := fun x y => id

theorem monotone_fst {α β : Type _} [Preorderₓ α] [Preorderₓ β] : Monotone (@Prod.fst α β) := fun x y h => h.1

theorem monotone_snd {α β : Type _} [Preorderₓ α] [Preorderₓ β] : Monotone (@Prod.snd α β) := fun x y h => h.2

