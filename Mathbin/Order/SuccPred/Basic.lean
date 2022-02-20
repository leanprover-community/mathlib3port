/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.BoundedOrder
import Mathbin.Order.CompleteLattice
import Mathbin.Order.Cover
import Mathbin.Order.Iterate
import Mathbin.Tactic.Monotonicity.Default

/-!
# Successor and predecessor

This file defines successor and predecessor orders. `succ a`, the successor of an element `a : α` is
the least element greater than `a`. `pred a` is the greatest element less than `a`. Typical examples
include `ℕ`, `ℤ`, `ℕ+`, `fin n`, but also `enat`, the lexicographic order of a successor/predecessor
order...

## Typeclasses

* `succ_order`: Order equipped with a sensible successor function.
* `pred_order`: Order equipped with a sensible predecessor function.
* `is_succ_archimedean`: `succ_order` where `succ` iterated to an element gives all the greater
  ones.
* `is_pred_archimedean`: `pred_order` where `pred` iterated to an element gives all the greater
  ones.

## Implementation notes

Maximal elements don't have a sensible successor. Thus the naïve typeclass
```lean
class naive_succ_order (α : Type*) [preorder α] :=
(succ : α → α)
(succ_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
(lt_succ_iff : ∀ {a b}, a < succ b ↔ a ≤ b)
```
can't apply to an `order_top` because plugging in `a = b = ⊤` into either of `succ_le_iff` and
`lt_succ_iff` yields `⊤ < ⊤` (or more generally `m < m` for a maximal element `m`).
The solution taken here is to remove the implications `≤ → <` and instead require that `a < succ a`
for all non maximal elements (enforced by the combination of `le_succ` and the contrapositive of
`maximal_of_succ_le`).
The stricter condition of every element having a sensible successor can be obtained through the
combination of `succ_order α` and `no_max_order α`.

## TODO

Is `galois_connection pred succ` always true? If not, we should introduce
```lean
class succ_pred_order (α : Type*) [preorder α] extends succ_order α, pred_order α :=
(pred_succ_gc : galois_connection (pred : α → α) succ)
```
`covby` should help here.
-/


open Function

/-! ### Successor order -/


variable {α : Type _}

/-- Order equipped with a sensible successor function. -/
@[ext]
class SuccOrder (α : Type _) [Preorderₓ α] where
  succ : α → α
  le_succ : ∀ a, a ≤ succ a
  maximal_of_succ_le : ∀ ⦃a⦄, succ a ≤ a → ∀ ⦃b⦄, ¬a < b
  succ_le_of_lt : ∀ {a b}, a < b → succ a ≤ b
  le_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b

namespace SuccOrder

section Preorderₓ

variable [Preorderₓ α]

/-- A constructor for `succ_order α` usable when `α` has no maximal element. -/
def ofSuccLeIffOfLeLtSucc (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
    (hle_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b) : SuccOrder α :=
  { succ, le_succ := fun a => (hsucc_le_iff.1 le_rfl).le,
    maximal_of_succ_le := fun a ha => (lt_irreflₓ a (hsucc_le_iff.1 ha)).elim,
    succ_le_of_lt := fun a b => hsucc_le_iff.2, le_of_lt_succ := fun a b => hle_of_lt_succ }

variable [SuccOrder α]

@[simp, mono]
theorem succ_le_succ {a b : α} (h : a ≤ b) : succ a ≤ succ b := by
  by_cases' ha : ∀ ⦃c⦄, ¬a < c
  · have hba : succ b ≤ a := by
      by_contra H
      exact ha ((h.trans (le_succ b)).lt_of_not_le H)
    by_contra H
    exact ha ((h.trans (le_succ b)).trans_lt ((hba.trans (le_succ a)).lt_of_not_le H))
    
  · push_neg  at ha
    obtain ⟨c, hc⟩ := ha
    exact
      succ_le_of_lt
        ((h.trans (le_succ b)).lt_of_not_le fun hba =>
          maximal_of_succ_le (hba.trans h) (((le_succ b).trans hba).trans_lt hc))
    

theorem succ_mono : Monotone (succ : α → α) := fun a b => succ_le_succ

theorem lt_succ_of_not_maximal {a b : α} (h : a < b) : a < succ a :=
  (le_succ a).lt_of_not_le fun ha => maximal_of_succ_le ha h

alias lt_succ_of_not_maximal ← LT.lt.lt_succ

protected theorem _root_.has_lt.lt.covby_succ {a b : α} (h : a < b) : a ⋖ succ a :=
  ⟨h.lt_succ, fun c hc => (succ_le_of_lt hc).not_lt⟩

@[simp]
theorem covby_succ_of_nonempty_Ioi {a : α} (h : (Set.Ioi a).Nonempty) : a ⋖ succ a :=
  LT.lt.covby_succ h.some_mem

theorem lt_succ_of_not_is_max {a : α} (ha : ¬IsMax a) : a < SuccOrder.succ a :=
  (le_succ a).lt_of_not_le fun h => not_exists.2 (maximal_of_succ_le h) (not_is_max_iff.mp ha)

theorem lt_succ_iff_of_not_is_max {a b : α} (ha : ¬IsMax a) : b < SuccOrder.succ a ↔ b ≤ a :=
  ⟨le_of_lt_succ, fun h_le => h_le.trans_lt (lt_succ_of_not_is_max ha)⟩

theorem succ_le_iff_of_not_is_max {a b : α} (ha : ¬IsMax a) : succ a ≤ b ↔ a < b :=
  ⟨(lt_succ_of_not_is_max ha).trans_le, succ_le_of_lt⟩

section NoMaxOrder

variable [NoMaxOrder α] {a b : α}

theorem lt_succ (a : α) : a < succ a :=
  lt_succ_of_not_is_max (not_is_max a)

theorem lt_succ_iff : a < succ b ↔ a ≤ b :=
  lt_succ_iff_of_not_is_max (not_is_max b)

theorem succ_le_iff : succ a ≤ b ↔ a < b :=
  succ_le_iff_of_not_is_max (not_is_max a)

@[simp]
theorem succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b :=
  ⟨fun h => le_of_lt_succ <| (lt_succ a).trans_le h, fun h => succ_le_of_lt <| h.trans_lt <| lt_succ b⟩

alias succ_le_succ_iff ↔ le_of_succ_le_succ _

theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := by
  simp_rw [lt_iff_le_not_leₓ, succ_le_succ_iff]

alias succ_lt_succ_iff ↔ lt_of_succ_lt_succ succ_lt_succ

theorem succ_strict_mono : StrictMono (succ : α → α) := fun a b => succ_lt_succ

theorem covby_succ (a : α) : a ⋖ succ a :=
  ⟨lt_succ a, fun c hc => (succ_le_of_lt hc).not_lt⟩

end NoMaxOrder

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α]

/-- There is at most one way to define the successors in a `partial_order`. -/
instance : Subsingleton (SuccOrder α) := by
  refine' Subsingleton.intro fun h₀ h₁ => _
  ext a
  by_cases' ha : @succ _ _ h₀ a ≤ a
  · refine' (ha.trans (@le_succ _ _ h₁ a)).antisymm _
    by_contra H
    exact
      @maximal_of_succ_le _ _ h₀ _ ha _ ((@le_succ _ _ h₁ a).lt_of_not_le fun h => H <| h.trans <| @le_succ _ _ h₀ a)
    
  · exact
      (@succ_le_of_lt _ _ h₀ _ _ <|
            (@le_succ _ _ h₁ a).lt_of_not_le fun h =>
              @maximal_of_succ_le _ _ h₁ _ h _ <| (@le_succ _ _ h₀ a).lt_of_not_le ha).antisymm
        (@succ_le_of_lt _ _ h₁ _ _ <| (@le_succ _ _ h₀ a).lt_of_not_le ha)
    

variable [SuccOrder α]

theorem le_le_succ_iff {a b : α} : a ≤ b ∧ b ≤ succ a ↔ b = a ∨ b = succ a := by
  constructor
  · rintro h
    rw [or_iff_not_imp_left]
    exact fun hba : b ≠ a => h.2.antisymm (succ_le_of_lt <| h.1.lt_of_ne <| hba.symm)
    
  rintro (rfl | rfl)
  · exact ⟨le_rfl, le_succ b⟩
    
  · exact ⟨le_succ a, le_rfl⟩
    

theorem _root_.covby.succ_eq {a b : α} (h : a ⋖ b) : succ a = b :=
  (succ_le_of_lt h.lt).eq_of_not_lt fun h' => h.2 (lt_succ_of_not_maximal h.lt) h'

section NoMaxOrder

variable [NoMaxOrder α] {a b : α}

theorem succ_injective : Injective (succ : α → α) := by
  rintro a b
  simp_rw [eq_iff_le_not_lt, succ_le_succ_iff, succ_lt_succ_iff]
  exact id

theorem succ_eq_succ_iff : succ a = succ b ↔ a = b :=
  succ_injective.eq_iff

theorem succ_ne_succ_iff : succ a ≠ succ b ↔ a ≠ b :=
  succ_injective.ne_iff

alias succ_ne_succ_iff ↔ ne_of_succ_ne_succ succ_ne_succ

theorem lt_succ_iff_lt_or_eq : a < succ b ↔ a < b ∨ a = b :=
  lt_succ_iff.trans le_iff_lt_or_eqₓ

theorem le_succ_iff_lt_or_eq : a ≤ succ b ↔ a ≤ b ∨ a = succ b := by
  rw [← lt_succ_iff, ← lt_succ_iff, lt_succ_iff_lt_or_eq]

theorem _root_.covby_iff_succ_eq : a ⋖ b ↔ succ a = b :=
  ⟨Covby.succ_eq, by
    rintro rfl
    exact covby_succ _⟩

end NoMaxOrder

end PartialOrderₓ

section OrderTop

variable [PartialOrderₓ α] [OrderTop α] [SuccOrder α]

@[simp]
theorem succ_top : succ (⊤ : α) = ⊤ :=
  le_top.antisymm (le_succ _)

@[simp]
theorem succ_le_iff_eq_top {a : α} : succ a ≤ a ↔ a = ⊤ :=
  ⟨fun h => eq_top_of_maximal (maximal_of_succ_le h), fun h => by
    rw [h, succ_top]⟩

@[simp]
theorem lt_succ_iff_ne_top {a : α} : a < succ a ↔ a ≠ ⊤ := by
  simp only [lt_iff_le_not_leₓ, true_andₓ, le_succ a]
  exact not_iff_not.2 succ_le_iff_eq_top

end OrderTop

section OrderBot

variable [PartialOrderₓ α] [OrderBot α] [SuccOrder α] [Nontrivial α]

theorem bot_lt_succ (a : α) : ⊥ < succ a := by
  obtain ⟨b, hb⟩ := exists_ne (⊥ : α)
  refine' bot_lt_iff_ne_bot.2 fun h => _
  have := eq_bot_iff.2 ((le_succ a).trans h.le)
  rw [this] at h
  exact maximal_of_succ_le h.le (bot_lt_iff_ne_bot.2 hb)

theorem succ_ne_bot (a : α) : succ a ≠ ⊥ :=
  (bot_lt_succ a).ne'

end OrderBot

section LinearOrderₓ

variable [LinearOrderₓ α]

/-- A constructor for `succ_order α` usable when `α` is a linear order with no maximal element. -/
def ofSuccLeIff (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) : SuccOrder α :=
  { succ, le_succ := fun a => (hsucc_le_iff.1 le_rfl).le,
    maximal_of_succ_le := fun a ha => (lt_irreflₓ a (hsucc_le_iff.1 ha)).elim,
    succ_le_of_lt := fun a b => hsucc_le_iff.2,
    le_of_lt_succ := fun a b h => le_of_not_ltₓ ((not_congr hsucc_le_iff).1 h.not_le) }

end LinearOrderₓ

section CompleteLattice

variable [CompleteLattice α] [SuccOrder α]

theorem succ_eq_infi (a : α) : succ a = ⨅ (b : α) (h : a < b), b := by
  refine' le_antisymmₓ (le_infi fun b => le_infi succ_le_of_lt) _
  obtain rfl | ha := eq_or_ne a ⊤
  · rw [succ_top]
    exact le_top
    
  exact binfi_le _ (lt_succ_iff_ne_top.2 ha)

end CompleteLattice

section Intervals

variable [Preorderₓ α] [SuccOrder α]

theorem Iic_eq_Iio_succ' {a : α} (ha : ¬IsMax a) : Set.Iic a = Set.Iio (SuccOrder.succ a) := by
  ext1 x
  rw [Set.mem_Iic, Set.mem_Iio]
  exact (lt_succ_iff_of_not_is_max ha).symm

theorem Iic_eq_Iio_succ [NoMaxOrder α] (a : α) : Set.Iic a = Set.Iio (SuccOrder.succ a) :=
  Iic_eq_Iio_succ' (not_is_max a)

theorem Ioi_eq_Ici_succ' {a : α} (ha : ¬IsMax a) : Set.Ioi a = Set.Ici (SuccOrder.succ a) := by
  ext1 x
  rw [Set.mem_Ioi, Set.mem_Ici]
  exact (succ_le_iff_of_not_is_max ha).symm

theorem Ioi_eq_Ici_succ [NoMaxOrder α] (a : α) : Set.Ioi a = Set.Ici (SuccOrder.succ a) :=
  Ioi_eq_Ici_succ' (not_is_max a)

end Intervals

end SuccOrder

/-! ### Predecessor order -/


/-- Order equipped with a sensible predecessor function. -/
@[ext]
class PredOrder (α : Type _) [Preorderₓ α] where
  pred : α → α
  pred_le : ∀ a, pred a ≤ a
  minimal_of_le_pred : ∀ ⦃a⦄, a ≤ pred a → ∀ ⦃b⦄, ¬b < a
  le_pred_of_lt : ∀ {a b}, a < b → a ≤ pred b
  le_of_pred_lt : ∀ {a b}, pred a < b → a ≤ b

namespace PredOrder

section Preorderₓ

variable [Preorderₓ α]

/-- A constructor for `pred_order α` usable when `α` has no minimal element. -/
def ofLePredIffOfPredLePred (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b)
    (hle_of_pred_lt : ∀ {a b}, pred a < b → a ≤ b) : PredOrder α :=
  { pred, pred_le := fun a => (hle_pred_iff.1 le_rfl).le,
    minimal_of_le_pred := fun a ha => (lt_irreflₓ a (hle_pred_iff.1 ha)).elim,
    le_pred_of_lt := fun a b => hle_pred_iff.2, le_of_pred_lt := fun a b => hle_of_pred_lt }

variable [PredOrder α]

@[simp, mono]
theorem pred_le_pred {a b : α} (h : a ≤ b) : pred a ≤ pred b := by
  by_cases' hb : ∀ ⦃c⦄, ¬c < b
  · have hba : b ≤ pred a := by
      by_contra H
      exact hb (((pred_le a).trans h).lt_of_not_le H)
    by_contra H
    exact hb ((((pred_le b).trans hba).lt_of_not_le H).trans_le ((pred_le a).trans h))
    
  · push_neg  at hb
    obtain ⟨c, hc⟩ := hb
    exact
      le_pred_of_lt
        (((pred_le a).trans h).lt_of_not_le fun hba =>
          minimal_of_le_pred (h.trans hba) <| hc.trans_le <| hba.trans <| pred_le a)
    

theorem pred_mono : Monotone (pred : α → α) := fun a b => pred_le_pred

theorem pred_lt_of_not_minimal {a b : α} (h : b < a) : pred a < a :=
  (pred_le a).lt_of_not_le fun ha => minimal_of_le_pred ha h

alias pred_lt_of_not_minimal ← LT.lt.pred_lt

protected theorem _root_.has_lt.lt.pred_covby {a b : α} (h : b < a) : pred a ⋖ a :=
  ⟨h.pred_lt, fun c hc => (le_of_pred_lt hc).not_lt⟩

@[simp]
theorem pred_covby_of_nonempty_Iio {a : α} (h : (Set.Iio a).Nonempty) : pred a ⋖ a :=
  LT.lt.pred_covby h.some_mem

theorem pred_lt_of_not_is_min {a : α} (ha : ¬IsMin a) : PredOrder.pred a < a :=
  (pred_le a).lt_of_not_le fun h => not_exists.2 (minimal_of_le_pred h) (not_is_min_iff.mp ha)

theorem pred_lt_iff_of_not_is_min {a b : α} (ha : ¬IsMin a) : PredOrder.pred a < b ↔ a ≤ b :=
  ⟨le_of_pred_lt, fun h_le => (pred_lt_of_not_is_min ha).trans_le h_le⟩

theorem le_pred_iff_of_not_is_min {a b : α} (hb : ¬IsMin b) : a ≤ pred b ↔ a < b :=
  ⟨fun h => h.trans_lt (pred_lt_of_not_is_min hb), le_pred_of_lt⟩

section NoMinOrder

variable [NoMinOrder α] {a b : α}

theorem pred_lt (a : α) : pred a < a :=
  pred_lt_of_not_is_min (not_is_min a)

theorem pred_lt_iff : pred a < b ↔ a ≤ b :=
  pred_lt_iff_of_not_is_min (not_is_min a)

theorem le_pred_iff : a ≤ pred b ↔ a < b :=
  le_pred_iff_of_not_is_min (not_is_min b)

@[simp]
theorem pred_le_pred_iff : pred a ≤ pred b ↔ a ≤ b :=
  ⟨fun h => le_of_pred_lt <| h.trans_lt (pred_lt b), fun h => le_pred_of_lt <| (pred_lt a).trans_le h⟩

alias pred_le_pred_iff ↔ le_of_pred_le_pred _

@[simp]
theorem pred_lt_pred_iff : pred a < pred b ↔ a < b := by
  simp_rw [lt_iff_le_not_leₓ, pred_le_pred_iff]

alias pred_lt_pred_iff ↔ lt_of_pred_lt_pred pred_lt_pred

theorem pred_strict_mono : StrictMono (pred : α → α) := fun a b => pred_lt_pred

theorem pred_covby (a : α) : pred a ⋖ a :=
  ⟨pred_lt a, fun c hc => (le_of_pred_lt hc).not_lt⟩

end NoMinOrder

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α]

/-- There is at most one way to define the predecessors in a `partial_order`. -/
instance : Subsingleton (PredOrder α) := by
  refine' Subsingleton.intro fun h₀ h₁ => _
  ext a
  by_cases' ha : a ≤ @pred _ _ h₀ a
  · refine' le_antisymmₓ _ ((@pred_le _ _ h₁ a).trans ha)
    by_contra H
    exact @minimal_of_le_pred _ _ h₀ _ ha _ ((@pred_le _ _ h₁ a).lt_of_not_le fun h => H <| (@pred_le _ _ h₀ a).trans h)
    
  · exact
      (@le_pred_of_lt _ _ h₁ _ _ <| (@pred_le _ _ h₀ a).lt_of_not_le ha).antisymm
        (@le_pred_of_lt _ _ h₀ _ _ <|
          (@pred_le _ _ h₁ a).lt_of_not_le fun h =>
            @minimal_of_le_pred _ _ h₁ _ h _ <| (@pred_le _ _ h₀ a).lt_of_not_le ha)
    

variable [PredOrder α]

theorem pred_le_le_iff {a b : α} : pred a ≤ b ∧ b ≤ a ↔ b = a ∨ b = pred a := by
  constructor
  · rintro h
    rw [or_iff_not_imp_left]
    exact fun hba => (le_pred_of_lt <| h.2.lt_of_ne hba).antisymm h.1
    
  rintro (rfl | rfl)
  · exact ⟨pred_le b, le_rfl⟩
    
  · exact ⟨le_rfl, pred_le a⟩
    

theorem _root_.covby.pred_eq {a b : α} (h : a ⋖ b) : pred b = a :=
  (le_pred_of_lt h.lt).eq_of_not_gt fun h' => h.2 h' <| pred_lt_of_not_minimal h.lt

section NoMinOrder

variable [NoMinOrder α] {a b : α}

theorem pred_injective : Injective (pred : α → α) := by
  rintro a b
  simp_rw [eq_iff_le_not_lt, pred_le_pred_iff, pred_lt_pred_iff]
  exact id

theorem pred_eq_pred_iff : pred a = pred b ↔ a = b :=
  pred_injective.eq_iff

theorem pred_ne_pred_iff : pred a ≠ pred b ↔ a ≠ b :=
  pred_injective.ne_iff

theorem pred_lt_iff_lt_or_eq : pred a < b ↔ a < b ∨ a = b :=
  pred_lt_iff.trans le_iff_lt_or_eqₓ

theorem le_pred_iff_lt_or_eq : pred a ≤ b ↔ a ≤ b ∨ pred a = b := by
  rw [← pred_lt_iff, ← pred_lt_iff, pred_lt_iff_lt_or_eq]

theorem _root_.covby_iff_pred_eq : a ⋖ b ↔ pred b = a :=
  ⟨Covby.pred_eq, by
    rintro rfl
    exact pred_covby _⟩

end NoMinOrder

end PartialOrderₓ

section OrderBot

variable [PartialOrderₓ α] [OrderBot α] [PredOrder α]

@[simp]
theorem pred_bot : pred (⊥ : α) = ⊥ :=
  (pred_le _).antisymm bot_le

@[simp]
theorem le_pred_iff_eq_bot {a : α} : a ≤ pred a ↔ a = ⊥ :=
  ⟨fun h => eq_bot_of_minimal (minimal_of_le_pred h), fun h => by
    rw [h, pred_bot]⟩

@[simp]
theorem pred_lt_iff_ne_bot {a : α} : pred a < a ↔ a ≠ ⊥ := by
  simp only [lt_iff_le_not_leₓ, true_andₓ, pred_le a]
  exact not_iff_not.2 le_pred_iff_eq_bot

end OrderBot

section OrderTop

variable [PartialOrderₓ α] [OrderTop α] [PredOrder α]

theorem pred_lt_top [Nontrivial α] (a : α) : pred a < ⊤ := by
  obtain ⟨b, hb⟩ := exists_ne (⊤ : α)
  refine' lt_top_iff_ne_top.2 fun h => _
  have := eq_top_iff.2 (h.ge.trans (pred_le a))
  rw [this] at h
  exact minimal_of_le_pred h.ge (lt_top_iff_ne_top.2 hb)

theorem pred_ne_top [Nontrivial α] (a : α) : pred a ≠ ⊤ :=
  (pred_lt_top a).Ne

end OrderTop

section LinearOrderₓ

variable [LinearOrderₓ α] {a b : α}

/-- A constructor for `pred_order α` usable when `α` is a linear order with no maximal element. -/
def ofLePredIff (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b) : PredOrder α :=
  { pred, pred_le := fun a => (hle_pred_iff.1 le_rfl).le,
    minimal_of_le_pred := fun a ha => (lt_irreflₓ a (hle_pred_iff.1 ha)).elim,
    le_pred_of_lt := fun a b => hle_pred_iff.2,
    le_of_pred_lt := fun a b h => le_of_not_ltₓ ((not_congr hle_pred_iff).1 h.not_le) }

end LinearOrderₓ

section CompleteLattice

variable [CompleteLattice α] [PredOrder α]

theorem pred_eq_supr (a : α) : pred a = ⨆ (b : α) (h : b < a), b := by
  refine' le_antisymmₓ _ (supr_le fun b => supr_le le_pred_of_lt)
  obtain rfl | ha := eq_or_ne a ⊥
  · rw [pred_bot]
    exact bot_le
    
  exact @le_bsupr _ _ _ (fun b => b < a) (fun a _ => a) (pred a) (pred_lt_iff_ne_bot.2 ha)

end CompleteLattice

section Intervals

variable [Preorderₓ α] [PredOrder α]

theorem Ici_eq_Ioi_pred' {a : α} (ha : ¬IsMin a) : Set.Ici a = Set.Ioi (PredOrder.pred a) := by
  ext1 x
  rw [Set.mem_Ici, Set.mem_Ioi]
  exact (pred_lt_iff_of_not_is_min ha).symm

theorem Ici_eq_Ioi_pred [NoMinOrder α] (a : α) : Set.Ici a = Set.Ioi (PredOrder.pred a) :=
  Ici_eq_Ioi_pred' (not_is_min a)

theorem Iio_eq_Iic_pred' {a : α} (ha : ¬IsMin a) : Set.Iio a = Set.Iic (PredOrder.pred a) := by
  ext1 x
  rw [Set.mem_Iio, Set.mem_Iic]
  exact (le_pred_iff_of_not_is_min ha).symm

theorem Iio_eq_Iic_pred [NoMinOrder α] (a : α) : Set.Iio a = Set.Iic (PredOrder.pred a) :=
  Iio_eq_Iic_pred' (not_is_min a)

end Intervals

end PredOrder

open SuccOrder PredOrder

/-! ### Successor-predecessor orders -/


section SuccPredOrder

variable [PartialOrderₓ α] [SuccOrder α] [PredOrder α] {a b : α}

protected theorem _root_.has_lt.lt.succ_pred (h : b < a) : succ (pred a) = a :=
  h.pred_covby.succ_eq

protected theorem _root_.has_lt.lt.pred_succ (h : a < b) : pred (succ a) = a :=
  h.covby_succ.pred_eq

@[simp]
theorem succ_pred_of_nonempty_Iio {a : α} (h : (Set.Iio a).Nonempty) : succ (pred a) = a :=
  LT.lt.succ_pred h.some_mem

@[simp]
theorem pred_succ_of_nonempty_Ioi {a : α} (h : (Set.Ioi a).Nonempty) : pred (succ a) = a :=
  LT.lt.pred_succ h.some_mem

@[simp]
theorem succ_pred [NoMinOrder α] (a : α) : succ (pred a) = a :=
  (pred_covby _).succ_eq

@[simp]
theorem pred_succ [NoMaxOrder α] (a : α) : pred (succ a) = a :=
  (covby_succ _).pred_eq

end SuccPredOrder

/-! ### Dual order -/


section OrderDual

variable [Preorderₓ α]

instance [PredOrder α] : SuccOrder (OrderDual α) where
  succ := (pred : α → α)
  le_succ := pred_le
  maximal_of_succ_le := minimal_of_le_pred
  succ_le_of_lt := fun a b h => le_pred_of_lt h
  le_of_lt_succ := fun a b => le_of_pred_lt

instance [SuccOrder α] : PredOrder (OrderDual α) where
  pred := (succ : α → α)
  pred_le := le_succ
  minimal_of_le_pred := maximal_of_succ_le
  le_pred_of_lt := fun a b h => succ_le_of_lt h
  le_of_pred_lt := fun a b => le_of_lt_succ

end OrderDual

/-! ### `with_bot`, `with_top`
Adding a greatest/least element to a `succ_order` or to a `pred_order`.

As far as successors and predecessors are concerned, there are four ways to add a bottom or top
element to an order:
* Adding a `⊤` to an `order_top`: Preserves `succ` and `pred`.
* Adding a `⊤` to a `no_max_order`: Preserves `succ`. Never preserves `pred`.
* Adding a `⊥` to an `order_bot`: Preserves `succ` and `pred`.
* Adding a `⊥` to a `no_min_order`: Preserves `pred`. Never preserves `succ`.
where "preserves `(succ/pred)`" means
`(succ/pred)_order α → (succ/pred)_order ((with_top/with_bot) α)`.
-/


section WithTop

open WithTop

/-! #### Adding a `⊤` to an `order_top` -/


instance [DecidableEq α] [PartialOrderₓ α] [OrderTop α] [SuccOrder α] : SuccOrder (WithTop α) where
  succ := fun a =>
    match a with
    | ⊤ => ⊤
    | some a => ite (a = ⊤) ⊤ (some (succ a))
  le_succ := fun a => by
    cases a
    · exact le_top
      
    change ((· ≤ ·) : WithTop α → WithTop α → Prop) _ (ite _ _ _)
    split_ifs
    · exact le_top
      
    · exact some_le_some.2 (le_succ a)
      
  maximal_of_succ_le := fun a ha b h => by
    cases a
    · exact not_top_lt h
      
    change ((· ≤ ·) : WithTop α → WithTop α → Prop) (ite _ _ _) _ at ha
    split_ifs  at ha with ha'
    · exact not_top_lt (ha.trans_lt h)
      
    · rw [some_le_some, succ_le_iff_eq_top] at ha
      exact ha' ha
      
  succ_le_of_lt := fun a b h => by
    cases b
    · exact le_top
      
    cases a
    · exact (not_top_lt h).elim
      
    rw [some_lt_some] at h
    change ((· ≤ ·) : WithTop α → WithTop α → Prop) (ite _ _ _) _
    split_ifs with ha
    · rw [ha] at h
      exact (not_top_lt h).elim
      
    · exact some_le_some.2 (succ_le_of_lt h)
      
  le_of_lt_succ := fun a b h => by
    cases a
    · exact (not_top_lt h).elim
      
    cases b
    · exact le_top
      
    change ((· < ·) : WithTop α → WithTop α → Prop) _ (ite _ _ _) at h
    rw [some_le_some]
    split_ifs  at h with hb
    · rw [hb]
      exact le_top
      
    · exact le_of_lt_succ (some_lt_some.1 h)
      

instance [PartialOrderₓ α] [OrderTop α] [PredOrder α] : PredOrder (WithTop α) where
  pred := fun a =>
    match a with
    | ⊤ => some ⊤
    | some a => some (pred a)
  pred_le := fun a =>
    match a with
    | ⊤ => le_top
    | some a => some_le_some.2 (pred_le a)
  minimal_of_le_pred := fun a ha b h => by
    cases a
    · exact (coe_lt_top (⊤ : α)).not_le ha
      
    cases b
    · exact h.not_le le_top
      
    · exact minimal_of_le_pred (some_le_some.1 ha) (some_lt_some.1 h)
      
  le_pred_of_lt := fun a b h => by
    cases a
    · exact (le_top.not_lt h).elim
      
    cases b
    · exact some_le_some.2 le_top
      
    exact some_le_some.2 (le_pred_of_lt <| some_lt_some.1 h)
  le_of_pred_lt := fun a b h => by
    cases b
    · exact le_top
      
    cases a
    · exact (not_top_lt <| some_lt_some.1 h).elim
      
    · exact some_le_some.2 (le_of_pred_lt <| some_lt_some.1 h)
      

/-! #### Adding a `⊤` to a `no_max_order` -/


instance WithTop.succOrderOfNoMaxOrder [PartialOrderₓ α] [NoMaxOrder α] [SuccOrder α] : SuccOrder (WithTop α) where
  succ := fun a =>
    match a with
    | ⊤ => ⊤
    | some a => some (succ a)
  le_succ := fun a => by
    cases a
    · exact le_top
      
    · exact some_le_some.2 (le_succ a)
      
  maximal_of_succ_le := fun a ha b h => by
    cases a
    · exact not_top_lt h
      
    · exact not_exists.2 (maximal_of_succ_le (some_le_some.1 ha)) (exists_gt a)
      
  succ_le_of_lt := fun a b h => by
    cases a
    · exact (not_top_lt h).elim
      
    cases b
    · exact le_top
      
    · exact some_le_some.2 (succ_le_of_lt <| some_lt_some.1 h)
      
  le_of_lt_succ := fun a b h => by
    cases a
    · exact (not_top_lt h).elim
      
    cases b
    · exact le_top
      
    · exact some_le_some.2 (le_of_lt_succ <| some_lt_some.1 h)
      

instance [PartialOrderₓ α] [NoMaxOrder α] [hα : Nonempty α] : IsEmpty (PredOrder (WithTop α)) :=
  ⟨by
    intro
    set b := pred (⊤ : WithTop α) with h
    cases' pred (⊤ : WithTop α) with a ha <;> change b with pred ⊤ at h
    · exact hα.elim fun a => minimal_of_le_pred h.ge (coe_lt_top a)
      
    · obtain ⟨c, hc⟩ := exists_gt a
      rw [← some_lt_some, ← h] at hc
      exact (le_of_pred_lt hc).not_lt (some_lt_none _)
      ⟩

end WithTop

section WithBot

open WithBot

/-! #### Adding a `⊥` to a `bot_order` -/


instance [Preorderₓ α] [OrderBot α] [SuccOrder α] : SuccOrder (WithBot α) where
  succ := fun a =>
    match a with
    | ⊥ => some ⊥
    | some a => some (succ a)
  le_succ := fun a =>
    match a with
    | ⊥ => bot_le
    | some a => some_le_some.2 (le_succ a)
  maximal_of_succ_le := fun a ha b h => by
    cases a
    · exact (none_lt_some (⊥ : α)).not_le ha
      
    cases b
    · exact not_lt_bot h
      
    · exact maximal_of_succ_le (some_le_some.1 ha) (some_lt_some.1 h)
      
  succ_le_of_lt := fun a b h => by
    cases b
    · exact (not_lt_bot h).elim
      
    cases a
    · exact some_le_some.2 bot_le
      
    · exact some_le_some.2 (succ_le_of_lt <| some_lt_some.1 h)
      
  le_of_lt_succ := fun a b h => by
    cases a
    · exact bot_le
      
    cases b
    · exact (not_lt_bot <| some_lt_some.1 h).elim
      
    · exact some_le_some.2 (le_of_lt_succ <| some_lt_some.1 h)
      

instance [DecidableEq α] [PartialOrderₓ α] [OrderBot α] [PredOrder α] : PredOrder (WithBot α) where
  pred := fun a =>
    match a with
    | ⊥ => ⊥
    | some a => ite (a = ⊥) ⊥ (some (pred a))
  pred_le := fun a => by
    cases a
    · exact bot_le
      
    change (ite _ _ _ : WithBot α) ≤ some a
    split_ifs
    · exact bot_le
      
    · exact some_le_some.2 (pred_le a)
      
  minimal_of_le_pred := fun a ha b h => by
    cases a
    · exact not_lt_bot h
      
    change ((· ≤ ·) : WithBot α → WithBot α → Prop) _ (ite _ _ _) at ha
    split_ifs  at ha with ha'
    · exact not_lt_bot (h.trans_le ha)
      
    · rw [some_le_some, le_pred_iff_eq_bot] at ha
      exact ha' ha
      
  le_pred_of_lt := fun a b h => by
    cases a
    · exact bot_le
      
    cases b
    · exact (not_lt_bot h).elim
      
    rw [some_lt_some] at h
    change ((· ≤ ·) : WithBot α → WithBot α → Prop) _ (ite _ _ _)
    split_ifs with hb
    · rw [hb] at h
      exact (not_lt_bot h).elim
      
    · exact some_le_some.2 (le_pred_of_lt h)
      
  le_of_pred_lt := fun a b h => by
    cases b
    · exact (not_lt_bot h).elim
      
    cases a
    · exact bot_le
      
    change ((· < ·) : WithBot α → WithBot α → Prop) (ite _ _ _) _ at h
    rw [some_le_some]
    split_ifs  at h with ha
    · rw [ha]
      exact bot_le
      
    · exact le_of_pred_lt (some_lt_some.1 h)
      

/-! #### Adding a `⊥` to a `no_min_order` -/


instance [PartialOrderₓ α] [NoMinOrder α] [hα : Nonempty α] : IsEmpty (SuccOrder (WithBot α)) :=
  ⟨by
    intro
    set b : WithBot α := succ ⊥ with h
    cases' succ (⊥ : WithBot α) with a ha <;> change b with succ ⊥ at h
    · exact hα.elim fun a => maximal_of_succ_le h.le (bot_lt_coe a)
      
    · obtain ⟨c, hc⟩ := exists_lt a
      rw [← some_lt_some, ← h] at hc
      exact (le_of_lt_succ hc).not_lt (none_lt_some _)
      ⟩

instance WithBot.predOrderOfNoMinOrder [PartialOrderₓ α] [NoMinOrder α] [PredOrder α] : PredOrder (WithBot α) where
  pred := fun a =>
    match a with
    | ⊥ => ⊥
    | some a => some (pred a)
  pred_le := fun a => by
    cases a
    · exact bot_le
      
    · exact some_le_some.2 (pred_le a)
      
  minimal_of_le_pred := fun a ha b h => by
    cases a
    · exact not_lt_bot h
      
    · exact not_exists.2 (minimal_of_le_pred (some_le_some.1 ha)) (exists_lt a)
      
  le_pred_of_lt := fun a b h => by
    cases b
    · exact (not_lt_bot h).elim
      
    cases a
    · exact bot_le
      
    · exact some_le_some.2 (le_pred_of_lt <| some_lt_some.1 h)
      
  le_of_pred_lt := fun a b h => by
    cases b
    · exact (not_lt_bot h).elim
      
    cases a
    · exact bot_le
      
    · exact some_le_some.2 (le_of_pred_lt <| some_lt_some.1 h)
      

end WithBot

/-! ### Archimedeanness -/


/-- A `succ_order` is succ-archimedean if one can go from any two comparable elements by iterating
`succ` -/
class IsSuccArchimedean (α : Type _) [Preorderₓ α] [SuccOrder α] : Prop where
  exists_succ_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, (succ^[n]) a = b

/-- A `pred_order` is pred-archimedean if one can go from any two comparable elements by iterating
`pred` -/
class IsPredArchimedean (α : Type _) [Preorderₓ α] [PredOrder α] : Prop where
  exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, (pred^[n]) b = a

export IsSuccArchimedean (exists_succ_iterate_of_le)

export IsPredArchimedean (exists_pred_iterate_of_le)

section Preorderₓ

variable [Preorderₓ α]

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

instance : IsPredArchimedean (OrderDual α) where
  exists_pred_iterate_of_le := fun a b h => by
    convert @exists_succ_iterate_of_le α _ _ _ _ _ h

theorem LE.le.exists_succ_iterate (h : a ≤ b) : ∃ n, (succ^[n]) a = b :=
  exists_succ_iterate_of_le h

theorem exists_succ_iterate_iff_le : (∃ n, (succ^[n]) a = b) ↔ a ≤ b := by
  refine' ⟨_, exists_succ_iterate_of_le⟩
  rintro ⟨n, rfl⟩
  exact id_le_iterate_of_id_le le_succ n a

/-- Induction principle on a type with a `succ_order` for all elements above a given element `m`. -/
@[elab_as_eliminator]
theorem Succ.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (succ n)) ⦃n : α⦄ (hmn : m ≤ n) : P n :=
  by
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate
  clear hmn
  induction' n with n ih
  · exact h0
    
  · rw [Function.iterate_succ_apply']
    exact h1 _ (id_le_iterate_of_id_le le_succ n m) ih
    

theorem Succ.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) {a b : α} (h : a ≤ b) : p a ↔ p b := by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  exact iterate.rec (fun b => p a ↔ p b) (fun c hc => hc.trans (hsucc _)) Iff.rfl n

end SuccOrder

section PredOrder

variable [PredOrder α] [IsPredArchimedean α] {a b : α}

instance : IsSuccArchimedean (OrderDual α) where
  exists_succ_iterate_of_le := fun a b h => by
    convert @exists_pred_iterate_of_le α _ _ _ _ _ h

theorem LE.le.exists_pred_iterate (h : a ≤ b) : ∃ n, (pred^[n]) b = a :=
  exists_pred_iterate_of_le h

theorem exists_pred_iterate_iff_le : (∃ n, (pred^[n]) b = a) ↔ a ≤ b :=
  @exists_succ_iterate_iff_le (OrderDual α) _ _ _ _ _

/-- Induction principle on a type with a `pred_order` for all elements below a given element `m`. -/
@[elab_as_eliminator]
theorem Pred.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, n ≤ m → P n → P (pred n)) ⦃n : α⦄ (hmn : n ≤ m) : P n :=
  @Succ.rec (OrderDual α) _ _ _ _ _ h0 h1 _ hmn

theorem Pred.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) {a b : α} (h : a ≤ b) : p a ↔ p b :=
  (@Succ.rec_iff (OrderDual α) _ _ _ _ hsucc _ _ h).symm

end PredOrder

end Preorderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

theorem exists_succ_iterate_or : (∃ n, (succ^[n]) a = b) ∨ ∃ n, (succ^[n]) b = a :=
  (le_totalₓ a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le

theorem Succ.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) (a b : α) : p a ↔ p b :=
  (le_totalₓ a b).elim (Succ.rec_iff hsucc) fun h => (Succ.rec_iff hsucc h).symm

end SuccOrder

section PredOrder

variable [PredOrder α] [IsPredArchimedean α] {a b : α}

theorem exists_pred_iterate_or : (∃ n, (pred^[n]) b = a) ∨ ∃ n, (pred^[n]) a = b :=
  (le_totalₓ a b).imp exists_pred_iterate_of_le exists_pred_iterate_of_le

theorem Pred.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) (a b : α) : p a ↔ p b :=
  (le_totalₓ a b).elim (Pred.rec_iff hsucc) fun h => (Pred.rec_iff hsucc h).symm

end PredOrder

end LinearOrderₓ

section OrderBot

variable [Preorderₓ α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]

theorem Succ.rec_bot (p : α → Prop) (hbot : p ⊥) (hsucc : ∀ a, p a → p (succ a)) (a : α) : p a :=
  Succ.rec hbot (fun x _ h => hsucc x h) (bot_le : ⊥ ≤ a)

end OrderBot

section OrderTop

variable [Preorderₓ α] [OrderTop α] [PredOrder α] [IsPredArchimedean α]

theorem Pred.rec_top (p : α → Prop) (htop : p ⊤) (hpred : ∀ a, p a → p (pred a)) (a : α) : p a :=
  Pred.rec htop (fun x _ h => hpred x h) (le_top : a ≤ ⊤)

end OrderTop

