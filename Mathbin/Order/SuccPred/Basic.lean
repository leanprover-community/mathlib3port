/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.succ_pred.basic
! leanprover-community/mathlib commit 0111834459f5d7400215223ea95ae38a1265a907
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteLattice
import Mathbin.Order.Cover
import Mathbin.Order.Iterate

/-!
# Successor and predecessor

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines successor and predecessor orders. `succ a`, the successor of an element `a : α` is
the least element greater than `a`. `pred a` is the greatest element less than `a`. Typical examples
include `ℕ`, `ℤ`, `ℕ+`, `fin n`, but also `enat`, the lexicographic order of a successor/predecessor
order...

## Typeclasses

* `succ_order`: Order equipped with a sensible successor function.
* `pred_order`: Order equipped with a sensible predecessor function.
* `is_succ_archimedean`: `succ_order` where `succ` iterated to an element gives all the greater
  ones.
* `is_pred_archimedean`: `pred_order` where `pred` iterated to an element gives all the smaller
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
`max_of_succ_le`).
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


open Function OrderDual Set

variable {α : Type _}

#print SuccOrder /-
/-- Order equipped with a sensible successor function. -/
@[ext]
class SuccOrder (α : Type _) [Preorder α] where
  succ : α → α
  le_succ : ∀ a, a ≤ succ a
  max_of_succ_le {a} : succ a ≤ a → IsMax a
  succ_le_of_lt {a b} : a < b → succ a ≤ b
  le_of_lt_succ {a b} : a < succ b → a ≤ b
#align succ_order SuccOrder
-/

#print PredOrder /-
/-- Order equipped with a sensible predecessor function. -/
@[ext]
class PredOrder (α : Type _) [Preorder α] where
  pred : α → α
  pred_le : ∀ a, pred a ≤ a
  min_of_le_pred {a} : a ≤ pred a → IsMin a
  le_pred_of_lt {a b} : a < b → a ≤ pred b
  le_of_pred_lt {a b} : pred a < b → a ≤ b
#align pred_order PredOrder
-/

instance [Preorder α] [SuccOrder α] : PredOrder αᵒᵈ
    where
  pred := toDual ∘ SuccOrder.succ ∘ ofDual
  pred_le := SuccOrder.le_succ
  min_of_le_pred _ := SuccOrder.max_of_succ_le
  le_pred_of_lt a b h := SuccOrder.succ_le_of_lt h
  le_of_pred_lt a b := SuccOrder.le_of_lt_succ

instance [Preorder α] [PredOrder α] : SuccOrder αᵒᵈ
    where
  succ := toDual ∘ PredOrder.pred ∘ ofDual
  le_succ := PredOrder.pred_le
  max_of_succ_le _ := PredOrder.min_of_le_pred
  succ_le_of_lt a b h := PredOrder.le_pred_of_lt h
  le_of_lt_succ a b := PredOrder.le_of_pred_lt

section Preorder

variable [Preorder α]

#print SuccOrder.ofSuccLeIffOfLeLtSucc /-
/-- A constructor for `succ_order α` usable when `α` has no maximal element. -/
def SuccOrder.ofSuccLeIffOfLeLtSucc (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b)
    (hle_of_lt_succ : ∀ {a b}, a < succ b → a ≤ b) : SuccOrder α :=
  { succ
    le_succ := fun a => (hsucc_le_iff.1 le_rfl).le
    max_of_succ_le := fun a ha => (lt_irrefl a <| hsucc_le_iff.1 ha).elim
    succ_le_of_lt := fun a b => hsucc_le_iff.2
    le_of_lt_succ := fun a b => hle_of_lt_succ }
#align succ_order.of_succ_le_iff_of_le_lt_succ SuccOrder.ofSuccLeIffOfLeLtSucc
-/

#print PredOrder.ofLePredIffOfPredLePred /-
/-- A constructor for `pred_order α` usable when `α` has no minimal element. -/
def PredOrder.ofLePredIffOfPredLePred (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b)
    (hle_of_pred_lt : ∀ {a b}, pred a < b → a ≤ b) : PredOrder α :=
  { pred
    pred_le := fun a => (hle_pred_iff.1 le_rfl).le
    min_of_le_pred := fun a ha => (lt_irrefl a <| hle_pred_iff.1 ha).elim
    le_pred_of_lt := fun a b => hle_pred_iff.2
    le_of_pred_lt := fun a b => hle_of_pred_lt }
#align pred_order.of_le_pred_iff_of_pred_le_pred PredOrder.ofLePredIffOfPredLePred
-/

end Preorder

section LinearOrder

variable [LinearOrder α]

#print SuccOrder.ofCore /-
/-- A constructor for `succ_order α` for `α` a linear order. -/
@[simps]
def SuccOrder.ofCore (succ : α → α) (hn : ∀ {a}, ¬IsMax a → ∀ b, a < b ↔ succ a ≤ b)
    (hm : ∀ a, IsMax a → succ a = a) : SuccOrder α :=
  { succ
    succ_le_of_lt := fun a b => by_cases (fun h hab => (hm a h).symm ▸ hab.le) fun h => (hn h b).mp
    le_succ := fun a =>
      by_cases (fun h => (hm a h).symm.le) fun h => le_of_lt <| by simpa using (hn h a).Not
    le_of_lt_succ := fun a b hab =>
      by_cases (fun h => hm b h ▸ hab.le) fun h => by simpa [hab] using (hn h a).Not
    max_of_succ_le := fun a => not_imp_not.mp fun h => by simpa using (hn h a).Not }
#align succ_order.of_core SuccOrder.ofCore
-/

#print PredOrder.ofCore /-
/-- A constructor for `pred_order α` for `α` a linear order. -/
@[simps]
def PredOrder.ofCore {α} [LinearOrder α] (pred : α → α)
    (hn : ∀ {a}, ¬IsMin a → ∀ b, b ≤ pred a ↔ b < a) (hm : ∀ a, IsMin a → pred a = a) :
    PredOrder α :=
  { pred
    le_pred_of_lt := fun a b => by_cases (fun h hab => (hm b h).symm ▸ hab.le) fun h => (hn h a).mpr
    pred_le := fun a =>
      by_cases (fun h => (hm a h).le) fun h => le_of_lt <| by simpa using (hn h a).Not
    le_of_pred_lt := fun a b hab =>
      by_cases (fun h => hm a h ▸ hab.le) fun h => by simpa [hab] using (hn h b).Not
    min_of_le_pred := fun a => not_imp_not.mp fun h => by simpa using (hn h a).Not }
#align pred_order.of_core PredOrder.ofCore
-/

#print SuccOrder.ofSuccLeIff /-
/-- A constructor for `succ_order α` usable when `α` is a linear order with no maximal element. -/
def SuccOrder.ofSuccLeIff (succ : α → α) (hsucc_le_iff : ∀ {a b}, succ a ≤ b ↔ a < b) :
    SuccOrder α :=
  { succ
    le_succ := fun a => (hsucc_le_iff.1 le_rfl).le
    max_of_succ_le := fun a ha => (lt_irrefl a <| hsucc_le_iff.1 ha).elim
    succ_le_of_lt := fun a b => hsucc_le_iff.2
    le_of_lt_succ := fun a b h => le_of_not_lt ((not_congr hsucc_le_iff).1 h.not_le) }
#align succ_order.of_succ_le_iff SuccOrder.ofSuccLeIff
-/

#print PredOrder.ofLePredIff /-
/-- A constructor for `pred_order α` usable when `α` is a linear order with no minimal element. -/
def PredOrder.ofLePredIff (pred : α → α) (hle_pred_iff : ∀ {a b}, a ≤ pred b ↔ a < b) :
    PredOrder α :=
  { pred
    pred_le := fun a => (hle_pred_iff.1 le_rfl).le
    min_of_le_pred := fun a ha => (lt_irrefl a <| hle_pred_iff.1 ha).elim
    le_pred_of_lt := fun a b => hle_pred_iff.2
    le_of_pred_lt := fun a b h => le_of_not_lt ((not_congr hle_pred_iff).1 h.not_le) }
#align pred_order.of_le_pred_iff PredOrder.ofLePredIff
-/

end LinearOrder

/-! ### Successor order -/


namespace Order

section Preorder

variable [Preorder α] [SuccOrder α] {a b : α}

#print Order.succ /-
/-- The successor of an element. If `a` is not maximal, then `succ a` is the least element greater
than `a`. If `a` is maximal, then `succ a = a`. -/
def succ : α → α :=
  SuccOrder.succ
#align order.succ Order.succ
-/

#print Order.le_succ /-
theorem le_succ : ∀ a : α, a ≤ succ a :=
  SuccOrder.le_succ
#align order.le_succ Order.le_succ
-/

#print Order.max_of_succ_le /-
theorem max_of_succ_le {a : α} : succ a ≤ a → IsMax a :=
  SuccOrder.max_of_succ_le
#align order.max_of_succ_le Order.max_of_succ_le
-/

#print Order.succ_le_of_lt /-
theorem succ_le_of_lt {a b : α} : a < b → succ a ≤ b :=
  SuccOrder.succ_le_of_lt
#align order.succ_le_of_lt Order.succ_le_of_lt
-/

#print Order.le_of_lt_succ /-
theorem le_of_lt_succ {a b : α} : a < succ b → a ≤ b :=
  SuccOrder.le_of_lt_succ
#align order.le_of_lt_succ Order.le_of_lt_succ
-/

#print Order.succ_le_iff_isMax /-
@[simp]
theorem succ_le_iff_isMax : succ a ≤ a ↔ IsMax a :=
  ⟨max_of_succ_le, fun h => h <| le_succ _⟩
#align order.succ_le_iff_is_max Order.succ_le_iff_isMax
-/

#print Order.lt_succ_iff_not_isMax /-
@[simp]
theorem lt_succ_iff_not_isMax : a < succ a ↔ ¬IsMax a :=
  ⟨not_isMax_of_lt, fun ha => (le_succ a).lt_of_not_le fun h => ha <| max_of_succ_le h⟩
#align order.lt_succ_iff_not_is_max Order.lt_succ_iff_not_isMax
-/

alias lt_succ_iff_not_is_max ↔ _ lt_succ_of_not_is_max
#align order.lt_succ_of_not_is_max Order.lt_succ_of_not_isMax

#print Order.wcovby_succ /-
theorem wcovby_succ (a : α) : a ⩿ succ a :=
  ⟨le_succ a, fun b hb => (succ_le_of_lt hb).not_lt⟩
#align order.wcovby_succ Order.wcovby_succ
-/

#print Order.covby_succ_of_not_isMax /-
theorem covby_succ_of_not_isMax (h : ¬IsMax a) : a ⋖ succ a :=
  (wcovby_succ a).covby_of_lt <| lt_succ_of_not_isMax h
#align order.covby_succ_of_not_is_max Order.covby_succ_of_not_isMax
-/

#print Order.lt_succ_iff_of_not_isMax /-
theorem lt_succ_iff_of_not_isMax (ha : ¬IsMax a) : b < succ a ↔ b ≤ a :=
  ⟨le_of_lt_succ, fun h => h.trans_lt <| lt_succ_of_not_isMax ha⟩
#align order.lt_succ_iff_of_not_is_max Order.lt_succ_iff_of_not_isMax
-/

#print Order.succ_le_iff_of_not_isMax /-
theorem succ_le_iff_of_not_isMax (ha : ¬IsMax a) : succ a ≤ b ↔ a < b :=
  ⟨(lt_succ_of_not_isMax ha).trans_le, succ_le_of_lt⟩
#align order.succ_le_iff_of_not_is_max Order.succ_le_iff_of_not_isMax
-/

#print Order.succ_lt_succ_iff_of_not_isMax /-
theorem succ_lt_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) : succ a < succ b ↔ a < b :=
  by rw [lt_succ_iff_of_not_is_max hb, succ_le_iff_of_not_is_max ha]
#align order.succ_lt_succ_iff_of_not_is_max Order.succ_lt_succ_iff_of_not_isMax
-/

#print Order.succ_le_succ_iff_of_not_isMax /-
theorem succ_le_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) : succ a ≤ succ b ↔ a ≤ b :=
  by rw [succ_le_iff_of_not_is_max ha, lt_succ_iff_of_not_is_max hb]
#align order.succ_le_succ_iff_of_not_is_max Order.succ_le_succ_iff_of_not_isMax
-/

#print Order.succ_le_succ /-
@[simp, mono]
theorem succ_le_succ (h : a ≤ b) : succ a ≤ succ b :=
  by
  by_cases hb : IsMax b
  · by_cases hba : b ≤ a
    · exact (hb <| hba.trans <| le_succ _).trans (le_succ _)
    · exact succ_le_of_lt ((h.lt_of_not_le hba).trans_le <| le_succ b)
  · rwa [succ_le_iff_of_not_is_max fun ha => hb <| ha.mono h, lt_succ_iff_of_not_is_max hb]
#align order.succ_le_succ Order.succ_le_succ
-/

#print Order.succ_mono /-
theorem succ_mono : Monotone (succ : α → α) := fun a b => succ_le_succ
#align order.succ_mono Order.succ_mono
-/

#print Order.le_succ_iterate /-
theorem le_succ_iterate (k : ℕ) (x : α) : x ≤ (succ^[k]) x :=
  by
  conv_lhs => rw [(by simp only [Function.iterate_id, id.def] : x = (id^[k]) x)]
  exact Monotone.le_iterate_of_le succ_mono le_succ k x
#align order.le_succ_iterate Order.le_succ_iterate
-/

#print Order.isMax_iterate_succ_of_eq_of_lt /-
theorem isMax_iterate_succ_of_eq_of_lt {n m : ℕ} (h_eq : (succ^[n]) a = (succ^[m]) a)
    (h_lt : n < m) : IsMax ((succ^[n]) a) :=
  by
  refine' max_of_succ_le (le_trans _ h_eq.symm.le)
  have : succ ((succ^[n]) a) = (succ^[n + 1]) a := by rw [Function.iterate_succ']
  rw [this]
  have h_le : n + 1 ≤ m := Nat.succ_le_of_lt h_lt
  exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ a) h_le
#align order.is_max_iterate_succ_of_eq_of_lt Order.isMax_iterate_succ_of_eq_of_lt
-/

#print Order.isMax_iterate_succ_of_eq_of_ne /-
theorem isMax_iterate_succ_of_eq_of_ne {n m : ℕ} (h_eq : (succ^[n]) a = (succ^[m]) a)
    (h_ne : n ≠ m) : IsMax ((succ^[n]) a) :=
  by
  cases le_total n m
  · exact is_max_iterate_succ_of_eq_of_lt h_eq (lt_of_le_of_ne h h_ne)
  · rw [h_eq]
    exact is_max_iterate_succ_of_eq_of_lt h_eq.symm (lt_of_le_of_ne h h_ne.symm)
#align order.is_max_iterate_succ_of_eq_of_ne Order.isMax_iterate_succ_of_eq_of_ne
-/

#print Order.Iio_succ_of_not_isMax /-
theorem Iio_succ_of_not_isMax (ha : ¬IsMax a) : Iio (succ a) = Iic a :=
  Set.ext fun x => lt_succ_iff_of_not_isMax ha
#align order.Iio_succ_of_not_is_max Order.Iio_succ_of_not_isMax
-/

#print Order.Ici_succ_of_not_isMax /-
theorem Ici_succ_of_not_isMax (ha : ¬IsMax a) : Ici (succ a) = Ioi a :=
  Set.ext fun x => succ_le_iff_of_not_isMax ha
#align order.Ici_succ_of_not_is_max Order.Ici_succ_of_not_isMax
-/

#print Order.Ico_succ_right_of_not_isMax /-
theorem Ico_succ_right_of_not_isMax (hb : ¬IsMax b) : Ico a (succ b) = Icc a b := by
  rw [← Ici_inter_Iio, Iio_succ_of_not_is_max hb, Ici_inter_Iic]
#align order.Ico_succ_right_of_not_is_max Order.Ico_succ_right_of_not_isMax
-/

#print Order.Ioo_succ_right_of_not_isMax /-
theorem Ioo_succ_right_of_not_isMax (hb : ¬IsMax b) : Ioo a (succ b) = Ioc a b := by
  rw [← Ioi_inter_Iio, Iio_succ_of_not_is_max hb, Ioi_inter_Iic]
#align order.Ioo_succ_right_of_not_is_max Order.Ioo_succ_right_of_not_isMax
-/

#print Order.Icc_succ_left_of_not_isMax /-
theorem Icc_succ_left_of_not_isMax (ha : ¬IsMax a) : Icc (succ a) b = Ioc a b := by
  rw [← Ici_inter_Iic, Ici_succ_of_not_is_max ha, Ioi_inter_Iic]
#align order.Icc_succ_left_of_not_is_max Order.Icc_succ_left_of_not_isMax
-/

#print Order.Ico_succ_left_of_not_isMax /-
theorem Ico_succ_left_of_not_isMax (ha : ¬IsMax a) : Ico (succ a) b = Ioo a b := by
  rw [← Ici_inter_Iio, Ici_succ_of_not_is_max ha, Ioi_inter_Iio]
#align order.Ico_succ_left_of_not_is_max Order.Ico_succ_left_of_not_isMax
-/

section NoMaxOrder

variable [NoMaxOrder α]

#print Order.lt_succ /-
theorem lt_succ (a : α) : a < succ a :=
  lt_succ_of_not_isMax <| not_isMax a
#align order.lt_succ Order.lt_succ
-/

#print Order.lt_succ_iff /-
@[simp]
theorem lt_succ_iff : a < succ b ↔ a ≤ b :=
  lt_succ_iff_of_not_isMax <| not_isMax b
#align order.lt_succ_iff Order.lt_succ_iff
-/

#print Order.succ_le_iff /-
@[simp]
theorem succ_le_iff : succ a ≤ b ↔ a < b :=
  succ_le_iff_of_not_isMax <| not_isMax a
#align order.succ_le_iff Order.succ_le_iff
-/

#print Order.succ_le_succ_iff /-
theorem succ_le_succ_iff : succ a ≤ succ b ↔ a ≤ b := by simp
#align order.succ_le_succ_iff Order.succ_le_succ_iff
-/

#print Order.succ_lt_succ_iff /-
theorem succ_lt_succ_iff : succ a < succ b ↔ a < b := by simp
#align order.succ_lt_succ_iff Order.succ_lt_succ_iff
-/

alias succ_le_succ_iff ↔ le_of_succ_le_succ _
#align order.le_of_succ_le_succ Order.le_of_succ_le_succ

alias succ_lt_succ_iff ↔ lt_of_succ_lt_succ succ_lt_succ
#align order.lt_of_succ_lt_succ Order.lt_of_succ_lt_succ
#align order.succ_lt_succ Order.succ_lt_succ

#print Order.succ_strictMono /-
theorem succ_strictMono : StrictMono (succ : α → α) := fun a b => succ_lt_succ
#align order.succ_strict_mono Order.succ_strictMono
-/

#print Order.covby_succ /-
theorem covby_succ (a : α) : a ⋖ succ a :=
  covby_succ_of_not_isMax <| not_isMax a
#align order.covby_succ Order.covby_succ
-/

#print Order.Iio_succ /-
@[simp]
theorem Iio_succ (a : α) : Iio (succ a) = Iic a :=
  Iio_succ_of_not_isMax <| not_isMax _
#align order.Iio_succ Order.Iio_succ
-/

#print Order.Ici_succ /-
@[simp]
theorem Ici_succ (a : α) : Ici (succ a) = Ioi a :=
  Ici_succ_of_not_isMax <| not_isMax _
#align order.Ici_succ Order.Ici_succ
-/

#print Order.Ico_succ_right /-
@[simp]
theorem Ico_succ_right (a b : α) : Ico a (succ b) = Icc a b :=
  Ico_succ_right_of_not_isMax <| not_isMax _
#align order.Ico_succ_right Order.Ico_succ_right
-/

#print Order.Ioo_succ_right /-
@[simp]
theorem Ioo_succ_right (a b : α) : Ioo a (succ b) = Ioc a b :=
  Ioo_succ_right_of_not_isMax <| not_isMax _
#align order.Ioo_succ_right Order.Ioo_succ_right
-/

#print Order.Icc_succ_left /-
@[simp]
theorem Icc_succ_left (a b : α) : Icc (succ a) b = Ioc a b :=
  Icc_succ_left_of_not_isMax <| not_isMax _
#align order.Icc_succ_left Order.Icc_succ_left
-/

#print Order.Ico_succ_left /-
@[simp]
theorem Ico_succ_left (a b : α) : Ico (succ a) b = Ioo a b :=
  Ico_succ_left_of_not_isMax <| not_isMax _
#align order.Ico_succ_left Order.Ico_succ_left
-/

end NoMaxOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [SuccOrder α] {a b : α}

#print Order.succ_eq_iff_isMax /-
@[simp]
theorem succ_eq_iff_isMax : succ a = a ↔ IsMax a :=
  ⟨fun h => max_of_succ_le h.le, fun h => h.eq_of_ge <| le_succ _⟩
#align order.succ_eq_iff_is_max Order.succ_eq_iff_isMax
-/

alias succ_eq_iff_is_max ↔ _ _root_.is_max.succ_eq
#align is_max.succ_eq IsMax.succ_eq

#print Order.succ_eq_succ_iff_of_not_isMax /-
theorem succ_eq_succ_iff_of_not_isMax (ha : ¬IsMax a) (hb : ¬IsMax b) : succ a = succ b ↔ a = b :=
  by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, succ_le_succ_iff_of_not_is_max ha hb,
    succ_lt_succ_iff_of_not_is_max ha hb]
#align order.succ_eq_succ_iff_of_not_is_max Order.succ_eq_succ_iff_of_not_isMax
-/

#print Order.le_le_succ_iff /-
theorem le_le_succ_iff : a ≤ b ∧ b ≤ succ a ↔ b = a ∨ b = succ a :=
  by
  refine'
    ⟨fun h =>
      or_iff_not_imp_left.2 fun hba : b ≠ a =>
        h.2.antisymm (succ_le_of_lt <| h.1.lt_of_ne <| hba.symm),
      _⟩
  rintro (rfl | rfl)
  · exact ⟨le_rfl, le_succ b⟩
  · exact ⟨le_succ a, le_rfl⟩
#align order.le_le_succ_iff Order.le_le_succ_iff
-/

#print Covby.succ_eq /-
theorem Covby.succ_eq (h : a ⋖ b) : succ a = b :=
  (succ_le_of_lt h.lt).eq_of_not_lt fun h' => h.2 (lt_succ_of_not_isMax h.lt.not_isMax) h'
#align covby.succ_eq Covby.succ_eq
-/

#print Wcovby.le_succ /-
theorem Wcovby.le_succ (h : a ⩿ b) : b ≤ succ a :=
  by
  obtain h | rfl := h.covby_or_eq
  · exact h.succ_eq.ge
  · exact le_succ _
#align wcovby.le_succ Wcovby.le_succ
-/

#print Order.le_succ_iff_eq_or_le /-
theorem le_succ_iff_eq_or_le : a ≤ succ b ↔ a = succ b ∨ a ≤ b :=
  by
  by_cases hb : IsMax b
  · rw [hb.succ_eq, or_iff_right_of_imp le_of_eq]
  · rw [← lt_succ_iff_of_not_is_max hb, le_iff_eq_or_lt]
#align order.le_succ_iff_eq_or_le Order.le_succ_iff_eq_or_le
-/

#print Order.lt_succ_iff_eq_or_lt_of_not_isMax /-
theorem lt_succ_iff_eq_or_lt_of_not_isMax (hb : ¬IsMax b) : a < succ b ↔ a = b ∨ a < b :=
  (lt_succ_iff_of_not_isMax hb).trans le_iff_eq_or_lt
#align order.lt_succ_iff_eq_or_lt_of_not_is_max Order.lt_succ_iff_eq_or_lt_of_not_isMax
-/

#print Order.Iic_succ /-
theorem Iic_succ (a : α) : Iic (succ a) = insert (succ a) (Iic a) :=
  ext fun _ => le_succ_iff_eq_or_le
#align order.Iic_succ Order.Iic_succ
-/

#print Order.Icc_succ_right /-
theorem Icc_succ_right (h : a ≤ succ b) : Icc a (succ b) = insert (succ b) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ici.2 h)]
#align order.Icc_succ_right Order.Icc_succ_right
-/

#print Order.Ioc_succ_right /-
theorem Ioc_succ_right (h : a < succ b) : Ioc a (succ b) = insert (succ b) (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Iic_succ, inter_insert_of_mem (mem_Ioi.2 h)]
#align order.Ioc_succ_right Order.Ioc_succ_right
-/

#print Order.Iio_succ_eq_insert_of_not_isMax /-
theorem Iio_succ_eq_insert_of_not_isMax (h : ¬IsMax a) : Iio (succ a) = insert a (Iio a) :=
  ext fun _ => lt_succ_iff_eq_or_lt_of_not_isMax h
#align order.Iio_succ_eq_insert_of_not_is_max Order.Iio_succ_eq_insert_of_not_isMax
-/

#print Order.Ico_succ_right_eq_insert_of_not_isMax /-
theorem Ico_succ_right_eq_insert_of_not_isMax (h₁ : a ≤ b) (h₂ : ¬IsMax b) :
    Ico a (succ b) = insert b (Ico a b) := by
  simp_rw [← Iio_inter_Ici, Iio_succ_eq_insert_of_not_is_max h₂, insert_inter_of_mem (mem_Ici.2 h₁)]
#align order.Ico_succ_right_eq_insert_of_not_is_max Order.Ico_succ_right_eq_insert_of_not_isMax
-/

#print Order.Ioo_succ_right_eq_insert_of_not_isMax /-
theorem Ioo_succ_right_eq_insert_of_not_isMax (h₁ : a < b) (h₂ : ¬IsMax b) :
    Ioo a (succ b) = insert b (Ioo a b) := by
  simp_rw [← Iio_inter_Ioi, Iio_succ_eq_insert_of_not_is_max h₂, insert_inter_of_mem (mem_Ioi.2 h₁)]
#align order.Ioo_succ_right_eq_insert_of_not_is_max Order.Ioo_succ_right_eq_insert_of_not_isMax
-/

section NoMaxOrder

variable [NoMaxOrder α]

#print Order.succ_eq_succ_iff /-
@[simp]
theorem succ_eq_succ_iff : succ a = succ b ↔ a = b :=
  succ_eq_succ_iff_of_not_isMax (not_isMax a) (not_isMax b)
#align order.succ_eq_succ_iff Order.succ_eq_succ_iff
-/

#print Order.succ_injective /-
theorem succ_injective : Injective (succ : α → α) := fun a b => succ_eq_succ_iff.1
#align order.succ_injective Order.succ_injective
-/

#print Order.succ_ne_succ_iff /-
theorem succ_ne_succ_iff : succ a ≠ succ b ↔ a ≠ b :=
  succ_injective.ne_iff
#align order.succ_ne_succ_iff Order.succ_ne_succ_iff
-/

alias succ_ne_succ_iff ↔ _ succ_ne_succ
#align order.succ_ne_succ Order.succ_ne_succ

#print Order.lt_succ_iff_eq_or_lt /-
theorem lt_succ_iff_eq_or_lt : a < succ b ↔ a = b ∨ a < b :=
  lt_succ_iff.trans le_iff_eq_or_lt
#align order.lt_succ_iff_eq_or_lt Order.lt_succ_iff_eq_or_lt
-/

#print Order.succ_eq_iff_covby /-
theorem succ_eq_iff_covby : succ a = b ↔ a ⋖ b :=
  ⟨by
    rintro rfl
    exact covby_succ _, Covby.succ_eq⟩
#align order.succ_eq_iff_covby Order.succ_eq_iff_covby
-/

#print Order.Iio_succ_eq_insert /-
theorem Iio_succ_eq_insert (a : α) : Iio (succ a) = insert a (Iio a) :=
  Iio_succ_eq_insert_of_not_isMax <| not_isMax a
#align order.Iio_succ_eq_insert Order.Iio_succ_eq_insert
-/

#print Order.Ico_succ_right_eq_insert /-
theorem Ico_succ_right_eq_insert (h : a ≤ b) : Ico a (succ b) = insert b (Ico a b) :=
  Ico_succ_right_eq_insert_of_not_isMax h <| not_isMax b
#align order.Ico_succ_right_eq_insert Order.Ico_succ_right_eq_insert
-/

#print Order.Ioo_succ_right_eq_insert /-
theorem Ioo_succ_right_eq_insert (h : a < b) : Ioo a (succ b) = insert b (Ioo a b) :=
  Ioo_succ_right_eq_insert_of_not_isMax h <| not_isMax b
#align order.Ioo_succ_right_eq_insert Order.Ioo_succ_right_eq_insert
-/

end NoMaxOrder

section OrderTop

variable [OrderTop α]

/- warning: order.succ_top -> Order.succ_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Eq.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Eq.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))
Case conversion may be inaccurate. Consider using '#align order.succ_top Order.succ_topₓ'. -/
@[simp]
theorem succ_top : succ (⊤ : α) = ⊤ :=
  isMax_top.succ_eq
#align order.succ_top Order.succ_top

/- warning: order.succ_le_iff_eq_top -> Order.succ_le_iff_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) a) (Eq.{succ u1} α a (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) a) (Eq.{succ u1} α a (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
Case conversion may be inaccurate. Consider using '#align order.succ_le_iff_eq_top Order.succ_le_iff_eq_topₓ'. -/
@[simp]
theorem succ_le_iff_eq_top : succ a ≤ a ↔ a = ⊤ :=
  succ_le_iff_isMax.trans isMax_iff_eq_top
#align order.succ_le_iff_eq_top Order.succ_le_iff_eq_top

/- warning: order.lt_succ_iff_ne_top -> Order.lt_succ_iff_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)) (Ne.{succ u1} α a (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)) (Ne.{succ u1} α a (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
Case conversion may be inaccurate. Consider using '#align order.lt_succ_iff_ne_top Order.lt_succ_iff_ne_topₓ'. -/
@[simp]
theorem lt_succ_iff_ne_top : a < succ a ↔ a ≠ ⊤ :=
  lt_succ_iff_not_isMax.trans not_isMax_iff_ne_top
#align order.lt_succ_iff_ne_top Order.lt_succ_iff_ne_top

end OrderTop

section OrderBot

variable [OrderBot α]

/- warning: order.lt_succ_bot_iff -> Order.lt_succ_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))) (Eq.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : NoMaxOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))) (Eq.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
Case conversion may be inaccurate. Consider using '#align order.lt_succ_bot_iff Order.lt_succ_bot_iffₓ'. -/
@[simp]
theorem lt_succ_bot_iff [NoMaxOrder α] : a < succ ⊥ ↔ a = ⊥ := by rw [lt_succ_iff, le_bot_iff]
#align order.lt_succ_bot_iff Order.lt_succ_bot_iff

/- warning: order.le_succ_bot_iff -> Order.le_succ_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))) (Or (Eq.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Eq.{succ u1} α a (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))) (Or (Eq.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Eq.{succ u1} α a (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))))
Case conversion may be inaccurate. Consider using '#align order.le_succ_bot_iff Order.le_succ_bot_iffₓ'. -/
theorem le_succ_bot_iff : a ≤ succ ⊥ ↔ a = ⊥ ∨ a = succ ⊥ := by
  rw [le_succ_iff_eq_or_le, le_bot_iff, or_comm']
#align order.le_succ_bot_iff Order.le_succ_bot_iff

variable [Nontrivial α]

/- warning: order.bot_lt_succ -> Order.bot_lt_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : Nontrivial.{u1} α] (a : α), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : Nontrivial.{u1} α] (a : α), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)
Case conversion may be inaccurate. Consider using '#align order.bot_lt_succ Order.bot_lt_succₓ'. -/
theorem bot_lt_succ (a : α) : ⊥ < succ a :=
  (lt_succ_of_not_isMax not_isMax_bot).trans_le <| succ_mono bot_le
#align order.bot_lt_succ Order.bot_lt_succ

/- warning: order.succ_ne_bot -> Order.succ_ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : Nontrivial.{u1} α] (a : α), Ne.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : Nontrivial.{u1} α] (a : α), Ne.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))
Case conversion may be inaccurate. Consider using '#align order.succ_ne_bot Order.succ_ne_botₓ'. -/
theorem succ_ne_bot (a : α) : succ a ≠ ⊥ :=
  (bot_lt_succ a).ne'
#align order.succ_ne_bot Order.succ_ne_bot

end OrderBot

end PartialOrder

/-- There is at most one way to define the successors in a `partial_order`. -/
instance [PartialOrder α] : Subsingleton (SuccOrder α) :=
  ⟨by
    intro h₀ h₁
    ext a
    by_cases ha : IsMax a
    · exact (@IsMax.succ_eq _ _ h₀ _ ha).trans ha.succ_eq.symm
    · exact @Covby.succ_eq _ _ h₀ _ _ (covby_succ_of_not_is_max ha)⟩

section CompleteLattice

variable [CompleteLattice α] [SuccOrder α]

/- warning: order.succ_eq_infi -> Order.succ_eq_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))] (a : α), Eq.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) _inst_2 a) (infᵢ.{u1, succ u1} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) α (fun (b : α) => infᵢ.{u1, 0} α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b) (fun (h : LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b) => b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))] (a : α), Eq.{succ u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) _inst_2 a) (infᵢ.{u1, succ u1} α (CompleteLattice.toInfSet.{u1} α _inst_1) α (fun (b : α) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α _inst_1) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b) (fun (h : LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) a b) => b)))
Case conversion may be inaccurate. Consider using '#align order.succ_eq_infi Order.succ_eq_infᵢₓ'. -/
theorem succ_eq_infᵢ (a : α) : succ a = ⨅ (b) (h : a < b), b :=
  by
  refine' le_antisymm (le_infᵢ fun b => le_infᵢ succ_le_of_lt) _
  obtain rfl | ha := eq_or_ne a ⊤
  · rw [succ_top]
    exact le_top
  exact infᵢ₂_le _ (lt_succ_iff_ne_top.2 ha)
#align order.succ_eq_infi Order.succ_eq_infᵢ

end CompleteLattice

/-! ### Predecessor order -/


section Preorder

variable [Preorder α] [PredOrder α] {a b : α}

#print Order.pred /-
/-- The predecessor of an element. If `a` is not minimal, then `pred a` is the greatest element less
than `a`. If `a` is minimal, then `pred a = a`. -/
def pred : α → α :=
  PredOrder.pred
#align order.pred Order.pred
-/

#print Order.pred_le /-
theorem pred_le : ∀ a : α, pred a ≤ a :=
  PredOrder.pred_le
#align order.pred_le Order.pred_le
-/

#print Order.min_of_le_pred /-
theorem min_of_le_pred {a : α} : a ≤ pred a → IsMin a :=
  PredOrder.min_of_le_pred
#align order.min_of_le_pred Order.min_of_le_pred
-/

#print Order.le_pred_of_lt /-
theorem le_pred_of_lt {a b : α} : a < b → a ≤ pred b :=
  PredOrder.le_pred_of_lt
#align order.le_pred_of_lt Order.le_pred_of_lt
-/

#print Order.le_of_pred_lt /-
theorem le_of_pred_lt {a b : α} : pred a < b → a ≤ b :=
  PredOrder.le_of_pred_lt
#align order.le_of_pred_lt Order.le_of_pred_lt
-/

#print Order.le_pred_iff_isMin /-
@[simp]
theorem le_pred_iff_isMin : a ≤ pred a ↔ IsMin a :=
  ⟨min_of_le_pred, fun h => h <| pred_le _⟩
#align order.le_pred_iff_is_min Order.le_pred_iff_isMin
-/

#print Order.pred_lt_iff_not_isMin /-
@[simp]
theorem pred_lt_iff_not_isMin : pred a < a ↔ ¬IsMin a :=
  ⟨not_isMin_of_lt, fun ha => (pred_le a).lt_of_not_le fun h => ha <| min_of_le_pred h⟩
#align order.pred_lt_iff_not_is_min Order.pred_lt_iff_not_isMin
-/

alias pred_lt_iff_not_is_min ↔ _ pred_lt_of_not_is_min
#align order.pred_lt_of_not_is_min Order.pred_lt_of_not_isMin

#print Order.pred_wcovby /-
theorem pred_wcovby (a : α) : pred a ⩿ a :=
  ⟨pred_le a, fun b hb => (le_of_pred_lt hb).not_lt⟩
#align order.pred_wcovby Order.pred_wcovby
-/

#print Order.pred_covby_of_not_isMin /-
theorem pred_covby_of_not_isMin (h : ¬IsMin a) : pred a ⋖ a :=
  (pred_wcovby a).covby_of_lt <| pred_lt_of_not_isMin h
#align order.pred_covby_of_not_is_min Order.pred_covby_of_not_isMin
-/

#print Order.pred_lt_iff_of_not_isMin /-
theorem pred_lt_iff_of_not_isMin (ha : ¬IsMin a) : pred a < b ↔ a ≤ b :=
  ⟨le_of_pred_lt, (pred_lt_of_not_isMin ha).trans_le⟩
#align order.pred_lt_iff_of_not_is_min Order.pred_lt_iff_of_not_isMin
-/

#print Order.le_pred_iff_of_not_isMin /-
theorem le_pred_iff_of_not_isMin (ha : ¬IsMin a) : b ≤ pred a ↔ b < a :=
  ⟨fun h => h.trans_lt <| pred_lt_of_not_isMin ha, le_pred_of_lt⟩
#align order.le_pred_iff_of_not_is_min Order.le_pred_iff_of_not_isMin
-/

#print Order.pred_le_pred /-
@[simp, mono]
theorem pred_le_pred {a b : α} (h : a ≤ b) : pred a ≤ pred b :=
  succ_le_succ h.dual
#align order.pred_le_pred Order.pred_le_pred
-/

#print Order.pred_mono /-
theorem pred_mono : Monotone (pred : α → α) := fun a b => pred_le_pred
#align order.pred_mono Order.pred_mono
-/

#print Order.pred_iterate_le /-
theorem pred_iterate_le (k : ℕ) (x : α) : (pred^[k]) x ≤ x :=
  by
  conv_rhs => rw [(by simp only [Function.iterate_id, id.def] : x = (id^[k]) x)]
  exact Monotone.iterate_le_of_le pred_mono pred_le k x
#align order.pred_iterate_le Order.pred_iterate_le
-/

#print Order.isMin_iterate_pred_of_eq_of_lt /-
theorem isMin_iterate_pred_of_eq_of_lt {n m : ℕ} (h_eq : (pred^[n]) a = (pred^[m]) a)
    (h_lt : n < m) : IsMin ((pred^[n]) a) :=
  @isMax_iterate_succ_of_eq_of_lt αᵒᵈ _ _ _ _ _ h_eq h_lt
#align order.is_min_iterate_pred_of_eq_of_lt Order.isMin_iterate_pred_of_eq_of_lt
-/

#print Order.isMin_iterate_pred_of_eq_of_ne /-
theorem isMin_iterate_pred_of_eq_of_ne {n m : ℕ} (h_eq : (pred^[n]) a = (pred^[m]) a)
    (h_ne : n ≠ m) : IsMin ((pred^[n]) a) :=
  @isMax_iterate_succ_of_eq_of_ne αᵒᵈ _ _ _ _ _ h_eq h_ne
#align order.is_min_iterate_pred_of_eq_of_ne Order.isMin_iterate_pred_of_eq_of_ne
-/

#print Order.Ioi_pred_of_not_isMin /-
theorem Ioi_pred_of_not_isMin (ha : ¬IsMin a) : Ioi (pred a) = Ici a :=
  Set.ext fun x => pred_lt_iff_of_not_isMin ha
#align order.Ioi_pred_of_not_is_min Order.Ioi_pred_of_not_isMin
-/

#print Order.Iic_pred_of_not_isMin /-
theorem Iic_pred_of_not_isMin (ha : ¬IsMin a) : Iic (pred a) = Iio a :=
  Set.ext fun x => le_pred_iff_of_not_isMin ha
#align order.Iic_pred_of_not_is_min Order.Iic_pred_of_not_isMin
-/

#print Order.Ioc_pred_left_of_not_isMin /-
theorem Ioc_pred_left_of_not_isMin (ha : ¬IsMin a) : Ioc (pred a) b = Icc a b := by
  rw [← Ioi_inter_Iic, Ioi_pred_of_not_is_min ha, Ici_inter_Iic]
#align order.Ioc_pred_left_of_not_is_min Order.Ioc_pred_left_of_not_isMin
-/

#print Order.Ioo_pred_left_of_not_isMin /-
theorem Ioo_pred_left_of_not_isMin (ha : ¬IsMin a) : Ioo (pred a) b = Ico a b := by
  rw [← Ioi_inter_Iio, Ioi_pred_of_not_is_min ha, Ici_inter_Iio]
#align order.Ioo_pred_left_of_not_is_min Order.Ioo_pred_left_of_not_isMin
-/

#print Order.Icc_pred_right_of_not_isMin /-
theorem Icc_pred_right_of_not_isMin (ha : ¬IsMin b) : Icc a (pred b) = Ico a b := by
  rw [← Ici_inter_Iic, Iic_pred_of_not_is_min ha, Ici_inter_Iio]
#align order.Icc_pred_right_of_not_is_min Order.Icc_pred_right_of_not_isMin
-/

#print Order.Ioc_pred_right_of_not_isMin /-
theorem Ioc_pred_right_of_not_isMin (ha : ¬IsMin b) : Ioc a (pred b) = Ioo a b := by
  rw [← Ioi_inter_Iic, Iic_pred_of_not_is_min ha, Ioi_inter_Iio]
#align order.Ioc_pred_right_of_not_is_min Order.Ioc_pred_right_of_not_isMin
-/

section NoMinOrder

variable [NoMinOrder α]

#print Order.pred_lt /-
theorem pred_lt (a : α) : pred a < a :=
  pred_lt_of_not_isMin <| not_isMin a
#align order.pred_lt Order.pred_lt
-/

#print Order.pred_lt_iff /-
@[simp]
theorem pred_lt_iff : pred a < b ↔ a ≤ b :=
  pred_lt_iff_of_not_isMin <| not_isMin a
#align order.pred_lt_iff Order.pred_lt_iff
-/

#print Order.le_pred_iff /-
@[simp]
theorem le_pred_iff : a ≤ pred b ↔ a < b :=
  le_pred_iff_of_not_isMin <| not_isMin b
#align order.le_pred_iff Order.le_pred_iff
-/

#print Order.pred_le_pred_iff /-
theorem pred_le_pred_iff : pred a ≤ pred b ↔ a ≤ b := by simp
#align order.pred_le_pred_iff Order.pred_le_pred_iff
-/

#print Order.pred_lt_pred_iff /-
theorem pred_lt_pred_iff : pred a < pred b ↔ a < b := by simp
#align order.pred_lt_pred_iff Order.pred_lt_pred_iff
-/

alias pred_le_pred_iff ↔ le_of_pred_le_pred _
#align order.le_of_pred_le_pred Order.le_of_pred_le_pred

alias pred_lt_pred_iff ↔ lt_of_pred_lt_pred pred_lt_pred
#align order.lt_of_pred_lt_pred Order.lt_of_pred_lt_pred
#align order.pred_lt_pred Order.pred_lt_pred

#print Order.pred_strictMono /-
theorem pred_strictMono : StrictMono (pred : α → α) := fun a b => pred_lt_pred
#align order.pred_strict_mono Order.pred_strictMono
-/

#print Order.pred_covby /-
theorem pred_covby (a : α) : pred a ⋖ a :=
  pred_covby_of_not_isMin <| not_isMin a
#align order.pred_covby Order.pred_covby
-/

#print Order.Ioi_pred /-
@[simp]
theorem Ioi_pred (a : α) : Ioi (pred a) = Ici a :=
  Ioi_pred_of_not_isMin <| not_isMin a
#align order.Ioi_pred Order.Ioi_pred
-/

#print Order.Iic_pred /-
@[simp]
theorem Iic_pred (a : α) : Iic (pred a) = Iio a :=
  Iic_pred_of_not_isMin <| not_isMin a
#align order.Iic_pred Order.Iic_pred
-/

#print Order.Ioc_pred_left /-
@[simp]
theorem Ioc_pred_left (a b : α) : Ioc (pred a) b = Icc a b :=
  Ioc_pred_left_of_not_isMin <| not_isMin _
#align order.Ioc_pred_left Order.Ioc_pred_left
-/

#print Order.Ioo_pred_left /-
@[simp]
theorem Ioo_pred_left (a b : α) : Ioo (pred a) b = Ico a b :=
  Ioo_pred_left_of_not_isMin <| not_isMin _
#align order.Ioo_pred_left Order.Ioo_pred_left
-/

#print Order.Icc_pred_right /-
@[simp]
theorem Icc_pred_right (a b : α) : Icc a (pred b) = Ico a b :=
  Icc_pred_right_of_not_isMin <| not_isMin _
#align order.Icc_pred_right Order.Icc_pred_right
-/

#print Order.Ioc_pred_right /-
@[simp]
theorem Ioc_pred_right (a b : α) : Ioc a (pred b) = Ioo a b :=
  Ioc_pred_right_of_not_isMin <| not_isMin _
#align order.Ioc_pred_right Order.Ioc_pred_right
-/

end NoMinOrder

end Preorder

section PartialOrder

variable [PartialOrder α] [PredOrder α] {a b : α}

#print Order.pred_eq_iff_isMin /-
@[simp]
theorem pred_eq_iff_isMin : pred a = a ↔ IsMin a :=
  ⟨fun h => min_of_le_pred h.ge, fun h => h.eq_of_le <| pred_le _⟩
#align order.pred_eq_iff_is_min Order.pred_eq_iff_isMin
-/

alias pred_eq_iff_is_min ↔ _ _root_.is_min.pred_eq
#align is_min.pred_eq IsMin.pred_eq

#print Order.pred_le_le_iff /-
theorem pred_le_le_iff {a b : α} : pred a ≤ b ∧ b ≤ a ↔ b = a ∨ b = pred a :=
  by
  refine'
    ⟨fun h =>
      or_iff_not_imp_left.2 fun hba : b ≠ a => (le_pred_of_lt <| h.2.lt_of_ne hba).antisymm h.1, _⟩
  rintro (rfl | rfl)
  · exact ⟨pred_le b, le_rfl⟩
  · exact ⟨le_rfl, pred_le a⟩
#align order.pred_le_le_iff Order.pred_le_le_iff
-/

#print Covby.pred_eq /-
theorem Covby.pred_eq {a b : α} (h : a ⋖ b) : pred b = a :=
  (le_pred_of_lt h.lt).eq_of_not_gt fun h' => h.2 h' <| pred_lt_of_not_isMin h.lt.not_isMin
#align covby.pred_eq Covby.pred_eq
-/

#print Wcovby.pred_le /-
theorem Wcovby.pred_le (h : a ⩿ b) : pred b ≤ a :=
  by
  obtain h | rfl := h.covby_or_eq
  · exact h.pred_eq.le
  · exact pred_le _
#align wcovby.pred_le Wcovby.pred_le
-/

#print Order.pred_le_iff_eq_or_le /-
theorem pred_le_iff_eq_or_le : pred a ≤ b ↔ b = pred a ∨ a ≤ b :=
  by
  by_cases ha : IsMin a
  · rw [ha.pred_eq, or_iff_right_of_imp ge_of_eq]
  · rw [← pred_lt_iff_of_not_is_min ha, le_iff_eq_or_lt, eq_comm]
#align order.pred_le_iff_eq_or_le Order.pred_le_iff_eq_or_le
-/

#print Order.pred_lt_iff_eq_or_lt_of_not_isMin /-
theorem pred_lt_iff_eq_or_lt_of_not_isMin (ha : ¬IsMin a) : pred a < b ↔ a = b ∨ a < b :=
  (pred_lt_iff_of_not_isMin ha).trans le_iff_eq_or_lt
#align order.pred_lt_iff_eq_or_lt_of_not_is_min Order.pred_lt_iff_eq_or_lt_of_not_isMin
-/

#print Order.Ici_pred /-
theorem Ici_pred (a : α) : Ici (pred a) = insert (pred a) (Ici a) :=
  ext fun _ => pred_le_iff_eq_or_le
#align order.Ici_pred Order.Ici_pred
-/

#print Order.Ioi_pred_eq_insert_of_not_isMin /-
theorem Ioi_pred_eq_insert_of_not_isMin (ha : ¬IsMin a) : Ioi (pred a) = insert a (Ioi a) :=
  by
  ext x; simp only [insert, mem_set_of, @eq_comm _ x a]
  exact pred_lt_iff_eq_or_lt_of_not_is_min ha
#align order.Ioi_pred_eq_insert_of_not_is_min Order.Ioi_pred_eq_insert_of_not_isMin
-/

#print Order.Icc_pred_left /-
theorem Icc_pred_left (h : pred a ≤ b) : Icc (pred a) b = insert (pred a) (Icc a b) := by
  simp_rw [← Ici_inter_Iic, Ici_pred, insert_inter_of_mem (mem_Iic.2 h)]
#align order.Icc_pred_left Order.Icc_pred_left
-/

#print Order.Ico_pred_left /-
theorem Ico_pred_left (h : pred a < b) : Ico (pred a) b = insert (pred a) (Ico a b) := by
  simp_rw [← Ici_inter_Iio, Ici_pred, insert_inter_of_mem (mem_Iio.2 h)]
#align order.Ico_pred_left Order.Ico_pred_left
-/

section NoMinOrder

variable [NoMinOrder α]

#print Order.pred_eq_pred_iff /-
@[simp]
theorem pred_eq_pred_iff : pred a = pred b ↔ a = b := by
  simp_rw [eq_iff_le_not_lt, pred_le_pred_iff, pred_lt_pred_iff]
#align order.pred_eq_pred_iff Order.pred_eq_pred_iff
-/

#print Order.pred_injective /-
theorem pred_injective : Injective (pred : α → α) := fun a b => pred_eq_pred_iff.1
#align order.pred_injective Order.pred_injective
-/

#print Order.pred_ne_pred_iff /-
theorem pred_ne_pred_iff : pred a ≠ pred b ↔ a ≠ b :=
  pred_injective.ne_iff
#align order.pred_ne_pred_iff Order.pred_ne_pred_iff
-/

alias pred_ne_pred_iff ↔ _ pred_ne_pred
#align order.pred_ne_pred Order.pred_ne_pred

#print Order.pred_lt_iff_eq_or_lt /-
theorem pred_lt_iff_eq_or_lt : pred a < b ↔ a = b ∨ a < b :=
  pred_lt_iff.trans le_iff_eq_or_lt
#align order.pred_lt_iff_eq_or_lt Order.pred_lt_iff_eq_or_lt
-/

#print Order.pred_eq_iff_covby /-
theorem pred_eq_iff_covby : pred b = a ↔ a ⋖ b :=
  ⟨by
    rintro rfl
    exact pred_covby _, Covby.pred_eq⟩
#align order.pred_eq_iff_covby Order.pred_eq_iff_covby
-/

#print Order.Ioi_pred_eq_insert /-
theorem Ioi_pred_eq_insert (a : α) : Ioi (pred a) = insert a (Ioi a) :=
  ext fun _ => pred_lt_iff_eq_or_lt.trans <| or_congr_left eq_comm
#align order.Ioi_pred_eq_insert Order.Ioi_pred_eq_insert
-/

#print Order.Ico_pred_right_eq_insert /-
theorem Ico_pred_right_eq_insert (h : a ≤ b) : Ioc (pred a) b = insert a (Ioc a b) := by
  simp_rw [← Ioi_inter_Iic, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iic.2 h)]
#align order.Ico_pred_right_eq_insert Order.Ico_pred_right_eq_insert
-/

#print Order.Ioo_pred_right_eq_insert /-
theorem Ioo_pred_right_eq_insert (h : a < b) : Ioo (pred a) b = insert a (Ioo a b) := by
  simp_rw [← Ioi_inter_Iio, Ioi_pred_eq_insert, insert_inter_of_mem (mem_Iio.2 h)]
#align order.Ioo_pred_right_eq_insert Order.Ioo_pred_right_eq_insert
-/

end NoMinOrder

section OrderBot

variable [OrderBot α]

/- warning: order.pred_bot -> Order.pred_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Eq.{succ u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Eq.{succ u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))
Case conversion may be inaccurate. Consider using '#align order.pred_bot Order.pred_botₓ'. -/
@[simp]
theorem pred_bot : pred (⊥ : α) = ⊥ :=
  isMin_bot.pred_eq
#align order.pred_bot Order.pred_bot

/- warning: order.le_pred_iff_eq_bot -> Order.le_pred_iff_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)) (Eq.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) a (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a)) (Eq.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
Case conversion may be inaccurate. Consider using '#align order.le_pred_iff_eq_bot Order.le_pred_iff_eq_botₓ'. -/
@[simp]
theorem le_pred_iff_eq_bot : a ≤ pred a ↔ a = ⊥ :=
  @succ_le_iff_eq_top αᵒᵈ _ _ _ _
#align order.le_pred_iff_eq_bot Order.le_pred_iff_eq_bot

/- warning: order.pred_lt_iff_ne_bot -> Order.pred_lt_iff_ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) a) (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) a) (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
Case conversion may be inaccurate. Consider using '#align order.pred_lt_iff_ne_bot Order.pred_lt_iff_ne_botₓ'. -/
@[simp]
theorem pred_lt_iff_ne_bot : pred a < a ↔ a ≠ ⊥ :=
  @lt_succ_iff_ne_top αᵒᵈ _ _ _ _
#align order.pred_lt_iff_ne_bot Order.pred_lt_iff_ne_bot

end OrderBot

section OrderTop

variable [OrderTop α]

/- warning: order.pred_top_lt_iff -> Order.pred_top_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) a) (Eq.{succ u1} α a (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : NoMinOrder.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) a) (Eq.{succ u1} α a (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))
Case conversion may be inaccurate. Consider using '#align order.pred_top_lt_iff Order.pred_top_lt_iffₓ'. -/
@[simp]
theorem pred_top_lt_iff [NoMinOrder α] : pred ⊤ < a ↔ a = ⊤ :=
  @lt_succ_bot_iff αᵒᵈ _ _ _ _ _
#align order.pred_top_lt_iff Order.pred_top_lt_iff

/- warning: order.pred_top_le_iff -> Order.pred_top_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) a) (Or (Eq.{succ u1} α a (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Eq.{succ u1} α a (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] {a : α} [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) a) (Or (Eq.{succ u1} α a (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))) (Eq.{succ u1} α a (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3)))))
Case conversion may be inaccurate. Consider using '#align order.pred_top_le_iff Order.pred_top_le_iffₓ'. -/
theorem pred_top_le_iff : pred ⊤ ≤ a ↔ a = ⊤ ∨ a = pred ⊤ :=
  @le_succ_bot_iff αᵒᵈ _ _ _ _
#align order.pred_top_le_iff Order.pred_top_le_iff

variable [Nontrivial α]

/- warning: order.pred_lt_top -> Order.pred_lt_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : Nontrivial.{u1} α] (a : α), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : Nontrivial.{u1} α] (a : α), LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))
Case conversion may be inaccurate. Consider using '#align order.pred_lt_top Order.pred_lt_topₓ'. -/
theorem pred_lt_top (a : α) : pred a < ⊤ :=
  (pred_mono le_top).trans_lt <| pred_lt_of_not_isMin not_isMin_top
#align order.pred_lt_top Order.pred_lt_top

/- warning: order.pred_ne_top -> Order.pred_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : Nontrivial.{u1} α] (a : α), Ne.{succ u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))] [_inst_4 : Nontrivial.{u1} α] (a : α), Ne.{succ u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_2 a) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_3))
Case conversion may be inaccurate. Consider using '#align order.pred_ne_top Order.pred_ne_topₓ'. -/
theorem pred_ne_top (a : α) : pred a ≠ ⊤ :=
  (pred_lt_top a).Ne
#align order.pred_ne_top Order.pred_ne_top

end OrderTop

end PartialOrder

/-- There is at most one way to define the predecessors in a `partial_order`. -/
instance [PartialOrder α] : Subsingleton (PredOrder α) :=
  ⟨by
    intro h₀ h₁
    ext a
    by_cases ha : IsMin a
    · exact (@IsMin.pred_eq _ _ h₀ _ ha).trans ha.pred_eq.symm
    · exact @Covby.pred_eq _ _ h₀ _ _ (pred_covby_of_not_is_min ha)⟩

section CompleteLattice

variable [CompleteLattice α] [PredOrder α]

/- warning: order.pred_eq_supr -> Order.pred_eq_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))] (a : α), Eq.{succ u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) _inst_2 a) (supᵢ.{u1, succ u1} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) α (fun (b : α) => supᵢ.{u1, 0} α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b a) (fun (h : LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b a) => b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))] (a : α), Eq.{succ u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) _inst_2 a) (supᵢ.{u1, succ u1} α (CompleteLattice.toSupSet.{u1} α _inst_1) α (fun (b : α) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α _inst_1) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b a) (fun (h : LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) b a) => b)))
Case conversion may be inaccurate. Consider using '#align order.pred_eq_supr Order.pred_eq_supᵢₓ'. -/
theorem pred_eq_supᵢ (a : α) : pred a = ⨆ (b) (h : b < a), b :=
  by
  refine' le_antisymm _ (supᵢ_le fun b => supᵢ_le le_pred_of_lt)
  obtain rfl | ha := eq_or_ne a ⊥
  · rw [pred_bot]
    exact bot_le
  · exact @le_supᵢ₂ _ _ (fun b => b < a) _ (fun a _ => a) (pred a) (pred_lt_iff_ne_bot.2 ha)
#align order.pred_eq_supr Order.pred_eq_supᵢ

end CompleteLattice

/-! ### Successor-predecessor orders -/


section SuccPredOrder

variable [PartialOrder α] [SuccOrder α] [PredOrder α] {a b : α}

#print Order.succ_pred_of_not_isMin /-
@[simp]
theorem succ_pred_of_not_isMin (h : ¬IsMin a) : succ (pred a) = a :=
  (pred_covby_of_not_isMin h).succ_eq
#align order.succ_pred_of_not_is_min Order.succ_pred_of_not_isMin
-/

#print Order.pred_succ_of_not_isMax /-
@[simp]
theorem pred_succ_of_not_isMax (h : ¬IsMax a) : pred (succ a) = a :=
  (covby_succ_of_not_isMax h).pred_eq
#align order.pred_succ_of_not_is_max Order.pred_succ_of_not_isMax
-/

#print Order.succ_pred /-
@[simp]
theorem succ_pred [NoMinOrder α] (a : α) : succ (pred a) = a :=
  (pred_covby _).succ_eq
#align order.succ_pred Order.succ_pred
-/

#print Order.pred_succ /-
@[simp]
theorem pred_succ [NoMaxOrder α] (a : α) : pred (succ a) = a :=
  (covby_succ _).pred_eq
#align order.pred_succ Order.pred_succ
-/

#print Order.pred_succ_iterate_of_not_isMax /-
theorem pred_succ_iterate_of_not_isMax (i : α) (n : ℕ) (hin : ¬IsMax ((succ^[n - 1]) i)) :
    (pred^[n]) ((succ^[n]) i) = i := by
  induction' n with n hn
  · simp only [Function.iterate_zero, id.def]
  rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at hin
  have h_not_max : ¬IsMax ((succ^[n - 1]) i) :=
    by
    cases n
    · simpa using hin
    rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at hn⊢
    have h_sub_le : (succ^[n]) i ≤ (succ^[n.succ]) i :=
      by
      rw [Function.iterate_succ']
      exact le_succ _
    refine' fun h_max => hin fun j hj => _
    have hj_le : j ≤ (succ^[n]) i := h_max (h_sub_le.trans hj)
    exact hj_le.trans h_sub_le
  rw [Function.iterate_succ, Function.iterate_succ']
  simp only [Function.comp_apply]
  rw [pred_succ_of_not_is_max hin]
  exact hn h_not_max
#align order.pred_succ_iterate_of_not_is_max Order.pred_succ_iterate_of_not_isMax
-/

#print Order.succ_pred_iterate_of_not_isMin /-
theorem succ_pred_iterate_of_not_isMin (i : α) (n : ℕ) (hin : ¬IsMin ((pred^[n - 1]) i)) :
    (succ^[n]) ((pred^[n]) i) = i :=
  @pred_succ_iterate_of_not_isMax αᵒᵈ _ _ _ i n hin
#align order.succ_pred_iterate_of_not_is_min Order.succ_pred_iterate_of_not_isMin
-/

end SuccPredOrder

end Order

open Order

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


namespace WithTop

/-! #### Adding a `⊤` to an `order_top` -/


section Succ

variable [DecidableEq α] [PartialOrder α] [OrderTop α] [SuccOrder α]

instance : SuccOrder (WithTop α)
    where
  succ a :=
    match a with
    | ⊤ => ⊤
    | some a => ite (a = ⊤) ⊤ (some (succ a))
  le_succ a := by
    cases a
    · exact le_top
    change _ ≤ ite _ _ _
    split_ifs
    · exact le_top
    · exact some_le_some.2 (le_succ a)
  max_of_succ_le a ha := by
    cases a
    · exact isMax_top
    change ite _ _ _ ≤ _ at ha
    split_ifs  at ha with ha'
    · exact (not_top_le_coe _ ha).elim
    · rw [some_le_some, succ_le_iff_eq_top] at ha
      exact (ha' ha).elim
  succ_le_of_lt a b h := by
    cases b
    · exact le_top
    cases a
    · exact (not_top_lt h).elim
    rw [some_lt_some] at h
    change ite _ _ _ ≤ _
    split_ifs with ha
    · rw [ha] at h
      exact (not_top_lt h).elim
    · exact some_le_some.2 (succ_le_of_lt h)
  le_of_lt_succ a b h := by
    cases a
    · exact (not_top_lt h).elim
    cases b
    · exact le_top
    change _ < ite _ _ _ at h
    rw [some_le_some]
    split_ifs  at h with hb
    · rw [hb]
      exact le_top
    · exact le_of_lt_succ (some_lt_some.1 h)

/- warning: with_top.succ_coe_top -> WithTop.succ_coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)], Eq.{succ u1} (WithTop.{u1} α) (Order.succ.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (WithTop.succOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 _inst_4) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3)))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)], Eq.{succ u1} (WithTop.{u1} α) (Order.succ.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (WithTop.instSuccOrderWithTopPreorderToPreorder.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 _inst_4) (WithTop.some.{u1} α (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3)))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))
Case conversion may be inaccurate. Consider using '#align with_top.succ_coe_top WithTop.succ_coe_topₓ'. -/
@[simp]
theorem succ_coe_top : succ ↑(⊤ : α) = (⊤ : WithTop α) :=
  dif_pos rfl
#align with_top.succ_coe_top WithTop.succ_coe_top

/- warning: with_top.succ_coe_of_ne_top -> WithTop.succ_coe_of_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)] {a : α}, (Ne.{succ u1} α a (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3))) -> (Eq.{succ u1} (WithTop.{u1} α) (Order.succ.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (WithTop.succOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 _inst_4) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) _inst_4 a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : SuccOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)] {a : α}, (Ne.{succ u1} α a (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3))) -> (Eq.{succ u1} (WithTop.{u1} α) (Order.succ.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (WithTop.instSuccOrderWithTopPreorderToPreorder.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 _inst_4) (WithTop.some.{u1} α a)) (WithTop.some.{u1} α (Order.succ.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) _inst_4 a)))
Case conversion may be inaccurate. Consider using '#align with_top.succ_coe_of_ne_top WithTop.succ_coe_of_ne_topₓ'. -/
theorem succ_coe_of_ne_top {a : α} (h : a ≠ ⊤) : succ (↑a : WithTop α) = ↑(succ a) :=
  dif_neg h
#align with_top.succ_coe_of_ne_top WithTop.succ_coe_of_ne_top

end Succ

section Pred

variable [Preorder α] [OrderTop α] [PredOrder α]

instance : PredOrder (WithTop α)
    where
  pred a :=
    match a with
    | ⊤ => some ⊤
    | some a => some (pred a)
  pred_le a :=
    match a with
    | ⊤ => le_top
    | some a => some_le_some.2 (pred_le a)
  min_of_le_pred a ha := by
    cases a
    · exact ((coe_lt_top (⊤ : α)).not_le ha).elim
    · exact (min_of_le_pred <| some_le_some.1 ha).WithTop
  le_pred_of_lt a b h := by
    cases a
    · exact (le_top.not_lt h).elim
    cases b
    · exact some_le_some.2 le_top
    exact some_le_some.2 (le_pred_of_lt <| some_lt_some.1 h)
  le_of_pred_lt a b h := by
    cases b
    · exact le_top
    cases a
    · exact (not_top_lt <| some_lt_some.1 h).elim
    · exact some_le_some.2 (le_of_pred_lt <| some_lt_some.1 h)

/- warning: with_top.pred_top -> WithTop.pred_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : PredOrder.{u1} α _inst_1], Eq.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : PredOrder.{u1} α _inst_1], Eq.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.instPredOrderWithTopPreorder.{u1} α _inst_1 _inst_2 _inst_3) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) (WithTop.some.{u1} α (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))
Case conversion may be inaccurate. Consider using '#align with_top.pred_top WithTop.pred_topₓ'. -/
@[simp]
theorem pred_top : pred (⊤ : WithTop α) = ↑(⊤ : α) :=
  rfl
#align with_top.pred_top WithTop.pred_top

#print WithTop.pred_coe /-
@[simp]
theorem pred_coe (a : α) : pred (↑a : WithTop α) = ↑(pred a) :=
  rfl
#align with_top.pred_coe WithTop.pred_coe
-/

/- warning: with_top.pred_untop -> WithTop.pred_untop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : PredOrder.{u1} α _inst_1] (a : WithTop.{u1} α) (ha : Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))), Eq.{succ u1} α (Order.pred.{u1} α _inst_1 _inst_3 (WithTop.untop.{u1} α a ha)) (WithTop.untop.{u1} α (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) a) (WithTop.recTopCoe.{u1, 0} α (fun (a : WithTop.{u1} α) => (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) -> (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) a) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))) (fun (ha : Ne.{succ u1} (WithTop.{u1} α) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) => Eq.mpr.{0} (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) True) (Eq.trans.{1} Prop (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Not False) True (Eq.trans.{1} Prop (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Not (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))) (Not False) (Eq.trans.{1} Prop (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Ne.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Not (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))) ((fun (a : WithTop.{u1} α) (a_1 : WithTop.{u1} α) (e_1 : Eq.{succ u1} (WithTop.{u1} α) a a_1) (b : WithTop.{u1} α) (b_1 : WithTop.{u1} α) (e_2 : Eq.{succ u1} (WithTop.{u1} α) b b_1) => congr.{succ u1, 1} (WithTop.{u1} α) Prop (Ne.{succ u1} (WithTop.{u1} α) a) (Ne.{succ u1} (WithTop.{u1} α) a_1) b b_1 (congr_arg.{succ u1, succ u1} (WithTop.{u1} α) ((WithTop.{u1} α) -> Prop) a a_1 (Ne.{succ u1} (WithTop.{u1} α)) e_1) e_2) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (WithTop.pred_top.{u1} α _inst_1 _inst_2 _inst_3) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)) (rfl.{succ u1} (WithTop.{u1} α) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))) (Ne.def.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))) ((fun (a : Prop) (a_1 : Prop) (e_1 : Eq.{1} Prop a a_1) => congr_arg.{1, 1} Prop Prop a a_1 Not e_1) (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) False (propext (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) False ((fun {α : Type.{u1}} {a : α} => iff_false_intro (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (WithTop.coe_ne_top.{u1} α a)) α (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))))) (propext (Not False) True not_false_iff))) trivial) (fun (a : α) (ha : Ne.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) => Eq.mpr.{0} (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) True) (Eq.trans.{1} Prop (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Not False) True (Eq.trans.{1} Prop (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Not (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Order.pred.{u1} α _inst_1 _inst_3 a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))) (Not False) (Eq.trans.{1} Prop (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Ne.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Order.pred.{u1} α _inst_1 _inst_3 a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (Not (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Order.pred.{u1} α _inst_1 _inst_3 a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))) ((fun (a : WithTop.{u1} α) (a_1 : WithTop.{u1} α) (e_1 : Eq.{succ u1} (WithTop.{u1} α) a a_1) (b : WithTop.{u1} α) (b_1 : WithTop.{u1} α) (e_2 : Eq.{succ u1} (WithTop.{u1} α) b b_1) => congr.{succ u1, 1} (WithTop.{u1} α) Prop (Ne.{succ u1} (WithTop.{u1} α) a) (Ne.{succ u1} (WithTop.{u1} α) a_1) b b_1 (congr_arg.{succ u1, succ u1} (WithTop.{u1} α) ((WithTop.{u1} α) -> Prop) a a_1 (Ne.{succ u1} (WithTop.{u1} α)) e_1) e_2) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.predOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Order.pred.{u1} α _inst_1 _inst_3 a)) (WithTop.pred_coe.{u1} α _inst_1 _inst_2 _inst_3 a) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)) (rfl.{succ u1} (WithTop.{u1} α) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))) (Ne.def.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Order.pred.{u1} α _inst_1 _inst_3 a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α)))) ((fun (a : Prop) (a_1 : Prop) (e_1 : Eq.{1} Prop a a_1) => congr_arg.{1, 1} Prop Prop a a_1 Not e_1) (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Order.pred.{u1} α _inst_1 _inst_3 a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) False (propext (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (Order.pred.{u1} α _inst_1 _inst_3 a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) False ((fun {α : Type.{u1}} {a : α} => iff_false_intro (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) a) (Top.top.{u1} (WithTop.{u1} α) (WithTop.hasTop.{u1} α))) (WithTop.coe_ne_top.{u1} α a)) α (Order.pred.{u1} α _inst_1 _inst_3 a))))) (propext (Not False) True not_false_iff))) trivial) a ha))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : PredOrder.{u1} α _inst_1] (a : WithTop.{u1} α) (ha : Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))), Eq.{succ u1} α (Order.pred.{u1} α _inst_1 _inst_3 (WithTop.untop.{u1} α a ha)) (WithTop.untop.{u1} α (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.instPredOrderWithTopPreorder.{u1} α _inst_1 _inst_2 _inst_3) a) (WithTop.recTopCoe.{u1, 0} α (fun (a : WithTop.{u1} α) => (Ne.{succ u1} (WithTop.{u1} α) a (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) -> (Ne.{succ u1} (WithTop.{u1} α) (Order.pred.{u1} (WithTop.{u1} α) (WithTop.preorder.{u1} α _inst_1) (WithTop.instPredOrderWithTopPreorder.{u1} α _inst_1 _inst_2 _inst_3) a) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)))) (fun (ha : Ne.{succ u1} (WithTop.{u1} α) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) => of_eq_true (Not (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)))) (Eq.trans.{1} Prop (Not (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)))) (Not False) True (congrArg.{1, 1} Prop Prop (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) False Not (Mathlib.Order.WithBot._auxLemma.22.{u1} α (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))) not_false_eq_true)) (fun (a : α) (ha : Ne.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α a) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) => of_eq_true (Not (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (Order.pred.{u1} α _inst_1 _inst_3 a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)))) (Eq.trans.{1} Prop (Not (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (Order.pred.{u1} α _inst_1 _inst_3 a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α)))) (Not False) True (congrArg.{1, 1} Prop Prop (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (Order.pred.{u1} α _inst_1 _inst_3 a)) (Top.top.{u1} (WithTop.{u1} α) (WithTop.top.{u1} α))) False Not (Mathlib.Order.WithBot._auxLemma.22.{u1} α (Order.pred.{u1} α _inst_1 _inst_3 a))) not_false_eq_true)) a ha))
Case conversion may be inaccurate. Consider using '#align with_top.pred_untop WithTop.pred_untopₓ'. -/
@[simp]
theorem pred_untop :
    ∀ (a : WithTop α) (ha : a ≠ ⊤),
      pred (a.untop ha) = (pred a).untop (by induction a using WithTop.recTopCoe <;> simp)
  | ⊤, ha => (ha rfl).elim
  | (a : α), ha => rfl
#align with_top.pred_untop WithTop.pred_untop

end Pred

/-! #### Adding a `⊤` to a `no_max_order` -/


section Succ

variable [Preorder α] [NoMaxOrder α] [SuccOrder α]

#print WithTop.succOrderOfNoMaxOrder /-
instance succOrderOfNoMaxOrder : SuccOrder (WithTop α)
    where
  succ a :=
    match a with
    | ⊤ => ⊤
    | some a => some (succ a)
  le_succ a := by
    cases a
    · exact le_top
    · exact some_le_some.2 (le_succ a)
  max_of_succ_le a ha := by
    cases a
    · exact isMax_top
    · exact (not_isMax _ <| max_of_succ_le <| some_le_some.1 ha).elim
  succ_le_of_lt a b h := by
    cases a
    · exact (not_top_lt h).elim
    cases b
    · exact le_top
    · exact some_le_some.2 (succ_le_of_lt <| some_lt_some.1 h)
  le_of_lt_succ a b h := by
    cases a
    · exact (not_top_lt h).elim
    cases b
    · exact le_top
    · exact some_le_some.2 (le_of_lt_succ <| some_lt_some.1 h)
#align with_top.succ_order_of_no_max_order WithTop.succOrderOfNoMaxOrder
-/

#print WithTop.succ_coe /-
@[simp]
theorem succ_coe (a : α) : succ (↑a : WithTop α) = ↑(succ a) :=
  rfl
#align with_top.succ_coe WithTop.succ_coe
-/

end Succ

section Pred

variable [Preorder α] [NoMaxOrder α]

instance [hα : Nonempty α] : IsEmpty (PredOrder (WithTop α)) :=
  ⟨by
    intro
    cases' h : pred (⊤ : WithTop α) with a ha
    · exact hα.elim fun a => (min_of_le_pred h.ge).not_lt <| coe_lt_top a
    · obtain ⟨c, hc⟩ := exists_gt a
      rw [← some_lt_some, ← h] at hc
      exact (le_of_pred_lt hc).not_lt (some_lt_none _)⟩

end Pred

end WithTop

namespace WithBot

/-! #### Adding a `⊥` to an `order_bot` -/


section Succ

variable [Preorder α] [OrderBot α] [SuccOrder α]

instance : SuccOrder (WithBot α)
    where
  succ a :=
    match a with
    | ⊥ => some ⊥
    | some a => some (succ a)
  le_succ a :=
    match a with
    | ⊥ => bot_le
    | some a => some_le_some.2 (le_succ a)
  max_of_succ_le a ha := by
    cases a
    · exact ((none_lt_some (⊥ : α)).not_le ha).elim
    · exact (max_of_succ_le <| some_le_some.1 ha).WithBot
  succ_le_of_lt a b h := by
    cases b
    · exact (not_lt_bot h).elim
    cases a
    · exact some_le_some.2 bot_le
    · exact some_le_some.2 (succ_le_of_lt <| some_lt_some.1 h)
  le_of_lt_succ a b h := by
    cases a
    · exact bot_le
    cases b
    · exact (not_lt_bot <| some_lt_some.1 h).elim
    · exact some_le_some.2 (le_of_lt_succ <| some_lt_some.1 h)

/- warning: with_bot.succ_bot -> WithBot.succ_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : SuccOrder.{u1} α _inst_1], Eq.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : SuccOrder.{u1} α _inst_1], Eq.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.instSuccOrderWithBotPreorder.{u1} α _inst_1 _inst_2 _inst_3) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))) (WithBot.some.{u1} α (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))
Case conversion may be inaccurate. Consider using '#align with_bot.succ_bot WithBot.succ_botₓ'. -/
@[simp]
theorem succ_bot : succ (⊥ : WithBot α) = ↑(⊥ : α) :=
  rfl
#align with_bot.succ_bot WithBot.succ_bot

#print WithBot.succ_coe /-
@[simp]
theorem succ_coe (a : α) : succ (↑a : WithBot α) = ↑(succ a) :=
  rfl
#align with_bot.succ_coe WithBot.succ_coe
-/

/- warning: with_bot.succ_unbot -> WithBot.succ_unbot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : SuccOrder.{u1} α _inst_1] (a : WithBot.{u1} α) (ha : Ne.{succ u1} (WithBot.{u1} α) a (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))), Eq.{succ u1} α (Order.succ.{u1} α _inst_1 _inst_3 (WithBot.unbot.{u1} α a ha)) (WithBot.unbot.{u1} α (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) a) (WithBot.recBotCoe.{u1, 0} α (fun (a : WithBot.{u1} α) => (Ne.{succ u1} (WithBot.{u1} α) a (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) -> (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) a) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))) (fun (ha : Ne.{succ u1} (WithBot.{u1} α) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) => Eq.mpr.{0} (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) True) (Eq.trans.{1} Prop (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Not False) True (Eq.trans.{1} Prop (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Not (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))) (Not False) (Eq.trans.{1} Prop (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Ne.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Not (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))) ((fun (a : WithBot.{u1} α) (a_1 : WithBot.{u1} α) (e_1 : Eq.{succ u1} (WithBot.{u1} α) a a_1) (b : WithBot.{u1} α) (b_1 : WithBot.{u1} α) (e_2 : Eq.{succ u1} (WithBot.{u1} α) b b_1) => congr.{succ u1, 1} (WithBot.{u1} α) Prop (Ne.{succ u1} (WithBot.{u1} α) a) (Ne.{succ u1} (WithBot.{u1} α) a_1) b b_1 (congr_arg.{succ u1, succ u1} (WithBot.{u1} α) ((WithBot.{u1} α) -> Prop) a a_1 (Ne.{succ u1} (WithBot.{u1} α)) e_1) e_2) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (WithBot.succ_bot.{u1} α _inst_1 _inst_2 _inst_3) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) (rfl.{succ u1} (WithBot.{u1} α) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))) (Ne.def.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))) ((fun (a : Prop) (a_1 : Prop) (e_1 : Eq.{1} Prop a a_1) => congr_arg.{1, 1} Prop Prop a a_1 Not e_1) (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) False (propext (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) False ((fun {α : Type.{u1}} {a : α} => iff_false_intro (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (WithBot.coe_ne_bot.{u1} α a)) α (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))))) (propext (Not False) True not_false_iff))) trivial) (fun (a : α) (ha : Ne.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) => Eq.mpr.{0} (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) True) (Eq.trans.{1} Prop (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Not False) True (Eq.trans.{1} Prop (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Not (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Order.succ.{u1} α _inst_1 _inst_3 a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))) (Not False) (Eq.trans.{1} Prop (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Ne.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Order.succ.{u1} α _inst_1 _inst_3 a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (Not (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Order.succ.{u1} α _inst_1 _inst_3 a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))) ((fun (a : WithBot.{u1} α) (a_1 : WithBot.{u1} α) (e_1 : Eq.{succ u1} (WithBot.{u1} α) a a_1) (b : WithBot.{u1} α) (b_1 : WithBot.{u1} α) (e_2 : Eq.{succ u1} (WithBot.{u1} α) b b_1) => congr.{succ u1, 1} (WithBot.{u1} α) Prop (Ne.{succ u1} (WithBot.{u1} α) a) (Ne.{succ u1} (WithBot.{u1} α) a_1) b b_1 (congr_arg.{succ u1, succ u1} (WithBot.{u1} α) ((WithBot.{u1} α) -> Prop) a a_1 (Ne.{succ u1} (WithBot.{u1} α)) e_1) e_2) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.succOrder.{u1} α _inst_1 _inst_2 _inst_3) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Order.succ.{u1} α _inst_1 _inst_3 a)) (WithBot.succ_coe.{u1} α _inst_1 _inst_2 _inst_3 a) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)) (rfl.{succ u1} (WithBot.{u1} α) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))) (Ne.def.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Order.succ.{u1} α _inst_1 _inst_3 a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α)))) ((fun (a : Prop) (a_1 : Prop) (e_1 : Eq.{1} Prop a a_1) => congr_arg.{1, 1} Prop Prop a a_1 Not e_1) (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Order.succ.{u1} α _inst_1 _inst_3 a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) False (propext (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Order.succ.{u1} α _inst_1 _inst_3 a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) False ((fun {α : Type.{u1}} {a : α} => iff_false_intro (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))) (WithBot.coe_ne_bot.{u1} α a)) α (Order.succ.{u1} α _inst_1 _inst_3 a))))) (propext (Not False) True not_false_iff))) trivial) a ha))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : SuccOrder.{u1} α _inst_1] (a : WithBot.{u1} α) (ha : Ne.{succ u1} (WithBot.{u1} α) a (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))), Eq.{succ u1} α (Order.succ.{u1} α _inst_1 _inst_3 (WithBot.unbot.{u1} α a ha)) (WithBot.unbot.{u1} α (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.instSuccOrderWithBotPreorder.{u1} α _inst_1 _inst_2 _inst_3) a) (WithBot.recBotCoe.{u1, 0} α (fun (a : WithBot.{u1} α) => (Ne.{succ u1} (WithBot.{u1} α) a (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))) -> (Ne.{succ u1} (WithBot.{u1} α) (Order.succ.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α _inst_1) (WithBot.instSuccOrderWithBotPreorder.{u1} α _inst_1 _inst_2 _inst_3) a) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)))) (fun (ha : Ne.{succ u1} (WithBot.{u1} α) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))) => of_eq_true (Not (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)))) (Eq.trans.{1} Prop (Not (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)))) (Not False) True (congrArg.{1, 1} Prop Prop (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))) False Not (Mathlib.Order.WithBot._auxLemma.3.{u1} α (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))) not_false_eq_true)) (fun (a : α) (ha : Ne.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α a) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))) => of_eq_true (Not (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (Order.succ.{u1} α _inst_1 _inst_3 a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)))) (Eq.trans.{1} Prop (Not (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (Order.succ.{u1} α _inst_1 _inst_3 a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α)))) (Not False) True (congrArg.{1, 1} Prop Prop (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (Order.succ.{u1} α _inst_1 _inst_3 a)) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))) False Not (Mathlib.Order.WithBot._auxLemma.3.{u1} α (Order.succ.{u1} α _inst_1 _inst_3 a))) not_false_eq_true)) a ha))
Case conversion may be inaccurate. Consider using '#align with_bot.succ_unbot WithBot.succ_unbotₓ'. -/
@[simp]
theorem succ_unbot :
    ∀ (a : WithBot α) (ha : a ≠ ⊥),
      succ (a.unbot ha) = (succ a).unbot (by induction a using WithBot.recBotCoe <;> simp)
  | ⊥, ha => (ha rfl).elim
  | (a : α), ha => rfl
#align with_bot.succ_unbot WithBot.succ_unbot

end Succ

section Pred

variable [DecidableEq α] [PartialOrder α] [OrderBot α] [PredOrder α]

instance : PredOrder (WithBot α)
    where
  pred a :=
    match a with
    | ⊥ => ⊥
    | some a => ite (a = ⊥) ⊥ (some (pred a))
  pred_le a := by
    cases a
    · exact bot_le
    change ite _ _ _ ≤ _
    split_ifs
    · exact bot_le
    · exact some_le_some.2 (pred_le a)
  min_of_le_pred a ha := by
    cases a
    · exact isMin_bot
    change _ ≤ ite _ _ _ at ha
    split_ifs  at ha with ha'
    · exact (not_coe_le_bot _ ha).elim
    · rw [some_le_some, le_pred_iff_eq_bot] at ha
      exact (ha' ha).elim
  le_pred_of_lt a b h := by
    cases a
    · exact bot_le
    cases b
    · exact (not_lt_bot h).elim
    rw [some_lt_some] at h
    change _ ≤ ite _ _ _
    split_ifs with hb
    · rw [hb] at h
      exact (not_lt_bot h).elim
    · exact some_le_some.2 (le_pred_of_lt h)
  le_of_pred_lt a b h := by
    cases b
    · exact (not_lt_bot h).elim
    cases a
    · exact bot_le
    change ite _ _ _ < _ at h
    rw [some_le_some]
    split_ifs  at h with ha
    · rw [ha]
      exact bot_le
    · exact le_of_pred_lt (some_lt_some.1 h)

/- warning: with_bot.pred_coe_bot -> WithBot.pred_coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)], Eq.{succ u1} (WithBot.{u1} α) (Order.pred.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (WithBot.predOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 _inst_4) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3)))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.hasBot.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)], Eq.{succ u1} (WithBot.{u1} α) (Order.pred.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (WithBot.instPredOrderWithBotPreorderToPreorder.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 _inst_4) (WithBot.some.{u1} α (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3)))) (Bot.bot.{u1} (WithBot.{u1} α) (WithBot.bot.{u1} α))
Case conversion may be inaccurate. Consider using '#align with_bot.pred_coe_bot WithBot.pred_coe_botₓ'. -/
@[simp]
theorem pred_coe_bot : pred ↑(⊥ : α) = (⊥ : WithBot α) :=
  dif_pos rfl
#align with_bot.pred_coe_bot WithBot.pred_coe_bot

/- warning: with_bot.pred_coe_of_ne_bot -> WithBot.pred_coe_of_ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)] {a : α}, (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3))) -> (Eq.{succ u1} (WithBot.{u1} α) (Order.pred.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (WithBot.predOrder.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 _inst_4) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) a)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) _inst_4 a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))] [_inst_4 : PredOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)] {a : α}, (Ne.{succ u1} α a (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) _inst_3))) -> (Eq.{succ u1} (WithBot.{u1} α) (Order.pred.{u1} (WithBot.{u1} α) (WithBot.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) (WithBot.instPredOrderWithBotPreorderToPreorder.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 _inst_3 _inst_4) (WithBot.some.{u1} α a)) (WithBot.some.{u1} α (Order.pred.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2) _inst_4 a)))
Case conversion may be inaccurate. Consider using '#align with_bot.pred_coe_of_ne_bot WithBot.pred_coe_of_ne_botₓ'. -/
theorem pred_coe_of_ne_bot {a : α} (h : a ≠ ⊥) : pred (↑a : WithBot α) = ↑(pred a) :=
  dif_neg h
#align with_bot.pred_coe_of_ne_bot WithBot.pred_coe_of_ne_bot

end Pred

/-! #### Adding a `⊥` to a `no_min_order` -/


section Succ

variable [Preorder α] [NoMinOrder α]

instance [hα : Nonempty α] : IsEmpty (SuccOrder (WithBot α)) :=
  ⟨by
    intro
    cases' h : succ (⊥ : WithBot α) with a ha
    · exact hα.elim fun a => (max_of_succ_le h.le).not_lt <| bot_lt_coe a
    · obtain ⟨c, hc⟩ := exists_lt a
      rw [← some_lt_some, ← h] at hc
      exact (le_of_lt_succ hc).not_lt (none_lt_some _)⟩

end Succ

section Pred

variable [Preorder α] [NoMinOrder α] [PredOrder α]

#print WithBot.predOrderOfNoMinOrder /-
instance predOrderOfNoMinOrder : PredOrder (WithBot α)
    where
  pred a :=
    match a with
    | ⊥ => ⊥
    | some a => some (pred a)
  pred_le a := by
    cases a
    · exact bot_le
    · exact some_le_some.2 (pred_le a)
  min_of_le_pred a ha := by
    cases a
    · exact isMin_bot
    · exact (not_isMin _ <| min_of_le_pred <| some_le_some.1 ha).elim
  le_pred_of_lt a b h := by
    cases b
    · exact (not_lt_bot h).elim
    cases a
    · exact bot_le
    · exact some_le_some.2 (le_pred_of_lt <| some_lt_some.1 h)
  le_of_pred_lt a b h := by
    cases b
    · exact (not_lt_bot h).elim
    cases a
    · exact bot_le
    · exact some_le_some.2 (le_of_pred_lt <| some_lt_some.1 h)
#align with_bot.pred_order_of_no_min_order WithBot.predOrderOfNoMinOrder
-/

#print WithBot.pred_coe /-
@[simp]
theorem pred_coe (a : α) : pred (↑a : WithBot α) = ↑(pred a) :=
  rfl
#align with_bot.pred_coe WithBot.pred_coe
-/

end Pred

end WithBot

/-! ### Archimedeanness -/


#print IsSuccArchimedean /-
/-- A `succ_order` is succ-archimedean if one can go from any two comparable elements by iterating
`succ` -/
class IsSuccArchimedean (α : Type _) [Preorder α] [SuccOrder α] : Prop where
  exists_succ_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, (succ^[n]) a = b
#align is_succ_archimedean IsSuccArchimedean
-/

#print IsPredArchimedean /-
/-- A `pred_order` is pred-archimedean if one can go from any two comparable elements by iterating
`pred` -/
class IsPredArchimedean (α : Type _) [Preorder α] [PredOrder α] : Prop where
  exists_pred_iterate_of_le {a b : α} (h : a ≤ b) : ∃ n, (pred^[n]) b = a
#align is_pred_archimedean IsPredArchimedean
-/

export IsSuccArchimedean (exists_succ_iterate_of_le)

export IsPredArchimedean (exists_pred_iterate_of_le)

section Preorder

variable [Preorder α]

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

instance : IsPredArchimedean αᵒᵈ :=
  ⟨fun a b h => by convert exists_succ_iterate_of_le h.of_dual⟩

#print LE.le.exists_succ_iterate /-
theorem LE.le.exists_succ_iterate (h : a ≤ b) : ∃ n, (succ^[n]) a = b :=
  exists_succ_iterate_of_le h
#align has_le.le.exists_succ_iterate LE.le.exists_succ_iterate
-/

#print exists_succ_iterate_iff_le /-
theorem exists_succ_iterate_iff_le : (∃ n, (succ^[n]) a = b) ↔ a ≤ b :=
  by
  refine' ⟨_, exists_succ_iterate_of_le⟩
  rintro ⟨n, rfl⟩
  exact id_le_iterate_of_id_le le_succ n a
#align exists_succ_iterate_iff_le exists_succ_iterate_iff_le
-/

#print Succ.rec /-
/-- Induction principle on a type with a `succ_order` for all elements above a given element `m`. -/
@[elab_as_elim]
theorem Succ.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (succ n)) ⦃n : α⦄
    (hmn : m ≤ n) : P n := by
  obtain ⟨n, rfl⟩ := hmn.exists_succ_iterate; clear hmn
  induction' n with n ih
  · exact h0
  · rw [Function.iterate_succ_apply']
    exact h1 _ (id_le_iterate_of_id_le le_succ n m) ih
#align succ.rec Succ.rec
-/

#print Succ.rec_iff /-
theorem Succ.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) {a b : α} (h : a ≤ b) :
    p a ↔ p b := by
  obtain ⟨n, rfl⟩ := h.exists_succ_iterate
  exact iterate.rec (fun b => p a ↔ p b) (fun c hc => hc.trans (hsucc _)) Iff.rfl n
#align succ.rec_iff Succ.rec_iff
-/

end SuccOrder

section PredOrder

variable [PredOrder α] [IsPredArchimedean α] {a b : α}

instance : IsSuccArchimedean αᵒᵈ :=
  ⟨fun a b h => by convert exists_pred_iterate_of_le h.of_dual⟩

#print LE.le.exists_pred_iterate /-
theorem LE.le.exists_pred_iterate (h : a ≤ b) : ∃ n, (pred^[n]) b = a :=
  exists_pred_iterate_of_le h
#align has_le.le.exists_pred_iterate LE.le.exists_pred_iterate
-/

#print exists_pred_iterate_iff_le /-
theorem exists_pred_iterate_iff_le : (∃ n, (pred^[n]) b = a) ↔ a ≤ b :=
  @exists_succ_iterate_iff_le αᵒᵈ _ _ _ _ _
#align exists_pred_iterate_iff_le exists_pred_iterate_iff_le
-/

#print Pred.rec /-
/-- Induction principle on a type with a `pred_order` for all elements below a given element `m`. -/
@[elab_as_elim]
theorem Pred.rec {P : α → Prop} {m : α} (h0 : P m) (h1 : ∀ n, n ≤ m → P n → P (pred n)) ⦃n : α⦄
    (hmn : n ≤ m) : P n :=
  @Succ.rec αᵒᵈ _ _ _ _ _ h0 h1 _ hmn
#align pred.rec Pred.rec
-/

#print Pred.rec_iff /-
theorem Pred.rec_iff {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) {a b : α} (h : a ≤ b) :
    p a ↔ p b :=
  (@Succ.rec_iff αᵒᵈ _ _ _ _ hsucc _ _ h).symm
#align pred.rec_iff Pred.rec_iff
-/

end PredOrder

end Preorder

section LinearOrder

variable [LinearOrder α]

section SuccOrder

variable [SuccOrder α] [IsSuccArchimedean α] {a b : α}

#print exists_succ_iterate_or /-
theorem exists_succ_iterate_or : (∃ n, (succ^[n]) a = b) ∨ ∃ n, (succ^[n]) b = a :=
  (le_total a b).imp exists_succ_iterate_of_le exists_succ_iterate_of_le
#align exists_succ_iterate_or exists_succ_iterate_or
-/

#print Succ.rec_linear /-
theorem Succ.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (succ a)) (a b : α) : p a ↔ p b :=
  (le_total a b).elim (Succ.rec_iff hsucc) fun h => (Succ.rec_iff hsucc h).symm
#align succ.rec_linear Succ.rec_linear
-/

end SuccOrder

section PredOrder

variable [PredOrder α] [IsPredArchimedean α] {a b : α}

#print exists_pred_iterate_or /-
theorem exists_pred_iterate_or : (∃ n, (pred^[n]) b = a) ∨ ∃ n, (pred^[n]) a = b :=
  (le_total a b).imp exists_pred_iterate_of_le exists_pred_iterate_of_le
#align exists_pred_iterate_or exists_pred_iterate_or
-/

#print Pred.rec_linear /-
theorem Pred.rec_linear {p : α → Prop} (hsucc : ∀ a, p a ↔ p (pred a)) (a b : α) : p a ↔ p b :=
  (le_total a b).elim (Pred.rec_iff hsucc) fun h => (Pred.rec_iff hsucc h).symm
#align pred.rec_linear Pred.rec_linear
-/

end PredOrder

end LinearOrder

section IsWellOrder

variable [LinearOrder α]

#print IsWellOrder.toIsPredArchimedean /-
instance (priority := 100) IsWellOrder.toIsPredArchimedean [h : IsWellOrder α (· < ·)]
    [PredOrder α] : IsPredArchimedean α :=
  ⟨fun a => by
    refine' WellFounded.fix h.wf fun b ih hab => _
    replace hab := hab.eq_or_lt
    rcases hab with (rfl | hab)
    · exact ⟨0, rfl⟩
    cases' le_or_lt b (pred b) with hb hb
    · cases (min_of_le_pred hb).not_lt hab
    obtain ⟨k, hk⟩ := ih (pred b) hb (le_pred_of_lt hab)
    refine' ⟨k + 1, _⟩
    rw [iterate_add_apply, iterate_one, hk]⟩
#align is_well_order.to_is_pred_archimedean IsWellOrder.toIsPredArchimedean
-/

#print IsWellOrder.toIsSuccArchimedean /-
instance (priority := 100) IsWellOrder.toIsSuccArchimedean [h : IsWellOrder α (· > ·)]
    [SuccOrder α] : IsSuccArchimedean α := by convert@OrderDual.isSuccArchimedean αᵒᵈ _ _ _
#align is_well_order.to_is_succ_archimedean IsWellOrder.toIsSuccArchimedean
-/

end IsWellOrder

section OrderBot

variable [Preorder α] [OrderBot α] [SuccOrder α] [IsSuccArchimedean α]

/- warning: succ.rec_bot -> Succ.rec_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : SuccOrder.{u1} α _inst_1] [_inst_4 : IsSuccArchimedean.{u1} α _inst_1 _inst_3] (p : α -> Prop), (p (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) -> (forall (a : α), (p a) -> (p (Order.succ.{u1} α _inst_1 _inst_3 a))) -> (forall (a : α), p a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : SuccOrder.{u1} α _inst_1] [_inst_4 : IsSuccArchimedean.{u1} α _inst_1 _inst_3] (p : α -> Prop), (p (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) -> (forall (a : α), (p a) -> (p (Order.succ.{u1} α _inst_1 _inst_3 a))) -> (forall (a : α), p a)
Case conversion may be inaccurate. Consider using '#align succ.rec_bot Succ.rec_botₓ'. -/
theorem Succ.rec_bot (p : α → Prop) (hbot : p ⊥) (hsucc : ∀ a, p a → p (succ a)) (a : α) : p a :=
  Succ.rec hbot (fun x _ h => hsucc x h) (bot_le : ⊥ ≤ a)
#align succ.rec_bot Succ.rec_bot

end OrderBot

section OrderTop

variable [Preorder α] [OrderTop α] [PredOrder α] [IsPredArchimedean α]

/- warning: pred.rec_top -> Pred.rec_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : PredOrder.{u1} α _inst_1] [_inst_4 : IsPredArchimedean.{u1} α _inst_1 _inst_3] (p : α -> Prop), (p (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) -> (forall (a : α), (p a) -> (p (Order.pred.{u1} α _inst_1 _inst_3 a))) -> (forall (a : α), p a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] [_inst_3 : PredOrder.{u1} α _inst_1] [_inst_4 : IsPredArchimedean.{u1} α _inst_1 _inst_3] (p : α -> Prop), (p (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2))) -> (forall (a : α), (p a) -> (p (Order.pred.{u1} α _inst_1 _inst_3 a))) -> (forall (a : α), p a)
Case conversion may be inaccurate. Consider using '#align pred.rec_top Pred.rec_topₓ'. -/
theorem Pred.rec_top (p : α → Prop) (htop : p ⊤) (hpred : ∀ a, p a → p (pred a)) (a : α) : p a :=
  Pred.rec htop (fun x _ h => hpred x h) (le_top : a ≤ ⊤)
#align pred.rec_top Pred.rec_top

end OrderTop

