/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Order.ConditionallyCompleteLattice.Basic
import Data.Int.LeastGreatest

#align_import data.int.conditionally_complete_order from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
## `ℤ` forms a conditionally complete linear order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The integers form a conditionally complete linear order.
-/


open Int

open scoped Classical

noncomputable section

instance : ConditionallyCompleteLinearOrder ℤ :=
  { Int.linearOrder,
    LinearOrder.toLattice with
    sSup := fun s =>
      if h : s.Nonempty ∧ BddAbove s then
        greatestOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
      else 0
    sInf := fun s =>
      if h : s.Nonempty ∧ BddBelow s then
        leastOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
      else 0
    le_cSup := by
      intro s n hs hns
      have : s.nonempty ∧ BddAbove s := ⟨⟨n, hns⟩, hs⟩
      rw [dif_pos this]
      exact (greatest_of_bdd _ _ _).2.2 n hns
    cSup_le := by
      intro s n hs hns
      have : s.nonempty ∧ BddAbove s := ⟨hs, ⟨n, hns⟩⟩
      rw [dif_pos this]
      exact hns (greatest_of_bdd _ (Classical.choose_spec this.2) _).2.1
    cInf_le := by
      intro s n hs hns
      have : s.nonempty ∧ BddBelow s := ⟨⟨n, hns⟩, hs⟩
      rw [dif_pos this]
      exact (least_of_bdd _ _ _).2.2 n hns
    le_cInf := by
      intro s n hs hns
      have : s.nonempty ∧ BddBelow s := ⟨hs, ⟨n, hns⟩⟩
      rw [dif_pos this]
      exact hns (least_of_bdd _ (Classical.choose_spec this.2) _).2.1 }

namespace Int

#print Int.csSup_eq_greatest_of_bdd /-
theorem csSup_eq_greatest_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b)
    (Hinh : ∃ z : ℤ, z ∈ s) : sSup s = greatestOfBdd b Hb Hinh :=
  by
  convert dif_pos _ using 1
  · convert coe_greatest_of_bdd_eq _ (Classical.choose_spec (⟨b, Hb⟩ : BddAbove s)) _
  · exact ⟨Hinh, b, Hb⟩
#align int.cSup_eq_greatest_of_bdd Int.csSup_eq_greatest_of_bdd
-/

#print Int.csSup_empty /-
@[simp]
theorem csSup_empty : sSup (∅ : Set ℤ) = 0 :=
  dif_neg (by simp)
#align int.cSup_empty Int.csSup_empty
-/

#print Int.csSup_of_not_bdd_above /-
theorem csSup_of_not_bdd_above {s : Set ℤ} (h : ¬BddAbove s) : sSup s = 0 :=
  dif_neg (by simp [h])
#align int.cSup_of_not_bdd_above Int.csSup_of_not_bdd_above
-/

#print Int.csInf_eq_least_of_bdd /-
theorem csInf_eq_least_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z)
    (Hinh : ∃ z : ℤ, z ∈ s) : sInf s = leastOfBdd b Hb Hinh :=
  by
  convert dif_pos _ using 1
  · convert coe_least_of_bdd_eq _ (Classical.choose_spec (⟨b, Hb⟩ : BddBelow s)) _
  · exact ⟨Hinh, b, Hb⟩
#align int.cInf_eq_least_of_bdd Int.csInf_eq_least_of_bdd
-/

#print Int.csInf_empty /-
@[simp]
theorem csInf_empty : sInf (∅ : Set ℤ) = 0 :=
  dif_neg (by simp)
#align int.cInf_empty Int.csInf_empty
-/

#print Int.csInf_of_not_bdd_below /-
theorem csInf_of_not_bdd_below {s : Set ℤ} (h : ¬BddBelow s) : sInf s = 0 :=
  dif_neg (by simp [h])
#align int.cInf_of_not_bdd_below Int.csInf_of_not_bdd_below
-/

#print Int.csSup_mem /-
theorem csSup_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddAbove s) : sSup s ∈ s :=
  by
  convert (greatest_of_bdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩
#align int.cSup_mem Int.csSup_mem
-/

#print Int.csInf_mem /-
theorem csInf_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddBelow s) : sInf s ∈ s :=
  by
  convert (least_of_bdd _ (Classical.choose_spec h2) h1).2.1
  exact dif_pos ⟨h1, h2⟩
#align int.cInf_mem Int.csInf_mem
-/

end Int

