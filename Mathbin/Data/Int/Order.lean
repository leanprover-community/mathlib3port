import Mathbin.Order.ConditionallyCompleteLattice 
import Mathbin.Data.Int.LeastGreatest

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/


open Int

open_locale Classical

noncomputable theory

-- error in Data.Int.Order: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : conditionally_complete_linear_order exprℤ() :=
{ Sup := λ
  s, if h : «expr ∧ »(s.nonempty, bdd_above s) then greatest_of_bdd (classical.some h.2) (classical.some_spec h.2) h.1 else 0,
  Inf := λ
  s, if h : «expr ∧ »(s.nonempty, bdd_below s) then least_of_bdd (classical.some h.2) (classical.some_spec h.2) h.1 else 0,
  le_cSup := begin
    intros [ident s, ident n, ident hs, ident hns],
    have [] [":", expr «expr ∧ »(s.nonempty, bdd_above s)] [":=", expr ⟨⟨n, hns⟩, hs⟩],
    rw ["[", expr dif_pos this, "]"] [],
    exact [expr (greatest_of_bdd _ _ _).2.2 n hns]
  end,
  cSup_le := begin
    intros [ident s, ident n, ident hs, ident hns],
    have [] [":", expr «expr ∧ »(s.nonempty, bdd_above s)] [":=", expr ⟨hs, ⟨n, hns⟩⟩],
    rw ["[", expr dif_pos this, "]"] [],
    exact [expr hns (greatest_of_bdd _ (classical.some_spec this.2) _).2.1]
  end,
  cInf_le := begin
    intros [ident s, ident n, ident hs, ident hns],
    have [] [":", expr «expr ∧ »(s.nonempty, bdd_below s)] [":=", expr ⟨⟨n, hns⟩, hs⟩],
    rw ["[", expr dif_pos this, "]"] [],
    exact [expr (least_of_bdd _ _ _).2.2 n hns]
  end,
  le_cInf := begin
    intros [ident s, ident n, ident hs, ident hns],
    have [] [":", expr «expr ∧ »(s.nonempty, bdd_below s)] [":=", expr ⟨hs, ⟨n, hns⟩⟩],
    rw ["[", expr dif_pos this, "]"] [],
    exact [expr hns (least_of_bdd _ (classical.some_spec this.2) _).2.1]
  end,
  ..int.linear_order,
  ..lattice_of_linear_order }

namespace Int

theorem cSup_eq_greatest_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z (_ : z ∈ s), z ≤ b)
  (Hinh : ∃ z : ℤ, z ∈ s) : Sup s = greatest_of_bdd b Hb Hinh :=
  by 
    convert dif_pos _ using 1
    ·
      convert coe_greatest_of_bdd_eq _ (Classical.some_spec (⟨b, Hb⟩ : BddAbove s)) _
    ·
      exact ⟨Hinh, b, Hb⟩

@[simp]
theorem cSup_empty : Sup (∅ : Set ℤ) = 0 :=
  dif_neg
    (by 
      simp )

theorem cSup_of_not_bdd_above {s : Set ℤ} (h : ¬BddAbove s) : Sup s = 0 :=
  dif_neg
    (by 
      simp [h])

theorem cInf_eq_least_of_bdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z (_ : z ∈ s), b ≤ z)
  (Hinh : ∃ z : ℤ, z ∈ s) : Inf s = least_of_bdd b Hb Hinh :=
  by 
    convert dif_pos _ using 1
    ·
      convert coe_least_of_bdd_eq _ (Classical.some_spec (⟨b, Hb⟩ : BddBelow s)) _
    ·
      exact ⟨Hinh, b, Hb⟩

@[simp]
theorem cInf_empty : Inf (∅ : Set ℤ) = 0 :=
  dif_neg
    (by 
      simp )

theorem cInf_of_not_bdd_below {s : Set ℤ} (h : ¬BddBelow s) : Inf s = 0 :=
  dif_neg
    (by 
      simp [h])

theorem cSup_mem {s : Set ℤ} (h1 : s.nonempty) (h2 : BddAbove s) : Sup s ∈ s :=
  by 
    convert (greatest_of_bdd _ (Classical.some_spec h2) h1).2.1 
    exact dif_pos ⟨h1, h2⟩

theorem cInf_mem {s : Set ℤ} (h1 : s.nonempty) (h2 : BddBelow s) : Inf s ∈ s :=
  by 
    convert (least_of_bdd _ (Classical.some_spec h2) h1).2.1 
    exact dif_pos ⟨h1, h2⟩

end Int

