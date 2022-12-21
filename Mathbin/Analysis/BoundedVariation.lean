/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.bounded_variation
! leanprover-community/mathlib commit 0743cc5d9d86bcd1bba10f480e948a257d65056f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.Lebesgue
import Mathbin.Analysis.Calculus.Monotone

/-!
# Functions of bounded variation

We study functions of bounded variation. In particular, we show that a bounded variation function
is a difference of monotone functions, and differentiable almost everywhere. This implies that
Lipschitz functions from the real line into finite-dimensional vector space are also differentiable
almost everywhere.

## Main definitions and results

* `evariation_on f s` is the total variation of the function `f` on the set `s`, in `ℝ≥0∞`.
* `has_bounded_variation_on f s` registers that the variation of `f` on `s` is finite.
* `has_locally_bounded_variation f s` registers that `f` has finite variation on any compact
  subinterval of `s`.

* `evariation_on.Icc_add_Icc` states that the variation of `f` on `[a, c]` is the sum of its
  variations on `[a, b]` and `[b, c]`.
* `has_locally_bounded_variation_on.exists_monotone_on_sub_monotone_on` proves that a function
  with locally bounded variation is the difference of two monotone functions.
* `lipschitz_with.has_locally_bounded_variation_on` shows that a Lipschitz function has locally
  bounded variation.
* `has_locally_bounded_variation_on.ae_differentiable_within_at` shows that a bounded variation
  function into a finite dimensional real vector space is differentiable almost everywhere.
* `lipschitz_on_with.ae_differentiable_within_at` is the same result for Lipschitz functions.

We also give several variations around these results.

## Implementation

We define the variation as an extended nonnegative real, to allow for infinite variation. This makes
it possible to use the complete linear order structure of `ℝ≥0∞`. The proofs would be much
more tedious with an `ℝ`-valued or `ℝ≥0`-valued variation, since one would always need to check
that the sets one uses are nonempty and bounded above as these are only conditionally complete.
-/


open BigOperators Nnreal Ennreal

open Set MeasureTheory

variable {α : Type _} [LinearOrder α] {E F : Type _} [PseudoEmetricSpace E] [PseudoEmetricSpace F]
  {V : Type _} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The (extended real valued) variation of a function `f` on a set `s` inside a linear order is
the supremum of the sum of `edist (f (u (i+1))) (f (u i))` over all finite increasing
sequences `u` in `s`. -/
noncomputable def evariationOn (f : α → E) (s : Set α) : ℝ≥0∞ :=
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i in Finset.range p.1, edist (f ((p.2 : ℕ → α) (i + 1))) (f ((p.2 : ℕ → α) i))
#align evariation_on evariationOn

/-- A function has bounded variation on a set `s` if its total variation there is finite. -/
def HasBoundedVariationOn (f : α → E) (s : Set α) :=
  evariationOn f s ≠ ∞
#align has_bounded_variation_on HasBoundedVariationOn

/-- A function has locally bounded variation on a set `s` if, given any interval `[a, b]` with
endpoints in `s`, then the function has finite variation on `s ∩ [a, b]`. -/
def HasLocallyBoundedVariationOn (f : α → E) (s : Set α) :=
  ∀ a b, a ∈ s → b ∈ s → HasBoundedVariationOn f (s ∩ Icc a b)
#align has_locally_bounded_variation_on HasLocallyBoundedVariationOn

/-! ## Basic computations of variation -/


namespace evariationOn

theorem nonempty_monotone_mem {s : Set α} (hs : s.Nonempty) :
    Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨fun i => x, fun i j hij => le_rfl, fun i => hx⟩⟩
#align evariation_on.nonempty_monotone_mem evariationOn.nonempty_monotone_mem

theorem sum_le (f : α → E) {s : Set α} (n : ℕ) {u : ℕ → α} (hu : Monotone u) (us : ∀ i, u i ∈ s) :
    (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ evariationOn f s := by
  let p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s } := (n, ⟨u, hu, us⟩)
  change
    (∑ i in Finset.range p.1, edist (f ((p.2 : ℕ → α) (i + 1))) (f ((p.2 : ℕ → α) i))) ≤
      evariationOn f s
  exact
    le_supᵢ
      (fun p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s } =>
        ∑ i in Finset.range p.1, edist (f ((p.2 : ℕ → α) (i + 1))) (f ((p.2 : ℕ → α) i)))
      _
#align evariation_on.sum_le evariationOn.sum_le

theorem sum_le_of_monotone_on_Iic (f : α → E) {s : Set α} {n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Iic n)) (us : ∀ i ≤ n, u i ∈ s) :
    (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ evariationOn f s := by
  let v i := if i ≤ n then u i else u n
  have vs : ∀ i, v i ∈ s := by 
    intro i
    simp only [v]
    split_ifs
    · exact us i h
    · exact us n le_rfl
  have hv : Monotone v := by 
    apply monotone_nat_of_le_succ fun i => _
    simp only [v]
    rcases lt_trichotomy i n with (hi | rfl | hi)
    · have : i + 1 ≤ n := by linarith
      simp only [hi.le, this, if_true]
      exact hu hi.le this (Nat.le_succ i)
    · simp only [le_refl, if_true, add_le_iff_nonpos_right, le_zero_iff, Nat.one_ne_zero, if_false]
    · have A : ¬i ≤ n := by linarith
      have B : ¬i + 1 ≤ n := by linarith
      simp [A, B]
  convert sum_le f n hv vs using 1
  apply Finset.sum_congr rfl fun i hi => _
  simp only [Finset.mem_range] at hi
  have : i + 1 ≤ n := by linarith
  simp only [v]
  simp [this, hi.le]
#align evariation_on.sum_le_of_monotone_on_Iic evariationOn.sum_le_of_monotone_on_Iic

theorem sum_le_of_monotone_on_Icc (f : α → E) {s : Set α} {m n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Icc m n)) (us : ∀ i ∈ Icc m n, u i ∈ s) :
    (∑ i in Finset.ico m n, edist (f (u (i + 1))) (f (u i))) ≤ evariationOn f s := by
  rcases le_or_lt n m with (hnm | hmn)
  · simp only [Finset.Ico_eq_empty_of_le hnm, Finset.sum_empty, zero_le']
  let v i := u (m + i)
  have hv : MonotoneOn v (Iic (n - m)) := by
    intro a ha b hb hab
    simp only [le_tsub_iff_left hmn.le, mem_Iic] at ha hb
    exact hu ⟨le_add_right le_rfl, ha⟩ ⟨le_add_right le_rfl, hb⟩ (add_le_add le_rfl hab)
  have vs : ∀ i ∈ Iic (n - m), v i ∈ s := by 
    intro i hi
    simp only [le_tsub_iff_left hmn.le, mem_Iic] at hi
    exact us _ ⟨le_add_right le_rfl, hi⟩
  calc
    (∑ i in Finset.ico m n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i in Finset.range (n - m), edist (f (u (m + i + 1))) (f (u (m + i))) :=
      by 
      rw [Finset.range_eq_Ico]
      convert (Finset.sum_Ico_add (fun i => edist (f (u (i + 1))) (f (u i))) 0 (n - m) m).symm
      · rw [zero_add]
      · rw [tsub_add_cancel_of_le hmn.le]
    _ = ∑ i in Finset.range (n - m), edist (f (v (i + 1))) (f (v i)) := by
      apply Finset.sum_congr rfl fun i hi => _
      simp only [v, add_assoc]
    _ ≤ evariationOn f s := sum_le_of_monotone_on_Iic f hv vs
    
#align evariation_on.sum_le_of_monotone_on_Icc evariationOn.sum_le_of_monotone_on_Icc

theorem mono (f : α → E) {s t : Set α} (hst : t ⊆ s) : evariationOn f t ≤ evariationOn f s := by
  apply supᵢ_le _
  rintro ⟨n, ⟨u, hu, ut⟩⟩
  exact sum_le f n hu fun i => hst (ut i)
#align evariation_on.mono evariationOn.mono

theorem HasBoundedVariationOn.mono {f : α → E} {s : Set α} (h : HasBoundedVariationOn f s)
    {t : Set α} (ht : t ⊆ s) : HasBoundedVariationOn f t :=
  (lt_of_le_of_lt (evariationOn.mono f ht) (lt_top_iff_ne_top.2 h)).Ne
#align has_bounded_variation_on.mono HasBoundedVariationOn.mono

theorem HasBoundedVariationOn.hasLocallyBoundedVariationOn {f : α → E} {s : Set α}
    (h : HasBoundedVariationOn f s) : HasLocallyBoundedVariationOn f s := fun x y hx hy =>
  h.mono (inter_subset_left _ _)
#align
  has_bounded_variation_on.has_locally_bounded_variation_on HasBoundedVariationOn.hasLocallyBoundedVariationOn

@[simp]
protected theorem subsingleton (f : α → E) {s : Set α} (hs : s.Subsingleton) :
    evariationOn f s = 0 := by 
  apply le_antisymm _ (zero_le _)
  apply supᵢ_le _
  rintro ⟨n, ⟨u, hu, ut⟩⟩
  have : ∀ i, u i = u 0 := fun i => hs (ut _) (ut _)
  simp [Subtype.coe_mk, le_zero_iff, Finset.sum_eq_zero_iff, Finset.mem_range, this]
#align evariation_on.subsingleton evariationOn.subsingleton

theorem edist_le (f : α → E) {s : Set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    edist (f x) (f y) ≤ evariationOn f s := by
  wlog (discharger := tactic.skip) hxy : x ≤ y := le_total x y using x y, y x
  swap
  · intro hx hy
    rw [edist_comm]
    exact this hy hx
  let u : ℕ → α := fun n => if n = 0 then x else y
  have hu : Monotone u := by 
    intro m n hmn
    dsimp only [u]
    split_ifs
    exacts[le_rfl, hxy, by linarith [pos_iff_ne_zero.2 h], le_rfl]
  have us : ∀ i, u i ∈ s := by 
    intro i
    dsimp only [u]
    split_ifs
    exacts[hx, hy]
  convert sum_le f 1 hu us
  simp [u, edist_comm]
#align evariation_on.edist_le evariationOn.edist_le

theorem HasBoundedVariationOn.dist_le {E : Type _} [PseudoMetricSpace E] {f : α → E} {s : Set α}
    (h : HasBoundedVariationOn f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    dist (f x) (f y) ≤ (evariationOn f s).toReal := by
  rw [← Ennreal.of_real_le_of_real_iff Ennreal.to_real_nonneg, Ennreal.of_real_to_real h, ←
    edist_dist]
  exact edist_le f hx hy
#align has_bounded_variation_on.dist_le HasBoundedVariationOn.dist_le

theorem HasBoundedVariationOn.sub_le {f : α → ℝ} {s : Set α} (h : HasBoundedVariationOn f s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : f x - f y ≤ (evariationOn f s).toReal := by
  apply (le_abs_self _).trans
  rw [← Real.dist_eq]
  exact h.dist_le hx hy
#align has_bounded_variation_on.sub_le HasBoundedVariationOn.sub_le

/-- Consider a monotone function `u` parameterizing some points of a set `s`. Given `x ∈ s`, then
one can find another monotone function `v` parameterizing the same points as `u`, with `x` added.
In particular, the variation of a function along `u` is bounded by its variation along `v`. -/
theorem add_point (f : α → E) {s : Set α} {x : α} (hx : x ∈ s) (u : ℕ → α) (hu : Monotone u)
    (us : ∀ i, u i ∈ s) (n : ℕ) :
    ∃ (v : ℕ → α)(m : ℕ),
      Monotone v ∧
        (∀ i, v i ∈ s) ∧
          x ∈ v '' Iio m ∧
            (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
              ∑ j in Finset.range m, edist (f (v (j + 1))) (f (v j)) :=
  by 
  rcases le_or_lt (u n) x with (h | h)
  · let v i := if i ≤ n then u i else x
    have vs : ∀ i, v i ∈ s := by 
      intro i
      simp only [v]
      split_ifs
      · exact us i
      · exact hx
    have hv : Monotone v := by 
      apply monotone_nat_of_le_succ fun i => _
      simp only [v]
      rcases lt_trichotomy i n with (hi | rfl | hi)
      · have : i + 1 ≤ n := by linarith
        simp only [hi.le, this, if_true]
        exact hu (Nat.le_succ i)
      ·
        simp only [le_refl, if_true, add_le_iff_nonpos_right, le_zero_iff, Nat.one_ne_zero,
          if_false, h]
      · have A : ¬i ≤ n := by linarith
        have B : ¬i + 1 ≤ n := by linarith
        simp only [A, B, if_false]
    refine' ⟨v, n + 2, hv, vs, (mem_image _ _ _).2 ⟨n + 1, _, _⟩, _⟩
    · rw [mem_Iio]
      exact Nat.lt_succ_self (n + 1)
    · have : ¬n + 1 ≤ n := by linarith
      simp only [this, ite_eq_right_iff, IsEmpty.forall_iff]
    ·
      calc
        (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
            ∑ i in Finset.range n, edist (f (v (i + 1))) (f (v i)) :=
          by 
          apply Finset.sum_congr rfl fun i hi => _
          simp only [Finset.mem_range] at hi
          have : i + 1 ≤ n := by linarith
          dsimp only [v]
          simp only [hi.le, this, if_true]
        _ ≤ ∑ j in Finset.range (n + 2), edist (f (v (j + 1))) (f (v j)) :=
          Finset.sum_le_sum_of_subset (Finset.range_mono (by linarith))
        
  have exists_N : ∃ N, N ≤ n ∧ x < u N := ⟨n, le_rfl, h⟩
  let N := Nat.find exists_N
  have hN : N ≤ n ∧ x < u N := Nat.find_spec exists_N
  let w : ℕ → α := fun i => if i < N then u i else if i = N then x else u (i - 1)
  have ws : ∀ i, w i ∈ s := by 
    dsimp only [w]
    intro i
    split_ifs
    exacts[us _, hx, us _]
  have hw : Monotone w := by 
    apply monotone_nat_of_le_succ fun i => _
    dsimp only [w]
    rcases lt_trichotomy (i + 1) N with (hi | hi | hi)
    · have : i < N := by linarith
      simp only [hi, this, if_true]
      exact hu (Nat.le_succ _)
    · have A : i < N := by linarith
      have B : ¬i + 1 < N := by linarith
      rw [if_pos A, if_neg B, if_pos hi]
      have T := Nat.find_min exists_N A
      push_neg  at T
      exact T (A.le.trans hN.1)
    · have A : ¬i < N := by linarith
      have B : ¬i + 1 < N := by linarith
      have C : ¬i + 1 = N := by linarith
      have D : i + 1 - 1 = i := Nat.pred_succ i
      rw [if_neg A, if_neg B, if_neg C, D]
      split_ifs
      · exact hN.2.le.trans (hu (by linarith))
      · exact hu (Nat.pred_le _)
  refine' ⟨w, n + 1, hw, ws, (mem_image _ _ _).2 ⟨N, hN.1.trans_lt (Nat.lt_succ_self n), _⟩, _⟩
  · dsimp only [w]
    rw [if_neg (lt_irrefl N), if_pos rfl]
  rcases eq_or_lt_of_le (zero_le N) with (Npos | Npos)
  ·
    calc
      (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i in Finset.range n, edist (f (w (1 + i + 1))) (f (w (1 + i))) :=
        by 
        apply Finset.sum_congr rfl fun i hi => _
        dsimp only [w]
        simp only [← Npos, Nat.not_lt_zero, Nat.add_succ_sub_one, add_zero, if_false,
          add_eq_zero_iff, Nat.one_ne_zero, false_and_iff, Nat.succ_add_sub_one, zero_add]
        rw [add_comm 1 i]
      _ = ∑ i in Finset.ico 1 (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        rw [Finset.range_eq_Ico]
        exact Finset.sum_Ico_add (fun i => edist (f (w (i + 1))) (f (w i))) 0 n 1
      _ ≤ ∑ j in Finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) := by
        apply Finset.sum_le_sum_of_subset _
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_subset_Ico zero_le_one le_rfl
      
  ·
    calc
      (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ((∑ i in Finset.ico 0 (N - 1), edist (f (u (i + 1))) (f (u i))) +
              ∑ i in Finset.ico (N - 1) N, edist (f (u (i + 1))) (f (u i))) +
            ∑ i in Finset.ico N n, edist (f (u (i + 1))) (f (u i)) :=
        by 
        rw [Finset.sum_Ico_consecutive, Finset.sum_Ico_consecutive, Finset.range_eq_Ico]
        · exact zero_le _
        · exact hN.1
        · exact zero_le _
        · exact Nat.pred_le _
      _ =
          (∑ i in Finset.ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              edist (f (u N)) (f (u (N - 1))) +
            ∑ i in Finset.ico N n, edist (f (w (1 + i + 1))) (f (w (1 + i))) :=
        by 
        congr 1; congr 1
        · apply Finset.sum_congr rfl fun i hi => _
          simp only [Finset.mem_Ico, zero_le', true_and_iff] at hi
          dsimp only [w]
          have A : i + 1 < N := Nat.lt_pred_iff.1 hi
          have B : i < N := by linarith
          rw [if_pos A, if_pos B]
        · have A : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
          have : Finset.ico (N - 1) N = {N - 1} := by rw [← Nat.Ico_succ_singleton, A]
          simp only [this, A, Finset.sum_singleton]
        · apply Finset.sum_congr rfl fun i hi => _
          simp only [Finset.mem_Ico] at hi
          dsimp only [w]
          have A : ¬1 + i + 1 < N := by linarith
          have B : ¬1 + i + 1 = N := by linarith
          have C : ¬1 + i < N := by linarith
          have D : ¬1 + i = N := by linarith
          rw [if_neg A, if_neg B, if_neg C, if_neg D]
          congr 3 <;>
            · rw [eq_tsub_iff_add_eq_of_le]
              · abel
              · linarith
      _ =
          (∑ i in Finset.ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              edist (f (w (N + 1))) (f (w (N - 1))) +
            ∑ i in Finset.ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) :=
        by 
        congr 1; congr 1
        · dsimp only [w]
          have A : ¬N + 1 < N := by linarith
          have B : N - 1 < N := Nat.pred_lt Npos.ne'
          simp only [A, not_and, not_lt, Nat.succ_ne_self, Nat.add_succ_sub_one, add_zero, if_false,
            B, if_true]
        · exact Finset.sum_Ico_add (fun i => edist (f (w (i + 1))) (f (w i))) N n 1
      _ ≤
          ((∑ i in Finset.ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              ∑ i in Finset.ico (N - 1) (N + 1), edist (f (w (i + 1))) (f (w i))) +
            ∑ i in Finset.ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) :=
        by 
        refine' add_le_add (add_le_add le_rfl _) le_rfl
        have A : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
        have B : N - 1 + 1 < N + 1 := by linarith
        have C : N - 1 < N + 1 := by linarith
        rw [Finset.sum_eq_sum_Ico_succ_bot C, Finset.sum_eq_sum_Ico_succ_bot B, A, Finset.Ico_self,
          Finset.sum_empty, add_zero, add_comm (edist _ _)]
        exact edist_triangle _ _ _
      _ = ∑ j in Finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) := by
        rw [Finset.sum_Ico_consecutive, Finset.sum_Ico_consecutive, Finset.range_eq_Ico]
        · exact zero_le _
        · linarith
        · exact zero_le _
        · linarith
      
#align evariation_on.add_point evariationOn.add_point

/-- The variation of a function on the union of two sets `s` and `t`, with `s` to the left of `t`,
bounds the sum of the variations along `s` and `t`. -/
theorem add_le_union (f : α → E) {s t : Set α} (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
    evariationOn f s + evariationOn f t ≤ evariationOn f (s ∪ t) := by
  by_cases hs : s = ∅
  · simp [hs]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 hs)
  by_cases ht : t = ∅
  · simp [ht]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ t } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 ht)
  refine' Ennreal.supr_add_supr_le _
  /- We start from two sequences `u` and `v` along `s` and `t` respectively, and we build a new
    sequence `w` along `s ∪ t` by juxtaposing them. Its variation is larger than the sum of the
    variations. -/
  rintro ⟨n, ⟨u, hu, us⟩⟩ ⟨m, ⟨v, hv, vt⟩⟩
  let w i := if i ≤ n then u i else v (i - (n + 1))
  have wst : ∀ i, w i ∈ s ∪ t := by 
    intro i
    by_cases hi : i ≤ n
    · simp [w, hi, us]
    · simp [w, hi, vt]
  have hw : Monotone w := by 
    intro i j hij
    dsimp only [w]
    split_ifs
    · exact hu hij
    · apply h _ (us _) _ (vt _)
    · linarith
    · apply hv (tsub_le_tsub hij le_rfl)
  calc
    ((∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          ∑ i : ℕ in Finset.range m, edist (f (v (i + 1))) (f (v i))) =
        (∑ i in Finset.range n, edist (f (w (i + 1))) (f (w i))) +
          ∑ i : ℕ in Finset.range m, edist (f (w (n + 1 + i + 1))) (f (w (n + 1 + i))) :=
      by 
      dsimp only [w]
      congr 1
      · apply Finset.sum_congr rfl fun i hi => _
        simp only [Finset.mem_range] at hi
        have : i + 1 ≤ n := by linarith
        simp [hi.le, this]
      · apply Finset.sum_congr rfl fun i hi => _
        simp only [Finset.mem_range] at hi
        have A : ¬n + 1 + i + 1 ≤ n := by linarith
        have B : ¬n + 1 + i ≤ n := by linarith
        have C : n + 1 + i - n = i + 1 := by
          rw [tsub_eq_iff_eq_add_of_le]
          · abel
          · linarith
        simp only [A, B, C, Nat.succ_sub_succ_eq_sub, if_false, add_tsub_cancel_left]
    _ =
        (∑ i in Finset.range n, edist (f (w (i + 1))) (f (w i))) +
          ∑ i : ℕ in Finset.ico (n + 1) (n + 1 + m), edist (f (w (i + 1))) (f (w i)) :=
      by 
      congr 1
      rw [Finset.range_eq_Ico]
      convert Finset.sum_Ico_add (fun i : ℕ => edist (f (w (i + 1))) (f (w i))) 0 m (n + 1) using
          3 <;>
        abel
    _ ≤ ∑ i in Finset.range (n + 1 + m), edist (f (w (i + 1))) (f (w i)) := by
      rw [← Finset.sum_union]
      · apply Finset.sum_le_sum_of_subset _
        rintro i hi
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at hi⊢
        cases hi
        · linarith
        · exact hi.2
      · apply Finset.disjoint_left.2 fun i hi h'i => _
        simp only [Finset.mem_Ico, Finset.mem_range] at hi h'i
        linarith [h'i.1]
    _ ≤ evariationOn f (s ∪ t) := sum_le f _ hw wst
    
#align evariation_on.add_le_union evariationOn.add_le_union

/-- If a set `s` is to the left of a set `t`, and both contain the boundary point `x`, then
the variation of `f` along `s ∪ t` is the sum of the variations. -/
theorem union (f : α → E) {s t : Set α} {x : α} (hs : IsGreatest s x) (ht : IsLeast t x) :
    evariationOn f (s ∪ t) = evariationOn f s + evariationOn f t := by
  classical 
    apply le_antisymm _ (evariationOn.add_le_union f fun a ha b hb => le_trans (hs.2 ha) (ht.2 hb))
    apply supᵢ_le _
    rintro ⟨n, ⟨u, hu, ust⟩⟩
    obtain ⟨v, m, hv, vst, xv, huv⟩ :
      ∃ (v : ℕ → α)(m : ℕ),
        Monotone v ∧
          (∀ i, v i ∈ s ∪ t) ∧
            x ∈ v '' Iio m ∧
              (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
                ∑ j in Finset.range m, edist (f (v (j + 1))) (f (v j))
    exact evariationOn.add_point f (mem_union_left t hs.1) u hu ust n
    obtain ⟨N, hN, Nx⟩ : ∃ N, N < m ∧ v N = x
    exact xv
    calc
      (∑ j in Finset.range n, edist (f (u (j + 1))) (f (u j))) ≤
          ∑ j in Finset.range m, edist (f (v (j + 1))) (f (v j)) :=
        huv
      _ =
          (∑ j in Finset.ico 0 N, edist (f (v (j + 1))) (f (v j))) +
            ∑ j in Finset.ico N m, edist (f (v (j + 1))) (f (v j)) :=
        by rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (zero_le _) hN.le]
      _ ≤ evariationOn f s + evariationOn f t := by
        refine' add_le_add _ _
        · apply sum_le_of_monotone_on_Icc _ (hv.monotone_on _) fun i hi => _
          rcases vst i with (h | h)
          · exact h
          have : v i = x := by 
            apply le_antisymm
            · rw [← Nx]
              exact hv hi.2
            · exact ht.2 h
          rw [this]
          exact hs.1
        · apply sum_le_of_monotone_on_Icc _ (hv.monotone_on _) fun i hi => _
          rcases vst i with (h | h)
          swap
          · exact h
          have : v i = x := by 
            apply le_antisymm
            · exact hs.2 h
            · rw [← Nx]
              exact hv hi.1
          rw [this]
          exact ht.1
      
#align evariation_on.union evariationOn.union

theorem Icc_add_Icc (f : α → E) {s : Set α} {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s) :
    evariationOn f (s ∩ Icc a b) + evariationOn f (s ∩ Icc b c) = evariationOn f (s ∩ Icc a c) := by
  have A : IsGreatest (s ∩ Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, (inter_subset_right _ _).trans Icc_subset_Iic_self⟩
  have B : IsLeast (s ∩ Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, (inter_subset_right _ _).trans Icc_subset_Ici_self⟩
  rw [← evariationOn.union f A B, ← inter_union_distrib_left, Icc_union_Icc_eq_Icc hab hbc]
#align evariation_on.Icc_add_Icc evariationOn.Icc_add_Icc

end evariationOn

/-! ## Monotone functions and bounded variation -/


theorem MonotoneOn.evariation_on_le {f : α → ℝ} {s : Set α} (hf : MonotoneOn f s) {a b : α}
    (as : a ∈ s) (bs : b ∈ s) : evariationOn f (s ∩ Icc a b) ≤ Ennreal.ofReal (f b - f a) := by
  apply supᵢ_le _
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i in Finset.range n, Ennreal.ofReal (f (u (i + 1)) - f (u i)) :=
      by 
      apply Finset.sum_congr rfl fun i hi => _
      simp only [Finset.mem_range] at hi
      rw [edist_dist, Real.dist_eq, abs_of_nonneg]
      exact sub_nonneg_of_le (hf (us i).1 (us (i + 1)).1 (hu (Nat.le_succ _)))
    _ = Ennreal.ofReal (∑ i in Finset.range n, f (u (i + 1)) - f (u i)) := by
      rw [Ennreal.of_real_sum_of_nonneg]
      intro i hi
      exact sub_nonneg_of_le (hf (us i).1 (us (i + 1)).1 (hu (Nat.le_succ _)))
    _ = Ennreal.ofReal (f (u n) - f (u 0)) := by rw [Finset.sum_range_sub fun i => f (u i)]
    _ ≤ Ennreal.ofReal (f b - f a) := by
      apply Ennreal.of_real_le_of_real
      exact sub_le_sub (hf (us n).1 bs (us n).2.2) (hf as (us 0).1 (us 0).2.1)
    
#align monotone_on.evariation_on_le MonotoneOn.evariation_on_le

theorem MonotoneOn.hasLocallyBoundedVariationOn {f : α → ℝ} {s : Set α} (hf : MonotoneOn f s) :
    HasLocallyBoundedVariationOn f s := fun a b as bs =>
  ((hf.evariation_on_le as bs).trans_lt Ennreal.of_real_lt_top).Ne
#align monotone_on.has_locally_bounded_variation_on MonotoneOn.hasLocallyBoundedVariationOn

/-- If a real valued function has bounded variation on a set, then it is a difference of monotone
functions there. -/
theorem HasLocallyBoundedVariationOn.exists_monotone_on_sub_monotone_on {f : α → ℝ} {s : Set α}
    (h : HasLocallyBoundedVariationOn f s) :
    ∃ p q : α → ℝ, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q := by
  rcases eq_empty_or_nonempty s with (rfl | hs)
  ·
    exact
      ⟨f, 0, subsingleton_empty.monotone_on _, subsingleton_empty.monotone_on _, by
        simp only [tsub_zero]⟩
  rcases hs with ⟨c, cs⟩
  let p x :=
    if c ≤ x then (evariationOn f (s ∩ Icc c x)).toReal else -(evariationOn f (s ∩ Icc x c)).toReal
  have hp : MonotoneOn p s := by 
    intro x xs y ys hxy
    dsimp only [p]
    split_ifs with hcx hcy hcy
    · have :
        evariationOn f (s ∩ Icc c x) + evariationOn f (s ∩ Icc x y) =
          evariationOn f (s ∩ Icc c y) :=
        evariationOn.Icc_add_Icc f hcx hxy xs
      rw [← this, Ennreal.to_real_add (h c x cs xs) (h x y xs ys)]
      exact le_add_of_le_of_nonneg le_rfl Ennreal.to_real_nonneg
    · exact (lt_irrefl _ ((not_le.1 hcy).trans_le (hcx.trans hxy))).elim
    · exact (neg_nonpos.2 Ennreal.to_real_nonneg).trans Ennreal.to_real_nonneg
    · simp only [neg_le_neg_iff]
      have :
        evariationOn f (s ∩ Icc x y) + evariationOn f (s ∩ Icc y c) =
          evariationOn f (s ∩ Icc x c) :=
        evariationOn.Icc_add_Icc f hxy (not_le.1 hcy).le ys
      rw [← this, Ennreal.to_real_add (h x y xs ys) (h y c ys cs), add_comm]
      exact le_add_of_le_of_nonneg le_rfl Ennreal.to_real_nonneg
  have hq : MonotoneOn (fun x => p x - f x) s := by
    intro x xs y ys hxy
    dsimp only [p]
    split_ifs with hcx hcy hcy
    · have :
        evariationOn f (s ∩ Icc c x) + evariationOn f (s ∩ Icc x y) =
          evariationOn f (s ∩ Icc c y) :=
        evariationOn.Icc_add_Icc f hcx hxy xs
      rw [← this, Ennreal.to_real_add (h c x cs xs) (h x y xs ys)]
      suffices f y - f x ≤ (evariationOn f (s ∩ Icc x y)).toReal by linarith
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩
    · exact (lt_irrefl _ ((not_le.1 hcy).trans_le (hcx.trans hxy))).elim
    · suffices
        f y - f x ≤ (evariationOn f (s ∩ Icc x c)).toReal + (evariationOn f (s ∩ Icc c y)).toReal by
        linarith
      rw [← Ennreal.to_real_add (h x c xs cs) (h c y cs ys),
        evariationOn.Icc_add_Icc f (not_le.1 hcx).le hcy cs]
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩
    · have :
        evariationOn f (s ∩ Icc x y) + evariationOn f (s ∩ Icc y c) =
          evariationOn f (s ∩ Icc x c) :=
        evariationOn.Icc_add_Icc f hxy (not_le.1 hcy).le ys
      rw [← this, Ennreal.to_real_add (h x y xs ys) (h y c ys cs)]
      suffices f y - f x ≤ (evariationOn f (s ∩ Icc x y)).toReal by linarith
      exact (h x y xs ys).sub_le ⟨ys, hxy, le_rfl⟩ ⟨xs, le_rfl, hxy⟩
  refine' ⟨p, fun x => p x - f x, hp, hq, _⟩
  ext x
  dsimp
  abel
#align
  has_locally_bounded_variation_on.exists_monotone_on_sub_monotone_on HasLocallyBoundedVariationOn.exists_monotone_on_sub_monotone_on

/-! ## Lipschitz functions and bounded variation -/


theorem LipschitzOnWith.comp_evariation_on_le {f : E → F} {C : ℝ≥0} {t : Set E}
    (h : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t) :
    evariationOn (f ∘ g) s ≤ C * evariationOn g s := by
  apply supᵢ_le _
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i in Finset.range n, edist (f (g (u (i + 1)))) (f (g (u i)))) ≤
        ∑ i in Finset.range n, C * edist (g (u (i + 1))) (g (u i)) :=
      Finset.sum_le_sum fun i hi => h (hg (us _)) (hg (us _))
    _ = C * ∑ i in Finset.range n, edist (g (u (i + 1))) (g (u i)) := by rw [Finset.mul_sum]
    _ ≤ C * evariationOn g s := mul_le_mul_left' (evariationOn.sum_le _ _ hu us) _
    
#align lipschitz_on_with.comp_evariation_on_le LipschitzOnWith.comp_evariation_on_le

theorem LipschitzOnWith.compHasBoundedVariationOn {f : E → F} {C : ℝ≥0} {t : Set E}
    (hf : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t)
    (h : HasBoundedVariationOn g s) : HasBoundedVariationOn (f ∘ g) s := by
  dsimp [HasBoundedVariationOn] at h
  apply ne_of_lt
  apply (hf.comp_evariation_on_le hg).trans_lt
  simp [lt_top_iff_ne_top, h]
#align lipschitz_on_with.comp_has_bounded_variation_on LipschitzOnWith.compHasBoundedVariationOn

theorem LipschitzOnWith.compHasLocallyBoundedVariationOn {f : E → F} {C : ℝ≥0} {t : Set E}
    (hf : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t)
    (h : HasLocallyBoundedVariationOn g s) : HasLocallyBoundedVariationOn (f ∘ g) s :=
  fun x y xs ys => hf.compHasBoundedVariationOn (hg.mono_left (inter_subset_left _ _)) (h x y xs ys)
#align
  lipschitz_on_with.comp_has_locally_bounded_variation_on LipschitzOnWith.compHasLocallyBoundedVariationOn

theorem LipschitzWith.compHasBoundedVariationOn {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f)
    {g : α → E} {s : Set α} (h : HasBoundedVariationOn g s) : HasBoundedVariationOn (f ∘ g) s :=
  (hf.LipschitzOnWith univ).compHasBoundedVariationOn (mapsTo_univ _ _) h
#align lipschitz_with.comp_has_bounded_variation_on LipschitzWith.compHasBoundedVariationOn

theorem LipschitzWith.compHasLocallyBoundedVariationOn {f : E → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) {g : α → E} {s : Set α} (h : HasLocallyBoundedVariationOn g s) :
    HasLocallyBoundedVariationOn (f ∘ g) s :=
  (hf.LipschitzOnWith univ).compHasLocallyBoundedVariationOn (mapsTo_univ _ _) h
#align
  lipschitz_with.comp_has_locally_bounded_variation_on LipschitzWith.compHasLocallyBoundedVariationOn

theorem LipschitzOnWith.hasLocallyBoundedVariationOn {f : ℝ → E} {C : ℝ≥0} {s : Set ℝ}
    (hf : LipschitzOnWith C f s) : HasLocallyBoundedVariationOn f s :=
  hf.compHasLocallyBoundedVariationOn (mapsTo_id _)
    (@monotoneOn_id ℝ _ s).HasLocallyBoundedVariationOn
#align
  lipschitz_on_with.has_locally_bounded_variation_on LipschitzOnWith.hasLocallyBoundedVariationOn

theorem LipschitzWith.hasLocallyBoundedVariationOn {f : ℝ → E} {C : ℝ≥0} (hf : LipschitzWith C f)
    (s : Set ℝ) : HasLocallyBoundedVariationOn f s :=
  (hf.LipschitzOnWith s).HasLocallyBoundedVariationOn
#align lipschitz_with.has_locally_bounded_variation_on LipschitzWith.hasLocallyBoundedVariationOn

/-! ## Almost everywhere differentiability of functions with locally bounded variation -/


namespace HasLocallyBoundedVariationOn

/-- A bounded variation function into `ℝ` is differentiable almost everywhere. Superseded by
`ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiable_within_at_of_mem_real {f : ℝ → ℝ} {s : Set ℝ}
    (h : HasLocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  obtain ⟨p, q, hp, hq, fpq⟩ : ∃ p q, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q
  exact h.exists_monotone_on_sub_monotone_on
  filter_upwards [hp.ae_differentiable_within_at_of_mem,
    hq.ae_differentiable_within_at_of_mem] with x hxp hxq xs
  have fpq : ∀ x, f x = p x - q x := by simp [fpq]
  refine' ((hxp xs).sub (hxq xs)).congr (fun y hy => fpq y) (fpq x)
#align
  has_locally_bounded_variation_on.ae_differentiable_within_at_of_mem_real HasLocallyBoundedVariationOn.ae_differentiable_within_at_of_mem_real

/-- A bounded variation function into a finite dimensional product vector space is differentiable
almost everywhere. Superseded by `ae_differentiable_within_at_of_mem`. -/
theorem ae_differentiable_within_at_of_mem_pi {ι : Type _} [Fintype ι] {f : ℝ → ι → ℝ} {s : Set ℝ}
    (h : HasLocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  have A : ∀ i : ι, LipschitzWith 1 fun x : ι → ℝ => x i := fun i => LipschitzWith.eval i
  have : ∀ i : ι, ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ (fun x : ℝ => f x i) s x := by
    intro i
    apply ae_differentiable_within_at_of_mem_real
    exact LipschitzWith.compHasLocallyBoundedVariationOn (A i) h
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiable_within_at_pi.2 fun i => hx i xs
#align
  has_locally_bounded_variation_on.ae_differentiable_within_at_of_mem_pi HasLocallyBoundedVariationOn.ae_differentiable_within_at_of_mem_pi

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiable_within_at_of_mem {f : ℝ → V} {s : Set ℝ}
    (h : HasLocallyBoundedVariationOn f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  let A := (Basis.ofVectorSpace ℝ V).equivFun.toContinuousLinearEquiv
  suffices H : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ (A ∘ f) s x
  · filter_upwards [H] with x hx xs
    have : f = (A.symm ∘ A) ∘ f := by
      simp only [ContinuousLinearEquiv.symm_comp_self, Function.comp.left_id]
    rw [this]
    exact A.symm.differentiable_at.comp_differentiable_within_at x (hx xs)
  apply ae_differentiable_within_at_of_mem_pi
  exact A.lipschitz.comp_has_locally_bounded_variation_on h
#align
  has_locally_bounded_variation_on.ae_differentiable_within_at_of_mem HasLocallyBoundedVariationOn.ae_differentiable_within_at_of_mem

/-- A real function into a finite dimensional real vector space with bounded variation on a set
is differentiable almost everywhere in this set. -/
theorem ae_differentiable_within_at {f : ℝ → V} {s : Set ℝ} (h : HasLocallyBoundedVariationOn f s)
    (hs : MeasurableSet s) : ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact h.ae_differentiable_within_at_of_mem
#align
  has_locally_bounded_variation_on.ae_differentiable_within_at HasLocallyBoundedVariationOn.ae_differentiable_within_at

/-- A real function into a finite dimensional real vector space with bounded variation
is differentiable almost everywhere. -/
theorem ae_differentiable_at {f : ℝ → V} (h : HasLocallyBoundedVariationOn f univ) :
    ∀ᵐ x, DifferentiableAt ℝ f x := by
  filter_upwards [h.ae_differentiable_within_at_of_mem] with x hx
  rw [differentiable_within_at_univ] at hx
  exact hx (mem_univ _)
#align
  has_locally_bounded_variation_on.ae_differentiable_at HasLocallyBoundedVariationOn.ae_differentiable_at

end HasLocallyBoundedVariationOn

/-- A real function into a finite dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set . -/
theorem LipschitzOnWith.ae_differentiable_within_at_of_mem {C : ℝ≥0} {f : ℝ → V} {s : Set ℝ}
    (h : LipschitzOnWith C f s) : ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x :=
  h.HasLocallyBoundedVariationOn.ae_differentiable_within_at_of_mem
#align
  lipschitz_on_with.ae_differentiable_within_at_of_mem LipschitzOnWith.ae_differentiable_within_at_of_mem

/-- A real function into a finite dimensional real vector space which is Lipschitz on a set
is differentiable almost everywhere in this set. -/
theorem LipschitzOnWith.ae_differentiable_within_at {C : ℝ≥0} {f : ℝ → V} {s : Set ℝ}
    (h : LipschitzOnWith C f s) (hs : MeasurableSet s) :
    ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x :=
  h.HasLocallyBoundedVariationOn.ae_differentiable_within_at hs
#align lipschitz_on_with.ae_differentiable_within_at LipschitzOnWith.ae_differentiable_within_at

/-- A real Lipschitz function into a finite dimensional real vector space is differentiable
almost everywhere. -/
theorem LipschitzWith.ae_differentiable_at {C : ℝ≥0} {f : ℝ → V} (h : LipschitzWith C f) :
    ∀ᵐ x, DifferentiableAt ℝ f x :=
  (h.HasLocallyBoundedVariationOn univ).ae_differentiable_at
#align lipschitz_with.ae_differentiable_at LipschitzWith.ae_differentiable_at

