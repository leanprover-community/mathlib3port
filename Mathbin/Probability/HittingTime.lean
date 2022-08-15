/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathbin.Probability.Stopping

/-!
# Hitting time

Given a stochastic process, the hitting time provides the first time the process ``hits'' some
subset of the state space. The hitting time is a stopping time in the case that the time index is
discrete and the process is adapted (this is true in a far more general setting however we have
only proved it for the discrete case so far).

## Main definition

* `measure_theory.hitting`: the hitting time of a stochastic process

## Main results

* `measure_theory.hitting_is_stopping_time`: a discrete hitting time of an adapted process is a
  stopping time

## Implementation notes

In the definition of the hitting time, we bound the hitting time by an upper and lower bound.
This is to ensure that our result is meaningful in the case we are taking the infimum of an
empty set or the infimum of a set which is unbounded from below. With this, we can talk about
hitting times indexed by the natural numbers or the reals. By taking the bounds to be
`⊤` and `⊥`, we obtain the standard definition in the case that the index is `with_top ℕ` or `ℝ≥0∞`.

-/


open Filter Order TopologicalSpace

open Classical MeasureTheory Nnreal Ennreal TopologicalSpace BigOperators

namespace MeasureTheory

variable {Ω β ι : Type _} {m : MeasurableSpace Ω}

/-- Hitting time: given a stochastic process `u` and a set `s`, `hitting u s n m` is the first time
`u` is in `s` after time `n` and before time `m` (if `u` does not hit `s` after time `n` and
before `m` then the hitting time is simply `m`).

The hitting time is a stopping time if the process is adapted and discrete. -/
noncomputable def hitting [Preorderₓ ι] [HasInfₓ ι] (u : ι → Ω → β) (s : Set β) (n m : ι) : Ω → ι := fun x =>
  if ∃ j ∈ Set.Icc n m, u j x ∈ s then inf (Set.Icc n m ∩ { i : ι | u i x ∈ s }) else m

section Inequalities

variable [ConditionallyCompleteLinearOrder ι] {u : ι → Ω → β} {s : Set β} {n i : ι} {ω : Ω}

theorem hitting_of_lt {m : ι} (h : m < n) : hitting u s n m ω = m := by
  simp_rw [hitting]
  have h_not : ¬∃ (j : ι)(H : j ∈ Set.Icc n m), u j ω ∈ s := by
    push_neg
    intro j
    rw [Set.Icc_eq_empty_of_lt h]
    simp only [← Set.mem_empty_eq, ← IsEmpty.forall_iff]
  simp only [← h_not, ← if_false]

theorem hitting_le {m : ι} (ω : Ω) : hitting u s n m ω ≤ m := by
  cases' le_or_ltₓ n m with h_le h_lt
  · simp only [← hitting]
    split_ifs
    · obtain ⟨j, hj₁, hj₂⟩ := h
      exact (cInf_le (BddBelow.inter_of_left bdd_below_Icc) (Set.mem_inter hj₁ hj₂)).trans hj₁.2
      
    · exact le_rfl
      
    
  · rw [hitting_of_lt h_lt]
    

theorem le_hitting {m : ι} (hnm : n ≤ m) (ω : Ω) : n ≤ hitting u s n m ω := by
  simp only [← hitting]
  split_ifs
  · refine' le_cInf _ fun b hb => _
    · obtain ⟨k, hk_Icc, hk_s⟩ := h
      exact ⟨k, hk_Icc, hk_s⟩
      
    · rw [Set.mem_inter_iff] at hb
      exact hb.1.1
      
    
  · exact hnm
    

theorem le_hitting_of_exists {m : ι} (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) : n ≤ hitting u s n m ω := by
  refine' le_hitting _ ω
  by_contra
  rw [Set.Icc_eq_empty_of_lt (not_le.mp h)] at h_exists
  simpa using h_exists

theorem hitting_mem_Icc {m : ι} (hnm : n ≤ m) (ω : Ω) : hitting u s n m ω ∈ Set.Icc n m :=
  ⟨le_hitting hnm ω, hitting_le ω⟩

theorem hitting_mem_set [IsWellOrder ι (· < ·)] {m : ι} (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    u (hitting u s n m ω) ω ∈ s := by
  simp_rw [hitting, if_pos h_exists]
  have h_nonempty : (Set.Icc n m ∩ { i : ι | u i ω ∈ s }).Nonempty := by
    obtain ⟨k, hk₁, hk₂⟩ := h_exists
    exact ⟨k, Set.mem_inter hk₁ hk₂⟩
  have h_mem := Inf_mem h_nonempty
  rw [Set.mem_inter_iff] at h_mem
  exact h_mem.2

theorem hitting_le_of_mem {m : ι} (hin : n ≤ i) (him : i ≤ m) (his : u i ω ∈ s) : hitting u s n m ω ≤ i := by
  have h_exists : ∃ k ∈ Set.Icc n m, u k ω ∈ s := ⟨i, ⟨hin, him⟩, his⟩
  simp_rw [hitting, if_pos h_exists]
  exact cInf_le (BddBelow.inter_of_left bdd_below_Icc) (Set.mem_inter ⟨hin, him⟩ his)

theorem hitting_le_iff_of_exists [IsWellOrder ι (· < ·)] {m : ι} (h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s) :
    hitting u s n m ω ≤ i ↔ ∃ j ∈ Set.Icc n i, u j ω ∈ s := by
  constructor <;> intro h'
  · exact ⟨hitting u s n m ω, ⟨le_hitting_of_exists h_exists, h'⟩, hitting_mem_set h_exists⟩
    
  · have h'' : ∃ k ∈ Set.Icc n (min m i), u k ω ∈ s := by
      obtain ⟨k₁, hk₁_mem, hk₁_s⟩ := h_exists
      obtain ⟨k₂, hk₂_mem, hk₂_s⟩ := h'
      refine' ⟨min k₁ k₂, ⟨le_minₓ hk₁_mem.1 hk₂_mem.1, min_le_min hk₁_mem.2 hk₂_mem.2⟩, _⟩
      exact min_rec' (fun j => u j ω ∈ s) hk₁_s hk₂_s
    obtain ⟨k, hk₁, hk₂⟩ := h''
    refine' le_transₓ _ (hk₁.2.trans (min_le_rightₓ _ _))
    exact hitting_le_of_mem hk₁.1 (hk₁.2.trans (min_le_leftₓ _ _)) hk₂
    

theorem hitting_le_iff_of_lt [IsWellOrder ι (· < ·)] {m : ι} (i : ι) (hi : i < m) :
    hitting u s n m ω ≤ i ↔ ∃ j ∈ Set.Icc n i, u j ω ∈ s := by
  by_cases' h_exists : ∃ j ∈ Set.Icc n m, u j ω ∈ s
  · rw [hitting_le_iff_of_exists h_exists]
    
  · simp_rw [hitting, if_neg h_exists]
    push_neg  at h_exists
    simp only [← not_le.mpr hi, ← Set.mem_Icc, ← false_iffₓ, ← not_exists, ← and_imp]
    exact fun k hkn hki => h_exists k ⟨hkn, hki.trans hi.le⟩
    

theorem hitting_lt_iff [IsWellOrder ι (· < ·)] {m : ι} (i : ι) (hi : i ≤ m) :
    hitting u s n m ω < i ↔ ∃ j ∈ Set.Ico n i, u j ω ∈ s := by
  constructor <;> intro h'
  · have h : ∃ j ∈ Set.Icc n m, u j ω ∈ s := by
      by_contra
      simp_rw [hitting, if_neg h, ← not_leₓ] at h'
      exact h' hi
    exact ⟨hitting u s n m ω, ⟨le_hitting_of_exists h, h'⟩, hitting_mem_set h⟩
    
  · obtain ⟨k, hk₁, hk₂⟩ := h'
    refine' lt_of_le_of_ltₓ _ hk₁.2
    exact hitting_le_of_mem hk₁.1 (hk₁.2.le.trans hi) hk₂
    

theorem hitting_eq_hitting_of_exists {m₁ m₂ : ι} (h : m₁ ≤ m₂) (h' : ∃ j ∈ Set.Icc n m₁, u j ω ∈ s) :
    hitting u s n m₁ ω = hitting u s n m₂ ω := by
  simp only [← hitting, ← if_pos h']
  obtain ⟨j, hj₁, hj₂⟩ := h'
  rw [if_pos]
  · refine'
      le_antisymmₓ _
        (cInf_le_cInf bdd_below_Icc.inter_of_left ⟨j, hj₁, hj₂⟩
          (Set.inter_subset_inter_left _ (Set.Icc_subset_Icc_right h)))
    refine' le_cInf ⟨j, Set.Icc_subset_Icc_right h hj₁, hj₂⟩ fun i hi => _
    by_cases' hi' : i ≤ m₁
    · exact cInf_le bdd_below_Icc.inter_of_left ⟨⟨hi.1.1, hi'⟩, hi.2⟩
      
    · exact
        ((cInf_le bdd_below_Icc.inter_of_left ⟨hj₁, hj₂⟩).trans (hj₁.2.trans le_rfl)).trans (le_of_ltₓ (not_leₓ.1 hi'))
      
    
  exact ⟨j, ⟨hj₁.1, hj₁.2.trans h⟩, hj₂⟩

end Inequalities

/-- A discrete hitting time is a stopping time. -/
theorem hitting_is_stopping_time [ConditionallyCompleteLinearOrder ι] [IsWellOrder ι (· < ·)] [Encodable ι]
    [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] {f : Filtration ι m}
    {u : ι → Ω → β} {s : Set β} {n n' : ι} (hu : Adapted f u) (hs : MeasurableSet s) :
    IsStoppingTime f (hitting u s n n') := by
  intro i
  cases' le_or_ltₓ n' i with hi hi
  · have h_le : ∀ ω, hitting u s n n' ω ≤ i := fun x => (hitting_le x).trans hi
    simp [← h_le]
    
  · have h_set_eq_Union : { ω | hitting u s n n' ω ≤ i } = ⋃ j ∈ Set.Icc n i, u j ⁻¹' s := by
      ext x
      rw [Set.mem_set_of_eq, hitting_le_iff_of_lt _ hi]
      simp only [← Set.mem_Icc, ← exists_prop, ← Set.mem_Union, ← Set.mem_preimage]
    rw [h_set_eq_Union]
    exact MeasurableSet.Union fun j => MeasurableSet.Union_Prop fun hj => f.mono hj.2 _ ((hu j).Measurable hs)
    

theorem stopped_value_hitting_mem [ConditionallyCompleteLinearOrder ι] [IsWellOrder ι (· < ·)] {u : ι → Ω → β}
    {s : Set β} {n m : ι} {ω : Ω} (h : ∃ j ∈ Set.Icc n m, u j ω ∈ s) : stoppedValue u (hitting u s n m) ω ∈ s := by
  simp only [← stopped_value, ← hitting, ← if_pos h]
  obtain ⟨j, hj₁, hj₂⟩ := h
  have : Inf (Set.Icc n m ∩ { i | u i ω ∈ s }) ∈ Set.Icc n m ∩ { i | u i ω ∈ s } :=
    Inf_mem (Set.nonempty_of_mem ⟨hj₁, hj₂⟩)
  exact this.2

/-- The hitting time of a discrete process with the starting time indexed by a stopping time
is a stopping time. -/
theorem is_stopping_time_hitting_is_stopping_time [ConditionallyCompleteLinearOrder ι] [IsWellOrder ι (· < ·)]
    [Encodable ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] {f : Filtration ι m} {u : ι → Ω → β} {τ : Ω → ι}
    (hτ : IsStoppingTime f τ) {N : ι} (hτbdd : ∀ x, τ x ≤ N) {s : Set β} (hs : MeasurableSet s) (hf : Adapted f u) :
    IsStoppingTime f fun x => hitting u s (τ x) N x := by
  intro n
  have h₁ :
    { x | hitting u s (τ x) N x ≤ n } =
      (⋃ i ≤ n, { x | τ x = i } ∩ { x | hitting u s i N x ≤ n }) ∪
        ⋃ i > n, { x | τ x = i } ∩ { x | hitting u s i N x ≤ n } :=
    by
    ext x
    simp [exists_or_distrib, or_and_distrib_right, ← le_or_ltₓ]
  have h₂ : (⋃ i > n, { x | τ x = i } ∩ { x | hitting u s i N x ≤ n }) = ∅ := by
    ext x
    simp only [← gt_iff_lt, ← Set.mem_Union, ← Set.mem_inter_eq, ← Set.mem_set_of_eq, ← exists_prop, ← Set.mem_empty_eq,
      ← iff_falseₓ, ← not_exists, ← not_and, ← not_leₓ]
    rintro m hm rfl
    exact lt_of_lt_of_leₓ hm (le_hitting (hτbdd _) _)
  rw [h₁, h₂, Set.union_empty]
  exact
    MeasurableSet.Union fun i =>
      MeasurableSet.Union_Prop fun hi => (f.mono hi _ (hτ.measurable_set_eq i)).inter (hitting_is_stopping_time hf hs n)

section CompleteLattice

variable [CompleteLattice ι] {u : ι → Ω → β} {s : Set β} {f : Filtration ι m}

theorem hitting_eq_Inf (ω : Ω) : hitting u s ⊥ ⊤ ω = inf { i : ι | u i ω ∈ s } := by
  simp only [← hitting, ← Set.mem_Icc, ← bot_le, ← le_top, ← and_selfₓ, ← exists_true_left, ← Set.Icc_bot, ←
    Set.Iic_top, ← Set.univ_inter, ← ite_eq_left_iff, ← not_exists]
  intro h_nmem_s
  symm
  rw [Inf_eq_top]
  exact fun i hi_mem_s => absurd hi_mem_s (h_nmem_s i)

end CompleteLattice

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι] [IsWellOrder ι (· < ·)]

variable {u : ι → Ω → β} {s : Set β} {f : Filtration ℕ m}

theorem hitting_bot_le_iff {i n : ι} {ω : Ω} (hx : ∃ j, j ≤ n ∧ u j ω ∈ s) :
    hitting u s ⊥ n ω ≤ i ↔ ∃ j ≤ i, u j ω ∈ s := by
  cases' lt_or_leₓ i n with hi hi
  · rw [hitting_le_iff_of_lt _ hi]
    simp
    
  · simp only [← (hitting_le ω).trans hi, ← true_iffₓ]
    obtain ⟨j, hj₁, hj₂⟩ := hx
    exact ⟨j, hj₁.trans hi, hj₂⟩
    

end ConditionallyCompleteLinearOrderBot

end MeasureTheory

