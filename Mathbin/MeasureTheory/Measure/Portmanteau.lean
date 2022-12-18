/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä

! This file was ported from Lean 3 source module measure_theory.measure.portmanteau
! leanprover-community/mathlib commit dcf2250875895376a142faeeac5eabff32c48655
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Characterizations of weak convergence of finite measures and probability measures

This file will provide portmanteau characterizations of the weak convergence of finite measures
and of probability measures, i.e., the standard characterizations of convergence in distribution.

## Main definitions

This file does not introduce substantial new definitions: the topologies of weak convergence on
the types of finite measures and probability measures are already defined in their corresponding
files.

## Main results

The main result will be the portmanteau theorem providing various characterizations of the
weak convergence of measures. The separate implications are:
 * `measure_theory.finite_measure.limsup_measure_closed_le_of_tendsto` proves that weak convergence
   implies a limsup-condition for closed sets.
 * `measure_theory.limsup_measure_closed_le_iff_liminf_measure_open_ge` proves for probability
   measures the equivalence of the limsup condition for closed sets and the liminf condition for
   open sets.
 * `measure_theory.tendsto_measure_of_null_frontier` proves that the liminf condition for open
   sets (which is equivalent to the limsup condition for closed sets) implies the convergence of
   probabilities of sets whose boundary carries no mass under the limit measure.
 * `measure_theory.probability_measure.tendsto_measure_of_null_frontier_of_tendsto` is a
   combination of earlier implications, which shows that weak convergence of probability measures
   implies the convergence of probabilities of sets whose boundary carries no mass under the
   limit measure.

TODO:
 * Prove the rest of the implications.

## Implementation notes

Many of the characterizations of weak convergence hold for finite measures and are proven in that
generality and then specialized to probability measures. Some implications hold with slightly
weaker assumptions than usually stated. The full portmanteau theorem, however, is most convenient
for probability measures on metrizable spaces with their Borel sigmas.

Some specific considerations on the assumptions in the different implications:
 * `measure_theory.finite_measure.limsup_measure_closed_le_of_tendsto` assumes
   `pseudo_emetric_space`. The only reason is to have bounded continuous pointwise approximations
   to the indicator function of a closed set. Clearly for example metrizability or
   pseudo-emetrizability would be sufficient assumptions. The typeclass assumptions should be later
   adjusted in a way that takes into account use cases, but the proof will presumably remain
   essentially the same.
 * Where formulations are currently only provided for probability measures, one can obtain the
   finite measure formulations using the characterization of convergence of finite measures by
   their total masses and their probability-normalized versions, i.e., by
   `measure_theory.finite_measure.tendsto_normalize_iff_tendsto`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, convergence in distribution, convergence in law, finite measure,
probability measure

-/


noncomputable section

open MeasureTheory

open Set

open Filter

open BoundedContinuousFunction

open TopologicalSpace Ennreal Nnreal BoundedContinuousFunction

namespace MeasureTheory

section LimsupClosedLeAndLeLiminfOpen

/-! ### Portmanteau: limsup condition for closed sets iff liminf condition for open sets

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, the following two conditions are equivalent:
  (C) For any closed set `F` in `Ω` the limsup of the measures of `F` is at most the limit
      measure of `F`.
  (O) For any open set `G` in `Ω` the liminf of the measures of `G` is at least the limit
      measure of `G`.
Either of these will later be shown to be equivalent to the weak convergence of the sequence
of measures.
-/


variable {Ω : Type _} [MeasurableSpace Ω]

theorem le_measure_compl_liminf_of_limsup_measure_le {ι : Type _} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i => μs i E) ≤ μ E) :
    μ (Eᶜ) ≤ L.liminf fun i => μs i (Eᶜ) := by
  by_cases L_bot : L = ⊥
  ·
    simp only [L_bot, le_top,
      show liminf (fun i => μs i (Eᶜ)) ⊥ = ⊤ by simp only [liminf, Filter.map_bot, Liminf_bot]]
  have : L.ne_bot := { ne' := L_bot }
  have meas_Ec : μ (Eᶜ) = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).Ne
  have meas_i_Ec : ∀ i, μs i (Eᶜ) = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).Ne
  simp_rw [meas_Ec, meas_i_Ec]
  have obs :
    (L.liminf fun i : ι => 1 - μs i E) = L.liminf ((fun x => 1 - x) ∘ fun i : ι => μs i E) := by rfl
  rw [obs]
  simp_rw [←
    antitone_const_tsub.map_limsup_of_continuous_at (fun i => μs i E)
      (Ennreal.continuous_sub_left Ennreal.one_ne_top).ContinuousAt]
  exact antitone_const_tsub h
#align
  measure_theory.le_measure_compl_liminf_of_limsup_measure_le MeasureTheory.le_measure_compl_liminf_of_limsup_measure_le

theorem le_measure_liminf_of_limsup_measure_compl_le {ι : Type _} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : (L.limsup fun i => μs i (Eᶜ)) ≤ μ (Eᶜ)) :
    μ E ≤ L.liminf fun i => μs i E :=
  compl_compl E ▸ le_measure_compl_liminf_of_limsup_measure_le (MeasurableSet.compl E_mble) h
#align
  measure_theory.le_measure_liminf_of_limsup_measure_compl_le MeasureTheory.le_measure_liminf_of_limsup_measure_compl_le

theorem limsup_measure_compl_le_of_le_liminf_measure {ι : Type _} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ E ≤ L.liminf fun i => μs i E) :
    (L.limsup fun i => μs i (Eᶜ)) ≤ μ (Eᶜ) := by
  by_cases L_bot : L = ⊥
  ·
    simp only [L_bot, bot_le,
      show limsup (fun i => μs i (Eᶜ)) ⊥ = ⊥ by simp only [limsup, Filter.map_bot, Limsup_bot]]
  have : L.ne_bot := { ne' := L_bot }
  have meas_Ec : μ (Eᶜ) = 1 - μ E := by
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).Ne
  have meas_i_Ec : ∀ i, μs i (Eᶜ) = 1 - μs i E := by
    intro i
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).Ne
  simp_rw [meas_Ec, meas_i_Ec]
  have obs :
    (L.limsup fun i : ι => 1 - μs i E) = L.limsup ((fun x => 1 - x) ∘ fun i : ι => μs i E) := by rfl
  rw [obs]
  simp_rw [←
    antitone_const_tsub.map_liminf_of_continuous_at (fun i => μs i E)
      (Ennreal.continuous_sub_left Ennreal.one_ne_top).ContinuousAt]
  exact antitone_const_tsub h
#align
  measure_theory.limsup_measure_compl_le_of_le_liminf_measure MeasureTheory.limsup_measure_compl_le_of_le_liminf_measure

theorem limsup_measure_le_of_le_liminf_measure_compl {ι : Type _} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)] {E : Set Ω}
    (E_mble : MeasurableSet E) (h : μ (Eᶜ) ≤ L.liminf fun i => μs i (Eᶜ)) :
    (L.limsup fun i => μs i E) ≤ μ E :=
  compl_compl E ▸ limsup_measure_compl_le_of_le_liminf_measure (MeasurableSet.compl E_mble) h
#align
  measure_theory.limsup_measure_le_of_le_liminf_measure_compl MeasureTheory.limsup_measure_le_of_le_liminf_measure_compl

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- One pair of implications of the portmanteau theorem:
For a sequence of Borel probability measures, the following two are equivalent:

(C) The limsup of the measures of any closed set is at most the measure of the closed set
under a candidate limit measure.

(O) The liminf of the measures of any open set is at least the measure of the open set
under a candidate limit measure.
-/
theorem limsup_measure_closed_le_iff_liminf_measure_open_ge {ι : Type _} {L : Filter ι}
    {μ : Measure Ω} {μs : ι → Measure Ω} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μs i)] :
    (∀ F, IsClosed F → (L.limsup fun i => μs i F) ≤ μ F) ↔
      ∀ G, IsOpen G → μ G ≤ L.liminf fun i => μs i G :=
  by 
  constructor
  · intro h G G_open
    exact
      le_measure_liminf_of_limsup_measure_compl_le G_open.measurable_set
        (h (Gᶜ) (is_closed_compl_iff.mpr G_open))
  · intro h F F_closed
    exact
      limsup_measure_le_of_le_liminf_measure_compl F_closed.measurable_set
        (h (Fᶜ) (is_open_compl_iff.mpr F_closed))
#align
  measure_theory.limsup_measure_closed_le_iff_liminf_measure_open_ge MeasureTheory.limsup_measure_closed_le_iff_liminf_measure_open_ge

end LimsupClosedLeAndLeLiminfOpen

-- section
section TendstoOfNullFrontier

/-! ### Portmanteau: limit of measures of Borel sets whose boundary carries no mass in the limit

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, either of the following equivalent conditions:
  (C) For any closed set `F` in `Ω` the limsup of the measures of `F` is at most the limit
      measure of `F`
  (O) For any open set `G` in `Ω` the liminf of the measures of `G` is at least the limit
      measure of `G`
implies that
  (B) For any Borel set `E` in `Ω` whose boundary `∂E` carries no mass under the candidate limit
      measure, we have that the limit of measures of `E` is the measure of `E` under the
      candidate limit measure.
-/


variable {Ω : Type _} [MeasurableSpace Ω]

theorem tendsto_measure_of_le_liminf_measure_of_limsup_measure_le {ι : Type _} {L : Filter ι}
    {μ : Measure Ω} {μs : ι → Measure Ω} {E₀ E E₁ : Set Ω} (E₀_subset : E₀ ⊆ E) (subset_E₁ : E ⊆ E₁)
    (nulldiff : μ (E₁ \ E₀) = 0) (h_E₀ : μ E₀ ≤ L.liminf fun i => μs i E₀)
    (h_E₁ : (L.limsup fun i => μs i E₁) ≤ μ E₁) : L.Tendsto (fun i => μs i E) (𝓝 (μ E)) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · have E₀_ae_eq_E : E₀ =ᵐ[μ] E :=
      eventually_le.antisymm E₀_subset.eventually_le
        (subset_E₁.eventually_le.trans (ae_le_set.mpr nulldiff))
    calc
      μ E = μ E₀ := measure_congr E₀_ae_eq_E.symm
      _ ≤ L.liminf fun i => μs i E₀ := h_E₀
      _ ≤ L.liminf fun i => μs i E := _
      
    · refine' liminf_le_liminf (eventually_of_forall fun _ => measure_mono E₀_subset) _
      infer_param
  · have E_ae_eq_E₁ : E =ᵐ[μ] E₁ :=
      eventually_le.antisymm subset_E₁.eventually_le
        ((ae_le_set.mpr nulldiff).trans E₀_subset.eventually_le)
    calc
      (L.limsup fun i => μs i E) ≤ L.limsup fun i => μs i E₁ := _
      _ ≤ μ E₁ := h_E₁
      _ = μ E := measure_congr E_ae_eq_E₁.symm
      
    · refine' limsup_le_limsup (eventually_of_forall fun _ => measure_mono subset_E₁) _
      infer_param
#align
  measure_theory.tendsto_measure_of_le_liminf_measure_of_limsup_measure_le MeasureTheory.tendsto_measure_of_le_liminf_measure_of_limsup_measure_le

variable [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- One implication of the portmanteau theorem:
For a sequence of Borel probability measures, if the liminf of the measures of any open set is at
least the measure of the open set under a candidate limit measure, then for any set whose
boundary carries no probability mass under the candidate limit measure, then its measures under the
sequence converge to its measure under the candidate limit measure.
-/
theorem tendsto_measure_of_null_frontier {ι : Type _} {L : Filter ι} {μ : Measure Ω}
    {μs : ι → Measure Ω} [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (μs i)]
    (h_opens : ∀ G, IsOpen G → μ G ≤ L.liminf fun i => μs i G) {E : Set Ω}
    (E_nullbdry : μ (frontier E) = 0) : L.Tendsto (fun i => μs i E) (𝓝 (μ E)) :=
  haveI h_closeds : ∀ F, IsClosed F → (L.limsup fun i => μs i F) ≤ μ F :=
    limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr h_opens
  tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure
    E_nullbdry (h_opens _ is_open_interior) (h_closeds _ is_closed_closure)
#align
  measure_theory.tendsto_measure_of_null_frontier MeasureTheory.tendsto_measure_of_null_frontier

end TendstoOfNullFrontier

--section
section ConvergenceImpliesLimsupClosedLe

/-! ### Portmanteau implication: weak convergence implies a limsup condition for closed sets

In this section we prove, under the assumption that the underlying topological space `Ω` is
pseudo-emetrizable, that the weak convergence of measures on `measure_theory.finite_measure Ω`
implies that for any closed set `F` in `Ω` the limsup of the measures of `F` is at most the
limit measure of `F`. This is one implication of the portmanteau theorem characterizing weak
convergence of measures.

Combining with an earlier implication we also get that weak convergence implies that for any Borel
set `E` in `Ω` whose boundary `∂E` carries no mass under the limit measure, the limit of measures
of `E` is the measure of `E` under the limit measure.
-/


variable {Ω : Type _} [MeasurableSpace Ω]

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere.
-/
theorem measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type _} {L : Filter ι}
    [L.IsCountablyGenerated] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {c : ℝ≥0} {E : Set Ω} (E_mble : MeasurableSet E) (fs : ι → Ω →ᵇ ℝ≥0)
    (fs_bdd : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂μ, fs i ω ≤ c)
    (fs_lim :
      ∀ᵐ ω : Ω ∂μ,
        Tendsto (fun i : ι => (coeFn : (Ω →ᵇ ℝ≥0) → Ω → ℝ≥0) (fs i) ω) L
          (𝓝 (indicator E (fun x => (1 : ℝ≥0)) ω))) :
    Tendsto (fun n => lintegral μ fun ω => fs n ω) L (𝓝 (μ E)) := by
  convert finite_measure.tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim
  have aux : ∀ ω, indicator E (fun ω => (1 : ℝ≥0∞)) ω = ↑(indicator E (fun ω => (1 : ℝ≥0)) ω) :=
    fun ω => by simp only [Ennreal.coe_indicator, Ennreal.coe_one]
  simp_rw [← aux, lintegral_indicator _ E_mble]
  simp only [lintegral_one, measure.restrict_apply, MeasurableSet.univ, univ_inter]
#align
  measure_theory.measure_of_cont_bdd_of_tendsto_filter_indicator MeasureTheory.measure_of_cont_bdd_of_tendsto_filter_indicator

/-- If a sequence of bounded continuous functions tends to the indicator of a measurable set and
the functions are uniformly bounded, then their integrals against a finite measure tend to the
measure of the set.

A similar result with more general assumptions is
`measure_theory.measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
theorem measure_of_cont_bdd_of_tendsto_indicator [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {c : ℝ≥0} {E : Set Ω} (E_mble : MeasurableSet E)
    (fs : ℕ → Ω →ᵇ ℝ≥0) (fs_bdd : ∀ n ω, fs n ω ≤ c)
    (fs_lim :
      Tendsto (fun n : ℕ => (coeFn : (Ω →ᵇ ℝ≥0) → Ω → ℝ≥0) (fs n)) atTop
        (𝓝 (indicator E fun x => (1 : ℝ≥0)))) :
    Tendsto (fun n => lintegral μ fun ω => fs n ω) atTop (𝓝 (μ E)) := by
  have fs_lim' :
    ∀ ω, tendsto (fun n : ℕ => (fs n ω : ℝ≥0)) at_top (𝓝 (indicator E (fun x => (1 : ℝ≥0)) ω)) := by
    rw [tendsto_pi_nhds] at fs_lim
    exact fun ω => fs_lim ω
  apply
    measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
      (eventually_of_forall fun n => eventually_of_forall (fs_bdd n)) (eventually_of_forall fs_lim')
#align
  measure_theory.measure_of_cont_bdd_of_tendsto_indicator MeasureTheory.measure_of_cont_bdd_of_tendsto_indicator

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero.
-/
theorem tendsto_lintegral_thickened_indicator_of_is_closed {Ω : Type _} [MeasurableSpace Ω]
    [PseudoEmetricSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {F : Set Ω}
    (F_closed : IsClosed F) {δs : ℕ → ℝ} (δs_pos : ∀ n, 0 < δs n)
    (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n => lintegral μ fun ω => (thickenedIndicator (δs_pos n) F ω : ℝ≥0∞)) atTop
      (𝓝 (μ F)) :=
  by
  apply
    measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurable_set
      (fun n => thickenedIndicator (δs_pos n) F) fun n ω =>
      thickened_indicator_le_one (δs_pos n) F ω
  have key := thickened_indicator_tendsto_indicator_closure δs_pos δs_lim F
  rwa [F_closed.closure_eq] at key
#align
  measure_theory.tendsto_lintegral_thickened_indicator_of_is_closed MeasureTheory.tendsto_lintegral_thickened_indicator_of_is_closed

/-- One implication of the portmanteau theorem:
Weak convergence of finite measures implies that the limsup of the measures of any closed set is
at most the measure of the closed set under the limit measure.
-/
theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type _} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEmetricSpace Ω] [OpensMeasurableSpace Ω] {μ : FiniteMeasure Ω}
    {μs : ι → FiniteMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {F : Set Ω} (F_closed : IsClosed F) :
    (L.limsup fun i => (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  by_cases L = ⊥
  · simp only [h, limsup, Filter.map_bot, Limsup_bot, Ennreal.bot_eq_zero, zero_le]
  apply Ennreal.le_of_forall_pos_le_add
  intro ε ε_pos μ_F_finite
  set δs := fun n : ℕ => (1 : ℝ) / (n + 1) with def_δs
  have δs_pos : ∀ n, 0 < δs n := fun n => Nat.one_div_pos_of_nat
  have δs_lim : tendsto δs at_top (𝓝 0) := tendsto_one_div_add_at_top_nhds_0_nat
  have key₁ :=
    tendsto_lintegral_thickened_indicator_of_is_closed (μ : Measure Ω) F_closed δs_pos δs_lim
  have room₁ : (μ : Measure Ω) F < (μ : Measure Ω) F + ε / 2 := by
    apply
      Ennreal.lt_add_right (measure_lt_top (μ : Measure Ω) F).Ne
        (ennreal.div_pos_iff.mpr ⟨(ennreal.coe_pos.mpr ε_pos).Ne.symm, Ennreal.two_ne_top⟩).Ne.symm
  rcases eventually_at_top.mp (eventually_lt_of_tendsto_lt room₁ key₁) with ⟨M, hM⟩
  have key₂ :=
    finite_measure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (thickenedIndicator (δs_pos M) F)
  have room₂ :
    (lintegral (μ : Measure Ω) fun a => thickenedIndicator (δs_pos M) F a) <
      (lintegral (μ : Measure Ω) fun a => thickenedIndicator (δs_pos M) F a) + ε / 2 :=
    by
    apply
      Ennreal.lt_add_right (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measure Ω) _).Ne
        (ennreal.div_pos_iff.mpr ⟨(ennreal.coe_pos.mpr ε_pos).Ne.symm, Ennreal.two_ne_top⟩).Ne.symm
  have ev_near := eventually.mono (eventually_lt_of_tendsto_lt room₂ key₂) fun n => le_of_lt
  have aux := fun n =>
    le_trans
      (measure_le_lintegral_thickened_indicator (μs n : Measure Ω) F_closed.measurable_set
        (δs_pos M))
  have ev_near' := eventually.mono ev_near aux
  apply (Filter.limsup_le_limsup ev_near').trans
  have : ne_bot L := ⟨h⟩
  rw [limsup_const]
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε / 2 : ℝ≥0∞)))
  simp only [add_assoc, Ennreal.add_halves, le_refl]
#align
  measure_theory.finite_measure.limsup_measure_closed_le_of_tendsto MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the limsup of the measures of any closed
set is at most the measure of the closed set under the limit probability measure.
-/
theorem ProbabilityMeasure.limsup_measure_closed_le_of_tendsto {Ω ι : Type _} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEmetricSpace Ω] [OpensMeasurableSpace Ω] {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {F : Set Ω}
    (F_closed : IsClosed F) : (L.limsup fun i => (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F := by
  apply
    finite_measure.limsup_measure_closed_le_of_tendsto
      ((probability_measure.tendsto_nhds_iff_to_finite_measures_tendsto_nhds L).mp μs_lim) F_closed
#align
  measure_theory.probability_measure.limsup_measure_closed_le_of_tendsto MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the liminf of the measures of any open set
is at least the measure of the open set under the limit probability measure.
-/
theorem ProbabilityMeasure.le_liminf_measure_open_of_tendsto {Ω ι : Type _} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEmetricSpace Ω] [OpensMeasurableSpace Ω] {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {G : Set Ω} (G_open : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf fun i => (μs i : Measure Ω) G :=
  haveI h_closeds :
    ∀ F, IsClosed F → (L.limsup fun i => (μs i : Measure Ω) F) ≤ (μ : Measure Ω) F :=
    fun F F_closed => probability_measure.limsup_measure_closed_le_of_tendsto μs_lim F_closed
  le_measure_liminf_of_limsup_measure_compl_le G_open.measurable_set
    (h_closeds _ (is_closed_compl_iff.mpr G_open))
#align
  measure_theory.probability_measure.le_liminf_measure_open_of_tendsto MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto

theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' {Ω ι : Type _}
    {L : Filter ι} [MeasurableSpace Ω] [PseudoEmetricSpace Ω] [OpensMeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (E_nullbdry : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i => (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E)) :=
  haveI h_opens : ∀ G, IsOpen G → (μ : Measure Ω) G ≤ L.liminf fun i => (μs i : Measure Ω) G :=
    fun G G_open => probability_measure.le_liminf_measure_open_of_tendsto μs_lim G_open
  tendsto_measure_of_null_frontier h_opens E_nullbdry
#align
  measure_theory.probability_measure.tendsto_measure_of_null_frontier_of_tendsto' MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that if the boundary of a Borel set
carries no probability mass under the limit measure, then the limit of the measures of the set
equals the measure of the set under the limit probability measure.

A version with coercions to ordinary `ℝ≥0∞`-valued measures is
`measure_theory.probability_measure.tendsto_measure_of_null_frontier_of_tendsto'`.
-/
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto {Ω ι : Type _} {L : Filter ι}
    [MeasurableSpace Ω] [PseudoEmetricSpace Ω] [OpensMeasurableSpace Ω] {μ : ProbabilityMeasure Ω}
    {μs : ι → ProbabilityMeasure Ω} (μs_lim : Tendsto μs L (𝓝 μ)) {E : Set Ω}
    (E_nullbdry : μ (frontier E) = 0) : Tendsto (fun i => μs i E) L (𝓝 (μ E)) := by
  have E_nullbdry' : (μ : Measure Ω) (frontier E) = 0 := by
    rw [← probability_measure.ennreal_coe_fn_eq_coe_fn_to_measure, E_nullbdry, Ennreal.coe_zero]
  have key := probability_measure.tendsto_measure_of_null_frontier_of_tendsto' μs_lim E_nullbdry'
  exact (Ennreal.tendsto_to_nnreal (measure_ne_top (↑μ) E)).comp key
#align
  measure_theory.probability_measure.tendsto_measure_of_null_frontier_of_tendsto MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto

end ConvergenceImpliesLimsupClosedLe

--section
end MeasureTheory

--namespace
