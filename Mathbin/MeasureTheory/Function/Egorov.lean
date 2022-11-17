/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathbin.MeasureTheory.Integral.SetIntegral

/-!
# Egorov theorem

This file contains the Egorov theorem which states that an almost everywhere convergent
sequence on a finite measure space converges uniformly except on an arbitrarily small set.
This theorem is useful for the Vitali convergence theorem as well as theorems regarding
convergence in measure.

## Main results

* `measure_theory.egorov`: Egorov's theorem which shows that a sequence of almost everywhere
  convergent functions converges uniformly except on an arbitrarily small set.

-/


noncomputable section

open Classical MeasureTheory Nnreal Ennreal TopologicalSpace

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type _} {m : MeasurableSpace α} [MetricSpace β] {μ : Measure α}

namespace Egorov

/-- Given a sequence of functions `f` and a function `g`, `not_convergent_seq f g n j` is the
set of elements such that `f k x` and `g x` are separated by at least `1 / (n + 1)` for some
`k ≥ j`.

This definition is useful for Egorov's theorem. -/
def notConvergentSeq [Preorder ι] (f : ι → α → β) (g : α → β) (n : ℕ) (j : ι) : Set α :=
  ⋃ (k) (hk : j ≤ k), { x | 1 / (n + 1 : ℝ) < dist (f k x) (g x) }
#align measure_theory.egorov.not_convergent_seq MeasureTheory.Egorov.notConvergentSeq

variable {n : ℕ} {i j : ι} {s : Set α} {ε : ℝ} {f : ι → α → β} {g : α → β}

theorem mem_not_convergent_seq_iff [Preorder ι] {x : α} :
    x ∈ notConvergentSeq f g n j ↔ ∃ (k) (hk : j ≤ k), 1 / (n + 1 : ℝ) < dist (f k x) (g x) := by
  simp_rw [not_convergent_seq, mem_Union]
  rfl
#align measure_theory.egorov.mem_not_convergent_seq_iff MeasureTheory.Egorov.mem_not_convergent_seq_iff

theorem not_convergent_seq_antitone [Preorder ι] : Antitone (notConvergentSeq f g n) := fun j k hjk =>
  Union₂_mono' $ fun l hl => ⟨l, le_trans hjk hl, Subset.rfl⟩
#align measure_theory.egorov.not_convergent_seq_antitone MeasureTheory.Egorov.not_convergent_seq_antitone

theorem measure_inter_not_convergent_seq_eq_zero [SemilatticeSup ι] [Nonempty ι]
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ ⋂ j, notConvergentSeq f g n j) = 0 := by
  simp_rw [Metric.tendsto_at_top, ae_iff] at hfg
  rw [← nonpos_iff_eq_zero, ← hfg]
  refine' measure_mono fun x => _
  simp only [mem_inter_iff, mem_Inter, ge_iff_le, mem_not_convergent_seq_iff]
  push_neg
  rintro ⟨hmem, hx⟩
  refine' ⟨hmem, 1 / (n + 1 : ℝ), Nat.one_div_pos_of_nat, fun N => _⟩
  obtain ⟨n, hn₁, hn₂⟩ := hx N
  exact ⟨n, hn₁, hn₂.le⟩
#align
  measure_theory.egorov.measure_inter_not_convergent_seq_eq_zero MeasureTheory.Egorov.measure_inter_not_convergent_seq_eq_zero

theorem notConvergentSeqMeasurableSet [Preorder ι] [Countable ι] (hf : ∀ n, strongly_measurable[m] (f n))
    (hg : StronglyMeasurable g) : MeasurableSet (notConvergentSeq f g n j) :=
  MeasurableSet.union fun k =>
    MeasurableSet.union $ fun hk => StronglyMeasurable.measurableSetLt stronglyMeasurableConst $ (hf k).dist hg
#align measure_theory.egorov.not_convergent_seq_measurable_set MeasureTheory.Egorov.notConvergentSeqMeasurableSet

theorem measure_not_convergent_seq_tendsto_zero [SemilatticeSup ι] [Countable ι] (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    Tendsto (fun j => μ (s ∩ notConvergentSeq f g n j)) atTop (𝓝 0) := by
  cases isEmpty_or_nonempty ι
  · have : (fun j => μ (s ∩ not_convergent_seq f g n j)) = fun j => 0 := by simp only [eq_iff_true_of_subsingleton]
    rw [this]
    exact tendsto_const_nhds
    
  rw [← measure_inter_not_convergent_seq_eq_zero hfg n, inter_Inter]
  refine'
    tendsto_measure_Inter (fun n => hsm.inter $ not_convergent_seq_measurable_set hf hg)
      (fun k l hkl => inter_subset_inter_right _ $ not_convergent_seq_antitone hkl)
      ⟨h.some, (lt_of_le_of_lt (measure_mono $ inter_subset_left _ _) (lt_top_iff_ne_top.2 hs)).Ne⟩
#align
  measure_theory.egorov.measure_not_convergent_seq_tendsto_zero MeasureTheory.Egorov.measure_not_convergent_seq_tendsto_zero

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι]

theorem exists_not_convergent_seq_lt (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    ∃ j : ι, μ (s ∩ notConvergentSeq f g n j) ≤ Ennreal.ofReal (ε * 2⁻¹ ^ n) := by
  obtain ⟨N, hN⟩ :=
    (Ennreal.tendsto_at_top Ennreal.zero_ne_top).1 (measure_not_convergent_seq_tendsto_zero hf hg hsm hs hfg n)
      (Ennreal.ofReal (ε * 2⁻¹ ^ n)) _
  · rw [zero_add] at hN
    exact ⟨N, (hN N le_rfl).2⟩
    
  · rw [gt_iff_lt, Ennreal.of_real_pos]
    exact mul_pos hε (pow_pos (by norm_num) n)
    
#align measure_theory.egorov.exists_not_convergent_seq_lt MeasureTheory.Egorov.exists_not_convergent_seq_lt

/-- Given some `ε > 0`, `not_convergent_seq_lt_index` provides the index such that
`not_convergent_seq` (intersected with a set of finite measure) has measure less than
`ε * 2⁻¹ ^ n`.

This definition is useful for Egorov's theorem. -/
def notConvergentSeqLtIndex (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    ι :=
  Classical.choose $ exists_not_convergent_seq_lt hε hf hg hsm hs hfg n
#align measure_theory.egorov.not_convergent_seq_lt_index MeasureTheory.Egorov.notConvergentSeqLtIndex

theorem not_convergent_seq_lt_index_spec (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ notConvergentSeq f g n (notConvergentSeqLtIndex hε hf hg hsm hs hfg n)) ≤ Ennreal.ofReal (ε * 2⁻¹ ^ n) :=
  Classical.choose_spec $ exists_not_convergent_seq_lt hε hf hg hsm hs hfg n
#align measure_theory.egorov.not_convergent_seq_lt_index_spec MeasureTheory.Egorov.not_convergent_seq_lt_index_spec

/-- Given some `ε > 0`, `Union_not_convergent_seq` is the union of `not_convergent_seq` with
specific indicies such that `Union_not_convergent_seq` has measure less equal than `ε`.

This definition is useful for Egorov's theorem. -/
def unionNotConvergentSeq (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Set α :=
  ⋃ n, s ∩ notConvergentSeq f g n (notConvergentSeqLtIndex (half_pos hε) hf hg hsm hs hfg n)
#align measure_theory.egorov.Union_not_convergent_seq MeasureTheory.Egorov.unionNotConvergentSeq

theorem unionNotConvergentSeqMeasurableSet (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MeasurableSet $ unionNotConvergentSeq hε hf hg hsm hs hfg :=
  MeasurableSet.union fun n => hsm.inter $ notConvergentSeqMeasurableSet hf hg
#align
  measure_theory.egorov.Union_not_convergent_seq_measurable_set MeasureTheory.Egorov.unionNotConvergentSeqMeasurableSet

theorem measure_Union_not_convergent_seq (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    μ (unionNotConvergentSeq hε hf hg hsm hs hfg) ≤ Ennreal.ofReal ε := by
  refine'
    le_trans (measure_Union_le _)
      (le_trans (Ennreal.tsum_le_tsum $ not_convergent_seq_lt_index_spec (half_pos hε) hf hg hsm hs hfg) _)
  simp_rw [Ennreal.of_real_mul (half_pos hε).le]
  rw [Ennreal.tsum_mul_left, ← Ennreal.of_real_tsum_of_nonneg, inv_eq_one_div, tsum_geometric_two, ←
    Ennreal.of_real_mul (half_pos hε).le, div_mul_cancel ε two_ne_zero]
  · exact le_rfl
    
  · exact fun n => pow_nonneg (by norm_num) _
    
  · rw [inv_eq_one_div]
    exact summable_geometric_two
    
#align measure_theory.egorov.measure_Union_not_convergent_seq MeasureTheory.Egorov.measure_Union_not_convergent_seq

theorem Union_not_convergent_seq_subset (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    unionNotConvergentSeq hε hf hg hsm hs hfg ⊆ s := by
  rw [Union_not_convergent_seq, ← inter_Union]
  exact inter_subset_left _ _
#align measure_theory.egorov.Union_not_convergent_seq_subset MeasureTheory.Egorov.Union_not_convergent_seq_subset

theorem tendsto_uniformly_on_diff_Union_not_convergent_seq (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop (s \ Egorov.unionNotConvergentSeq hε hf hg hsm hs hfg) := by
  rw [Metric.tendsto_uniformly_on_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  rw [eventually_at_top]
  refine' ⟨egorov.not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg N, fun n hn x hx => _⟩
  simp only [mem_diff, egorov.Union_not_convergent_seq, not_exists, mem_Union, mem_inter_iff, not_and,
    exists_and_left] at hx
  obtain ⟨hxs, hx⟩ := hx
  specialize hx hxs N
  rw [egorov.mem_not_convergent_seq_iff] at hx
  push_neg  at hx
  rw [dist_comm]
  exact lt_of_le_of_lt (hx n hn) hN
#align
  measure_theory.egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq MeasureTheory.Egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq

end Egorov

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι] {γ : Type _} [TopologicalSpace γ] {f : ι → α → β} {g : α → β}
  {s : Set α}

/- ./././Mathport/Syntax/Translate/Basic.lean:611:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- **Egorov's theorem**: If `f : ι → α → β` is a sequence of strongly measurable functions that
converges to `g : α → β` almost everywhere on a measurable set `s` of finite measure,
then for all `ε > 0`, there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` converges to `g`
uniformly on `s \ t`. We require the index type `ι` to be countable, and usually `ι = ℕ`.

In other words, a sequence of almost everywhere convergent functions converges uniformly except on
an arbitrarily small set. -/
theorem tendsto_uniformly_on_of_ae_tendsto (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ}
    (hε : 0 < ε) : ∃ (t) (_ : t ⊆ s), MeasurableSet t ∧ μ t ≤ Ennreal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  ⟨Egorov.unionNotConvergentSeq hε hf hg hsm hs hfg, Egorov.Union_not_convergent_seq_subset hε hf hg hsm hs hfg,
    Egorov.unionNotConvergentSeqMeasurableSet hε hf hg hsm hs hfg,
    Egorov.measure_Union_not_convergent_seq hε hf hg hsm hs hfg,
    Egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq hε hf hg hsm hs hfg⟩
#align measure_theory.tendsto_uniformly_on_of_ae_tendsto MeasureTheory.tendsto_uniformly_on_of_ae_tendsto

/-- Egorov's theorem for finite measure spaces. -/
theorem tendsto_uniformly_on_of_ae_tendsto' [IsFiniteMeasure μ] (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, MeasurableSet t ∧ μ t ≤ Ennreal.ofReal ε ∧ TendstoUniformlyOn f g atTop (tᶜ) := by
  obtain ⟨t, _, ht, htendsto⟩ :=
    tendsto_uniformly_on_of_ae_tendsto hf hg MeasurableSet.univ (measure_ne_top μ univ) _ hε
  · refine' ⟨_, ht, _⟩
    rwa [compl_eq_univ_diff]
    
  · filter_upwards [hfg] with _ htendsto _ using htendsto
    
#align measure_theory.tendsto_uniformly_on_of_ae_tendsto' MeasureTheory.tendsto_uniformly_on_of_ae_tendsto'

end MeasureTheory

