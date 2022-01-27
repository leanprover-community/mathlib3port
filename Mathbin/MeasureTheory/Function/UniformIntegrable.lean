import Mathbin.MeasureTheory.Integral.SetIntegral

/-!
# Uniform integrability

This file will be used in the future to define uniform integrability. Uniform integrability
is an important notion in both measure theory as well as probability theory. So far this file
only contains the Egorov theorem which will be used to prove the Vitali convergence theorem
which is one of the main results about uniform integrability.

## Main results

* `measure_theory.egorov`: Egorov's theorem which shows that a sequence of almost everywhere
  convergent functions converges uniformly except on an arbitrarily small set.

-/


noncomputable section

open_locale Classical MeasureTheory Nnreal Ennreal TopologicalSpace

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type _} {m : MeasurableSpace α} [MetricSpace β] {μ : Measureₓ α}

section

/-! We will in this section prove Egorov's theorem. -/


namespace Egorov

/-- Given a sequence of functions `f` and a function `g`, `not_convergent_seq f g i j` is the
set of elements such that `f k x` and `g x` are separated by at least `1 / (i + 1)` for some
`k ≥ j`.

This definition is useful for Egorov's theorem. -/
def not_convergent_seq (f : ℕ → α → β) (g : α → β) (i j : ℕ) : Set α :=
  ⋃ (k) (hk : j ≤ k), { x | 1 / (i + 1 : ℝ) < dist (f k x) (g x) }

variable {i j : ℕ} {s : Set α} {ε : ℝ} {f : ℕ → α → β} {g : α → β}

theorem mem_not_convergent_seq_iff {x : α} :
    x ∈ not_convergent_seq f g i j ↔ ∃ (k : _)(hk : j ≤ k), 1 / (i + 1 : ℝ) < dist (f k x) (g x) := by
  simp_rw [not_convergent_seq, mem_Union]
  rfl

theorem not_convergent_seq_antitone : Antitone (not_convergent_seq f g i) := fun j k hjk =>
  Union₂_mono' fun l hl => ⟨l, le_transₓ hjk hl, subset.rfl⟩

theorem measure_inter_not_convergent_seq_eq_zero (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x)))
    (i : ℕ) : μ (s ∩ ⋂ j, not_convergent_seq f g i j) = 0 := by
  simp_rw [Metric.tendsto_at_top, ae_iff]  at hfg
  rw [← nonpos_iff_eq_zero, ← hfg]
  refine' measure_mono fun x => _
  simp only [mem_inter_eq, mem_Inter, ge_iff_le, mem_not_convergent_seq_iff]
  push_neg
  rintro ⟨hmem, hx⟩
  refine' ⟨hmem, 1 / (i + 1 : ℝ), Nat.one_div_pos_of_nat, fun N => _⟩
  obtain ⟨n, hn₁, hn₂⟩ := hx N
  exact ⟨n, hn₁, hn₂.le⟩

variable [second_countable_topology β] [MeasurableSpace β] [BorelSpace β]

theorem not_convergent_seq_measurable_set (hf : ∀ n, measurable[m] (f n)) (hg : Measurable g) :
    MeasurableSet (not_convergent_seq f g i j) :=
  MeasurableSet.Union fun k => MeasurableSet.Union_Prop fun hk => measurable_set_lt measurable_const <| (hf k).dist hg

theorem measure_not_convergent_seq_tendsto_zero (hf : ∀ n, Measurable (f n)) (hg : Measurable g) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x))) (i : ℕ) :
    tendsto (fun j => μ (s ∩ not_convergent_seq f g i j)) at_top (𝓝 0) := by
  rw [← measure_inter_not_convergent_seq_eq_zero hfg, inter_Inter]
  exact
    tendsto_measure_Inter (fun n => hsm.inter <| not_convergent_seq_measurable_set hf hg)
      (fun k l hkl => inter_subset_inter_right _ <| not_convergent_seq_antitone hkl)
      ⟨0, (lt_of_le_of_ltₓ (measure_mono <| inter_subset_left _ _) (lt_top_iff_ne_top.2 hs)).Ne⟩

theorem exists_not_convergent_seq_lt (hε : 0 < ε) (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x))) (i : ℕ) :
    ∃ j : ℕ, μ (s ∩ not_convergent_seq f g i j) ≤ Ennreal.ofReal (ε * 2⁻¹ ^ i) := by
  obtain ⟨N, hN⟩ :=
    (Ennreal.tendsto_at_top Ennreal.zero_ne_top).1 (measure_not_convergent_seq_tendsto_zero hf hg hsm hs hfg i)
      (Ennreal.ofReal (ε * 2⁻¹ ^ i)) _
  · rw [zero_addₓ] at hN
    exact ⟨N, (hN N le_rfl).2⟩
    
  · rw [gt_iff_lt, Ennreal.of_real_pos]
    exact
      mul_pos hε
        (pow_pos
          (by
            norm_num)
          _)
    

/-- Given some `ε > 0`, `not_convergent_seq_lt_index` provides the index such that
`not_convergent_seq` (intersected with a set of finite measure) has measure less than
`ε * 2⁻¹ ^ i`.

This definition is useful for Egorov's theorem. -/
def not_convergent_seq_lt_index (hε : 0 < ε) (hf : ∀ n, Measurable (f n)) (hg : Measurable g) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x))) (i : ℕ) : ℕ :=
  Classical.some <| exists_not_convergent_seq_lt hε hf hg hsm hs hfg i

theorem not_convergent_seq_lt_index_spec (hε : 0 < ε) (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x))) (i : ℕ) :
    μ (s ∩ not_convergent_seq f g i (not_convergent_seq_lt_index hε hf hg hsm hs hfg i)) ≤
      Ennreal.ofReal (ε * 2⁻¹ ^ i) :=
  Classical.some_spec <| exists_not_convergent_seq_lt hε hf hg hsm hs hfg i

/-- Given some `ε > 0`, `Union_not_convergent_seq` is the union of `not_convergent_seq` with
specific indicies such that `Union_not_convergent_seq` has measure less equal than `ε`.

This definition is useful for Egorov's theorem. -/
def Union_not_convergent_seq (hε : 0 < ε) (hf : ∀ n, Measurable (f n)) (hg : Measurable g) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x))) : Set α :=
  ⋃ i, s ∩ not_convergent_seq f g i (not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg i)

theorem Union_not_convergent_seq_measurable_set (hε : 0 < ε) (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x))) :
    MeasurableSet <| Union_not_convergent_seq hε hf hg hsm hs hfg :=
  MeasurableSet.Union fun n => hsm.inter <| not_convergent_seq_measurable_set hf hg

theorem measure_Union_not_convergent_seq (hε : 0 < ε) (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x))) :
    μ (Union_not_convergent_seq hε hf hg hsm hs hfg) ≤ Ennreal.ofReal ε := by
  refine'
    le_transₓ (measure_Union_le _)
      (le_transₓ (Ennreal.tsum_le_tsum <| not_convergent_seq_lt_index_spec (half_pos hε) hf hg hsm hs hfg) _)
  simp_rw [Ennreal.of_real_mul (half_pos hε).le]
  rw [Ennreal.tsum_mul_left, ← Ennreal.of_real_tsum_of_nonneg, inv_eq_one_div, tsum_geometric_two, ←
    Ennreal.of_real_mul (half_pos hε).le, div_mul_cancel ε two_ne_zero]
  · exact le_rfl
    
  · exact fun n =>
      pow_nonneg
        (by
          norm_num)
        _
    
  · rw [inv_eq_one_div]
    exact summable_geometric_two
    

theorem Union_not_convergent_seq_subset (hε : 0 < ε) (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x))) :
    Union_not_convergent_seq hε hf hg hsm hs hfg ⊆ s := by
  rw [Union_not_convergent_seq, ← inter_Union]
  exact inter_subset_left _ _

theorem tendsto_uniformly_on_diff_Union_not_convergent_seq (hε : 0 < ε) (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x))) :
    TendstoUniformlyOn f g at_top (s \ egorov.Union_not_convergent_seq hε hf hg hsm hs hfg) := by
  rw [Metric.tendsto_uniformly_on_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  rw [eventually_at_top]
  refine' ⟨egorov.not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg N, fun n hn x hx => _⟩
  simp only [mem_diff, egorov.Union_not_convergent_seq, not_exists, mem_Union, mem_inter_eq, not_and,
    exists_and_distrib_left] at hx
  obtain ⟨hxs, hx⟩ := hx
  specialize hx hxs N
  rw [egorov.mem_not_convergent_seq_iff] at hx
  push_neg  at hx
  rw [dist_comm]
  exact lt_of_le_of_ltₓ (hx n hn) hN

end Egorov

variable [second_countable_topology β] [MeasurableSpace β] [BorelSpace β] {f : ℕ → α → β} {g : α → β} {s : Set α}

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- **Egorov's theorem**: If `f : ℕ → α → β` is a sequence of measurable functions that converges
to `g : α → β` almost everywhere on a measurable set `s` of finite measure, then for all `ε > 0`,
there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` converges to `g` uniformly on `s \ t`.

In other words, a sequence of almost everywhere convergent functions converges uniformly except on
an arbitrarily small set. -/
theorem tendsto_uniformly_on_of_ae_tendsto (hf : ∀ n, Measurable (f n)) (hg : Measurable g) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (fun n => f n x) at_top (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : _)(_ : t ⊆ s), MeasurableSet t ∧ μ t ≤ Ennreal.ofReal ε ∧ TendstoUniformlyOn f g at_top (s \ t) :=
  ⟨egorov.Union_not_convergent_seq hε hf hg hsm hs hfg, egorov.Union_not_convergent_seq_subset hε hf hg hsm hs hfg,
    egorov.Union_not_convergent_seq_measurable_set hε hf hg hsm hs hfg,
    egorov.measure_Union_not_convergent_seq hε hf hg hsm hs hfg,
    egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq hε hf hg hsm hs hfg⟩

/-- Egorov's theorem for finite measure spaces. -/
theorem tendsto_uniformly_on_of_ae_tendsto' [is_finite_measure μ] (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hfg : ∀ᵐ x ∂μ, tendsto (fun n => f n x) at_top (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, MeasurableSet t ∧ μ t ≤ Ennreal.ofReal ε ∧ TendstoUniformlyOn f g at_top (tᶜ) := by
  obtain ⟨t, _, ht, htendsto⟩ :=
    tendsto_uniformly_on_of_ae_tendsto hf hg MeasurableSet.univ (measure_ne_top μ univ) _ hε
  · refine' ⟨_, ht, _⟩
    rwa [compl_eq_univ_diff]
    
  · filter_upwards [hfg] with _ htendsto _ using htendsto
    

end

end MeasureTheory

