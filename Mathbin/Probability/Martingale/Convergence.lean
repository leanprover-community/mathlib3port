/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathbin.Probability.Martingale.Upcrossing
import Mathbin.MeasureTheory.Function.UniformIntegrable
import Mathbin.MeasureTheory.Constructions.Polish

/-!

# Martingale convergence theorems

The martingale convergence theorems are a collection of theorems characterizing the convergence
of a martingale provided it satisfies some boundedness conditions. This file contains the
almost everywhere martingale convergence theorem which provides an almost everywhere limit to
an L¹ bounded submartingale.

## Main results

* `measure_theory.submartingale.ae_tendsto_limit_process`: the almost everywhere martingale
  convergence theorem: an L¹-bounded submartingale adapted to the filtration `ℱ` converges almost
  everywhere to its limit process.
* `measure_theory.submartingale.mem_ℒ1_limit_process`: the limit process of an L¹-bounded
  submartingale is integrable.

-/


open TopologicalSpace Filter MeasureTheory.Filtration

open Nnreal Ennreal MeasureTheory ProbabilityTheory BigOperators TopologicalSpace

namespace MeasureTheory

variable {Ω ι : Type _} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

variable {a b : ℝ} {f : ℕ → Ω → ℝ} {ω : Ω} {R : ℝ≥0 }

section AeConvergence

/-!

### Almost everywhere martingale convergence theorem

We will now prove the almost everywhere martingale convergence theorem.

The a.e. martingale convergence theorem states: if `f` is an L¹-bounded `ℱ`-submartingale, then
it converges almost everywhere to an integrable function which is measurable with respect to
the σ-algebra `ℱ∞ := ⨆ n, ℱ n`.

Mathematically, we proceed by first noting that a real sequence $(x_n)$ converges if
(a) $\limsup_{n \to \infty} |x_n| < \infty$, (b) for all $a < b \in \mathbb{Q}$ we have the
number of upcrossings of $(x_n)$ from below $a$ to above $b$ is finite.
Thus, for all $\omega$ satisfying $\limsup_{n \to \infty} |f_n(\omega)| < \infty$ and the number of
upcrossings of $(f_n(\omega))$ from below $a$ to above $b$ is finite for all $a < b \in \mathbb{Q}$,
we have $(f_n(\omega))$ is convergent.

Hence, assuming $(f_n)$ is L¹-bounded, using Fatou's lemma, we have
$$
  \mathbb{E] \limsup_{n \to \infty} |f_n| \le \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
implying $\limsup_{n \to \infty} |f_n| < \infty$ a.e. Furthermore, by the upcrossing estimate,
the number of upcrossings is finite almost everywhere implying $f$ converges pointwise almost
everywhere.

Thus, denoting $g$ the a.e. limit of $(f_n)$, $g$ is $\mathcal{F}_\infty$-measurable as for all
$n$, $f_n$ is $\mathcal{F}_n$-measurable and $\mathcal{F}_n \le \mathcal{F}_\infty$. Finally, $g$
is integrable as $|g| \le \liminf_{n \to \infty} |f_n|$ so
$$
  \mathbb{E}|g| \le \mathbb{E} \limsup_{n \to \infty} |f_n| \le
    \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
as required.

Implementation wise, we have `tendsto_of_no_upcrossings` which showed that
a bounded sequence converges if it does not visit below $a$ and above $b$ infinitely often
for all $a, b ∈ s$ for some dense set $s$. So, we may skip the first step provided we can prove
that the realizations are bounded almost everywhere. Indeed, suppose $(|f_n(\omega)|)$ is not
bounded, then either $f_n(\omega) \to \pm \infty$ or one of $\limsup f_n(\omega)$ or
$\liminf f_n(\omega)$ equals $\pm \infty$ while the other is finite. But the first case
contradicts $\liminf |f_n(\omega)| < \infty$ while the second case contradicts finite upcrossings.

-/


/-- If a stochastic process has bounded upcrossing from below `a` to above `b`,
then it does not frequently visit both below `a` and above `b`. -/
theorem not_frequently_of_upcrossings_lt_top (hab : a < b) (hω : upcrossings a b f ω ≠ ∞) :
    ¬((∃ᶠ n in at_top, f n ω < a) ∧ ∃ᶠ n in at_top, b < f n ω) := by
  rw [← lt_top_iff_ne_top, upcrossings_lt_top_iff] at hω
  replace hω : ∃ k, ∀ N, upcrossings_before a b f N ω < k
  · obtain ⟨k, hk⟩ := hω
    exact ⟨k + 1, fun N => lt_of_le_of_ltₓ (hk N) k.lt_succ_self⟩
    
  rintro ⟨h₁, h₂⟩
  rw [frequently_at_top] at h₁ h₂
  refine' not_not.2 hω _
  push_neg
  intro k
  induction' k with k ih
  · simp only [← zero_le', ← exists_const]
    
  · obtain ⟨N, hN⟩ := ih
    obtain ⟨N₁, hN₁, hN₁'⟩ := h₁ N
    obtain ⟨N₂, hN₂, hN₂'⟩ := h₂ N₁
    exact
      ⟨N₂ + 1,
        Nat.succ_le_of_ltₓ <| lt_of_le_of_ltₓ hN (upcrossings_before_lt_of_exists_upcrossing hab hN₁ hN₁' hN₂ hN₂')⟩
    

/-- A stochastic process that frequently visits below `a` and above `b` have infinite
upcrossings. -/
theorem upcrossings_eq_top_of_frequently_lt (hab : a < b) (h₁ : ∃ᶠ n in at_top, f n ω < a)
    (h₂ : ∃ᶠ n in at_top, b < f n ω) : upcrossings a b f ω = ∞ :=
  Classical.by_contradiction fun h => not_frequently_of_upcrossings_lt_top hab h ⟨h₁, h₂⟩

/-- A realization of a stochastic process with bounded upcrossings and bounded liminfs is
convergent.

We use the spelling `< ∞` instead of the standard `≠ ∞` in the assumptions since it is not as easy
to change `<` to `≠` under binders. -/
theorem tendsto_of_uncrossing_lt_top (hf₁ : (liminfₓ atTop fun n => (∥f n ω∥₊ : ℝ≥0∞)) < ∞)
    (hf₂ : ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞) : ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  by_cases' h : is_bounded_under (· ≤ ·) at_top fun n => abs (f n ω)
  · rw [is_bounded_under_le_abs] at h
    refine' tendsto_of_no_upcrossings Rat.dense_range_cast _ h.1 h.2
    · intro a ha b hb hab
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := ha, hb
      exact not_frequently_of_upcrossings_lt_top hab (hf₂ a b (Rat.cast_lt.1 hab)).Ne
      
    
  · obtain ⟨a, b, hab, h₁, h₂⟩ := Ennreal.exists_upcrossings_of_not_bounded_under hf₁.ne h
    exact False.elim ((hf₂ a b hab).Ne (upcrossings_eq_top_of_frequently_lt (Rat.cast_lt.2 hab) h₁ h₂))
    

/-- An L¹-bounded submartingale has bounded upcrossings almost everywhere. -/
theorem Submartingale.upcrossings_ae_lt_top' [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) (hab : a < b) : ∀ᵐ ω ∂μ, upcrossings a b f ω < ∞ := by
  refine' ae_lt_top (hf.adapted.measurable_upcrossings hab) _
  have := hf.mul_lintegral_upcrossings_le_lintegral_pos_part a b
  rw [mul_comm, ← Ennreal.le_div_iff_mul_le] at this
  · refine' (lt_of_le_of_ltₓ this (Ennreal.div_lt_top _ _)).Ne
    · have hR' : ∀ n, (∫⁻ ω, ∥f n ω - a∥₊ ∂μ) ≤ R + ∥a∥₊ * μ Set.Univ := by
        simp_rw [snorm_one_eq_lintegral_nnnorm] at hbdd
        intro n
        refine' (lintegral_mono _ : (∫⁻ ω, ∥f n ω - a∥₊ ∂μ) ≤ ∫⁻ ω, ∥f n ω∥₊ + ∥a∥₊ ∂μ).trans _
        · intro ω
          simp_rw [sub_eq_add_neg, ← nnnorm_neg a, ← Ennreal.coe_add, Ennreal.coe_le_coe]
          exact nnnorm_add_le _ _
          
        · simp_rw [lintegral_add_right _ measurable_const, lintegral_const]
          exact add_le_add (hbdd _) le_rfl
          
      refine'
        ne_of_ltₓ
          (supr_lt_iff.2
            ⟨R + ∥a∥₊ * μ Set.Univ,
              Ennreal.add_lt_top.2 ⟨Ennreal.coe_lt_top, Ennreal.mul_lt_top ennreal.coe_lt_top.ne (measure_ne_top _ _)⟩,
              fun n => le_transₓ _ (hR' n)⟩)
      refine' lintegral_mono fun ω => _
      rw [Ennreal.of_real_le_iff_le_to_real, Ennreal.coe_to_real, coe_nnnorm]
      by_cases' hnonneg : 0 ≤ f n ω - a
      · rw [LatticeOrderedCommGroup.pos_of_nonneg _ hnonneg, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        
      · rw [LatticeOrderedCommGroup.pos_of_nonpos _ (not_leₓ.1 hnonneg).le]
        exact norm_nonneg _
        
      · simp only [← Ne.def, ← Ennreal.coe_ne_top, ← not_false_iff]
        
      
    · simp only [← hab, ← Ne.def, ← Ennreal.of_real_eq_zero, ← sub_nonpos, ← not_leₓ]
      
    
  · simp only [← hab, ← Ne.def, ← Ennreal.of_real_eq_zero, ← sub_nonpos, ← not_leₓ, ← true_orₓ]
    
  · simp only [← Ne.def, ← Ennreal.of_real_ne_top, ← not_false_iff, ← true_orₓ]
    

theorem Submartingale.upcrossings_ae_lt_top [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞ := by
  simp only [← ae_all_iff, ← eventually_imp_distrib_left]
  rintro a b hab
  exact hf.upcrossings_ae_lt_top' hbdd (Rat.cast_lt.2 hab)

/-- An L¹-bounded submartingale converges almost everywhere. -/
theorem Submartingale.exists_ae_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  filter_upwards [hf.upcrossings_ae_lt_top hbdd,
    ae_bdd_liminf_at_top_of_snorm_bdd one_ne_zero (fun n => (hf.strongly_measurable n).Measurable.mono (ℱ.le n) le_rfl)
      hbdd] with ω h₁ h₂
  exact tendsto_of_uncrossing_lt_top h₂ h₁

theorem Submartingale.exists_ae_trim_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ.trim (Sup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _ : (⨆ n, ℱ n) ≤ m0), ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) :=
  by
  rw [ae_iff, trim_measurable_set_eq]
  · exact hf.exists_ae_tendsto_of_bdd hbdd
    
  · exact
      MeasurableSet.compl
        (@measurable_set_exists_tendsto _ _ _ _ _ _ (⨆ n, ℱ n) _ _ _ _ _ fun n =>
          (hf.strongly_measurable n).Measurable.mono (le_Sup ⟨n, rfl⟩) le_rfl)
    

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a `⨆ n, ℱ n`-measurable function. -/
theorem Submartingale.ae_tendsto_limit_process [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, snorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) := by
  classical
  suffices ∃ g, strongly_measurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, tendsto (fun n => f n ω) at_top (𝓝 (g ω)) by
    rw [limit_process, dif_pos this]
    exact (Classical.some_spec this).2
  set g' : Ω → ℝ := fun ω => if h : ∃ c, tendsto (fun n => f n ω) at_top (𝓝 c) then h.some else 0
  have hle : (⨆ n, ℱ n) ≤ m0 := Sup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _
  have hg' : ∀ᵐ ω ∂μ.trim hle, tendsto (fun n => f n ω) at_top (𝓝 (g' ω)) := by
    filter_upwards [hf.exists_ae_trim_tendsto_of_bdd hbdd] with ω hω
    simp_rw [g', dif_pos hω]
    exact hω.some_spec
  have hg'm : @ae_strongly_measurable _ _ _ (⨆ n, ℱ n) g' (μ.trim hle) :=
    (@ae_measurable_of_tendsto_metrizable_ae' _ _ (⨆ n, ℱ n) _ _ _ _ _ _ _
        (fun n => ((hf.strongly_measurable n).Measurable.mono (le_Sup ⟨n, rfl⟩ : ℱ n ≤ ⨆ n, ℱ n) le_rfl).AeMeasurable)
        hg').AeStronglyMeasurable
  obtain ⟨g, hgm, hae⟩ := hg'm
  have hg : ∀ᵐ ω ∂μ.trim hle, tendsto (fun n => f n ω) at_top (𝓝 (g ω)) := by
    filter_upwards [hae, hg'] with ω hω hg'ω
    exact hω ▸ hg'ω
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩

/-- The limiting process of an Lᵖ-bounded submartingale is Lᵖ. -/
theorem Submartingale.mem_ℒp_limit_process {p : ℝ≥0∞} (hf : Submartingale f ℱ μ) (hbdd : ∀ n, snorm (f n) p μ ≤ R) :
    Memℒp (ℱ.limitProcess f μ) p μ :=
  mem_ℒp_limit_process_of_snorm_bdd (fun n => ((hf.StronglyMeasurable n).mono (ℱ.le n)).AeStronglyMeasurable) hbdd

end AeConvergence

end MeasureTheory

