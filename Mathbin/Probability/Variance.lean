/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Kexing Ying

! This file was ported from Lean 3 source module probability.variance
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Probability.Notation
import Mathbin.Probability.Integration

/-!
# Variance of random variables

We define the variance of a real-valued random variable as `Var[X] = 𝔼[(X - 𝔼[X])^2]` (in the
`probability_theory` locale).

## Main definitions

* `probability_theory.evariance`: the variance of a real-valued random variable as a extended
  non-negative real.
* `probability_theory.variance`: the variance of a real-valued random variable as a real number.

## Main results

* `probability_theory.variance_le_expectation_sq`: the inequality `Var[X] ≤ 𝔼[X^2]`.
* `probability_theory.meas_ge_le_variance_div_sq`: Chebyshev's inequality, i.e.,
      `ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ennreal.of_real (Var[X] / c ^ 2)`.
* `probability_theory.meas_ge_le_evariance_div_sq`: Chebyshev's inequality formulated with
  `evariance` without requiring the random variables to be L².
* `probability_theory.indep_fun.variance_add`: the variance of the sum of two independent
  random variables is the sum of the variances.
* `probability_theory.indep_fun.variance_sum`: the variance of a finite sum of pairwise
  independent random variables is the sum of the variances.
-/


open MeasureTheory Filter Finset

noncomputable section

open BigOperators MeasureTheory ProbabilityTheory Ennreal Nnreal

namespace ProbabilityTheory

/-- The `ℝ≥0∞`-valued variance of a real-valued random variable defined as the Lebesgue integral of
`(X - 𝔼[X])^2`. -/
def evariance {Ω : Type _} {m : MeasurableSpace Ω} (X : Ω → ℝ) (μ : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ω, ‖X ω - μ[X]‖₊ ^ 2 ∂μ
#align probability_theory.evariance ProbabilityTheory.evariance

/-- The `ℝ`-valued variance of a real-valued random variable defined by applying `ennreal.to_real`
to `evariance`. -/
def variance {Ω : Type _} {m : MeasurableSpace Ω} (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  (evariance X μ).toReal
#align probability_theory.variance ProbabilityTheory.variance

variable {Ω : Type _} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}

theorem MeasureTheory.Memℒp.evariance_lt_top [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    evariance X μ < ∞ :=
  by
  have := Ennreal.pow_lt_top (hX.sub <| mem_ℒp_const <| μ[X]).2 2
  rw [snorm_eq_lintegral_rpow_nnnorm Ennreal.two_ne_zero Ennreal.two_ne_top, ← Ennreal.rpow_two] at
    this
  simp only [Pi.sub_apply, Ennreal.toReal_bit0, Ennreal.one_toReal, one_div] at this
  rw [← Ennreal.rpow_mul, inv_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), Ennreal.rpow_one] at this
  simp_rw [Ennreal.rpow_two] at this
  exact this
#align measure_theory.mem_ℒp.evariance_lt_top MeasureTheory.Memℒp.evariance_lt_top

theorem evariance_eq_top [IsFiniteMeasure μ] (hXm : AeStronglyMeasurable X μ) (hX : ¬Memℒp X 2 μ) :
    evariance X μ = ∞ := by
  by_contra h
  rw [← Ne.def, ← lt_top_iff_ne_top] at h
  have : mem_ℒp (fun ω => X ω - μ[X]) 2 μ :=
    by
    refine' ⟨hXm.sub ae_strongly_measurable_const, _⟩
    rw [snorm_eq_lintegral_rpow_nnnorm Ennreal.two_ne_zero Ennreal.two_ne_top]
    simp only [Ennreal.toReal_bit0, Ennreal.one_toReal, Ennreal.rpow_two, Ne.def]
    exact Ennreal.rpow_lt_top_of_nonneg (by simp) h.ne
  refine' hX _
  convert this.add (mem_ℒp_const <| μ[X])
  ext ω
  rw [Pi.add_apply, sub_add_cancel]
#align probability_theory.evariance_eq_top ProbabilityTheory.evariance_eq_top

theorem evariance_lt_top_iff_memℒp [IsFiniteMeasure μ] (hX : AeStronglyMeasurable X μ) :
    evariance X μ < ∞ ↔ Memℒp X 2 μ :=
  by
  refine' ⟨_, MeasureTheory.Memℒp.evariance_lt_top⟩
  contrapose
  rw [not_lt, top_le_iff]
  exact evariance_eq_top hX
#align probability_theory.evariance_lt_top_iff_mem_ℒp ProbabilityTheory.evariance_lt_top_iff_memℒp

theorem MeasureTheory.Memℒp.ofReal_variance_eq [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    Ennreal.ofReal (variance X μ) = evariance X μ :=
  by
  rw [variance, Ennreal.ofReal_toReal]
  exact hX.evariance_lt_top.ne
#align measure_theory.mem_ℒp.of_real_variance_eq MeasureTheory.Memℒp.ofReal_variance_eq

include m

theorem evariance_eq_lintegral_ofReal (X : Ω → ℝ) (μ : Measure Ω) :
    evariance X μ = ∫⁻ ω, Ennreal.ofReal ((X ω - μ[X]) ^ 2) ∂μ :=
  by
  rw [evariance]
  congr
  ext1 ω
  rw [pow_two, ← Ennreal.coe_mul, ← nnnorm_mul, ← pow_two]
  congr
  exact (Real.toNnreal_eq_nnnorm_of_nonneg <| sq_nonneg _).symm
#align probability_theory.evariance_eq_lintegral_of_real ProbabilityTheory.evariance_eq_lintegral_ofReal

theorem MeasureTheory.Memℒp.variance_eq_of_integral_eq_zero (hX : Memℒp X 2 μ) (hXint : μ[X] = 0) :
    variance X μ = μ[X ^ 2] :=
  by
  rw [variance, evariance_eq_lintegral_of_real, ← of_real_integral_eq_lintegral_of_real,
      Ennreal.toReal_ofReal] <;>
    simp_rw [hXint, sub_zero]
  · rfl
  · exact integral_nonneg fun ω => pow_two_nonneg _
  · convert hX.integrable_norm_rpow Ennreal.two_ne_zero Ennreal.two_ne_top
    ext ω
    simp only [Pi.sub_apply, Real.norm_eq_abs, Ennreal.toReal_bit0, Ennreal.one_toReal,
      Real.rpow_two, pow_bit0_abs]
  · exact ae_of_all _ fun ω => pow_two_nonneg _
#align measure_theory.mem_ℒp.variance_eq_of_integral_eq_zero MeasureTheory.Memℒp.variance_eq_of_integral_eq_zero

theorem MeasureTheory.Memℒp.variance_eq [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    variance X μ = μ[(X - fun ω => μ[X]) ^ 2] :=
  by
  rw [variance, evariance_eq_lintegral_of_real, ← of_real_integral_eq_lintegral_of_real,
    Ennreal.toReal_ofReal]
  · rfl
  · exact integral_nonneg fun ω => pow_two_nonneg _
  · convert
      (hX.sub <| mem_ℒp_const (μ[X])).integrableNormRpow Ennreal.two_ne_zero Ennreal.two_ne_top
    ext ω
    simp only [Pi.sub_apply, Real.norm_eq_abs, Ennreal.toReal_bit0, Ennreal.one_toReal,
      Real.rpow_two, pow_bit0_abs]
  · exact ae_of_all _ fun ω => pow_two_nonneg _
#align measure_theory.mem_ℒp.variance_eq MeasureTheory.Memℒp.variance_eq

@[simp]
theorem evariance_zero : evariance 0 μ = 0 := by simp [evariance]
#align probability_theory.evariance_zero ProbabilityTheory.evariance_zero

theorem evariance_eq_zero_iff (hX : AeMeasurable X μ) : evariance X μ = 0 ↔ X =ᵐ[μ] fun ω => μ[X] :=
  by
  rw [evariance, lintegral_eq_zero_iff']
  constructor <;> intro hX <;> filter_upwards [hX]with ω hω
  · simp only [Pi.zero_apply, pow_eq_zero_iff, Nat.succ_pos', Ennreal.coe_eq_zero, nnnorm_eq_zero,
      sub_eq_zero] at hω
    exact hω
  · rw [hω]
    simp
  · measurability
#align probability_theory.evariance_eq_zero_iff ProbabilityTheory.evariance_eq_zero_iff

theorem evariance_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    evariance (fun ω => c * X ω) μ = Ennreal.ofReal (c ^ 2) * evariance X μ :=
  by
  rw [evariance, evariance, ← lintegral_const_mul' _ _ ennreal.of_real_lt_top.ne]
  congr
  ext1 ω
  rw [Ennreal.ofReal, ← Ennreal.coe_pow, ← Ennreal.coe_pow, ← Ennreal.coe_mul]
  congr
  rw [← sq_abs, ← Real.rpow_two, Real.toNnreal_rpow_of_nonneg (abs_nonneg _), Nnreal.rpow_two, ←
    mul_pow, Real.toNnreal_mul_nnnorm _ (abs_nonneg _)]
  conv_rhs => rw [← nnnorm_norm, norm_mul, norm_abs_eq_norm, ← norm_mul, nnnorm_norm, mul_sub]
  congr
  rw [mul_comm]
  simp_rw [← smul_eq_mul, ← integral_smul_const, smul_eq_mul, mul_comm]
#align probability_theory.evariance_mul ProbabilityTheory.evariance_mul

-- mathport name: probability_theory.evariance
scoped notation "eVar[" X "]" => ProbabilityTheory.evariance X MeasureTheory.MeasureSpace.volume

@[simp]
theorem variance_zero (μ : Measure Ω) : variance 0 μ = 0 := by
  simp only [variance, evariance_zero, Ennreal.zero_toReal]
#align probability_theory.variance_zero ProbabilityTheory.variance_zero

theorem variance_nonneg (X : Ω → ℝ) (μ : Measure Ω) : 0 ≤ variance X μ :=
  Ennreal.toReal_nonneg
#align probability_theory.variance_nonneg ProbabilityTheory.variance_nonneg

theorem variance_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (fun ω => c * X ω) μ = c ^ 2 * variance X μ :=
  by
  rw [variance, evariance_mul, Ennreal.toReal_mul, Ennreal.toReal_ofReal (sq_nonneg _)]
  rfl
#align probability_theory.variance_mul ProbabilityTheory.variance_mul

theorem variance_smul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (c • X) μ = c ^ 2 * variance X μ :=
  variance_mul c X μ
#align probability_theory.variance_smul ProbabilityTheory.variance_smul

theorem variance_smul' {A : Type _} [CommSemiring A] [Algebra A ℝ] (c : A) (X : Ω → ℝ)
    (μ : Measure Ω) : variance (c • X) μ = c ^ 2 • variance X μ :=
  by
  convert variance_smul (algebraMap A ℝ c) X μ
  · ext1 x
    simp only [algebraMap_smul]
  · simp only [Algebra.smul_def, map_pow]
#align probability_theory.variance_smul' ProbabilityTheory.variance_smul'

-- mathport name: probability_theory.variance
scoped notation "Var[" X "]" => ProbabilityTheory.variance X MeasureTheory.MeasureSpace.volume

omit m

variable [MeasureSpace Ω]

theorem variance_def' [IsProbabilityMeasure (ℙ : Measure Ω)] {X : Ω → ℝ} (hX : Memℒp X 2) :
    Var[X] = 𝔼[X ^ 2] - 𝔼[X] ^ 2 :=
  by
  rw [hX.variance_eq, sub_sq', integral_sub', integral_add']; rotate_left
  · exact hX.integrable_sq
  · convert integrable_const (𝔼[X] ^ 2)
    infer_instance
  · apply hX.integrable_sq.add
    convert integrable_const (𝔼[X] ^ 2)
    infer_instance
  · exact ((hX.integrable one_le_two).const_mul 2).mul_const' _
  simp only [integral_mul_right, Pi.pow_apply, Pi.mul_apply, Pi.bit0_apply, Pi.one_apply,
    integral_const (integral ℙ X ^ 2), integral_mul_left (2 : ℝ), one_mul, variance, Pi.pow_apply,
    measure_univ, Ennreal.one_toReal, Algebra.id.smul_eq_mul]
  ring
#align probability_theory.variance_def' ProbabilityTheory.variance_def'

theorem variance_le_expectation_sq [IsProbabilityMeasure (ℙ : Measure Ω)] {X : Ω → ℝ}
    (hm : AeStronglyMeasurable X ℙ) : Var[X] ≤ 𝔼[X ^ 2] :=
  by
  by_cases hX : mem_ℒp X 2
  · rw [variance_def' hX]
    simp only [sq_nonneg, sub_le_self_iff]
  rw [variance, evariance_eq_lintegral_of_real, ← integral_eq_lintegral_of_nonneg_ae]
  by_cases hint : integrable X; swap
  · simp only [integral_undef hint, Pi.pow_apply, Pi.sub_apply, sub_zero]
  · rw [integral_undef]
    · exact integral_nonneg fun a => sq_nonneg _
    · intro h
      have A : mem_ℒp (X - fun ω : Ω => 𝔼[X]) 2 ℙ :=
        (mem_ℒp_two_iff_integrable_sq
              (hint.ae_strongly_measurable.sub ae_strongly_measurable_const)).2
          h
      have B : mem_ℒp (fun ω : Ω => 𝔼[X]) 2 ℙ := mem_ℒp_const _
      apply hX
      convert A.add B
      simp
  · exact ae_of_all _ fun x => sq_nonneg _
  · exact (AeMeasurable.powConst (hm.ae_measurable.sub_const _) _).AeStronglyMeasurable
#align probability_theory.variance_le_expectation_sq ProbabilityTheory.variance_le_expectation_sq

theorem evariance_def' [IsProbabilityMeasure (ℙ : Measure Ω)] {X : Ω → ℝ}
    (hX : AeStronglyMeasurable X ℙ) : eVar[X] = (∫⁻ ω, ‖X ω‖₊ ^ 2) - Ennreal.ofReal (𝔼[X] ^ 2) :=
  by
  by_cases hℒ : mem_ℒp X 2
  · rw [← hℒ.of_real_variance_eq, variance_def' hℒ, Ennreal.ofReal_sub _ (sq_nonneg _)]
    congr
    simp_rw [← Ennreal.coe_pow]
    rw [lintegral_coe_eq_integral]
    · congr 2 with ω
      simp only [Pi.pow_apply, Nnreal.coe_pow, coe_nnnorm, Real.norm_eq_abs, pow_bit0_abs]
    · exact hℒ.abs.integrable_sq
  · symm
    rw [evariance_eq_top hX hℒ, Ennreal.sub_eq_top_iff]
    refine' ⟨_, Ennreal.ofReal_ne_top⟩
    rw [mem_ℒp, not_and] at hℒ
    specialize hℒ hX
    simp only [snorm_eq_lintegral_rpow_nnnorm Ennreal.two_ne_zero Ennreal.two_ne_top, not_lt,
      top_le_iff, Ennreal.toReal_bit0, Ennreal.one_toReal, Ennreal.rpow_two, one_div,
      Ennreal.rpow_eq_top_iff, inv_lt_zero, inv_pos, zero_lt_bit0, zero_lt_one, and_true_iff,
      or_iff_not_imp_left, not_and_or] at hℒ
    exact hℒ fun _ => zero_le_two
#align probability_theory.evariance_def' ProbabilityTheory.evariance_def'

/-- *Chebyshev's inequality* for `ℝ≥0∞`-valued variance. -/
theorem meas_ge_le_evariance_div_sq {X : Ω → ℝ} (hX : AeStronglyMeasurable X ℙ) {c : ℝ≥0}
    (hc : c ≠ 0) : ℙ { ω | ↑c ≤ |X ω - 𝔼[X]| } ≤ eVar[X] / c ^ 2 :=
  by
  have A : (c : ℝ≥0∞) ≠ 0 := by rwa [Ne.def, Ennreal.coe_eq_zero]
  have B : ae_strongly_measurable (fun ω : Ω => 𝔼[X]) ℙ := ae_strongly_measurable_const
  convert meas_ge_le_mul_pow_snorm ℙ Ennreal.two_ne_zero Ennreal.two_ne_top (hX.sub B) A
  · ext ω
    simp only [Pi.sub_apply, Ennreal.coe_le_coe, ← Real.norm_eq_abs, ← coe_nnnorm,
      Nnreal.coe_le_coe, Ennreal.ofReal_coe_nnreal]
  · rw [snorm_eq_lintegral_rpow_nnnorm Ennreal.two_ne_zero Ennreal.two_ne_top]
    simp only [Ennreal.toReal_bit0, Ennreal.one_toReal, Pi.sub_apply, one_div]
    rw [div_eq_mul_inv, Ennreal.inv_pow, mul_comm, Ennreal.rpow_two]
    congr
    simp_rw [← Ennreal.rpow_mul, inv_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), Ennreal.rpow_two,
      Ennreal.rpow_one, evariance]
#align probability_theory.meas_ge_le_evariance_div_sq ProbabilityTheory.meas_ge_le_evariance_div_sq

/-- *Chebyshev's inequality* : one can control the deviation probability of a real random variable
from its expectation in terms of the variance. -/
theorem meas_ge_le_variance_div_sq [IsFiniteMeasure (ℙ : Measure Ω)] {X : Ω → ℝ} (hX : Memℒp X 2)
    {c : ℝ} (hc : 0 < c) : ℙ { ω | c ≤ |X ω - 𝔼[X]| } ≤ Ennreal.ofReal (Var[X] / c ^ 2) :=
  by
  rw [Ennreal.ofReal_div_of_pos (sq_pos_of_ne_zero _ hc.ne.symm), hX.of_real_variance_eq]
  convert @meas_ge_le_evariance_div_sq _ _ _ hX.1 c.to_nnreal (by simp [hc])
  · simp only [Real.coe_to_nnreal', max_le_iff, abs_nonneg, and_true_iff]
  · rw [Ennreal.ofReal_pow hc.le]
    rfl
#align probability_theory.meas_ge_le_variance_div_sq ProbabilityTheory.meas_ge_le_variance_div_sq

/-- The variance of the sum of two independent random variables is the sum of the variances. -/
theorem IndepFunCat.variance_add [IsProbabilityMeasure (ℙ : Measure Ω)] {X Y : Ω → ℝ}
    (hX : Memℒp X 2) (hY : Memℒp Y 2) (h : IndepFunCat X Y) : Var[X + Y] = Var[X] + Var[Y] :=
  calc
    Var[X + Y] = 𝔼[fun a => X a ^ 2 + Y a ^ 2 + 2 * X a * Y a] - 𝔼[X + Y] ^ 2 := by
      simp [variance_def' (hX.add hY), add_sq']
    _ = 𝔼[X ^ 2] + 𝔼[Y ^ 2] + 2 * 𝔼[X * Y] - (𝔼[X] + 𝔼[Y]) ^ 2 :=
      by
      simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, mul_assoc]
      rw [integral_add, integral_add, integral_add, integral_mul_left]
      · exact hX.integrable one_le_two
      · exact hY.integrable one_le_two
      · exact hX.integrable_sq
      · exact hY.integrable_sq
      · exact hX.integrable_sq.add hY.integrable_sq
      · apply integrable.const_mul
        exact h.integrable_mul (hX.integrable one_le_two) (hY.integrable one_le_two)
    _ = 𝔼[X ^ 2] + 𝔼[Y ^ 2] + 2 * (𝔼[X] * 𝔼[Y]) - (𝔼[X] + 𝔼[Y]) ^ 2 :=
      by
      congr
      exact h.integral_mul_of_integrable (hX.integrable one_le_two) (hY.integrable one_le_two)
    _ = Var[X] + Var[Y] := by
      simp only [variance_def', hX, hY, Pi.pow_apply]
      ring
    
#align probability_theory.indep_fun.variance_add ProbabilityTheory.IndepFunCat.variance_add

/-- The variance of a finite sum of pairwise independent random variables is the sum of the
variances. -/
theorem IndepFunCat.variance_sum [IsProbabilityMeasure (ℙ : Measure Ω)] {ι : Type _} {X : ι → Ω → ℝ}
    {s : Finset ι} (hs : ∀ i ∈ s, Memℒp (X i) 2)
    (h : Set.Pairwise ↑s fun i j => IndepFunCat (X i) (X j)) :
    Var[∑ i in s, X i] = ∑ i in s, Var[X i] := by
  classical
    induction' s using Finset.induction_on with k s ks IH
    · simp only [Finset.sum_empty, variance_zero]
    rw [variance_def' (mem_ℒp_finset_sum' _ hs), sum_insert ks, sum_insert ks]
    simp only [add_sq']
    calc
      𝔼[X k ^ 2 + (∑ i in s, X i) ^ 2 + 2 * X k * ∑ i in s, X i] - 𝔼[X k + ∑ i in s, X i] ^ 2 =
          𝔼[X k ^ 2] + 𝔼[(∑ i in s, X i) ^ 2] + 𝔼[2 * X k * ∑ i in s, X i] -
            (𝔼[X k] + 𝔼[∑ i in s, X i]) ^ 2 :=
        by
        rw [integral_add', integral_add', integral_add']
        · exact mem_ℒp.integrable one_le_two (hs _ (mem_insert_self _ _))
        · apply integrable_finset_sum' _ fun i hi => _
          exact mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi))
        · exact mem_ℒp.integrable_sq (hs _ (mem_insert_self _ _))
        · apply mem_ℒp.integrable_sq
          exact mem_ℒp_finset_sum' _ fun i hi => hs _ (mem_insert_of_mem hi)
        · apply integrable.add
          · exact mem_ℒp.integrable_sq (hs _ (mem_insert_self _ _))
          · apply mem_ℒp.integrable_sq
            exact mem_ℒp_finset_sum' _ fun i hi => hs _ (mem_insert_of_mem hi)
        · rw [mul_assoc]
          apply integrable.const_mul _ (2 : ℝ)
          simp only [mul_sum, sum_apply, Pi.mul_apply]
          apply integrable_finset_sum _ fun i hi => _
          apply
            indep_fun.integrable_mul _ (mem_ℒp.integrable one_le_two (hs _ (mem_insert_self _ _)))
              (mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)))
          apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
          exact fun hki => ks (hki.symm ▸ hi)
      _ =
          Var[X k] + Var[∑ i in s, X i] +
            (𝔼[2 * X k * ∑ i in s, X i] - 2 * 𝔼[X k] * 𝔼[∑ i in s, X i]) :=
        by
        rw [variance_def' (hs _ (mem_insert_self _ _)),
          variance_def' (mem_ℒp_finset_sum' _ fun i hi => hs _ (mem_insert_of_mem hi))]
        ring
      _ = Var[X k] + Var[∑ i in s, X i] :=
        by
        simp only [mul_assoc, integral_mul_left, Pi.mul_apply, Pi.bit0_apply, Pi.one_apply,
          sum_apply, add_right_eq_self, mul_sum]
        rw [integral_finset_sum s fun i hi => _]; swap
        · apply integrable.const_mul _ (2 : ℝ)
          apply
            indep_fun.integrable_mul _ (mem_ℒp.integrable one_le_two (hs _ (mem_insert_self _ _)))
              (mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)))
          apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
          exact fun hki => ks (hki.symm ▸ hi)
        rw [integral_finset_sum s fun i hi =>
            mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)),
          mul_sum, mul_sum, ← sum_sub_distrib]
        apply Finset.sum_eq_zero fun i hi => _
        rw [integral_mul_left, indep_fun.integral_mul', sub_self]
        · apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
          exact fun hki => ks (hki.symm ▸ hi)
        · exact mem_ℒp.ae_strongly_measurable (hs _ (mem_insert_self _ _))
        · exact mem_ℒp.ae_strongly_measurable (hs _ (mem_insert_of_mem hi))
      _ = Var[X k] + ∑ i in s, Var[X i] := by
        rw [IH (fun i hi => hs i (mem_insert_of_mem hi))
            (h.mono (by simp only [coe_insert, Set.subset_insert]))]
      
#align probability_theory.indep_fun.variance_sum ProbabilityTheory.IndepFunCat.variance_sum

end ProbabilityTheory

