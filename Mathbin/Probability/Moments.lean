/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.Probability.Variance

/-!
# Moments and moment generating function

## Main definitions

* `moment X p μ`: `p`th moment of a real random variable `X` with respect to measure `μ`, `μ[X^p]`
* `central_moment X p μ`:`p`th central moment of `X` with respect to measure `μ`, `μ[(X - μ[X])^p]`
* `mgf X μ t`: moment generating function of `X` with respect to measure `μ`, `μ[exp(t*X)]`
* `cgf X μ t`: cumulant generating function, logarithm of the moment generating function

## Main results

* `indep_fun.mgf_add`: if two real random variables `X` and `Y` are independent and their mgf are
  defined at `t`, then `mgf (X + Y) μ t = mgf X μ t * mgf Y μ t`
* `indep_fun.cgf_add`: if two real random variables `X` and `Y` are independent and their mgf are
  defined at `t`, then `cgf (X + Y) μ t = cgf X μ t + cgf Y μ t`

-/


open MeasureTheory Filter Finset

noncomputable section

open BigOperators MeasureTheory ProbabilityTheory Ennreal Nnreal

namespace ProbabilityTheory

variable {Ω : Type _} {m : MeasurableSpace Ω} {X : Ω → ℝ} {p : ℕ} {μ : Measureₓ Ω}

include m

/-- Moment of a real random variable, `μ[X ^ p]`. -/
def moment (X : Ω → ℝ) (p : ℕ) (μ : Measureₓ Ω) : ℝ :=
  μ[X ^ p]

/-- Central moment of a real random variable, `μ[(X - μ[X]) ^ p]`. -/
def centralMoment (X : Ω → ℝ) (p : ℕ) (μ : Measureₓ Ω) : ℝ :=
  μ[(X - fun x => μ[X]) ^ p]

@[simp]
theorem moment_zero (hp : p ≠ 0) : moment 0 p μ = 0 := by
  simp only [← moment, ← hp, ← zero_pow', ← Ne.def, ← not_false_iff, ← Pi.zero_apply, ← integral_const, ←
    Algebra.id.smul_eq_mul, ← mul_zero]

@[simp]
theorem central_moment_zero (hp : p ≠ 0) : centralMoment 0 p μ = 0 := by
  simp only [← central_moment, ← hp, ← Pi.zero_apply, ← integral_const, ← Algebra.id.smul_eq_mul, ← mul_zero, ←
    zero_sub, ← Pi.pow_apply, ← Pi.neg_apply, ← neg_zero', ← zero_pow', ← Ne.def, ← not_false_iff]

theorem central_moment_one' [IsFiniteMeasure μ] (h_int : Integrable X μ) :
    centralMoment X 1 μ = (1 - (μ Set.Univ).toReal) * μ[X] := by
  simp only [← central_moment, ← Pi.sub_apply, ← pow_oneₓ]
  rw [integral_sub h_int (integrable_const _)]
  simp only [← sub_mul, ← integral_const, ← Algebra.id.smul_eq_mul, ← one_mulₓ]

@[simp]
theorem central_moment_one [IsProbabilityMeasure μ] : centralMoment X 1 μ = 0 := by
  by_cases' h_int : integrable X μ
  · rw [central_moment_one' h_int]
    simp only [← measure_univ, ← Ennreal.one_to_real, ← sub_self, ← zero_mul]
    
  · simp only [← central_moment, ← Pi.sub_apply, ← pow_oneₓ]
    have : ¬integrable (fun x => X x - integral μ X) μ := by
      refine' fun h_sub => h_int _
      have h_add : X = (fun x => X x - integral μ X) + fun x => integral μ X := by
        ext1 x
        simp
      rw [h_add]
      exact h_sub.add (integrable_const _)
    rw [integral_undef this]
    

@[simp]
theorem central_moment_two_eq_variance : centralMoment X 2 μ = variance X μ :=
  rfl

section MomentGeneratingFunction

variable {t : ℝ}

/-- Moment generating function of a real random variable `X`: `λ t, μ[exp(t*X)]`. -/
def mgf (X : Ω → ℝ) (μ : Measureₓ Ω) (t : ℝ) : ℝ :=
  μ[fun ω => Real.exp (t * X ω)]

/-- Cumulant generating function of a real random variable `X`: `λ t, log μ[exp(t*X)]`. -/
def cgf (X : Ω → ℝ) (μ : Measureₓ Ω) (t : ℝ) : ℝ :=
  Real.log (mgf X μ t)

@[simp]
theorem mgf_zero_fun : mgf 0 μ t = (μ Set.Univ).toReal := by
  simp only [← mgf, ← Pi.zero_apply, ← mul_zero, ← Real.exp_zero, ← integral_const, ← Algebra.id.smul_eq_mul, ←
    mul_oneₓ]

@[simp]
theorem cgf_zero_fun : cgf 0 μ t = Real.log (μ Set.Univ).toReal := by
  simp only [← cgf, ← mgf_zero_fun]

@[simp]
theorem mgf_zero_measure : mgf X (0 : Measureₓ Ω) t = 0 := by
  simp only [← mgf, ← integral_zero_measure]

@[simp]
theorem cgf_zero_measure : cgf X (0 : Measureₓ Ω) t = 0 := by
  simp only [← cgf, ← Real.log_zero, ← mgf_zero_measure]

@[simp]
theorem mgf_const' (c : ℝ) : mgf (fun _ => c) μ t = (μ Set.Univ).toReal * Real.exp (t * c) := by
  simp only [← mgf, ← integral_const, ← Algebra.id.smul_eq_mul]

@[simp]
theorem mgf_const (c : ℝ) [IsProbabilityMeasure μ] : mgf (fun _ => c) μ t = Real.exp (t * c) := by
  simp only [← mgf_const', ← measure_univ, ← Ennreal.one_to_real, ← one_mulₓ]

@[simp]
theorem cgf_const' [IsFiniteMeasure μ] (hμ : μ ≠ 0) (c : ℝ) :
    cgf (fun _ => c) μ t = Real.log (μ Set.Univ).toReal + t * c := by
  simp only [← cgf, ← mgf_const']
  rw [Real.log_mul _ (Real.exp_pos _).ne']
  · rw [Real.log_exp _]
    
  · rw [Ne.def, Ennreal.to_real_eq_zero_iff, measure.measure_univ_eq_zero]
    simp only [← hμ, ← measure_ne_top μ Set.Univ, ← or_selfₓ, ← not_false_iff]
    

@[simp]
theorem cgf_const [IsProbabilityMeasure μ] (c : ℝ) : cgf (fun _ => c) μ t = t * c := by
  simp only [← cgf, ← mgf_const, ← Real.log_exp]

@[simp]
theorem mgf_zero' : mgf X μ 0 = (μ Set.Univ).toReal := by
  simp only [← mgf, ← zero_mul, ← Real.exp_zero, ← integral_const, ← Algebra.id.smul_eq_mul, ← mul_oneₓ]

@[simp]
theorem mgf_zero [IsProbabilityMeasure μ] : mgf X μ 0 = 1 := by
  simp only [← mgf_zero', ← measure_univ, ← Ennreal.one_to_real]

@[simp]
theorem cgf_zero' : cgf X μ 0 = Real.log (μ Set.Univ).toReal := by
  simp only [← cgf, ← mgf_zero']

@[simp]
theorem cgf_zero [IsProbabilityMeasure μ] : cgf X μ 0 = 0 := by
  simp only [← cgf_zero', ← measure_univ, ← Ennreal.one_to_real, ← Real.log_one]

theorem mgf_undef (hX : ¬Integrable (fun ω => Real.exp (t * X ω)) μ) : mgf X μ t = 0 := by
  simp only [← mgf, ← integral_undef hX]

theorem cgf_undef (hX : ¬Integrable (fun ω => Real.exp (t * X ω)) μ) : cgf X μ t = 0 := by
  simp only [← cgf, ← mgf_undef hX, ← Real.log_zero]

theorem mgf_nonneg : 0 ≤ mgf X μ t := by
  refine' integral_nonneg _
  intro ω
  simp only [← Pi.zero_apply]
  exact (Real.exp_pos _).le

theorem mgf_pos' (hμ : μ ≠ 0) (h_int_X : Integrable (fun ω => Real.exp (t * X ω)) μ) : 0 < mgf X μ t := by
  simp_rw [mgf]
  have : (∫ x : Ω, Real.exp (t * X x) ∂μ) = ∫ x : Ω in Set.Univ, Real.exp (t * X x) ∂μ := by
    simp only [← measure.restrict_univ]
  rw [this, set_integral_pos_iff_support_of_nonneg_ae _ _]
  · have h_eq_univ : (Function.Support fun x : Ω => Real.exp (t * X x)) = Set.Univ := by
      ext1 x
      simp only [← Function.mem_support, ← Set.mem_univ, ← iff_trueₓ]
      exact (Real.exp_pos _).ne'
    rw [h_eq_univ, Set.inter_univ _]
    refine' Ne.bot_lt _
    simp only [← hμ, ← Ennreal.bot_eq_zero, ← Ne.def, ← measure.measure_univ_eq_zero, ← not_false_iff]
    
  · refine' eventually_of_forall fun x => _
    rw [Pi.zero_apply]
    exact (Real.exp_pos _).le
    
  · rwa [integrable_on_univ]
    

theorem mgf_pos [IsProbabilityMeasure μ] (h_int_X : Integrable (fun ω => Real.exp (t * X ω)) μ) : 0 < mgf X μ t :=
  mgf_pos' (IsProbabilityMeasure.ne_zero μ) h_int_X

theorem IndepFunₓ.mgf_add {X Y : Ω → ℝ} (h_indep : IndepFunₓ X Y μ)
    (h_int_X : Integrable (fun ω => Real.exp (t * X ω)) μ) (h_int_Y : Integrable (fun ω => Real.exp (t * Y ω)) μ) :
    mgf (X + Y) μ t = mgf X μ t * mgf Y μ t := by
  simp_rw [mgf, Pi.add_apply, mul_addₓ, Real.exp_add]
  refine' indep_fun.integral_mul_of_integrable' _ h_int_X h_int_Y
  have h_meas : Measurable fun x => Real.exp (t * x) := (measurable_id'.const_mul t).exp
  change indep_fun ((fun x => Real.exp (t * x)) ∘ X) ((fun x => Real.exp (t * x)) ∘ Y) μ
  exact indep_fun.comp h_indep h_meas h_meas

theorem IndepFunₓ.cgf_add {X Y : Ω → ℝ} (h_indep : IndepFunₓ X Y μ)
    (h_int_X : Integrable (fun ω => Real.exp (t * X ω)) μ) (h_int_Y : Integrable (fun ω => Real.exp (t * Y ω)) μ) :
    cgf (X + Y) μ t = cgf X μ t + cgf Y μ t := by
  by_cases' hμ : μ = 0
  · simp [← hμ]
    
  simp only [← cgf, ← h_indep.mgf_add h_int_X h_int_Y]
  exact Real.log_mul (mgf_pos' hμ h_int_X).ne' (mgf_pos' hμ h_int_Y).ne'

end MomentGeneratingFunction

end ProbabilityTheory

