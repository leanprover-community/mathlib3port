/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Probability.Notation
import Mathbin.Probability.Integration

/-!
# Variance of random variables

We define the variance of a real-valued random variable as `Var[X] = 𝔼[(X - 𝔼[X])^2]` (in the
`probability_theory` locale).

We prove the basic properties of the variance:
* `variance_le_expectation_sq`: the inequality `Var[X] ≤ 𝔼[X^2]`.
* `meas_ge_le_variance_div_sq`: Chebyshev's inequality, i.e.,
      `ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ennreal.of_real (Var[X] / c ^ 2)`.
* `indep_fun.variance_add`: the variance of the sum of two independent random variables is the sum
  of the variances.
* `indep_fun.variance_sum`: the variance of a finite sum of pairwise independent random variables is
  the sum of the variances.
-/


open MeasureTheory Filter Finset

noncomputable section

open BigOperators MeasureTheory ProbabilityTheory Ennreal Nnreal

namespace ProbabilityTheory

/-- The variance of a random variable is `𝔼[X^2] - 𝔼[X]^2` or, equivalently, `𝔼[(X - 𝔼[X])^2]`. We
use the latter as the definition, to ensure better behavior even in garbage situations. -/
def variance {Ω : Type _} {m : MeasurableSpace Ω} (f : Ω → ℝ) (μ : Measureₓ Ω) : ℝ :=
  μ[(f - fun ω => μ[f]) ^ 2]

@[simp]
theorem variance_zero {Ω : Type _} {m : MeasurableSpace Ω} (μ : Measureₓ Ω) : variance 0 μ = 0 := by
  simp [variance]

theorem variance_nonneg {Ω : Type _} {m : MeasurableSpace Ω} (f : Ω → ℝ) (μ : Measureₓ Ω) : 0 ≤ variance f μ :=
  integral_nonneg fun ω => sq_nonneg _

theorem variance_mul {Ω : Type _} {m : MeasurableSpace Ω} (c : ℝ) (f : Ω → ℝ) (μ : Measureₓ Ω) :
    variance (fun ω => c * f ω) μ = c ^ 2 * variance f μ :=
  calc
    variance (fun ω => c * f ω) μ = ∫ x, (c * f x - ∫ y, c * f y ∂μ) ^ 2 ∂μ := rfl
    _ = ∫ x, (c * (f x - ∫ y, f y ∂μ)) ^ 2 ∂μ := by
      congr 1 with x
      simp_rw [integral_mul_left, mul_sub]
    _ = c ^ 2 * variance f μ := by
      simp_rw [mul_powₓ, integral_mul_left]
      rfl
    

theorem variance_smul {Ω : Type _} {m : MeasurableSpace Ω} (c : ℝ) (f : Ω → ℝ) (μ : Measureₓ Ω) :
    variance (c • f) μ = c ^ 2 * variance f μ :=
  variance_mul c f μ

theorem variance_smul' {A : Type _} [CommSemiringₓ A] [Algebra A ℝ] {Ω : Type _} {m : MeasurableSpace Ω} (c : A)
    (f : Ω → ℝ) (μ : Measureₓ Ω) : variance (c • f) μ = c ^ 2 • variance f μ := by
  convert variance_smul (algebraMap A ℝ c) f μ
  · ext1 x
    simp only [algebra_map_smul]
    
  · simp only [Algebra.smul_def, map_pow]
    

-- mathport name: «exprVar[ ]»
localized [ProbabilityTheory] notation "Var[" X "]" => ProbabilityTheory.variance X MeasureTheory.MeasureSpace.volume

variable {Ω : Type _} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measureₓ Ω)]

theorem variance_def' {X : Ω → ℝ} (hX : Memℒp X 2) : Var[X] = 𝔼[X ^ 2] - 𝔼[X] ^ 2 := by
  rw [variance, sub_sq', integral_sub', integral_add']
  rotate_left
  · exact hX.integrable_sq
    
  · convert integrable_const (𝔼[X] ^ 2)
    infer_instance
    
  · apply hX.integrable_sq.add
    convert integrable_const (𝔼[X] ^ 2)
    infer_instance
    
  · exact ((hX.integrable one_le_two).const_mul 2).mul_const' _
    
  simp only [integral_mul_right, Pi.pow_apply, Pi.mul_apply, Pi.bit0_apply, Pi.one_apply,
    integral_const (integral ℙ X ^ 2), integral_mul_left (2 : ℝ), one_mulₓ, variance, Pi.pow_apply, measure_univ,
    Ennreal.one_to_real, Algebra.id.smul_eq_mul]
  ring

theorem variance_le_expectation_sq {X : Ω → ℝ} : Var[X] ≤ 𝔼[X ^ 2] := by
  by_cases' h_int : integrable X
  swap
  · simp only [variance, integral_undef h_int, Pi.pow_apply, Pi.sub_apply, sub_zero]
    
  by_cases' hX : mem_ℒp X 2
  · rw [variance_def' hX]
    simp only [sq_nonneg, sub_le_self_iff]
    
  · rw [variance, integral_undef]
    · exact integral_nonneg fun a => sq_nonneg _
      
    · intro h
      have A : mem_ℒp (X - fun ω : Ω => 𝔼[X]) 2 ℙ :=
        (mem_ℒp_two_iff_integrable_sq (h_int.ae_strongly_measurable.sub ae_strongly_measurable_const)).2 h
      have B : mem_ℒp (fun ω : Ω => 𝔼[X]) 2 ℙ := mem_ℒp_const _
      apply hX
      convert A.add B
      simp
      
    

/-- *Chebyshev's inequality* : one can control the deviation probability of a real random variable
from its expectation in terms of the variance. -/
theorem meas_ge_le_variance_div_sq {X : Ω → ℝ} (hX : Memℒp X 2) {c : ℝ} (hc : 0 < c) :
    ℙ { ω | c ≤ abs (X ω - 𝔼[X]) } ≤ Ennreal.ofReal (Var[X] / c ^ 2) := by
  have A : (Ennreal.ofReal c : ℝ≥0∞) ≠ 0 := by
    simp only [hc, Ne.def, Ennreal.of_real_eq_zero, not_leₓ]
  have B : ae_strongly_measurable (fun ω : Ω => 𝔼[X]) ℙ := ae_strongly_measurable_const
  convert meas_ge_le_mul_pow_snorm ℙ Ennreal.two_ne_zero Ennreal.two_ne_top (hX.ae_strongly_measurable.sub B) A
  · ext ω
    set d : ℝ≥0 := ⟨c, hc.le⟩ with hd
    have cd : c = d := by
      simp only [Subtype.coe_mk]
    simp only [Pi.sub_apply, Ennreal.coe_le_coe, ← Real.norm_eq_abs, ← coe_nnnorm, Nnreal.coe_le_coe, cd,
      Ennreal.of_real_coe_nnreal]
    
  · rw [(hX.sub (mem_ℒp_const _)).snorm_eq_integral_rpow_norm Ennreal.two_ne_zero Ennreal.two_ne_top]
    simp only [Pi.sub_apply, Ennreal.to_real_bit0, Ennreal.one_to_real]
    rw [Ennreal.of_real_rpow_of_nonneg _ zero_le_two]
    rotate_left
    · apply Real.rpow_nonneg_of_nonneg
      exact integral_nonneg fun x => Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
      
    rw [variance, ← Real.rpow_mul, inv_mul_cancel]
    rotate_left
    · exact two_ne_zero
      
    · exact integral_nonneg fun x => Real.rpow_nonneg_of_nonneg (norm_nonneg _) _
      
    simp only [Pi.pow_apply, Pi.sub_apply, Real.rpow_two, Real.rpow_one, Real.norm_eq_abs, pow_bit0_abs,
      Ennreal.of_real_inv_of_pos hc, Ennreal.rpow_two]
    rw [← Ennreal.of_real_pow (inv_nonneg.2 hc.le), ← Ennreal.of_real_mul (sq_nonneg _), div_eq_inv_mul, inv_pow]
    

/-- The variance of the sum of two independent random variables is the sum of the variances. -/
theorem IndepFunₓ.variance_add {X Y : Ω → ℝ} (hX : Memℒp X 2) (hY : Memℒp Y 2) (h : IndepFunₓ X Y) :
    Var[X + Y] = Var[X] + Var[Y] :=
  calc
    Var[X + Y] = 𝔼[fun a => X a ^ 2 + Y a ^ 2 + 2 * X a * Y a] - 𝔼[X + Y] ^ 2 := by
      simp [variance_def' (hX.add hY), add_sq']
    _ = 𝔼[X ^ 2] + 𝔼[Y ^ 2] + 2 * 𝔼[X * Y] - (𝔼[X] + 𝔼[Y]) ^ 2 := by
      simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, mul_assoc]
      rw [integral_add, integral_add, integral_add, integral_mul_left]
      · exact hX.integrable one_le_two
        
      · exact hY.integrable one_le_two
        
      · exact hX.integrable_sq
        
      · exact hY.integrable_sq
        
      · exact hX.integrable_sq.add hY.integrable_sq
        
      · apply integrable.const_mul
        exact h.integrable_mul (hX.integrable one_le_two) (hY.integrable one_le_two)
        
    _ = 𝔼[X ^ 2] + 𝔼[Y ^ 2] + 2 * (𝔼[X] * 𝔼[Y]) - (𝔼[X] + 𝔼[Y]) ^ 2 := by
      congr
      exact h.integral_mul_of_integrable (hX.integrable one_le_two) (hY.integrable one_le_two)
    _ = Var[X] + Var[Y] := by
      simp only [variance_def', hX, hY, Pi.pow_apply]
      ring
    

/-- The variance of a finite sum of pairwise independent random variables is the sum of the
variances. -/
theorem IndepFunₓ.variance_sum {ι : Type _} {X : ι → Ω → ℝ} {s : Finset ι} (hs : ∀ i ∈ s, Memℒp (X i) 2)
    (h : Set.Pairwise ↑s fun i j => IndepFunₓ (X i) (X j)) : Var[∑ i in s, X i] = ∑ i in s, Var[X i] := by
  classical
  induction' s using Finset.induction_on with k s ks IH
  · simp only [Finset.sum_empty, variance_zero]
    
  rw [variance_def' (mem_ℒp_finset_sum' _ hs), sum_insert ks, sum_insert ks]
  simp only [add_sq']
  calc
    𝔼[X k ^ 2 + (∑ i in s, X i) ^ 2 + 2 * X k * ∑ i in s, X i] - 𝔼[X k + ∑ i in s, X i] ^ 2 =
        𝔼[X k ^ 2] + 𝔼[(∑ i in s, X i) ^ 2] + 𝔼[2 * X k * ∑ i in s, X i] - (𝔼[X k] + 𝔼[∑ i in s, X i]) ^ 2 :=
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
        apply integrable.const_mul _ 2
        simp only [mul_sum, sum_apply, Pi.mul_apply]
        apply integrable_finset_sum _ fun i hi => _
        apply
          indep_fun.integrable_mul _ (mem_ℒp.integrable one_le_two (hs _ (mem_insert_self _ _)))
            (mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)))
        apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
        exact fun hki => ks (hki.symm ▸ hi)
        
    _ = Var[X k] + Var[∑ i in s, X i] + (𝔼[2 * X k * ∑ i in s, X i] - 2 * 𝔼[X k] * 𝔼[∑ i in s, X i]) := by
      rw [variance_def' (hs _ (mem_insert_self _ _)),
        variance_def' (mem_ℒp_finset_sum' _ fun i hi => hs _ (mem_insert_of_mem hi))]
      ring
    _ = Var[X k] + Var[∑ i in s, X i] := by
      simp only [mul_assoc, integral_mul_left, Pi.mul_apply, Pi.bit0_apply, Pi.one_apply, sum_apply, add_right_eq_selfₓ,
        mul_sum]
      rw [integral_finset_sum s fun i hi => _]
      swap
      · apply integrable.const_mul _ 2
        apply
          indep_fun.integrable_mul _ (mem_ℒp.integrable one_le_two (hs _ (mem_insert_self _ _)))
            (mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)))
        apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
        exact fun hki => ks (hki.symm ▸ hi)
        
      rw [integral_finset_sum s fun i hi => mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)), mul_sum,
        mul_sum, ← sum_sub_distrib]
      apply Finset.sum_eq_zero fun i hi => _
      rw [integral_mul_left, indep_fun.integral_mul_of_integrable', sub_self]
      · apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
        exact fun hki => ks (hki.symm ▸ hi)
        
      · exact mem_ℒp.integrable one_le_two (hs _ (mem_insert_self _ _))
        
      · exact mem_ℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi))
        
    _ = Var[X k] + ∑ i in s, Var[X i] := by
      rw
        [IH (fun i hi => hs i (mem_insert_of_mem hi))
          (h.mono
            (by
              simp only [coe_insert, Set.subset_insert]))]
    

end ProbabilityTheory

