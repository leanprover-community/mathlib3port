/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Data.Complex.Determinant
import Mathbin.Data.Complex.IsROrC

/-!
# Normed space structure on `ℂ`.

This file gathers basic facts on complex numbers of an analytic nature.

## Main results

This file registers `ℂ` as a normed field, expresses basic properties of the norm, and gives
tools on the real vector space structure of `ℂ`. Notably, in the namespace `complex`,
it defines functions:

* `re_clm`
* `im_clm`
* `of_real_clm`
* `conj_cle`

They are bundled versions of the real part, the imaginary part, the embedding of `ℝ` in `ℂ`, and
the complex conjugate as continuous `ℝ`-linear maps. The last two are also bundled as linear
isometries in `of_real_li` and `conj_lie`.

We also register the fact that `ℂ` is an `is_R_or_C` field.
-/


noncomputable section

namespace Complex

open ComplexConjugate

instance : HasNorm ℂ :=
  ⟨abs⟩

@[simp]
theorem norm_eq_abs (z : ℂ) : ∥z∥ = abs z :=
  rfl

instance : NormedGroup ℂ :=
  NormedGroup.ofCore ℂ { norm_eq_zero_iff := fun z => abs_eq_zero, triangle := abs_add, norm_neg := abs_neg }

instance : NormedField ℂ :=
  { Complex.field with norm := abs, dist_eq := fun _ _ => rfl, norm_mul' := abs_mul }

instance : NondiscreteNormedField ℂ where
  non_trivial :=
    ⟨2, by
      simp <;> norm_num⟩

instance {R : Type _} [NormedField R] [NormedAlgebra R ℝ] : NormedAlgebra R ℂ where
  norm_smul_le := fun r x => by
    rw [norm_eq_abs, norm_eq_abs, ← algebra_map_smul ℝ r x, Algebra.smul_def, abs_mul, ← norm_algebra_map' ℝ r,
      coe_algebra_map, abs_of_real]
    rfl
  toAlgebra := Complex.algebra

/-- The module structure from `module.complex_to_real` is a normed space. -/
-- see Note [lower instance priority]
instance (priority := 900) _root_.normed_space.complex_to_real {E : Type _} [NormedGroup E] [NormedSpace ℂ E] :
    NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E

theorem dist_eq (z w : ℂ) : dist z w = abs (z - w) :=
  rfl

theorem dist_self_conj (z : ℂ) : dist z (conj z) = 2 * abs z.im := by
  simp only [dist_eq, sub_conj, of_real_mul, of_real_bit0, of_real_one, abs_mul, abs_two, abs_of_real, abs_I, mul_oneₓ]

theorem dist_conj_self (z : ℂ) : dist (conj z) z = 2 * abs z.im := by
  rw [dist_comm, dist_self_conj]

@[simp]
theorem norm_real (r : ℝ) : ∥(r : ℂ)∥ = ∥r∥ :=
  abs_of_real _

@[simp]
theorem norm_rat (r : ℚ) : ∥(r : ℂ)∥ = abs (r : ℝ) := by
  rw [← of_real_rat_cast]
  exact norm_real _

@[simp]
theorem norm_nat (n : ℕ) : ∥(n : ℂ)∥ = n :=
  abs_of_nat _

@[simp]
theorem norm_int {n : ℤ} : ∥(n : ℂ)∥ = abs n := by
  simp (config := { singlePass := true })[← Rat.cast_coe_int]

theorem norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ∥(n : ℂ)∥ = n := by
  simp [hn]

@[continuity]
theorem continuous_abs : Continuous abs :=
  continuous_norm

@[continuity]
theorem continuous_norm_sq : Continuous normSq := by
  simpa [← norm_sq_eq_abs] using continuous_abs.pow 2

@[simp, norm_cast]
theorem nnnorm_real (r : ℝ) : ∥(r : ℂ)∥₊ = ∥r∥₊ :=
  Subtype.ext <| norm_real r

@[simp, norm_cast]
theorem nnnorm_nat (n : ℕ) : ∥(n : ℂ)∥₊ = n :=
  Subtype.ext <| by
    simp

@[simp, norm_cast]
theorem nnnorm_int (n : ℤ) : ∥(n : ℂ)∥₊ = ∥n∥₊ :=
  Subtype.ext <| by
    simp only [coe_nnnorm, norm_int, Int.norm_eq_abs]

theorem nnnorm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ∥ζ∥₊ = 1 := by
  refine' (@pow_left_inj Nnreal _ _ _ _ zero_le' zero_le' hn.bot_lt).mp _
  rw [← nnnorm_pow, h, nnnorm_one, one_pow]

theorem norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ∥ζ∥ = 1 :=
  congr_argₓ coe (nnnorm_eq_one_of_pow_eq_one h hn)

/-- The `abs` function on `ℂ` is proper. -/
theorem tendsto_abs_cocompact_at_top : Filter.Tendsto abs (Filter.cocompact ℂ) Filter.atTop :=
  tendsto_norm_cocompact_at_top

/-- The `norm_sq` function on `ℂ` is proper. -/
theorem tendsto_norm_sq_cocompact_at_top : Filter.Tendsto normSq (Filter.cocompact ℂ) Filter.atTop := by
  simpa [mul_self_abs] using tendsto_abs_cocompact_at_top.at_top_mul_at_top tendsto_abs_cocompact_at_top

open ContinuousLinearMap

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reClm : ℂ →L[ℝ] ℝ :=
  reLm.mkContinuous 1 fun x => by
    simp [Real.norm_eq_abs, abs_re_le_abs]

@[continuity]
theorem continuous_re : Continuous re :=
  reClm.Continuous

@[simp]
theorem re_clm_coe : (coe reClm : ℂ →ₗ[ℝ] ℝ) = re_lm :=
  rfl

@[simp]
theorem re_clm_apply (z : ℂ) : (reClm : ℂ → ℝ) z = z.re :=
  rfl

@[simp]
theorem re_clm_norm : ∥re_clm∥ = 1 :=
  le_antisymmₓ (LinearMap.mk_continuous_norm_le _ zero_le_one _) <|
    calc
      1 = ∥reClm 1∥ := by
        simp
      _ ≤ ∥re_clm∥ :=
        unit_le_op_norm _ _
          (by
            simp )
      

@[simp]
theorem re_clm_nnnorm : ∥re_clm∥₊ = 1 :=
  Subtype.ext re_clm_norm

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def imClm : ℂ →L[ℝ] ℝ :=
  imLm.mkContinuous 1 fun x => by
    simp [Real.norm_eq_abs, abs_im_le_abs]

@[continuity]
theorem continuous_im : Continuous im :=
  imClm.Continuous

@[simp]
theorem im_clm_coe : (coe imClm : ℂ →ₗ[ℝ] ℝ) = im_lm :=
  rfl

@[simp]
theorem im_clm_apply (z : ℂ) : (imClm : ℂ → ℝ) z = z.im :=
  rfl

@[simp]
theorem im_clm_norm : ∥im_clm∥ = 1 :=
  le_antisymmₓ (LinearMap.mk_continuous_norm_le _ zero_le_one _) <|
    calc
      1 = ∥imClm i∥ := by
        simp
      _ ≤ ∥im_clm∥ :=
        unit_le_op_norm _ _
          (by
            simp )
      

@[simp]
theorem im_clm_nnnorm : ∥im_clm∥₊ = 1 :=
  Subtype.ext im_clm_norm

theorem restrict_scalars_one_smul_right' {E : Type _} [NormedGroup E] [NormedSpace ℂ E] (x : E) :
    ContinuousLinearMap.restrictScalars ℝ ((1 : ℂ →L[ℂ] ℂ).smul_right x : ℂ →L[ℂ] E) =
      reClm.smul_right x + I • imClm.smul_right x :=
  by
  ext ⟨a, b⟩
  simp [mk_eq_add_mul_I, add_smul, mul_smul, smul_comm I]

theorem restrict_scalars_one_smul_right (x : ℂ) :
    ContinuousLinearMap.restrictScalars ℝ ((1 : ℂ →L[ℂ] ℂ).smul_right x : ℂ →L[ℂ] ℂ) = x • 1 := by
  ext1 z
  dsimp
  apply mul_comm

/-- The complex-conjugation function from `ℂ` to itself is an isometric linear equivalence. -/
def conjLie : ℂ ≃ₗᵢ[ℝ] ℂ :=
  ⟨conjAe.toLinearEquiv, abs_conj⟩

@[simp]
theorem conj_lie_apply (z : ℂ) : conjLie z = conj z :=
  rfl

@[simp]
theorem conj_lie_symm : conjLie.symm = conj_lie :=
  rfl

theorem isometry_conj : Isometry (conj : ℂ → ℂ) :=
  conjLie.Isometry

@[simp]
theorem dist_conj_conj (z w : ℂ) : dist (conj z) (conj w) = dist z w :=
  isometry_conj.dist_eq z w

@[simp]
theorem nndist_conj_conj (z w : ℂ) : nndist (conj z) (conj w) = nndist z w :=
  isometry_conj.nndist_eq z w

theorem dist_conj_comm (z w : ℂ) : dist (conj z) w = dist z (conj w) := by
  rw [← dist_conj_conj, conj_conj]

theorem nndist_conj_comm (z w : ℂ) : nndist (conj z) w = nndist z (conj w) :=
  Subtype.ext <| dist_conj_comm _ _

/-- The determinant of `conj_lie`, as a linear map. -/
@[simp]
theorem det_conj_lie : (conjLie.toLinearEquiv : ℂ →ₗ[ℝ] ℂ).det = -1 :=
  det_conj_ae

/-- The determinant of `conj_lie`, as a linear equiv. -/
@[simp]
theorem linear_equiv_det_conj_lie : conjLie.toLinearEquiv.det = -1 :=
  linear_equiv_det_conj_ae

@[continuity]
theorem continuous_conj : Continuous (conj : ℂ → ℂ) :=
  conjLie.Continuous

/-- Continuous linear equiv version of the conj function, from `ℂ` to `ℂ`. -/
def conjCle : ℂ ≃L[ℝ] ℂ :=
  conj_lie

@[simp]
theorem conj_cle_coe : conjCle.toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[simp]
theorem conj_cle_apply (z : ℂ) : conjCle z = conj z :=
  rfl

@[simp]
theorem conj_cle_norm : ∥(conjCle : ℂ →L[ℝ] ℂ)∥ = 1 :=
  conjLie.toLinearIsometry.norm_to_continuous_linear_map

@[simp]
theorem conj_cle_nnorm : ∥(conjCle : ℂ →L[ℝ] ℂ)∥₊ = 1 :=
  Subtype.ext conj_cle_norm

/-- Linear isometry version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealLi : ℝ →ₗᵢ[ℝ] ℂ :=
  ⟨ofRealAm.toLinearMap, norm_real⟩

theorem isometry_of_real : Isometry (coe : ℝ → ℂ) :=
  ofRealLi.Isometry

@[continuity]
theorem continuous_of_real : Continuous (coe : ℝ → ℂ) :=
  ofRealLi.Continuous

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealClm : ℝ →L[ℝ] ℂ :=
  ofRealLi.toContinuousLinearMap

@[simp]
theorem of_real_clm_coe : (ofRealClm : ℝ →ₗ[ℝ] ℂ) = ofRealAm.toLinearMap :=
  rfl

@[simp]
theorem of_real_clm_apply (x : ℝ) : ofRealClm x = x :=
  rfl

@[simp]
theorem of_real_clm_norm : ∥of_real_clm∥ = 1 :=
  ofRealLi.norm_to_continuous_linear_map

@[simp]
theorem of_real_clm_nnnorm : ∥of_real_clm∥₊ = 1 :=
  Subtype.ext <| of_real_clm_norm

noncomputable instance : IsROrC ℂ where
  re := ⟨Complex.re, Complex.zero_re, Complex.add_re⟩
  im := ⟨Complex.im, Complex.zero_im, Complex.add_im⟩
  i := Complex.i
  I_re_ax := by
    simp only [AddMonoidHom.coe_mk, Complex.I_re]
  I_mul_I_ax := by
    simp only [Complex.I_mul_I, eq_self_iff_true, or_trueₓ]
  re_add_im_ax := fun z => by
    simp only [AddMonoidHom.coe_mk, Complex.re_add_im, Complex.coe_algebra_map, Complex.of_real_eq_coe]
  of_real_re_ax := fun r => by
    simp only [AddMonoidHom.coe_mk, Complex.of_real_re, Complex.coe_algebra_map, Complex.of_real_eq_coe]
  of_real_im_ax := fun r => by
    simp only [AddMonoidHom.coe_mk, Complex.of_real_im, Complex.coe_algebra_map, Complex.of_real_eq_coe]
  mul_re_ax := fun z w => by
    simp only [Complex.mul_re, AddMonoidHom.coe_mk]
  mul_im_ax := fun z w => by
    simp only [AddMonoidHom.coe_mk, Complex.mul_im]
  conj_re_ax := fun z => rfl
  conj_im_ax := fun z => rfl
  conj_I_ax := by
    simp only [Complex.conj_I, RingHom.coe_mk]
  norm_sq_eq_def_ax := fun z => by
    simp only [← Complex.norm_sq_eq_abs, ← Complex.norm_sq_apply, AddMonoidHom.coe_mk, Complex.norm_eq_abs]
  mul_im_I_ax := fun z => by
    simp only [mul_oneₓ, AddMonoidHom.coe_mk, Complex.I_im]
  inv_def_ax := fun z => by
    simp only [Complex.inv_def, Complex.norm_sq_eq_abs, Complex.coe_algebra_map, Complex.of_real_eq_coe,
      Complex.norm_eq_abs]
  div_I_ax := Complex.div_I

theorem _root_.is_R_or_C.re_eq_complex_re : ⇑(IsROrC.re : ℂ →+ ℝ) = Complex.re :=
  rfl

theorem _root_.is_R_or_C.im_eq_complex_im : ⇑(IsROrC.im : ℂ →+ ℝ) = Complex.im :=
  rfl

section

variable {α β γ : Type _} [AddCommMonoidₓ α] [TopologicalSpace α] [AddCommMonoidₓ γ] [TopologicalSpace γ]

/-- The natural `add_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdAddHom : ℂ ≃+ ℝ × ℝ :=
  { equivRealProd with
    map_add' := by
      simp }

/-- The natural `linear_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdAddHomLm : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  { equivRealProdAddHom with
    map_smul' := by
      simp [equiv_real_prod_add_hom] }

/-- The natural `continuous_linear_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdₗ : ℂ ≃L[ℝ] ℝ × ℝ :=
  equivRealProdAddHomLm.toContinuousLinearEquiv

end

theorem has_sum_iff {α} (f : α → ℂ) (c : ℂ) :
    HasSum f c ↔ HasSum (fun x => (f x).re) c.re ∧ HasSum (fun x => (f x).im) c.im := by
  -- For some reason, `continuous_linear_map.has_sum` is orders of magnitude faster than
  -- `has_sum.mapL` here:
  refine' ⟨fun h => ⟨re_clm.has_sum h, im_clm.has_sum h⟩, _⟩
  rintro ⟨h₁, h₂⟩
  convert (h₁.prod_mk h₂).mapL equiv_real_prodₗ.symm.to_continuous_linear_map
  · ext x <;> rfl
    
  · cases c
    rfl
    

end Complex

namespace IsROrC

-- mathport name: «exprreC»
local notation "reC" => @IsROrC.re ℂ _

-- mathport name: «exprimC»
local notation "imC" => @IsROrC.im ℂ _

-- mathport name: «exprIC»
local notation "IC" => @IsROrC.i ℂ _

-- mathport name: «exprabsC»
local notation "absC" => @IsROrC.abs ℂ _

-- mathport name: «exprnorm_sqC»
local notation "norm_sqC" => @IsROrC.normSq ℂ _

@[simp]
theorem re_to_complex {x : ℂ} : reC x = x.re :=
  rfl

@[simp]
theorem im_to_complex {x : ℂ} : imC x = x.im :=
  rfl

@[simp]
theorem I_to_complex : IC = Complex.i :=
  rfl

@[simp]
theorem norm_sq_to_complex {x : ℂ} : norm_sqC x = Complex.normSq x := by
  simp [IsROrC.normSq, Complex.normSq]

@[simp]
theorem abs_to_complex {x : ℂ} : absC x = Complex.abs x := by
  simp [IsROrC.abs, Complex.abs]

end IsROrC

