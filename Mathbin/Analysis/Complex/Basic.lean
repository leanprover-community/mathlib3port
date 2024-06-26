/-
Copyright (c) Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Data.Complex.Module
import Data.Complex.Exponential
import Analysis.RCLike.Basic
import Topology.Algebra.InfiniteSum.Module
import Topology.Instances.RealVectorSpace

#align_import analysis.complex.basic from "leanprover-community/mathlib"@"2ed2c6310e6f1c5562bdf6bfbda55ebbf6891abe"

/-!
# Normed space structure on `ℂ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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


assert_not_exists Absorbs

noncomputable section

namespace Complex

open scoped ComplexConjugate Topology

instance : Norm ℂ :=
  ⟨abs⟩

#print Complex.norm_eq_abs /-
@[simp]
theorem norm_eq_abs (z : ℂ) : ‖z‖ = abs z :=
  rfl
#align complex.norm_eq_abs Complex.norm_eq_abs
-/

#print Complex.norm_exp_ofReal_mul_I /-
theorem norm_exp_ofReal_mul_I (t : ℝ) : ‖exp (t * I)‖ = 1 := by
  simp only [norm_eq_abs, abs_exp_of_real_mul_I]
#align complex.norm_exp_of_real_mul_I Complex.norm_exp_ofReal_mul_I
-/

instance : NormedAddCommGroup ℂ :=
  AddGroupNorm.toNormedAddCommGroup
    { abs with
      map_zero' := map_zero abs
      neg' := abs.map_neg
      eq_zero_of_map_eq_zero' := fun _ => abs.eq_zero.1 }

instance : NormedField ℂ :=
  { Complex.instField,
    Complex.normedAddCommGroup with
    norm := abs
    dist_eq := fun _ _ => rfl
    norm_mul' := map_mul abs }

instance : DenselyNormedField ℂ
    where lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨x, h⟩ := NormedField.exists_lt_norm_lt ℝ h₀ hr
    have this : ‖(‖x‖ : ℂ)‖ = ‖‖x‖‖ := by simp only [norm_eq_abs, abs_of_real, Real.norm_eq_abs]
    ⟨‖x‖, by rwa [this, norm_norm]⟩

instance {R : Type _} [NormedField R] [NormedAlgebra R ℝ] : NormedAlgebra R ℂ
    where
  norm_smul_le r x :=
    by
    rw [norm_eq_abs, norm_eq_abs, ← algebraMap_smul ℝ r x, Algebra.smul_def, map_mul, ←
      norm_algebraMap' ℝ r, coe_algebra_map, abs_of_real]
    rfl
  toAlgebra := Complex.algebra

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]

#print NormedSpace.complexToReal /-
-- see Note [lower instance priority]
/-- The module structure from `module.complex_to_real` is a normed space. -/
instance (priority := 900) NormedSpace.complexToReal : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E
#align normed_space.complex_to_real NormedSpace.complexToReal
-/

#print Complex.dist_eq /-
theorem dist_eq (z w : ℂ) : dist z w = abs (z - w) :=
  rfl
#align complex.dist_eq Complex.dist_eq
-/

#print Complex.dist_eq_re_im /-
theorem dist_eq_re_im (z w : ℂ) : dist z w = Real.sqrt ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := by
  rw [sq, sq]; rfl
#align complex.dist_eq_re_im Complex.dist_eq_re_im
-/

#print Complex.dist_mk /-
@[simp]
theorem dist_mk (x₁ y₁ x₂ y₂ : ℝ) :
    dist (mk x₁ y₁) (mk x₂ y₂) = Real.sqrt ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2) :=
  dist_eq_re_im _ _
#align complex.dist_mk Complex.dist_mk
-/

#print Complex.dist_of_re_eq /-
theorem dist_of_re_eq {z w : ℂ} (h : z.re = w.re) : dist z w = dist z.im w.im := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_pos, zero_add, Real.sqrt_sq_eq_abs, Real.dist_eq]
#align complex.dist_of_re_eq Complex.dist_of_re_eq
-/

#print Complex.nndist_of_re_eq /-
theorem nndist_of_re_eq {z w : ℂ} (h : z.re = w.re) : nndist z w = nndist z.im w.im :=
  NNReal.eq <| dist_of_re_eq h
#align complex.nndist_of_re_eq Complex.nndist_of_re_eq
-/

#print Complex.edist_of_re_eq /-
theorem edist_of_re_eq {z w : ℂ} (h : z.re = w.re) : edist z w = edist z.im w.im := by
  rw [edist_nndist, edist_nndist, nndist_of_re_eq h]
#align complex.edist_of_re_eq Complex.edist_of_re_eq
-/

#print Complex.dist_of_im_eq /-
theorem dist_of_im_eq {z w : ℂ} (h : z.im = w.im) : dist z w = dist z.re w.re := by
  rw [dist_eq_re_im, h, sub_self, zero_pow two_pos, add_zero, Real.sqrt_sq_eq_abs, Real.dist_eq]
#align complex.dist_of_im_eq Complex.dist_of_im_eq
-/

#print Complex.nndist_of_im_eq /-
theorem nndist_of_im_eq {z w : ℂ} (h : z.im = w.im) : nndist z w = nndist z.re w.re :=
  NNReal.eq <| dist_of_im_eq h
#align complex.nndist_of_im_eq Complex.nndist_of_im_eq
-/

#print Complex.edist_of_im_eq /-
theorem edist_of_im_eq {z w : ℂ} (h : z.im = w.im) : edist z w = edist z.re w.re := by
  rw [edist_nndist, edist_nndist, nndist_of_im_eq h]
#align complex.edist_of_im_eq Complex.edist_of_im_eq
-/

#print Complex.dist_conj_self /-
theorem dist_conj_self (z : ℂ) : dist (conj z) z = 2 * |z.im| := by
  rw [dist_of_re_eq (conj_re z), conj_im, dist_comm, Real.dist_eq, sub_neg_eq_add, ← two_mul,
    _root_.abs_mul, abs_of_pos (zero_lt_two' ℝ)]
#align complex.dist_conj_self Complex.dist_conj_self
-/

#print Complex.nndist_conj_self /-
theorem nndist_conj_self (z : ℂ) : nndist (conj z) z = 2 * Real.nnabs z.im :=
  NNReal.eq <| by rw [← dist_nndist, NNReal.coe_mul, NNReal.coe_two, Real.coe_nnabs, dist_conj_self]
#align complex.nndist_conj_self Complex.nndist_conj_self
-/

#print Complex.dist_self_conj /-
theorem dist_self_conj (z : ℂ) : dist z (conj z) = 2 * |z.im| := by rw [dist_comm, dist_conj_self]
#align complex.dist_self_conj Complex.dist_self_conj
-/

#print Complex.nndist_self_conj /-
theorem nndist_self_conj (z : ℂ) : nndist z (conj z) = 2 * Real.nnabs z.im := by
  rw [nndist_comm, nndist_conj_self]
#align complex.nndist_self_conj Complex.nndist_self_conj
-/

#print Complex.comap_abs_nhds_zero /-
@[simp]
theorem comap_abs_nhds_zero : Filter.comap abs (𝓝 0) = 𝓝 0 :=
  comap_norm_nhds_zero
#align complex.comap_abs_nhds_zero Complex.comap_abs_nhds_zero
-/

#print Complex.norm_real /-
theorem norm_real (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖ :=
  abs_ofReal _
#align complex.norm_real Complex.norm_real
-/

#print Complex.norm_rat /-
@[simp]
theorem norm_rat (r : ℚ) : ‖(r : ℂ)‖ = |(r : ℝ)| := by rw [← of_real_rat_cast]; exact norm_real _
#align complex.norm_rat Complex.norm_rat
-/

#print Complex.norm_nat /-
@[simp]
theorem norm_nat (n : ℕ) : ‖(n : ℂ)‖ = n :=
  abs_natCast _
#align complex.norm_nat Complex.norm_nat
-/

#print Complex.norm_int /-
@[simp]
theorem norm_int {n : ℤ} : ‖(n : ℂ)‖ = |n| := by
  simp (config := { singlePass := true }) [← Rat.cast_intCast]
#align complex.norm_int Complex.norm_int
-/

#print Complex.norm_int_of_nonneg /-
theorem norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ‖(n : ℂ)‖ = n := by simp [hn]
#align complex.norm_int_of_nonneg Complex.norm_int_of_nonneg
-/

#print Complex.continuous_abs /-
@[continuity]
theorem continuous_abs : Continuous abs :=
  continuous_norm
#align complex.continuous_abs Complex.continuous_abs
-/

#print Complex.continuous_normSq /-
@[continuity]
theorem continuous_normSq : Continuous normSq := by
  simpa [← norm_sq_eq_abs] using continuous_abs.pow 2
#align complex.continuous_norm_sq Complex.continuous_normSq
-/

#print Complex.nnnorm_real /-
@[simp, norm_cast]
theorem nnnorm_real (r : ℝ) : ‖(r : ℂ)‖₊ = ‖r‖₊ :=
  Subtype.ext <| norm_real r
#align complex.nnnorm_real Complex.nnnorm_real
-/

#print Complex.nnnorm_nat /-
@[simp, norm_cast]
theorem nnnorm_nat (n : ℕ) : ‖(n : ℂ)‖₊ = n :=
  Subtype.ext <| by simp
#align complex.nnnorm_nat Complex.nnnorm_nat
-/

#print Complex.nnnorm_int /-
@[simp, norm_cast]
theorem nnnorm_int (n : ℤ) : ‖(n : ℂ)‖₊ = ‖n‖₊ :=
  Subtype.ext <| by simp only [coe_nnnorm, norm_int, Int.norm_eq_abs]
#align complex.nnnorm_int Complex.nnnorm_int
-/

#print Complex.nnnorm_eq_one_of_pow_eq_one /-
theorem nnnorm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ‖ζ‖₊ = 1 :=
  by
  refine' (@pow_left_inj NNReal _ _ _ _ zero_le' zero_le' hn.bot_lt).mp _
  rw [← nnnorm_pow, h, nnnorm_one, one_pow]
#align complex.nnnorm_eq_one_of_pow_eq_one Complex.nnnorm_eq_one_of_pow_eq_one
-/

#print Complex.norm_eq_one_of_pow_eq_one /-
theorem norm_eq_one_of_pow_eq_one {ζ : ℂ} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ‖ζ‖ = 1 :=
  congr_arg coe (nnnorm_eq_one_of_pow_eq_one h hn)
#align complex.norm_eq_one_of_pow_eq_one Complex.norm_eq_one_of_pow_eq_one
-/

#print Complex.equivRealProd_apply_le /-
theorem equivRealProd_apply_le (z : ℂ) : ‖equivRealProd z‖ ≤ abs z := by
  simp [Prod.norm_def, abs_re_le_abs, abs_im_le_abs]
#align complex.equiv_real_prod_apply_le Complex.equivRealProd_apply_le
-/

#print Complex.equivRealProd_apply_le' /-
theorem equivRealProd_apply_le' (z : ℂ) : ‖equivRealProd z‖ ≤ 1 * abs z := by
  simpa using equiv_real_prod_apply_le z
#align complex.equiv_real_prod_apply_le' Complex.equivRealProd_apply_le'
-/

#print Complex.lipschitz_equivRealProd /-
theorem lipschitz_equivRealProd : LipschitzWith 1 equivRealProd := by
  simpa using AddMonoidHomClass.lipschitz_of_bound equiv_real_prod_lm 1 equiv_real_prod_apply_le'
#align complex.lipschitz_equiv_real_prod Complex.lipschitz_equivRealProd
-/

#print Complex.antilipschitz_equivRealProd /-
theorem antilipschitz_equivRealProd : AntilipschitzWith (NNReal.sqrt 2) equivRealProd := by
  simpa using AddMonoidHomClass.antilipschitz_of_bound equiv_real_prod_lm abs_le_sqrt_two_mul_max
#align complex.antilipschitz_equiv_real_prod Complex.antilipschitz_equivRealProd
-/

#print Complex.uniformEmbedding_equivRealProd /-
theorem uniformEmbedding_equivRealProd : UniformEmbedding equivRealProd :=
  antilipschitz_equivRealProd.UniformEmbedding lipschitz_equivRealProd.UniformContinuous
#align complex.uniform_embedding_equiv_real_prod Complex.uniformEmbedding_equivRealProd
-/

instance : CompleteSpace ℂ :=
  (completeSpace_congr uniformEmbedding_equivRealProd).mpr inferInstance

#print Complex.equivRealProdCLM /-
/-- The natural `continuous_linear_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ :=
  equivRealProdLm.toContinuousLinearEquivOfBounds 1 (Real.sqrt 2) equivRealProd_apply_le' fun p =>
    abs_le_sqrt_two_mul_max (equivRealProd.symm p)
#align complex.equiv_real_prod_clm Complex.equivRealProdCLM
-/

instance : ProperSpace ℂ :=
  (id lipschitz_equivRealProd : LipschitzWith 1 equivRealProdCLM.toHomeomorph).ProperSpace

#print Complex.tendsto_abs_cocompact_atTop /-
/-- The `abs` function on `ℂ` is proper. -/
theorem tendsto_abs_cocompact_atTop : Filter.Tendsto abs (Filter.cocompact ℂ) Filter.atTop :=
  tendsto_norm_cocompact_atTop
#align complex.tendsto_abs_cocompact_at_top Complex.tendsto_abs_cocompact_atTop
-/

#print Complex.tendsto_normSq_cocompact_atTop /-
/-- The `norm_sq` function on `ℂ` is proper. -/
theorem tendsto_normSq_cocompact_atTop : Filter.Tendsto normSq (Filter.cocompact ℂ) Filter.atTop :=
  by
  simpa [mul_self_abs] using
    tendsto_abs_cocompact_at_top.at_top_mul_at_top tendsto_abs_cocompact_at_top
#align complex.tendsto_norm_sq_cocompact_at_top Complex.tendsto_normSq_cocompact_atTop
-/

open ContinuousLinearMap

#print Complex.reCLM /-
/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def reCLM : ℂ →L[ℝ] ℝ :=
  reLm.mkContinuous 1 fun x => by simp [abs_re_le_abs]
#align complex.re_clm Complex.reCLM
-/

#print Complex.continuous_re /-
@[continuity]
theorem continuous_re : Continuous re :=
  reCLM.Continuous
#align complex.continuous_re Complex.continuous_re
-/

#print Complex.reCLM_coe /-
@[simp]
theorem reCLM_coe : (coe reCLM : ℂ →ₗ[ℝ] ℝ) = reLm :=
  rfl
#align complex.re_clm_coe Complex.reCLM_coe
-/

#print Complex.reCLM_apply /-
@[simp]
theorem reCLM_apply (z : ℂ) : (reCLM : ℂ → ℝ) z = z.re :=
  rfl
#align complex.re_clm_apply Complex.reCLM_apply
-/

#print Complex.imCLM /-
/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def imCLM : ℂ →L[ℝ] ℝ :=
  imLm.mkContinuous 1 fun x => by simp [abs_im_le_abs]
#align complex.im_clm Complex.imCLM
-/

#print Complex.continuous_im /-
@[continuity]
theorem continuous_im : Continuous im :=
  imCLM.Continuous
#align complex.continuous_im Complex.continuous_im
-/

#print Complex.imCLM_coe /-
@[simp]
theorem imCLM_coe : (coe imCLM : ℂ →ₗ[ℝ] ℝ) = imLm :=
  rfl
#align complex.im_clm_coe Complex.imCLM_coe
-/

#print Complex.imCLM_apply /-
@[simp]
theorem imCLM_apply (z : ℂ) : (imCLM : ℂ → ℝ) z = z.im :=
  rfl
#align complex.im_clm_apply Complex.imCLM_apply
-/

#print Complex.restrictScalars_one_smulRight' /-
theorem restrictScalars_one_smulRight' (x : E) :
    ContinuousLinearMap.restrictScalars ℝ ((1 : ℂ →L[ℂ] ℂ).smul_right x : ℂ →L[ℂ] E) =
      reCLM.smul_right x + I • imCLM.smul_right x :=
  by ext ⟨a, b⟩; simp [mk_eq_add_mul_I, add_smul, mul_smul, smul_comm I]
#align complex.restrict_scalars_one_smul_right' Complex.restrictScalars_one_smulRight'
-/

#print Complex.restrictScalars_one_smulRight /-
theorem restrictScalars_one_smulRight (x : ℂ) :
    ContinuousLinearMap.restrictScalars ℝ ((1 : ℂ →L[ℂ] ℂ).smul_right x : ℂ →L[ℂ] ℂ) = x • 1 := by
  ext1 z; dsimp; apply mul_comm
#align complex.restrict_scalars_one_smul_right Complex.restrictScalars_one_smulRight
-/

#print Complex.conjLIE /-
/-- The complex-conjugation function from `ℂ` to itself is an isometric linear equivalence. -/
def conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  ⟨conjAe.toLinearEquiv, abs_conj⟩
#align complex.conj_lie Complex.conjLIE
-/

#print Complex.conjLIE_apply /-
@[simp]
theorem conjLIE_apply (z : ℂ) : conjLIE z = conj z :=
  rfl
#align complex.conj_lie_apply Complex.conjLIE_apply
-/

#print Complex.conjLIE_symm /-
@[simp]
theorem conjLIE_symm : conjLIE.symm = conjLIE :=
  rfl
#align complex.conj_lie_symm Complex.conjLIE_symm
-/

#print Complex.isometry_conj /-
theorem isometry_conj : Isometry (conj : ℂ → ℂ) :=
  conjLIE.Isometry
#align complex.isometry_conj Complex.isometry_conj
-/

#print Complex.dist_conj_conj /-
@[simp]
theorem dist_conj_conj (z w : ℂ) : dist (conj z) (conj w) = dist z w :=
  isometry_conj.dist_eq z w
#align complex.dist_conj_conj Complex.dist_conj_conj
-/

#print Complex.nndist_conj_conj /-
@[simp]
theorem nndist_conj_conj (z w : ℂ) : nndist (conj z) (conj w) = nndist z w :=
  isometry_conj.nndist_eq z w
#align complex.nndist_conj_conj Complex.nndist_conj_conj
-/

#print Complex.dist_conj_comm /-
theorem dist_conj_comm (z w : ℂ) : dist (conj z) w = dist z (conj w) := by
  rw [← dist_conj_conj, conj_conj]
#align complex.dist_conj_comm Complex.dist_conj_comm
-/

#print Complex.nndist_conj_comm /-
theorem nndist_conj_comm (z w : ℂ) : nndist (conj z) w = nndist z (conj w) :=
  Subtype.ext <| dist_conj_comm _ _
#align complex.nndist_conj_comm Complex.nndist_conj_comm
-/

instance : ContinuousStar ℂ :=
  ⟨conjLIE.Continuous⟩

#print Complex.continuous_conj /-
@[continuity]
theorem continuous_conj : Continuous (conj : ℂ → ℂ) :=
  continuous_star
#align complex.continuous_conj Complex.continuous_conj
-/

#print Complex.ringHom_eq_id_or_conj_of_continuous /-
/-- The only continuous ring homomorphisms from `ℂ` to `ℂ` are the identity and the complex
conjugation. -/
theorem ringHom_eq_id_or_conj_of_continuous {f : ℂ →+* ℂ} (hf : Continuous f) :
    f = RingHom.id ℂ ∨ f = conj :=
  by
  refine'
    (real_alg_hom_eq_id_or_conj <| AlgHom.mk' f <| map_real_smul f hf).imp (fun h => _) fun h => _
  all_goals convert congr_arg AlgHom.toRingHom h; ext1; rfl
#align complex.ring_hom_eq_id_or_conj_of_continuous Complex.ringHom_eq_id_or_conj_of_continuous
-/

#print Complex.conjCLE /-
/-- Continuous linear equiv version of the conj function, from `ℂ` to `ℂ`. -/
def conjCLE : ℂ ≃L[ℝ] ℂ :=
  conjLIE
#align complex.conj_cle Complex.conjCLE
-/

#print Complex.conjCLE_coe /-
@[simp]
theorem conjCLE_coe : conjCLE.toLinearEquiv = conjAe.toLinearEquiv :=
  rfl
#align complex.conj_cle_coe Complex.conjCLE_coe
-/

#print Complex.conjCLE_apply /-
@[simp]
theorem conjCLE_apply (z : ℂ) : conjCLE z = conj z :=
  rfl
#align complex.conj_cle_apply Complex.conjCLE_apply
-/

#print Complex.ofRealLI /-
/-- Linear isometry version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealLI : ℝ →ₗᵢ[ℝ] ℂ :=
  ⟨ofRealAm.toLinearMap, norm_real⟩
#align complex.of_real_li Complex.ofRealLI
-/

#print Complex.isometry_ofReal /-
theorem isometry_ofReal : Isometry (coe : ℝ → ℂ) :=
  ofRealLI.Isometry
#align complex.isometry_of_real Complex.isometry_ofReal
-/

#print Complex.continuous_ofReal /-
@[continuity]
theorem continuous_ofReal : Continuous (coe : ℝ → ℂ) :=
  ofRealLI.Continuous
#align complex.continuous_of_real Complex.continuous_ofReal
-/

#print Complex.ringHom_eq_ofReal_of_continuous /-
/-- The only continuous ring homomorphism from `ℝ` to `ℂ` is the identity. -/
theorem ringHom_eq_ofReal_of_continuous {f : ℝ →+* ℂ} (h : Continuous f) : f = Complex.ofReal :=
  by
  convert
    congr_arg AlgHom.toRingHom
      (Subsingleton.elim (AlgHom.mk' f <| map_real_smul f h) <| Algebra.ofId ℝ ℂ)
  ext1; rfl
#align complex.ring_hom_eq_of_real_of_continuous Complex.ringHom_eq_ofReal_of_continuous
-/

#print Complex.ofRealCLM /-
/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def ofRealCLM : ℝ →L[ℝ] ℂ :=
  ofRealLI.toContinuousLinearMap
#align complex.of_real_clm Complex.ofRealCLM
-/

#print Complex.ofRealCLM_coe /-
@[simp]
theorem ofRealCLM_coe : (ofRealCLM : ℝ →ₗ[ℝ] ℂ) = ofRealAm.toLinearMap :=
  rfl
#align complex.of_real_clm_coe Complex.ofRealCLM_coe
-/

#print Complex.ofRealCLM_apply /-
@[simp]
theorem ofRealCLM_apply (x : ℝ) : ofRealCLM x = x :=
  rfl
#align complex.of_real_clm_apply Complex.ofRealCLM_apply
-/

noncomputable instance : RCLike ℂ
    where
  re := ⟨Complex.re, Complex.zero_re, Complex.add_re⟩
  im := ⟨Complex.im, Complex.zero_im, Complex.add_im⟩
  I := Complex.I
  i_re_ax := by simp only [AddMonoidHom.coe_mk, Complex.I_re]
  i_hMul_i_ax := by simp only [Complex.I_mul_I, eq_self_iff_true, or_true_iff]
  re_add_im_ax z := by
    simp only [AddMonoidHom.coe_mk, Complex.re_add_im, Complex.coe_algebraMap,
      Complex.ofReal_eq_coe]
  of_real_re_ax r := by
    simp only [AddMonoidHom.coe_mk, Complex.ofReal_re, Complex.coe_algebraMap,
      Complex.ofReal_eq_coe]
  of_real_im_ax r := by
    simp only [AddMonoidHom.coe_mk, Complex.ofReal_im, Complex.coe_algebraMap,
      Complex.ofReal_eq_coe]
  hMul_re_ax z w := by simp only [Complex.mul_re, AddMonoidHom.coe_mk]
  hMul_im_ax z w := by simp only [AddMonoidHom.coe_mk, Complex.mul_im]
  conj_re_ax z := rfl
  conj_im_ax z := rfl
  conj_i_ax := by simp only [Complex.conj_I, RingHom.coe_mk]
  norm_sq_eq_def_ax z := by
    simp only [← Complex.normSq_eq_abs, ← Complex.normSq_apply, AddMonoidHom.coe_mk,
      Complex.norm_eq_abs]
  hMul_im_i_ax z := by simp only [mul_one, AddMonoidHom.coe_mk, Complex.I_im]

#print RCLike.re_eq_complex_re /-
theorem RCLike.re_eq_complex_re : ⇑(RCLike.re : ℂ →+ ℝ) = Complex.re :=
  rfl
#align is_R_or_C.re_eq_complex_re RCLike.re_eq_complex_re
-/

#print RCLike.im_eq_complex_im /-
theorem RCLike.im_eq_complex_im : ⇑(RCLike.im : ℂ →+ ℝ) = Complex.im :=
  rfl
#align is_R_or_C.im_eq_complex_im RCLike.im_eq_complex_im
-/

section ComplexOrder

open scoped ComplexOrder

#print Complex.eq_coe_norm_of_nonneg /-
theorem eq_coe_norm_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z = ↑‖z‖ := by
  rw [eq_re_of_real_le hz, RCLike.norm_ofReal, _root_.abs_of_nonneg (Complex.le_def.2 hz).1]
#align complex.eq_coe_norm_of_nonneg Complex.eq_coe_norm_of_nonneg
-/

end ComplexOrder

end Complex

namespace RCLike

open scoped ComplexConjugate

local notation "reC" => @RCLike.re ℂ _

local notation "imC" => @RCLike.im ℂ _

local notation "IC" => @RCLike.i ℂ _

local notation "norm_sqC" => @RCLike.normSq ℂ _

#print RCLike.re_to_complex /-
@[simp]
theorem re_to_complex {x : ℂ} : reC x = x.re :=
  rfl
#align is_R_or_C.re_to_complex RCLike.re_to_complex
-/

#print RCLike.im_to_complex /-
@[simp]
theorem im_to_complex {x : ℂ} : imC x = x.im :=
  rfl
#align is_R_or_C.im_to_complex RCLike.im_to_complex
-/

#print RCLike.I_to_complex /-
@[simp]
theorem I_to_complex : IC = Complex.I :=
  rfl
#align is_R_or_C.I_to_complex RCLike.I_to_complex
-/

#print RCLike.normSq_to_complex /-
@[simp]
theorem normSq_to_complex {x : ℂ} : norm_sqC x = Complex.normSq x :=
  rfl
#align is_R_or_C.norm_sq_to_complex RCLike.normSq_to_complex
-/

section tsum

variable {α : Type _} (𝕜 : Type _) [RCLike 𝕜]

#print RCLike.hasSum_conj /-
@[simp]
theorem hasSum_conj {f : α → 𝕜} {x : 𝕜} : HasSum (fun x => conj (f x)) x ↔ HasSum f (conj x) :=
  conjCLE.HasSum
#align is_R_or_C.has_sum_conj RCLike.hasSum_conj
-/

#print RCLike.hasSum_conj' /-
theorem hasSum_conj' {f : α → 𝕜} {x : 𝕜} : HasSum (fun x => conj (f x)) (conj x) ↔ HasSum f x :=
  conjCLE.hasSum'
#align is_R_or_C.has_sum_conj' RCLike.hasSum_conj'
-/

#print RCLike.summable_conj /-
@[simp]
theorem summable_conj {f : α → 𝕜} : (Summable fun x => conj (f x)) ↔ Summable f :=
  summable_star_iff
#align is_R_or_C.summable_conj RCLike.summable_conj
-/

variable {𝕜}

#print RCLike.conj_tsum /-
theorem conj_tsum (f : α → 𝕜) : conj (∑' a, f a) = ∑' a, conj (f a) :=
  tsum_star
#align is_R_or_C.conj_tsum RCLike.conj_tsum
-/

variable (𝕜)

#print RCLike.hasSum_ofReal /-
@[simp, norm_cast]
theorem hasSum_ofReal {f : α → ℝ} {x : ℝ} : HasSum (fun x => (f x : 𝕜)) x ↔ HasSum f x :=
  ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using re_clm.has_sum h,
    ofRealCLM.HasSum⟩
#align is_R_or_C.has_sum_of_real RCLike.hasSum_ofReal
-/

#print RCLike.summable_ofReal /-
@[simp, norm_cast]
theorem summable_ofReal {f : α → ℝ} : (Summable fun x => (f x : 𝕜)) ↔ Summable f :=
  ⟨fun h => by simpa only [RCLike.reCLM_apply, RCLike.ofReal_re] using re_clm.summable h,
    ofRealCLM.Summable⟩
#align is_R_or_C.summable_of_real RCLike.summable_ofReal
-/

#print RCLike.ofReal_tsum /-
@[norm_cast]
theorem ofReal_tsum (f : α → ℝ) : (↑(∑' a, f a) : 𝕜) = ∑' a, f a :=
  by
  by_cases h : Summable f
  · exact ContinuousLinearMap.map_tsum of_real_clm h
  ·
    rw [tsum_eq_zero_of_not_summable h,
      tsum_eq_zero_of_not_summable ((summable_of_real _).Not.mpr h), of_real_zero]
#align is_R_or_C.of_real_tsum RCLike.ofReal_tsum
-/

#print RCLike.hasSum_re /-
theorem hasSum_re {f : α → 𝕜} {x : 𝕜} (h : HasSum f x) : HasSum (fun x => re (f x)) (re x) :=
  reCLM.HasSum h
#align is_R_or_C.has_sum_re RCLike.hasSum_re
-/

#print RCLike.hasSum_im /-
theorem hasSum_im {f : α → 𝕜} {x : 𝕜} (h : HasSum f x) : HasSum (fun x => im (f x)) (im x) :=
  imCLM.HasSum h
#align is_R_or_C.has_sum_im RCLike.hasSum_im
-/

#print RCLike.re_tsum /-
theorem re_tsum {f : α → 𝕜} (h : Summable f) : re (∑' a, f a) = ∑' a, re (f a) :=
  reCLM.map_tsum h
#align is_R_or_C.re_tsum RCLike.re_tsum
-/

#print RCLike.im_tsum /-
theorem im_tsum {f : α → 𝕜} (h : Summable f) : im (∑' a, f a) = ∑' a, im (f a) :=
  imCLM.map_tsum h
#align is_R_or_C.im_tsum RCLike.im_tsum
-/

variable {𝕜}

#print RCLike.hasSum_iff /-
theorem hasSum_iff (f : α → 𝕜) (c : 𝕜) :
    HasSum f c ↔ HasSum (fun x => re (f x)) (re c) ∧ HasSum (fun x => im (f x)) (im c) :=
  by
  refine' ⟨fun h => ⟨has_sum_re _ h, has_sum_im _ h⟩, _⟩
  rintro ⟨h₁, h₂⟩
  rw [← RCLike.re_add_im c]
  convert ((has_sum_of_real 𝕜).mpr h₁).add (((has_sum_of_real 𝕜).mpr h₂).hMul_right I)
  simp_rw [RCLike.re_add_im]
#align is_R_or_C.has_sum_iff RCLike.hasSum_iff
-/

end tsum

end RCLike

namespace Complex

/-!
We have to repeat the lemmas about `is_R_or_C.re` and `is_R_or_C.im` as they are not syntactic
matches for `complex.re` and `complex.im`.

We do not have this problem with `of_real` and `conj`, although we repeat them anyway for
discoverability and to avoid the need to unify `𝕜`.
-/


section tsum

variable {α : Type _}

open scoped ComplexConjugate

#print Complex.hasSum_conj /-
@[simp]
theorem hasSum_conj {f : α → ℂ} {x : ℂ} : HasSum (fun x => conj (f x)) x ↔ HasSum f (conj x) :=
  RCLike.hasSum_conj _
#align complex.has_sum_conj Complex.hasSum_conj
-/

#print Complex.hasSum_conj' /-
theorem hasSum_conj' {f : α → ℂ} {x : ℂ} : HasSum (fun x => conj (f x)) (conj x) ↔ HasSum f x :=
  RCLike.hasSum_conj' _
#align complex.has_sum_conj' Complex.hasSum_conj'
-/

#print Complex.summable_conj /-
@[simp]
theorem summable_conj {f : α → ℂ} : (Summable fun x => conj (f x)) ↔ Summable f :=
  RCLike.summable_conj _
#align complex.summable_conj Complex.summable_conj
-/

#print Complex.conj_tsum /-
theorem conj_tsum (f : α → ℂ) : conj (∑' a, f a) = ∑' a, conj (f a) :=
  RCLike.conj_tsum _
#align complex.conj_tsum Complex.conj_tsum
-/

#print Complex.hasSum_ofReal /-
@[simp, norm_cast]
theorem hasSum_ofReal {f : α → ℝ} {x : ℝ} : HasSum (fun x => (f x : ℂ)) x ↔ HasSum f x :=
  RCLike.hasSum_ofReal _
#align complex.has_sum_of_real Complex.hasSum_ofReal
-/

#print Complex.summable_ofReal /-
@[simp, norm_cast]
theorem summable_ofReal {f : α → ℝ} : (Summable fun x => (f x : ℂ)) ↔ Summable f :=
  RCLike.summable_ofReal _
#align complex.summable_of_real Complex.summable_ofReal
-/

#print Complex.ofReal_tsum /-
@[norm_cast]
theorem ofReal_tsum (f : α → ℝ) : (↑(∑' a, f a) : ℂ) = ∑' a, f a :=
  RCLike.ofReal_tsum _ _
#align complex.of_real_tsum Complex.ofReal_tsum
-/

#print Complex.hasSum_re /-
theorem hasSum_re {f : α → ℂ} {x : ℂ} (h : HasSum f x) : HasSum (fun x => (f x).re) x.re :=
  RCLike.hasSum_re _ h
#align complex.has_sum_re Complex.hasSum_re
-/

#print Complex.hasSum_im /-
theorem hasSum_im {f : α → ℂ} {x : ℂ} (h : HasSum f x) : HasSum (fun x => (f x).im) x.im :=
  RCLike.hasSum_im _ h
#align complex.has_sum_im Complex.hasSum_im
-/

#print Complex.re_tsum /-
theorem re_tsum {f : α → ℂ} (h : Summable f) : (∑' a, f a).re = ∑' a, (f a).re :=
  RCLike.re_tsum _ h
#align complex.re_tsum Complex.re_tsum
-/

#print Complex.im_tsum /-
theorem im_tsum {f : α → ℂ} (h : Summable f) : (∑' a, f a).im = ∑' a, (f a).im :=
  RCLike.im_tsum _ h
#align complex.im_tsum Complex.im_tsum
-/

#print Complex.hasSum_iff /-
theorem hasSum_iff (f : α → ℂ) (c : ℂ) :
    HasSum f c ↔ HasSum (fun x => (f x).re) c.re ∧ HasSum (fun x => (f x).im) c.im :=
  RCLike.hasSum_iff _ _
#align complex.has_sum_iff Complex.hasSum_iff
-/

end tsum

end Complex

