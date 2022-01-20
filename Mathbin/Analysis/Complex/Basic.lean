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

open_locale ComplexConjugate

instance : HasNorm ℂ :=
  ⟨abs⟩

instance : NormedGroup ℂ :=
  NormedGroup.ofCore ℂ { norm_eq_zero_iff := fun z => abs_eq_zero, triangle := abs_add, norm_neg := abs_neg }

instance : NormedField ℂ :=
  { Complex.field with norm := abs, dist_eq := fun _ _ => rfl, norm_mul' := abs_mul }

instance : NondiscreteNormedField ℂ where
  non_trivial :=
    ⟨2, by
      simp [norm] <;> norm_num⟩

instance {R : Type _} [NormedField R] [NormedAlgebra R ℝ] : NormedAlgebra R ℂ where
  norm_algebra_map_eq := fun x => (abs_of_real $ algebraMap R ℝ x).trans (norm_algebra_map_eq ℝ x)
  toAlgebra := Complex.algebra

/-- The module structure from `module.complex_to_real` is a normed space. -/
instance (priority := 900) _root_.normed_space.complex_to_real {E : Type _} [NormedGroup E] [NormedSpace ℂ E] :
    NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ ℂ E

@[simp]
theorem norm_eq_abs (z : ℂ) : ∥z∥ = abs z :=
  rfl

theorem dist_eq (z w : ℂ) : dist z w = abs (z - w) :=
  rfl

@[simp]
theorem norm_real (r : ℝ) : ∥(r : ℂ)∥ = ∥r∥ :=
  abs_of_real _

@[simp]
theorem norm_rat (r : ℚ) : ∥(r : ℂ)∥ = |(r : ℝ)| := by
  suffices ∥((r : ℝ) : ℂ)∥ = |r| by
    simpa
  rw [norm_real, Real.norm_eq_abs]

@[simp]
theorem norm_nat (n : ℕ) : ∥(n : ℂ)∥ = n :=
  abs_of_nat _

@[simp]
theorem norm_int {n : ℤ} : ∥(n : ℂ)∥ = |n| := by
  suffices ∥((n : ℝ) : ℂ)∥ = |n| by
    simpa
  rw [norm_real, Real.norm_eq_abs]

theorem norm_int_of_nonneg {n : ℤ} (hn : 0 ≤ n) : ∥(n : ℂ)∥ = n := by
  rw [norm_int, _root_.abs_of_nonneg] <;> exact Int.cast_nonneg.2 hn

@[continuity]
theorem continuous_abs : Continuous abs :=
  continuous_norm

@[continuity]
theorem continuous_norm_sq : Continuous norm_sq := by
  simpa [← norm_sq_eq_abs] using continuous_abs.pow 2

/-- The `abs` function on `ℂ` is proper. -/
theorem tendsto_abs_cocompact_at_top : Filter.Tendsto abs (Filter.cocompact ℂ) Filter.atTop :=
  tendsto_norm_cocompact_at_top

/-- The `norm_sq` function on `ℂ` is proper. -/
theorem tendsto_norm_sq_cocompact_at_top : Filter.Tendsto norm_sq (Filter.cocompact ℂ) Filter.atTop := by
  simpa [mul_self_abs] using tendsto_abs_cocompact_at_top.at_top_mul_at_top tendsto_abs_cocompact_at_top

open ContinuousLinearMap

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def re_clm : ℂ →L[ℝ] ℝ :=
  re_lm.mkContinuous 1 fun x => by
    simp [Real.norm_eq_abs, abs_re_le_abs]

@[continuity]
theorem continuous_re : Continuous re :=
  re_clm.Continuous

@[simp]
theorem re_clm_coe : (coeₓ re_clm : ℂ →ₗ[ℝ] ℝ) = re_lm :=
  rfl

@[simp]
theorem re_clm_apply (z : ℂ) : (re_clm : ℂ → ℝ) z = z.re :=
  rfl

@[simp]
theorem re_clm_norm : ∥re_clm∥ = 1 :=
  le_antisymmₓ (LinearMap.mk_continuous_norm_le _ zero_le_one _) $
    calc
      1 = ∥re_clm 1∥ := by
        simp
      _ ≤ ∥re_clm∥ :=
        unit_le_op_norm _ _
          (by
            simp )
      

/-- Continuous linear map version of the real part function, from `ℂ` to `ℝ`. -/
def im_clm : ℂ →L[ℝ] ℝ :=
  im_lm.mkContinuous 1 fun x => by
    simp [Real.norm_eq_abs, abs_im_le_abs]

@[continuity]
theorem continuous_im : Continuous im :=
  im_clm.Continuous

@[simp]
theorem im_clm_coe : (coeₓ im_clm : ℂ →ₗ[ℝ] ℝ) = im_lm :=
  rfl

@[simp]
theorem im_clm_apply (z : ℂ) : (im_clm : ℂ → ℝ) z = z.im :=
  rfl

@[simp]
theorem im_clm_norm : ∥im_clm∥ = 1 :=
  le_antisymmₓ (LinearMap.mk_continuous_norm_le _ zero_le_one _) $
    calc
      1 = ∥im_clm I∥ := by
        simp
      _ ≤ ∥im_clm∥ :=
        unit_le_op_norm _ _
          (by
            simp )
      

theorem restrict_scalars_one_smul_right' {E : Type _} [NormedGroup E] [NormedSpace ℂ E] (x : E) :
    ContinuousLinearMap.restrictScalars ℝ ((1 : ℂ →L[ℂ] ℂ).smulRight x : ℂ →L[ℂ] E) =
      re_clm.smulRight x + I • im_clm.smulRight x :=
  by
  ext ⟨a, b⟩
  simp [mk_eq_add_mul_I, add_smul, mul_smul, smul_comm I]

theorem restrict_scalars_one_smul_right (x : ℂ) :
    ContinuousLinearMap.restrictScalars ℝ ((1 : ℂ →L[ℂ] ℂ).smulRight x : ℂ →L[ℂ] ℂ) = x • 1 := by
  ext1 z
  dsimp
  apply mul_commₓ

/-- The complex-conjugation function from `ℂ` to itself is an isometric linear equivalence. -/
def conj_lie : ℂ ≃ₗᵢ[ℝ] ℂ :=
  ⟨conj_ae.toLinearEquiv, abs_conj⟩

@[simp]
theorem conj_lie_apply (z : ℂ) : conj_lie z = conj z :=
  rfl

theorem isometry_conj : Isometry (conj : ℂ → ℂ) :=
  conj_lie.Isometry

/-- The determinant of `conj_lie`, as a linear map. -/
@[simp]
theorem det_conj_lie : (conj_lie.toLinearEquiv : ℂ →ₗ[ℝ] ℂ).det = -1 :=
  det_conj_ae

/-- The determinant of `conj_lie`, as a linear equiv. -/
@[simp]
theorem linear_equiv_det_conj_lie : conj_lie.toLinearEquiv.det = -1 :=
  linear_equiv_det_conj_ae

@[continuity]
theorem continuous_conj : Continuous (conj : ℂ → ℂ) :=
  conj_lie.Continuous

/-- Continuous linear equiv version of the conj function, from `ℂ` to `ℂ`. -/
def conj_cle : ℂ ≃L[ℝ] ℂ :=
  conj_lie

@[simp]
theorem conj_cle_coe : conj_cle.toLinearEquiv = conj_ae.toLinearEquiv :=
  rfl

@[simp]
theorem conj_cle_apply (z : ℂ) : conj_cle z = conj z :=
  rfl

@[simp]
theorem conj_cle_norm : ∥(conj_cle : ℂ →L[ℝ] ℂ)∥ = 1 :=
  conj_lie.toLinearIsometry.norm_to_continuous_linear_map

/-- Linear isometry version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_li : ℝ →ₗᵢ[ℝ] ℂ :=
  ⟨of_real_am.toLinearMap, norm_real⟩

theorem isometry_of_real : Isometry (coeₓ : ℝ → ℂ) :=
  of_real_li.Isometry

@[continuity]
theorem continuous_of_real : Continuous (coeₓ : ℝ → ℂ) :=
  of_real_li.Continuous

/-- Continuous linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_clm : ℝ →L[ℝ] ℂ :=
  of_real_li.toContinuousLinearMap

@[simp]
theorem of_real_clm_coe : (of_real_clm : ℝ →ₗ[ℝ] ℂ) = of_real_am.toLinearMap :=
  rfl

@[simp]
theorem of_real_clm_apply (x : ℝ) : of_real_clm x = x :=
  rfl

@[simp]
theorem of_real_clm_norm : ∥of_real_clm∥ = 1 :=
  of_real_li.norm_to_continuous_linear_map

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

section

variable {α β γ : Type _} [AddCommMonoidₓ α] [TopologicalSpace α] [AddCommMonoidₓ γ] [TopologicalSpace γ]

/-- The natural `add_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps (config := { simpRhs := tt }) apply symm_apply_re symm_apply_im]
def equiv_real_prod_add_hom : ℂ ≃+ ℝ × ℝ :=
  { equiv_real_prod with
    map_add' := by
      simp }

/-- The natural `linear_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps (config := { simpRhs := tt }) apply symm_apply_re symm_apply_im]
def equiv_real_prod_add_hom_lm : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  { equiv_real_prod_add_hom with
    map_smul' := by
      simp [equiv_real_prod_add_hom] }

/-- The natural `continuous_linear_equiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps (config := { simpRhs := tt }) apply symm_apply_re symm_apply_im]
def equiv_real_prodₗ : ℂ ≃L[ℝ] ℝ × ℝ :=
  equiv_real_prod_add_hom_lm.toContinuousLinearEquiv

end

theorem has_sum_iff {α} (f : α → ℂ) (c : ℂ) :
    HasSum f c ↔ HasSum (fun x => (f x).re) c.re ∧ HasSum (fun x => (f x).im) c.im := by
  refine' ⟨fun h => ⟨re_clm.has_sum h, im_clm.has_sum h⟩, _⟩
  rintro ⟨h₁, h₂⟩
  convert (h₁.prod_mk h₂).mapL equiv_real_prodₗ.symm.to_continuous_linear_map
  · ext x <;> rfl
    
  · cases c
    rfl
    

end Complex

namespace IsROrC

local notation "reC" => @IsROrC.re ℂ _

local notation "imC" => @IsROrC.im ℂ _

local notation "IC" => @IsROrC.i ℂ _

local notation "absC" => @IsROrC.abs ℂ _

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

