/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.special_functions.polar_coord
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.Jacobian

/-!
# Polar coordinates

We define polar coordinates, as a local homeomorphism in `ℝ^2` between `ℝ^2 - (-∞, 0]` and
`(0, +∞) × (-π, π)`. Its inverse is given by `(r, θ) ↦ (r cos θ, r sin θ)`.

It satisfies the following change of variables formula (see `integral_comp_polar_coord_symm`):
`∫ p in polar_coord.target, p.1 • f (polar_coord.symm p) = ∫ p, f p`

-/


noncomputable section

open Real Set MeasureTheory

open Real TopologicalSpace

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The polar coordinates local homeomorphism in `ℝ^2`, mapping `(r cos θ, r sin θ)` to `(r, θ)`.
It is a homeomorphism between `ℝ^2 - (-∞, 0]` and `(0, +∞) × (-π, π)`. -/
@[simps]
def polarCoord : LocalHomeomorph (ℝ × ℝ) (ℝ × ℝ)
    where
  toFun q := (Real.sqrt (q.1 ^ 2 + q.2 ^ 2), Complex.arg (Complex.equivRealProd.symm q))
  invFun p := (p.1 * cos p.2, p.1 * sin p.2)
  source := { q | 0 < q.1 } ∪ { q | q.2 ≠ 0 }
  target := Ioi (0 : ℝ) ×ˢ Ioo (-π) π
  map_target' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    dsimp at hr hθ
    rcases eq_or_ne θ 0 with (rfl | h'θ)
    · simpa using hr
    · right
      simpa only [ne_of_gt hr, Ne.def, mem_set_of_eq, mul_eq_zero, false_or_iff,
        sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2] using h'θ
  map_source' := by
    rintro ⟨x, y⟩ hxy
    simp only [prod_mk_mem_set_prod_eq, mem_Ioi, sqrt_pos, mem_Ioo, Complex.neg_pi_lt_arg,
      true_and_iff, Complex.arg_lt_pi_iff]
    constructor
    · cases hxy
      · dsimp at hxy
        linarith [sq_pos_of_ne_zero _ hxy.ne', sq_nonneg y]
      · linarith [sq_nonneg x, sq_pos_of_ne_zero _ hxy]
    · cases hxy
      · exact Or.inl (le_of_lt hxy)
      · exact Or.inr hxy
  right_inv' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    dsimp at hr hθ
    simp only [Prod.mk.inj_iff]
    constructor
    · conv_rhs => rw [← sqrt_sq (le_of_lt hr), ← one_mul (r ^ 2), ← sin_sq_add_cos_sq θ]
      congr 1
      ring
    · convert Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
      simp only [Complex.equiv_real_prod_symm_apply, Complex.of_real_mul, Complex.of_real_cos,
        Complex.of_real_sin]
      ring
  left_inv' := by
    rintro ⟨x, y⟩ hxy
    have A : sqrt (x ^ 2 + y ^ 2) = Complex.abs (x + y * Complex.i) := by
      simp only [Complex.abs_def, Complex.normSq, pow_two, MonoidWithZeroHom.coe_mk, Complex.add_re,
        Complex.of_real_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.of_real_im,
        Complex.I_im, sub_self, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add]
    have Z := Complex.abs_mul_cos_add_sin_mul_I (x + y * Complex.i)
    simp only [← Complex.of_real_cos, ← Complex.of_real_sin, mul_add, ← Complex.of_real_mul, ←
      mul_assoc] at Z
    simpa [A, -Complex.of_real_cos, -Complex.of_real_sin] using Complex.ext_iff.1 Z
  open_target := is_open_Ioi.Prod is_open_Ioo
  open_source :=
    (is_open_lt continuous_const continuous_fst).union
      (is_open_ne_fun continuous_snd continuous_const)
  continuous_inv_fun :=
    ((continuous_fst.mul (continuous_cos.comp continuous_snd)).prod_mk
        (continuous_fst.mul (continuous_sin.comp continuous_snd))).ContinuousOn
  continuous_to_fun :=
    by
    apply ((continuous_fst.pow 2).add (continuous_snd.pow 2)).sqrt.ContinuousOn.Prod
    have A :
      maps_to complex.equiv_real_prod.symm ({ q : ℝ × ℝ | 0 < q.1 } ∪ { q : ℝ × ℝ | q.2 ≠ 0 })
        { z | 0 < z.re ∨ z.im ≠ 0 } :=
      by
      rintro ⟨x, y⟩ hxy
      simpa only using hxy
    apply ContinuousOn.comp (fun z hz => _) _ A
    · exact (Complex.continuous_at_arg hz).ContinuousWithinAt
    · exact complex.equiv_real_prodₗ.symm.continuous.continuous_on
#align polar_coord polarCoord

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
theorem hasFderivAtPolarCoordSymm (p : ℝ × ℝ) :
    HasFderivAt polarCoord.symm
      (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
          («expr!![ »
            "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation")).toContinuousLinearMap
      p :=
  by
  rw [Matrix.to_lin_fin_two_prod_to_continuous_linear_map]
  convert
      HasFderivAt.prod
        (has_fderiv_at_fst.mul ((has_deriv_at_cos p.2).compHasFderivAt p hasFderivAtSnd))
        (has_fderiv_at_fst.mul ((has_deriv_at_sin p.2).compHasFderivAt p hasFderivAtSnd)) using
      2 <;>
    simp only [smul_smul, add_comm, neg_mul, neg_smul, smul_neg]
#align has_fderiv_at_polar_coord_symm hasFderivAtPolarCoordSymm

theorem polar_coord_source_ae_eq_univ : polarCoord.source =ᵐ[volume] univ :=
  by
  have A : polar_coord.sourceᶜ ⊆ (LinearMap.snd ℝ ℝ ℝ).ker :=
    by
    intro x hx
    simp only [polar_coord_source, compl_union, mem_inter_iff, mem_compl_iff, mem_set_of_eq, not_lt,
      not_not] at hx
    exact hx.2
  have B : volume ((LinearMap.snd ℝ ℝ ℝ).ker : Set (ℝ × ℝ)) = 0 :=
    by
    apply measure.add_haar_submodule
    rw [Ne.def, LinearMap.ker_eq_top]
    intro h
    have : (LinearMap.snd ℝ ℝ ℝ) (0, 1) = (0 : ℝ × ℝ →ₗ[ℝ] ℝ) (0, 1) := by rw [h]
    simpa using this
  simp only [ae_eq_univ]
  exact le_antisymm ((measure_mono A).trans (le_of_eq B)) bot_le
#align polar_coord_source_ae_eq_univ polar_coord_source_ae_eq_univ

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `«expr!![ » -/
/- ./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation -/
theorem integral_comp_polar_coord_symm {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ × ℝ → E) :
    (∫ p in polarCoord.target, p.1 • f (polarCoord.symm p)) = ∫ p, f p :=
  by
  set B : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ × ℝ := fun p =>
    (Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
        («expr!![ »
          "./././Mathport/Syntax/Translate/Expr.lean:390:14: unsupported user notation matrix.notation")).toContinuousLinearMap with
    hB
  have A : ∀ p ∈ polar_coord.symm.source, HasFderivAt polar_coord.symm (B p) p := fun p hp =>
    hasFderivAtPolarCoordSymm p
  have B_det : ∀ p, (B p).det = p.1 := by
    intro p
    conv_rhs => rw [← one_mul p.1, ← cos_sq_add_sin_sq p.2]
    simp only [neg_mul, LinearMap.det_to_continuous_linear_map, LinearMap.det_to_lin,
      Matrix.det_fin_two_of, sub_neg_eq_add]
    ring
  symm
  calc
    (∫ p, f p) = ∫ p in polar_coord.source, f p :=
      by
      rw [← integral_univ]
      apply set_integral_congr_set_ae
      exact polar_coord_source_ae_eq_univ.symm
    _ = ∫ p in polar_coord.target, abs (B p).det • f (polar_coord.symm p) := by
      apply integral_target_eq_integral_abs_det_fderiv_smul volume A
    _ = ∫ p in polar_coord.target, p.1 • f (polar_coord.symm p) :=
      by
      apply set_integral_congr polar_coord.open_target.measurable_set fun x hx => _
      rw [B_det, abs_of_pos]
      exact hx.1
    
#align integral_comp_polar_coord_symm integral_comp_polar_coord_symm

