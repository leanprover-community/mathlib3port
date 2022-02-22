/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
import Mathbin.LinearAlgebra.SpecialLinearGroup
import Mathbin.Analysis.Complex.Basic
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# The upper half plane and its automorphisms

This file defines `upper_half_plane` to be the upper half plane in `ℂ`.

We furthermore equip it with the structure of an `SL(2,ℝ)` action by
fractional linear transformations.

We define the notation `ℍ` for the upper half plane available in the locale
`upper_half_plane` so as not to conflict with the quaternions.
-/


noncomputable section

open Matrix Matrix.SpecialLinearGroup

open_locale Classical BigOperators MatrixGroups

attribute [local instance] Fintype.card_fin_even

/-- The open upper half plane -/
abbrev UpperHalfPlane :=
  { point : ℂ // 0 < point.im }

-- mathport name: «exprℍ»
localized [UpperHalfPlane] notation "ℍ" => UpperHalfPlane

namespace UpperHalfPlane

/-- Imaginary part -/
def im (z : ℍ) :=
  (z : ℂ).im

/-- Real part -/
def re (z : ℍ) :=
  (z : ℂ).re

@[simp]
theorem coe_im (z : ℍ) : (z : ℂ).im = z.im :=
  rfl

@[simp]
theorem coe_re (z : ℍ) : (z : ℂ).re = z.re :=
  rfl

theorem im_pos (z : ℍ) : 0 < z.im :=
  z.2

theorem im_ne_zero (z : ℍ) : z.im ≠ 0 :=
  z.im_pos.ne'

theorem ne_zero (z : ℍ) : (z : ℂ) ≠ 0 :=
  mt (congr_argₓ Complex.im) z.im_ne_zero

theorem norm_sq_pos (z : ℍ) : 0 < Complex.normSq (z : ℂ) := by
  rw [Complex.norm_sq_pos]
  exact z.ne_zero

theorem norm_sq_ne_zero (z : ℍ) : Complex.normSq (z : ℂ) ≠ 0 :=
  (norm_sq_pos z).ne'

/-- Numerator of the formula for a fractional linear transformation -/
@[simp]
def num (g : SL(2,ℝ)) (z : ℍ) : ℂ :=
  g 0 0 * z + g 0 1

/-- Denominator of the formula for a fractional linear transformation -/
@[simp]
def denom (g : SL(2,ℝ)) (z : ℍ) : ℂ :=
  g 1 0 * z + g 1 1

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:29:26: unsupported: too many args
theorem linear_ne_zero (cd : Finₓ 2 → ℝ) (z : ℍ) (h : cd ≠ 0) : (cd 0 : ℂ) * z + cd 1 ≠ 0 := by
  contrapose! h
  have : cd 0 = 0 := by
    -- we will need this twice
    apply_fun Complex.im  at h
    simpa only [z.im_ne_zero, Complex.add_im, add_zeroₓ, coe_im, zero_mul, or_falseₓ, Complex.of_real_im,
      Complex.zero_im, Complex.mul_im, mul_eq_zero] using h
  simp only [this, zero_mul, Complex.of_real_zero, zero_addₓ, Complex.of_real_eq_zero] at h
  ext i
  fin_cases i <;> assumption

theorem denom_ne_zero (g : SL(2,ℝ)) (z : ℍ) : denom g z ≠ 0 :=
  linear_ne_zero (g 1) z (g.row_ne_zero 1)

theorem norm_sq_denom_pos (g : SL(2,ℝ)) (z : ℍ) : 0 < Complex.normSq (denom g z) :=
  Complex.norm_sq_pos.mpr (denom_ne_zero g z)

theorem norm_sq_denom_ne_zero (g : SL(2,ℝ)) (z : ℍ) : Complex.normSq (denom g z) ≠ 0 :=
  ne_of_gtₓ (norm_sq_denom_pos g z)

/-- Fractional linear transformation -/
def smulAux' (g : SL(2,ℝ)) (z : ℍ) : ℂ :=
  num g z / denom g z

theorem smul_aux'_im (g : SL(2,ℝ)) (z : ℍ) : (smulAux' g z).im = z.im / (denom g z).normSq := by
  rw [smul_aux', Complex.div_im]
  set NsqBot := (denom g z).normSq
  have : NsqBot ≠ 0 := by
    simp only [denom_ne_zero g z, MonoidWithZeroHom.map_eq_zero, Ne.def, not_false_iff]
  field_simp [smul_aux']
  convert congr_argₓ (fun x => x * z.im * NsqBot ^ 2) g.det_coe using 1
  · rw [det_fin_two ↑g]
    ring
    
  · ring
    

/-- Fractional linear transformation -/
def smulAux (g : SL(2,ℝ)) (z : ℍ) : ℍ :=
  ⟨smulAux' g z, by
    rw [smul_aux'_im]
    exact div_pos z.im_pos (complex.norm_sq_pos.mpr (denom_ne_zero g z))⟩

theorem denom_cocycle (x y : SL(2,ℝ)) (z : ℍ) : denom (x * y) z = denom x (smulAux y z) * denom y z := by
  change _ = (_ * (_ / _) + _) * _
  field_simp [denom_ne_zero, -denom, -Num]
  simp [Matrix.mul, dot_product, Finₓ.sum_univ_succ]
  ring

theorem mul_smul' (x y : SL(2,ℝ)) (z : ℍ) : smulAux (x * y) z = smulAux x (smulAux y z) := by
  ext1
  change _ / _ = (_ * (_ / _) + _) * _
  rw [denom_cocycle]
  field_simp [denom_ne_zero, -denom, -Num]
  simp [Matrix.mul, dot_product, Finₓ.sum_univ_succ]
  ring

/-- The action of `SL(2, ℝ)` on the upper half-plane by fractional linear transformations. -/
instance : MulAction SL(2,ℝ) ℍ where
  smul := smulAux
  one_smul := fun z => by
    ext1
    change _ / _ = _
    simp
  mul_smul := mul_smul'

@[simp]
theorem coe_smul (g : SL(2,ℝ)) (z : ℍ) : ↑(g • z) = num g z / denom g z :=
  rfl

@[simp]
theorem re_smul (g : SL(2,ℝ)) (z : ℍ) : (g • z).re = (num g z / denom g z).re :=
  rfl

theorem im_smul (g : SL(2,ℝ)) (z : ℍ) : (g • z).im = (num g z / denom g z).im :=
  rfl

theorem im_smul_eq_div_norm_sq (g : SL(2,ℝ)) (z : ℍ) : (g • z).im = z.im / Complex.normSq (denom g z) :=
  smul_aux'_im g z

@[simp]
theorem neg_smul (g : SL(2,ℝ)) (z : ℍ) : -g • z = g • z := by
  ext1
  change _ / _ = _ / _
  field_simp [denom_ne_zero, -denom, -Num]
  simp
  ring

end UpperHalfPlane

