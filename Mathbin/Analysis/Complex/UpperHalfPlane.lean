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


noncomputable theory

open Matrix Matrix.SpecialLinearGroup

open_locale Classical BigOperators MatrixGroups

attribute [local instance] Fintype.card_fin_even

/-- The open upper half plane -/
abbrev UpperHalfPlane :=
  { point : ℂ // 0 < point.im }

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

theorem norm_sq_pos (z : ℍ) : 0 < Complex.normSq (z : ℂ) :=
  by 
    rw [Complex.norm_sq_pos]
    exact z.ne_zero

theorem norm_sq_ne_zero (z : ℍ) : Complex.normSq (z : ℂ) ≠ 0 :=
  (norm_sq_pos z).ne'

/-- Numerator of the formula for a fractional linear transformation -/
@[simp]
def Num (g : SL(2,ℝ)) (z : ℍ) : ℂ :=
  (g 0 0*z)+g 0 1

/-- Denominator of the formula for a fractional linear transformation -/
@[simp]
def denom (g : SL(2,ℝ)) (z : ℍ) : ℂ :=
  (g 1 0*z)+g 1 1

-- error in Analysis.Complex.UpperHalfPlane: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_ne_zero
(cd : fin 2 → exprℝ())
(z : exprℍ())
(h : «expr ≠ »(cd, 0)) : «expr ≠ »(«expr + »(«expr * »((cd 0 : exprℂ()), z), cd 1), 0) :=
begin
  contrapose ["!"] [ident h],
  have [] [":", expr «expr = »(cd 0, 0)] [],
  { apply_fun [expr complex.im] ["at", ident h] [],
    simpa [] [] ["only"] ["[", expr z.im_ne_zero, ",", expr complex.add_im, ",", expr add_zero, ",", expr coe_im, ",", expr zero_mul, ",", expr or_false, ",", expr complex.of_real_im, ",", expr complex.zero_im, ",", expr complex.mul_im, ",", expr mul_eq_zero, "]"] [] ["using", expr h] },
  simp [] [] ["only"] ["[", expr this, ",", expr zero_mul, ",", expr complex.of_real_zero, ",", expr zero_add, ",", expr complex.of_real_eq_zero, "]"] [] ["at", ident h],
  ext [] [ident i] [],
  fin_cases [ident i] []; assumption
end

theorem denom_ne_zero (g : SL(2,ℝ)) (z : ℍ) : denom g z ≠ 0 :=
  linear_ne_zero (g 1) z (g.row_ne_zero 1)

theorem norm_sq_denom_pos (g : SL(2,ℝ)) (z : ℍ) : 0 < Complex.normSq (denom g z) :=
  Complex.norm_sq_pos.mpr (denom_ne_zero g z)

theorem norm_sq_denom_ne_zero (g : SL(2,ℝ)) (z : ℍ) : Complex.normSq (denom g z) ≠ 0 :=
  ne_of_gtₓ (norm_sq_denom_pos g z)

/-- Fractional linear transformation -/
def smul_aux' (g : SL(2,ℝ)) (z : ℍ) : ℂ :=
  Num g z / denom g z

-- error in Analysis.Complex.UpperHalfPlane: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem smul_aux'_im
(g : «exprSL( , )»(2, exprℝ()))
(z : exprℍ()) : «expr = »((smul_aux' g z).im, «expr / »(z.im, (denom g z).norm_sq)) :=
begin
  rw ["[", expr smul_aux', ",", expr complex.div_im, "]"] [],
  set [] [ident NsqBot] [] [":="] [expr (denom g z).norm_sq] [],
  have [] [":", expr «expr ≠ »(NsqBot, 0)] [],
  { simp [] [] ["only"] ["[", expr denom_ne_zero g z, ",", expr monoid_with_zero_hom.map_eq_zero, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [] },
  field_simp [] ["[", expr smul_aux', "]"] [] [],
  convert [] [expr congr_arg (λ x, «expr * »(«expr * »(x, z.im), «expr ^ »(NsqBot, 2))) g.det_coe] ["using", 1],
  { rw [expr det_fin_two «expr↑ »(g)] [],
    ring [] },
  { ring [] }
end

/-- Fractional linear transformation -/
def smul_aux (g : SL(2,ℝ)) (z : ℍ) : ℍ :=
  ⟨smul_aux' g z,
    by 
      rw [smul_aux'_im]
      exact div_pos z.im_pos (complex.norm_sq_pos.mpr (denom_ne_zero g z))⟩

theorem denom_cocycle (x y : SL(2,ℝ)) (z : ℍ) : denom (x*y) z = denom x (smul_aux y z)*denom y z :=
  by 
    change _ = ((_*_ / _)+_)*_ 
    fieldSimp [denom_ne_zero, -denom, -Num]
    simp [Matrix.mul, dot_product, Finₓ.sum_univ_succ]
    ring

theorem mul_smul' (x y : SL(2,ℝ)) (z : ℍ) : smul_aux (x*y) z = smul_aux x (smul_aux y z) :=
  by 
    ext1 
    change _ / _ = ((_*_ / _)+_)*_ 
    rw [denom_cocycle]
    fieldSimp [denom_ne_zero, -denom, -Num]
    simp [Matrix.mul, dot_product, Finₓ.sum_univ_succ]
    ring

/-- The action of `SL(2, ℝ)` on the upper half-plane by fractional linear transformations. -/
instance  : MulAction SL(2,ℝ) ℍ :=
  { smul := smul_aux,
    one_smul :=
      fun z =>
        by 
          ext1 
          change _ / _ = _ 
          simp ,
    mul_smul := mul_smul' }

@[simp]
theorem coe_smul (g : SL(2,ℝ)) (z : ℍ) : «expr↑ » (g • z) = Num g z / denom g z :=
  rfl

@[simp]
theorem re_smul (g : SL(2,ℝ)) (z : ℍ) : (g • z).re = (Num g z / denom g z).re :=
  rfl

theorem im_smul (g : SL(2,ℝ)) (z : ℍ) : (g • z).im = (Num g z / denom g z).im :=
  rfl

theorem im_smul_eq_div_norm_sq (g : SL(2,ℝ)) (z : ℍ) : (g • z).im = z.im / Complex.normSq (denom g z) :=
  smul_aux'_im g z

@[simp]
theorem neg_smul (g : SL(2,ℝ)) (z : ℍ) : -g • z = g • z :=
  by 
    ext1 
    change _ / _ = _ / _ 
    fieldSimp [denom_ne_zero, -denom, -Num]
    simp 
    ring

end UpperHalfPlane

