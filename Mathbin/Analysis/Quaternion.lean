/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.quaternion
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Quaternion
import Mathbin.Analysis.InnerProductSpace.Basic

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

## Notation

The following notation is available with `open_locale quaternion`:

* `ℍ` : quaternions

## Tags

quaternion, normed ring, normed space, normed algebra
-/


-- mathport name: quaternion.real
scoped[Quaternion] notation "ℍ" => Quaternion ℝ

open RealInnerProductSpace

noncomputable section

namespace Quaternion

instance : HasInner ℝ ℍ :=
  ⟨fun a b => (a * b.conj).re⟩

theorem inner_self (a : ℍ) : ⟪a, a⟫ = normSq a :=
  rfl
#align quaternion.inner_self Quaternion.inner_self

theorem inner_def (a b : ℍ) : ⟪a, b⟫ = (a * b.conj).re :=
  rfl
#align quaternion.inner_def Quaternion.inner_def

instance : InnerProductSpace ℝ ℍ :=
  InnerProductSpace.ofCore
    { inner := HasInner.inner
      conj_sym := fun x y => by simp [inner_def, mul_comm]
      nonneg_re := fun x => normSq_nonneg
      definite := fun x => normSq_eq_zero.1
      add_left := fun x y z => by simp only [inner_def, add_mul, add_re]
      smul_left := fun x y r => by simp [inner_def] }

theorem normSq_eq_normSq (a : ℍ) : normSq a = ‖a‖ * ‖a‖ := by
  rw [← inner_self, real_inner_self_eq_norm_mul_norm]
#align quaternion.norm_sq_eq_norm_sq Quaternion.normSq_eq_normSq

instance : NormOneClass ℍ :=
  ⟨by rw [norm_eq_sqrt_real_inner, inner_self, norm_sq.map_one, Real.sqrt_one]⟩

@[simp, norm_cast]
theorem norm_coe (a : ℝ) : ‖(a : ℍ)‖ = ‖a‖ := by
  rw [norm_eq_sqrt_real_inner, inner_self, normSq_coe, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
#align quaternion.norm_coe Quaternion.norm_coe

@[simp, norm_cast]
theorem nnnorm_coe (a : ℝ) : ‖(a : ℍ)‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_coe a
#align quaternion.nnnorm_coe Quaternion.nnnorm_coe

noncomputable instance : NormedDivisionRing ℍ
    where
  dist_eq _ _ := rfl
  norm_mul' a b :=
    by
    simp only [norm_eq_sqrt_real_inner, inner_self, norm_sq.map_mul]
    exact Real.sqrt_mul normSq_nonneg _

noncomputable instance : NormedAlgebra ℝ ℍ
    where
  norm_smul_le a x := (norm_smul a x).le
  toAlgebra := Quaternion.algebra

instance : Coe ℂ ℍ :=
  ⟨fun z => ⟨z.re, z.im, 0, 0⟩⟩

@[simp, norm_cast]
theorem coe_complex_re (z : ℂ) : (z : ℍ).re = z.re :=
  rfl
#align quaternion.coe_complex_re Quaternion.coe_complex_re

@[simp, norm_cast]
theorem coe_complex_imI (z : ℂ) : (z : ℍ).imI = z.im :=
  rfl
#align quaternion.coe_complex_im_i Quaternion.coe_complex_imI

@[simp, norm_cast]
theorem coe_complex_imJ (z : ℂ) : (z : ℍ).imJ = 0 :=
  rfl
#align quaternion.coe_complex_im_j Quaternion.coe_complex_imJ

@[simp, norm_cast]
theorem coe_complex_imK (z : ℂ) : (z : ℍ).imK = 0 :=
  rfl
#align quaternion.coe_complex_im_k Quaternion.coe_complex_imK

@[simp, norm_cast]
theorem coe_complex_add (z w : ℂ) : ↑(z + w) = (z + w : ℍ) := by ext <;> simp
#align quaternion.coe_complex_add Quaternion.coe_complex_add

@[simp, norm_cast]
theorem coe_complex_mul (z w : ℂ) : ↑(z * w) = (z * w : ℍ) := by ext <;> simp
#align quaternion.coe_complex_mul Quaternion.coe_complex_mul

@[simp, norm_cast]
theorem coe_complex_zero : ((0 : ℂ) : ℍ) = 0 :=
  rfl
#align quaternion.coe_complex_zero Quaternion.coe_complex_zero

@[simp, norm_cast]
theorem coe_complex_one : ((1 : ℂ) : ℍ) = 1 :=
  rfl
#align quaternion.coe_complex_one Quaternion.coe_complex_one

@[simp, norm_cast]
theorem coe_real_complex_mul (r : ℝ) (z : ℂ) : (r • z : ℍ) = ↑r * ↑z := by ext <;> simp
#align quaternion.coe_real_complex_mul Quaternion.coe_real_complex_mul

@[simp, norm_cast]
theorem coe_complex_coe (r : ℝ) : ((r : ℂ) : ℍ) = r :=
  rfl
#align quaternion.coe_complex_coe Quaternion.coe_complex_coe

/-- Coercion `ℂ →ₐ[ℝ] ℍ` as an algebra homomorphism. -/
def ofComplex : ℂ →ₐ[ℝ] ℍ where
  toFun := coe
  map_one' := rfl
  map_zero' := rfl
  map_add' := coe_complex_add
  map_mul' := coe_complex_mul
  commutes' x := rfl
#align quaternion.of_complex Quaternion.ofComplex

@[simp]
theorem coe_ofComplex : ⇑ofComplex = coe :=
  rfl
#align quaternion.coe_of_complex Quaternion.coe_ofComplex

end Quaternion

