/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser

! This file was ported from Lean 3 source module analysis.quaternion
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Quaternion
import Mathbin.Analysis.InnerProductSpace.Basic
import Mathbin.Analysis.InnerProductSpace.PiL2
import Mathbin.Topology.Algebra.Algebra

/-!
# Quaternions as a normed algebra

In this file we define the following structures on the space `ℍ := ℍ[ℝ]` of quaternions:

* inner product space;
* normed ring;
* normed space over `ℝ`.

We show that the norm on `ℍ[ℝ]` agrees with the euclidean norm of its components.

## Notation

The following notation is available with `open_locale quaternion`:

* `ℍ` : quaternions

## Tags

quaternion, normed ring, normed space, normed algebra
-/


-- mathport name: quaternion.real
scoped[Quaternion] notation "ℍ" => Quaternion ℝ

open RealInnerProductSpace

namespace Quaternion

instance : HasInner ℝ ℍ :=
  ⟨fun a b => (a * b.conj).re⟩

theorem inner_self (a : ℍ) : ⟪a, a⟫ = normSq a :=
  rfl
#align quaternion.inner_self Quaternion.inner_self

theorem inner_def (a b : ℍ) : ⟪a, b⟫ = (a * b.conj).re :=
  rfl
#align quaternion.inner_def Quaternion.inner_def

noncomputable instance : InnerProductSpace ℝ ℍ :=
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
  rw [norm_eq_sqrt_real_inner, inner_self, norm_sq_coe, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
#align quaternion.norm_coe Quaternion.norm_coe

@[simp, norm_cast]
theorem nnnorm_coe (a : ℝ) : ‖(a : ℍ)‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_coe a
#align quaternion.nnnorm_coe Quaternion.nnnorm_coe

@[simp]
theorem norm_conj (a : ℍ) : ‖conj a‖ = ‖a‖ := by
  simp_rw [norm_eq_sqrt_real_inner, inner_self, norm_sq_conj]
#align quaternion.norm_conj Quaternion.norm_conj

@[simp]
theorem nnnorm_conj (a : ℍ) : ‖conj a‖₊ = ‖a‖₊ :=
  Subtype.ext <| norm_conj a
#align quaternion.nnnorm_conj Quaternion.nnnorm_conj

noncomputable instance : NormedDivisionRing ℍ
    where
  dist_eq _ _ := rfl
  norm_mul' a b :=
    by
    simp only [norm_eq_sqrt_real_inner, inner_self, norm_sq.map_mul]
    exact Real.sqrt_mul norm_sq_nonneg _

instance : NormedAlgebra ℝ ℍ
    where
  norm_smul_le a x := (norm_smul a x).le
  toAlgebra := (Quaternion.algebra : Algebra ℝ ℍ)

instance : CstarRing ℍ
    where norm_star_mul_self x := (norm_mul _ _).trans <| congr_arg (· * ‖x‖) (norm_conj x)

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

/-- The norm of the components as a euclidean vector equals the norm of the quaternion. -/
theorem norm_piLp_equiv_symm_equivTuple (x : ℍ) :
    ‖(PiLp.equiv 2 fun _ : Fin 4 => _).symm (equivTuple ℝ x)‖ = ‖x‖ :=
  by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_self, norm_sq_def', PiLp.inner_apply,
    Fin.sum_univ_four]
  simp_rw [IsROrC.inner_apply, starRingEnd_apply, star_trivial, ← sq]
  rfl
#align quaternion.norm_pi_Lp_equiv_symm_equiv_tuple Quaternion.norm_piLp_equiv_symm_equivTuple

/-- `quaternion_algebra.linear_equiv_tuple` as a `linear_isometry_equiv`. -/
@[simps apply symm_apply]
noncomputable def linearIsometryEquivTuple : ℍ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  {
    (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) (-1 : ℝ)).trans
      (PiLp.linearEquiv 2 ℝ fun _ : Fin 4 =>
          ℝ).symm with
    toFun := fun a => (PiLp.equiv _ fun _ : Fin 4 => _).symm ![a.1, a.2, a.3, a.4]
    invFun := fun a => ⟨a 0, a 1, a 2, a 3⟩
    norm_map' := norm_piLp_equiv_symm_equivTuple }
#align quaternion.linear_isometry_equiv_tuple Quaternion.linearIsometryEquivTuple

@[continuity]
theorem continuous_conj : Continuous (conj : ℍ → ℍ) :=
  continuous_star
#align quaternion.continuous_conj Quaternion.continuous_conj

@[continuity]
theorem continuous_coe : Continuous (coe : ℝ → ℍ) :=
  continuous_algebraMap ℝ ℍ
#align quaternion.continuous_coe Quaternion.continuous_coe

@[continuity]
theorem continuous_normSq : Continuous (normSq : ℍ → ℝ) := by
  simpa [← norm_sq_eq_norm_sq] using
    (continuous_norm.mul continuous_norm : Continuous fun q : ℍ => ‖q‖ * ‖q‖)
#align quaternion.continuous_norm_sq Quaternion.continuous_normSq

@[continuity]
theorem continuous_re : Continuous fun q : ℍ => q.re :=
  (continuous_apply 0).comp linearIsometryEquivTuple.Continuous
#align quaternion.continuous_re Quaternion.continuous_re

@[continuity]
theorem continuous_imI : Continuous fun q : ℍ => q.imI :=
  (continuous_apply 1).comp linearIsometryEquivTuple.Continuous
#align quaternion.continuous_im_i Quaternion.continuous_imI

@[continuity]
theorem continuous_imJ : Continuous fun q : ℍ => q.imJ :=
  (continuous_apply 2).comp linearIsometryEquivTuple.Continuous
#align quaternion.continuous_im_j Quaternion.continuous_imJ

@[continuity]
theorem continuous_imK : Continuous fun q : ℍ => q.imK :=
  (continuous_apply 3).comp linearIsometryEquivTuple.Continuous
#align quaternion.continuous_im_k Quaternion.continuous_imK

instance : CompleteSpace ℍ :=
  haveI : UniformEmbedding linear_isometry_equiv_tuple.to_linear_equiv.to_equiv.symm :=
    linear_isometry_equiv_tuple.to_continuous_linear_equiv.symm.uniform_embedding
  (completeSpace_congr this).1 (by infer_instance)

end Quaternion

