/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Eric Wieser
-/
import LinearAlgebra.QuadraticForm.Basic

#align_import linear_algebra.quadratic_form.isometry from "leanprover-community/mathlib"@"c20927220ef87bb4962ba08bf6da2ce3cf50a6dd"

/-!
# Isometries with respect to quadratic forms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `quadratic_form.isometry`: `linear_equiv`s which map between two different quadratic forms
* `quadratic_form.equvialent`: propositional version of the above

## Main results

* `equivalent_weighted_sum_squares`: in finite dimensions, any quadratic form is equivalent to a
  parametrization of `quadratic_form.weighted_sum_squares`.
-/


variable {ι R K M M₁ M₂ M₃ V : Type _}

namespace QuadraticMap

variable [Semiring R]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃]

/-- An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic forms. -/
@[nolint has_nonempty_instance]
structure IsometryEquiv (Q₁ : QuadraticMap R M₁) (Q₂ : QuadraticMap R M₂) extends M₁ ≃ₗ[R] M₂ where
  map_app' : ∀ m, Q₂ (to_fun m) = Q₁ m
#align quadratic_form.isometry QuadraticMap.IsometryEquivₓ

#print QuadraticMap.Equivalent /-
/-- Two quadratic forms over a ring `R` are equivalent
if there exists an isometry between them:
a linear equivalence that transforms one quadratic form into the other. -/
def Equivalent (Q₁ : QuadraticMap R M₁) (Q₂ : QuadraticMap R M₂) :=
  Nonempty (Q₁.IsometryEquivₓ Q₂)
#align quadratic_form.equivalent QuadraticMap.Equivalent
-/

namespace Isometry

variable {Q₁ : QuadraticMap R M₁} {Q₂ : QuadraticMap R M₂} {Q₃ : QuadraticMap R M₃}

instance : Coe (Q₁.IsometryEquivₓ Q₂) (M₁ ≃ₗ[R] M₂) :=
  ⟨IsometryEquiv.toLinearEquiv⟩

@[simp]
theorem toLinearEquiv_eq_coe (f : Q₁.IsometryEquivₓ Q₂) : f.toLinearEquiv = f :=
  rfl
#align quadratic_form.isometry.to_linear_equiv_eq_coe QuadraticMap.IsometryEquivₓ.toLinearEquiv_eq_coe

instance : CoeFun (Q₁.IsometryEquivₓ Q₂) fun _ => M₁ → M₂ :=
  ⟨fun f => ⇑(f : M₁ ≃ₗ[R] M₂)⟩

#print QuadraticMap.IsometryEquiv.coe_toLinearEquiv /-
@[simp]
theorem coe_toLinearEquiv (f : Q₁.IsometryEquivₓ Q₂) : ⇑(f : M₁ ≃ₗ[R] M₂) = f :=
  rfl
#align quadratic_form.isometry.coe_to_linear_equiv QuadraticMap.IsometryEquiv.coe_toLinearEquiv
-/

#print QuadraticMap.IsometryEquiv.map_app /-
@[simp]
theorem map_app (f : Q₁.IsometryEquivₓ Q₂) (m : M₁) : Q₂ (f m) = Q₁ m :=
  f.map_app' m
#align quadratic_form.isometry.map_app QuadraticMap.IsometryEquiv.map_app
-/

#print QuadraticMap.IsometryEquiv.refl /-
/-- The identity isometry from a quadratic form to itself. -/
@[refl]
def refl (Q : QuadraticMap R M) : Q.IsometryEquivₓ Q :=
  { LinearEquiv.refl R M with map_app' := fun m => rfl }
#align quadratic_form.isometry.refl QuadraticMap.IsometryEquiv.refl
-/

#print QuadraticMap.IsometryEquiv.symm /-
/-- The inverse isometry of an isometry between two quadratic forms. -/
@[symm]
def symm (f : Q₁.IsometryEquivₓ Q₂) : Q₂.IsometryEquivₓ Q₁ :=
  { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' := by intro m; rw [← f.map_app]; congr; exact f.to_linear_equiv.apply_symm_apply m }
#align quadratic_form.isometry.symm QuadraticMap.IsometryEquiv.symm
-/

#print QuadraticMap.IsometryEquiv.trans /-
/-- The composition of two isometries between quadratic forms. -/
@[trans]
def trans (f : Q₁.IsometryEquivₓ Q₂) (g : Q₂.IsometryEquivₓ Q₃) : Q₁.IsometryEquivₓ Q₃ :=
  { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' := by intro m; rw [← f.map_app, ← g.map_app]; rfl }
#align quadratic_form.isometry.trans QuadraticMap.IsometryEquiv.trans
-/

end Isometry

namespace Equivalent

variable {Q₁ : QuadraticMap R M₁} {Q₂ : QuadraticMap R M₂} {Q₃ : QuadraticMap R M₃}

#print QuadraticMap.Equivalent.refl /-
@[refl]
theorem refl (Q : QuadraticMap R M) : Q.Equivalent Q :=
  ⟨IsometryEquiv.refl Q⟩
#align quadratic_form.equivalent.refl QuadraticMap.Equivalent.refl
-/

#print QuadraticMap.Equivalent.symm /-
@[symm]
theorem symm (h : Q₁.Equivalent Q₂) : Q₂.Equivalent Q₁ :=
  h.elim fun f => ⟨f.symm⟩
#align quadratic_form.equivalent.symm QuadraticMap.Equivalent.symm
-/

#print QuadraticMap.Equivalent.trans /-
@[trans]
theorem trans (h : Q₁.Equivalent Q₂) (h' : Q₂.Equivalent Q₃) : Q₁.Equivalent Q₃ :=
  h'.elim <| h.elim fun f g => ⟨f.trans g⟩
#align quadratic_form.equivalent.trans QuadraticMap.Equivalent.trans
-/

end Equivalent

variable [Fintype ι] {v : Basis ι R M}

#print QuadraticMap.isometryEquivOfCompLinearEquiv /-
/-- A quadratic form composed with a `linear_equiv` is isometric to itself. -/
def isometryEquivOfCompLinearEquiv (Q : QuadraticMap R M) (f : M₁ ≃ₗ[R] M) :
    Q.IsometryEquivₓ (Q.comp (f : M₁ →ₗ[R] M)) :=
  { f.symm with
    map_app' := by
      intro
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe,
        LinearEquiv.apply_symm_apply, f.apply_symm_apply] }
#align quadratic_form.isometry_of_comp_linear_equiv QuadraticMap.isometryEquivOfCompLinearEquiv
-/

#print QuadraticMap.isometryEquivBasisRepr /-
/-- A quadratic form is isometric to its bases representations. -/
noncomputable def isometryEquivBasisRepr (Q : QuadraticMap R M) (v : Basis ι R M) :
    IsometryEquiv Q (Q.basis_repr v) :=
  isometryEquivOfCompLinearEquiv Q v.equivFun.symm
#align quadratic_form.isometry_basis_repr QuadraticMap.isometryEquivBasisRepr
-/

variable [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]

#print QuadraticForm.isometryEquivWeightedSumSquares /-
/-- Given an orthogonal basis, a quadratic form is isometric with a weighted sum of squares. -/
noncomputable def isometryEquivWeightedSumSquares (Q : QuadraticMap K V)
    (v : Basis (Fin (FiniteDimensional.finrank K V)) K V) (hv₁ : (associated Q).IsOrthoᵢ v) :
    Q.IsometryEquivₓ (weightedSumSquares K fun i => Q (v i)) :=
  by
  let iso := Q.isometry_basis_repr v
  refine' ⟨iso, fun m => _⟩
  convert iso.map_app m
  rw [basis_repr_eq_of_is_Ortho _ _ hv₁]
#align quadratic_form.isometry_weighted_sum_squares QuadraticForm.isometryEquivWeightedSumSquares
-/

variable [FiniteDimensional K V]

open BilinForm

#print QuadraticForm.equivalent_weightedSumSquares /-
theorem equivalent_weightedSumSquares (Q : QuadraticMap K V) :
    ∃ w : Fin (FiniteDimensional.finrank K V) → K, Equivalent Q (weightedSumSquares K w) :=
  let ⟨v, hv₁⟩ := LinearMap.BilinForm.exists_orthogonal_basis (associated_isSymm _ Q)
  ⟨_, ⟨Q.isometryEquivWeightedSumSquares v hv₁⟩⟩
#align quadratic_form.equivalent_weighted_sum_squares QuadraticForm.equivalent_weightedSumSquares
-/

#print QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' /-
theorem equivalent_weightedSumSquares_units_of_nondegenerate' (Q : QuadraticMap K V)
    (hQ : (associated Q).Nondegenerate) :
    ∃ w : Fin (FiniteDimensional.finrank K V) → Kˣ, Equivalent Q (weightedSumSquares K w) :=
  by
  obtain ⟨v, hv₁⟩ := exists_orthogonal_basis (associated_is_symm _ Q)
  have hv₂ := hv₁.not_is_ortho_basis_self_of_nondegenerate hQ
  simp_rw [is_ortho, associated_eq_self_apply] at hv₂
  exact ⟨fun i => Units.mk0 _ (hv₂ i), ⟨Q.isometry_weighted_sum_squares v hv₁⟩⟩
#align quadratic_form.equivalent_weighted_sum_squares_units_of_nondegenerate' QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'
-/

end QuadraticMap

