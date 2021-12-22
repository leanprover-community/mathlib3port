import Mathbin.Algebra.Module.LinearMap
import Mathbin.LinearAlgebra.BilinearMap

/-!
# Sesquilinear form

This file defines a sesquilinear form over a module. The definition requires a ring antiautomorphism
on the scalar ring. Basic ideas such as
orthogonality are also introduced.

A sesquilinear form on an `R`-module `M`, is a function from `M × M` to `R`, that is linear in the
first argument and antilinear in the second, with respect to an antiautomorphism on `R` (an
antiisomorphism from `R` to `R`).

## Notations

Given any term `S` of type `sesq_form`, due to a coercion, can use the notation `S x y` to
refer to the function field, ie. `S x y = S.sesq x y`.

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form,
-/


open_locale BigOperators

namespace LinearMap

section CommRingₓ

variable {R : Type _} {M : Type _} [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] {I : R →+* R}

/--  The proposition that two elements of a sesquilinear form space are orthogonal -/
def is_ortho (B : M →ₗ[R] M →ₛₗ[I] R) x y : Prop :=
  B x y = 0

theorem is_ortho_def {B : M →ₗ[R] M →ₛₗ[I] R} {x y : M} : B.is_ortho x y ↔ B x y = 0 :=
  Iff.rfl

theorem is_ortho_zero_left (B : M →ₗ[R] M →ₛₗ[I] R) x : is_ortho B (0 : M) x := by
  dunfold is_ortho
  rw [map_zero B, zero_apply]

theorem is_ortho_zero_right (B : M →ₗ[R] M →ₛₗ[I] R) x : is_ortho B x (0 : M) :=
  map_zero (B x)

end CommRingₓ

section IsDomain

variable {R : Type _} {M : Type _} [CommRingₓ R] [IsDomain R] [AddCommGroupₓ M] [Module R M] {I : R ≃+* R}
  {B : M →ₗ[R] M →ₛₗ[I.to_ring_hom] R}

theorem ortho_smul_left {x y} {a : R} (ha : a ≠ 0) : is_ortho B x y ↔ is_ortho B (a • x) y := by
  dunfold is_ortho
  constructor <;> intro H
  ·
    rw [map_smul, smul_apply, H, smul_zero]
  ·
    rw [map_smul, smul_apply, smul_eq_zero] at H
    cases H
    ·
      trivial
    ·
      exact H

theorem ortho_smul_right {x y} {a : R} {ha : a ≠ 0} : is_ortho B x y ↔ is_ortho B x (a • y) := by
  dunfold is_ortho
  constructor <;> intro H
  ·
    rw [map_smulₛₗ, H, smul_zero]
  ·
    rw [map_smulₛₗ, smul_eq_zero] at H
    cases H
    ·
      rw [RingEquiv.to_ring_hom_eq_coe, RingEquiv.coe_to_ring_hom] at H
      exfalso
      exact ha (I.map_eq_zero_iff.mp H)
    ·
      exact H

end IsDomain

variable {R : Type _} {M : Type _} [CommRingₓ R] [AddCommGroupₓ M] [Module R M] {I : R →+* R} {B : M →ₗ[R] M →ₛₗ[I] R}

/--  The proposition that a sesquilinear form is reflexive -/
def IsRefl (B : M →ₗ[R] M →ₛₗ[I] R) : Prop :=
  ∀ x y, B x y = 0 → B y x = 0

namespace IsRefl

variable (H : B.is_refl)

theorem eq_zero : ∀ {x y}, B x y = 0 → B y x = 0 := fun x y => H x y

theorem ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x :=
  ⟨eq_zero H, eq_zero H⟩

end IsRefl

/--  The proposition that a sesquilinear form is symmetric -/
def IsSymm (B : M →ₗ[R] M →ₛₗ[I] R) : Prop :=
  ∀ x y, I (B x y) = B y x

namespace IsSymm

variable (H : B.is_symm)

include H

protected theorem Eq x y : I (B x y) = B y x :=
  H x y

theorem IsRefl : B.is_refl := fun x y H1 => by
  rw [← H]
  simp [H1]

theorem ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x :=
  H.is_refl.ortho_comm

end IsSymm

/--  The proposition that a sesquilinear form is alternating -/
def is_alt (B : M →ₗ[R] M →ₛₗ[I] R) : Prop :=
  ∀ x : M, B x x = 0

namespace IsAlt

variable (H : B.is_alt)

include H

theorem self_eq_zero x : B x x = 0 :=
  H x

theorem neg x y : -B x y = B y x := by
  have H1 : B (y+x) (y+x) = 0 := by
    exact self_eq_zero H (y+x)
  simp [map_add, self_eq_zero H] at H1
  rw [add_eq_zero_iff_neg_eq] at H1
  exact H1

theorem IsRefl : B.is_refl := by
  intro x y h
  rw [← neg H, h, neg_zero]

theorem ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x :=
  H.is_refl.ortho_comm

end IsAlt

end LinearMap

