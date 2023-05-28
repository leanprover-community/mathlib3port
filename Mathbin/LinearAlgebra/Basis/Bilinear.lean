/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll

! This file was ported from Lean 3 source module linear_algebra.basis.bilinear
! leanprover-community/mathlib commit 832f7b9162039c28b9361289c8681f155cae758f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Basis
import Mathbin.LinearAlgebra.BilinearMap

/-!
# Lemmas about bilinear maps with a basis over each argument

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace LinearMap

variable {ι₁ ι₂ : Type _}

variable {R R₂ S S₂ M N P : Type _}

variable {Mₗ Nₗ Pₗ : Type _}

variable [CommSemiring R] [CommSemiring S] [CommSemiring R₂] [CommSemiring S₂]

section AddCommMonoid

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [AddCommMonoid Mₗ] [AddCommMonoid Nₗ] [AddCommMonoid Pₗ]

variable [Module R M] [Module S N] [Module R₂ P] [Module S₂ P]

variable [Module R Mₗ] [Module R Nₗ] [Module R Pₗ]

variable [SMulCommClass S₂ R₂ P]

variable {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}

variable (b₁ : Basis ι₁ R M) (b₂ : Basis ι₂ S N) (b₁' : Basis ι₁ R Mₗ) (b₂' : Basis ι₂ R Nₗ)

/- warning: linear_map.ext_basis -> LinearMap.ext_basis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.ext_basis LinearMap.ext_basisₓ'. -/
/-- Two bilinear maps are equal when they are equal on all basis vectors. -/
theorem ext_basis {B B' : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (h : ∀ i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)) :
    B = B' :=
  b₁.ext fun i => b₂.ext fun j => h i j
#align linear_map.ext_basis LinearMap.ext_basis

/- warning: linear_map.sum_repr_mul_repr_mulₛₗ -> LinearMap.sum_repr_mul_repr_mulₛₗ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.sum_repr_mul_repr_mulₛₗ LinearMap.sum_repr_mul_repr_mulₛₗₓ'. -/
/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.

Version for semi-bilinear maps, see `sum_repr_mul_repr_mul` for the bilinear version. -/
theorem sum_repr_mul_repr_mulₛₗ {B : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (x y) :
    ((b₁.repr x).Sum fun i xi => (b₂.repr y).Sum fun j yj => ρ₁₂ xi • σ₁₂ yj • B (b₁ i) (b₂ j)) =
      B x y :=
  by
  conv_rhs => rw [← b₁.total_repr x, ← b₂.total_repr y]
  simp_rw [Finsupp.total_apply, Finsupp.sum, map_sum₂, map_sum, LinearMap.map_smulₛₗ₂,
    LinearMap.map_smulₛₗ]
#align linear_map.sum_repr_mul_repr_mulₛₗ LinearMap.sum_repr_mul_repr_mulₛₗ

/- warning: linear_map.sum_repr_mul_repr_mul -> LinearMap.sum_repr_mul_repr_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.sum_repr_mul_repr_mul LinearMap.sum_repr_mul_repr_mulₓ'. -/
/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.

Version for bilinear maps, see `sum_repr_mul_repr_mulₛₗ` for the semi-bilinear version. -/
theorem sum_repr_mul_repr_mul {B : Mₗ →ₗ[R] Nₗ →ₗ[R] Pₗ} (x y) :
    ((b₁'.repr x).Sum fun i xi => (b₂'.repr y).Sum fun j yj => xi • yj • B (b₁' i) (b₂' j)) =
      B x y :=
  by
  conv_rhs => rw [← b₁'.total_repr x, ← b₂'.total_repr y]
  simp_rw [Finsupp.total_apply, Finsupp.sum, map_sum₂, map_sum, LinearMap.map_smul₂,
    LinearMap.map_smul]
#align linear_map.sum_repr_mul_repr_mul LinearMap.sum_repr_mul_repr_mul

end AddCommMonoid

end LinearMap

