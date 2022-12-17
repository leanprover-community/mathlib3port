/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.free_algebra
! leanprover-community/mathlib commit 11bb0c9152e5d14278fb0ac5e0be6d50e2c8fa05
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Basis
import Mathbin.Algebra.FreeAlgebra
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!
# Linear algebra properties of `free_algebra R X`

This file provides a `free_monoid X` basis on the `free_algebra R X`, and uses it to show the
dimension of the algebra is the cardinality of `list X`
-/


universe u v

namespace FreeAlgebra

/-- The `free_monoid X` basis on the `free_algebra R X`,
mapping `[x₁, x₂, ..., xₙ]` to the "monomial" `1 • x₁ * x₂ * ⋯ * xₙ` -/
@[simps]
noncomputable def basisFreeMonoid (R : Type u) (X : Type v) [CommRing R] :
    Basis (FreeMonoid X) R (FreeAlgebra R X) :=
  Finsupp.basisSingleOne.map
    (equivMonoidAlgebraFreeMonoid.symm.toLinearEquiv : _ ≃ₗ[R] FreeAlgebra R X)
#align free_algebra.basis_free_monoid FreeAlgebra.basisFreeMonoid

-- TODO: generalize to `X : Type v`
theorem dim_eq {K : Type u} {X : Type max u v} [Field K] :
    Module.rank K (FreeAlgebra K X) = Cardinal.mk (List X) :=
  (Cardinal.lift_inj.mp (basisFreeMonoid K X).mk_eq_dim).symm
#align free_algebra.dim_eq FreeAlgebra.dim_eq

end FreeAlgebra

