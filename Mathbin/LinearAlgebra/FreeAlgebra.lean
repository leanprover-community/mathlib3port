/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.Basis
import Mathbin.Algebra.FreeAlgebra
import Mathbin.LinearAlgebra.Dimension
import Mathbin.LinearAlgebra.FinsuppVectorSpace

#align_import linear_algebra.free_algebra from "leanprover-community/mathlib"@"814d76e2247d5ba8bc024843552da1278bfe9e5c"

/-!
# Linear algebra properties of `free_algebra R X`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides a `free_monoid X` basis on the `free_algebra R X`, and uses it to show the
dimension of the algebra is the cardinality of `list X`
-/


universe u v

namespace FreeAlgebra

#print FreeAlgebra.basisFreeMonoid /-
/-- The `free_monoid X` basis on the `free_algebra R X`,
mapping `[x₁, x₂, ..., xₙ]` to the "monomial" `1 • x₁ * x₂ * ⋯ * xₙ` -/
@[simps]
noncomputable def basisFreeMonoid (R : Type u) (X : Type v) [CommRing R] :
    Basis (FreeMonoid X) R (FreeAlgebra R X) :=
  Finsupp.basisSingleOne.map
    (equivMonoidAlgebraFreeMonoid.symm.toLinearEquiv : _ ≃ₗ[R] FreeAlgebra R X)
#align free_algebra.basis_free_monoid FreeAlgebra.basisFreeMonoid
-/

#print FreeAlgebra.rank_eq /-
-- TODO: generalize to `X : Type v`
theorem rank_eq {K : Type u} {X : Type max u v} [Field K] :
    Module.rank K (FreeAlgebra K X) = Cardinal.mk (List X) :=
  (Cardinal.lift_inj.mp (basisFreeMonoid K X).mk_eq_rank).symm
#align free_algebra.rank_eq FreeAlgebra.rank_eq
-/

end FreeAlgebra

