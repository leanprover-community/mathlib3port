/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.free_algebra
! leanprover-community/mathlib commit 814d76e2247d5ba8bc024843552da1278bfe9e5c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Basis
import Mathbin.Algebra.FreeAlgebra
import Mathbin.LinearAlgebra.Dimension
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!
# Linear algebra properties of `free_algebra R X`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides a `free_monoid X` basis on the `free_algebra R X`, and uses it to show the
dimension of the algebra is the cardinality of `list X`
-/


universe u v

namespace FreeAlgebra

/- warning: free_algebra.basis_free_monoid -> FreeAlgebra.basisFreeMonoid is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (X : Type.{u2}) [_inst_1 : CommRing.{u1} R], Basis.{u2, u1, max u1 u2} (FreeMonoid.{u2} X) R (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{max u1 u2} (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (NonUnitalNonAssocRing.toAddCommGroup.{max u1 u2} (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (NonAssocRing.toNonUnitalNonAssocRing.{max u1 u2} (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (Ring.toNonAssocRing.{max u1 u2} (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (FreeAlgebra.ring.{u2, u1} X R _inst_1))))) (Algebra.toModule.{u1, max u1 u2} R (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (CommRing.toCommSemiring.{u1} R _inst_1) (FreeAlgebra.semiring.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (FreeAlgebra.algebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X))
but is expected to have type
  forall (R : Type.{u1}) (X : Type.{u2}) [_inst_1 : CommRing.{u1} R], Basis.{u2, u1, max u2 u1} (FreeMonoid.{u2} X) R (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u1 u2} (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{max u1 u2} (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (NonAssocRing.toNonUnitalNonAssocRing.{max u1 u2} (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (Ring.toNonAssocRing.{max u1 u2} (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (FreeAlgebra.instRingFreeAlgebraToCommSemiring.{u2, u1} X R _inst_1))))) (Algebra.toModule.{u1, max u1 u2} R (FreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (CommRing.toCommSemiring.{u1} R _inst_1) (FreeAlgebra.instSemiringFreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X) (FreeAlgebra.instAlgebraFreeAlgebraInstSemiringFreeAlgebra.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) X))
Case conversion may be inaccurate. Consider using '#align free_algebra.basis_free_monoid FreeAlgebra.basisFreeMonoidₓ'. -/
/-- The `free_monoid X` basis on the `free_algebra R X`,
mapping `[x₁, x₂, ..., xₙ]` to the "monomial" `1 • x₁ * x₂ * ⋯ * xₙ` -/
@[simps]
noncomputable def basisFreeMonoid (R : Type u) (X : Type v) [CommRing R] :
    Basis (FreeMonoid X) R (FreeAlgebra R X) :=
  Finsupp.basisSingleOne.map
    (equivMonoidAlgebraFreeMonoid.symm.toLinearEquiv : _ ≃ₗ[R] FreeAlgebra R X)
#align free_algebra.basis_free_monoid FreeAlgebra.basisFreeMonoid

/- warning: free_algebra.rank_eq -> FreeAlgebra.rank_eq is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {X : Type.{max u1 u2}} [_inst_1 : Field.{u1} K], Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Module.rank.{u1, max u1 u2} K (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))) (AddCommGroup.toAddCommMonoid.{max u1 u2} (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (NonUnitalNonAssocRing.toAddCommGroup.{max u1 u2} (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (NonAssocRing.toNonUnitalNonAssocRing.{max u1 u2} (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (Ring.toNonAssocRing.{max u1 u2} (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (FreeAlgebra.ring.{max u1 u2, u1} X K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_1))))))) (Algebra.toModule.{u1, max u1 u2} K (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) (FreeAlgebra.semiring.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (FreeAlgebra.algebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X))) (Cardinal.mk.{max u1 u2} (List.{max u1 u2} X))
but is expected to have type
  forall {K : Type.{u1}} {X : Type.{max u1 u2}} [_inst_1 : Field.{u1} K], Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Module.rank.{u1, max u1 u2} K (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u1 u2} (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{max u1 u2} (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (NonAssocRing.toNonUnitalNonAssocRing.{max u1 u2} (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (Ring.toNonAssocRing.{max u1 u2} (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (FreeAlgebra.instRingFreeAlgebraToCommSemiring.{max u1 u2, u1} X K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_1))))))) (Algebra.toModule.{u1, max u1 u2} K (FreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) (FreeAlgebra.instSemiringFreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X) (FreeAlgebra.instAlgebraFreeAlgebraInstSemiringFreeAlgebra.{u1, max u1 u2} K (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_1)) X))) (Cardinal.mk.{max u1 u2} (List.{max u1 u2} X))
Case conversion may be inaccurate. Consider using '#align free_algebra.rank_eq FreeAlgebra.rank_eqₓ'. -/
-- TODO: generalize to `X : Type v`
theorem rank_eq {K : Type u} {X : Type max u v} [Field K] :
    Module.rank K (FreeAlgebra K X) = Cardinal.mk (List X) :=
  (Cardinal.lift_inj.mp (basisFreeMonoid K X).mk_eq_rank).symm
#align free_algebra.rank_eq FreeAlgebra.rank_eq

end FreeAlgebra

