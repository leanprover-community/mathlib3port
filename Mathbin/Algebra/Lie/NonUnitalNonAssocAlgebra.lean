/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module algebra.lie.non_unital_non_assoc_algebra
! leanprover-community/mathlib commit 841ac1a3d9162bf51c6327812ecb6e5e71883ac4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.NonUnitalAlg
import Mathbin.Algebra.Lie.Basic

/-!
# Lie algebras as non-unital, non-associative algebras

The definition of Lie algebras uses the `has_bracket` typeclass for multiplication whereas we have a
separate `has_mul` typeclass used for general algebras.

It is useful to have a special typeclass for Lie algebras because:
 * it enables us to use the traditional notation `⁅x, y⁆` for the Lie multiplication,
 * associative algebras carry a natural Lie algebra structure via the ring commutator and so we need
   them to carry both `has_mul` and `has_bracket` simultaneously,
 * more generally, Poisson algebras (not yet defined) need both typeclasses.

However there are times when it is convenient to be able to regard a Lie algebra as a general
algebra and we provide some basic definitions for doing so here.

## Main definitions

  * `commutator_ring` turns a Lie ring into a `non_unital_non_assoc_semiring` by turning its
    `has_bracket` (denoted `⁅, ⁆`) into a `has_mul` (denoted `*`).
  * `lie_hom.to_non_unital_alg_hom`

## Tags

lie algebra, non-unital, non-associative
-/


universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

#print CommutatorRing /-
/-- Type synonym for turning a `lie_ring` into a `non_unital_non_assoc_semiring`.

A `lie_ring` can be regarded as a `non_unital_non_assoc_semiring` by turning its
`has_bracket` (denoted `⁅, ⁆`) into a `has_mul` (denoted `*`). -/
def CommutatorRing (L : Type v) : Type v :=
  L
#align commutator_ring CommutatorRing
-/

/-- A `lie_ring` can be regarded as a `non_unital_non_assoc_semiring` by turning its
`has_bracket` (denoted `⁅, ⁆`) into a `has_mul` (denoted `*`). -/
instance : NonUnitalNonAssocSemiring (CommutatorRing L) :=
  show NonUnitalNonAssocSemiring L from
    {
      (inferInstance : AddCommMonoid
          L) with
      mul := Bracket.bracket
      left_distrib := lie_add
      right_distrib := add_lie
      zero_mul := zero_lie
      mul_zero := lie_zero }

namespace LieAlgebra

instance (L : Type v) [Nonempty L] : Nonempty (CommutatorRing L) :=
  ‹Nonempty L›

instance (L : Type v) [Inhabited L] : Inhabited (CommutatorRing L) :=
  ‹Inhabited L›

instance : LieRing (CommutatorRing L) :=
  show LieRing L by infer_instance

instance : LieAlgebra R (CommutatorRing L) :=
  show LieAlgebra R L by infer_instance

/- warning: lie_algebra.is_scalar_tower -> LieAlgebra.isScalarTower is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (L : Type.{u2}) [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2], IsScalarTower.{u1, u2, u2} R (CommutatorRing.{u2} L) (CommutatorRing.{u2} L) (SMulZeroClass.toHasSmul.{u1, u2} R (CommutatorRing.{u2} L) (AddZeroClass.toHasZero.{u2} (CommutatorRing.{u2} L) (AddMonoid.toAddZeroClass.{u2} (CommutatorRing.{u2} L) (AddCommMonoid.toAddMonoid.{u2} (CommutatorRing.{u2} L) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R (CommutatorRing.{u2} L) (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} (CommutatorRing.{u2} L) (AddMonoid.toAddZeroClass.{u2} (CommutatorRing.{u2} L) (AddCommMonoid.toAddMonoid.{u2} (CommutatorRing.{u2} L) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} (CommutatorRing.{u2} L) (AddMonoid.toAddZeroClass.{u2} (CommutatorRing.{u2} L) (AddCommMonoid.toAddMonoid.{u2} (CommutatorRing.{u2} L) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2))) (LieAlgebra.toModule.{u1, u2} R (CommutatorRing.{u2} L) _inst_1 (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2) (LieAlgebra.CommutatorRing.lieAlgebra.{u1, u2} R L _inst_1 _inst_2 _inst_3)))))) (Mul.toSMul.{u2} (CommutatorRing.{u2} L) (Distrib.toHasMul.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toDistrib.{u2} (CommutatorRing.{u2} L) (CommutatorRing.nonUnitalNonAssocSemiring.{u2} L _inst_2)))) (SMulZeroClass.toHasSmul.{u1, u2} R (CommutatorRing.{u2} L) (AddZeroClass.toHasZero.{u2} (CommutatorRing.{u2} L) (AddMonoid.toAddZeroClass.{u2} (CommutatorRing.{u2} L) (AddCommMonoid.toAddMonoid.{u2} (CommutatorRing.{u2} L) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R (CommutatorRing.{u2} L) (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} (CommutatorRing.{u2} L) (AddMonoid.toAddZeroClass.{u2} (CommutatorRing.{u2} L) (AddCommMonoid.toAddMonoid.{u2} (CommutatorRing.{u2} L) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} (CommutatorRing.{u2} L) (AddMonoid.toAddZeroClass.{u2} (CommutatorRing.{u2} L) (AddCommMonoid.toAddMonoid.{u2} (CommutatorRing.{u2} L) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2))) (LieAlgebra.toModule.{u1, u2} R (CommutatorRing.{u2} L) _inst_1 (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2) (LieAlgebra.CommutatorRing.lieAlgebra.{u1, u2} R L _inst_1 _inst_2 _inst_3))))))
but is expected to have type
  forall (R : Type.{u1}) (L : Type.{u2}) [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2], IsScalarTower.{u1, u2, u2} R (CommutatorRing.{u2} L) (CommutatorRing.{u2} L) (SMulZeroClass.toSMul.{u1, u2} R (CommutatorRing.{u2} L) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (SMulWithZero.toSMulZeroClass.{u1, u2} R (CommutatorRing.{u2} L) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (Module.toMulActionWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2)) (LieAlgebra.toModule.{u1, u2} R (CommutatorRing.{u2} L) _inst_1 (LieAlgebra.instLieRingCommutatorRing.{u2} L _inst_2) (LieAlgebra.instLieAlgebraCommutatorRingInstLieRingCommutatorRing.{u1, u2} R L _inst_1 _inst_2 _inst_3)))))) (SMulZeroClass.toSMul.{u2, u2} (CommutatorRing.{u2} L) (CommutatorRing.{u2} L) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (SMulWithZero.toSMulZeroClass.{u2, u2} (CommutatorRing.{u2} L) (CommutatorRing.{u2} L) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (MulZeroClass.toSMulWithZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))))) (SMulZeroClass.toSMul.{u1, u2} R (CommutatorRing.{u2} L) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (SMulWithZero.toSMulZeroClass.{u1, u2} R (CommutatorRing.{u2} L) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (Module.toMulActionWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2)) (LieAlgebra.toModule.{u1, u2} R (CommutatorRing.{u2} L) _inst_1 (LieAlgebra.instLieRingCommutatorRing.{u2} L _inst_2) (LieAlgebra.instLieAlgebraCommutatorRingInstLieRingCommutatorRing.{u1, u2} R L _inst_1 _inst_2 _inst_3))))))
Case conversion may be inaccurate. Consider using '#align lie_algebra.is_scalar_tower LieAlgebra.isScalarTowerₓ'. -/
/-- Regarding the `lie_ring` of a `lie_algebra` as a `non_unital_non_assoc_semiring`, we can
reinterpret the `smul_lie` law as an `is_scalar_tower`. -/
instance isScalarTower : IsScalarTower R (CommutatorRing L) (CommutatorRing L) :=
  ⟨smul_lie⟩
#align lie_algebra.is_scalar_tower LieAlgebra.isScalarTower

/- warning: lie_algebra.smul_comm_class -> LieAlgebra.sMulCommClass is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (L : Type.{u2}) [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2], SMulCommClass.{u1, u2, u2} R (CommutatorRing.{u2} L) (CommutatorRing.{u2} L) (SMulZeroClass.toHasSmul.{u1, u2} R (CommutatorRing.{u2} L) (AddZeroClass.toHasZero.{u2} (CommutatorRing.{u2} L) (AddMonoid.toAddZeroClass.{u2} (CommutatorRing.{u2} L) (AddCommMonoid.toAddMonoid.{u2} (CommutatorRing.{u2} L) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R (CommutatorRing.{u2} L) (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) (AddZeroClass.toHasZero.{u2} (CommutatorRing.{u2} L) (AddMonoid.toAddZeroClass.{u2} (CommutatorRing.{u2} L) (AddCommMonoid.toAddMonoid.{u2} (CommutatorRing.{u2} L) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (AddZeroClass.toHasZero.{u2} (CommutatorRing.{u2} L) (AddMonoid.toAddZeroClass.{u2} (CommutatorRing.{u2} L) (AddCommMonoid.toAddMonoid.{u2} (CommutatorRing.{u2} L) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2))) (LieAlgebra.toModule.{u1, u2} R (CommutatorRing.{u2} L) _inst_1 (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2) (LieAlgebra.CommutatorRing.lieAlgebra.{u1, u2} R L _inst_1 _inst_2 _inst_3)))))) (Mul.toSMul.{u2} (CommutatorRing.{u2} L) (Distrib.toHasMul.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toDistrib.{u2} (CommutatorRing.{u2} L) (CommutatorRing.nonUnitalNonAssocSemiring.{u2} L _inst_2))))
but is expected to have type
  forall (R : Type.{u1}) (L : Type.{u2}) [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2], SMulCommClass.{u1, u2, u2} R (CommutatorRing.{u2} L) (CommutatorRing.{u2} L) (SMulZeroClass.toSMul.{u1, u2} R (CommutatorRing.{u2} L) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (SMulWithZero.toSMulZeroClass.{u1, u2} R (CommutatorRing.{u2} L) (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (Module.toMulActionWithZero.{u1, u2} R (CommutatorRing.{u2} L) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2)) (LieAlgebra.toModule.{u1, u2} R (CommutatorRing.{u2} L) _inst_1 (LieAlgebra.instLieRingCommutatorRing.{u2} L _inst_2) (LieAlgebra.instLieAlgebraCommutatorRingInstLieRingCommutatorRing.{u1, u2} R L _inst_1 _inst_2 _inst_3)))))) (SMulZeroClass.toSMul.{u2, u2} (CommutatorRing.{u2} L) (CommutatorRing.{u2} L) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (SMulWithZero.toSMulZeroClass.{u2, u2} (CommutatorRing.{u2} L) (CommutatorRing.{u2} L) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (MulZeroClass.toZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2))) (MulZeroClass.toSMulWithZero.{u2} (CommutatorRing.{u2} L) (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2)))))
Case conversion may be inaccurate. Consider using '#align lie_algebra.smul_comm_class LieAlgebra.sMulCommClassₓ'. -/
/-- Regarding the `lie_ring` of a `lie_algebra` as a `non_unital_non_assoc_semiring`, we can
reinterpret the `lie_smul` law as an `smul_comm_class`. -/
instance sMulCommClass : SMulCommClass R (CommutatorRing L) (CommutatorRing L) :=
  ⟨fun t x y => (lie_smul t x y).symm⟩
#align lie_algebra.smul_comm_class LieAlgebra.sMulCommClass

end LieAlgebra

namespace LieHom

variable {R L} {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

/- warning: lie_hom.to_non_unital_alg_hom -> LieHom.toNonUnitalAlgHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2] {L₂ : Type.{u3}} [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4], (LieHom.{u1, u2, u3} R L L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) -> (NonUnitalAlgHom.{u1, u2, u3} R (CommutatorRing.{u2} L) (CommutatorRing.{u3} L₂) (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)) (CommutatorRing.nonUnitalNonAssocSemiring.{u2} L _inst_2) (Module.toDistribMulAction.{u1, u2} R (CommutatorRing.{u2} L) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2))) (LieAlgebra.toModule.{u1, u2} R (CommutatorRing.{u2} L) _inst_1 (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2) (LieAlgebra.CommutatorRing.lieAlgebra.{u1, u2} R L _inst_1 _inst_2 _inst_3))) (CommutatorRing.nonUnitalNonAssocSemiring.{u3} L₂ _inst_4) (Module.toDistribMulAction.{u1, u3} R (CommutatorRing.{u3} L₂) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} (CommutatorRing.{u3} L₂) (LieRing.toAddCommGroup.{u3} (CommutatorRing.{u3} L₂) (LieAlgebra.CommutatorRing.lieRing.{u3} L₂ _inst_4))) (LieAlgebra.toModule.{u1, u3} R (CommutatorRing.{u3} L₂) _inst_1 (LieAlgebra.CommutatorRing.lieRing.{u3} L₂ _inst_4) (LieAlgebra.CommutatorRing.lieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4 _inst_5))))
but is expected to have type
  forall {R : Type.{u1}} {L : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2] {L₂ : Type.{u3}} [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4], (LieHom.{u1, u2, u3} R L L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) -> (NonUnitalAlgHom.{u1, u2, u3} R (CommutatorRing.{u2} L) (CommutatorRing.{u3} L₂) (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2) (Module.toDistribMulAction.{u1, u2} R (CommutatorRing.{u2} L) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2)) (LieAlgebra.toModule.{u1, u2} R (CommutatorRing.{u2} L) _inst_1 (LieAlgebra.instLieRingCommutatorRing.{u2} L _inst_2) (LieAlgebra.instLieAlgebraCommutatorRingInstLieRingCommutatorRing.{u1, u2} R L _inst_1 _inst_2 _inst_3))) (instNonUnitalNonAssocSemiringCommutatorRing.{u3} L₂ _inst_4) (Module.toDistribMulAction.{u1, u3} R (CommutatorRing.{u3} L₂) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} (CommutatorRing.{u3} L₂) (instNonUnitalNonAssocSemiringCommutatorRing.{u3} L₂ _inst_4)) (LieAlgebra.toModule.{u1, u3} R (CommutatorRing.{u3} L₂) _inst_1 (LieAlgebra.instLieRingCommutatorRing.{u3} L₂ _inst_4) (LieAlgebra.instLieAlgebraCommutatorRingInstLieRingCommutatorRing.{u1, u3} R L₂ _inst_1 _inst_4 _inst_5))))
Case conversion may be inaccurate. Consider using '#align lie_hom.to_non_unital_alg_hom LieHom.toNonUnitalAlgHomₓ'. -/
/-- Regarding the `lie_ring` of a `lie_algebra` as a `non_unital_non_assoc_semiring`, we can
regard a `lie_hom` as a `non_unital_alg_hom`. -/
@[simps]
def toNonUnitalAlgHom (f : L →ₗ⁅R⁆ L₂) : CommutatorRing L →ₙₐ[R] CommutatorRing L₂ :=
  { f with
    toFun := f
    map_zero' := f.map_zero
    map_mul' := f.map_lie }
#align lie_hom.to_non_unital_alg_hom LieHom.toNonUnitalAlgHom

/- warning: lie_hom.to_non_unital_alg_hom_injective -> LieHom.toNonUnitalAlgHom_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2] {L₂ : Type.{u3}} [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4], Function.Injective.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (NonUnitalAlgHom.{u1, u2, u3} R (CommutatorRing.{u2} L) (CommutatorRing.{u3} L₂) (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)) (CommutatorRing.nonUnitalNonAssocSemiring.{u2} L _inst_2) (Module.toDistribMulAction.{u1, u2} R (CommutatorRing.{u2} L) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (LieRing.toAddCommGroup.{u2} (CommutatorRing.{u2} L) (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2))) (LieAlgebra.toModule.{u1, u2} R (CommutatorRing.{u2} L) _inst_1 (LieAlgebra.CommutatorRing.lieRing.{u2} L _inst_2) (LieAlgebra.CommutatorRing.lieAlgebra.{u1, u2} R L _inst_1 _inst_2 _inst_3))) (CommutatorRing.nonUnitalNonAssocSemiring.{u3} L₂ _inst_4) (Module.toDistribMulAction.{u1, u3} R (CommutatorRing.{u3} L₂) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} (CommutatorRing.{u3} L₂) (LieRing.toAddCommGroup.{u3} (CommutatorRing.{u3} L₂) (LieAlgebra.CommutatorRing.lieRing.{u3} L₂ _inst_4))) (LieAlgebra.toModule.{u1, u3} R (CommutatorRing.{u3} L₂) _inst_1 (LieAlgebra.CommutatorRing.lieRing.{u3} L₂ _inst_4) (LieAlgebra.CommutatorRing.lieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4 _inst_5)))) (LieHom.toNonUnitalAlgHom.{u1, u2, u3} R L _inst_1 _inst_2 _inst_3 L₂ _inst_4 _inst_5)
but is expected to have type
  forall {R : Type.{u1}} {L : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2] {L₂ : Type.{u3}} [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4], Function.Injective.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (NonUnitalAlgHom.{u1, u2, u3} R (CommutatorRing.{u2} L) (CommutatorRing.{u3} L₂) (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2) (Module.toDistribMulAction.{u1, u2} R (CommutatorRing.{u2} L) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} (CommutatorRing.{u2} L) (instNonUnitalNonAssocSemiringCommutatorRing.{u2} L _inst_2)) (LieAlgebra.toModule.{u1, u2} R (CommutatorRing.{u2} L) _inst_1 (LieAlgebra.instLieRingCommutatorRing.{u2} L _inst_2) (LieAlgebra.instLieAlgebraCommutatorRingInstLieRingCommutatorRing.{u1, u2} R L _inst_1 _inst_2 _inst_3))) (instNonUnitalNonAssocSemiringCommutatorRing.{u3} L₂ _inst_4) (Module.toDistribMulAction.{u1, u3} R (CommutatorRing.{u3} L₂) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} (CommutatorRing.{u3} L₂) (instNonUnitalNonAssocSemiringCommutatorRing.{u3} L₂ _inst_4)) (LieAlgebra.toModule.{u1, u3} R (CommutatorRing.{u3} L₂) _inst_1 (LieAlgebra.instLieRingCommutatorRing.{u3} L₂ _inst_4) (LieAlgebra.instLieAlgebraCommutatorRingInstLieRingCommutatorRing.{u1, u3} R L₂ _inst_1 _inst_4 _inst_5)))) (LieHom.toNonUnitalAlgHom.{u1, u2, u3} R L _inst_1 _inst_2 _inst_3 L₂ _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align lie_hom.to_non_unital_alg_hom_injective LieHom.toNonUnitalAlgHom_injectiveₓ'. -/
theorem toNonUnitalAlgHom_injective :
    Function.Injective (toNonUnitalAlgHom : _ → CommutatorRing L →ₙₐ[R] CommutatorRing L₂) :=
  fun f g h => ext <| NonUnitalAlgHom.congr_fun h
#align lie_hom.to_non_unital_alg_hom_injective LieHom.toNonUnitalAlgHom_injective

end LieHom

