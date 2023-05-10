/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module data.complex.orientation
! leanprover-community/mathlib commit 7d34004e19699895c13c86b78ae62bbaea0bc893
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Complex.Module
import Mathbin.LinearAlgebra.Orientation

/-!
# The standard orientation on `ℂ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This had previously been in `linear_algebra.orientation`,
but keeping it separate results in a significant import reduction.
-/


namespace Complex

/- warning: complex.orientation -> Complex.orientation is a dubious translation:
lean 3 declaration is
  Orientation.{0, 0, 0} Real Real.strictOrderedCommSemiring Complex (AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup) (Complex.module.{0} Real (StrictOrderedSemiring.toSemiring.{0} Real (StrictOrderedCommSemiring.toStrictOrderedSemiring.{0} Real Real.strictOrderedCommSemiring)) (Semiring.toModule.{0} Real (StrictOrderedSemiring.toSemiring.{0} Real (StrictOrderedCommSemiring.toStrictOrderedSemiring.{0} Real Real.strictOrderedCommSemiring)))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  Orientation.{0, 0, 0} Real Real.strictOrderedCommSemiring Complex (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex (NonAssocRing.toNonUnitalNonAssocRing.{0} Complex (Ring.toNonAssocRing.{0} Complex Complex.instRingComplex)))) (Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRingInstRingComplex.{0} Real (StrictOrderedSemiring.toSemiring.{0} Real (StrictOrderedCommSemiring.toStrictOrderedSemiring.{0} Real Real.strictOrderedCommSemiring)) (Semiring.toModule.{0} Real (StrictOrderedSemiring.toSemiring.{0} Real (StrictOrderedCommSemiring.toStrictOrderedSemiring.{0} Real Real.strictOrderedCommSemiring)))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align complex.orientation Complex.orientationₓ'. -/
/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : Orientation ℝ ℂ (Fin 2) :=
  Complex.basisOneI.Orientation
#align complex.orientation Complex.orientation

end Complex

