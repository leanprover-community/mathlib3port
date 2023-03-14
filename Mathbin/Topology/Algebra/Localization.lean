/-
Copyright (c) 2021 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández

! This file was ported from Lean 3 source module topology.algebra.localization
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Localization.Basic
import Mathbin.Topology.Algebra.Ring.Basic

/-!

# Localization of topological rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The topological localization of a topological commutative ring `R` at a submonoid `M` is the ring
`localization M`  endowed with the final ring topology of the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)` in the localization of `R` at a `M`.

## Main Results

- `localization.topological_ring`: The localization of a topological commutative ring at a submonoid
  is a topological ring.

-/


variable {R : Type _} [CommRing R] [TopologicalSpace R] {M : Submonoid R}

/- warning: localization.ring_topology -> Localization.ringTopology is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))}, RingTopology.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (CommRing.toRing.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Localization.commRing.{u1} R _inst_1 M))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] {M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))}, RingTopology.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (CommRing.toRing.{u1} (Localization.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) M) (Localization.instCommRingLocalizationToCommMonoid.{u1} R _inst_1 M))
Case conversion may be inaccurate. Consider using '#align localization.ring_topology Localization.ringTopologyₓ'. -/
/-- The ring topology on `localization M` coinduced from the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)`. -/
def Localization.ringTopology : RingTopology (Localization M) :=
  RingTopology.coinduced (Localization.monoidOf M).toFun
#align localization.ring_topology Localization.ringTopology

instance : TopologicalSpace (Localization M) :=
  Localization.ringTopology.toTopologicalSpace

instance : TopologicalRing (Localization M) :=
  Localization.ringTopology.toTopologicalRing

