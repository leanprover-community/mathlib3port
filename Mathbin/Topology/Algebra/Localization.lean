/-
Copyright (c) 2021 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández

! This file was ported from Lean 3 source module topology.algebra.localization
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Localization.Basic
import Mathbin.Topology.Algebra.Ring

/-!

# Localization of topological rings

The topological localization of a topological commutative ring `R` at a submonoid `M` is the ring
`localization M`  endowed with the final ring topology of the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)` in the localization of `R` at a `M`.

## Main Results

- `localization.topological_ring`: The localization of a topological commutative ring at a submonoid
  is a topological ring.

-/


variable {R : Type _} [CommRing R] [TopologicalSpace R] {M : Submonoid R}

/-- The ring topology on `localization M` coinduced from the natural homomorphism sending `x : R`
to the equivalence class of `(x, 1)`. -/
def Localization.ringTopology : RingTopology (Localization M) :=
  RingTopology.coinduced (Localization.monoidOf M).toFun
#align localization.ring_topology Localization.ringTopology

instance : TopologicalSpace (Localization M) :=
  Localization.ringTopology.toTopologicalSpace

instance : TopologicalRing (Localization M) :=
  Localization.ringTopology.to_topological_ring

