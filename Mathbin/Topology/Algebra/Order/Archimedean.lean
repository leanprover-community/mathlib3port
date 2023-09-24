/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Topology.Order.Basic
import Algebra.Order.Archimedean

#align_import topology.algebra.order.archimedean from "leanprover-community/mathlib"@"50832daea47b195a48b5b33b1c8b2162c48c3afc"

/-!
# Rational numbers are dense in a linear ordered archimedean field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that coercion from `ℚ` to a linear ordered archimedean field has dense range.
This lemma is in a separate file because `topology.order.basic` does not import
`algebra.order.archimedean`.
-/


variable {𝕜 : Type _} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [Archimedean 𝕜]

#print Rat.denseRange_cast /-
/-- Rational numbers are dense in a linear ordered archimedean field. -/
theorem Rat.denseRange_cast : DenseRange (coe : ℚ → 𝕜) :=
  dense_of_exists_between fun a b h => Set.exists_range_iff.2 <| exists_rat_btwn h
#align rat.dense_range_cast Rat.denseRange_cast
-/

