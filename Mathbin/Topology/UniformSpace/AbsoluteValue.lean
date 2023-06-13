/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.absolute_value
! leanprover-community/mathlib commit e1a7bdeb4fd826b7e71d130d34988f0a2d26a177
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Topology.UniformSpace.Basic

/-!
# Uniform structure induced by an absolute value

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## Implementation details

Note that we import `data.real.cau_seq` because this is where absolute values are defined, but
the current file does not depend on real numbers. TODO: extract absolute values from that
`data.real` folder.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/


open Set Function Filter UniformSpace

open scoped Filter Topology

namespace AbsoluteValue

variable {𝕜 : Type _} [LinearOrderedField 𝕜]

variable {R : Type _} [CommRing R] (abv : AbsoluteValue R 𝕜)

#print AbsoluteValue.uniformSpace /-
/-- The uniform space structure coming from an absolute value. -/
protected def uniformSpace : UniformSpace R :=
  UniformSpace.ofFun (fun x y => abv (y - x)) (by simp) (fun x y => abv.map_sub y x)
    (fun x y z => (abv.sub_le _ _ _).trans_eq (add_comm _ _)) fun ε ε0 =>
    ⟨ε / 2, half_pos ε0, fun _ h₁ _ h₂ => (add_lt_add h₁ h₂).trans_eq (add_halves ε)⟩
#align absolute_value.uniform_space AbsoluteValue.uniformSpace
-/

#print AbsoluteValue.hasBasis_uniformity /-
theorem hasBasis_uniformity :
    𝓤[abv.UniformSpace].HasBasis (fun ε : 𝕜 => 0 < ε) fun ε => {p : R × R | abv (p.2 - p.1) < ε} :=
  UniformSpace.hasBasis_ofFun (exists_gt _) _ _ _ _ _
#align absolute_value.has_basis_uniformity AbsoluteValue.hasBasis_uniformity
-/

end AbsoluteValue

