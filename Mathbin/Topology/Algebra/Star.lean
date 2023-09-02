/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Star.Pi
import Mathbin.Algebra.Star.Prod
import Mathbin.Topology.Algebra.Constructions
import Mathbin.Topology.ContinuousFunction.Basic

#align_import topology.algebra.star from "leanprover-community/mathlib"@"50832daea47b195a48b5b33b1c8b2162c48c3afc"

/-!
# Continuity of `star`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `has_continuous_star` typeclass, along with instances on `pi`, `prod`,
`mul_opposite`, and `units`.
-/


open scoped Filter Topology

open Filter

universe u

variable {ι α R S : Type _}

#print ContinuousStar /-
/-- Basic hypothesis to talk about a topological space with a continuous `star` operator. -/
class ContinuousStar (R : Type u) [TopologicalSpace R] [Star R] : Prop where
  continuous_star : Continuous (star : R → R)
#align has_continuous_star ContinuousStar
-/

export ContinuousStar (continuous_star)

section Continuity

variable [TopologicalSpace R] [Star R] [ContinuousStar R]

#print continuousOn_star /-
theorem continuousOn_star {s : Set R} : ContinuousOn star s :=
  continuous_star.ContinuousOn
#align continuous_on_star continuousOn_star
-/

#print continuousWithinAt_star /-
theorem continuousWithinAt_star {s : Set R} {x : R} : ContinuousWithinAt star s x :=
  continuous_star.ContinuousWithinAt
#align continuous_within_at_star continuousWithinAt_star
-/

#print continuousAt_star /-
theorem continuousAt_star {x : R} : ContinuousAt star x :=
  continuous_star.ContinuousAt
#align continuous_at_star continuousAt_star
-/

#print tendsto_star /-
theorem tendsto_star (a : R) : Tendsto star (𝓝 a) (𝓝 (star a)) :=
  continuousAt_star
#align tendsto_star tendsto_star
-/

#print Filter.Tendsto.star /-
theorem Filter.Tendsto.star {f : α → R} {l : Filter α} {y : R} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => star (f x)) l (𝓝 (star y)) :=
  (continuous_star.Tendsto y).comp h
#align filter.tendsto.star Filter.Tendsto.star
-/

variable [TopologicalSpace α] {f : α → R} {s : Set α} {x : α}

#print Continuous.star /-
@[continuity]
theorem Continuous.star (hf : Continuous f) : Continuous fun x => star (f x) :=
  continuous_star.comp hf
#align continuous.star Continuous.star
-/

#print ContinuousAt.star /-
theorem ContinuousAt.star (hf : ContinuousAt f x) : ContinuousAt (fun x => star (f x)) x :=
  continuousAt_star.comp hf
#align continuous_at.star ContinuousAt.star
-/

#print ContinuousOn.star /-
theorem ContinuousOn.star (hf : ContinuousOn f s) : ContinuousOn (fun x => star (f x)) s :=
  continuous_star.comp_continuousOn hf
#align continuous_on.star ContinuousOn.star
-/

#print ContinuousWithinAt.star /-
theorem ContinuousWithinAt.star (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => star (f x)) s x :=
  hf.unit
#align continuous_within_at.star ContinuousWithinAt.star
-/

#print starContinuousMap /-
/-- The star operation bundled as a continuous map. -/
@[simps]
def starContinuousMap : C(R, R) :=
  ⟨star, continuous_star⟩
#align star_continuous_map starContinuousMap
-/

end Continuity

section Instances

instance [Star R] [Star S] [TopologicalSpace R] [TopologicalSpace S] [ContinuousStar R]
    [ContinuousStar S] : ContinuousStar (R × S) :=
  ⟨(continuous_star.comp continuous_fst).prod_mk (continuous_star.comp continuous_snd)⟩

instance {C : ι → Type _} [∀ i, TopologicalSpace (C i)] [∀ i, Star (C i)]
    [∀ i, ContinuousStar (C i)] : ContinuousStar (∀ i, C i)
    where continuous_star := continuous_pi fun i => Continuous.star (continuous_apply i)

instance [Star R] [TopologicalSpace R] [ContinuousStar R] : ContinuousStar Rᵐᵒᵖ :=
  ⟨MulOpposite.continuous_op.comp <| MulOpposite.continuous_unop.unit⟩

instance [Monoid R] [StarMul R] [TopologicalSpace R] [ContinuousStar R] : ContinuousStar Rˣ :=
  ⟨continuous_induced_rng.2 Units.continuous_embedProduct.unit⟩

end Instances

