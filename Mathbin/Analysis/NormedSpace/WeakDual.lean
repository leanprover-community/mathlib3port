/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.normed_space.weak_dual
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Module.WeakDual
import Mathbin.Analysis.NormedSpace.Dual
import Mathbin.Analysis.NormedSpace.OperatorNorm

/-!
# Weak dual of normed space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `E` be a normed space over a field `𝕜`. This file is concerned with properties of the weak-*
topology on the dual of `E`. By the dual, we mean either of the type synonyms
`normed_space.dual 𝕜 E` or `weak_dual 𝕜 E`, depending on whether it is viewed as equipped with its
usual operator norm topology or the weak-* topology.

It is shown that the canonical mapping `normed_space.dual 𝕜 E → weak_dual 𝕜 E` is continuous, and
as a consequence the weak-* topology is coarser than the topology obtained from the operator norm
(dual norm).

In this file, we also establish the Banach-Alaoglu theorem about the compactness of closed balls
in the dual of `E` (as well as sets of somewhat more general form) with respect to the weak-*
topology.

## Main definitions

The main definitions concern the canonical mapping `dual 𝕜 E → weak_dual 𝕜 E`.

* `normed_space.dual.to_weak_dual` and `weak_dual.to_normed_dual`: Linear equivalences from
  `dual 𝕜 E` to `weak_dual 𝕜 E` and in the converse direction.
* `normed_space.dual.continuous_linear_map_to_weak_dual`: A continuous linear mapping from
  `dual 𝕜 E` to `weak_dual 𝕜 E` (same as `normed_space.dual.to_weak_dual` but different bundled
  data).

## Main results

The first main result concerns the comparison of the operator norm topology on `dual 𝕜 E` and the
weak-* topology on (its type synonym) `weak_dual 𝕜 E`:
* `dual_norm_topology_le_weak_dual_topology`: The weak-* topology on the dual of a normed space is
  coarser (not necessarily strictly) than the operator norm topology.
* `weak_dual.is_compact_polar` (a version of the Banach-Alaoglu theorem): The polar set of a
  neighborhood of the origin in a normed space `E` over `𝕜` is compact in `weak_dual _ E`, if the
  nontrivially normed field `𝕜` is proper as a topological space.
* `weak_dual.is_compact_closed_ball` (the most common special case of the Banach-Alaoglu theorem):
  Closed balls in the dual of a normed space `E` over `ℝ` or `ℂ` are compact in the weak-star
  topology.

TODOs:
* Add that in finite dimensions, the weak-* topology and the dual norm topology coincide.
* Add that in infinite dimensions, the weak-* topology is strictly coarser than the dual norm
  topology.
* Add metrizability of the dual unit ball (more generally weak-star compact subsets) of
  `weak_dual 𝕜 E` under the assumption of separability of `E`.
* Add the sequential Banach-Alaoglu theorem: the dual unit ball of a separable normed space `E`
  is sequentially compact in the weak-star topology. This would follow from the metrizability above.

## Notations

No new notation is introduced.

## Implementation notes

Weak-* topology is defined generally in the file `topology.algebra.module.weak_dual`.

When `E` is a normed space, the duals `dual 𝕜 E` and `weak_dual 𝕜 E` are type synonyms with
different topology instances.

For the proof of Banach-Alaoglu theorem, the weak dual of `E` is embedded in the space of
functions `E → 𝕜` with the topology of pointwise convergence.

The polar set `polar 𝕜 s` of a subset `s` of `E` is originally defined as a subset of the dual
`dual 𝕜 E`. We care about properties of these w.r.t. weak-* topology, and for this purpose give
the definition `weak_dual.polar 𝕜 s` for the "same" subset viewed as a subset of `weak_dual 𝕜 E`
(a type synonym of the dual but with a different topology instance).

## References

* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology
* https://en.wikipedia.org/wiki/Banach%E2%80%93Alaoglu_theorem

## Tags

weak-star, weak dual

-/


noncomputable section

open Filter Function Metric Set

open Topology Filter

/-!
### Weak star topology on duals of normed spaces

In this section, we prove properties about the weak-* topology on duals of normed spaces.
We prove in particular that the canonical mapping `dual 𝕜 E → weak_dual 𝕜 E` is continuous,
i.e., that the weak-* topology is coarser (not necessarily strictly) than the topology given
by the dual-norm (i.e. the operator-norm).
-/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]

variable {E : Type _} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace NormedSpace

namespace Dual

#print NormedSpace.Dual.toWeakDual /-
/-- For normed spaces `E`, there is a canonical map `dual 𝕜 E → weak_dual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
def toWeakDual : Dual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E :=
  LinearEquiv.refl 𝕜 (E →L[𝕜] 𝕜)
#align normed_space.dual.to_weak_dual NormedSpace.Dual.toWeakDual
-/

/- warning: normed_space.dual.coe_to_weak_dual -> NormedSpace.Dual.coe_toWeakDual is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.dual.coe_to_weak_dual NormedSpace.Dual.coe_toWeakDualₓ'. -/
@[simp]
theorem coe_toWeakDual (x' : Dual 𝕜 E) : ⇑x'.toWeakDual = x' :=
  rfl
#align normed_space.dual.coe_to_weak_dual NormedSpace.Dual.coe_toWeakDual

/- warning: normed_space.dual.to_weak_dual_eq_iff -> NormedSpace.Dual.toWeakDual_eq_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.dual.to_weak_dual_eq_iff NormedSpace.Dual.toWeakDual_eq_iffₓ'. -/
@[simp]
theorem toWeakDual_eq_iff (x' y' : Dual 𝕜 E) : x'.toWeakDual = y'.toWeakDual ↔ x' = y' :=
  toWeakDual.Injective.eq_iff
#align normed_space.dual.to_weak_dual_eq_iff NormedSpace.Dual.toWeakDual_eq_iff

/- warning: normed_space.dual.to_weak_dual_continuous -> NormedSpace.Dual.toWeakDual_continuous is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.dual.to_weak_dual_continuous NormedSpace.Dual.toWeakDual_continuousₓ'. -/
theorem toWeakDual_continuous : Continuous fun x' : Dual 𝕜 E => x'.toWeakDual :=
  WeakBilin.continuous_of_continuous_eval _ fun z => (inclusionInDoubleDual 𝕜 E z).Continuous
#align normed_space.dual.to_weak_dual_continuous NormedSpace.Dual.toWeakDual_continuous

#print NormedSpace.Dual.continuousLinearMapToWeakDual /-
/-- For a normed space `E`, according to `to_weak_dual_continuous` the "identity mapping"
`dual 𝕜 E → weak_dual 𝕜 E` is continuous. This definition implements it as a continuous linear
map. -/
def continuousLinearMapToWeakDual : Dual 𝕜 E →L[𝕜] WeakDual 𝕜 E :=
  { toWeakDual with cont := toWeakDual_continuous }
#align normed_space.dual.continuous_linear_map_to_weak_dual NormedSpace.Dual.continuousLinearMapToWeakDual
-/

/- warning: normed_space.dual.dual_norm_topology_le_weak_dual_topology -> NormedSpace.Dual.dual_norm_topology_le_weak_dual_topology is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.dual.dual_norm_topology_le_weak_dual_topology NormedSpace.Dual.dual_norm_topology_le_weak_dual_topologyₓ'. -/
/-- The weak-star topology is coarser than the dual-norm topology. -/
theorem dual_norm_topology_le_weak_dual_topology :
    (by infer_instance : TopologicalSpace (Dual 𝕜 E)) ≤
      (by infer_instance : TopologicalSpace (WeakDual 𝕜 E)) :=
  by convert to_weak_dual_continuous.le_induced; exact induced_id.symm
#align normed_space.dual.dual_norm_topology_le_weak_dual_topology NormedSpace.Dual.dual_norm_topology_le_weak_dual_topology

end Dual

end NormedSpace

namespace WeakDual

open NormedSpace

#print WeakDual.toNormedDual /-
/-- For normed spaces `E`, there is a canonical map `weak_dual 𝕜 E → dual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. Here it is implemented as the inverse of the linear
equivalence `normed_space.dual.to_weak_dual` in the other direction. -/
def toNormedDual : WeakDual 𝕜 E ≃ₗ[𝕜] Dual 𝕜 E :=
  NormedSpace.Dual.toWeakDual.symm
#align weak_dual.to_normed_dual WeakDual.toNormedDual
-/

/- warning: weak_dual.to_normed_dual_apply -> WeakDual.toNormedDual_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align weak_dual.to_normed_dual_apply WeakDual.toNormedDual_applyₓ'. -/
theorem toNormedDual_apply (x : WeakDual 𝕜 E) (y : E) : (toNormedDual x) y = x y :=
  rfl
#align weak_dual.to_normed_dual_apply WeakDual.toNormedDual_apply

/- warning: weak_dual.coe_to_normed_dual -> WeakDual.coe_toNormedDual is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align weak_dual.coe_to_normed_dual WeakDual.coe_toNormedDualₓ'. -/
@[simp]
theorem coe_toNormedDual (x' : WeakDual 𝕜 E) : ⇑x'.toNormedDual = x' :=
  rfl
#align weak_dual.coe_to_normed_dual WeakDual.coe_toNormedDual

/- warning: weak_dual.to_normed_dual_eq_iff -> WeakDual.toNormedDual_eq_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align weak_dual.to_normed_dual_eq_iff WeakDual.toNormedDual_eq_iffₓ'. -/
@[simp]
theorem toNormedDual_eq_iff (x' y' : WeakDual 𝕜 E) : x'.toNormedDual = y'.toNormedDual ↔ x' = y' :=
  WeakDual.toNormedDual.Injective.eq_iff
#align weak_dual.to_normed_dual_eq_iff WeakDual.toNormedDual_eq_iff

/- warning: weak_dual.is_closed_closed_ball -> WeakDual.isClosed_closedBall is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align weak_dual.is_closed_closed_ball WeakDual.isClosed_closedBallₓ'. -/
theorem isClosed_closedBall (x' : Dual 𝕜 E) (r : ℝ) : IsClosed (toNormedDual ⁻¹' closedBall x' r) :=
  isClosed_induced_iff'.2 (ContinuousLinearMap.is_weak_closed_closedBall x' r)
#align weak_dual.is_closed_closed_ball WeakDual.isClosed_closedBall

/-!
### Polar sets in the weak dual space
-/


variable (𝕜)

#print WeakDual.polar /-
/-- The polar set `polar 𝕜 s` of `s : set E` seen as a subset of the dual of `E` with the
weak-star topology is `weak_dual.polar 𝕜 s`. -/
def polar (s : Set E) : Set (WeakDual 𝕜 E) :=
  toNormedDual ⁻¹' polar 𝕜 s
#align weak_dual.polar WeakDual.polar
-/

/- warning: weak_dual.polar_def -> WeakDual.polar_def is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align weak_dual.polar_def WeakDual.polar_defₓ'. -/
theorem polar_def (s : Set E) : polar 𝕜 s = { f : WeakDual 𝕜 E | ∀ x ∈ s, ‖f x‖ ≤ 1 } :=
  rfl
#align weak_dual.polar_def WeakDual.polar_def

#print WeakDual.isClosed_polar /-
/-- The polar `polar 𝕜 s` of a set `s : E` is a closed subset when the weak star topology
is used. -/
theorem isClosed_polar (s : Set E) : IsClosed (polar 𝕜 s) :=
  by
  simp only [polar_def, set_of_forall]
  exact isClosed_biInter fun x hx => is_closed_Iic.preimage (WeakBilin.eval_continuous _ _).norm
#align weak_dual.is_closed_polar WeakDual.isClosed_polar
-/

variable {𝕜}

/- warning: weak_dual.is_closed_image_coe_of_bounded_of_closed -> WeakDual.isClosed_image_coe_of_bounded_of_closed is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align weak_dual.is_closed_image_coe_of_bounded_of_closed WeakDual.isClosed_image_coe_of_bounded_of_closedₓ'. -/
/-- While the coercion `coe_fn : weak_dual 𝕜 E → (E → 𝕜)` is not a closed map, it sends *bounded*
closed sets to closed sets. -/
theorem isClosed_image_coe_of_bounded_of_closed {s : Set (WeakDual 𝕜 E)}
    (hb : Bounded (Dual.toWeakDual ⁻¹' s)) (hc : IsClosed s) :
    IsClosed ((coeFn : WeakDual 𝕜 E → E → 𝕜) '' s) :=
  ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed hb (isClosed_induced_iff'.1 hc)
#align weak_dual.is_closed_image_coe_of_bounded_of_closed WeakDual.isClosed_image_coe_of_bounded_of_closed

/- warning: weak_dual.is_compact_of_bounded_of_closed -> WeakDual.isCompact_of_bounded_of_closed is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align weak_dual.is_compact_of_bounded_of_closed WeakDual.isCompact_of_bounded_of_closedₓ'. -/
theorem isCompact_of_bounded_of_closed [ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)}
    (hb : Bounded (Dual.toWeakDual ⁻¹' s)) (hc : IsClosed s) : IsCompact s :=
  (Embedding.isCompact_iff_isCompact_image FunLike.coe_injective.embedding_induced).mpr <|
    ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image hb <|
      isClosed_image_coe_of_bounded_of_closed hb hc
#align weak_dual.is_compact_of_bounded_of_closed WeakDual.isCompact_of_bounded_of_closed

variable (𝕜)

/- warning: weak_dual.is_closed_image_polar_of_mem_nhds -> WeakDual.isClosed_image_polar_of_mem_nhds is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align weak_dual.is_closed_image_polar_of_mem_nhds WeakDual.isClosed_image_polar_of_mem_nhdsₓ'. -/
/-- The image under `coe_fn : weak_dual 𝕜 E → (E → 𝕜)` of a polar `weak_dual.polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
theorem isClosed_image_polar_of_mem_nhds {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
    IsClosed ((coeFn : WeakDual 𝕜 E → E → 𝕜) '' polar 𝕜 s) :=
  isClosed_image_coe_of_bounded_of_closed (bounded_polar_of_mem_nhds_zero 𝕜 s_nhd)
    (isClosed_polar _ _)
#align weak_dual.is_closed_image_polar_of_mem_nhds WeakDual.isClosed_image_polar_of_mem_nhds

/- warning: normed_space.dual.is_closed_image_polar_of_mem_nhds -> NormedSpace.Dual.isClosed_image_polar_of_mem_nhds is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.dual.is_closed_image_polar_of_mem_nhds NormedSpace.Dual.isClosed_image_polar_of_mem_nhdsₓ'. -/
/-- The image under `coe_fn : normed_space.dual 𝕜 E → (E → 𝕜)` of a polar `polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
theorem NormedSpace.Dual.isClosed_image_polar_of_mem_nhds {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
    IsClosed ((coeFn : Dual 𝕜 E → E → 𝕜) '' NormedSpace.polar 𝕜 s) :=
  isClosed_image_polar_of_mem_nhds 𝕜 s_nhd
#align normed_space.dual.is_closed_image_polar_of_mem_nhds NormedSpace.Dual.isClosed_image_polar_of_mem_nhds

/- warning: weak_dual.is_compact_polar -> WeakDual.isCompact_polar is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align weak_dual.is_compact_polar WeakDual.isCompact_polarₓ'. -/
/-- The **Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origin in a
normed space `E` is a compact subset of `weak_dual 𝕜 E`. -/
theorem isCompact_polar [ProperSpace 𝕜] {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) :
    IsCompact (polar 𝕜 s) :=
  isCompact_of_bounded_of_closed (bounded_polar_of_mem_nhds_zero 𝕜 s_nhd) (isClosed_polar _ _)
#align weak_dual.is_compact_polar WeakDual.isCompact_polar

/- warning: weak_dual.is_compact_closed_ball -> WeakDual.isCompact_closedBall is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align weak_dual.is_compact_closed_ball WeakDual.isCompact_closedBallₓ'. -/
/-- The **Banach-Alaoglu theorem**: closed balls of the dual of a normed space `E` are compact in
the weak-star topology. -/
theorem isCompact_closedBall [ProperSpace 𝕜] (x' : Dual 𝕜 E) (r : ℝ) :
    IsCompact (toNormedDual ⁻¹' closedBall x' r) :=
  isCompact_of_bounded_of_closed bounded_closedBall (isClosed_closedBall x' r)
#align weak_dual.is_compact_closed_ball WeakDual.isCompact_closedBall

end WeakDual

