import Mathbin.Topology.Algebra.WeakDualTopology 
import Mathbin.Analysis.NormedSpace.Dual 
import Mathbin.Analysis.NormedSpace.OperatorNorm

/-!
# Weak dual of normed space

Let `E` be a normed space over a field `𝕜`. This file is concerned with properties of the weak-*
topology on the dual of `E`. By the dual, we mean either of the type synonyms
`normed_space.dual 𝕜 E` or `weak_dual 𝕜 E`, depending on whether it is viewed as equipped with its
usual operator norm topology or the weak-* topology.

It is shown that the canonical mapping `normed_space.dual 𝕜 E → weak_dual 𝕜 E` is continuous, and
as a consequence the weak-* topology is coarser than the topology obtained from the operator norm
(dual norm).

The file is a stub, some TODOs below.

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

TODOs:
* Add that in finite dimensions, the weak-* topology and the dual norm topology coincide.
* Add that in infinite dimensions, the weak-* topology is strictly coarser than the dual norm
  topology.
* Add Banach-Alaoglu theorem (general version maybe in `topology.algebra.weak_dual_topology`).
* Add metrizability of the dual unit ball (more generally bounded subsets) of `weak_dual 𝕜 E`
  under the assumption of separability of `E`. Sequential Banach-Alaoglu theorem would then follow
  from the general one.

## Notations

No new notation is introduced.

## Implementation notes

Weak-* topology is defined generally in the file `topology.algebra.weak_dual_topology`.

When `E` is a normed space, the duals `dual 𝕜 E` and `weak_dual 𝕜 E` are type synonyms with
different topology instances.

## References

* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology

## Tags

weak-star, weak dual

-/


noncomputable theory

open Filter

open_locale TopologicalSpace

section WeakStarTopologyForDualsOfNormedSpaces

/-!
### Weak star topology on duals of normed spaces
In this section, we prove properties about the weak-* topology on duals of normed spaces.
We prove in particular that the canonical mapping `dual 𝕜 E → weak_dual 𝕜 E` is continuous,
i.e., that the weak-* topology is coarser (not necessarily strictly) than the topology given
by the dual-norm (i.e. the operator-norm).
-/


open NormedSpace

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜]

variable {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]

/-- For normed spaces `E`, there is a canonical map `dual 𝕜 E → weak_dual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. -/
def NormedSpace.Dual.toWeakDual : dual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E :=
  LinearEquiv.refl 𝕜 (E →L[𝕜] 𝕜)

/-- For normed spaces `E`, there is a canonical map `weak_dual 𝕜 E → dual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. Here it is implemented as the inverse of the linear
equivalence `normed_space.dual.to_weak_dual` in the other direction. -/
def WeakDual.toNormedDual : WeakDual 𝕜 E ≃ₗ[𝕜] dual 𝕜 E :=
  NormedSpace.Dual.toWeakDual.symm

@[simp]
theorem WeakDual.coe_to_fun_eq_normed_coe_to_fun (x' : dual 𝕜 E) : (x'.to_weak_dual : E → 𝕜) = x' :=
  rfl

namespace NormedSpace.Dual

@[simp]
theorem to_weak_dual_eq_iff (x' y' : dual 𝕜 E) : x'.to_weak_dual = y'.to_weak_dual ↔ x' = y' :=
  to_weak_dual.Injective.eq_iff

@[simp]
theorem _root_.weak_dual.to_normed_dual_eq_iff (x' y' : WeakDual 𝕜 E) :
  x'.to_normed_dual = y'.to_normed_dual ↔ x' = y' :=
  WeakDual.toNormedDual.Injective.eq_iff

theorem to_weak_dual_continuous : Continuous fun x' : dual 𝕜 E => x'.to_weak_dual :=
  by 
    apply WeakDual.continuous_of_continuous_eval 
    intro z 
    exact (inclusion_in_double_dual 𝕜 E z).Continuous

/-- For a normed space `E`, according to `to_weak_dual_continuous` the "identity mapping"
`dual 𝕜 E → weak_dual 𝕜 E` is continuous. This definition implements it as a continuous linear
map. -/
def continuous_linear_map_to_weak_dual : dual 𝕜 E →L[𝕜] WeakDual 𝕜 E :=
  { to_weak_dual with cont := to_weak_dual_continuous }

/-- The weak-star topology is coarser than the dual-norm topology. -/
theorem dual_norm_topology_le_weak_dual_topology :
  (by 
      infer_instance :
    TopologicalSpace (dual 𝕜 E)) ≤
    (by 
      infer_instance :
    TopologicalSpace (WeakDual 𝕜 E)) :=
  by 
    refine' Continuous.le_induced _ 
    apply continuous_pi_iff.mpr 
    intro z 
    exact (inclusion_in_double_dual 𝕜 E z).Continuous

end NormedSpace.Dual

end WeakStarTopologyForDualsOfNormedSpaces

