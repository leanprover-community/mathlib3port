/-
Copyright (c) 2021 Kalle KytΓΆlΓ€. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle KytΓΆlΓ€, Moritz Doll
-/
import Mathbin.Topology.Algebra.Module.Basic

/-!
# Weak dual topology

This file defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`π` and a bilinear form `B : E ββ[π] F ββ[π] π`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `Ξ» x, B x y` is continuous.

In the case that `F = E βL[π] π` and `B` being the canonical pairing, we obtain the weak-* topology,
`weak_dual π E := (E βL[π] π)`. Interchanging the arguments in the bilinear form yields the
weak topology `weak_space π E := E`.

## Main definitions

The main definitions are the types `weak_bilin B` for the general case and the two special cases
`weak_dual π E` and `weak_space π E` with the respective topology instances on it.

* Given `B : E ββ[π] F ββ[π] π`, the type `weak_bilin B` is a type synonym for `E`.
* The instance `weak_bilin.topological_space` is the weak topology induced by the bilinear form `B`.
* `weak_dual π E` is a type synonym for `dual π E` (when the latter is defined): both are equal to
  the type `E βL[π] π` of continuous linear maps from a module `E` over `π` to the ring `π`.
* The instance `weak_dual.topological_space` is the weak-* topology on `weak_dual π E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `weak_space π E` is a type synonym for `E` (when the latter is defined).
* The instance `weak_dual.topological_space` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : dual π E` remain continuous.

## Main results

We establish that `weak_bilin B` has the following structure:
* `weak_bilin.has_continuous_add`: The addition in `weak_bilin B` is continuous.
* `weak_bilin.has_continuous_smul`: The scalar multiplication in `weak_bilin B` is continuous.

We prove the following results characterizing the weak topology:
* `eval_continuous`: For any `y : F`, the evaluation mapping `Ξ» x, B x y` is continuous.
* `continuous_of_continuous_eval`: For a mapping to `weak_bilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `tendsto_iff_forall_eval_tendsto`: Convergence in `weak_bilin B` can be characterized
  in terms of convergence of the evaluations at all points `y : F`.

## Notations

No new notation is introduced.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/


noncomputable section

open Filter

open TopologicalSpace

variable {Ξ± π π R E F M : Type _}

section WeakTopology

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module π
/-- The space `E` equipped with the weak topology induced by the bilinear form `B`. -/
@[nolint has_inhabited_instance unused_arguments]
def WeakBilin [CommSemiringβ π] [AddCommMonoidβ E] [Module π E] [AddCommMonoidβ F] [Module π F]
    (B : E ββ[π] F ββ[π] π) :=
  E deriving AddCommMonoidβ, Β«./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module πΒ»

namespace WeakBilin

instance [CommSemiringβ π] [a : AddCommGroupβ E] [Module π E] [AddCommMonoidβ F] [Module π F] (B : E ββ[π] F ββ[π] π) :
    AddCommGroupβ (WeakBilin B) :=
  a

instance (priority := 100) module' [CommSemiringβ π] [CommSemiringβ π] [AddCommGroupβ E] [Module π E] [AddCommGroupβ F]
    [Module π F] [m : Module π E] (B : E ββ[π] F ββ[π] π) : Module π (WeakBilin B) :=
  m

instance [CommSemiringβ π] [CommSemiringβ π] [AddCommGroupβ E] [Module π E] [AddCommGroupβ F] [Module π F] [HasSmul π π]
    [Module π E] [s : IsScalarTower π π E] (B : E ββ[π] F ββ[π] π) : IsScalarTower π π (WeakBilin B) :=
  s

section Semiringβ

variable [TopologicalSpace π] [CommSemiringβ π]

variable [AddCommMonoidβ E] [Module π E]

variable [AddCommMonoidβ F] [Module π F]

variable (B : E ββ[π] F ββ[π] π)

instance : TopologicalSpace (WeakBilin B) :=
  TopologicalSpace.induced (fun x y => B x y) Pi.topologicalSpace

theorem coe_fn_continuous : Continuous fun (x : WeakBilin B) y => B x y :=
  continuous_induced_dom

theorem eval_continuous (y : F) : Continuous fun x : WeakBilin B => B x y :=
  (continuous_pi_iff.mp (coe_fn_continuous B)) y

theorem continuous_of_continuous_eval [TopologicalSpace Ξ±] {g : Ξ± β WeakBilin B}
    (h : β y, Continuous fun a => B (g a) y) : Continuous g :=
  continuous_induced_rng (continuous_pi_iff.mpr h)

/-- The coercion `(Ξ» x y, B x y) : E β (F β π)` is an embedding. -/
theorem embedding {B : E ββ[π] F ββ[π] π} (hB : Function.Injective B) : Embedding fun (x : WeakBilin B) y => B x y :=
  Function.Injective.embedding_induced <| LinearMap.coe_injective.comp hB

theorem tendsto_iff_forall_eval_tendsto {l : Filter Ξ±} {f : Ξ± β WeakBilin B} {x : WeakBilin B}
    (hB : Function.Injective B) : Tendsto f l (π x) β β y, Tendsto (fun i => B (f i) y) l (π (B x y)) := by
  rw [β tendsto_pi_nhds, Embedding.tendsto_nhds_iff (Embedding hB)]

/-- Addition in `weak_space B` is continuous. -/
instance [HasContinuousAdd π] : HasContinuousAdd (WeakBilin B) := by
  refine' β¨continuous_induced_rng _β©
  refine'
    cast (congr_arg _ _) (((coe_fn_continuous B).comp continuous_fst).add ((coe_fn_continuous B).comp continuous_snd))
  ext
  simp only [β Function.comp_app, β Pi.add_apply, β map_add, β LinearMap.add_apply]

/-- Scalar multiplication by `π` on `weak_bilin B` is continuous. -/
instance [HasContinuousSmul π π] : HasContinuousSmul π (WeakBilin B) := by
  refine' β¨continuous_induced_rng _β©
  refine' cast (congr_arg _ _) (continuous_fst.smul ((coe_fn_continuous B).comp continuous_snd))
  ext
  simp only [β Function.comp_app, β Pi.smul_apply, β LinearMap.map_smulββ, β RingHom.id_apply, β LinearMap.smul_apply]

end Semiringβ

section Ringβ

variable [TopologicalSpace π] [CommRingβ π]

variable [AddCommGroupβ E] [Module π E]

variable [AddCommGroupβ F] [Module π F]

variable (B : E ββ[π] F ββ[π] π)

/-- `weak_space B` is a `topological_add_group`, meaning that addition and negation are
continuous. -/
instance [HasContinuousAdd π] : TopologicalAddGroup (WeakBilin B) where
  to_has_continuous_add := by
    infer_instance
  continuous_neg := by
    refine' continuous_induced_rng (continuous_pi_iff.mpr fun y => _)
    refine' cast (congr_arg _ _) (eval_continuous B (-y))
    ext
    simp only [β map_neg, β Function.comp_app, β LinearMap.neg_apply]

end Ringβ

end WeakBilin

end WeakTopology

section WeakStarTopology

/-- The canonical pairing of a vector space and its topological dual. -/
def topDualPairing (π E) [CommSemiringβ π] [TopologicalSpace π] [HasContinuousAdd π] [AddCommMonoidβ E] [Module π E]
    [TopologicalSpace E] [HasContinuousConstSmul π π] : (E βL[π] π) ββ[π] E ββ[π] π :=
  ContinuousLinearMap.coeLm π

variable [CommSemiringβ π] [TopologicalSpace π] [HasContinuousAdd π]

variable [HasContinuousConstSmul π π]

variable [AddCommMonoidβ E] [Module π E] [TopologicalSpace E]

theorem dual_pairing_apply (v : E βL[π] π) (x : E) : topDualPairing π E v x = v x :=
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module π
/-- The weak star topology is the topology coarsest topology on `E βL[π] π` such that all
functionals `Ξ» v, top_dual_pairing π E v x` are continuous. -/
def WeakDual (π E) [CommSemiringβ π] [TopologicalSpace π] [HasContinuousAdd π] [HasContinuousConstSmul π π]
    [AddCommMonoidβ E] [Module π E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing π E)deriving AddCommMonoidβ,
  Β«./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module πΒ», TopologicalSpace,
  HasContinuousAdd

namespace WeakDual

instance : Inhabited (WeakDual π E) :=
  ContinuousLinearMap.inhabited

instance WeakDual.continuousLinearMapClass : ContinuousLinearMapClass (WeakDual π E) π E π :=
  ContinuousLinearMap.continuousSemilinearMapClass

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (WeakDual π E) fun _ => E β π :=
  FunLike.hasCoeToFun

/-- If a monoid `M` distributively continuously acts on `π` and this action commutes with
multiplication on `π`, then it acts on `weak_dual π E`. -/
instance (M) [Monoidβ M] [DistribMulAction M π] [SmulCommClass π M π] [HasContinuousConstSmul M π] :
    MulAction M (WeakDual π E) :=
  ContinuousLinearMap.mulAction

/-- If a monoid `M` distributively continuously acts on `π` and this action commutes with
multiplication on `π`, then it acts distributively on `weak_dual π E`. -/
instance (M) [Monoidβ M] [DistribMulAction M π] [SmulCommClass π M π] [HasContinuousConstSmul M π] :
    DistribMulAction M (WeakDual π E) :=
  ContinuousLinearMap.distribMulAction

/-- If `π` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `π`, then `weak_dual π E` is a module over `R`. -/
instance module' (R) [Semiringβ R] [Module R π] [SmulCommClass π R π] [HasContinuousConstSmul R π] :
    Module R (WeakDual π E) :=
  ContinuousLinearMap.module

instance (M) [Monoidβ M] [DistribMulAction M π] [SmulCommClass π M π] [HasContinuousConstSmul M π] :
    HasContinuousConstSmul M (WeakDual π E) :=
  β¨fun m => continuous_induced_rng <| (WeakBilin.coe_fn_continuous (topDualPairing π E)).const_smul mβ©

/-- If a monoid `M` distributively continuously acts on `π` and this action commutes with
multiplication on `π`, then it continuously acts on `weak_dual π E`. -/
instance (M) [Monoidβ M] [DistribMulAction M π] [SmulCommClass π M π] [TopologicalSpace M] [HasContinuousSmul M π] :
    HasContinuousSmul M (WeakDual π E) :=
  β¨continuous_induced_rng <|
      continuous_fst.smul ((WeakBilin.coe_fn_continuous (topDualPairing π E)).comp continuous_snd)β©

theorem coe_fn_continuous : Continuous fun (x : WeakDual π E) y => x y :=
  continuous_induced_dom

theorem eval_continuous (y : E) : Continuous fun x : WeakDual π E => x y :=
  continuous_pi_iff.mp coe_fn_continuous y

theorem continuous_of_continuous_eval [TopologicalSpace Ξ±] {g : Ξ± β WeakDual π E}
    (h : β y, Continuous fun a => (g a) y) : Continuous g :=
  continuous_induced_rng (continuous_pi_iff.mpr h)

end WeakDual

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module π
/-- The weak topology is the topology coarsest topology on `E` such that all
functionals `Ξ» x, top_dual_pairing π E v x` are continuous. -/
@[nolint has_inhabited_instance]
def WeakSpace (π E) [CommSemiringβ π] [TopologicalSpace π] [HasContinuousAdd π] [HasContinuousConstSmul π π]
    [AddCommMonoidβ E] [Module π E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing π E).flip deriving AddCommMonoidβ,
  Β«./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module πΒ», TopologicalSpace,
  HasContinuousAdd

theorem tendsto_iff_forall_eval_tendsto_top_dual_pairing {l : Filter Ξ±} {f : Ξ± β WeakDual π E} {x : WeakDual π E} :
    Tendsto f l (π x) β β y, Tendsto (fun i => topDualPairing π E (f i) y) l (π (topDualPairing π E x y)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective

end WeakStarTopology

