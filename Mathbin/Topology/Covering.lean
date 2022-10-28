/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.Topology.IsLocallyHomeomorph
import Mathbin.Topology.FiberBundle

/-!
# Covering Maps

This file defines covering maps.

## Main definitions

* `is_evenly_covered f x I`: A point `x` is evenly coverd by `f : E → X` with fiber `I` if `I` is
  discrete and there is a `trivialization` of `f` at `x` with fiber `I`.
* `is_covering_map f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/


variable {E X : Type _} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

open TopologicalFiberBundle

/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood. -/
def IsEvenlyCovered (x : X) (I : Type _) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ t : Trivialization I f, x ∈ t.BaseSet

namespace IsEvenlyCovered

variable {f}

/-- If `x` is evenly covered by `f`, then we can construct a trivialization of `f` at `x`. -/
noncomputable def toTrivialization {x : X} {I : Type _} [TopologicalSpace I] (h : IsEvenlyCovered f x I) :
    Trivialization (f ⁻¹' {x}) f :=
  (Classical.choose h.2).transFiberHomeomorph
    ((Classical.choose h.2).preimageSingletonHomeomorph (Classical.choose_spec h.2)).symm

theorem mem_to_trivialization_base_set {x : X} {I : Type _} [TopologicalSpace I] (h : IsEvenlyCovered f x I) :
    x ∈ h.toTrivialization.BaseSet :=
  Classical.choose_spec h.2

theorem to_trivialization_apply {x : E} {I : Type _} [TopologicalSpace I] (h : IsEvenlyCovered f (f x) I) :
    (h.toTrivialization x).2 = ⟨x, rfl⟩ :=
  let e := Classical.choose h.2
  let h := Classical.choose_spec h.2
  let he := e.mk_proj_snd' h
  Subtype.ext
    ((e.toLocalEquiv.eq_symm_apply (e.mem_source.mpr h) (by rwa [he, e.mem_target, e.coe_fst (e.mem_source.mpr h)])).mpr
        he.symm).symm

protected theorem continuous_at {x : E} {I : Type _} [TopologicalSpace I] (h : IsEvenlyCovered f (f x) I) :
    ContinuousAt f x :=
  let e := h.toTrivialization
  e.continuous_at_proj (e.mem_source.mpr (mem_to_trivialization_base_set h))

theorem to_is_evenly_covered_preimage {x : X} {I : Type _} [TopologicalSpace I] (h : IsEvenlyCovered f x I) :
    IsEvenlyCovered f x (f ⁻¹' {x}) :=
  let ⟨h1, h2⟩ := h
  ⟨((Classical.choose h2).preimageSingletonHomeomorph (Classical.choose_spec h2)).Embedding.DiscreteTopology, _,
    h.mem_to_trivialization_base_set⟩

end IsEvenlyCovered

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMapOn :=
  ∀ x ∈ s, IsEvenlyCovered f x (f ⁻¹' {x})

namespace IsCoveringMapOn

theorem mk (F : X → Type _) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x ∈ s, Trivialization (F x) f) (h : ∀ (x : X) (hx : x ∈ s), x ∈ (e x hx).BaseSet) : IsCoveringMapOn f s :=
  fun x hx => IsEvenlyCovered.to_is_evenly_covered_preimage ⟨hF x, e x hx, h x hx⟩

variable {f} {s}

protected theorem continuous_at (hf : IsCoveringMapOn f s) {x : E} (hx : f x ∈ s) : ContinuousAt f x :=
  (hf (f x) hx).ContinuousAt

protected theorem continuous_on (hf : IsCoveringMapOn f s) : ContinuousOn f (f ⁻¹' s) :=
  ContinuousAt.continuous_on fun x => hf.ContinuousAt

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
protected theorem is_locally_homeomorph_on (hf : IsCoveringMapOn f s) : IsLocallyHomeomorphOn f (f ⁻¹' s) := by
  refine' IsLocallyHomeomorphOn.mk f (f ⁻¹' s) fun x hx => _
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_to_trivialization_base_set
  let he := e.mem_source.2 h
  refine'
    ⟨e.to_local_homeomorph.trans
        { toFun := fun p => p.1, invFun := fun p => ⟨p, x, rfl⟩,
          Source := e.base_set ×ˢ ({⟨x, rfl⟩} : Set (f ⁻¹' {f x})), Target := e.base_set,
          open_source := e.open_base_set.prod (singletons_open_iff_discrete.2 (hf (f x) hx).1 ⟨x, rfl⟩),
          open_target := e.open_base_set, map_source' := fun p => And.left, map_target' := fun p hp => ⟨hp, rfl⟩,
          left_inv' := fun p hp => Prod.ext rfl hp.2.symm, right_inv' := fun p hp => rfl,
          continuous_to_fun := continuous_fst.continuous_on,
          continuous_inv_fun := (continuous_id'.prod_mk continuous_const).ContinuousOn },
      ⟨he, by rwa [e.to_local_homeomorph.symm_symm, e.proj_to_fun x he], (hf (f x) hx).to_trivialization_apply⟩,
      fun p h => (e.proj_to_fun p h.1).symm⟩

end IsCoveringMapOn

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})

variable {f}

theorem is_covering_map_iff_is_covering_map_on_univ : IsCoveringMap f ↔ IsCoveringMapOn f Set.Univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]

protected theorem IsCoveringMap.is_covering_map_on (hf : IsCoveringMap f) : IsCoveringMapOn f Set.Univ :=
  is_covering_map_iff_is_covering_map_on_univ.mp hf

variable (f)

namespace IsCoveringMap

theorem mk (F : X → Type _) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x ∈ (e x).BaseSet) : IsCoveringMap f :=
  is_covering_map_iff_is_covering_map_on_univ.mpr (IsCoveringMapOn.mk f Set.Univ F (fun x hx => e x) fun x hx => h x)

variable {f}

protected theorem continuous (hf : IsCoveringMap f) : Continuous f :=
  continuous_iff_continuous_on_univ.mpr hf.IsCoveringMapOn.ContinuousOn

protected theorem is_locally_homeomorph (hf : IsCoveringMap f) : IsLocallyHomeomorph f :=
  is_locally_homeomorph_iff_is_locally_homeomorph_on_univ.mpr hf.IsCoveringMapOn.IsLocallyHomeomorphOn

protected theorem is_open_map (hf : IsCoveringMap f) : IsOpenMap f :=
  hf.IsLocallyHomeomorph.IsOpenMap

protected theorem quotient_map (hf : IsCoveringMap f) (hf' : Function.Surjective f) : QuotientMap f :=
  hf.IsOpenMap.to_quotient_map hf.Continuous hf'

end IsCoveringMap

variable {f}

protected theorem IsTopologicalFiberBundle.is_covering_map {F : Type _} [TopologicalSpace F] [DiscreteTopology F]
    (hf : IsTopologicalFiberBundle F f) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun x => F) (fun x => Classical.choose (hf x)) fun x => Classical.choose_spec (hf x)

