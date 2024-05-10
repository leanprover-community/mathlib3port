/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Topology.IsLocalHomeomorph
import Topology.FiberBundle.Basic

#align_import topology.covering from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Covering Maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines covering maps.

## Main definitions

* `is_evenly_covered f x I`: A point `x` is evenly coverd by `f : E → X` with fiber `I` if `I` is
  discrete and there is a `trivialization` of `f` at `x` with fiber `I`.
* `is_covering_map f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/


open scoped Bundle

variable {E X : Type _} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

#print IsEvenlyCovered /-
/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood. -/
def IsEvenlyCovered (x : X) (I : Type _) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ t : Trivialization I f, x ∈ t.baseSet
#align is_evenly_covered IsEvenlyCovered
-/

namespace IsEvenlyCovered

variable {f}

#print IsEvenlyCovered.toTrivialization /-
/-- If `x` is evenly covered by `f`, then we can construct a trivialization of `f` at `x`. -/
noncomputable def toTrivialization {x : X} {I : Type _} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : Trivialization (f ⁻¹' {x}) f :=
  (Classical.choose h.2).transFiberHomeomorph
    ((Classical.choose h.2).preimageSingletonHomeomorph (Classical.choose_spec h.2)).symm
#align is_evenly_covered.to_trivialization IsEvenlyCovered.toTrivialization
-/

#print IsEvenlyCovered.mem_toTrivialization_baseSet /-
theorem mem_toTrivialization_baseSet {x : X} {I : Type _} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : x ∈ h.toTrivialization.baseSet :=
  Classical.choose_spec h.2
#align is_evenly_covered.mem_to_trivialization_base_set IsEvenlyCovered.mem_toTrivialization_baseSet
-/

#print IsEvenlyCovered.toTrivialization_apply /-
theorem toTrivialization_apply {x : E} {I : Type _} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : (h.toTrivialization x).2 = ⟨x, rfl⟩ :=
  let e := Classical.choose h.2
  let h := Classical.choose_spec h.2
  let he := e.mk_proj_snd' h
  Subtype.ext
    ((e.toPartialEquiv.eq_symm_apply (e.mem_source.mpr h)
            (by rwa [he, e.mem_target, e.coe_fst (e.mem_source.mpr h)])).mpr
        he.symm).symm
#align is_evenly_covered.to_trivialization_apply IsEvenlyCovered.toTrivialization_apply
-/

#print IsEvenlyCovered.continuousAt /-
protected theorem continuousAt {x : E} {I : Type _} [TopologicalSpace I]
    (h : IsEvenlyCovered f (f x) I) : ContinuousAt f x :=
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))
#align is_evenly_covered.continuous_at IsEvenlyCovered.continuousAt
-/

#print IsEvenlyCovered.to_isEvenlyCovered_preimage /-
theorem to_isEvenlyCovered_preimage {x : X} {I : Type _} [TopologicalSpace I]
    (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x}) :=
  let ⟨h1, h2⟩ := h
  ⟨((Classical.choose h2).preimageSingletonHomeomorph
          (Classical.choose_spec h2)).Embedding.DiscreteTopology,
    _, h.mem_to_trivialization_base_set⟩
#align is_evenly_covered.to_is_evenly_covered_preimage IsEvenlyCovered.to_isEvenlyCovered_preimage
-/

end IsEvenlyCovered

#print IsCoveringMapOn /-
/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMapOn :=
  ∀ x ∈ s, IsEvenlyCovered f x (f ⁻¹' {x})
#align is_covering_map_on IsCoveringMapOn
-/

namespace IsCoveringMapOn

#print IsCoveringMapOn.mk /-
theorem mk (F : X → Type _) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x ∈ s, Trivialization (F x) f) (h : ∀ (x : X) (hx : x ∈ s), x ∈ (e x hx).baseSet) :
    IsCoveringMapOn f s := fun x hx =>
  IsEvenlyCovered.to_isEvenlyCovered_preimage ⟨hF x, e x hx, h x hx⟩
#align is_covering_map_on.mk IsCoveringMapOn.mk
-/

variable {f} {s}

#print IsCoveringMapOn.continuousAt /-
protected theorem continuousAt (hf : IsCoveringMapOn f s) {x : E} (hx : f x ∈ s) :
    ContinuousAt f x :=
  (hf (f x) hx).ContinuousAt
#align is_covering_map_on.continuous_at IsCoveringMapOn.continuousAt
-/

#print IsCoveringMapOn.continuousOn /-
protected theorem continuousOn (hf : IsCoveringMapOn f s) : ContinuousOn f (f ⁻¹' s) :=
  ContinuousAt.continuousOn fun x => hf.ContinuousAt
#align is_covering_map_on.continuous_on IsCoveringMapOn.continuousOn
-/

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print IsCoveringMapOn.isLocalHomeomorphOn /-
protected theorem isLocalHomeomorphOn (hf : IsCoveringMapOn f s) :
    IsLocalHomeomorphOn f (f ⁻¹' s) :=
  by
  refine' IsLocalHomeomorphOn.mk f (f ⁻¹' s) fun x hx => _
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine'
    ⟨e.to_local_homeomorph.trans
        { toFun := fun p => p.1
          invFun := fun p => ⟨p, x, rfl⟩
          source := e.base_set ×ˢ ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))
          target := e.base_set
          open_source :=
            e.open_base_set.prod (singletons_open_iff_discrete.2 (hf (f x) hx).1 ⟨x, rfl⟩)
          open_target := e.open_base_set
          map_source' := fun p => And.left
          map_target' := fun p hp => ⟨hp, rfl⟩
          left_inv' := fun p hp => Prod.ext rfl hp.2.symm
          right_inv' := fun p hp => rfl
          continuous_toFun := continuous_fst.continuous_on
          continuous_invFun := (continuous_id'.prod_mk continuous_const).ContinuousOn },
      ⟨he, by rwa [e.to_local_homeomorph.symm_symm, e.proj_to_fun x he],
        (hf (f x) hx).toTrivialization_apply⟩,
      fun p h => (e.proj_to_fun p h.1).symm⟩
#align is_covering_map_on.is_locally_homeomorph_on IsCoveringMapOn.isLocalHomeomorphOn
-/

end IsCoveringMapOn

#print IsCoveringMap /-
/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})
#align is_covering_map IsCoveringMap
-/

variable {f}

#print isCoveringMap_iff_isCoveringMapOn_univ /-
theorem isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn f Set.univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]
#align is_covering_map_iff_is_covering_map_on_univ isCoveringMap_iff_isCoveringMapOn_univ
-/

#print IsCoveringMap.isCoveringMapOn /-
protected theorem IsCoveringMap.isCoveringMapOn (hf : IsCoveringMap f) :
    IsCoveringMapOn f Set.univ :=
  isCoveringMap_iff_isCoveringMapOn_univ.mp hf
#align is_covering_map.is_covering_map_on IsCoveringMap.isCoveringMapOn
-/

variable (f)

namespace IsCoveringMap

#print IsCoveringMap.mk /-
theorem mk (F : X → Type _) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x ∈ (e x).baseSet) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr
    (IsCoveringMapOn.mk f Set.univ F (fun x hx => e x) fun x hx => h x)
#align is_covering_map.mk IsCoveringMap.mk
-/

variable {f}

#print IsCoveringMap.continuous /-
protected theorem continuous (hf : IsCoveringMap f) : Continuous f :=
  continuous_iff_continuousOn_univ.mpr hf.IsCoveringMapOn.ContinuousOn
#align is_covering_map.continuous IsCoveringMap.continuous
-/

#print IsCoveringMap.isLocalHomeomorph /-
protected theorem isLocalHomeomorph (hf : IsCoveringMap f) : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr hf.IsCoveringMapOn.IsLocalHomeomorphOn
#align is_covering_map.is_locally_homeomorph IsCoveringMap.isLocalHomeomorph
-/

#print IsCoveringMap.isOpenMap /-
protected theorem isOpenMap (hf : IsCoveringMap f) : IsOpenMap f :=
  hf.IsLocalHomeomorph.IsOpenMap
#align is_covering_map.is_open_map IsCoveringMap.isOpenMap
-/

#print IsCoveringMap.quotientMap /-
protected theorem quotientMap (hf : IsCoveringMap f) (hf' : Function.Surjective f) :
    QuotientMap f :=
  hf.IsOpenMap.to_quotientMap hf.Continuous hf'
#align is_covering_map.quotient_map IsCoveringMap.quotientMap
-/

end IsCoveringMap

variable {f}

#print IsFiberBundle.isCoveringMap /-
protected theorem IsFiberBundle.isCoveringMap {F : Type _} [TopologicalSpace F] [DiscreteTopology F]
    (hf : ∀ x : X, ∃ e : Trivialization F f, x ∈ e.baseSet) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun x => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)
#align is_fiber_bundle.is_covering_map IsFiberBundle.isCoveringMap
-/

#print FiberBundle.isCoveringMap /-
protected theorem FiberBundle.isCoveringMap {F : Type _} {E : X → Type _} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [hf : FiberBundle F E] : IsCoveringMap (π F E) :=
  IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩
#align fiber_bundle.is_covering_map FiberBundle.isCoveringMap
-/

