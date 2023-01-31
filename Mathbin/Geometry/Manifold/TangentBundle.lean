/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module geometry.manifold.tangent_bundle
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.VectorBundle.Basic
import Mathbin.Geometry.Manifold.SmoothManifoldWithCorners
import Mathbin.Data.Set.Prod

/-!
# Basic smooth bundles

In general, a smooth bundle is a bundle over a smooth manifold, whose fiber is a manifold, and
for which the coordinate changes are smooth. In this definition, there are charts involved at
several places: in the manifold structure of the base, in the manifold structure of the fibers, and
in the local trivializations. This makes it a complicated object in general. There is however a
specific situation where things are much simpler: when the fiber is a vector space (no need for
charts for the fibers), and when the local trivializations of the bundle and the charts of the base
coincide. Then everything is expressed in terms of the charts of the base, making for a much
simpler overall structure, which is easier to manipulate formally.

Most vector bundles that naturally occur in differential geometry are of this form:
the tangent bundle, the cotangent bundle, differential forms (used to define de Rham cohomology)
and the bundle of Riemannian metrics. Therefore, it is worth defining a specific constructor for
this kind of bundle, that we call basic smooth bundles.

A basic smooth bundle is thus a smooth bundle over a smooth manifold whose fiber is a vector space,
and which is trivial in the coordinate charts of the base. (We recall that in our notion of manifold
there is a distinguished atlas, which does not need to be maximal: we require the triviality above
this specific atlas). It can be constructed from a basic smooth bundled core, defined below,
specifying the changes in the fiber when one goes from one coordinate chart to another one.

## Main definitions

* `basic_smooth_vector_bundle_core I M F`: assuming that `M` is a smooth manifold over the model
  with corners `I` on `(𝕜, E, H)`, and `F` is a normed vector space over `𝕜`, this structure
  registers, for each pair of charts of `M`, a linear change of coordinates on `F` depending
  smoothly on the base point. This is the core structure from which one will build a smooth vector
  bundle with fiber `F` over `M`.

Let `Z` be a basic smooth bundle core over `M` with fiber `F`. We define
`Z.to_vector_bundle_core`, the (topological) vector bundle core associated to `Z`. From
it, we get a space `Z.to_vector_bundle_core.total_space` (which as a Type is just
`Σ (x : M), F`), with the fiber bundle topology. It inherits a manifold structure (where the
charts are in bijection with the charts of the basis). We show that this manifold is smooth.

Then we use this machinery to construct the tangent bundle of a smooth manifold.

* `tangent_bundle_core I M`: the basic smooth bundle core associated to a smooth manifold `M` over
  a model with corners `I`.
* `tangent_bundle I M`     : the total space of `tangent_bundle_core I M`. It is itself a
  smooth manifold over the model with corners `I.tangent`, the product of `I` and the trivial model
  with corners on `E`.
* `tangent_space I x`      : the tangent space to `M` at `x`
* `tangent_bundle.proj I M`: the projection from the tangent bundle to the base manifold

## Implementation notes

We register the vector space structure on the fibers of the tangent bundle, but we do not register
the normed space structure coming from that of `F` (as it is not canonical, and we also want to
keep the possibility to add a Riemannian structure on the manifold later on without having two
competing normed space instances on the tangent spaces).

We require `F` to be a normed space, and not just a topological vector space, as we want to talk
about smooth functions on `F`. The notion of derivative requires a norm to be defined.

## TODO
construct the cotangent bundle, and the bundles of differential forms. They should follow
functorially from the description of the tangent bundle as a basic smooth bundle.

## Tags
Smooth fiber bundle, vector bundle, tangent space, tangent bundle
-/


noncomputable section

universe u

open TopologicalSpace Set

open Manifold Topology

/-- Core structure used to create a smooth bundle above `M` (a manifold over the model with
corner `I`) with fiber the normed vector space `F` over `𝕜`, which is trivial in the chart domains
of `M`. This structure registers the changes in the fibers when one changes coordinate charts in the
base. We require the change of coordinates of the fibers to be linear, so that the resulting bundle
is a vector bundle. -/
structure BasicSmoothVectorBundleCore {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] (F : Type _) [NormedAddCommGroup F] [NormedSpace 𝕜 F] where
  coordChange : atlas H M → atlas H M → H → F →L[𝕜] F
  coordChange_self : ∀ i : atlas H M, ∀ x ∈ i.1.target, ∀ v, coord_change i i x v = v
  coordChange_comp :
    ∀ i j k : atlas H M,
      ∀ x ∈ ((i.1.symm.trans j.1).trans (j.1.symm.trans k.1)).source,
        ∀ v,
          (coord_change j k ((i.1.symm.trans j.1) x)) (coord_change i j x v) = coord_change i k x v
  coordChange_smooth_clm :
    ∀ i j : atlas H M, ContDiffOn 𝕜 ∞ (coord_change i j ∘ I.symm) (I '' (i.1.symm.trans j.1).source)
#align basic_smooth_vector_bundle_core BasicSmoothVectorBundleCore

/-- The trivial basic smooth bundle core, in which all the changes of coordinates are the
identity. -/
def trivialBasicSmoothVectorBundleCore {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] (F : Type _) [NormedAddCommGroup F] [NormedSpace 𝕜 F] :
    BasicSmoothVectorBundleCore I M F
    where
  coordChange i j x := ContinuousLinearMap.id 𝕜 F
  coordChange_self i x hx v := rfl
  coordChange_comp i j k x hx v := rfl
  coordChange_smooth_clm i j := by
    dsimp
    exact contDiffOn_const
#align trivial_basic_smooth_vector_bundle_core trivialBasicSmoothVectorBundleCore

namespace BasicSmoothVectorBundleCore

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (Z : BasicSmoothVectorBundleCore I M F)

instance : Inhabited (BasicSmoothVectorBundleCore I M F) :=
  ⟨trivialBasicSmoothVectorBundleCore I M F⟩

/-- A reformulation of `coord_change_comp`, formulated in terms of a point in `M`.
The conditions on this point a significantly simpler than in `coord_change_comp`. -/
theorem coordChange_comp' {i j k : atlas H M} {x : M} (hi : x ∈ i.1.source) (hj : x ∈ j.1.source)
    (hk : x ∈ k.1.source) (v : F) :
    Z.coordChange j k (j x) (Z.coordChange i j (i x) v) = Z.coordChange i k (i x) v :=
  by
  rw [show j x = _ by rw [← i.1.left_inv hi]]
  apply Z.coord_change_comp
  simp only [hi, hj, hk, mfld_simps]
#align basic_smooth_vector_bundle_core.coord_change_comp' BasicSmoothVectorBundleCore.coordChange_comp'

/-- A reformulation of `coord_change_self`, formulated in terms of a point in `M`. -/
theorem coordChange_self' {i : atlas H M} {x : M} (hi : x ∈ i.1.source) (v : F) :
    Z.coordChange i i (i x) v = v :=
  Z.coordChange_self i (i x) (i.1.MapsTo hi) v
#align basic_smooth_vector_bundle_core.coord_change_self' BasicSmoothVectorBundleCore.coordChange_self'

/-- `Z.coord_change j i` is a partial inverse of `Z.coord_change i j`. -/
theorem coordChange_comp_eq_self (i j : atlas H M) {x : H} (hx : x ∈ (i.1.symm.trans j.1).source)
    (v : F) : Z.coordChange j i (i.1.symm.trans j.1 x) (Z.coordChange i j x v) = v :=
  by
  rw [Z.coord_change_comp i j i x _ v, Z.coord_change_self _ _ hx.1]
  simp only [mfld_simps] at hx
  simp only [hx.1, hx.2, mfld_simps]
#align basic_smooth_vector_bundle_core.coord_change_comp_eq_self BasicSmoothVectorBundleCore.coordChange_comp_eq_self

/-- `Z.coord_change j i` is a partial inverse of `Z.coord_change i j`,
formulated in terms of a point in `M`. -/
theorem coordChange_comp_eq_self' {i j : atlas H M} {x : M} (hi : x ∈ i.1.source)
    (hj : x ∈ j.1.source) (v : F) : Z.coordChange j i (j x) (Z.coordChange i j (i x) v) = v := by
  rw [Z.coord_change_comp' hi hj hi v, Z.coord_change_self' hi]
#align basic_smooth_vector_bundle_core.coord_change_comp_eq_self' BasicSmoothVectorBundleCore.coordChange_comp_eq_self'

theorem coordChange_continuous (i j : atlas H M) :
    ContinuousOn (Z.coordChange i j) (i.1.symm.trans j.1).source :=
  by
  intro x hx
  apply
    (((Z.coord_change_smooth_clm i j).ContinuousOn.ContinuousWithinAt (mem_image_of_mem I hx)).comp
        I.continuous_within_at _).congr
  · intro y hy
    simp only [mfld_simps]
  · simp only [mfld_simps]
  · exact maps_to_image I _
#align basic_smooth_vector_bundle_core.coord_change_continuous BasicSmoothVectorBundleCore.coordChange_continuous

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem coordChange_smooth (i j : atlas H M) :
    ContDiffOn 𝕜 ∞ (fun p : E × F => Z.coordChange i j (I.symm p.1) p.2)
      ((I '' (i.1.symm.trans j.1).source) ×ˢ univ) :=
  by
  have A : ContDiff 𝕜 ∞ fun p : (F →L[𝕜] F) × F => p.1 p.2 :=
    by
    apply IsBoundedBilinearMap.contDiff
    exact isBoundedBilinearMapApply
  have B :
    ContDiffOn 𝕜 ∞ (fun p : E × F => (Z.coord_change i j (I.symm p.1), p.snd))
      ((I '' (i.1.symm.trans j.1).source) ×ˢ univ) :=
    by
    apply ContDiffOn.prod _ _
    ·
      exact
        (Z.coord_change_smooth_clm i j).comp cont_diff_fst.cont_diff_on
          (prod_subset_preimage_fst _ _)
    · exact is_bounded_linear_map.snd.cont_diff.cont_diff_on
  exact A.comp_cont_diff_on B
#align basic_smooth_vector_bundle_core.coord_change_smooth BasicSmoothVectorBundleCore.coordChange_smooth

/-- Vector bundle core associated to a basic smooth bundle core -/
@[simps coordChange indexAt]
def toVectorBundleCore : VectorBundleCore 𝕜 M F (atlas H M)
    where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at x := mem_chart_source H x
  coordChange i j x := Z.coordChange i j (i.1 x)
  coordChange_self i x hx v := Z.coordChange_self i (i.1 x) (i.1.map_source hx) v
  coordChange_comp := fun i j k x ⟨⟨hx1, hx2⟩, hx3⟩ v =>
    by
    have := Z.coord_change_comp i j k (i.1 x) _ v
    convert this using 2
    · simp only [hx1, mfld_simps]
    · simp only [hx1, hx2, hx3, mfld_simps]
  continuousOn_coordChange i j :=
    by
    refine' ((Z.coord_change_continuous i j).comp' i.1.ContinuousOn).mono _
    rintro p ⟨hp₁, hp₂⟩
    refine' ⟨hp₁, i.1.MapsTo hp₁, _⟩
    simp only [i.1.left_inv hp₁, hp₂, mfld_simps]
#align basic_smooth_vector_bundle_core.to_vector_bundle_core BasicSmoothVectorBundleCore.toVectorBundleCore

@[simp, mfld_simps]
theorem baseSet (i : atlas H M) : (Z.toVectorBundleCore.localTriv i).baseSet = i.1.source :=
  rfl
#align basic_smooth_vector_bundle_core.base_set BasicSmoothVectorBundleCore.baseSet

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, mfld_simps]
theorem target (i : atlas H M) : (Z.toVectorBundleCore.localTriv i).target = i.1.source ×ˢ univ :=
  rfl
#align basic_smooth_vector_bundle_core.target BasicSmoothVectorBundleCore.target

/-- Local chart for the total space of a basic smooth bundle -/
def chart {e : LocalHomeomorph M H} (he : e ∈ atlas H M) :
    LocalHomeomorph Z.toVectorBundleCore.TotalSpace (ModelProd H F) :=
  (Z.toVectorBundleCore.localTriv ⟨e, he⟩).toLocalHomeomorph.trans
    (LocalHomeomorph.prod e (LocalHomeomorph.refl F))
#align basic_smooth_vector_bundle_core.chart BasicSmoothVectorBundleCore.chart

theorem chart_apply {x : M} (z : Z.toVectorBundleCore.TotalSpace) :
    Z.chart (chart_mem_atlas H x) z =
      (chartAt H x z.proj,
        Z.coordChange (achart H z.proj) (achart H x) (achart H z.proj z.proj) z.2) :=
  rfl
#align basic_smooth_vector_bundle_core.chart_apply BasicSmoothVectorBundleCore.chart_apply

@[simp, mfld_simps]
theorem chart_source (e : LocalHomeomorph M H) (he : e ∈ atlas H M) :
    (Z.chart he).source = Z.toVectorBundleCore.proj ⁻¹' e.source :=
  by
  simp only [chart, mem_prod]
  mfld_set_tac
#align basic_smooth_vector_bundle_core.chart_source BasicSmoothVectorBundleCore.chart_source

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, mfld_simps]
theorem chart_target (e : LocalHomeomorph M H) (he : e ∈ atlas H M) :
    (Z.chart he).target = e.target ×ˢ univ :=
  by
  simp only [chart]
  mfld_set_tac
#align basic_smooth_vector_bundle_core.chart_target BasicSmoothVectorBundleCore.chart_target

/-- The total space of a basic smooth bundle is endowed with a charted space structure, where the
charts are in bijection with the charts of the basis. -/
@[simps (config := lemmasOnly) chartAt]
instance toChartedSpace : ChartedSpace (ModelProd H F) Z.toVectorBundleCore.TotalSpace
    where
  atlas := ⋃ (e : LocalHomeomorph M H) (he : e ∈ atlas H M), {Z.chart he}
  chartAt p := Z.chart (chart_mem_atlas H p.1)
  mem_chart_source p := by simp [mem_chart_source]
  chart_mem_atlas p :=
    by
    simp only [mem_Union, mem_singleton_iff, chart_mem_atlas]
    exact ⟨chart_at H p.1, chart_mem_atlas H p.1, rfl⟩
#align basic_smooth_vector_bundle_core.to_charted_space BasicSmoothVectorBundleCore.toChartedSpace

theorem mem_atlas_iff (f : LocalHomeomorph Z.toVectorBundleCore.TotalSpace (ModelProd H F)) :
    f ∈ atlas (ModelProd H F) Z.toVectorBundleCore.TotalSpace ↔
      ∃ (e : LocalHomeomorph M H)(he : e ∈ atlas H M), f = Z.chart he :=
  by simp only [atlas, mem_Union, mem_singleton_iff]
#align basic_smooth_vector_bundle_core.mem_atlas_iff BasicSmoothVectorBundleCore.mem_atlas_iff

@[simp, mfld_simps]
theorem mem_chart_source_iff (p q : Z.toVectorBundleCore.TotalSpace) :
    p ∈ (chartAt (ModelProd H F) q).source ↔ p.1 ∈ (chartAt H q.1).source := by
  simp only [chart_at, mfld_simps]
#align basic_smooth_vector_bundle_core.mem_chart_source_iff BasicSmoothVectorBundleCore.mem_chart_source_iff

@[simp, mfld_simps]
theorem mem_chart_target_iff (p : H × F) (q : Z.toVectorBundleCore.TotalSpace) :
    p ∈ (chartAt (ModelProd H F) q).target ↔ p.1 ∈ (chartAt H q.1).target := by
  simp only [chart_at, mfld_simps]
#align basic_smooth_vector_bundle_core.mem_chart_target_iff BasicSmoothVectorBundleCore.mem_chart_target_iff

@[simp, mfld_simps]
theorem coe_chartAt_fst (p q : Z.toVectorBundleCore.TotalSpace) :
    ((chartAt (ModelProd H F) q) p).1 = chartAt H q.1 p.1 :=
  rfl
#align basic_smooth_vector_bundle_core.coe_chart_at_fst BasicSmoothVectorBundleCore.coe_chartAt_fst

@[simp, mfld_simps]
theorem coe_chartAt_symm_fst (p : H × F) (q : Z.toVectorBundleCore.TotalSpace) :
    ((chartAt (ModelProd H F) q).symm p).1 = ((chartAt H q.1).symm : H → M) p.1 :=
  rfl
#align basic_smooth_vector_bundle_core.coe_chart_at_symm_fst BasicSmoothVectorBundleCore.coe_chartAt_symm_fst

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Smooth manifold structure on the total space of a basic smooth bundle -/
instance to_smooth_manifold :
    SmoothManifoldWithCorners (I.Prod 𝓘(𝕜, F)) Z.toVectorBundleCore.TotalSpace :=
  by
  /- We have to check that the charts belong to the smooth groupoid, i.e., they are smooth on their
    source, and their inverses are smooth on the target. Since both objects are of the same kind, it
    suffices to prove the first statement in A below, and then glue back the pieces at the end. -/
  let J := ModelWithCorners.toLocalEquiv (I.prod 𝓘(𝕜, F))
  have A :
    ∀ (e e' : LocalHomeomorph M H) (he : e ∈ atlas H M) (he' : e' ∈ atlas H M),
      ContDiffOn 𝕜 ∞ (J ∘ (Z.chart he).symm.trans (Z.chart he') ∘ J.symm)
        (J.symm ⁻¹' ((Z.chart he).symm.trans (Z.chart he')).source ∩ range J) :=
    by
    intro e e' he he'
    have :
      J.symm ⁻¹' ((chart Z he).symm.trans (chart Z he')).source ∩ range J =
        (I.symm ⁻¹' (e.symm.trans e').source ∩ range I) ×ˢ univ :=
      by
      simp only [J, chart, ModelWithCorners.prod]
      mfld_set_tac
    rw [this]
    -- check separately that the two components of the coordinate change are smooth
    apply ContDiffOn.prod
    show
      ContDiffOn 𝕜 ∞ (fun p : E × F => (I ∘ e' ∘ e.symm ∘ I.symm) p.1)
        ((I.symm ⁻¹' (e.symm.trans e').source ∩ range I) ×ˢ univ)
    · -- the coordinate change on the base is just a coordinate change for `M`, smooth since
      -- `M` is smooth
      have A :
        ContDiffOn 𝕜 ∞ (I ∘ e.symm.trans e' ∘ I.symm)
          (I.symm ⁻¹' (e.symm.trans e').source ∩ range I) :=
        (HasGroupoid.compatible (contDiffGroupoid ∞ I) he he').1
      have B :
        ContDiffOn 𝕜 ∞ (fun p : E × F => p.1)
          ((I.symm ⁻¹' (e.symm.trans e').source ∩ range I) ×ˢ univ) :=
        cont_diff_fst.cont_diff_on
      exact ContDiffOn.comp A B (prod_subset_preimage_fst _ _)
    show
      ContDiffOn 𝕜 ∞
        (fun p : E × F =>
          Z.coord_change ⟨chart_at H (e.symm (I.symm p.1)), _⟩ ⟨e', he'⟩
            ((chart_at H (e.symm (I.symm p.1)) : M → H) (e.symm (I.symm p.1)))
            (Z.coord_change ⟨e, he⟩ ⟨chart_at H (e.symm (I.symm p.1)), _⟩ (e (e.symm (I.symm p.1)))
              p.2))
        ((I.symm ⁻¹' (e.symm.trans e').source ∩ range I) ×ˢ univ)
    · /- The coordinate change in the fiber is more complicated as its definition involves the
            reference chart chosen at each point. However, it appears with its inverse, so using the
            cocycle property one can get rid of it, and then conclude using the smoothness of the
            cocycle as given in the definition of basic smooth bundles. -/
      have := Z.coord_change_smooth ⟨e, he⟩ ⟨e', he'⟩
      rw [I.image_eq] at this
      apply ContDiffOn.congr this
      rintro ⟨x, v⟩ hx
      simp only [mfld_simps] at hx
      let f := chart_at H (e.symm (I.symm x))
      have A : I.symm x ∈ ((e.symm.trans f).trans (f.symm.trans e')).source := by
        simp only [hx.1.1, hx.1.2, mfld_simps]
      rw [e.right_inv hx.1.1]
      have := Z.coord_change_comp ⟨e, he⟩ ⟨f, chart_mem_atlas _ _⟩ ⟨e', he'⟩ (I.symm x) A v
      simpa only using this
  refine' @SmoothManifoldWithCorners.mk _ _ _ _ _ _ _ _ _ _ _ ⟨_⟩
  intro e₀ e₀' he₀ he₀'
  rcases(Z.mem_atlas_iff _).1 he₀ with ⟨e, he, rfl⟩
  rcases(Z.mem_atlas_iff _).1 he₀' with ⟨e', he', rfl⟩
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  exact ⟨A e e' he he', A e' e he' he⟩
#align basic_smooth_vector_bundle_core.to_smooth_manifold BasicSmoothVectorBundleCore.to_smooth_manifold

end BasicSmoothVectorBundleCore

section TangentBundle

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _)
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Basic smooth bundle core version of the tangent bundle of a smooth manifold `M` modelled over a
model with corners `I` on `(E, H)`. The fibers are equal to `E`, and the coordinate change in the
fiber corresponds to the derivative of the coordinate change in `M`. -/
@[simps]
def tangentBundleCore : BasicSmoothVectorBundleCore I M E
    where
  coordChange i j x := fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) (I x)
  coordChange_smooth_clm i j := by
    rw [I.image_eq]
    have A :
      ContDiffOn 𝕜 ∞ (I ∘ i.1.symm.trans j.1 ∘ I.symm)
        (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) :=
      (HasGroupoid.compatible (contDiffGroupoid ∞ I) i.2 j.2).1
    have B : UniqueDiffOn 𝕜 (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) :=
      I.unique_diff_preimage_source
    have C :
      ContDiffOn 𝕜 ∞
        (fun p : E × E =>
          (fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
                (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) p.1 :
              E → E)
            p.2)
        ((I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) ×ˢ univ) :=
      contDiffOn_fderivWithin_apply A B le_top
    have D :
      ∀ x ∈ I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I,
        fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) x =
          fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
            (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) x :=
      by
      intro x hx
      have N : I.symm ⁻¹' (i.1.symm.trans j.1).source ∈ nhds x :=
        I.continuous_symm.continuous_at.preimage_mem_nhds
          (IsOpen.mem_nhds (LocalHomeomorph.open_source _) hx.1)
      symm
      rw [inter_comm]
      exact fderivWithin_inter N (I.unique_diff _ hx.2)
    apply (A.fderiv_within B le_top).congr
    intro x hx
    simp only [mfld_simps] at hx
    simp only [hx, D, mfld_simps]
  coordChange_self i x hx v :=
    by
    /- Locally, a self-change of coordinate is just the identity, thus its derivative is the
        identity. One just needs to write this carefully, paying attention to the sets where the
        functions are defined. -/
    have A : I.symm ⁻¹' (i.1.symm.trans i.1).source ∩ range I ∈ 𝓝[range I] I x :=
      by
      rw [inter_comm]
      apply inter_mem_nhdsWithin
      apply
        I.continuous_symm.continuous_at.preimage_mem_nhds
          (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
      simp only [hx, i.1.map_target, mfld_simps]
    have B : ∀ᶠ y in 𝓝[range I] I x, (I ∘ i.1 ∘ i.1.symm ∘ I.symm) y = (id : E → E) y :=
      by
      filter_upwards [A]with _ hy
      rw [← I.image_eq] at hy
      rcases hy with ⟨z, hz⟩
      simp only [mfld_simps] at hz
      simp only [hz.2.symm, hz.1, mfld_simps]
    have C :
      fderivWithin 𝕜 (I ∘ i.1 ∘ i.1.symm ∘ I.symm) (range I) (I x) =
        fderivWithin 𝕜 (id : E → E) (range I) (I x) :=
      Filter.EventuallyEq.fderivWithin_eq I.unique_diff_at_image B (by simp only [hx, mfld_simps])
    rw [fderivWithin_id I.unique_diff_at_image] at C
    rw [C]
    rfl
  coordChange_comp i j u x hx :=
    by
    /- The cocycle property is just the fact that the derivative of a composition is the product of
        the derivatives. One needs however to check that all the functions one considers are smooth, and
        to pay attention to the domains where these functions are defined, making this proof a little
        bit cumbersome although there is nothing complicated here. -/
    have M : I x ∈ I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I :=
      ⟨by simpa only [mem_preimage, ModelWithCorners.left_inv] using hx, mem_range_self _⟩
    have U :
      UniqueDiffWithinAt 𝕜
        (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) (I x) :=
      I.unique_diff_preimage_source _ M
    have A :
      fderivWithin 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ I ∘ j.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) (I x) =
        (fderivWithin 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
              (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I)
              ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x))).comp
          (fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
            (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
            (I x)) :=
      by
      apply fderivWithin.comp _ _ _ _ U
      show
        DifferentiableWithinAt 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) (I x)
      · have A :
          ContDiffOn 𝕜 ∞ (I ∘ i.1.symm.trans j.1 ∘ I.symm)
            (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) :=
          (HasGroupoid.compatible (contDiffGroupoid ∞ I) i.2 j.2).1
        have B :
          DifferentiableOn 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
            (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) :=
          by
          apply (A.differentiable_on le_top).mono
          have :
            ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ⊆
              (i.1.symm.trans j.1).source :=
            inter_subset_left _ _
          exact inter_subset_inter (preimage_mono this) (subset.refl (range I))
        apply B
        simpa only [mfld_simps] using hx
      show
        DifferentiableWithinAt 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
          (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I) ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x))
      · have A :
          ContDiffOn 𝕜 ∞ (I ∘ j.1.symm.trans u.1 ∘ I.symm)
            (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I) :=
          (HasGroupoid.compatible (contDiffGroupoid ∞ I) j.2 u.2).1
        apply A.differentiable_on le_top
        rw [LocalHomeomorph.trans_source] at hx
        simp only [mfld_simps]
        exact hx.2
      show
        I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I ⊆
          I ∘ j.1 ∘ i.1.symm ∘ I.symm ⁻¹' (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I)
      · intro y hy
        simp only [mfld_simps] at hy
        rw [LocalHomeomorph.left_inv] at hy
        · simp only [hy, mfld_simps]
        · exact hy.1.1.2
    have B :
      fderivWithin 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ I ∘ j.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) (I x) =
        fderivWithin 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) (I x) :=
      haveI E :
        ∀ y ∈ I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I,
          ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ I ∘ j.1 ∘ i.1.symm ∘ I.symm) y =
            (I ∘ u.1 ∘ i.1.symm ∘ I.symm) y :=
        by
        intro y hy
        simp only [Function.comp_apply, ModelWithCorners.left_inv]
        rw [j.1.left_inv]
        exact hy.1.1.2
      fderivWithin_congr U E (E _ M)
    have C :
      fderivWithin 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) (I x) =
        fderivWithin 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm) (range I) (I x) :=
      by
      rw [inter_comm]
      apply fderivWithin_inter _ I.unique_diff_at_image
      apply
        I.continuous_symm.continuous_at.preimage_mem_nhds
          (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
      simpa only [ModelWithCorners.left_inv] using hx
    have D :
      fderivWithin 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
          (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I) ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)) =
        fderivWithin 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (range I)
          ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)) :=
      by
      rw [inter_comm]
      apply fderivWithin_inter _ I.unique_diff_at_image
      apply
        I.continuous_symm.continuous_at.preimage_mem_nhds
          (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
      rw [LocalHomeomorph.trans_source] at hx
      simp only [mfld_simps]
      exact hx.2
    have E :
      fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) (I x) =
        fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) (I x) :=
      by
      rw [inter_comm]
      apply fderivWithin_inter _ I.unique_diff_at_image
      apply
        I.continuous_symm.continuous_at.preimage_mem_nhds
          (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
      simpa only [ModelWithCorners.left_inv] using hx
    rw [B, C, D, E] at A
    simp only [A, ContinuousLinearMap.coe_comp', mfld_simps]
#align tangent_bundle_core tangentBundleCore

variable {M}

include I

/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangent_bundle_core I M).to_vector_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unused_arguments]
def TangentSpace (x : M) : Type _ :=
  E
#align tangent_space TangentSpace

omit I

variable (M)

-- is empty if the base manifold is empty
/-- The tangent bundle to a smooth manifold, as a Sigma type. Defined in terms of
`bundle.total_space` to be able to put a suitable topology on it. -/
@[nolint has_nonempty_instance, reducible]
def TangentBundle :=
  Bundle.TotalSpace (TangentSpace I : M → Type _)
#align tangent_bundle TangentBundle

-- mathport name: exprTM
local notation "TM" => TangentBundle I M

/-- The projection from the tangent bundle of a smooth manifold to the manifold. As the tangent
bundle is represented internally as a sigma type, the notation `p.1` also works for the projection
of the point `p`. -/
def TangentBundle.proj : TM → M := fun p => p.1
#align tangent_bundle.proj TangentBundle.proj

variable {M}

@[simp, mfld_simps]
theorem TangentBundle.proj_apply (x : M) (v : TangentSpace I x) :
    TangentBundle.proj I M ⟨x, v⟩ = x :=
  rfl
#align tangent_bundle.proj_apply TangentBundle.proj_apply

section TangentBundleInstances

/- In general, the definition of tangent_bundle and tangent_space are not reducible, so that type
class inference does not pick wrong instances. In this section, we record the right instances for
them, noting in particular that the tangent bundle is a smooth manifold. -/
section

attribute [local reducible] TangentSpace

variable {M} (x : M)

instance : TopologicalSpace (TangentSpace I x) := by infer_instance

instance : AddCommGroup (TangentSpace I x) := by infer_instance

instance : TopologicalAddGroup (TangentSpace I x) := by infer_instance

instance : Module 𝕜 (TangentSpace I x) := by infer_instance

instance : Inhabited (TangentSpace I x) :=
  ⟨0⟩

end

variable (M)

instance : TopologicalSpace TM :=
  (tangentBundleCore I M).toVectorBundleCore.toTopologicalSpace

instance : ChartedSpace (ModelProd H E) TM :=
  (tangentBundleCore I M).toChartedSpace

instance : SmoothManifoldWithCorners I.tangent TM :=
  (tangentBundleCore I M).to_smooth_manifold

instance : FiberBundle E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).toVectorBundleCore.FiberBundle

instance : VectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).toVectorBundleCore.VectorBundle

end TangentBundleInstances

variable (M)

/-- The tangent bundle projection on the basis is a continuous map. -/
theorem tangentBundle_proj_continuous : Continuous (TangentBundle.proj I M) :=
  (tangentBundleCore I M).toVectorBundleCore.continuous_proj
#align tangent_bundle_proj_continuous tangentBundle_proj_continuous

/-- The tangent bundle projection on the basis is an open map. -/
theorem tangentBundle_proj_open : IsOpenMap (TangentBundle.proj I M) :=
  (tangentBundleCore I M).toVectorBundleCore.isOpenMap_proj
#align tangent_bundle_proj_open tangentBundle_proj_open

/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `equiv.sigma_equiv_prod`. -/
@[simp, mfld_simps]
theorem tangentBundle_model_space_chartAt (p : TangentBundle I H) :
    (chartAt (ModelProd H E) p).toLocalEquiv = (Equiv.sigmaEquivProd H E).toLocalEquiv :=
  by
  have A : ∀ x_fst, fderivWithin 𝕜 (I ∘ I.symm) (range I) (I x_fst) = ContinuousLinearMap.id 𝕜 E :=
    by
    intro x_fst
    have :
      fderivWithin 𝕜 (I ∘ I.symm) (range I) (I x_fst) = fderivWithin 𝕜 id (range I) (I x_fst) :=
      by
      refine' fderivWithin_congr I.unique_diff_at_image (fun y hy => _) (by simp)
      exact ModelWithCorners.right_inv _ hy
    rwa [fderivWithin_id I.unique_diff_at_image] at this
  ext x : 1
  show
    (chart_at (ModelProd H E) p : TangentBundle I H → ModelProd H E) x =
      (Equiv.sigmaEquivProd H E) x
  · cases x
    simp only [chart_at, BasicSmoothVectorBundleCore.chart, tangentBundleCore,
      BasicSmoothVectorBundleCore.toVectorBundleCore, A, Prod.mk.inj_iff,
      ContinuousLinearMap.coe_id', mfld_simps]
  show ∀ x, (chart_at (ModelProd H E) p).toLocalEquiv.symm x = (Equiv.sigmaEquivProd H E).symm x
  · rintro ⟨x_fst, x_snd⟩
    simp only [BasicSmoothVectorBundleCore.toVectorBundleCore, tangentBundleCore, A,
      ContinuousLinearMap.coe_id', BasicSmoothVectorBundleCore.chart, chart_at,
      ContinuousLinearMap.coe_coe, Sigma.mk.inj_iff, mfld_simps]
  show (chart_at (ModelProd H E) p).toLocalEquiv.source = univ
  · simp only [chart_at, mfld_simps]
#align tangent_bundle_model_space_chart_at tangentBundle_model_space_chartAt

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt (p : TangentBundle I H) :
    ⇑(chartAt (ModelProd H E) p) = Equiv.sigmaEquivProd H E :=
  by
  unfold_coes
  simp only [mfld_simps]
#align tangent_bundle_model_space_coe_chart_at tangentBundle_model_space_coe_chartAt

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt_symm (p : TangentBundle I H) :
    ((chartAt (ModelProd H E) p).symm : ModelProd H E → TangentBundle I H) =
      (Equiv.sigmaEquivProd H E).symm :=
  by
  unfold_coes
  simp only [mfld_simps]
#align tangent_bundle_model_space_coe_chart_at_symm tangentBundle_model_space_coe_chartAt_symm

variable (H)

/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism -/
def tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E :=
  {
    Equiv.sigmaEquivProd H
      E with
    continuous_toFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chart_at (ModelProd H E) p) :=
        by
        rw [continuous_iff_continuousOn_univ]
        convert LocalHomeomorph.continuousOn _
        simp only [mfld_simps]
      simpa only [mfld_simps] using this
    continuous_invFun :=
      by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chart_at (ModelProd H E) p).symm :=
        by
        rw [continuous_iff_continuousOn_univ]
        convert LocalHomeomorph.continuousOn _
        simp only [mfld_simps]
      simpa only [mfld_simps] using this }
#align tangent_bundle_model_space_homeomorph tangentBundleModelSpaceHomeomorph

@[simp, mfld_simps]
theorem tangentBundleModelSpaceHomeomorph_coe :
    (tangentBundleModelSpaceHomeomorph H I : TangentBundle I H → ModelProd H E) =
      Equiv.sigmaEquivProd H E :=
  rfl
#align tangent_bundle_model_space_homeomorph_coe tangentBundleModelSpaceHomeomorph_coe

@[simp, mfld_simps]
theorem tangentBundleModelSpaceHomeomorph_coe_symm :
    ((tangentBundleModelSpaceHomeomorph H I).symm : ModelProd H E → TangentBundle I H) =
      (Equiv.sigmaEquivProd H E).symm :=
  rfl
#align tangent_bundle_model_space_homeomorph_coe_symm tangentBundleModelSpaceHomeomorph_coe_symm

end TangentBundle

