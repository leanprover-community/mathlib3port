/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth

! This file was ported from Lean 3 source module geometry.manifold.vector_bundle.tangent
! leanprover-community/mathlib commit 7dfe85833014fb54258a228081ebb76b7e96ec98
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Manifold.VectorBundle.Basic

/-! # Tangent bundles

This file defines the tangent bundle as a smooth vector bundle.

Let `M` be a smooth manifold with corners with model `I` on `(E, H)`. We define the tangent bundle
of `M` using the `vector_bundle_core` construction indexed by the charts of `M` with fibers `E`.
Given two charts `i, j : local_homeomorph M H`, the coordinate change between `i` and `j` at a point
`x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`.
This defines a smooth vector bundle `tangent_bundle` with fibers `tangent_space`.

## Main definitions

* `tangent_space I M x` is the fiber of the tangent bundle at `x : M`, which is defined to be `E`.

* `tangent_bundle I M` is the total space of `tangent_space I M`, proven to be a smooth vector
  bundle.
-/


open Bundle Set SmoothManifoldWithCorners LocalHomeomorph

open Manifold Topology Bundle

noncomputable section

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (I)

/-- Auxiliary lemma for tangent spaces: the derivative of a coordinate change between two charts is
  smooth on its source. -/
theorem contDiffOn_fderiv_coord_change (i j : atlas H M) :
    ContDiffOn 𝕜 ∞ (fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I))
      ((i.1.extend I).symm ≫ j.1.extend I).source :=
  by
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source ⊆ range I :=
    by
    rw [i.1.extend_coord_change_source]
    apply image_subset_range
  intro x hx
  refine' (ContDiffWithinAt.fderivWithin_right _ I.unique_diff le_top <| h hx).mono h
  refine'
    (LocalHomeomorph.contDiffOn_extend_coord_change I (subset_maximal_atlas I j.2)
          (subset_maximal_atlas I i.2) x hx).mono_of_mem
      _
  exact i.1.extend_coord_change_source_mem_nhdsWithin j.1 I hx
#align cont_diff_on_fderiv_coord_change contDiffOn_fderiv_coord_change

variable (M)

open SmoothManifoldWithCorners

/-- Let `M` be a smooth manifold with corners with model `I` on `(E, H)`.
Then `vector_bundle_core I M` is the vector bundle core for the tangent bundle over `M`.
It is indexed by the atlas of `M`, with fiber `E` and its change of coordinates from the chart `i`
to the chart `j` at point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`. -/
@[simps]
def tangentBundleCore : VectorBundleCore 𝕜 M E (atlas H M)
    where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I) (i.1.extend I x)
  coordChange_self i x hx v :=
    by
    rw [Filter.EventuallyEq.fderivWithin_eq, fderivWithin_id', ContinuousLinearMap.id_apply]
    · exact I.unique_diff_at_image
    · exact I.unique_diff_at_image
    · filter_upwards [i.1.extend_target_mem_nhdsWithin I hx]with y hy
      exact (i.1.extend I).right_inv hy
    · simp_rw [Function.comp_apply, i.1.extend_left_inv I hx]
  continuousOn_coordChange i j :=
    by
    refine'
      (contDiffOn_fderiv_coord_change I i j).ContinuousOn.comp ((i.1.continuousOn_extend I).mono _)
        _
    · rw [i.1.extend_source]
      exact inter_subset_left _ _
    simp_rw [← i.1.extend_image_source_inter, maps_to_image]
  coordChange_comp := by
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ v
    rw [fderivWithin_fderivWithin, Filter.EventuallyEq.fderivWithin_eq]
    · exact I.unique_diff_at_image
    · have := i.1.extend_preimage_mem_nhds I hxi (j.1.extend_source_mem_nhds I hxj)
      filter_upwards [nhdsWithin_le_nhds this]with y hy
      simp_rw [Function.comp_apply, (j.1.extend I).left_inv hy]
    · simp_rw [Function.comp_apply, i.1.extend_left_inv I hxi, j.1.extend_left_inv I hxj]
    ·
      exact
        (cont_diff_within_at_extend_coord_change' I (subset_maximal_atlas I k.2)
              (subset_maximal_atlas I j.2) hxk hxj).DifferentiableWithinAt
          le_top
    ·
      exact
        (cont_diff_within_at_extend_coord_change' I (subset_maximal_atlas I j.2)
              (subset_maximal_atlas I i.2) hxj hxi).DifferentiableWithinAt
          le_top
    · intro x hx
      exact mem_range_self _
    · exact I.unique_diff_at_image
    · rw [Function.comp_apply, i.1.extend_left_inv I hxi]
#align tangent_bundle_core tangentBundleCore

variable {M}

theorem tangentBundleCore_coordChange_achart (x x' z : M) :
    (tangentBundleCore I M).coordChange (achart H x) (achart H x') z =
      fderivWithin 𝕜 (extChartAt I x' ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) :=
  rfl
#align tangent_bundle_core_coord_change_achart tangentBundleCore_coordChange_achart

include I

/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangent_bundle_core I M).to_topological_vector_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unused_arguments]
def TangentSpace (x : M) : Type _ :=
  E deriving TopologicalSpace, AddCommGroup, TopologicalAddGroup
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

section TangentBundleInstances

/- In general, the definition of tangent_space is not reducible, so that type class inference
does not pick wrong instances. In this section, we record the right instances for
them, noting in particular that the tangent bundle is a smooth manifold. -/
section

variable {M} (x : M)

instance : Module 𝕜 (TangentSpace I x) := by delta_instance tangent_space

instance : Inhabited (TangentSpace I x) :=
  ⟨0⟩

end

instance : TopologicalSpace TM :=
  (tangentBundleCore I M).toTopologicalSpace

instance : FiberBundle E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).FiberBundle

instance : VectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  (tangentBundleCore I M).VectorBundle

namespace TangentBundle

protected theorem chartAt (p : TM) :
    chartAt (ModelProd H E) p =
      ((tangentBundleCore I M).toFiberBundleCore.localTriv (achart H p.1)).toLocalHomeomorph ≫ₕ
        (chartAt H p.1).Prod (LocalHomeomorph.refl E) :=
  rfl
#align tangent_bundle.chart_at TangentBundle.chartAt

theorem chartAt_toLocalEquiv (p : TM) :
    (chartAt (ModelProd H E) p).toLocalEquiv =
      (tangentBundleCore I M).toFiberBundleCore.localTrivAsLocalEquiv (achart H p.1) ≫
        (chartAt H p.1).toLocalEquiv.Prod (LocalEquiv.refl E) :=
  rfl
#align tangent_bundle.chart_at_to_local_equiv TangentBundle.chartAt_toLocalEquiv

theorem trivializationAt_eq_localTriv (x : M) :
    trivializationAt E (TangentSpace I) x =
      (tangentBundleCore I M).toFiberBundleCore.localTriv (achart H x) :=
  rfl
#align tangent_bundle.trivialization_at_eq_local_triv TangentBundle.trivializationAt_eq_localTriv

@[simp, mfld_simps]
theorem trivializationAt_source (x : M) :
    (trivializationAt E (TangentSpace I) x).source = π _ ⁻¹' (chartAt H x).source :=
  rfl
#align tangent_bundle.trivialization_at_source TangentBundle.trivializationAt_source

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, mfld_simps]
theorem trivializationAt_target (x : M) :
    (trivializationAt E (TangentSpace I) x).target = (chartAt H x).source ×ˢ univ :=
  rfl
#align tangent_bundle.trivialization_at_target TangentBundle.trivializationAt_target

@[simp, mfld_simps]
theorem trivializationAt_baseSet (x : M) :
    (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source :=
  rfl
#align tangent_bundle.trivialization_at_base_set TangentBundle.trivializationAt_baseSet

theorem trivializationAt_apply (x : M) (z : TM) :
    trivializationAt E (TangentSpace I) x z =
      (z.1,
        fderivWithin 𝕜 ((chartAt H x).extend I ∘ ((chartAt H z.1).extend I).symm) (range I)
          ((chartAt H z.1).extend I z.1) z.2) :=
  rfl
#align tangent_bundle.trivialization_at_apply TangentBundle.trivializationAt_apply

@[simp, mfld_simps]
theorem trivializationAt_fst (x : M) (z : TM) : (trivializationAt E (TangentSpace I) x z).1 = z.1 :=
  rfl
#align tangent_bundle.trivialization_at_fst TangentBundle.trivializationAt_fst

@[simp, mfld_simps]
theorem mem_chart_source_iff (p q : TM) :
    p ∈ (chartAt (ModelProd H E) q).source ↔ p.1 ∈ (chartAt H q.1).source := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
#align tangent_bundle.mem_chart_source_iff TangentBundle.mem_chart_source_iff

@[simp, mfld_simps]
theorem mem_chart_target_iff (p : H × E) (q : TM) :
    p ∈ (chartAt (ModelProd H E) q).target ↔ p.1 ∈ (chartAt H q.1).target := by
  simp (config := { contextual := true }) only [FiberBundle.chartedSpace_chartAt,
    and_iff_left_iff_imp, mfld_simps]
#align tangent_bundle.mem_chart_target_iff TangentBundle.mem_chart_target_iff

@[simp, mfld_simps]
theorem coe_chartAt_fst (p q : TM) : ((chartAt (ModelProd H E) q) p).1 = chartAt H q.1 p.1 :=
  rfl
#align tangent_bundle.coe_chart_at_fst TangentBundle.coe_chartAt_fst

@[simp, mfld_simps]
theorem coe_chartAt_symm_fst (p : H × E) (q : TM) :
    ((chartAt (ModelProd H E) q).symm p).1 = ((chartAt H q.1).symm : H → M) p.1 :=
  rfl
#align tangent_bundle.coe_chart_at_symm_fst TangentBundle.coe_chartAt_symm_fst

@[simp, mfld_simps]
theorem trivializationAt_continuousLinearMapAt {b₀ b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b) (achart H b₀) b :=
  (tangentBundleCore I M).localTriv_continuousLinearMapAt hb
#align tangent_bundle.trivialization_at_continuous_linear_map_at TangentBundle.trivializationAt_continuousLinearMapAt

@[simp, mfld_simps]
theorem trivializationAt_symmL {b₀ b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) b₀).baseSet) :
    (trivializationAt E (TangentSpace I) b₀).symmL 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b₀) (achart H b) b :=
  (tangentBundleCore I M).localTriv_symmL hb
#align tangent_bundle.trivialization_at_symmL TangentBundle.trivializationAt_symmL

@[simp, mfld_simps]
theorem coordChange_model_space (b b' x : F) :
    (tangentBundleCore 𝓘(𝕜, F) F).coordChange (achart F b) (achart F b') x = 1 := by
  simpa only [tangentBundleCore_coordChange, mfld_simps] using
    fderivWithin_id uniqueDiffWithinAt_univ
#align tangent_bundle.coord_change_model_space TangentBundle.coordChange_model_space

@[simp, mfld_simps]
theorem symmL_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).symmL 𝕜 b' = (1 : F →L[𝕜] F) :=
  by
  rw [TangentBundle.trivializationAt_symmL, coord_change_model_space]
  apply mem_univ
#align tangent_bundle.symmL_model_space TangentBundle.symmL_model_space

@[simp, mfld_simps]
theorem continuousLinearMapAt_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).continuousLinearMapAt 𝕜 b' = (1 : F →L[𝕜] F) :=
  by
  rw [TangentBundle.trivializationAt_continuousLinearMapAt, coord_change_model_space]
  apply mem_univ
#align tangent_bundle.continuous_linear_map_at_model_space TangentBundle.continuousLinearMapAt_model_space

end TangentBundle

instance tangentBundleCore.isSmooth : (tangentBundleCore I M).IsSmooth I :=
  by
  refine' ⟨fun i j => _⟩
  rw [SmoothOn, contMdiffOn_iff_source_of_mem_maximalAtlas (subset_maximal_atlas I i.2),
    contMdiffOn_iff_contDiffOn]
  refine' ((contDiffOn_fderiv_coord_change I i j).congr fun x hx => _).mono _
  · rw [LocalEquiv.trans_source'] at hx
    simp_rw [Function.comp_apply, tangentBundleCore_coordChange, (i.1.extend I).right_inv hx.1]
  · exact (i.1.extend_image_source_inter j.1 I).Subset
  · apply inter_subset_left
#align tangent_bundle_core.is_smooth tangentBundleCore.isSmooth

instance TangentBundle.smoothVectorBundle : SmoothVectorBundle E (TangentSpace I : M → Type _) I :=
  (tangentBundleCore I M).SmoothVectorBundle _
#align tangent_bundle.smooth_vector_bundle TangentBundle.smoothVectorBundle

end TangentBundleInstances

/-! ## The tangent bundle to the model space -/


/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `equiv.sigma_equiv_prod`. -/
@[simp, mfld_simps]
theorem tangentBundle_model_space_chartAt (p : TangentBundle I H) :
    (chartAt (ModelProd H E) p).toLocalEquiv = (Equiv.sigmaEquivProd H E).toLocalEquiv :=
  by
  ext x : 1
  · ext
    · rfl
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  · intro x
    ext
    · rfl
    apply hEq_of_eq
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  simp_rw [TangentBundle.chartAt, FiberBundleCore.localTriv, FiberBundleCore.localTrivAsLocalEquiv,
    VectorBundleCore.toFiberBundleCore_baseSet, tangentBundleCore_baseSet]
  simp only [mfld_simps]
#align tangent_bundle_model_space_chart_at tangentBundle_model_space_chartAt

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt (p : TangentBundle I H) :
    ⇑(chartAt (ModelProd H E) p) = Equiv.sigmaEquivProd H E :=
  by
  unfold_coes
  simp_rw [tangentBundle_model_space_chartAt]
  rfl
#align tangent_bundle_model_space_coe_chart_at tangentBundle_model_space_coe_chartAt

@[simp, mfld_simps]
theorem tangentBundle_model_space_coe_chartAt_symm (p : TangentBundle I H) :
    ((chartAt (ModelProd H E) p).symm : ModelProd H E → TangentBundle I H) =
      (Equiv.sigmaEquivProd H E).symm :=
  by
  unfold_coes
  simp_rw [LocalHomeomorph.symm_toLocalEquiv, tangentBundle_model_space_chartAt]
  rfl
#align tangent_bundle_model_space_coe_chart_at_symm tangentBundle_model_space_coe_chartAt_symm

theorem tangentBundleCore_coordChange_model_space (x x' z : H) :
    (tangentBundleCore I H).coordChange (achart H x) (achart H x') z = ContinuousLinearMap.id 𝕜 E :=
  by
  ext v
  exact (tangentBundleCore I H).coordChange_self (achart _ z) z (mem_univ _) v
#align tangent_bundle_core_coord_change_model_space tangentBundleCore_coordChange_model_space

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
        simp only [TangentSpace.fiberBundle, mfld_simps]
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

