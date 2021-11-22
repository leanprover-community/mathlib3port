import Mathbin.Topology.FiberBundle 
import Mathbin.Geometry.Manifold.SmoothManifoldWithCorners

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
specifying the changes in the fiber when one goes from one coordinate chart to another one. We do
not require that this changes in fiber are linear, but only diffeomorphisms.

## Main definitions

* `basic_smooth_bundle_core I M F`: assuming that `M` is a smooth manifold over the model with
  corners `I` on `(𝕜, E, H)`, and `F` is a normed vector space over `𝕜`, this structure registers,
  for each pair of charts of `M`, a smooth change of coordinates on `F`. This is the core structure
  from which one will build a smooth bundle with fiber `F` over `M`.

Let `Z` be a basic smooth bundle core over `M` with fiber `F`. We define
`Z.to_topological_fiber_bundle_core`, the (topological) fiber bundle core associated to `Z`. From
it, we get a space `Z.to_topological_fiber_bundle_core.total_space` (which as a Type is just `Σ (x :
M), F`), with the fiber bundle topology. It inherits a manifold structure (where the charts are in
bijection with the charts of the basis). We show that this manifold is smooth.

Then we use this machinery to construct the tangent bundle of a smooth manifold.

* `tangent_bundle_core I M`: the basic smooth bundle core associated to a smooth manifold `M` over a
  model with corners `I`.
* `tangent_bundle I M`     : the total space of `tangent_bundle_core I M`. It is itself a
  smooth manifold over the model with corners `I.tangent`, the product of `I` and the trivial model
  with corners on `E`.
* `tangent_space I x`      : the tangent space to `M` at `x`
* `tangent_bundle.proj I M`: the projection from the tangent bundle to the base manifold

## Implementation notes

In the definition of a basic smooth bundle core, we do not require that the coordinate changes of
the fibers are linear map, only that they are diffeomorphisms. Therefore, the fibers of the
resulting fiber bundle do not inherit a vector space structure (as an algebraic object) in general.
As the fiber, as a type, is just `F`, one can still always register the vector space structure, but
it does not make sense to do so (i.e., it will not lead to any useful theorem) unless this structure
is canonical, i.e., the coordinate changes are linear maps.

For instance, we register the vector space structure on the fibers of the tangent bundle. However,
we do not register the normed space structure coming from that of `F` (as it is not canonical, and
we also want to keep the possibility to add a Riemannian structure on the manifold later on without
having two competing normed space instances on the tangent spaces).

We require `F` to be a normed space, and not just a topological vector space, as we want to talk
about smooth functions on `F`. The notion of derivative requires a norm to be defined.

## TODO
construct the cotangent bundle, and the bundles of differential forms. They should follow
functorially from the description of the tangent bundle as a basic smooth bundle.

## Tags
Smooth fiber bundle, vector bundle, tangent space, tangent bundle
-/


noncomputable theory

universe u

open TopologicalSpace Set

open_locale Manifold TopologicalSpace

/-- Core structure used to create a smooth bundle above `M` (a manifold over the model with
corner `I`) with fiber the normed vector space `F` over `𝕜`, which is trivial in the chart domains
of `M`. This structure registers the changes in the fibers when one changes coordinate charts in the
base. We do not require the change of coordinates of the fibers to be linear, only smooth.
Therefore, the fibers of the resulting bundle will not inherit a canonical vector space structure
in general. -/
structure
  BasicSmoothBundleCore{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E :
    Type
      _}[NormedGroup
      E][NormedSpace 𝕜
      E]{H :
    Type
      _}[TopologicalSpace
      H](I :
    ModelWithCorners 𝕜 E
      H)(M :
    Type
      _)[TopologicalSpace
      M][ChartedSpace H M][SmoothManifoldWithCorners I M](F : Type _)[NormedGroup F][NormedSpace 𝕜 F] where
  
  coordChange : atlas H M → atlas H M → H → F → F 
  coord_change_self : ∀ i : atlas H M, ∀ x _ : x ∈ i.1.Target, ∀ v, coord_change i i x v = v 
  coord_change_comp :
  ∀ i j k : atlas H M,
    ∀ x _ : x ∈ ((i.1.symm.trans j.1).trans (j.1.symm.trans k.1)).Source,
      ∀ v, (coord_change j k ((i.1.symm.trans j.1) x)) (coord_change i j x v) = coord_change i k x v 
  coord_change_smooth :
  ∀ i j : atlas H M,
    TimesContDiffOn 𝕜 ∞ (fun p : E × F => coord_change i j (I.symm p.1) p.2)
      ((I '' (i.1.symm.trans j.1).Source).Prod (univ : Set F))

/-- The trivial basic smooth bundle core, in which all the changes of coordinates are the
identity. -/
def trivialBasicSmoothBundleCore {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E]
  {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] (F : Type _) [NormedGroup F] [NormedSpace 𝕜 F] : BasicSmoothBundleCore I M F :=
  { coordChange := fun i j x v => v, coord_change_self := fun i x hx v => rfl,
    coord_change_comp := fun i j k x hx v => rfl,
    coord_change_smooth := fun i j => times_cont_diff_snd.TimesContDiffOn }

namespace BasicSmoothBundleCore

variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E :
    Type
      _}[NormedGroup
      E][NormedSpace 𝕜
      E]{H :
    Type
      _}[TopologicalSpace
      H]{I :
    ModelWithCorners 𝕜 E
      H}{M :
    Type
      _}[TopologicalSpace
      M][ChartedSpace H
      M][SmoothManifoldWithCorners I M]{F : Type _}[NormedGroup F][NormedSpace 𝕜 F](Z : BasicSmoothBundleCore I M F)

instance  : Inhabited (BasicSmoothBundleCore I M F) :=
  ⟨trivialBasicSmoothBundleCore I M F⟩

/-- Fiber bundle core associated to a basic smooth bundle core -/
def to_topological_fiber_bundle_core : TopologicalFiberBundleCore (atlas H M) M F :=
  { BaseSet := fun i => i.1.Source, is_open_base_set := fun i => i.1.open_source,
    indexAt := fun x => ⟨chart_at H x, chart_mem_atlas H x⟩, mem_base_set_at := fun x => mem_chart_source H x,
    coordChange := fun i j x v => Z.coord_change i j (i.1 x) v,
    coord_change_self := fun i x hx v => Z.coord_change_self i (i.1 x) (i.1.map_source hx) v,
    coord_change_comp :=
      fun i j k x ⟨⟨hx1, hx2⟩, hx3⟩ v =>
        by 
          have  := Z.coord_change_comp i j k (i.1 x) _ v 
          convert this using 2
          ·
            simp' only [hx1] with mfld_simps
          ·
            simp' only [hx1, hx2, hx3] with mfld_simps,
    coord_change_continuous :=
      fun i j =>
        by 
          have A :
            ContinuousOn (fun p : E × F => Z.coord_change i j (I.symm p.1) p.2)
              ((I '' (i.1.symm.trans j.1).Source).Prod (univ : Set F)) :=
            (Z.coord_change_smooth i j).ContinuousOn 
          have B : ContinuousOn (fun x : M => I (i.1 x)) i.1.Source := I.continuous.comp_continuous_on i.1.ContinuousOn 
          have C : ContinuousOn (fun p : M × F => (⟨I (i.1 p.1), p.2⟩ : E × F)) (i.1.Source.Prod univ)
          ·
            apply ContinuousOn.prod _ continuous_snd.continuous_on 
            exact B.comp continuous_fst.continuous_on (prod_subset_preimage_fst _ _)
          have C' :
            ContinuousOn (fun p : M × F => (⟨I (i.1 p.1), p.2⟩ : E × F)) ((i.1.Source ∩ j.1.Source).Prod univ) :=
            ContinuousOn.mono C (prod_mono (inter_subset_left _ _) (subset.refl _))
          have D :
            (i.1.Source ∩ j.1.Source).Prod univ ⊆
              (fun p : M × F => (I (i.1 p.1), p.2)) ⁻¹' (I '' (i.1.symm.trans j.1).Source).Prod univ
          ·
            rintro ⟨x, v⟩ hx 
            simp' only with mfld_simps  at hx 
            simp' only [hx] with mfld_simps 
          convert ContinuousOn.comp A C' D 
          ext p 
          simp' only with mfld_simps }

@[simp, mfld_simps]
theorem base_set (i : atlas H M) : (Z.to_topological_fiber_bundle_core.local_triv i).BaseSet = i.1.Source :=
  rfl

/-- Local chart for the total space of a basic smooth bundle -/
def chart {e : LocalHomeomorph M H} (he : e ∈ atlas H M) :
  LocalHomeomorph Z.to_topological_fiber_bundle_core.total_space (ModelProd H F) :=
  (Z.to_topological_fiber_bundle_core.local_triv ⟨e, he⟩).toLocalHomeomorph.trans
    (LocalHomeomorph.prod e (LocalHomeomorph.refl F))

@[simp, mfld_simps]
theorem chart_source (e : LocalHomeomorph M H) (he : e ∈ atlas H M) :
  (Z.chart he).Source = Z.to_topological_fiber_bundle_core.proj ⁻¹' e.source :=
  by 
    simp only [chart, mem_prod]
    mfldSetTac

@[simp, mfld_simps]
theorem chart_target (e : LocalHomeomorph M H) (he : e ∈ atlas H M) : (Z.chart he).Target = e.target.prod univ :=
  by 
    simp only [chart]
    mfldSetTac

/-- The total space of a basic smooth bundle is endowed with a charted space structure, where the
charts are in bijection with the charts of the basis. -/
instance to_charted_space : ChartedSpace (ModelProd H F) Z.to_topological_fiber_bundle_core.total_space :=
  { Atlas := ⋃(e : LocalHomeomorph M H)(he : e ∈ atlas H M), {Z.chart he},
    chartAt := fun p => Z.chart (chart_mem_atlas H p.1),
    mem_chart_source :=
      fun p =>
        by 
          simp [mem_chart_source],
    chart_mem_atlas :=
      fun p =>
        by 
          simp only [mem_Union, mem_singleton_iff, chart_mem_atlas]
          exact ⟨chart_at H p.1, chart_mem_atlas H p.1, rfl⟩ }

theorem mem_atlas_iff (f : LocalHomeomorph Z.to_topological_fiber_bundle_core.total_space (ModelProd H F)) :
  f ∈ atlas (ModelProd H F) Z.to_topological_fiber_bundle_core.total_space ↔
    ∃ (e : LocalHomeomorph M H)(he : e ∈ atlas H M), f = Z.chart he :=
  by 
    simp only [atlas, mem_Union, mem_singleton_iff]

@[simp, mfld_simps]
theorem mem_chart_source_iff (p q : Z.to_topological_fiber_bundle_core.total_space) :
  p ∈ (chart_at (ModelProd H F) q).Source ↔ p.1 ∈ (chart_at H q.1).Source :=
  by 
    simp' only [chart_at] with mfld_simps

@[simp, mfld_simps]
theorem mem_chart_target_iff (p : H × F) (q : Z.to_topological_fiber_bundle_core.total_space) :
  p ∈ (chart_at (ModelProd H F) q).Target ↔ p.1 ∈ (chart_at H q.1).Target :=
  by 
    simp' only [chart_at] with mfld_simps

@[simp, mfld_simps]
theorem coe_chart_at_fst (p q : Z.to_topological_fiber_bundle_core.total_space) :
  ((chart_at (ModelProd H F) q) p).1 = chart_at H q.1 p.1 :=
  rfl

@[simp, mfld_simps]
theorem coe_chart_at_symm_fst (p : H × F) (q : Z.to_topological_fiber_bundle_core.total_space) :
  ((chart_at (ModelProd H F) q).symm p).1 = ((chart_at H q.1).symm : H → M) p.1 :=
  rfl

/-- Smooth manifold structure on the total space of a basic smooth bundle -/
instance to_smooth_manifold :
  SmoothManifoldWithCorners (I.prod 𝓘(𝕜, F)) Z.to_topological_fiber_bundle_core.total_space :=
  by 
    let J := ModelWithCorners.toLocalEquiv (I.prod 𝓘(𝕜, F))
    have A :
      ∀ e e' : LocalHomeomorph M H he : e ∈ atlas H M he' : e' ∈ atlas H M,
        TimesContDiffOn 𝕜 ∞ (J ∘ (Z.chart he).symm.trans (Z.chart he') ∘ J.symm)
          (J.symm ⁻¹' ((Z.chart he).symm.trans (Z.chart he')).Source ∩ range J)
    ·
      intro e e' he he' 
      have  :
        J.symm ⁻¹' ((chart Z he).symm.trans (chart Z he')).Source ∩ range J =
          (I.symm ⁻¹' (e.symm.trans e').Source ∩ range I).Prod univ
      ·
        ·
          simp only [J, chart, ModelWithCorners.prod]
          mfldSetTac 
      rw [this]
      apply TimesContDiffOn.prod 
      show
        TimesContDiffOn 𝕜 ∞ (fun p : E × F => (I ∘ e' ∘ e.symm ∘ I.symm) p.1)
          ((I.symm ⁻¹' (e.symm.trans e').Source ∩ range I).Prod (univ : Set F))
      ·
        have A : TimesContDiffOn 𝕜 ∞ (I ∘ e.symm.trans e' ∘ I.symm) (I.symm ⁻¹' (e.symm.trans e').Source ∩ range I) :=
          (HasGroupoid.compatible (timesContDiffGroupoid ∞ I) he he').1
        have B :
          TimesContDiffOn 𝕜 ∞ (fun p : E × F => p.1) ((I.symm ⁻¹' (e.symm.trans e').Source ∩ range I).Prod univ) :=
          times_cont_diff_fst.times_cont_diff_on 
        exact TimesContDiffOn.comp A B (prod_subset_preimage_fst _ _)
      show
        TimesContDiffOn 𝕜 ∞
          (fun p : E × F =>
            Z.coord_change ⟨chart_at H (e.symm (I.symm p.1)), _⟩ ⟨e', he'⟩
              ((chart_at H (e.symm (I.symm p.1)) : M → H) (e.symm (I.symm p.1)))
              (Z.coord_change ⟨e, he⟩ ⟨chart_at H (e.symm (I.symm p.1)), _⟩ (e (e.symm (I.symm p.1))) p.2))
          ((I.symm ⁻¹' (e.symm.trans e').Source ∩ range I).Prod (univ : Set F))
      ·
        have  := Z.coord_change_smooth ⟨e, he⟩ ⟨e', he'⟩
        rw [I.image_eq] at this 
        apply TimesContDiffOn.congr this 
        rintro ⟨x, v⟩ hx 
        simp' only with mfld_simps  at hx 
        let f := chart_at H (e.symm (I.symm x))
        have A : I.symm x ∈ ((e.symm.trans f).trans (f.symm.trans e')).Source
        ·
          simp' only [hx.1.1, hx.1.2] with mfld_simps 
        rw [e.right_inv hx.1.1]
        have  := Z.coord_change_comp ⟨e, he⟩ ⟨f, chart_mem_atlas _ _⟩ ⟨e', he'⟩ (I.symm x) A v 
        simpa only using this 
    refine' @SmoothManifoldWithCorners.mk _ _ _ _ _ _ _ _ _ _ _ ⟨_⟩
    intro e₀ e₀' he₀ he₀' 
    rcases(Z.mem_atlas_iff _).1 he₀ with ⟨e, he, rfl⟩
    rcases(Z.mem_atlas_iff _).1 he₀' with ⟨e', he', rfl⟩
    rw [timesContDiffGroupoid, mem_groupoid_of_pregroupoid]
    exact ⟨A e e' he he', A e' e he' he⟩

end BasicSmoothBundleCore

section TangentBundle

variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E :
    Type
      _}[NormedGroup
      E][NormedSpace 𝕜
      E]{H :
    Type
      _}[TopologicalSpace
      H](I : ModelWithCorners 𝕜 E H)(M : Type _)[TopologicalSpace M][ChartedSpace H M][SmoothManifoldWithCorners I M]

/-- Basic smooth bundle core version of the tangent bundle of a smooth manifold `M` modelled over a
model with corners `I` on `(E, H)`. The fibers are equal to `E`, and the coordinate change in the
fiber corresponds to the derivative of the coordinate change in `M`. -/
def tangentBundleCore : BasicSmoothBundleCore I M E :=
  { coordChange := fun i j x v => (fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) (I x) : E → E) v,
    coord_change_smooth :=
      fun i j =>
        by 
          rw [I.image_eq]
          have A :
            TimesContDiffOn 𝕜 ∞ (I ∘ i.1.symm.trans j.1 ∘ I.symm) (I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) :=
            (HasGroupoid.compatible (timesContDiffGroupoid ∞ I) i.2 j.2).1
          have B : UniqueDiffOn 𝕜 (I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) := I.unique_diff_preimage_source 
          have C :
            TimesContDiffOn 𝕜 ∞
              (fun p : E × E =>
                (fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) p.1 :
                  E → E)
                  p.2)
              ((I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I).Prod univ) :=
            times_cont_diff_on_fderiv_within_apply A B le_top 
          have D :
            ∀ x _ : x ∈ I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I,
              fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) x =
                fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) x
          ·
            intro x hx 
            have N : I.symm ⁻¹' (i.1.symm.trans j.1).Source ∈ nhds x :=
              I.continuous_symm.continuous_at.preimage_mem_nhds (IsOpen.mem_nhds (LocalHomeomorph.open_source _) hx.1)
            symm 
            rw [inter_comm]
            exact fderiv_within_inter N (I.unique_diff _ hx.2)
          apply TimesContDiffOn.congr C 
          rintro ⟨x, v⟩ hx 
          have E : x ∈ I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I
          ·
            simpa only [prod_mk_mem_set_prod_eq, and_trueₓ, mem_univ] using hx 
          have  : I (I.symm x) = x
          ·
            simp [E.2]
          dsimp [-Subtype.val_eq_coe]
          rw [this, D x E]
          rfl,
    coord_change_self :=
      fun i x hx v =>
        by 
          have A : I.symm ⁻¹' (i.1.symm.trans i.1).Source ∩ range I ∈ 𝓝[range I] I x
          ·
            rw [inter_comm]
            apply inter_mem_nhds_within 
            apply I.continuous_symm.continuous_at.preimage_mem_nhds (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
            simp' only [hx, i.1.map_target] with mfld_simps 
          have B : ∀ᶠy in 𝓝[range I] I x, (I ∘ i.1 ∘ i.1.symm ∘ I.symm) y = (id : E → E) y
          ·
            filterUpwards [A]
            intro y hy 
            rw [←I.image_eq] at hy 
            rcases hy with ⟨z, hz⟩
            simp' only with mfld_simps  at hz 
            simp' only [hz.2.symm, hz.1] with mfld_simps 
          have C :
            fderivWithin 𝕜 (I ∘ i.1 ∘ i.1.symm ∘ I.symm) (range I) (I x) =
              fderivWithin 𝕜 (id : E → E) (range I) (I x) :=
            Filter.EventuallyEq.fderiv_within_eq I.unique_diff_at_image B
              (by 
                simp' only [hx] with mfld_simps)
          rw [fderiv_within_id I.unique_diff_at_image] at C 
          rw [C]
          rfl,
    coord_change_comp :=
      fun i j u x hx =>
        by 
          have M : I x ∈ I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I :=
            ⟨by 
                simpa only [mem_preimage, ModelWithCorners.left_inv] using hx,
              mem_range_self _⟩
          have U :
            UniqueDiffWithinAt 𝕜 (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I)
              (I x) :=
            I.unique_diff_preimage_source _ M 
          have A :
            fderivWithin 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ I ∘ j.1 ∘ i.1.symm ∘ I.symm)
                (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x) =
              (fderivWithin 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (I.symm ⁻¹' (j.1.symm.trans u.1).Source ∩ range I)
                    ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x))).comp
                (fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
                  (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x))
          ·
            apply fderivWithin.comp _ _ _ _ U 
            show
              DifferentiableWithinAt 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
                (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x)
            ·
              have A :
                TimesContDiffOn 𝕜 ∞ (I ∘ i.1.symm.trans j.1 ∘ I.symm)
                  (I.symm ⁻¹' (i.1.symm.trans j.1).Source ∩ range I) :=
                (HasGroupoid.compatible (timesContDiffGroupoid ∞ I) i.2 j.2).1
              have B :
                DifferentiableOn 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
                  (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I)
              ·
                apply (A.differentiable_on le_top).mono 
                have  : ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ⊆ (i.1.symm.trans j.1).Source :=
                  inter_subset_left _ _ 
                exact inter_subset_inter (preimage_mono this) (subset.refl (range I))
              apply B 
              simpa only with mfld_simps using hx 
            show
              DifferentiableWithinAt 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (I.symm ⁻¹' (j.1.symm.trans u.1).Source ∩ range I)
                ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x))
            ·
              have A :
                TimesContDiffOn 𝕜 ∞ (I ∘ j.1.symm.trans u.1 ∘ I.symm)
                  (I.symm ⁻¹' (j.1.symm.trans u.1).Source ∩ range I) :=
                (HasGroupoid.compatible (timesContDiffGroupoid ∞ I) j.2 u.2).1
              apply A.differentiable_on le_top 
              rw [LocalHomeomorph.trans_source] at hx 
              simp' only with mfld_simps 
              exact hx.2
            show
              I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I ⊆
                (I ∘ j.1 ∘ i.1.symm ∘ I.symm) ⁻¹' (I.symm ⁻¹' (j.1.symm.trans u.1).Source ∩ range I)
            ·
              intro y hy 
              simp' only with mfld_simps  at hy 
              rw [LocalHomeomorph.left_inv] at hy
              ·
                simp' only [hy] with mfld_simps
              ·
                exact hy.1.1.2
          have B :
            fderivWithin 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ I ∘ j.1 ∘ i.1.symm ∘ I.symm)
                (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x) =
              fderivWithin 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
                (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x)
          ·
            have E :
              ∀ y _ : y ∈ I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I,
                ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ I ∘ j.1 ∘ i.1.symm ∘ I.symm) y = (I ∘ u.1 ∘ i.1.symm ∘ I.symm) y
            ·
              intro y hy 
              simp only [Function.comp_app, ModelWithCorners.left_inv]
              rw [j.1.left_inv]
              exact hy.1.1.2 
            exact fderiv_within_congr U E (E _ M)
          have C :
            fderivWithin 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
                (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x) =
              fderivWithin 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm) (range I) (I x)
          ·
            rw [inter_comm]
            apply fderiv_within_inter _ I.unique_diff_at_image 
            apply I.continuous_symm.continuous_at.preimage_mem_nhds (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
            simpa only [ModelWithCorners.left_inv] using hx 
          have D :
            fderivWithin 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (I.symm ⁻¹' (j.1.symm.trans u.1).Source ∩ range I)
                ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)) =
              fderivWithin 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (range I) ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x))
          ·
            rw [inter_comm]
            apply fderiv_within_inter _ I.unique_diff_at_image 
            apply I.continuous_symm.continuous_at.preimage_mem_nhds (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
            rw [LocalHomeomorph.trans_source] at hx 
            simp' only with mfld_simps 
            exact hx.2
          have E :
            fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
                (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).Source ∩ range I) (I x) =
              fderivWithin 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) (I x)
          ·
            rw [inter_comm]
            apply fderiv_within_inter _ I.unique_diff_at_image 
            apply I.continuous_symm.continuous_at.preimage_mem_nhds (IsOpen.mem_nhds (LocalHomeomorph.open_source _) _)
            simpa only [ModelWithCorners.left_inv] using hx 
          rw [B, C, D, E] at A 
          simp' only [A, ContinuousLinearMap.coe_comp'] with mfld_simps }

variable{M}

include I

/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangent_bundle_core I M).to_topological_fiber_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unused_arguments]
def TangentSpace (x : M) : Type _ :=
  E

omit I

variable(M)

/-- The tangent bundle to a smooth manifold, as a plain type. We could use
`(tangent_bundle_core I M).to_topological_fiber_bundle_core.total_space`, but instead we use the
(definitionally equal) `Σ (x : M), tangent_space I x`, to make sure that rcasing an element of the
tangent bundle gives a second component in the tangent space. -/
@[nolint has_inhabited_instance, reducible]
def TangentBundle :=
  Σx : M, TangentSpace I x

/-- The projection from the tangent bundle of a smooth manifold to the manifold. As the tangent
bundle is represented internally as a sigma type, the notation `p.1` also works for the projection
of the point `p`. -/
def TangentBundle.proj : TangentBundle I M → M :=
  fun p => p.1

variable{M}

@[simp, mfld_simps]
theorem TangentBundle.proj_apply (x : M) (v : TangentSpace I x) : TangentBundle.proj I M ⟨x, v⟩ = x :=
  rfl

section TangentBundleInstances

variable(M)

instance  : TopologicalSpace (TangentBundle I M) :=
  (tangentBundleCore I M).toTopologicalFiberBundleCore.toTopologicalSpace (atlas H M)

instance  : ChartedSpace (ModelProd H E) (TangentBundle I M) :=
  (tangentBundleCore I M).toChartedSpace

instance  : SmoothManifoldWithCorners I.tangent (TangentBundle I M) :=
  (tangentBundleCore I M).to_smooth_manifold

attribute [local reducible] TangentSpace

variable{M}(x : M)

instance  : HasContinuousSmul 𝕜 (TangentSpace I x) :=
  by 
    infer_instance

instance  : TopologicalSpace (TangentSpace I x) :=
  by 
    infer_instance

instance  : AddCommGroupₓ (TangentSpace I x) :=
  by 
    infer_instance

instance  : TopologicalAddGroup (TangentSpace I x) :=
  by 
    infer_instance

instance  : Module 𝕜 (TangentSpace I x) :=
  by 
    infer_instance

instance  : Inhabited (TangentSpace I x) :=
  ⟨0⟩

end TangentBundleInstances

variable(M)

/-- The tangent bundle projection on the basis is a continuous map. -/
theorem tangent_bundle_proj_continuous : Continuous (TangentBundle.proj I M) :=
  TopologicalFiberBundleCore.continuous_proj _

/-- The tangent bundle projection on the basis is an open map. -/
theorem tangent_bundle_proj_open : IsOpenMap (TangentBundle.proj I M) :=
  TopologicalFiberBundleCore.is_open_map_proj _

/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `equiv.sigma_equiv_prod`. -/
@[simp, mfld_simps]
theorem tangent_bundle_model_space_chart_at (p : TangentBundle I H) :
  (chart_at (ModelProd H E) p).toLocalEquiv = (Equiv.sigmaEquivProd H E).toLocalEquiv :=
  by 
    have A : ∀ x_fst, fderivWithin 𝕜 (I ∘ I.symm) (range I) (I x_fst) = ContinuousLinearMap.id 𝕜 E
    ·
      intro x_fst 
      have  : fderivWithin 𝕜 (I ∘ I.symm) (range I) (I x_fst) = fderivWithin 𝕜 id (range I) (I x_fst)
      ·
        refine'
          fderiv_within_congr I.unique_diff_at_image (fun y hy => _)
            (by 
              simp )
        exact ModelWithCorners.right_inv _ hy 
      rwa [fderiv_within_id I.unique_diff_at_image] at this 
    ext x : 1
    show (chart_at (ModelProd H E) p : TangentBundle I H → ModelProd H E) x = (Equiv.sigmaEquivProd H E) x
    ·
      cases x 
      simp' only [chart_at, BasicSmoothBundleCore.chart, tangentBundleCore,
        BasicSmoothBundleCore.toTopologicalFiberBundleCore, A, Prod.mk.inj_iffₓ, ContinuousLinearMap.coe_id'] with
        mfld_simps 
    show ∀ x, (chart_at (ModelProd H E) p).toLocalEquiv.symm x = (Equiv.sigmaEquivProd H E).symm x
    ·
      rintro ⟨x_fst, x_snd⟩
      simp' only [chart_at, BasicSmoothBundleCore.chart, tangentBundleCore, ContinuousLinearMap.coe_id',
        BasicSmoothBundleCore.toTopologicalFiberBundleCore, A] with mfld_simps 
    show (chart_at (ModelProd H E) p).toLocalEquiv.Source = univ
    ·
      simp' only [chart_at] with mfld_simps

@[simp, mfld_simps]
theorem tangent_bundle_model_space_coe_chart_at (p : TangentBundle I H) :
  «expr⇑ » (chart_at (ModelProd H E) p) = Equiv.sigmaEquivProd H E :=
  by 
    unfoldCoes 
    simp' only with mfld_simps

@[simp, mfld_simps]
theorem tangent_bundle_model_space_coe_chart_at_symm (p : TangentBundle I H) :
  ((chart_at (ModelProd H E) p).symm : ModelProd H E → TangentBundle I H) = (Equiv.sigmaEquivProd H E).symm :=
  by 
    unfoldCoes 
    simp' only with mfld_simps

variable(H)

/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism -/
def tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E :=
  { Equiv.sigmaEquivProd H E with
    continuous_to_fun :=
      by 
        let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
        have  : Continuous (chart_at (ModelProd H E) p)
        ·
          rw [continuous_iff_continuous_on_univ]
          convert LocalHomeomorph.continuous_on _ 
          simp' only with mfld_simps 
        simpa only with mfld_simps using this,
    continuous_inv_fun :=
      by 
        let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
        have  : Continuous (chart_at (ModelProd H E) p).symm
        ·
          rw [continuous_iff_continuous_on_univ]
          convert LocalHomeomorph.continuous_on _ 
          simp' only with mfld_simps 
        simpa only with mfld_simps using this }

@[simp, mfld_simps]
theorem tangent_bundle_model_space_homeomorph_coe :
  (tangentBundleModelSpaceHomeomorph H I : TangentBundle I H → ModelProd H E) = Equiv.sigmaEquivProd H E :=
  rfl

@[simp, mfld_simps]
theorem tangent_bundle_model_space_homeomorph_coe_symm :
  ((tangentBundleModelSpaceHomeomorph H I).symm : ModelProd H E → TangentBundle I H) =
    (Equiv.sigmaEquivProd H E).symm :=
  rfl

end TangentBundle

