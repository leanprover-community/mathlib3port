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

-- error in Geometry.Manifold.BasicSmoothBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Core structure used to create a smooth bundle above `M` (a manifold over the model with
corner `I`) with fiber the normed vector space `F` over `𝕜`, which is trivial in the chart domains
of `M`. This structure registers the changes in the fibers when one changes coordinate charts in the
base. We do not require the change of coordinates of the fibers to be linear, only smooth.
Therefore, the fibers of the resulting bundle will not inherit a canonical vector space structure
in general. -/
structure basic_smooth_bundle_core
{𝕜 : Type*}
[nondiscrete_normed_field 𝕜]
{E : Type*}
[normed_group E]
[normed_space 𝕜 E]
{H : Type*}
[topological_space H]
(I : model_with_corners 𝕜 E H)
(M : Type*)
[topological_space M]
[charted_space H M]
[smooth_manifold_with_corners I M]
(F : Type*)
[normed_group F]
[normed_space 𝕜 F] :=
  (coord_change : atlas H M → atlas H M → H → F → F)
  (coord_change_self : ∀ i : atlas H M, ∀ x «expr ∈ » i.1.target, ∀ v, «expr = »(coord_change i i x v, v))
  (coord_change_comp : ∀
   i
   j
   k : atlas H M, ∀
   x «expr ∈ » ((i.1.symm.trans j.1).trans (j.1.symm.trans k.1)).source, ∀
   v, «expr = »(coord_change j k (i.1.symm.trans j.1 x) (coord_change i j x v), coord_change i k x v))
  (coord_change_smooth : ∀
   i
   j : atlas H M, times_cont_diff_on 𝕜 «expr∞»() (λ
    p : «expr × »(E, F), coord_change i j (I.symm p.1) p.2) («expr '' »(I, (i.1.symm.trans j.1).source).prod (univ : set F)))

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

-- error in Geometry.Manifold.BasicSmoothBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Fiber bundle core associated to a basic smooth bundle core -/
def to_topological_fiber_bundle_core : topological_fiber_bundle_core (atlas H M) M F :=
{ base_set := λ i, i.1.source,
  is_open_base_set := λ i, i.1.open_source,
  index_at := λ x, ⟨chart_at H x, chart_mem_atlas H x⟩,
  mem_base_set_at := λ x, mem_chart_source H x,
  coord_change := λ i j x v, Z.coord_change i j (i.1 x) v,
  coord_change_self := λ i x hx v, Z.coord_change_self i (i.1 x) (i.1.map_source hx) v,
  coord_change_comp := λ (i j k x) ⟨⟨hx1, hx2⟩, hx3⟩ (v), begin
    have [] [] [":=", expr Z.coord_change_comp i j k (i.1 x) _ v],
    convert [] [expr this] ["using", 2],
    { simp [] [] ["only"] ["[", expr hx1, "]"] ["with", ident mfld_simps] [] },
    { simp [] [] ["only"] ["[", expr hx1, ",", expr hx2, ",", expr hx3, "]"] ["with", ident mfld_simps] [] }
  end,
  coord_change_continuous := λ i j, begin
    have [ident A] [":", expr continuous_on (λ
      p : «expr × »(E, F), Z.coord_change i j (I.symm p.1) p.2) («expr '' »(I, (i.1.symm.trans j.1).source).prod (univ : set F))] [":=", expr (Z.coord_change_smooth i j).continuous_on],
    have [ident B] [":", expr continuous_on (λ
      x : M, I (i.1 x)) i.1.source] [":=", expr I.continuous.comp_continuous_on i.1.continuous_on],
    have [ident C] [":", expr continuous_on (λ
      p : «expr × »(M, F), (⟨I (i.1 p.1), p.2⟩ : «expr × »(E, F))) (i.1.source.prod univ)] [],
    { apply [expr continuous_on.prod _ continuous_snd.continuous_on],
      exact [expr B.comp continuous_fst.continuous_on (prod_subset_preimage_fst _ _)] },
    have [ident C'] [":", expr continuous_on (λ
      p : «expr × »(M, F), (⟨I (i.1 p.1), p.2⟩ : «expr × »(E, F))) («expr ∩ »(i.1.source, j.1.source).prod univ)] [":=", expr continuous_on.mono C (prod_mono (inter_subset_left _ _) (subset.refl _))],
    have [ident D] [":", expr «expr ⊆ »(«expr ∩ »(i.1.source, j.1.source).prod univ, «expr ⁻¹' »(λ
       p : «expr × »(M, F), (I (i.1 p.1), p.2), «expr '' »(I, (i.1.symm.trans j.1).source).prod univ))] [],
    { rintros ["⟨", ident x, ",", ident v, "⟩", ident hx],
      simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hx],
      simp [] [] ["only"] ["[", expr hx, "]"] ["with", ident mfld_simps] [] },
    convert [] [expr continuous_on.comp A C' D] [],
    ext [] [ident p] [],
    simp [] [] ["only"] [] ["with", ident mfld_simps] []
  end }

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

-- error in Geometry.Manifold.BasicSmoothBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Smooth manifold structure on the total space of a basic smooth bundle -/
instance to_smooth_manifold : smooth_manifold_with_corners (I.prod «expr𝓘( , )»(𝕜, F)) Z.to_topological_fiber_bundle_core.total_space :=
begin
  let [ident J] [] [":=", expr model_with_corners.to_local_equiv (I.prod «expr𝓘( , )»(𝕜, F))],
  have [ident A] [":", expr ∀
   (e e' : local_homeomorph M H)
   (he : «expr ∈ »(e, atlas H M))
   (he' : «expr ∈ »(e', atlas H M)), times_cont_diff_on 𝕜 «expr∞»() «expr ∘ »(J, «expr ∘ »((Z.chart he).symm.trans (Z.chart he'), J.symm)) «expr ∩ »(«expr ⁻¹' »(J.symm, ((Z.chart he).symm.trans (Z.chart he')).source), range J)] [],
  { assume [binders (e e' he he')],
    have [] [":", expr «expr = »(«expr ∩ »(«expr ⁻¹' »(J.symm, ((chart Z he).symm.trans (chart Z he')).source), range J), «expr ∩ »(«expr ⁻¹' »(I.symm, (e.symm.trans e').source), range I).prod univ)] [],
    by { simp [] [] ["only"] ["[", expr J, ",", expr chart, ",", expr model_with_corners.prod, "]"] [] [],
      mfld_set_tac },
    rw [expr this] [],
    apply [expr times_cont_diff_on.prod],
    show [expr times_cont_diff_on 𝕜 «expr∞»() (λ
      p : «expr × »(E, F), «expr ∘ »(I, «expr ∘ »(e', «expr ∘ »(e.symm, I.symm))) p.1) («expr ∩ »(«expr ⁻¹' »(I.symm, (e.symm.trans e').source), range I).prod (univ : set F))],
    { have [ident A] [":", expr times_cont_diff_on 𝕜 «expr∞»() «expr ∘ »(I, «expr ∘ »(e.symm.trans e', I.symm)) «expr ∩ »(«expr ⁻¹' »(I.symm, (e.symm.trans e').source), range I)] [":=", expr (has_groupoid.compatible (times_cont_diff_groupoid «expr∞»() I) he he').1],
      have [ident B] [":", expr times_cont_diff_on 𝕜 «expr∞»() (λ
        p : «expr × »(E, F), p.1) («expr ∩ »(«expr ⁻¹' »(I.symm, (e.symm.trans e').source), range I).prod univ)] [":=", expr times_cont_diff_fst.times_cont_diff_on],
      exact [expr times_cont_diff_on.comp A B (prod_subset_preimage_fst _ _)] },
    show [expr times_cont_diff_on 𝕜 «expr∞»() (λ
      p : «expr × »(E, F), Z.coord_change ⟨chart_at H (e.symm (I.symm p.1)), _⟩ ⟨e', he'⟩ ((chart_at H (e.symm (I.symm p.1)) : M → H) (e.symm (I.symm p.1))) (Z.coord_change ⟨e, he⟩ ⟨chart_at H (e.symm (I.symm p.1)), _⟩ (e (e.symm (I.symm p.1))) p.2)) («expr ∩ »(«expr ⁻¹' »(I.symm, (e.symm.trans e').source), range I).prod (univ : set F))],
    { have [] [] [":=", expr Z.coord_change_smooth ⟨e, he⟩ ⟨e', he'⟩],
      rw [expr I.image_eq] ["at", ident this],
      apply [expr times_cont_diff_on.congr this],
      rintros ["⟨", ident x, ",", ident v, "⟩", ident hx],
      simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hx],
      let [ident f] [] [":=", expr chart_at H (e.symm (I.symm x))],
      have [ident A] [":", expr «expr ∈ »(I.symm x, ((e.symm.trans f).trans (f.symm.trans e')).source)] [],
      by simp [] [] ["only"] ["[", expr hx.1.1, ",", expr hx.1.2, "]"] ["with", ident mfld_simps] [],
      rw [expr e.right_inv hx.1.1] [],
      have [] [] [":=", expr Z.coord_change_comp ⟨e, he⟩ ⟨f, chart_mem_atlas _ _⟩ ⟨e', he'⟩ (I.symm x) A v],
      simpa [] [] ["only"] ["[", "]"] [] ["using", expr this] } },
  refine [expr @smooth_manifold_with_corners.mk _ _ _ _ _ _ _ _ _ _ _ ⟨_⟩],
  assume [binders (e₀ e₀' he₀ he₀')],
  rcases [expr (Z.mem_atlas_iff _).1 he₀, "with", "⟨", ident e, ",", ident he, ",", ident rfl, "⟩"],
  rcases [expr (Z.mem_atlas_iff _).1 he₀', "with", "⟨", ident e', ",", ident he', ",", ident rfl, "⟩"],
  rw ["[", expr times_cont_diff_groupoid, ",", expr mem_groupoid_of_pregroupoid, "]"] [],
  exact [expr ⟨A e e' he he', A e' e he' he⟩]
end

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

-- error in Geometry.Manifold.BasicSmoothBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Basic smooth bundle core version of the tangent bundle of a smooth manifold `M` modelled over a
model with corners `I` on `(E, H)`. The fibers are equal to `E`, and the coordinate change in the
fiber corresponds to the derivative of the coordinate change in `M`. -/
def tangent_bundle_core : basic_smooth_bundle_core I M E :=
{ coord_change := λ
  i j x v, (fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) (range I) (I x) : E → E) v,
  coord_change_smooth := λ i j, begin
    rw [expr I.image_eq] [],
    have [ident A] [":", expr times_cont_diff_on 𝕜 «expr∞»() «expr ∘ »(I, «expr ∘ »(i.1.symm.trans j.1, I.symm)) «expr ∩ »(«expr ⁻¹' »(I.symm, (i.1.symm.trans j.1).source), range I)] [":=", expr (has_groupoid.compatible (times_cont_diff_groupoid «expr∞»() I) i.2 j.2).1],
    have [ident B] [":", expr unique_diff_on 𝕜 «expr ∩ »(«expr ⁻¹' »(I.symm, (i.1.symm.trans j.1).source), range I)] [":=", expr I.unique_diff_preimage_source],
    have [ident C] [":", expr times_cont_diff_on 𝕜 «expr∞»() (λ
      p : «expr × »(E, E), (fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, (i.1.symm.trans j.1).source), range I) p.1 : E → E) p.2) («expr ∩ »(«expr ⁻¹' »(I.symm, (i.1.symm.trans j.1).source), range I).prod univ)] [":=", expr times_cont_diff_on_fderiv_within_apply A B le_top],
    have [ident D] [":", expr ∀
     x «expr ∈ » «expr ∩ »(«expr ⁻¹' »(I.symm, (i.1.symm.trans j.1).source), range I), «expr = »(fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) (range I) x, fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, (i.1.symm.trans j.1).source), range I) x)] [],
    { assume [binders (x hx)],
      have [ident N] [":", expr «expr ∈ »(«expr ⁻¹' »(I.symm, (i.1.symm.trans j.1).source), nhds x)] [":=", expr I.continuous_symm.continuous_at.preimage_mem_nhds (is_open.mem_nhds (local_homeomorph.open_source _) hx.1)],
      symmetry,
      rw [expr inter_comm] [],
      exact [expr fderiv_within_inter N (I.unique_diff _ hx.2)] },
    apply [expr times_cont_diff_on.congr C],
    rintros ["⟨", ident x, ",", ident v, "⟩", ident hx],
    have [ident E] [":", expr «expr ∈ »(x, «expr ∩ »(«expr ⁻¹' »(I.symm, (i.1.symm.trans j.1).source), range I))] [],
    by simpa [] [] ["only"] ["[", expr prod_mk_mem_set_prod_eq, ",", expr and_true, ",", expr mem_univ, "]"] [] ["using", expr hx],
    have [] [":", expr «expr = »(I (I.symm x), x)] [],
    by simp [] [] [] ["[", expr E.2, "]"] [] [],
    dsimp [] ["[", "-", ident subtype.val_eq_coe, "]"] [] [],
    rw ["[", expr this, ",", expr D x E, "]"] [],
    refl
  end,
  coord_change_self := λ i x hx v, begin
    have [ident A] [":", expr «expr ∈ »(«expr ∩ »(«expr ⁻¹' »(I.symm, (i.1.symm.trans i.1).source), range I), «expr𝓝[ ] »(range I, I x))] [],
    { rw [expr inter_comm] [],
      apply [expr inter_mem_nhds_within],
      apply [expr I.continuous_symm.continuous_at.preimage_mem_nhds (is_open.mem_nhds (local_homeomorph.open_source _) _)],
      simp [] [] ["only"] ["[", expr hx, ",", expr i.1.map_target, "]"] ["with", ident mfld_simps] [] },
    have [ident B] [":", expr «expr∀ᶠ in , »((y), «expr𝓝[ ] »(range I, I x), «expr = »(«expr ∘ »(I, «expr ∘ »(i.1, «expr ∘ »(i.1.symm, I.symm))) y, (id : E → E) y))] [],
    { filter_upwards ["[", expr A, "]"] [],
      assume [binders (y hy)],
      rw ["<-", expr I.image_eq] ["at", ident hy],
      rcases [expr hy, "with", "⟨", ident z, ",", ident hz, "⟩"],
      simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hz],
      simp [] [] ["only"] ["[", expr hz.2.symm, ",", expr hz.1, "]"] ["with", ident mfld_simps] [] },
    have [ident C] [":", expr «expr = »(fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(i.1, «expr ∘ »(i.1.symm, I.symm))) (range I) (I x), fderiv_within 𝕜 (id : E → E) (range I) (I x))] [":=", expr filter.eventually_eq.fderiv_within_eq I.unique_diff_at_image B (by simp [] [] ["only"] ["[", expr hx, "]"] ["with", ident mfld_simps] [])],
    rw [expr fderiv_within_id I.unique_diff_at_image] ["at", ident C],
    rw [expr C] [],
    refl
  end,
  coord_change_comp := λ i j u x hx, begin
    have [ident M] [":", expr «expr ∈ »(I x, «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I))] [":=", expr ⟨by simpa [] [] ["only"] ["[", expr mem_preimage, ",", expr model_with_corners.left_inv, "]"] [] ["using", expr hx], mem_range_self _⟩],
    have [ident U] [":", expr unique_diff_within_at 𝕜 «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I) (I x)] [":=", expr I.unique_diff_preimage_source _ M],
    have [ident A] [":", expr «expr = »(fderiv_within 𝕜 «expr ∘ »(«expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(j.1.symm, I.symm))), «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm)))) «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I) (I x), (fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(j.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, (j.1.symm.trans u.1).source), range I) («expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) (I x))).comp (fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I) (I x)))] [],
    { apply [expr fderiv_within.comp _ _ _ _ U],
      show [expr differentiable_within_at 𝕜 «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I) (I x)],
      { have [ident A] [":", expr times_cont_diff_on 𝕜 «expr∞»() «expr ∘ »(I, «expr ∘ »(i.1.symm.trans j.1, I.symm)) «expr ∩ »(«expr ⁻¹' »(I.symm, (i.1.symm.trans j.1).source), range I)] [":=", expr (has_groupoid.compatible (times_cont_diff_groupoid «expr∞»() I) i.2 j.2).1],
        have [ident B] [":", expr differentiable_on 𝕜 «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I)] [],
        { apply [expr (A.differentiable_on le_top).mono],
          have [] [":", expr «expr ⊆ »(((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source, (i.1.symm.trans j.1).source)] [":=", expr inter_subset_left _ _],
          exact [expr inter_subset_inter (preimage_mono this) (subset.refl (range I))] },
        apply [expr B],
        simpa [] [] ["only"] ["[", "]"] ["with", ident mfld_simps] ["using", expr hx] },
      show [expr differentiable_within_at 𝕜 «expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(j.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, (j.1.symm.trans u.1).source), range I) («expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) (I x))],
      { have [ident A] [":", expr times_cont_diff_on 𝕜 «expr∞»() «expr ∘ »(I, «expr ∘ »(j.1.symm.trans u.1, I.symm)) «expr ∩ »(«expr ⁻¹' »(I.symm, (j.1.symm.trans u.1).source), range I)] [":=", expr (has_groupoid.compatible (times_cont_diff_groupoid «expr∞»() I) j.2 u.2).1],
        apply [expr A.differentiable_on le_top],
        rw ["[", expr local_homeomorph.trans_source, "]"] ["at", ident hx],
        simp [] [] ["only"] [] ["with", ident mfld_simps] [],
        exact [expr hx.2] },
      show [expr «expr ⊆ »(«expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I), «expr ⁻¹' »(«expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))), «expr ∩ »(«expr ⁻¹' »(I.symm, (j.1.symm.trans u.1).source), range I)))],
      { assume [binders (y hy)],
        simp [] [] ["only"] [] ["with", ident mfld_simps] ["at", ident hy],
        rw ["[", expr local_homeomorph.left_inv, "]"] ["at", ident hy],
        { simp [] [] ["only"] ["[", expr hy, "]"] ["with", ident mfld_simps] [] },
        { exact [expr hy.1.1.2] } } },
    have [ident B] [":", expr «expr = »(fderiv_within 𝕜 «expr ∘ »(«expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(j.1.symm, I.symm))), «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm)))) «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I) (I x), fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(i.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I) (I x))] [],
    { have [ident E] [":", expr ∀
       y «expr ∈ » «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I), «expr = »(«expr ∘ »(«expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(j.1.symm, I.symm))), «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm)))) y, «expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(i.1.symm, I.symm))) y)] [],
      { assume [binders (y hy)],
        simp [] [] ["only"] ["[", expr function.comp_app, ",", expr model_with_corners.left_inv, "]"] [] [],
        rw ["[", expr j.1.left_inv, "]"] [],
        exact [expr hy.1.1.2] },
      exact [expr fderiv_within_congr U E (E _ M)] },
    have [ident C] [":", expr «expr = »(fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(i.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I) (I x), fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(i.1.symm, I.symm))) (range I) (I x))] [],
    { rw [expr inter_comm] [],
      apply [expr fderiv_within_inter _ I.unique_diff_at_image],
      apply [expr I.continuous_symm.continuous_at.preimage_mem_nhds (is_open.mem_nhds (local_homeomorph.open_source _) _)],
      simpa [] [] ["only"] ["[", expr model_with_corners.left_inv, "]"] [] ["using", expr hx] },
    have [ident D] [":", expr «expr = »(fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(j.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, (j.1.symm.trans u.1).source), range I) («expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) (I x)), fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(u.1, «expr ∘ »(j.1.symm, I.symm))) (range I) («expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) (I x)))] [],
    { rw [expr inter_comm] [],
      apply [expr fderiv_within_inter _ I.unique_diff_at_image],
      apply [expr I.continuous_symm.continuous_at.preimage_mem_nhds (is_open.mem_nhds (local_homeomorph.open_source _) _)],
      rw ["[", expr local_homeomorph.trans_source, "]"] ["at", ident hx],
      simp [] [] ["only"] [] ["with", ident mfld_simps] [],
      exact [expr hx.2] },
    have [ident E] [":", expr «expr = »(fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) «expr ∩ »(«expr ⁻¹' »(I.symm, ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source), range I) (I x), fderiv_within 𝕜 «expr ∘ »(I, «expr ∘ »(j.1, «expr ∘ »(i.1.symm, I.symm))) (range I) (I x))] [],
    { rw [expr inter_comm] [],
      apply [expr fderiv_within_inter _ I.unique_diff_at_image],
      apply [expr I.continuous_symm.continuous_at.preimage_mem_nhds (is_open.mem_nhds (local_homeomorph.open_source _) _)],
      simpa [] [] ["only"] ["[", expr model_with_corners.left_inv, "]"] [] ["using", expr hx] },
    rw ["[", expr B, ",", expr C, ",", expr D, ",", expr E, "]"] ["at", ident A],
    simp [] [] ["only"] ["[", expr A, ",", expr continuous_linear_map.coe_comp', "]"] ["with", ident mfld_simps] []
  end }

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

-- error in Geometry.Manifold.BasicSmoothBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `equiv.sigma_equiv_prod`. -/
@[simp, mfld_simps #[]]
theorem tangent_bundle_model_space_chart_at
(p : tangent_bundle I H) : «expr = »((chart_at (model_prod H E) p).to_local_equiv, (equiv.sigma_equiv_prod H E).to_local_equiv) :=
begin
  have [ident A] [":", expr ∀
   x_fst, «expr = »(fderiv_within 𝕜 «expr ∘ »(I, I.symm) (range I) (I x_fst), continuous_linear_map.id 𝕜 E)] [],
  { assume [binders (x_fst)],
    have [] [":", expr «expr = »(fderiv_within 𝕜 «expr ∘ »(I, I.symm) (range I) (I x_fst), fderiv_within 𝕜 id (range I) (I x_fst))] [],
    { refine [expr fderiv_within_congr I.unique_diff_at_image (λ y hy, _) (by simp [] [] [] [] [] [])],
      exact [expr model_with_corners.right_inv _ hy] },
    rwa [expr fderiv_within_id I.unique_diff_at_image] ["at", ident this] },
  ext [] [ident x] [":", 1],
  show [expr «expr = »((chart_at (model_prod H E) p : tangent_bundle I H → model_prod H E) x, equiv.sigma_equiv_prod H E x)],
  { cases [expr x] [],
    simp [] [] ["only"] ["[", expr chart_at, ",", expr basic_smooth_bundle_core.chart, ",", expr tangent_bundle_core, ",", expr basic_smooth_bundle_core.to_topological_fiber_bundle_core, ",", expr A, ",", expr prod.mk.inj_iff, ",", expr continuous_linear_map.coe_id', "]"] ["with", ident mfld_simps] [] },
  show [expr ∀ x, «expr = »((chart_at (model_prod H E) p).to_local_equiv.symm x, (equiv.sigma_equiv_prod H E).symm x)],
  { rintros ["⟨", ident x_fst, ",", ident x_snd, "⟩"],
    simp [] [] ["only"] ["[", expr chart_at, ",", expr basic_smooth_bundle_core.chart, ",", expr tangent_bundle_core, ",", expr continuous_linear_map.coe_id', ",", expr basic_smooth_bundle_core.to_topological_fiber_bundle_core, ",", expr A, "]"] ["with", ident mfld_simps] [] },
  show [expr «expr = »((chart_at (model_prod H E) p).to_local_equiv.source, univ)],
  by simp [] [] ["only"] ["[", expr chart_at, "]"] ["with", ident mfld_simps] []
end

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

-- error in Geometry.Manifold.BasicSmoothBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism -/ def tangent_bundle_model_space_homeomorph : «expr ≃ₜ »(tangent_bundle I H, model_prod H E) :=
{ continuous_to_fun := begin
    let [ident p] [":", expr tangent_bundle I H] [":=", expr ⟨I.symm (0 : E), (0 : E)⟩],
    have [] [":", expr continuous (chart_at (model_prod H E) p)] [],
    { rw [expr continuous_iff_continuous_on_univ] [],
      convert [] [expr local_homeomorph.continuous_on _] [],
      simp [] [] ["only"] [] ["with", ident mfld_simps] [] },
    simpa [] [] ["only"] [] ["with", ident mfld_simps] ["using", expr this]
  end,
  continuous_inv_fun := begin
    let [ident p] [":", expr tangent_bundle I H] [":=", expr ⟨I.symm (0 : E), (0 : E)⟩],
    have [] [":", expr continuous (chart_at (model_prod H E) p).symm] [],
    { rw [expr continuous_iff_continuous_on_univ] [],
      convert [] [expr local_homeomorph.continuous_on _] [],
      simp [] [] ["only"] [] ["with", ident mfld_simps] [] },
    simpa [] [] ["only"] [] ["with", ident mfld_simps] ["using", expr this]
  end,
  ..equiv.sigma_equiv_prod H E }

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

