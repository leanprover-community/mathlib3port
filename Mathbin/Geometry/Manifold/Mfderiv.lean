/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Geometry.Manifold.LocalInvariantProperties
import Mathbin.Geometry.Manifold.TangentBundle

/-!
# The derivative of functions between smooth manifolds

Let `M` and `M'` be two smooth manifolds with corners over a field `𝕜` (with respective models with
corners `I` on `(E, H)` and `I'` on `(E', H')`), and let `f : M → M'`. We define the
derivative of the function at a point, within a set or along the whole space, mimicking the API
for (Fréchet) derivatives. It is denoted by `mfderiv I I' f x`, where "m" stands for "manifold" and
"f" for "Fréchet" (as in the usual derivative `fderiv 𝕜 f x`).

## Main definitions

* `unique_mdiff_on I s` : predicate saying that, at each point of the set `s`, a function can have
  at most one derivative. This technical condition is important when we define
  `mfderiv_within` below, as otherwise there is an arbitrary choice in the derivative,
  and many properties will fail (for instance the chain rule). This is analogous to
  `unique_diff_on 𝕜 s` in a vector space.

Let `f` be a map between smooth manifolds. The following definitions follow the `fderiv` API.

* `mfderiv I I' f x` : the derivative of `f` at `x`, as a continuous linear map from the tangent
  space at `x` to the tangent space at `f x`. If the map is not differentiable, this is `0`.
* `mfderiv_within I I' f s x` : the derivative of `f` at `x` within `s`, as a continuous linear map
  from the tangent space at `x` to the tangent space at `f x`. If the map is not differentiable
  within `s`, this is `0`.
* `mdifferentiable_at I I' f x` : Prop expressing whether `f` is differentiable at `x`.
* `mdifferentiable_within_at 𝕜 f s x` : Prop expressing whether `f` is differentiable within `s`
  at `x`.
* `has_mfderiv_at I I' f s x f'` : Prop expressing whether `f` has `f'` as a derivative at `x`.
* `has_mfderiv_within_at I I' f s x f'` : Prop expressing whether `f` has `f'` as a derivative
  within `s` at `x`.
* `mdifferentiable_on I I' f s` : Prop expressing that `f` is differentiable on the set `s`.
* `mdifferentiable I I' f` : Prop expressing that `f` is differentiable everywhere.
* `tangent_map I I' f` : the derivative of `f`, as a map from the tangent bundle of `M` to the
  tangent bundle of `M'`.

We also establish results on the differential of the identity, constant functions, charts, extended
charts. For functions between vector spaces, we show that the usual notions and the manifold notions
coincide.

## Implementation notes

The tangent bundle is constructed using the machinery of topological fiber bundles, for which one
can define bundled morphisms and construct canonically maps from the total space of one bundle to
the total space of another one. One could use this mechanism to construct directly the derivative
of a smooth map. However, we want to define the derivative of any map (and let it be zero if the map
is not differentiable) to avoid proof arguments everywhere. This means we have to go back to the
details of the definition of the total space of a fiber bundle constructed from core, to cook up a
suitable definition of the derivative. It is the following: at each point, we have a preferred chart
(used to identify the fiber above the point with the model vector space in fiber bundles). Then one
should read the function using these preferred charts at `x` and `f x`, and take the derivative
of `f` in these charts.

Due to the fact that we are working in a model with corners, with an additional embedding `I` of the
model space `H` in the model vector space `E`, the charts taking values in `E` are not the original
charts of the manifold, but those ones composed with `I`, called extended charts. We define
`written_in_ext_chart I I' x f` for the function `f` written in the preferred extended charts.  Then
the manifold derivative of `f`, at `x`, is just the usual derivative of `written_in_ext_chart I I' x
f`, at the point `(ext_chart_at I x) x`.

There is a subtelty with respect to continuity: if the function is not continuous, then the image
of a small open set around `x` will not be contained in the source of the preferred chart around
`f x`, which means that when reading `f` in the chart one is losing some information. To avoid this,
we include continuity in the definition of differentiablity (which is reasonable since with any
definition, differentiability implies continuity).

*Warning*: the derivative (even within a subset) is a linear map on the whole tangent space. Suppose
that one is given a smooth submanifold `N`, and a function which is smooth on `N` (i.e., its
restriction to the subtype  `N` is smooth). Then, in the whole manifold `M`, the property
`mdifferentiable_on I I' f N` holds. However, `mfderiv_within I I' f N` is not uniquely defined
(what values would one choose for vectors that are transverse to `N`?), which can create issues down
the road. The problem here is that knowing the value of `f` along `N` does not determine the
differential of `f` in all directions. This is in contrast to the case where `N` would be an open
subset, or a submanifold with boundary of maximal dimension, where this issue does not appear.
The predicate `unique_mdiff_on I N` indicates that the derivative along `N` is unique if it exists,
and is an assumption in most statements requiring a form of uniqueness.

On a vector space, the manifold derivative and the usual derivative are equal. This means in
particular that they live on the same space, i.e., the tangent space is defeq to the original vector
space. To get this property is a motivation for our definition of the tangent space as a single
copy of the vector space, instead of more usual definitions such as the space of derivations, or
the space of equivalence classes of smooth curves in the manifold.

## Tags
Derivative, manifold
-/


noncomputable section

open Classical TopologicalSpace Manifold

open Set

universe u

section DerivativesDefinitions

/-!
### Derivative of maps between manifolds

The derivative of a smooth map `f` between smooth manifold `M` and `M'` at `x` is a bounded linear
map from the tangent space to `M` at `x`, to the tangent space to `M'` at `f x`. Since we defined
the tangent space using one specific chart, the formula for the derivative is written in terms of
this specific chart.

We use the names `mdifferentiable` and `mfderiv`, where the prefix letter `m` means "manifold".
-/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M] [ChartedSpace H M] {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']

/-- Property in the model space of a model with corners of being differentiable within at set at a
point, when read in the model vector space. This property will be lifted to manifolds to define
differentiable functions between manifolds. -/
def DifferentiableWithinAtProp (f : H → H') (s : Set H) (x : H) : Prop :=
  DifferentiableWithinAt 𝕜 (I' ∘ f ∘ I.symm) (⇑I.symm ⁻¹' s ∩ Set.range I) (I x)
#align differentiable_within_at_prop DifferentiableWithinAtProp

/-- Being differentiable in the model space is a local property, invariant under smooth maps.
Therefore, it will lift nicely to manifolds. -/
theorem differentiable_within_at_local_invariant_prop :
    (contDiffGroupoid ⊤ I).LocalInvariantProp (contDiffGroupoid ⊤ I') (DifferentiableWithinAtProp I I') :=
  { is_local := by
      intro s x u f u_open xu
      have : I.symm ⁻¹' (s ∩ u) ∩ Set.range I = I.symm ⁻¹' s ∩ Set.range I ∩ I.symm ⁻¹' u := by
        simp only [Set.inter_right_comm, Set.preimage_inter]
      rw [DifferentiableWithinAtProp, DifferentiableWithinAtProp, this]
      symm
      apply differentiable_within_at_inter
      have : u ∈ 𝓝 (I.symm (I x)) := by
        rw [ModelWithCorners.left_inv]
        exact IsOpen.mem_nhds u_open xu
      apply ContinuousAt.preimage_mem_nhds I.continuous_symm.continuous_at this,
    right_invariance' := by
      intro s x f e he hx h
      rw [DifferentiableWithinAtProp] at h⊢
      have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
      rw [this] at h
      have : I (e x) ∈ I.symm ⁻¹' e.target ∩ Set.range I := by simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he).2.ContDiffWithinAt this
      convert (h.comp' _ (this.differentiable_within_at le_top)).mono_of_mem _ using 1
      · ext y
        simp only [mfld_simps]
        
      refine'
        mem_nhds_within.mpr
          ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
            simp_rw [Set.mem_preimage, I.left_inv, e.maps_to hx], _⟩
      mfld_set_tac,
    congr_of_forall := by
      intro s x f g h hx hf
      apply hf.congr
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [h, hy, mfld_simps]
        
      · simp only [hx, mfld_simps]
        ,
    left_invariance' := by
      intro s x f e' he' hs hx h
      rw [DifferentiableWithinAtProp] at h⊢
      have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ Set.range I' := by simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he').1.ContDiffWithinAt A
      convert (this.differentiable_within_at le_top).comp _ h _
      · ext y
        simp only [mfld_simps]
        
      · intro y hy
        simp only [mfld_simps] at hy
        simpa only [hy, mfld_simps] using hs hy.1
         }
#align differentiable_within_at_local_invariant_prop differentiable_within_at_local_invariant_prop

/-- Predicate ensuring that, at a point and within a set, a function can have at most one
derivative. This is expressed using the preferred chart at the considered point. -/
def UniqueMdiffWithinAt (s : Set M) (x : M) :=
  UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
#align unique_mdiff_within_at UniqueMdiffWithinAt

/-- Predicate ensuring that, at all points of a set, a function can have at most one derivative. -/
def UniqueMdiffOn (s : Set M) :=
  ∀ x ∈ s, UniqueMdiffWithinAt I s x
#align unique_mdiff_on UniqueMdiffOn

/-- `mdifferentiable_within_at I I' f s x` indicates that the function `f` between manifolds
has a derivative at the point `x` within the set `s`.
This is a generalization of `differentiable_within_at` to manifolds.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def MdifferentiableWithinAt (f : M → M') (s : Set M) (x : M) :=
  ContinuousWithinAt f s x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
#align mdifferentiable_within_at MdifferentiableWithinAt

theorem mdifferentiable_within_at_iff_lift_prop_within_at (f : M → M') (s : Set M) (x : M) :
    MdifferentiableWithinAt I I' f s x ↔ LiftPropWithinAt (DifferentiableWithinAtProp I I') f s x := by rfl
#align mdifferentiable_within_at_iff_lift_prop_within_at mdifferentiable_within_at_iff_lift_prop_within_at

/-- `mdifferentiable_at I I' f x` indicates that the function `f` between manifolds
has a derivative at the point `x`.
This is a generalization of `differentiable_at` to manifolds.

We require continuity in the definition, as otherwise points close to `x` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def MdifferentiableAt (f : M → M') (x : M) :=
  ContinuousAt f x ∧ DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x)
#align mdifferentiable_at MdifferentiableAt

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]] -/
theorem mdifferentiable_at_iff_lift_prop_at (f : M → M') (x : M) :
    MdifferentiableAt I I' f x ↔ LiftPropAt (DifferentiableWithinAtProp I I') f x := by
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:66:14: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]"
  · rw [continuous_within_at_univ]
    
  · simp [DifferentiableWithinAtProp, Set.univ_inter]
    
#align mdifferentiable_at_iff_lift_prop_at mdifferentiable_at_iff_lift_prop_at

/-- `mdifferentiable_on I I' f s` indicates that the function `f` between manifolds
has a derivative within `s` at all points of `s`.
This is a generalization of `differentiable_on` to manifolds. -/
def MdifferentiableOn (f : M → M') (s : Set M) :=
  ∀ x ∈ s, MdifferentiableWithinAt I I' f s x
#align mdifferentiable_on MdifferentiableOn

/-- `mdifferentiable I I' f` indicates that the function `f` between manifolds
has a derivative everywhere.
This is a generalization of `differentiable` to manifolds. -/
def Mdifferentiable (f : M → M') :=
  ∀ x, MdifferentiableAt I I' f x
#align mdifferentiable Mdifferentiable

/-- Prop registering if a local homeomorphism is a local diffeomorphism on its source -/
def LocalHomeomorph.Mdifferentiable (f : LocalHomeomorph M M') :=
  MdifferentiableOn I I' f f.source ∧ MdifferentiableOn I' I f.symm f.target
#align local_homeomorph.mdifferentiable LocalHomeomorph.Mdifferentiable

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M']

/-- `has_mfderiv_within_at I I' f s x f'` indicates that the function `f` between manifolds
has, at the point `x` and within the set `s`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

This is a generalization of `has_fderiv_within_at` to manifolds (as indicated by the prefix `m`).
The order of arguments is changed as the type of the derivative `f'` depends on the choice of `x`.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def HasMfderivWithinAt (f : M → M') (s : Set M) (x : M) (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousWithinAt f s x ∧
    HasFderivWithinAt (writtenInExtChartAt I I' x f : E → E') f' ((extChartAt I x).symm ⁻¹' s ∩ range I)
      ((extChartAt I x) x)
#align has_mfderiv_within_at HasMfderivWithinAt

/-- `has_mfderiv_at I I' f x f'` indicates that the function `f` between manifolds
has, at the point `x`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

We require continuity in the definition, as otherwise points close to `x` `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def HasMfderivAt (f : M → M') (x : M) (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousAt f x ∧ HasFderivWithinAt (writtenInExtChartAt I I' x f : E → E') f' (range I) ((extChartAt I x) x)
#align has_mfderiv_at HasMfderivAt

/-- Let `f` be a function between two smooth manifolds. Then `mfderiv_within I I' f s x` is the
derivative of `f` at `x` within `s`, as a continuous linear map from the tangent space at `x` to the
tangent space at `f x`. -/
def mfderivWithin (f : M → M') (s : Set M) (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if h : MdifferentiableWithinAt I I' f s x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) : _)
  else 0
#align mfderiv_within mfderivWithin

/-- Let `f` be a function between two smooth manifolds. Then `mfderiv I I' f x` is the derivative of
`f` at `x`, as a continuous linear map from the tangent space at `x` to the tangent space at
`f x`. -/
def mfderiv (f : M → M') (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if h : MdifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f : E → E') (range I) ((extChartAt I x) x) : _)
  else 0
#align mfderiv mfderiv

/-- The derivative within a set, as a map between the tangent bundles -/
def tangentMapWithin (f : M → M') (s : Set M) : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderivWithin I I' f s p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩
#align tangent_map_within tangentMapWithin

/-- The derivative, as a map between the tangent bundles -/
def tangentMap (f : M → M') : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderiv I I' f p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩
#align tangent_map tangentMap

end DerivativesDefinitions

section DerivativesProperties

/-! ### Unique differentiability sets in manifolds -/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  --
  {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type _} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type _} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type _} [TopologicalSpace M'']
  [ChartedSpace H'' M''] {f f₀ f₁ : M → M'} {x : M} {s t : Set M} {g : M' → M''} {u : Set M'}

theorem uniqueMdiffWithinAtUniv : UniqueMdiffWithinAt I univ x := by
  unfold UniqueMdiffWithinAt
  simp only [preimage_univ, univ_inter]
  exact I.unique_diff _ (mem_range_self _)
#align unique_mdiff_within_at_univ uniqueMdiffWithinAtUniv

variable {I}

theorem unique_mdiff_within_at_iff {s : Set M} {x : M} :
    UniqueMdiffWithinAt I s x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target) ((extChartAt I x) x) :=
  by
  apply unique_diff_within_at_congr
  rw [nhds_within_inter, nhds_within_inter, nhds_within_ext_chart_target_eq]
#align unique_mdiff_within_at_iff unique_mdiff_within_at_iff

theorem UniqueMdiffWithinAt.mono (h : UniqueMdiffWithinAt I s x) (st : s ⊆ t) : UniqueMdiffWithinAt I t x :=
  UniqueDiffWithinAt.mono h <| inter_subset_inter (preimage_mono st) (Subset.refl _)
#align unique_mdiff_within_at.mono UniqueMdiffWithinAt.mono

theorem UniqueMdiffWithinAt.inter' (hs : UniqueMdiffWithinAt I s x) (ht : t ∈ 𝓝[s] x) :
    UniqueMdiffWithinAt I (s ∩ t) x := by
  rw [UniqueMdiffWithinAt, ext_chart_preimage_inter_eq]
  exact UniqueDiffWithinAt.inter' hs (ext_chart_preimage_mem_nhds_within I x ht)
#align unique_mdiff_within_at.inter' UniqueMdiffWithinAt.inter'

theorem UniqueMdiffWithinAt.inter (hs : UniqueMdiffWithinAt I s x) (ht : t ∈ 𝓝 x) : UniqueMdiffWithinAt I (s ∩ t) x :=
  by
  rw [UniqueMdiffWithinAt, ext_chart_preimage_inter_eq]
  exact UniqueDiffWithinAt.inter hs (ext_chart_preimage_mem_nhds I x ht)
#align unique_mdiff_within_at.inter UniqueMdiffWithinAt.inter

theorem IsOpen.uniqueMdiffWithinAt (xs : x ∈ s) (hs : IsOpen s) : UniqueMdiffWithinAt I s x := by
  have := UniqueMdiffWithinAt.inter (uniqueMdiffWithinAtUniv I) (IsOpen.mem_nhds hs xs)
  rwa [univ_inter] at this
#align is_open.unique_mdiff_within_at IsOpen.uniqueMdiffWithinAt

theorem UniqueMdiffOn.inter (hs : UniqueMdiffOn I s) (ht : IsOpen t) : UniqueMdiffOn I (s ∩ t) := fun x hx =>
  UniqueMdiffWithinAt.inter (hs _ hx.1) (IsOpen.mem_nhds ht hx.2)
#align unique_mdiff_on.inter UniqueMdiffOn.inter

theorem IsOpen.uniqueMdiffOn (hs : IsOpen s) : UniqueMdiffOn I s := fun x hx => IsOpen.uniqueMdiffWithinAt hx hs
#align is_open.unique_mdiff_on IsOpen.uniqueMdiffOn

theorem uniqueMdiffOnUniv : UniqueMdiffOn I (univ : Set M) :=
  is_open_univ.UniqueMdiffOn
#align unique_mdiff_on_univ uniqueMdiffOnUniv

/- We name the typeclass variables related to `smooth_manifold_with_corners` structure as they are
necessary in lemmas mentioning the derivative, but not in lemmas about differentiability, so we
want to include them or omit them when necessary. -/
variable [Is : SmoothManifoldWithCorners I M] [I's : SmoothManifoldWithCorners I' M']
  [I''s : SmoothManifoldWithCorners I'' M''] {f' f₀' f₁' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)}
  {g' : TangentSpace I' (f x) →L[𝕜] TangentSpace I'' (g (f x))}

/-- `unique_mdiff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem UniqueMdiffWithinAt.eq (U : UniqueMdiffWithinAt I s x) (h : HasMfderivWithinAt I I' f s x f')
    (h₁ : HasMfderivWithinAt I I' f s x f₁') : f' = f₁' :=
  U.Eq h.2 h₁.2
#align unique_mdiff_within_at.eq UniqueMdiffWithinAt.eq

theorem UniqueMdiffOn.eq (U : UniqueMdiffOn I s) (hx : x ∈ s) (h : HasMfderivWithinAt I I' f s x f')
    (h₁ : HasMfderivWithinAt I I' f s x f₁') : f' = f₁' :=
  UniqueMdiffWithinAt.eq (U _ hx) h h₁
#align unique_mdiff_on.eq UniqueMdiffOn.eq

/-!
### General lemmas on derivatives of functions between manifolds

We mimick the API for functions between vector spaces
-/


theorem mdifferentiable_within_at_iff {f : M → M'} {s : Set M} {x : M} :
    MdifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
          ((extChartAt I x) x) :=
  by
  refine' and_congr Iff.rfl (exists_congr fun f' => _)
  rw [inter_comm]
  simp only [HasFderivWithinAt, nhds_within_inter, nhds_within_ext_chart_target_eq]
#align mdifferentiable_within_at_iff mdifferentiable_within_at_iff

include Is I's

/-- One can reformulate differentiability within a set at a point as continuity within this set at
this point, and differentiability in any chart containing that point. -/
theorem mdifferentiable_within_at_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (ChartedSpace.chartAt H x).source)
    (hy : f x' ∈ (ChartedSpace.chartAt H' y).source) :
    MdifferentiableWithinAt I I' f s x' ↔
      ContinuousWithinAt f s x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ Set.range I) ((extChartAt I x) x') :=
  (differentiable_within_at_local_invariant_prop I I').lift_prop_within_at_indep_chart
    (StructureGroupoid.chart_mem_maximal_atlas _ x) hx (StructureGroupoid.chart_mem_maximal_atlas _ y) hy
#align mdifferentiable_within_at_iff_of_mem_source mdifferentiable_within_at_iff_of_mem_source

theorem mfderiv_within_zero_of_not_mdifferentiable_within_at (h : ¬MdifferentiableWithinAt I I' f s x) :
    mfderivWithin I I' f s x = 0 := by simp only [mfderivWithin, h, dif_neg, not_false_iff]
#align mfderiv_within_zero_of_not_mdifferentiable_within_at mfderiv_within_zero_of_not_mdifferentiable_within_at

theorem mfderiv_zero_of_not_mdifferentiable_at (h : ¬MdifferentiableAt I I' f x) : mfderiv I I' f x = 0 := by
  simp only [mfderiv, h, dif_neg, not_false_iff]
#align mfderiv_zero_of_not_mdifferentiable_at mfderiv_zero_of_not_mdifferentiable_at

theorem HasMfderivWithinAt.mono (h : HasMfderivWithinAt I I' f t x f') (hst : s ⊆ t) :
    HasMfderivWithinAt I I' f s x f' :=
  ⟨ContinuousWithinAt.mono h.1 hst, HasFderivWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩
#align has_mfderiv_within_at.mono HasMfderivWithinAt.mono

theorem HasMfderivAt.hasMfderivWithinAt (h : HasMfderivAt I I' f x f') : HasMfderivWithinAt I I' f s x f' :=
  ⟨ContinuousAt.continuous_within_at h.1, HasFderivWithinAt.mono h.2 (inter_subset_right _ _)⟩
#align has_mfderiv_at.has_mfderiv_within_at HasMfderivAt.hasMfderivWithinAt

theorem HasMfderivWithinAt.mdifferentiableWithinAt (h : HasMfderivWithinAt I I' f s x f') :
    MdifferentiableWithinAt I I' f s x :=
  ⟨h.1, ⟨f', h.2⟩⟩
#align has_mfderiv_within_at.mdifferentiable_within_at HasMfderivWithinAt.mdifferentiableWithinAt

theorem HasMfderivAt.mdifferentiableAt (h : HasMfderivAt I I' f x f') : MdifferentiableAt I I' f x :=
  ⟨h.1, ⟨f', h.2⟩⟩
#align has_mfderiv_at.mdifferentiable_at HasMfderivAt.mdifferentiableAt

@[simp, mfld_simps]
theorem has_mfderiv_within_at_univ : HasMfderivWithinAt I I' f univ x f' ↔ HasMfderivAt I I' f x f' := by
  simp only [HasMfderivWithinAt, HasMfderivAt, continuous_within_at_univ, mfld_simps]
#align has_mfderiv_within_at_univ has_mfderiv_within_at_univ

theorem has_mfderiv_at_unique (h₀ : HasMfderivAt I I' f x f₀') (h₁ : HasMfderivAt I I' f x f₁') : f₀' = f₁' := by
  rw [← has_mfderiv_within_at_univ] at h₀ h₁
  exact (uniqueMdiffWithinAtUniv I).Eq h₀ h₁
#align has_mfderiv_at_unique has_mfderiv_at_unique

theorem has_mfderiv_within_at_inter' (h : t ∈ 𝓝[s] x) :
    HasMfderivWithinAt I I' f (s ∩ t) x f' ↔ HasMfderivWithinAt I I' f s x f' := by
  rw [HasMfderivWithinAt, HasMfderivWithinAt, ext_chart_preimage_inter_eq, has_fderiv_within_at_inter',
    continuous_within_at_inter' h]
  exact ext_chart_preimage_mem_nhds_within I x h
#align has_mfderiv_within_at_inter' has_mfderiv_within_at_inter'

theorem has_mfderiv_within_at_inter (h : t ∈ 𝓝 x) :
    HasMfderivWithinAt I I' f (s ∩ t) x f' ↔ HasMfderivWithinAt I I' f s x f' := by
  rw [HasMfderivWithinAt, HasMfderivWithinAt, ext_chart_preimage_inter_eq, has_fderiv_within_at_inter,
    continuous_within_at_inter h]
  exact ext_chart_preimage_mem_nhds I x h
#align has_mfderiv_within_at_inter has_mfderiv_within_at_inter

theorem HasMfderivWithinAt.union (hs : HasMfderivWithinAt I I' f s x f') (ht : HasMfderivWithinAt I I' f t x f') :
    HasMfderivWithinAt I I' f (s ∪ t) x f' := by
  constructor
  · exact ContinuousWithinAt.union hs.1 ht.1
    
  · convert HasFderivWithinAt.union hs.2 ht.2
    simp only [union_inter_distrib_right, preimage_union]
    
#align has_mfderiv_within_at.union HasMfderivWithinAt.union

theorem HasMfderivWithinAt.nhdsWithin (h : HasMfderivWithinAt I I' f s x f') (ht : s ∈ 𝓝[t] x) :
    HasMfderivWithinAt I I' f t x f' :=
  (has_mfderiv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))
#align has_mfderiv_within_at.nhds_within HasMfderivWithinAt.nhdsWithin

theorem HasMfderivWithinAt.hasMfderivAt (h : HasMfderivWithinAt I I' f s x f') (hs : s ∈ 𝓝 x) :
    HasMfderivAt I I' f x f' := by rwa [← univ_inter s, has_mfderiv_within_at_inter hs, has_mfderiv_within_at_univ] at h
#align has_mfderiv_within_at.has_mfderiv_at HasMfderivWithinAt.hasMfderivAt

theorem MdifferentiableWithinAt.hasMfderivWithinAt (h : MdifferentiableWithinAt I I' f s x) :
    HasMfderivWithinAt I I' f s x (mfderivWithin I I' f s x) := by
  refine' ⟨h.1, _⟩
  simp only [mfderivWithin, h, dif_pos, mfld_simps]
  exact DifferentiableWithinAt.hasFderivWithinAt h.2
#align mdifferentiable_within_at.has_mfderiv_within_at MdifferentiableWithinAt.hasMfderivWithinAt

theorem MdifferentiableWithinAt.mfderiv_within (h : MdifferentiableWithinAt I I' f s x) :
    mfderivWithin I I' f s x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f : _) ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) :=
  by simp only [mfderivWithin, h, dif_pos]
#align mdifferentiable_within_at.mfderiv_within MdifferentiableWithinAt.mfderiv_within

theorem MdifferentiableAt.hasMfderivAt (h : MdifferentiableAt I I' f x) : HasMfderivAt I I' f x (mfderiv I I' f x) := by
  refine' ⟨h.1, _⟩
  simp only [mfderiv, h, dif_pos, mfld_simps]
  exact DifferentiableWithinAt.hasFderivWithinAt h.2
#align mdifferentiable_at.has_mfderiv_at MdifferentiableAt.hasMfderivAt

theorem MdifferentiableAt.mfderiv (h : MdifferentiableAt I I' f x) :
    mfderiv I I' f x = fderivWithin 𝕜 (writtenInExtChartAt I I' x f : _) (range I) ((extChartAt I x) x) := by
  simp only [mfderiv, h, dif_pos]
#align mdifferentiable_at.mfderiv MdifferentiableAt.mfderiv

theorem HasMfderivAt.mfderiv (h : HasMfderivAt I I' f x f') : mfderiv I I' f x = f' :=
  (has_mfderiv_at_unique h h.MdifferentiableAt.HasMfderivAt).symm
#align has_mfderiv_at.mfderiv HasMfderivAt.mfderiv

theorem HasMfderivWithinAt.mfderiv_within (h : HasMfderivWithinAt I I' f s x f') (hxs : UniqueMdiffWithinAt I s x) :
    mfderivWithin I I' f s x = f' := by
  ext
  rw [hxs.eq h h.mdifferentiable_within_at.has_mfderiv_within_at]
#align has_mfderiv_within_at.mfderiv_within HasMfderivWithinAt.mfderiv_within

theorem Mdifferentiable.mfderiv_within (h : MdifferentiableAt I I' f x) (hxs : UniqueMdiffWithinAt I s x) :
    mfderivWithin I I' f s x = mfderiv I I' f x := by
  apply HasMfderivWithinAt.mfderiv_within _ hxs
  exact h.has_mfderiv_at.has_mfderiv_within_at
#align mdifferentiable.mfderiv_within Mdifferentiable.mfderiv_within

theorem mfderiv_within_subset (st : s ⊆ t) (hs : UniqueMdiffWithinAt I s x) (h : MdifferentiableWithinAt I I' f t x) :
    mfderivWithin I I' f s x = mfderivWithin I I' f t x :=
  ((MdifferentiableWithinAt.hasMfderivWithinAt h).mono st).mfderivWithin hs
#align mfderiv_within_subset mfderiv_within_subset

omit Is I's

theorem MdifferentiableWithinAt.mono (hst : s ⊆ t) (h : MdifferentiableWithinAt I I' f t x) :
    MdifferentiableWithinAt I I' f s x :=
  ⟨ContinuousWithinAt.mono h.1 hst,
    DifferentiableWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩
#align mdifferentiable_within_at.mono MdifferentiableWithinAt.mono

theorem mdifferentiable_within_at_univ : MdifferentiableWithinAt I I' f univ x ↔ MdifferentiableAt I I' f x := by
  simp only [MdifferentiableWithinAt, MdifferentiableAt, continuous_within_at_univ, mfld_simps]
#align mdifferentiable_within_at_univ mdifferentiable_within_at_univ

theorem mdifferentiable_within_at_inter (ht : t ∈ 𝓝 x) :
    MdifferentiableWithinAt I I' f (s ∩ t) x ↔ MdifferentiableWithinAt I I' f s x := by
  rw [MdifferentiableWithinAt, MdifferentiableWithinAt, ext_chart_preimage_inter_eq, differentiable_within_at_inter,
    continuous_within_at_inter ht]
  exact ext_chart_preimage_mem_nhds I x ht
#align mdifferentiable_within_at_inter mdifferentiable_within_at_inter

theorem mdifferentiable_within_at_inter' (ht : t ∈ 𝓝[s] x) :
    MdifferentiableWithinAt I I' f (s ∩ t) x ↔ MdifferentiableWithinAt I I' f s x := by
  rw [MdifferentiableWithinAt, MdifferentiableWithinAt, ext_chart_preimage_inter_eq, differentiable_within_at_inter',
    continuous_within_at_inter' ht]
  exact ext_chart_preimage_mem_nhds_within I x ht
#align mdifferentiable_within_at_inter' mdifferentiable_within_at_inter'

theorem MdifferentiableAt.mdifferentiableWithinAt (h : MdifferentiableAt I I' f x) :
    MdifferentiableWithinAt I I' f s x :=
  MdifferentiableWithinAt.mono (subset_univ _) (mdifferentiable_within_at_univ.2 h)
#align mdifferentiable_at.mdifferentiable_within_at MdifferentiableAt.mdifferentiableWithinAt

theorem MdifferentiableWithinAt.mdifferentiableAt (h : MdifferentiableWithinAt I I' f s x) (hs : s ∈ 𝓝 x) :
    MdifferentiableAt I I' f x := by
  have : s = univ ∩ s := by rw [univ_inter]
  rwa [this, mdifferentiable_within_at_inter hs, mdifferentiable_within_at_univ] at h
#align mdifferentiable_within_at.mdifferentiable_at MdifferentiableWithinAt.mdifferentiableAt

theorem MdifferentiableOn.mono (h : MdifferentiableOn I I' f t) (st : s ⊆ t) : MdifferentiableOn I I' f s := fun x hx =>
  (h x (st hx)).mono st
#align mdifferentiable_on.mono MdifferentiableOn.mono

theorem mdifferentiable_on_univ : MdifferentiableOn I I' f univ ↔ Mdifferentiable I I' f := by
  simp only [MdifferentiableOn, mdifferentiable_within_at_univ, mfld_simps]
  rfl
#align mdifferentiable_on_univ mdifferentiable_on_univ

theorem Mdifferentiable.mdifferentiableOn (h : Mdifferentiable I I' f) : MdifferentiableOn I I' f s :=
  (mdifferentiable_on_univ.2 h).mono (subset_univ _)
#align mdifferentiable.mdifferentiable_on Mdifferentiable.mdifferentiableOn

theorem mdifferentiableOnOfLocallyMdifferentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ MdifferentiableOn I I' f (s ∩ u)) : MdifferentiableOn I I' f s := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (mdifferentiable_within_at_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)
#align mdifferentiable_on_of_locally_mdifferentiable_on mdifferentiableOnOfLocallyMdifferentiableOn

include Is I's

@[simp, mfld_simps]
theorem mfderiv_within_univ : mfderivWithin I I' f univ = mfderiv I I' f := by
  ext x : 1
  simp only [mfderivWithin, mfderiv, mfld_simps]
  rw [mdifferentiable_within_at_univ]
#align mfderiv_within_univ mfderiv_within_univ

theorem mfderiv_within_inter (ht : t ∈ 𝓝 x) (hs : UniqueMdiffWithinAt I s x) :
    mfderivWithin I I' f (s ∩ t) x = mfderivWithin I I' f s x := by
  rw [mfderivWithin, mfderivWithin, ext_chart_preimage_inter_eq, mdifferentiable_within_at_inter ht,
    fderiv_within_inter (ext_chart_preimage_mem_nhds I x ht) hs]
#align mfderiv_within_inter mfderiv_within_inter

theorem mdifferentiable_at_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (ChartedSpace.chartAt H x).source)
    (hy : f x' ∈ (ChartedSpace.chartAt H' y).source) :
    MdifferentiableAt I I' f x' ↔
      ContinuousAt f x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (Set.range I) ((extChartAt I x) x') :=
  mdifferentiable_within_at_univ.symm.trans <|
    (mdifferentiable_within_at_iff_of_mem_source hx hy).trans <| by
      rw [continuous_within_at_univ, Set.preimage_univ, Set.univ_inter]
#align mdifferentiable_at_iff_of_mem_source mdifferentiable_at_iff_of_mem_source

omit Is I's

/-! ### Deriving continuity from differentiability on manifolds -/


theorem HasMfderivWithinAt.continuous_within_at (h : HasMfderivWithinAt I I' f s x f') : ContinuousWithinAt f s x :=
  h.1
#align has_mfderiv_within_at.continuous_within_at HasMfderivWithinAt.continuous_within_at

theorem HasMfderivAt.continuous_at (h : HasMfderivAt I I' f x f') : ContinuousAt f x :=
  h.1
#align has_mfderiv_at.continuous_at HasMfderivAt.continuous_at

theorem MdifferentiableWithinAt.continuous_within_at (h : MdifferentiableWithinAt I I' f s x) :
    ContinuousWithinAt f s x :=
  h.1
#align mdifferentiable_within_at.continuous_within_at MdifferentiableWithinAt.continuous_within_at

theorem MdifferentiableAt.continuous_at (h : MdifferentiableAt I I' f x) : ContinuousAt f x :=
  h.1
#align mdifferentiable_at.continuous_at MdifferentiableAt.continuous_at

theorem MdifferentiableOn.continuous_on (h : MdifferentiableOn I I' f s) : ContinuousOn f s := fun x hx =>
  (h x hx).ContinuousWithinAt
#align mdifferentiable_on.continuous_on MdifferentiableOn.continuous_on

theorem Mdifferentiable.continuous (h : Mdifferentiable I I' f) : Continuous f :=
  continuous_iff_continuous_at.2 fun x => (h x).ContinuousAt
#align mdifferentiable.continuous Mdifferentiable.continuous

include Is I's

theorem tangent_map_within_subset {p : TangentBundle I M} (st : s ⊆ t) (hs : UniqueMdiffWithinAt I s p.1)
    (h : MdifferentiableWithinAt I I' f t p.1) : tangentMapWithin I I' f s p = tangentMapWithin I I' f t p := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderiv_within_subset st hs h]
#align tangent_map_within_subset tangent_map_within_subset

theorem tangent_map_within_univ : tangentMapWithin I I' f univ = tangentMap I I' f := by
  ext p : 1
  simp only [tangentMapWithin, tangentMap, mfld_simps]
#align tangent_map_within_univ tangent_map_within_univ

theorem tangent_map_within_eq_tangent_map {p : TangentBundle I M} (hs : UniqueMdiffWithinAt I s p.1)
    (h : MdifferentiableAt I I' f p.1) : tangentMapWithin I I' f s p = tangentMap I I' f p := by
  rw [← mdifferentiable_within_at_univ] at h
  rw [← tangent_map_within_univ]
  exact tangent_map_within_subset (subset_univ _) hs h
#align tangent_map_within_eq_tangent_map tangent_map_within_eq_tangent_map

@[simp, mfld_simps]
theorem tangent_map_within_tangent_bundle_proj {p : TangentBundle I M} :
    TangentBundle.proj I' M' (tangentMapWithin I I' f s p) = f (TangentBundle.proj I M p) :=
  rfl
#align tangent_map_within_tangent_bundle_proj tangent_map_within_tangent_bundle_proj

@[simp, mfld_simps]
theorem tangent_map_within_proj {p : TangentBundle I M} : (tangentMapWithin I I' f s p).1 = f p.1 :=
  rfl
#align tangent_map_within_proj tangent_map_within_proj

@[simp, mfld_simps]
theorem tangent_map_tangent_bundle_proj {p : TangentBundle I M} :
    TangentBundle.proj I' M' (tangentMap I I' f p) = f (TangentBundle.proj I M p) :=
  rfl
#align tangent_map_tangent_bundle_proj tangent_map_tangent_bundle_proj

@[simp, mfld_simps]
theorem tangent_map_proj {p : TangentBundle I M} : (tangentMap I I' f p).1 = f p.1 :=
  rfl
#align tangent_map_proj tangent_map_proj

omit Is I's

/-! ### Congruence lemmas for derivatives on manifolds -/


theorem HasMfderivWithinAt.congrOfEventuallyEq (h : HasMfderivWithinAt I I' f s x f') (h₁ : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : HasMfderivWithinAt I I' f₁ s x f' := by
  refine' ⟨ContinuousWithinAt.congr_of_eventually_eq h.1 h₁ hx, _⟩
  apply HasFderivWithinAt.congrOfEventuallyEq h.2
  · have : (extChartAt I x).symm ⁻¹' { y | f₁ y = f y } ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      ext_chart_preimage_mem_nhds_within I x h₁
    apply Filter.mem_of_superset this fun y => _
    simp (config := { contextual := true }) only [hx, mfld_simps]
    
  · simp only [hx, mfld_simps]
    
#align has_mfderiv_within_at.congr_of_eventually_eq HasMfderivWithinAt.congrOfEventuallyEq

theorem HasMfderivWithinAt.congrMono (h : HasMfderivWithinAt I I' f s x f') (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x)
    (h₁ : t ⊆ s) : HasMfderivWithinAt I I' f₁ t x f' :=
  (h.mono h₁).congr_of_eventually_eq (Filter.mem_inf_of_right ht) hx
#align has_mfderiv_within_at.congr_mono HasMfderivWithinAt.congrMono

theorem HasMfderivAt.congrOfEventuallyEq (h : HasMfderivAt I I' f x f') (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasMfderivAt I I' f₁ x f' := by
  rw [← has_mfderiv_within_at_univ] at h⊢
  apply h.congr_of_eventually_eq _ (mem_of_mem_nhds h₁ : _)
  rwa [nhds_within_univ]
#align has_mfderiv_at.congr_of_eventually_eq HasMfderivAt.congrOfEventuallyEq

include Is I's

theorem MdifferentiableWithinAt.congrOfEventuallyEq (h : MdifferentiableWithinAt I I' f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : MdifferentiableWithinAt I I' f₁ s x :=
  (h.HasMfderivWithinAt.congr_of_eventually_eq h₁ hx).MdifferentiableWithinAt
#align mdifferentiable_within_at.congr_of_eventually_eq MdifferentiableWithinAt.congrOfEventuallyEq

variable (I I')

theorem Filter.EventuallyEq.mdifferentiable_within_at_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    MdifferentiableWithinAt I I' f s x ↔ MdifferentiableWithinAt I I' f₁ s x := by
  constructor
  · intro h
    apply h.congr_of_eventually_eq h₁ hx
    
  · intro h
    apply h.congr_of_eventually_eq _ hx.symm
    apply h₁.mono
    intro y
    apply Eq.symm
    
#align filter.eventually_eq.mdifferentiable_within_at_iff Filter.EventuallyEq.mdifferentiable_within_at_iff

variable {I I'}

theorem MdifferentiableWithinAt.congrMono (h : MdifferentiableWithinAt I I' f s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : MdifferentiableWithinAt I I' f₁ t x :=
  (HasMfderivWithinAt.congrMono h.HasMfderivWithinAt ht hx h₁).MdifferentiableWithinAt
#align mdifferentiable_within_at.congr_mono MdifferentiableWithinAt.congrMono

theorem MdifferentiableWithinAt.congr (h : MdifferentiableWithinAt I I' f s x) (ht : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : MdifferentiableWithinAt I I' f₁ s x :=
  (HasMfderivWithinAt.congrMono h.HasMfderivWithinAt ht hx (Subset.refl _)).MdifferentiableWithinAt
#align mdifferentiable_within_at.congr MdifferentiableWithinAt.congr

theorem MdifferentiableOn.congrMono (h : MdifferentiableOn I I' f s) (h' : ∀ x ∈ t, f₁ x = f x) (h₁ : t ⊆ s) :
    MdifferentiableOn I I' f₁ t := fun x hx => (h x (h₁ hx)).congr_mono h' (h' x hx) h₁
#align mdifferentiable_on.congr_mono MdifferentiableOn.congrMono

theorem MdifferentiableAt.congrOfEventuallyEq (h : MdifferentiableAt I I' f x) (hL : f₁ =ᶠ[𝓝 x] f) :
    MdifferentiableAt I I' f₁ x :=
  (h.HasMfderivAt.congr_of_eventually_eq hL).MdifferentiableAt
#align mdifferentiable_at.congr_of_eventually_eq MdifferentiableAt.congrOfEventuallyEq

theorem MdifferentiableWithinAt.mfderiv_within_congr_mono (h : MdifferentiableWithinAt I I' f s x)
    (hs : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : UniqueMdiffWithinAt I t x) (h₁ : t ⊆ s) :
    mfderivWithin I I' f₁ t x = (mfderivWithin I I' f s x : _) :=
  (HasMfderivWithinAt.congrMono h.HasMfderivWithinAt hs hx h₁).mfderivWithin hxt
#align mdifferentiable_within_at.mfderiv_within_congr_mono MdifferentiableWithinAt.mfderiv_within_congr_mono

theorem Filter.EventuallyEq.mfderiv_within_eq (hs : UniqueMdiffWithinAt I s x) (hL : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : mfderivWithin I I' f₁ s x = (mfderivWithin I I' f s x : _) := by
  by_cases h:MdifferentiableWithinAt I I' f s x
  · exact (h.has_mfderiv_within_at.congr_of_eventually_eq hL hx).mfderivWithin hs
    
  · unfold mfderivWithin
    rw [dif_neg h, dif_neg]
    rwa [← hL.mdifferentiable_within_at_iff I I' hx]
    
#align filter.eventually_eq.mfderiv_within_eq Filter.EventuallyEq.mfderiv_within_eq

theorem mfderiv_within_congr (hs : UniqueMdiffWithinAt I s x) (hL : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) :
    mfderivWithin I I' f₁ s x = (mfderivWithin I I' f s x : _) :=
  Filter.EventuallyEq.mfderiv_within_eq hs (Filter.eventually_eq_of_mem self_mem_nhds_within hL) hx
#align mfderiv_within_congr mfderiv_within_congr

theorem tangent_map_within_congr (h : ∀ x ∈ s, f x = f₁ x) (p : TangentBundle I M) (hp : p.1 ∈ s)
    (hs : UniqueMdiffWithinAt I s p.1) : tangentMapWithin I I' f s p = tangentMapWithin I I' f₁ s p := by
  simp only [tangentMapWithin, h p.fst hp, true_and_iff, eq_self_iff_true, heq_iff_eq, Sigma.mk.inj_iff]
  congr 1
  exact mfderiv_within_congr hs h (h _ hp)
#align tangent_map_within_congr tangent_map_within_congr

theorem Filter.EventuallyEq.mfderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) : mfderiv I I' f₁ x = (mfderiv I I' f x : _) := by
  have A : f₁ x = f x := (mem_of_mem_nhds hL : _)
  rw [← mfderiv_within_univ, ← mfderiv_within_univ]
  rw [← nhds_within_univ] at hL
  exact hL.mfderiv_within_eq (uniqueMdiffWithinAtUniv I) A
#align filter.eventually_eq.mfderiv_eq Filter.EventuallyEq.mfderiv_eq

/-! ### Composition lemmas -/


omit Is I's

theorem written_in_ext_chart_comp (h : ContinuousWithinAt f s x) :
    { y |
        writtenInExtChartAt I I'' x (g ∘ f) y =
          (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f) y } ∈
      𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
  by
  apply
    @Filter.mem_of_superset _ _ (f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source) _
      (ext_chart_preimage_mem_nhds_within I x (h.preimage_mem_nhds_within (ext_chart_at_source_mem_nhds _ _)))
  mfld_set_tac
#align written_in_ext_chart_comp written_in_ext_chart_comp

variable (x)

include Is I's I''s

theorem HasMfderivWithinAt.comp (hg : HasMfderivWithinAt I' I'' g u (f x) g') (hf : HasMfderivWithinAt I I' f s x f')
    (hst : s ⊆ f ⁻¹' u) : HasMfderivWithinAt I I'' (g ∘ f) s x (g'.comp f') := by
  refine' ⟨ContinuousWithinAt.comp hg.1 hf.1 hst, _⟩
  have A :
    HasFderivWithinAt (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f)
      (ContinuousLinearMap.comp g' f' : E →L[𝕜] E'') ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x) :=
    by
    have :
      (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' (f x)).source) ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      ext_chart_preimage_mem_nhds_within I x (hf.1.preimage_mem_nhds_within (ext_chart_at_source_mem_nhds _ _))
    unfold HasMfderivWithinAt at *
    rw [← has_fderiv_within_at_inter' this, ← ext_chart_preimage_inter_eq] at hf⊢
    have : writtenInExtChartAt I I' x f ((extChartAt I x) x) = (extChartAt I' (f x)) (f x) := by simp only [mfld_simps]
    rw [← this] at hg
    apply HasFderivWithinAt.comp ((extChartAt I x) x) hg.2 hf.2 _
    intro y hy
    simp only [mfld_simps] at hy
    have : f (((chart_at H x).symm : H → M) (I.symm y)) ∈ u := hst hy.1.1
    simp only [hy, this, mfld_simps]
  apply A.congr_of_eventually_eq (written_in_ext_chart_comp hf.1)
  simp only [mfld_simps]
#align has_mfderiv_within_at.comp HasMfderivWithinAt.comp

/-- The chain rule. -/
theorem HasMfderivAt.comp (hg : HasMfderivAt I' I'' g (f x) g') (hf : HasMfderivAt I I' f x f') :
    HasMfderivAt I I'' (g ∘ f) x (g'.comp f') := by
  rw [← has_mfderiv_within_at_univ] at *
  exact HasMfderivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ
#align has_mfderiv_at.comp HasMfderivAt.comp

theorem HasMfderivAt.compHasMfderivWithinAt (hg : HasMfderivAt I' I'' g (f x) g')
    (hf : HasMfderivWithinAt I I' f s x f') : HasMfderivWithinAt I I'' (g ∘ f) s x (g'.comp f') := by
  rw [← has_mfderiv_within_at_univ] at *
  exact HasMfderivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ
#align has_mfderiv_at.comp_has_mfderiv_within_at HasMfderivAt.compHasMfderivWithinAt

theorem MdifferentiableWithinAt.comp (hg : MdifferentiableWithinAt I' I'' g u (f x))
    (hf : MdifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) : MdifferentiableWithinAt I I'' (g ∘ f) s x := by
  rcases hf.2 with ⟨f', hf'⟩
  have F : HasMfderivWithinAt I I' f s x f' := ⟨hf.1, hf'⟩
  rcases hg.2 with ⟨g', hg'⟩
  have G : HasMfderivWithinAt I' I'' g u (f x) g' := ⟨hg.1, hg'⟩
  exact (HasMfderivWithinAt.comp x G F h).MdifferentiableWithinAt
#align mdifferentiable_within_at.comp MdifferentiableWithinAt.comp

theorem MdifferentiableAt.comp (hg : MdifferentiableAt I' I'' g (f x)) (hf : MdifferentiableAt I I' f x) :
    MdifferentiableAt I I'' (g ∘ f) x :=
  (hg.HasMfderivAt.comp x hf.HasMfderivAt).MdifferentiableAt
#align mdifferentiable_at.comp MdifferentiableAt.comp

theorem mfderiv_within_comp (hg : MdifferentiableWithinAt I' I'' g u (f x)) (hf : MdifferentiableWithinAt I I' f s x)
    (h : s ⊆ f ⁻¹' u) (hxs : UniqueMdiffWithinAt I s x) :
    mfderivWithin I I'' (g ∘ f) s x = (mfderivWithin I' I'' g u (f x)).comp (mfderivWithin I I' f s x) := by
  apply HasMfderivWithinAt.mfderiv_within _ hxs
  exact HasMfderivWithinAt.comp x hg.has_mfderiv_within_at hf.has_mfderiv_within_at h
#align mfderiv_within_comp mfderiv_within_comp

theorem mfderiv_comp (hg : MdifferentiableAt I' I'' g (f x)) (hf : MdifferentiableAt I I' f x) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) := by
  apply HasMfderivAt.mfderiv
  exact HasMfderivAt.comp x hg.has_mfderiv_at hf.has_mfderiv_at
#align mfderiv_comp mfderiv_comp

theorem MdifferentiableOn.comp (hg : MdifferentiableOn I' I'' g u) (hf : MdifferentiableOn I I' f s)
    (st : s ⊆ f ⁻¹' u) : MdifferentiableOn I I'' (g ∘ f) s := fun x hx =>
  MdifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st
#align mdifferentiable_on.comp MdifferentiableOn.comp

theorem Mdifferentiable.comp (hg : Mdifferentiable I' I'' g) (hf : Mdifferentiable I I' f) :
    Mdifferentiable I I'' (g ∘ f) := fun x => MdifferentiableAt.comp x (hg (f x)) (hf x)
#align mdifferentiable.comp Mdifferentiable.comp

theorem tangent_map_within_comp_at (p : TangentBundle I M) (hg : MdifferentiableWithinAt I' I'' g u (f p.1))
    (hf : MdifferentiableWithinAt I I' f s p.1) (h : s ⊆ f ⁻¹' u) (hps : UniqueMdiffWithinAt I s p.1) :
    tangentMapWithin I I'' (g ∘ f) s p = tangentMapWithin I' I'' g u (tangentMapWithin I I' f s p) := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderiv_within_comp p.1 hg hf h hps]
  rfl
#align tangent_map_within_comp_at tangent_map_within_comp_at

theorem tangent_map_comp_at (p : TangentBundle I M) (hg : MdifferentiableAt I' I'' g (f p.1))
    (hf : MdifferentiableAt I I' f p.1) : tangentMap I I'' (g ∘ f) p = tangentMap I' I'' g (tangentMap I I' f p) := by
  simp only [tangentMap, mfld_simps]
  rw [mfderiv_comp p.1 hg hf]
  rfl
#align tangent_map_comp_at tangent_map_comp_at

theorem tangent_map_comp (hg : Mdifferentiable I' I'' g) (hf : Mdifferentiable I I' f) :
    tangentMap I I'' (g ∘ f) = tangentMap I' I'' g ∘ tangentMap I I' f := by
  ext p : 1
  exact tangent_map_comp_at _ (hg _) (hf _)
#align tangent_map_comp tangent_map_comp

end DerivativesProperties

section MfderivFderiv

/-!
### Relations between vector space derivative and manifold derivative

The manifold derivative `mfderiv`, when considered on the model vector space with its trivial
manifold structure, coincides with the usual Frechet derivative `fderiv`. In this section, we prove
this and related statements.
-/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {f : E → E'} {s : Set E} {x : E}

theorem unique_mdiff_within_at_iff_unique_diff_within_at : UniqueMdiffWithinAt 𝓘(𝕜, E) s x ↔ UniqueDiffWithinAt 𝕜 s x :=
  by simp only [UniqueMdiffWithinAt, mfld_simps]
#align unique_mdiff_within_at_iff_unique_diff_within_at unique_mdiff_within_at_iff_unique_diff_within_at

alias unique_mdiff_within_at_iff_unique_diff_within_at ↔
  UniqueMdiffWithinAt.uniqueDiffWithinAt UniqueDiffWithinAt.uniqueMdiffWithinAt

theorem unique_mdiff_on_iff_unique_diff_on : UniqueMdiffOn 𝓘(𝕜, E) s ↔ UniqueDiffOn 𝕜 s := by
  simp [UniqueMdiffOn, UniqueDiffOn, unique_mdiff_within_at_iff_unique_diff_within_at]
#align unique_mdiff_on_iff_unique_diff_on unique_mdiff_on_iff_unique_diff_on

alias unique_mdiff_on_iff_unique_diff_on ↔ UniqueMdiffOn.uniqueDiffOn UniqueDiffOn.uniqueMdiffOn

@[simp, mfld_simps]
theorem written_in_ext_chart_model_space : writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E') x f = f :=
  rfl
#align written_in_ext_chart_model_space written_in_ext_chart_model_space

theorem has_mfderiv_within_at_iff_has_fderiv_within_at {f'} :
    HasMfderivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f' ↔ HasFderivWithinAt f f' s x := by
  simpa only [HasMfderivWithinAt, and_iff_right_iff_imp, mfld_simps] using HasFderivWithinAt.continuous_within_at
#align has_mfderiv_within_at_iff_has_fderiv_within_at has_mfderiv_within_at_iff_has_fderiv_within_at

alias has_mfderiv_within_at_iff_has_fderiv_within_at ↔
  HasMfderivWithinAt.hasFderivWithinAt HasFderivWithinAt.hasMfderivWithinAt

theorem has_mfderiv_at_iff_has_fderiv_at {f'} : HasMfderivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f' ↔ HasFderivAt f f' x := by
  rw [← has_mfderiv_within_at_univ, has_mfderiv_within_at_iff_has_fderiv_within_at, has_fderiv_within_at_univ]
#align has_mfderiv_at_iff_has_fderiv_at has_mfderiv_at_iff_has_fderiv_at

alias has_mfderiv_at_iff_has_fderiv_at ↔ HasMfderivAt.hasFderivAt HasFderivAt.hasMfderivAt

/-- For maps between vector spaces, `mdifferentiable_within_at` and `fdifferentiable_within_at`
coincide -/
theorem mdifferentiable_within_at_iff_differentiable_within_at :
    MdifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [MdifferentiableWithinAt, mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.ContinuousWithinAt, H⟩⟩
#align mdifferentiable_within_at_iff_differentiable_within_at mdifferentiable_within_at_iff_differentiable_within_at

alias mdifferentiable_within_at_iff_differentiable_within_at ↔
  MdifferentiableWithinAt.differentiableWithinAt DifferentiableWithinAt.mdifferentiableWithinAt

/-- For maps between vector spaces, `mdifferentiable_at` and `differentiable_at` coincide -/
theorem mdifferentiable_at_iff_differentiable_at : MdifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x ↔ DifferentiableAt 𝕜 f x := by
  simp only [MdifferentiableAt, differentiable_within_at_univ, mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.ContinuousAt, H⟩⟩
#align mdifferentiable_at_iff_differentiable_at mdifferentiable_at_iff_differentiable_at

alias mdifferentiable_at_iff_differentiable_at ↔ MdifferentiableAt.differentiableAt DifferentiableAt.mdifferentiableAt

/-- For maps between vector spaces, `mdifferentiable_on` and `differentiable_on` coincide -/
theorem mdifferentiable_on_iff_differentiable_on : MdifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s ↔ DifferentiableOn 𝕜 f s := by
  simp only [MdifferentiableOn, DifferentiableOn, mdifferentiable_within_at_iff_differentiable_within_at]
#align mdifferentiable_on_iff_differentiable_on mdifferentiable_on_iff_differentiable_on

alias mdifferentiable_on_iff_differentiable_on ↔ MdifferentiableOn.differentiableOn DifferentiableOn.mdifferentiableOn

/-- For maps between vector spaces, `mdifferentiable` and `differentiable` coincide -/
theorem mdifferentiable_iff_differentiable : Mdifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f ↔ Differentiable 𝕜 f := by
  simp only [Mdifferentiable, Differentiable, mdifferentiable_at_iff_differentiable_at]
#align mdifferentiable_iff_differentiable mdifferentiable_iff_differentiable

alias mdifferentiable_iff_differentiable ↔ Mdifferentiable.differentiable Differentiable.mdifferentiable

/-- For maps between vector spaces, `mfderiv_within` and `fderiv_within` coincide -/
@[simp]
theorem mfderiv_within_eq_fderiv_within : mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = fderivWithin 𝕜 f s x := by
  by_cases h:MdifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x
  · simp only [mfderivWithin, h, dif_pos, mfld_simps]
    
  · simp only [mfderivWithin, h, dif_neg, not_false_iff]
    rw [mdifferentiable_within_at_iff_differentiable_within_at] at h
    exact (fderiv_within_zero_of_not_differentiable_within_at h).symm
    
#align mfderiv_within_eq_fderiv_within mfderiv_within_eq_fderiv_within

/-- For maps between vector spaces, `mfderiv` and `fderiv` coincide -/
@[simp]
theorem mfderiv_eq_fderiv : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = fderiv 𝕜 f x := by
  rw [← mfderiv_within_univ, ← fderiv_within_univ]
  exact mfderiv_within_eq_fderiv_within
#align mfderiv_eq_fderiv mfderiv_eq_fderiv

end MfderivFderiv

section SpecificFunctions

/-! ### Differentiability of specific functions -/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _}
  [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']

namespace ContinuousLinearMap

variable (f : E →L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMfderivWithinAt : HasMfderivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f :=
  f.HasFderivWithinAt.HasMfderivWithinAt
#align continuous_linear_map.has_mfderiv_within_at ContinuousLinearMap.hasMfderivWithinAt

protected theorem hasMfderivAt : HasMfderivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f :=
  f.HasFderivAt.HasMfderivAt
#align continuous_linear_map.has_mfderiv_at ContinuousLinearMap.hasMfderivAt

protected theorem mdifferentiableWithinAt : MdifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
  f.DifferentiableWithinAt.MdifferentiableWithinAt
#align continuous_linear_map.mdifferentiable_within_at ContinuousLinearMap.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MdifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  f.DifferentiableOn.MdifferentiableOn
#align continuous_linear_map.mdifferentiable_on ContinuousLinearMap.mdifferentiableOn

protected theorem mdifferentiableAt : MdifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  f.DifferentiableAt.MdifferentiableAt
#align continuous_linear_map.mdifferentiable_at ContinuousLinearMap.mdifferentiableAt

protected theorem mdifferentiable : Mdifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  f.Differentiable.Mdifferentiable
#align continuous_linear_map.mdifferentiable ContinuousLinearMap.mdifferentiable

theorem mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = f :=
  f.HasMfderivAt.mfderiv
#align continuous_linear_map.mfderiv_eq ContinuousLinearMap.mfderiv_eq

theorem mfderiv_within_eq (hs : UniqueMdiffWithinAt 𝓘(𝕜, E) s x) : mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = f :=
  f.HasMfderivWithinAt.mfderivWithin hs
#align continuous_linear_map.mfderiv_within_eq ContinuousLinearMap.mfderiv_within_eq

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMfderivWithinAt : HasMfderivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x (f : E →L[𝕜] E') :=
  f.HasFderivWithinAt.HasMfderivWithinAt
#align continuous_linear_equiv.has_mfderiv_within_at ContinuousLinearEquiv.hasMfderivWithinAt

protected theorem hasMfderivAt : HasMfderivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x (f : E →L[𝕜] E') :=
  f.HasFderivAt.HasMfderivAt
#align continuous_linear_equiv.has_mfderiv_at ContinuousLinearEquiv.hasMfderivAt

protected theorem mdifferentiableWithinAt : MdifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
  f.DifferentiableWithinAt.MdifferentiableWithinAt
#align continuous_linear_equiv.mdifferentiable_within_at ContinuousLinearEquiv.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MdifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  f.DifferentiableOn.MdifferentiableOn
#align continuous_linear_equiv.mdifferentiable_on ContinuousLinearEquiv.mdifferentiableOn

protected theorem mdifferentiableAt : MdifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  f.DifferentiableAt.MdifferentiableAt
#align continuous_linear_equiv.mdifferentiable_at ContinuousLinearEquiv.mdifferentiableAt

protected theorem mdifferentiable : Mdifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  f.Differentiable.Mdifferentiable
#align continuous_linear_equiv.mdifferentiable ContinuousLinearEquiv.mdifferentiable

theorem mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = (f : E →L[𝕜] E') :=
  f.HasMfderivAt.mfderiv
#align continuous_linear_equiv.mfderiv_eq ContinuousLinearEquiv.mfderiv_eq

theorem mfderiv_within_eq (hs : UniqueMdiffWithinAt 𝓘(𝕜, E) s x) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = (f : E →L[𝕜] E') :=
  f.HasMfderivWithinAt.mfderivWithin hs
#align continuous_linear_equiv.mfderiv_within_eq ContinuousLinearEquiv.mfderiv_within_eq

end ContinuousLinearEquiv

variable {s : Set M} {x : M}

section id

/-! #### Identity -/


theorem hasMfderivAtId (x : M) : HasMfderivAt I I (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) := by
  refine' ⟨continuous_id.continuous_at, _⟩
  have : ∀ᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = id y := by
    apply Filter.mem_of_superset (ext_chart_at_target_mem_nhds_within I x)
    mfld_set_tac
  apply HasFderivWithinAt.congrOfEventuallyEq (hasFderivWithinAtId _ _) this
  simp only [mfld_simps]
#align has_mfderiv_at_id hasMfderivAtId

theorem hasMfderivWithinAtId (s : Set M) (x : M) :
    HasMfderivWithinAt I I (@id M) s x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) :=
  (hasMfderivAtId I x).HasMfderivWithinAt
#align has_mfderiv_within_at_id hasMfderivWithinAtId

theorem mdifferentiableAtId : MdifferentiableAt I I (@id M) x :=
  (hasMfderivAtId I x).MdifferentiableAt
#align mdifferentiable_at_id mdifferentiableAtId

theorem mdifferentiableWithinAtId : MdifferentiableWithinAt I I (@id M) s x :=
  (mdifferentiableAtId I).MdifferentiableWithinAt
#align mdifferentiable_within_at_id mdifferentiableWithinAtId

theorem mdifferentiableId : Mdifferentiable I I (@id M) := fun x => mdifferentiableAtId I
#align mdifferentiable_id mdifferentiableId

theorem mdifferentiableOnId : MdifferentiableOn I I (@id M) s :=
  (mdifferentiableId I).MdifferentiableOn
#align mdifferentiable_on_id mdifferentiableOnId

@[simp, mfld_simps]
theorem mfderiv_id : mfderiv I I (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
  HasMfderivAt.mfderiv (hasMfderivAtId I x)
#align mfderiv_id mfderiv_id

theorem mfderiv_within_id (hxs : UniqueMdiffWithinAt I s x) :
    mfderivWithin I I (@id M) s x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  rw [Mdifferentiable.mfderiv_within (mdifferentiableAtId I) hxs]
  exact mfderiv_id I
#align mfderiv_within_id mfderiv_within_id

@[simp, mfld_simps]
theorem tangent_map_id : tangentMap I I (id : M → M) = id := by
  ext1 ⟨x, v⟩
  simp [tangentMap]
#align tangent_map_id tangent_map_id

theorem tangent_map_within_id {p : TangentBundle I M} (hs : UniqueMdiffWithinAt I s (TangentBundle.proj I M p)) :
    tangentMapWithin I I (id : M → M) s p = p := by
  simp only [tangentMapWithin, id.def]
  rw [mfderiv_within_id]
  · rcases p with ⟨⟩
    rfl
    
  · exact hs
    
#align tangent_map_within_id tangent_map_within_id

end id

section Const

/-! #### Constants -/


variable {c : M'}

theorem hasMfderivAtConst (c : M') (x : M) :
    HasMfderivAt I I' (fun y : M => c) x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) := by
  refine' ⟨continuous_const.continuous_at, _⟩
  simp only [writtenInExtChartAt, (· ∘ ·), hasFderivWithinAtConst]
#align has_mfderiv_at_const hasMfderivAtConst

theorem hasMfderivWithinAtConst (c : M') (s : Set M) (x : M) :
    HasMfderivWithinAt I I' (fun y : M => c) s x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  (hasMfderivAtConst I I' c x).HasMfderivWithinAt
#align has_mfderiv_within_at_const hasMfderivWithinAtConst

theorem mdifferentiableAtConst : MdifferentiableAt I I' (fun y : M => c) x :=
  (hasMfderivAtConst I I' c x).MdifferentiableAt
#align mdifferentiable_at_const mdifferentiableAtConst

theorem mdifferentiableWithinAtConst : MdifferentiableWithinAt I I' (fun y : M => c) s x :=
  (mdifferentiableAtConst I I').MdifferentiableWithinAt
#align mdifferentiable_within_at_const mdifferentiableWithinAtConst

theorem mdifferentiableConst : Mdifferentiable I I' fun y : M => c := fun x => mdifferentiableAtConst I I'
#align mdifferentiable_const mdifferentiableConst

theorem mdifferentiableOnConst : MdifferentiableOn I I' (fun y : M => c) s :=
  (mdifferentiableConst I I').MdifferentiableOn
#align mdifferentiable_on_const mdifferentiableOnConst

@[simp, mfld_simps]
theorem mfderiv_const : mfderiv I I' (fun y : M => c) x = (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  HasMfderivAt.mfderiv (hasMfderivAtConst I I' c x)
#align mfderiv_const mfderiv_const

theorem mfderiv_within_const (hxs : UniqueMdiffWithinAt I s x) :
    mfderivWithin I I' (fun y : M => c) s x = (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  (hasMfderivWithinAtConst _ _ _ _ _).mfderivWithin hxs
#align mfderiv_within_const mfderiv_within_const

end Const

section Arithmetic

/-! #### Arithmetic

Note that in the in `has_mfderiv_at` lemmas there is an abuse of the defeq between `E'` and
`tangent_space 𝓘(𝕜, E') (f z)` (similarly for `g',F',p',q'`). In general this defeq is not
canonical, but in this case (the tangent space of a vector space) it is canonical.
 -/


variable {z : M} {F' : Type _} [NormedCommRing F'] [NormedAlgebra 𝕜 F'] {f g : M → E'} {p q : M → F'}
  {f' g' : TangentSpace I z →L[𝕜] E'} {p' q' : TangentSpace I z →L[𝕜] F'}

theorem HasMfderivAt.add (hf : HasMfderivAt I 𝓘(𝕜, E') f z f') (hg : HasMfderivAt I 𝓘(𝕜, E') g z g') :
    HasMfderivAt I 𝓘(𝕜, E') (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩
#align has_mfderiv_at.add HasMfderivAt.add

theorem MdifferentiableAt.add (hf : MdifferentiableAt I 𝓘(𝕜, E') f z) (hg : MdifferentiableAt I 𝓘(𝕜, E') g z) :
    MdifferentiableAt I 𝓘(𝕜, E') (f + g) z :=
  (hf.HasMfderivAt.add I hg.HasMfderivAt).MdifferentiableAt
#align mdifferentiable_at.add MdifferentiableAt.add

theorem Mdifferentiable.add (hf : Mdifferentiable I 𝓘(𝕜, E') f) (hg : Mdifferentiable I 𝓘(𝕜, E') g) :
    Mdifferentiable I 𝓘(𝕜, E') (f + g) := fun x => (hf x).add I (hg x)
#align mdifferentiable.add Mdifferentiable.add

theorem HasMfderivAt.mul (hp : HasMfderivAt I 𝓘(𝕜, F') p z p') (hq : HasMfderivAt I 𝓘(𝕜, F') q z q') :
    HasMfderivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + q z • p' : E →L[𝕜] F') :=
  ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using hp.2.mul hq.2⟩
#align has_mfderiv_at.mul HasMfderivAt.mul

theorem MdifferentiableAt.mul (hp : MdifferentiableAt I 𝓘(𝕜, F') p z) (hq : MdifferentiableAt I 𝓘(𝕜, F') q z) :
    MdifferentiableAt I 𝓘(𝕜, F') (p * q) z :=
  (hp.HasMfderivAt.mul I hq.HasMfderivAt).MdifferentiableAt
#align mdifferentiable_at.mul MdifferentiableAt.mul

theorem Mdifferentiable.mul {f g : M → F'} (hf : Mdifferentiable I 𝓘(𝕜, F') f) (hg : Mdifferentiable I 𝓘(𝕜, F') g) :
    Mdifferentiable I 𝓘(𝕜, F') (f * g) := fun x => (hf x).mul I (hg x)
#align mdifferentiable.mul Mdifferentiable.mul

theorem HasMfderivAt.constSmul (hf : HasMfderivAt I 𝓘(𝕜, E') f z f') (s : 𝕜) :
    HasMfderivAt I 𝓘(𝕜, E') (s • f) z (s • f') :=
  ⟨hf.1.const_smul s, hf.2.const_smul s⟩
#align has_mfderiv_at.const_smul HasMfderivAt.constSmul

theorem MdifferentiableAt.constSmul (hf : MdifferentiableAt I 𝓘(𝕜, E') f z) (s : 𝕜) :
    MdifferentiableAt I 𝓘(𝕜, E') (s • f) z :=
  (hf.HasMfderivAt.const_smul I s).MdifferentiableAt
#align mdifferentiable_at.const_smul MdifferentiableAt.constSmul

theorem Mdifferentiable.constSmul {f : M → E'} (s : 𝕜) (hf : Mdifferentiable I 𝓘(𝕜, E') f) :
    Mdifferentiable I 𝓘(𝕜, E') (s • f) := fun x => (hf x).const_smul I s
#align mdifferentiable.const_smul Mdifferentiable.constSmul

theorem HasMfderivAt.neg (hf : HasMfderivAt I 𝓘(𝕜, E') f z f') : HasMfderivAt I 𝓘(𝕜, E') (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩
#align has_mfderiv_at.neg HasMfderivAt.neg

theorem MdifferentiableAt.neg (hf : MdifferentiableAt I 𝓘(𝕜, E') f z) : MdifferentiableAt I 𝓘(𝕜, E') (-f) z :=
  (hf.HasMfderivAt.neg I).MdifferentiableAt
#align mdifferentiable_at.neg MdifferentiableAt.neg

theorem Mdifferentiable.neg {f : M → E'} (hf : Mdifferentiable I 𝓘(𝕜, E') f) : Mdifferentiable I 𝓘(𝕜, E') (-f) :=
  fun x => (hf x).neg I
#align mdifferentiable.neg Mdifferentiable.neg

theorem HasMfderivAt.sub (hf : HasMfderivAt I 𝓘(𝕜, E') f z f') (hg : HasMfderivAt I 𝓘(𝕜, E') g z g') :
    HasMfderivAt I 𝓘(𝕜, E') (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
#align has_mfderiv_at.sub HasMfderivAt.sub

theorem MdifferentiableAt.sub (hf : MdifferentiableAt I 𝓘(𝕜, E') f z) (hg : MdifferentiableAt I 𝓘(𝕜, E') g z) :
    MdifferentiableAt I 𝓘(𝕜, E') (f - g) z :=
  (hf.HasMfderivAt.sub I hg.HasMfderivAt).MdifferentiableAt
#align mdifferentiable_at.sub MdifferentiableAt.sub

theorem Mdifferentiable.sub {f : M → E'} (hf : Mdifferentiable I 𝓘(𝕜, E') f) (hg : Mdifferentiable I 𝓘(𝕜, E') g) :
    Mdifferentiable I 𝓘(𝕜, E') (f - g) := fun x => (hf x).sub I (hg x)
#align mdifferentiable.sub Mdifferentiable.sub

end Arithmetic

namespace ModelWithCorners

/-! #### Model with corners -/


protected theorem hasMfderivAt {x} : HasMfderivAt I 𝓘(𝕜, E) I x (ContinuousLinearMap.id _ _) :=
  ⟨I.ContinuousAt, (hasFderivWithinAtId _ _).congr' I.RightInvOn (mem_range_self _)⟩
#align model_with_corners.has_mfderiv_at ModelWithCorners.hasMfderivAt

protected theorem hasMfderivWithinAt {s x} : HasMfderivWithinAt I 𝓘(𝕜, E) I s x (ContinuousLinearMap.id _ _) :=
  I.HasMfderivAt.HasMfderivWithinAt
#align model_with_corners.has_mfderiv_within_at ModelWithCorners.hasMfderivWithinAt

protected theorem mdifferentiableWithinAt {s x} : MdifferentiableWithinAt I 𝓘(𝕜, E) I s x :=
  I.HasMfderivWithinAt.MdifferentiableWithinAt
#align model_with_corners.mdifferentiable_within_at ModelWithCorners.mdifferentiableWithinAt

protected theorem mdifferentiableAt {x} : MdifferentiableAt I 𝓘(𝕜, E) I x :=
  I.HasMfderivAt.MdifferentiableAt
#align model_with_corners.mdifferentiable_at ModelWithCorners.mdifferentiableAt

protected theorem mdifferentiableOn {s} : MdifferentiableOn I 𝓘(𝕜, E) I s := fun x hx => I.MdifferentiableWithinAt
#align model_with_corners.mdifferentiable_on ModelWithCorners.mdifferentiableOn

protected theorem mdifferentiable : Mdifferentiable I 𝓘(𝕜, E) I := fun x => I.MdifferentiableAt
#align model_with_corners.mdifferentiable ModelWithCorners.mdifferentiable

theorem hasMfderivWithinAtSymm {x} (hx : x ∈ range I) :
    HasMfderivWithinAt 𝓘(𝕜, E) I I.symm (range I) x (ContinuousLinearMap.id _ _) :=
  ⟨I.continuous_within_at_symm, (hasFderivWithinAtId _ _).congr' (fun y hy => I.RightInvOn hy.1) ⟨hx, mem_range_self _⟩⟩
#align model_with_corners.has_mfderiv_within_at_symm ModelWithCorners.hasMfderivWithinAtSymm

theorem mdifferentiableOnSymm : MdifferentiableOn 𝓘(𝕜, E) I I.symm (range I) := fun x hx =>
  (I.hasMfderivWithinAtSymm hx).MdifferentiableWithinAt
#align model_with_corners.mdifferentiable_on_symm ModelWithCorners.mdifferentiableOnSymm

end ModelWithCorners

section Charts

variable {e : LocalHomeomorph M H}

theorem mdifferentiableAtAtlas (h : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) : MdifferentiableAt I I e x := by
  refine' ⟨(e.continuous_on x hx).ContinuousAt (IsOpen.mem_nhds e.open_source hx), _⟩
  have mem : I ((chart_at H x : M → H) x) ∈ I.symm ⁻¹' ((chart_at H x).symm ≫ₕ e).source ∩ range I := by
    simp only [hx, mfld_simps]
  have : (chart_at H x).symm.trans e ∈ contDiffGroupoid ∞ I := HasGroupoid.compatible _ (chart_mem_atlas H x) h
  have A :
    ContDiffOn 𝕜 ∞ (I ∘ (chart_at H x).symm.trans e ∘ I.symm)
      (I.symm ⁻¹' ((chart_at H x).symm.trans e).source ∩ range I) :=
    this.1
  have B := A.differentiable_on le_top (I ((chart_at H x : M → H) x)) mem
  simp only [mfld_simps] at B
  rw [inter_comm, differentiable_within_at_inter] at B
  · simpa only [mfld_simps]
    
  · apply IsOpen.mem_nhds ((LocalHomeomorph.open_source _).Preimage I.continuous_symm) mem.1
    
#align mdifferentiable_at_atlas mdifferentiableAtAtlas

theorem mdifferentiableOnAtlas (h : e ∈ atlas H M) : MdifferentiableOn I I e e.source := fun x hx =>
  (mdifferentiableAtAtlas I h hx).MdifferentiableWithinAt
#align mdifferentiable_on_atlas mdifferentiableOnAtlas

theorem mdifferentiableAtAtlasSymm (h : e ∈ atlas H M) {x : H} (hx : x ∈ e.target) : MdifferentiableAt I I e.symm x :=
  by
  refine' ⟨(e.continuous_on_symm x hx).ContinuousAt (IsOpen.mem_nhds e.open_target hx), _⟩
  have mem : I x ∈ I.symm ⁻¹' (e.symm ≫ₕ chart_at H (e.symm x)).source ∩ range I := by simp only [hx, mfld_simps]
  have : e.symm.trans (chart_at H (e.symm x)) ∈ contDiffGroupoid ∞ I := HasGroupoid.compatible _ h (chart_mem_atlas H _)
  have A :
    ContDiffOn 𝕜 ∞ (I ∘ e.symm.trans (chart_at H (e.symm x)) ∘ I.symm)
      (I.symm ⁻¹' (e.symm.trans (chart_at H (e.symm x))).source ∩ range I) :=
    this.1
  have B := A.differentiable_on le_top (I x) mem
  simp only [mfld_simps] at B
  rw [inter_comm, differentiable_within_at_inter] at B
  · simpa only [mfld_simps]
    
  · apply IsOpen.mem_nhds ((LocalHomeomorph.open_source _).Preimage I.continuous_symm) mem.1
    
#align mdifferentiable_at_atlas_symm mdifferentiableAtAtlasSymm

theorem mdifferentiableOnAtlasSymm (h : e ∈ atlas H M) : MdifferentiableOn I I e.symm e.target := fun x hx =>
  (mdifferentiableAtAtlasSymm I h hx).MdifferentiableWithinAt
#align mdifferentiable_on_atlas_symm mdifferentiableOnAtlasSymm

theorem mdifferentiableOfMemAtlas (h : e ∈ atlas H M) : e.Mdifferentiable I I :=
  ⟨mdifferentiableOnAtlas I h, mdifferentiableOnAtlasSymm I h⟩
#align mdifferentiable_of_mem_atlas mdifferentiableOfMemAtlas

theorem mdifferentiableChart (x : M) : (chartAt H x).Mdifferentiable I I :=
  mdifferentiableOfMemAtlas _ (chart_mem_atlas _ _)
#align mdifferentiable_chart mdifferentiableChart

/-- The derivative of the chart at a base point is the chart of the tangent bundle, composed with
the identification between the tangent bundle of the model space and the product space. -/
theorem tangent_map_chart {p q : TangentBundle I M} (h : q.1 ∈ (chartAt H p.1).source) :
    tangentMap I I (chartAt H p.1) q =
      (Equiv.sigmaEquivProd _ _).symm ((chartAt (ModelProd H E) p : TangentBundle I M → ModelProd H E) q) :=
  by
  dsimp [tangentMap]
  rw [MdifferentiableAt.mfderiv]
  · rfl
    
  · exact mdifferentiableAtAtlas _ (chart_mem_atlas _ _) h
    
#align tangent_map_chart tangent_map_chart

/-- The derivative of the inverse of the chart at a base point is the inverse of the chart of the
tangent bundle, composed with the identification between the tangent bundle of the model space and
the product space. -/
theorem tangent_map_chart_symm {p : TangentBundle I M} {q : TangentBundle I H} (h : q.1 ∈ (chartAt H p.1).target) :
    tangentMap I I (chartAt H p.1).symm q =
      ((chartAt (ModelProd H E) p).symm : ModelProd H E → TangentBundle I M) ((Equiv.sigmaEquivProd H E) q) :=
  by
  dsimp only [tangentMap]
  rw [MdifferentiableAt.mfderiv (mdifferentiableAtAtlasSymm _ (chart_mem_atlas _ _) h)]
  -- a trivial instance is needed after the rewrite, handle it right now.
  rotate_left
  · infer_instance
    
  simp only [ContinuousLinearMap.coe_coe, BasicSmoothVectorBundleCore.chart, h, tangentBundleCore,
    BasicSmoothVectorBundleCore.toTopologicalVectorBundleCore, chart_at, Sigma.mk.inj_iff, mfld_simps]
#align tangent_map_chart_symm tangent_map_chart_symm

end Charts

end SpecificFunctions

/-! ### Differentiable local homeomorphisms -/


namespace LocalHomeomorph.Mdifferentiable

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type _} [TopologicalSpace M] [ChartedSpace H M] {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type _} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type _} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type _} [TopologicalSpace M'']
  [ChartedSpace H'' M''] {e : LocalHomeomorph M M'} (he : e.Mdifferentiable I I') {e' : LocalHomeomorph M' M''}

include he

theorem symm : e.symm.Mdifferentiable I' I :=
  ⟨he.2, he.1⟩
#align local_homeomorph.mdifferentiable.symm LocalHomeomorph.Mdifferentiable.symm

protected theorem mdifferentiableAt {x : M} (hx : x ∈ e.source) : MdifferentiableAt I I' e x :=
  (he.1 x hx).MdifferentiableAt (IsOpen.mem_nhds e.open_source hx)
#align local_homeomorph.mdifferentiable.mdifferentiable_at LocalHomeomorph.Mdifferentiable.mdifferentiableAt

theorem mdifferentiableAtSymm {x : M'} (hx : x ∈ e.target) : MdifferentiableAt I' I e.symm x :=
  (he.2 x hx).MdifferentiableAt (IsOpen.mem_nhds e.open_target hx)
#align local_homeomorph.mdifferentiable.mdifferentiable_at_symm LocalHomeomorph.Mdifferentiable.mdifferentiableAtSymm

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M'] [SmoothManifoldWithCorners I'' M'']

theorem symm_comp_deriv {x : M} (hx : x ∈ e.source) :
    (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
  have : mfderiv I I (e.symm ∘ e) x = (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) :=
    mfderiv_comp x (he.mdifferentiable_at_symm (e.map_source hx)) (he.mdifferentiable_at hx)
  rw [← this]
  have : mfderiv I I (_root_.id : M → M) x = ContinuousLinearMap.id _ _ := mfderiv_id I
  rw [← this]
  apply Filter.EventuallyEq.mfderiv_eq
  have : e.source ∈ 𝓝 x := IsOpen.mem_nhds e.open_source hx
  exact Filter.mem_of_superset this (by mfld_set_tac)
#align local_homeomorph.mdifferentiable.symm_comp_deriv LocalHomeomorph.Mdifferentiable.symm_comp_deriv

theorem comp_symm_deriv {x : M'} (hx : x ∈ e.target) :
    (mfderiv I I' e (e.symm x)).comp (mfderiv I' I e.symm x) = ContinuousLinearMap.id 𝕜 (TangentSpace I' x) :=
  he.symm.symm_comp_deriv hx
#align local_homeomorph.mdifferentiable.comp_symm_deriv LocalHomeomorph.Mdifferentiable.comp_symm_deriv

/-- The derivative of a differentiable local homeomorphism, as a continuous linear equivalence
between the tangent spaces at `x` and `e x`. -/
protected def mfderiv {x : M} (hx : x ∈ e.source) : TangentSpace I x ≃L[𝕜] TangentSpace I' (e x) :=
  { mfderiv I I' e x with invFun := mfderiv I' I e.symm (e x), continuous_to_fun := (mfderiv I I' e x).cont,
    continuous_inv_fun := (mfderiv I' I e.symm (e x)).cont,
    left_inv := fun y => by
      have : (ContinuousLinearMap.id _ _ : TangentSpace I x →L[𝕜] TangentSpace I x) y = y := rfl
      conv_rhs => rw [← this, ← he.symm_comp_deriv hx]
      rfl,
    right_inv := fun y => by
      have : (ContinuousLinearMap.id 𝕜 _ : TangentSpace I' (e x) →L[𝕜] TangentSpace I' (e x)) y = y := rfl
      conv_rhs => rw [← this, ← he.comp_symm_deriv (e.map_source hx)]
      rw [e.left_inv hx]
      rfl }
#align local_homeomorph.mdifferentiable.mfderiv LocalHomeomorph.Mdifferentiable.mfderiv

theorem mfderiv_bijective {x : M} (hx : x ∈ e.source) : Function.Bijective (mfderiv I I' e x) :=
  (he.mfderiv hx).Bijective
#align local_homeomorph.mdifferentiable.mfderiv_bijective LocalHomeomorph.Mdifferentiable.mfderiv_bijective

theorem mfderiv_injective {x : M} (hx : x ∈ e.source) : Function.Injective (mfderiv I I' e x) :=
  (he.mfderiv hx).Injective
#align local_homeomorph.mdifferentiable.mfderiv_injective LocalHomeomorph.Mdifferentiable.mfderiv_injective

theorem mfderiv_surjective {x : M} (hx : x ∈ e.source) : Function.Surjective (mfderiv I I' e x) :=
  (he.mfderiv hx).Surjective
#align local_homeomorph.mdifferentiable.mfderiv_surjective LocalHomeomorph.Mdifferentiable.mfderiv_surjective

theorem ker_mfderiv_eq_bot {x : M} (hx : x ∈ e.source) : LinearMap.ker (mfderiv I I' e x) = ⊥ :=
  (he.mfderiv hx).toLinearEquiv.ker
#align local_homeomorph.mdifferentiable.ker_mfderiv_eq_bot LocalHomeomorph.Mdifferentiable.ker_mfderiv_eq_bot

theorem range_mfderiv_eq_top {x : M} (hx : x ∈ e.source) : LinearMap.range (mfderiv I I' e x) = ⊤ :=
  (he.mfderiv hx).toLinearEquiv.range
#align local_homeomorph.mdifferentiable.range_mfderiv_eq_top LocalHomeomorph.Mdifferentiable.range_mfderiv_eq_top

theorem range_mfderiv_eq_univ {x : M} (hx : x ∈ e.source) : range (mfderiv I I' e x) = univ :=
  (he.mfderiv_surjective hx).range_eq
#align local_homeomorph.mdifferentiable.range_mfderiv_eq_univ LocalHomeomorph.Mdifferentiable.range_mfderiv_eq_univ

theorem trans (he' : e'.Mdifferentiable I' I'') : (e.trans e').Mdifferentiable I I'' := by
  constructor
  · intro x hx
    simp only [mfld_simps] at hx
    exact ((he'.mdifferentiable_at hx.2).comp _ (he.mdifferentiable_at hx.1)).MdifferentiableWithinAt
    
  · intro x hx
    simp only [mfld_simps] at hx
    exact ((he.symm.mdifferentiable_at hx.2).comp _ (he'.symm.mdifferentiable_at hx.1)).MdifferentiableWithinAt
    
#align local_homeomorph.mdifferentiable.trans LocalHomeomorph.Mdifferentiable.trans

end LocalHomeomorph.Mdifferentiable

/-! ### Differentiability of `ext_chart_at` -/


section extChartAt

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {s : Set M} {x y : M}

theorem hasMfderivAtExtChartAt (h : y ∈ (chartAt H x).source) :
    HasMfderivAt I 𝓘(𝕜, E) (extChartAt I x) y (mfderiv I I (chartAt H x) y : _) :=
  I.HasMfderivAt.comp y ((mdifferentiableChart I x).MdifferentiableAt h).HasMfderivAt
#align has_mfderiv_at_ext_chart_at hasMfderivAtExtChartAt

theorem hasMfderivWithinAtExtChartAt (h : y ∈ (chartAt H x).source) :
    HasMfderivWithinAt I 𝓘(𝕜, E) (extChartAt I x) s y (mfderiv I I (chartAt H x) y : _) :=
  (hasMfderivAtExtChartAt I h).HasMfderivWithinAt
#align has_mfderiv_within_at_ext_chart_at hasMfderivWithinAtExtChartAt

theorem mdifferentiableAtExtChartAt (h : y ∈ (chartAt H x).source) : MdifferentiableAt I 𝓘(𝕜, E) (extChartAt I x) y :=
  (hasMfderivAtExtChartAt I h).MdifferentiableAt
#align mdifferentiable_at_ext_chart_at mdifferentiableAtExtChartAt

theorem mdifferentiableOnExtChartAt : MdifferentiableOn I 𝓘(𝕜, E) (extChartAt I x) (chartAt H x).source := fun y hy =>
  (hasMfderivWithinAtExtChartAt I hy).MdifferentiableWithinAt
#align mdifferentiable_on_ext_chart_at mdifferentiableOnExtChartAt

end extChartAt

/-! ### Unique derivative sets in manifolds -/


section UniqueMdiff

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _}
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  {s : Set M}

/-- If a set has the unique differential property, then its image under a local
diffeomorphism also has the unique differential property. -/
theorem UniqueMdiffOn.uniqueMdiffOnPreimage [SmoothManifoldWithCorners I' M'] (hs : UniqueMdiffOn I s)
    {e : LocalHomeomorph M M'} (he : e.Mdifferentiable I I') : UniqueMdiffOn I' (e.target ∩ e.symm ⁻¹' s) := by
  /- Start from a point `x` in the image, and let `z` be its preimage. Then the unique
    derivative property at `x` is expressed through `ext_chart_at I' x`, and the unique
    derivative property at `z` is expressed through `ext_chart_at I z`. We will argue that
    the composition of these two charts with `e` is a local diffeomorphism in vector spaces,
    and therefore preserves the unique differential property thanks to lemma
    `has_fderiv_within_at.unique_diff_within_at`, saying that a differentiable function with onto
    derivative preserves the unique derivative property.-/
  intro x hx
  let z := e.symm x
  have z_source : z ∈ e.source := by simp only [hx.1, mfld_simps]
  have zx : e z = x := by simp only [z, hx.1, mfld_simps]
  let F := extChartAt I z
  -- the unique derivative property at `z` is expressed through its preferred chart,
  -- that we call `F`.
  have B : UniqueDiffWithinAt 𝕜 (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' (extChartAt I' x).source)) ∩ F.target) (F z) := by
    have : UniqueMdiffWithinAt I s z := hs _ hx.2
    have S : e.source ∩ e ⁻¹' (extChartAt I' x).source ∈ 𝓝 z := by
      apply IsOpen.mem_nhds
      apply e.continuous_on.preimage_open_of_open e.open_source (ext_chart_at_open_source I' x)
      simp only [z_source, zx, mfld_simps]
    have := this.inter S
    rw [unique_mdiff_within_at_iff] at this
    exact this
  -- denote by `G` the change of coordinate, i.e., the composition of the two extended charts and
  -- of `e`
  let G := F.symm ≫ e.to_local_equiv ≫ extChartAt I' x
  -- `G` is differentiable
  have Diff : ((chart_at H z).symm ≫ₕ e ≫ₕ chart_at H' x).Mdifferentiable I I' := by
    have A := mdifferentiableOfMemAtlas I (chart_mem_atlas H z)
    have B := mdifferentiableOfMemAtlas I' (chart_mem_atlas H' x)
    exact A.symm.trans (he.trans B)
  have Mmem : (chart_at H z : M → H) z ∈ ((chart_at H z).symm ≫ₕ e ≫ₕ chart_at H' x).source := by
    simp only [z_source, zx, mfld_simps]
  have A : DifferentiableWithinAt 𝕜 G (range I) (F z) := by
    refine' (Diff.mdifferentiable_at Mmem).2.congr (fun p hp => _) _ <;> simp only [G, F, mfld_simps]
  -- let `G'` be its derivative
  let G' := fderivWithin 𝕜 G (range I) (F z)
  have D₁ : HasFderivWithinAt G G' (range I) (F z) := A.has_fderiv_within_at
  have D₂ : HasFderivWithinAt G G' (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' (extChartAt I' x).source)) ∩ F.target) (F z) :=
    D₁.mono (by mfld_set_tac)
  -- The derivative `G'` is onto, as it is the derivative of a local diffeomorphism, the composition
  -- of the two charts and of `e`.
  have C : DenseRange (G' : E → E') := by
    have : G' = mfderiv I I' ((chart_at H z).symm ≫ₕ e ≫ₕ chart_at H' x) ((chart_at H z : M → H) z) := by
      rw [(Diff.mdifferentiable_at Mmem).mfderiv]
      rfl
    rw [this]
    exact (Diff.mfderiv_surjective Mmem).DenseRange
  -- key step: thanks to what we have proved about it, `G` preserves the unique derivative property
  have key :
    UniqueDiffWithinAt 𝕜 (G '' (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' (extChartAt I' x).source)) ∩ F.target)) (G (F z)) :=
    D₂.unique_diff_within_at B C
  have : G (F z) = (extChartAt I' x) x := by
    dsimp [G, F]
    simp only [hx.1, mfld_simps]
  rw [this] at key
  apply key.mono
  show
    G '' (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' (extChartAt I' x).source)) ∩ F.target) ⊆
      (extChartAt I' x).symm ⁻¹' e.target ∩ (extChartAt I' x).symm ⁻¹' (e.symm ⁻¹' s) ∩ range I'
  rw [image_subset_iff]
  mfld_set_tac
#align unique_mdiff_on.unique_mdiff_on_preimage UniqueMdiffOn.uniqueMdiffOnPreimage

/-- If a set in a manifold has the unique derivative property, then its pullback by any extended
chart, in the vector space, also has the unique derivative property. -/
theorem UniqueMdiffOn.uniqueDiffOnTargetInter (hs : UniqueMdiffOn I s) (x : M) :
    UniqueDiffOn 𝕜 ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) := by
  -- this is just a reformulation of `unique_mdiff_on.unique_mdiff_on_preimage`, using as `e`
  -- the local chart at `x`.
  intro z hz
  simp only [mfld_simps] at hz
  have : (chart_at H x).Mdifferentiable I I := mdifferentiableChart _ _
  have T := (hs.unique_mdiff_on_preimage this) (I.symm z)
  simp only [hz.left.left, hz.left.right, hz.right, UniqueMdiffWithinAt, mfld_simps] at T⊢
  convert T using 1
  rw [@preimage_comp _ _ _ _ (chart_at H x).symm]
  mfld_set_tac
#align unique_mdiff_on.unique_diff_on_target_inter UniqueMdiffOn.uniqueDiffOnTargetInter

/-- When considering functions between manifolds, this statement shows up often. It entails
the unique differential of the pullback in extended charts of the set where the function can
be read in the charts. -/
theorem UniqueMdiffOn.uniqueDiffOnInterPreimage (hs : UniqueMdiffOn I s) (x : M) (y : M') {f : M → M'}
    (hf : ContinuousOn f s) :
    UniqueDiffOn 𝕜 ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) :=
  haveI : UniqueMdiffOn I (s ∩ f ⁻¹' (extChartAt I' y).source) := by
    intro z hz
    apply (hs z hz.1).inter'
    apply (hf z hz.1).preimage_mem_nhds_within
    exact IsOpen.mem_nhds (ext_chart_at_open_source I' y) hz.2
  this.unique_diff_on_target_inter _
#align unique_mdiff_on.unique_diff_on_inter_preimage UniqueMdiffOn.uniqueDiffOnInterPreimage

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (Z : BasicSmoothVectorBundleCore I M F)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- In a smooth fiber bundle constructed from core, the preimage under the projection of a set with
unique differential in the basis also has unique differential. -/
theorem UniqueMdiffOn.smoothBundlePreimage (hs : UniqueMdiffOn I s) :
    UniqueMdiffOn (I.Prod 𝓘(𝕜, F)) (Z.toTopologicalVectorBundleCore.proj ⁻¹' s) := by
  /- Using a chart (and the fact that unique differentiability is invariant under charts), we
    reduce the situation to the model space, where we can use the fact that products respect
    unique differentiability. -/
  intro p hp
  replace hp : p.fst ∈ s
  · simpa only [mfld_simps] using hp
    
  let e₀ := chart_at H p.1
  let e := chart_at (ModelProd H F) p
  -- It suffices to prove unique differentiability in a chart
  suffices h : UniqueMdiffOn (I.prod 𝓘(𝕜, F)) (e.target ∩ e.symm ⁻¹' (Z.to_topological_vector_bundle_core.proj ⁻¹' s))
  · have A :
      UniqueMdiffOn (I.prod 𝓘(𝕜, F))
        (e.symm.target ∩ e.symm.symm ⁻¹' (e.target ∩ e.symm ⁻¹' (Z.to_topological_vector_bundle_core.proj ⁻¹' s))) :=
      by
      apply h.unique_mdiff_on_preimage
      exact (mdifferentiableOfMemAtlas _ (chart_mem_atlas _ _)).symm
      infer_instance
    have :
      p ∈ e.symm.target ∩ e.symm.symm ⁻¹' (e.target ∩ e.symm ⁻¹' (Z.to_topological_vector_bundle_core.proj ⁻¹' s)) := by
      simp only [e, hp, mfld_simps]
    apply (A _ this).mono
    intro q hq
    simp only [e, LocalHomeomorph.left_inv _ hq.1, mfld_simps] at hq
    simp only [hq, mfld_simps]
    
  -- rewrite the relevant set in the chart as a direct product
  have :
    (fun p : E × F => (I.symm p.1, p.snd)) ⁻¹' e.target ∩
          (fun p : E × F => (I.symm p.1, p.snd)) ⁻¹' (e.symm ⁻¹' (Sigma.fst ⁻¹' s)) ∩
        range I ×ˢ univ =
      (I.symm ⁻¹' (e₀.target ∩ e₀.symm ⁻¹' s) ∩ range I) ×ˢ univ :=
    by mfld_set_tac
  intro q hq
  replace hq : q.1 ∈ (chart_at H p.1).target ∧ ((chart_at H p.1).symm : H → M) q.1 ∈ s
  · simpa only [mfld_simps] using hq
    
  simp only [UniqueMdiffWithinAt, ModelWithCorners.prod, preimage_inter, this, mfld_simps]
  -- apply unique differentiability of products to conclude
  apply UniqueDiffOn.prod _ uniqueDiffOnUniv
  · simp only [hq, mfld_simps]
    
  · intro x hx
    have A : UniqueMdiffOn I (e₀.target ∩ e₀.symm ⁻¹' s) := by
      apply hs.unique_mdiff_on_preimage
      exact mdifferentiableOfMemAtlas _ (chart_mem_atlas _ _)
      infer_instance
    simp only [UniqueMdiffOn, UniqueMdiffWithinAt, preimage_inter, mfld_simps] at A
    have B := A (I.symm x) hx.1.1 hx.1.2
    rwa [← preimage_inter, ModelWithCorners.right_inv _ hx.2] at B
    
#align unique_mdiff_on.smooth_bundle_preimage UniqueMdiffOn.smoothBundlePreimage

theorem UniqueMdiffOn.tangentBundleProjPreimage (hs : UniqueMdiffOn I s) :
    UniqueMdiffOn I.tangent (TangentBundle.proj I M ⁻¹' s) :=
  hs.smoothBundlePreimage _
#align unique_mdiff_on.tangent_bundle_proj_preimage UniqueMdiffOn.tangentBundleProjPreimage

end UniqueMdiff

