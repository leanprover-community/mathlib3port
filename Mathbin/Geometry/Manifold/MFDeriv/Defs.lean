/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Geometry.Manifold.VectorBundle.Tangent

#align_import geometry.manifold.mfderiv from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# The derivative of functions between smooth manifolds

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
`written_in_ext_chart I I' x f` for the function `f` written in the preferred extended charts. Then
the manifold derivative of `f`, at `x`, is just the usual derivative of
`written_in_ext_chart I I' x f`, at the point `(ext_chart_at I x) x`.

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

open scoped Classical Topology Manifold Bundle

open Set Bundle

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


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type _} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') {M' : Type _}
  [TopologicalSpace M'] [ChartedSpace H' M']

#print DifferentiableWithinAtProp /-
/-- Property in the model space of a model with corners of being differentiable within at set at a
point, when read in the model vector space. This property will be lifted to manifolds to define
differentiable functions between manifolds. -/
def DifferentiableWithinAtProp (f : H → H') (s : Set H) (x : H) : Prop :=
  DifferentiableWithinAt 𝕜 (I' ∘ f ∘ I.symm) (⇑I.symm ⁻¹' s ∩ Set.range I) (I x)
#align differentiable_within_at_prop DifferentiableWithinAtProp
-/

#print differentiable_within_at_localInvariantProp /-
/-- Being differentiable in the model space is a local property, invariant under smooth maps.
Therefore, it will lift nicely to manifolds. -/
theorem differentiable_within_at_localInvariantProp :
    (contDiffGroupoid ⊤ I).LocalInvariantProp (contDiffGroupoid ⊤ I')
      (DifferentiableWithinAtProp I I') :=
  { is_local := by
      intro s x u f u_open xu
      have : I.symm ⁻¹' (s ∩ u) ∩ Set.range I = I.symm ⁻¹' s ∩ Set.range I ∩ I.symm ⁻¹' u := by
        simp only [Set.inter_right_comm, Set.preimage_inter]
      rw [DifferentiableWithinAtProp, DifferentiableWithinAtProp, this]
      symm
      apply differentiableWithinAt_inter
      have : u ∈ 𝓝 (I.symm (I x)) := by rw [ModelWithCorners.left_inv];
        exact IsOpen.mem_nhds u_open xu
      apply ContinuousAt.preimage_mem_nhds I.continuous_symm.continuous_at this
    right_invariance' := by
      intro s x f e he hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)) := by simp only [hx, mfld_simps]
      rw [this] at h
      have : I (e x) ∈ I.symm ⁻¹' e.target ∩ Set.range I := by simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he).2.ContDiffWithinAt this
      convert (h.comp' _ (this.differentiable_within_at le_top)).mono_of_mem _ using 1
      · ext y; simp only [mfld_simps]
      refine'
        mem_nhds_within.mpr
          ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
            simp_rw [Set.mem_preimage, I.left_inv, e.maps_to hx], _⟩
      mfld_set_tac
    congr_of_forall := by
      intro s x f g h hx hf
      apply hf.congr
      · intro y hy
        simp only [mfld_simps] at hy
        simp only [h, hy, mfld_simps]
      · simp only [hx, mfld_simps]
    left_invariance' := by
      intro s x f e' he' hs hx h
      rw [DifferentiableWithinAtProp] at h ⊢
      have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ Set.range I' := by
        simp only [hx, mfld_simps]
      have := (mem_groupoid_of_pregroupoid.2 he').1.ContDiffWithinAt A
      convert (this.differentiable_within_at le_top).comp _ h _
      · ext y; simp only [mfld_simps]
      · intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1 }
#align differentiable_within_at_local_invariant_prop differentiable_within_at_localInvariantProp
-/

#print UniqueMDiffWithinAt /-
/-- Predicate ensuring that, at a point and within a set, a function can have at most one
derivative. This is expressed using the preferred chart at the considered point. -/
def UniqueMDiffWithinAt (s : Set M) (x : M) :=
  UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
#align unique_mdiff_within_at UniqueMDiffWithinAt
-/

#print UniqueMDiffOn /-
/-- Predicate ensuring that, at all points of a set, a function can have at most one derivative. -/
def UniqueMDiffOn (s : Set M) :=
  ∀ x ∈ s, UniqueMDiffWithinAt I s x
#align unique_mdiff_on UniqueMDiffOn
-/

#print MDifferentiableWithinAt /-
/-- `mdifferentiable_within_at I I' f s x` indicates that the function `f` between manifolds
has a derivative at the point `x` within the set `s`.
This is a generalization of `differentiable_within_at` to manifolds.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def MDifferentiableWithinAt (f : M → M') (s : Set M) (x : M) :=
  ContinuousWithinAt f s x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      ((extChartAt I x) x)
#align mdifferentiable_within_at MDifferentiableWithinAt
-/

#print mdifferentiableWithinAt_iff' /-
theorem mdifferentiableWithinAt_iff' (f : M → M') (s : Set M) (x : M) :
    MDifferentiableWithinAt I I' f s x ↔ LiftPropWithinAt (DifferentiableWithinAtProp I I') f s x :=
  by rfl
#align mdifferentiable_within_at_iff_lift_prop_within_at mdifferentiableWithinAt_iff'
-/

#print MDifferentiableAt /-
/-- `mdifferentiable_at I I' f x` indicates that the function `f` between manifolds
has a derivative at the point `x`.
This is a generalization of `differentiable_at` to manifolds.

We require continuity in the definition, as otherwise points close to `x` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def MDifferentiableAt (f : M → M') (x : M) :=
  ContinuousAt f x ∧
    DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f) (range I) ((extChartAt I x) x)
#align mdifferentiable_at MDifferentiableAt
-/

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]] -/
#print mdifferentiableAt_iff /-
theorem mdifferentiableAt_iff (f : M → M') (x : M) :
    MDifferentiableAt I I' f x ↔ LiftPropAt (DifferentiableWithinAtProp I I') f x :=
  by
  trace
    "././././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]"
  · rw [continuousWithinAt_univ]
  · simp [DifferentiableWithinAtProp, Set.univ_inter]
#align mdifferentiable_at_iff_lift_prop_at mdifferentiableAt_iff
-/

#print MDifferentiableOn /-
/-- `mdifferentiable_on I I' f s` indicates that the function `f` between manifolds
has a derivative within `s` at all points of `s`.
This is a generalization of `differentiable_on` to manifolds. -/
def MDifferentiableOn (f : M → M') (s : Set M) :=
  ∀ x ∈ s, MDifferentiableWithinAt I I' f s x
#align mdifferentiable_on MDifferentiableOn
-/

#print MDifferentiable /-
/-- `mdifferentiable I I' f` indicates that the function `f` between manifolds
has a derivative everywhere.
This is a generalization of `differentiable` to manifolds. -/
def MDifferentiable (f : M → M') :=
  ∀ x, MDifferentiableAt I I' f x
#align mdifferentiable MDifferentiable
-/

#print PartialHomeomorph.MDifferentiable /-
/-- Prop registering if a local homeomorphism is a local diffeomorphism on its source -/
def PartialHomeomorph.MDifferentiable (f : PartialHomeomorph M M') :=
  MDifferentiableOn I I' f f.source ∧ MDifferentiableOn I' I f.symm f.target
#align local_homeomorph.mdifferentiable PartialHomeomorph.MDifferentiable
-/

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M']

#print HasMFDerivWithinAt /-
/-- `has_mfderiv_within_at I I' f s x f'` indicates that the function `f` between manifolds
has, at the point `x` and within the set `s`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

This is a generalization of `has_fderiv_within_at` to manifolds (as indicated by the prefix `m`).
The order of arguments is changed as the type of the derivative `f'` depends on the choice of `x`.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def HasMFDerivWithinAt (f : M → M') (s : Set M) (x : M)
    (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousWithinAt f s x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f'
      ((extChartAt I x).symm ⁻¹' s ∩ range I) ((extChartAt I x) x)
#align has_mfderiv_within_at HasMFDerivWithinAt
-/

#print HasMFDerivAt /-
/-- `has_mfderiv_at I I' f x f'` indicates that the function `f` between manifolds
has, at the point `x`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

We require continuity in the definition, as otherwise points close to `x` `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def HasMFDerivAt (f : M → M') (x : M) (f' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)) :=
  ContinuousAt f x ∧
    HasFDerivWithinAt (writtenInExtChartAt I I' x f : E → E') f' (range I) ((extChartAt I x) x)
#align has_mfderiv_at HasMFDerivAt
-/

#print mfderivWithin /-
/-- Let `f` be a function between two smooth manifolds. Then `mfderiv_within I I' f s x` is the
derivative of `f` at `x` within `s`, as a continuous linear map from the tangent space at `x` to the
tangent space at `f x`. -/
def mfderivWithin (f : M → M') (s : Set M) (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableWithinAt I I' f s x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) :
      _)
  else 0
#align mfderiv_within mfderivWithin
-/

#print mfderiv /-
/-- Let `f` be a function between two smooth manifolds. Then `mfderiv I I' f x` is the derivative of
`f` at `x`, as a continuous linear map from the tangent space at `x` to the tangent space at
`f x`. -/
def mfderiv (f : M → M') (x : M) : TangentSpace I x →L[𝕜] TangentSpace I' (f x) :=
  if MDifferentiableAt I I' f x then
    (fderivWithin 𝕜 (writtenInExtChartAt I I' x f : E → E') (range I) ((extChartAt I x) x) : _)
  else 0
#align mfderiv mfderiv
-/

#print tangentMapWithin /-
/-- The derivative within a set, as a map between the tangent bundles -/
def tangentMapWithin (f : M → M') (s : Set M) : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderivWithin I I' f s p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩
#align tangent_map_within tangentMapWithin
-/

#print tangentMap /-
/-- The derivative, as a map between the tangent bundles -/
def tangentMap (f : M → M') : TangentBundle I M → TangentBundle I' M' := fun p =>
  ⟨f p.1, (mfderiv I I' f p.1 : TangentSpace I p.1 → TangentSpace I' (f p.1)) p.2⟩
#align tangent_map tangentMap
-/

end DerivativesDefinitions

section DerivativesProperties

/-! ### Unique differentiability sets in manifolds -/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M]
  --
  {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type _} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type _} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f f₀ f₁ : M → M'} {x : M} {s t : Set M} {g : M' → M''} {u : Set M'}

#print uniqueMDiffWithinAt_univ /-
theorem uniqueMDiffWithinAt_univ : UniqueMDiffWithinAt I univ x :=
  by
  unfold UniqueMDiffWithinAt
  simp only [preimage_univ, univ_inter]
  exact I.unique_diff _ (mem_range_self _)
#align unique_mdiff_within_at_univ uniqueMDiffWithinAt_univ
-/

variable {I}

#print uniqueMDiffWithinAt_iff /-
theorem uniqueMDiffWithinAt_iff {s : Set M} {x : M} :
    UniqueMDiffWithinAt I s x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target)
        ((extChartAt I x) x) :=
  by
  apply uniqueDiffWithinAt_congr
  rw [nhdsWithin_inter, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]
#align unique_mdiff_within_at_iff uniqueMDiffWithinAt_iff
-/

#print UniqueMDiffWithinAt.mono /-
theorem UniqueMDiffWithinAt.mono (h : UniqueMDiffWithinAt I s x) (st : s ⊆ t) :
    UniqueMDiffWithinAt I t x :=
  UniqueDiffWithinAt.mono h <| inter_subset_inter (preimage_mono st) (Subset.refl _)
#align unique_mdiff_within_at.mono UniqueMDiffWithinAt.mono
-/

#print UniqueMDiffWithinAt.inter' /-
theorem UniqueMDiffWithinAt.inter' (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝[s] x) :
    UniqueMDiffWithinAt I (s ∩ t) x :=
  by
  rw [UniqueMDiffWithinAt, extChartAt_preimage_inter_eq]
  exact UniqueDiffWithinAt.inter' hs (extChartAt_preimage_mem_nhdsWithin I x ht)
#align unique_mdiff_within_at.inter' UniqueMDiffWithinAt.inter'
-/

#print UniqueMDiffWithinAt.inter /-
theorem UniqueMDiffWithinAt.inter (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝 x) :
    UniqueMDiffWithinAt I (s ∩ t) x :=
  by
  rw [UniqueMDiffWithinAt, extChartAt_preimage_inter_eq]
  exact UniqueDiffWithinAt.inter hs (extChartAt_preimage_mem_nhds I x ht)
#align unique_mdiff_within_at.inter UniqueMDiffWithinAt.inter
-/

#print IsOpen.uniqueMDiffWithinAt /-
theorem IsOpen.uniqueMDiffWithinAt (xs : x ∈ s) (hs : IsOpen s) : UniqueMDiffWithinAt I s x :=
  by
  have := UniqueMDiffWithinAt.inter (uniqueMDiffWithinAt_univ I) (IsOpen.mem_nhds hs xs)
  rwa [univ_inter] at this
#align is_open.unique_mdiff_within_at IsOpen.uniqueMDiffWithinAt
-/

#print UniqueMDiffOn.inter /-
theorem UniqueMDiffOn.inter (hs : UniqueMDiffOn I s) (ht : IsOpen t) : UniqueMDiffOn I (s ∩ t) :=
  fun x hx => UniqueMDiffWithinAt.inter (hs _ hx.1) (IsOpen.mem_nhds ht hx.2)
#align unique_mdiff_on.inter UniqueMDiffOn.inter
-/

#print IsOpen.uniqueMDiffOn /-
theorem IsOpen.uniqueMDiffOn (hs : IsOpen s) : UniqueMDiffOn I s := fun x hx =>
  IsOpen.uniqueMDiffWithinAt hx hs
#align is_open.unique_mdiff_on IsOpen.uniqueMDiffOn
-/

#print uniqueMDiffOn_univ /-
theorem uniqueMDiffOn_univ : UniqueMDiffOn I (univ : Set M) :=
  isOpen_univ.UniqueMDiffOn
#align unique_mdiff_on_univ uniqueMDiffOn_univ
-/

/- We name the typeclass variables related to `smooth_manifold_with_corners` structure as they are
necessary in lemmas mentioning the derivative, but not in lemmas about differentiability, so we
want to include them or omit them when necessary. -/
variable [Is : SmoothManifoldWithCorners I M] [I's : SmoothManifoldWithCorners I' M']
  [I''s : SmoothManifoldWithCorners I'' M'']
  {f' f₀' f₁' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)}
  {g' : TangentSpace I' (f x) →L[𝕜] TangentSpace I'' (g (f x))}

#print UniqueMDiffWithinAt.eq /-
/-- `unique_mdiff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem UniqueMDiffWithinAt.eq (U : UniqueMDiffWithinAt I s x)
    (h : HasMFDerivWithinAt I I' f s x f') (h₁ : HasMFDerivWithinAt I I' f s x f₁') : f' = f₁' :=
  U.Eq h.2 h₁.2
#align unique_mdiff_within_at.eq UniqueMDiffWithinAt.eq
-/

#print UniqueMDiffOn.eq /-
theorem UniqueMDiffOn.eq (U : UniqueMDiffOn I s) (hx : x ∈ s) (h : HasMFDerivWithinAt I I' f s x f')
    (h₁ : HasMFDerivWithinAt I I' f s x f₁') : f' = f₁' :=
  UniqueMDiffWithinAt.eq (U _ hx) h h₁
#align unique_mdiff_on.eq UniqueMDiffOn.eq
-/

/-!
### General lemmas on derivatives of functions between manifolds

We mimick the API for functions between vector spaces
-/


#print mdifferentiableWithinAt_iff /-
theorem mdifferentiableWithinAt_iff {f : M → M'} {s : Set M} {x : M} :
    MDifferentiableWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) :=
  by
  refine' and_congr Iff.rfl (exists_congr fun f' => _)
  rw [inter_comm]
  simp only [HasFDerivWithinAt, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]
#align mdifferentiable_within_at_iff mdifferentiableWithinAt_iff
-/

#print mdifferentiableWithinAt_iff_of_mem_source /-
/-- One can reformulate differentiability within a set at a point as continuity within this set at
this point, and differentiability in any chart containing that point. -/
theorem mdifferentiableWithinAt_iff_of_mem_source {x' : M} {y : M'}
    (hx : x' ∈ (ChartedSpace.chartAt H x).source) (hy : f x' ∈ (ChartedSpace.chartAt H' y).source) :
    MDifferentiableWithinAt I I' f s x' ↔
      ContinuousWithinAt f s x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ Set.range I) ((extChartAt I x) x') :=
  (differentiable_within_at_localInvariantProp I I').liftPropWithinAt_indep_chart
    (StructureGroupoid.chart_mem_maximalAtlas _ x) hx (StructureGroupoid.chart_mem_maximalAtlas _ y)
    hy
#align mdifferentiable_within_at_iff_of_mem_source mdifferentiableWithinAt_iff_of_mem_source
-/

#print mfderivWithin_zero_of_not_mdifferentiableWithinAt /-
theorem mfderivWithin_zero_of_not_mdifferentiableWithinAt
    (h : ¬MDifferentiableWithinAt I I' f s x) : mfderivWithin I I' f s x = 0 := by
  simp only [mfderivWithin, h, if_neg, not_false_iff]
#align mfderiv_within_zero_of_not_mdifferentiable_within_at mfderivWithin_zero_of_not_mdifferentiableWithinAt
-/

#print mfderiv_zero_of_not_mdifferentiableAt /-
theorem mfderiv_zero_of_not_mdifferentiableAt (h : ¬MDifferentiableAt I I' f x) :
    mfderiv I I' f x = 0 := by simp only [mfderiv, h, if_neg, not_false_iff]
#align mfderiv_zero_of_not_mdifferentiable_at mfderiv_zero_of_not_mdifferentiableAt
-/

#print HasMFDerivWithinAt.mono /-
theorem HasMFDerivWithinAt.mono (h : HasMFDerivWithinAt I I' f t x f') (hst : s ⊆ t) :
    HasMFDerivWithinAt I I' f s x f' :=
  ⟨ContinuousWithinAt.mono h.1 hst,
    HasFDerivWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩
#align has_mfderiv_within_at.mono HasMFDerivWithinAt.mono
-/

#print HasMFDerivAt.hasMFDerivWithinAt /-
theorem HasMFDerivAt.hasMFDerivWithinAt (h : HasMFDerivAt I I' f x f') :
    HasMFDerivWithinAt I I' f s x f' :=
  ⟨ContinuousAt.continuousWithinAt h.1, HasFDerivWithinAt.mono h.2 (inter_subset_right _ _)⟩
#align has_mfderiv_at.has_mfderiv_within_at HasMFDerivAt.hasMFDerivWithinAt
-/

#print HasMFDerivWithinAt.mdifferentiableWithinAt /-
theorem HasMFDerivWithinAt.mdifferentiableWithinAt (h : HasMFDerivWithinAt I I' f s x f') :
    MDifferentiableWithinAt I I' f s x :=
  ⟨h.1, ⟨f', h.2⟩⟩
#align has_mfderiv_within_at.mdifferentiable_within_at HasMFDerivWithinAt.mdifferentiableWithinAt
-/

#print HasMFDerivAt.mdifferentiableAt /-
theorem HasMFDerivAt.mdifferentiableAt (h : HasMFDerivAt I I' f x f') :
    MDifferentiableAt I I' f x :=
  ⟨h.1, ⟨f', h.2⟩⟩
#align has_mfderiv_at.mdifferentiable_at HasMFDerivAt.mdifferentiableAt
-/

#print hasMFDerivWithinAt_univ /-
@[simp, mfld_simps]
theorem hasMFDerivWithinAt_univ : HasMFDerivWithinAt I I' f univ x f' ↔ HasMFDerivAt I I' f x f' :=
  by simp only [HasMFDerivWithinAt, HasMFDerivAt, continuousWithinAt_univ, mfld_simps]
#align has_mfderiv_within_at_univ hasMFDerivWithinAt_univ
-/

#print hasMFDerivAt_unique /-
theorem hasMFDerivAt_unique (h₀ : HasMFDerivAt I I' f x f₀') (h₁ : HasMFDerivAt I I' f x f₁') :
    f₀' = f₁' := by
  rw [← hasMFDerivWithinAt_univ] at h₀ h₁
  exact (uniqueMDiffWithinAt_univ I).Eq h₀ h₁
#align has_mfderiv_at_unique hasMFDerivAt_unique
-/

#print hasMFDerivWithinAt_inter' /-
theorem hasMFDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasMFDerivWithinAt I I' f (s ∩ t) x f' ↔ HasMFDerivWithinAt I I' f s x f' :=
  by
  rw [HasMFDerivWithinAt, HasMFDerivWithinAt, extChartAt_preimage_inter_eq,
    hasFDerivWithinAt_inter', continuousWithinAt_inter' h]
  exact extChartAt_preimage_mem_nhdsWithin I x h
#align has_mfderiv_within_at_inter' hasMFDerivWithinAt_inter'
-/

#print hasMFDerivWithinAt_inter /-
theorem hasMFDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasMFDerivWithinAt I I' f (s ∩ t) x f' ↔ HasMFDerivWithinAt I I' f s x f' :=
  by
  rw [HasMFDerivWithinAt, HasMFDerivWithinAt, extChartAt_preimage_inter_eq, hasFDerivWithinAt_inter,
    continuousWithinAt_inter h]
  exact extChartAt_preimage_mem_nhds I x h
#align has_mfderiv_within_at_inter hasMFDerivWithinAt_inter
-/

#print HasMFDerivWithinAt.union /-
theorem HasMFDerivWithinAt.union (hs : HasMFDerivWithinAt I I' f s x f')
    (ht : HasMFDerivWithinAt I I' f t x f') : HasMFDerivWithinAt I I' f (s ∪ t) x f' :=
  by
  constructor
  · exact ContinuousWithinAt.union hs.1 ht.1
  · convert HasFDerivWithinAt.union hs.2 ht.2
    simp only [union_inter_distrib_right, preimage_union]
#align has_mfderiv_within_at.union HasMFDerivWithinAt.union
-/

#print HasMFDerivWithinAt.mono_of_mem /-
theorem HasMFDerivWithinAt.mono_of_mem (h : HasMFDerivWithinAt I I' f s x f') (ht : s ∈ 𝓝[t] x) :
    HasMFDerivWithinAt I I' f t x f' :=
  (hasMFDerivWithinAt_inter' ht).1 (h.mono (inter_subset_right _ _))
#align has_mfderiv_within_at.nhds_within HasMFDerivWithinAt.mono_of_mem
-/

#print HasMFDerivWithinAt.hasMFDerivAt /-
theorem HasMFDerivWithinAt.hasMFDerivAt (h : HasMFDerivWithinAt I I' f s x f') (hs : s ∈ 𝓝 x) :
    HasMFDerivAt I I' f x f' := by
  rwa [← univ_inter s, hasMFDerivWithinAt_inter hs, hasMFDerivWithinAt_univ] at h
#align has_mfderiv_within_at.has_mfderiv_at HasMFDerivWithinAt.hasMFDerivAt
-/

#print MDifferentiableWithinAt.hasMFDerivWithinAt /-
theorem MDifferentiableWithinAt.hasMFDerivWithinAt (h : MDifferentiableWithinAt I I' f s x) :
    HasMFDerivWithinAt I I' f s x (mfderivWithin I I' f s x) :=
  by
  refine' ⟨h.1, _⟩
  simp only [mfderivWithin, h, if_pos, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.2
#align mdifferentiable_within_at.has_mfderiv_within_at MDifferentiableWithinAt.hasMFDerivWithinAt
-/

#print MDifferentiableWithinAt.mfderivWithin /-
theorem MDifferentiableWithinAt.mfderivWithin (h : MDifferentiableWithinAt I I' f s x) :
    mfderivWithin I I' f s x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f : _) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) :=
  by simp only [mfderivWithin, h, if_pos]
#align mdifferentiable_within_at.mfderiv_within MDifferentiableWithinAt.mfderivWithin
-/

#print MDifferentiableAt.hasMFDerivAt /-
theorem MDifferentiableAt.hasMFDerivAt (h : MDifferentiableAt I I' f x) :
    HasMFDerivAt I I' f x (mfderiv I I' f x) :=
  by
  refine' ⟨h.1, _⟩
  simp only [mfderiv, h, if_pos, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.2
#align mdifferentiable_at.has_mfderiv_at MDifferentiableAt.hasMFDerivAt
-/

#print MDifferentiableAt.mfderiv /-
theorem MDifferentiableAt.mfderiv (h : MDifferentiableAt I I' f x) :
    mfderiv I I' f x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f : _) (range I) ((extChartAt I x) x) :=
  by simp only [mfderiv, h, if_pos]
#align mdifferentiable_at.mfderiv MDifferentiableAt.mfderiv
-/

#print HasMFDerivAt.mfderiv /-
theorem HasMFDerivAt.mfderiv (h : HasMFDerivAt I I' f x f') : mfderiv I I' f x = f' :=
  (hasMFDerivAt_unique h h.MDifferentiableAt.HasMFDerivAt).symm
#align has_mfderiv_at.mfderiv HasMFDerivAt.mfderiv
-/

#print HasMFDerivWithinAt.mfderivWithin /-
theorem HasMFDerivWithinAt.mfderivWithin (h : HasMFDerivWithinAt I I' f s x f')
    (hxs : UniqueMDiffWithinAt I s x) : mfderivWithin I I' f s x = f' := by ext;
  rw [hxs.eq h h.mdifferentiable_within_at.has_mfderiv_within_at]
#align has_mfderiv_within_at.mfderiv_within HasMFDerivWithinAt.mfderivWithin
-/

#print MDifferentiable.mfderivWithin /-
theorem MDifferentiable.mfderivWithin (h : MDifferentiableAt I I' f x)
    (hxs : UniqueMDiffWithinAt I s x) : mfderivWithin I I' f s x = mfderiv I I' f x :=
  by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact h.has_mfderiv_at.has_mfderiv_within_at
#align mdifferentiable.mfderiv_within MDifferentiable.mfderivWithin
-/

#print mfderivWithin_subset /-
theorem mfderivWithin_subset (st : s ⊆ t) (hs : UniqueMDiffWithinAt I s x)
    (h : MDifferentiableWithinAt I I' f t x) :
    mfderivWithin I I' f s x = mfderivWithin I I' f t x :=
  ((MDifferentiableWithinAt.hasMFDerivWithinAt h).mono st).mfderivWithin hs
#align mfderiv_within_subset mfderivWithin_subset
-/

#print MDifferentiableWithinAt.mono /-
theorem MDifferentiableWithinAt.mono (hst : s ⊆ t) (h : MDifferentiableWithinAt I I' f t x) :
    MDifferentiableWithinAt I I' f s x :=
  ⟨ContinuousWithinAt.mono h.1 hst,
    DifferentiableWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩
#align mdifferentiable_within_at.mono MDifferentiableWithinAt.mono
-/

#print mdifferentiableWithinAt_univ /-
theorem mdifferentiableWithinAt_univ :
    MDifferentiableWithinAt I I' f univ x ↔ MDifferentiableAt I I' f x := by
  simp only [MDifferentiableWithinAt, MDifferentiableAt, continuousWithinAt_univ, mfld_simps]
#align mdifferentiable_within_at_univ mdifferentiableWithinAt_univ
-/

#print mdifferentiableWithinAt_inter /-
theorem mdifferentiableWithinAt_inter (ht : t ∈ 𝓝 x) :
    MDifferentiableWithinAt I I' f (s ∩ t) x ↔ MDifferentiableWithinAt I I' f s x :=
  by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt, extChartAt_preimage_inter_eq,
    differentiableWithinAt_inter, continuousWithinAt_inter ht]
  exact extChartAt_preimage_mem_nhds I x ht
#align mdifferentiable_within_at_inter mdifferentiableWithinAt_inter
-/

#print mdifferentiableWithinAt_inter' /-
theorem mdifferentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    MDifferentiableWithinAt I I' f (s ∩ t) x ↔ MDifferentiableWithinAt I I' f s x :=
  by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt, extChartAt_preimage_inter_eq,
    differentiableWithinAt_inter', continuousWithinAt_inter' ht]
  exact extChartAt_preimage_mem_nhdsWithin I x ht
#align mdifferentiable_within_at_inter' mdifferentiableWithinAt_inter'
-/

#print MDifferentiableAt.mdifferentiableWithinAt /-
theorem MDifferentiableAt.mdifferentiableWithinAt (h : MDifferentiableAt I I' f x) :
    MDifferentiableWithinAt I I' f s x :=
  MDifferentiableWithinAt.mono (subset_univ _) (mdifferentiableWithinAt_univ.2 h)
#align mdifferentiable_at.mdifferentiable_within_at MDifferentiableAt.mdifferentiableWithinAt
-/

#print MDifferentiableWithinAt.mdifferentiableAt /-
theorem MDifferentiableWithinAt.mdifferentiableAt (h : MDifferentiableWithinAt I I' f s x)
    (hs : s ∈ 𝓝 x) : MDifferentiableAt I I' f x :=
  by
  have : s = univ ∩ s := by rw [univ_inter]
  rwa [this, mdifferentiableWithinAt_inter hs, mdifferentiableWithinAt_univ] at h
#align mdifferentiable_within_at.mdifferentiable_at MDifferentiableWithinAt.mdifferentiableAt
-/

#print MDifferentiableOn.mono /-
theorem MDifferentiableOn.mono (h : MDifferentiableOn I I' f t) (st : s ⊆ t) :
    MDifferentiableOn I I' f s := fun x hx => (h x (st hx)).mono st
#align mdifferentiable_on.mono MDifferentiableOn.mono
-/

#print mdifferentiableOn_univ /-
theorem mdifferentiableOn_univ : MDifferentiableOn I I' f univ ↔ MDifferentiable I I' f := by
  simp only [MDifferentiableOn, mdifferentiableWithinAt_univ, mfld_simps]; rfl
#align mdifferentiable_on_univ mdifferentiableOn_univ
-/

#print MDifferentiable.mdifferentiableOn /-
theorem MDifferentiable.mdifferentiableOn (h : MDifferentiable I I' f) :
    MDifferentiableOn I I' f s :=
  (mdifferentiableOn_univ.2 h).mono (subset_univ _)
#align mdifferentiable.mdifferentiable_on MDifferentiable.mdifferentiableOn
-/

#print mdifferentiableOn_of_locally_mdifferentiableOn /-
theorem mdifferentiableOn_of_locally_mdifferentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ MDifferentiableOn I I' f (s ∩ u)) :
    MDifferentiableOn I I' f s := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (mdifferentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)
#align mdifferentiable_on_of_locally_mdifferentiable_on mdifferentiableOn_of_locally_mdifferentiableOn
-/

#print mfderivWithin_univ /-
@[simp, mfld_simps]
theorem mfderivWithin_univ : mfderivWithin I I' f univ = mfderiv I I' f :=
  by
  ext x : 1
  simp only [mfderivWithin, mfderiv, mfld_simps]
  rw [mdifferentiableWithinAt_univ]
#align mfderiv_within_univ mfderivWithin_univ
-/

#print mfderivWithin_inter /-
theorem mfderivWithin_inter (ht : t ∈ 𝓝 x) :
    mfderivWithin I I' f (s ∩ t) x = mfderivWithin I I' f s x := by
  rw [mfderivWithin, mfderivWithin, extChartAt_preimage_inter_eq, mdifferentiableWithinAt_inter ht,
    fderivWithin_inter (extChartAt_preimage_mem_nhds I x ht)]
#align mfderiv_within_inter mfderivWithin_inter
-/

#print mdifferentiableAt_iff_of_mem_source /-
theorem mdifferentiableAt_iff_of_mem_source {x' : M} {y : M'}
    (hx : x' ∈ (ChartedSpace.chartAt H x).source) (hy : f x' ∈ (ChartedSpace.chartAt H' y).source) :
    MDifferentiableAt I I' f x' ↔
      ContinuousAt f x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (Set.range I)
          ((extChartAt I x) x') :=
  mdifferentiableWithinAt_univ.symm.trans <|
    (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans <| by
      rw [continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
#align mdifferentiable_at_iff_of_mem_source mdifferentiableAt_iff_of_mem_source
-/

/-! ### Deriving continuity from differentiability on manifolds -/


#print HasMFDerivWithinAt.continuousWithinAt /-
theorem HasMFDerivWithinAt.continuousWithinAt (h : HasMFDerivWithinAt I I' f s x f') :
    ContinuousWithinAt f s x :=
  h.1
#align has_mfderiv_within_at.continuous_within_at HasMFDerivWithinAt.continuousWithinAt
-/

#print HasMFDerivAt.continuousAt /-
theorem HasMFDerivAt.continuousAt (h : HasMFDerivAt I I' f x f') : ContinuousAt f x :=
  h.1
#align has_mfderiv_at.continuous_at HasMFDerivAt.continuousAt
-/

#print MDifferentiableWithinAt.continuousWithinAt /-
theorem MDifferentiableWithinAt.continuousWithinAt (h : MDifferentiableWithinAt I I' f s x) :
    ContinuousWithinAt f s x :=
  h.1
#align mdifferentiable_within_at.continuous_within_at MDifferentiableWithinAt.continuousWithinAt
-/

#print MDifferentiableAt.continuousAt /-
theorem MDifferentiableAt.continuousAt (h : MDifferentiableAt I I' f x) : ContinuousAt f x :=
  h.1
#align mdifferentiable_at.continuous_at MDifferentiableAt.continuousAt
-/

#print MDifferentiableOn.continuousOn /-
theorem MDifferentiableOn.continuousOn (h : MDifferentiableOn I I' f s) : ContinuousOn f s :=
  fun x hx => (h x hx).ContinuousWithinAt
#align mdifferentiable_on.continuous_on MDifferentiableOn.continuousOn
-/

#print MDifferentiable.continuous /-
theorem MDifferentiable.continuous (h : MDifferentiable I I' f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).ContinuousAt
#align mdifferentiable.continuous MDifferentiable.continuous
-/

#print tangentMapWithin_subset /-
theorem tangentMapWithin_subset {p : TangentBundle I M} (st : s ⊆ t)
    (hs : UniqueMDiffWithinAt I s p.1) (h : MDifferentiableWithinAt I I' f t p.1) :
    tangentMapWithin I I' f s p = tangentMapWithin I I' f t p :=
  by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_subset st hs h]
#align tangent_map_within_subset tangentMapWithin_subset
-/

#print tangentMapWithin_univ /-
theorem tangentMapWithin_univ : tangentMapWithin I I' f univ = tangentMap I I' f := by ext p : 1;
  simp only [tangentMapWithin, tangentMap, mfld_simps]
#align tangent_map_within_univ tangentMapWithin_univ
-/

#print tangentMapWithin_eq_tangentMap /-
theorem tangentMapWithin_eq_tangentMap {p : TangentBundle I M} (hs : UniqueMDiffWithinAt I s p.1)
    (h : MDifferentiableAt I I' f p.1) : tangentMapWithin I I' f s p = tangentMap I I' f p :=
  by
  rw [← mdifferentiableWithinAt_univ] at h
  rw [← tangentMapWithin_univ]
  exact tangentMapWithin_subset (subset_univ _) hs h
#align tangent_map_within_eq_tangent_map tangentMapWithin_eq_tangentMap
-/

#print tangentMapWithin_proj /-
@[simp, mfld_simps]
theorem tangentMapWithin_proj {p : TangentBundle I M} :
    (tangentMapWithin I I' f s p).proj = f p.proj :=
  rfl
#align tangent_map_within_proj tangentMapWithin_proj
-/

#print tangentMap_proj /-
@[simp, mfld_simps]
theorem tangentMap_proj {p : TangentBundle I M} : (tangentMap I I' f p).proj = f p.proj :=
  rfl
#align tangent_map_proj tangentMap_proj
-/

#print MDifferentiableWithinAt.prod_mk /-
theorem MDifferentiableWithinAt.prod_mk {f : M → M'} {g : M → M''}
    (hf : MDifferentiableWithinAt I I' f s x) (hg : MDifferentiableWithinAt I I'' g s x) :
    MDifferentiableWithinAt I (I'.Prod I'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.Prod hg.1, hf.2.Prod hg.2⟩
#align mdifferentiable_within_at.prod_mk MDifferentiableWithinAt.prod_mk
-/

#print MDifferentiableAt.prod_mk /-
theorem MDifferentiableAt.prod_mk {f : M → M'} {g : M → M''} (hf : MDifferentiableAt I I' f x)
    (hg : MDifferentiableAt I I'' g x) :
    MDifferentiableAt I (I'.Prod I'') (fun x => (f x, g x)) x :=
  ⟨hf.1.Prod hg.1, hf.2.Prod hg.2⟩
#align mdifferentiable_at.prod_mk MDifferentiableAt.prod_mk
-/

#print MDifferentiableOn.prod_mk /-
theorem MDifferentiableOn.prod_mk {f : M → M'} {g : M → M''} (hf : MDifferentiableOn I I' f s)
    (hg : MDifferentiableOn I I'' g s) :
    MDifferentiableOn I (I'.Prod I'') (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prod_mk (hg x hx)
#align mdifferentiable_on.prod_mk MDifferentiableOn.prod_mk
-/

#print MDifferentiable.prod_mk /-
theorem MDifferentiable.prod_mk {f : M → M'} {g : M → M''} (hf : MDifferentiable I I' f)
    (hg : MDifferentiable I I'' g) : MDifferentiable I (I'.Prod I'') fun x => (f x, g x) := fun x =>
  (hf x).prod_mk (hg x)
#align mdifferentiable.prod_mk MDifferentiable.prod_mk
-/

#print MDifferentiableWithinAt.prod_mk_space /-
theorem MDifferentiableWithinAt.prod_mk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableWithinAt I 𝓘(𝕜, E') f s x)
    (hg : MDifferentiableWithinAt I 𝓘(𝕜, E'') g s x) :
    MDifferentiableWithinAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s x :=
  ⟨hf.1.Prod hg.1, hf.2.Prod hg.2⟩
#align mdifferentiable_within_at.prod_mk_space MDifferentiableWithinAt.prod_mk_space
-/

#print MDifferentiableAt.prod_mk_space /-
theorem MDifferentiableAt.prod_mk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableAt I 𝓘(𝕜, E') f x) (hg : MDifferentiableAt I 𝓘(𝕜, E'') g x) :
    MDifferentiableAt I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) x :=
  ⟨hf.1.Prod hg.1, hf.2.Prod hg.2⟩
#align mdifferentiable_at.prod_mk_space MDifferentiableAt.prod_mk_space
-/

#print MDifferentiableOn.prod_mk_space /-
theorem MDifferentiableOn.prod_mk_space {f : M → E'} {g : M → E''}
    (hf : MDifferentiableOn I 𝓘(𝕜, E') f s) (hg : MDifferentiableOn I 𝓘(𝕜, E'') g s) :
    MDifferentiableOn I 𝓘(𝕜, E' × E'') (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prod_mk_space (hg x hx)
#align mdifferentiable_on.prod_mk_space MDifferentiableOn.prod_mk_space
-/

#print MDifferentiable.prod_mk_space /-
theorem MDifferentiable.prod_mk_space {f : M → E'} {g : M → E''} (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E'') g) : MDifferentiable I 𝓘(𝕜, E' × E'') fun x => (f x, g x) :=
  fun x => (hf x).prod_mk_space (hg x)
#align mdifferentiable.prod_mk_space MDifferentiable.prod_mk_space
-/

/-! ### Congruence lemmas for derivatives on manifolds -/


#print HasMFDerivWithinAt.congr_of_eventuallyEq /-
theorem HasMFDerivWithinAt.congr_of_eventuallyEq (h : HasMFDerivWithinAt I I' f s x f')
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasMFDerivWithinAt I I' f₁ s x f' :=
  by
  refine' ⟨ContinuousWithinAt.congr_of_eventuallyEq h.1 h₁ hx, _⟩
  apply HasFDerivWithinAt.congr_of_eventuallyEq h.2
  · have :
      (extChartAt I x).symm ⁻¹' {y | f₁ y = f y} ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin I x h₁
    apply Filter.mem_of_superset this fun y => _
    simp (config := { contextual := true }) only [hx, mfld_simps]
  · simp only [hx, mfld_simps]
#align has_mfderiv_within_at.congr_of_eventually_eq HasMFDerivWithinAt.congr_of_eventuallyEq
-/

#print HasMFDerivWithinAt.congr_mono /-
theorem HasMFDerivWithinAt.congr_mono (h : HasMFDerivWithinAt I I' f s x f')
    (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasMFDerivWithinAt I I' f₁ t x f' :=
  (h.mono h₁).congr_of_eventuallyEq (Filter.mem_inf_of_right ht) hx
#align has_mfderiv_within_at.congr_mono HasMFDerivWithinAt.congr_mono
-/

#print HasMFDerivAt.congr_of_eventuallyEq /-
theorem HasMFDerivAt.congr_of_eventuallyEq (h : HasMFDerivAt I I' f x f') (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasMFDerivAt I I' f₁ x f' :=
  by
  rw [← hasMFDerivWithinAt_univ] at h ⊢
  apply h.congr_of_eventually_eq _ (mem_of_mem_nhds h₁ : _)
  rwa [nhdsWithin_univ]
#align has_mfderiv_at.congr_of_eventually_eq HasMFDerivAt.congr_of_eventuallyEq
-/

#print MDifferentiableWithinAt.congr_of_eventuallyEq /-
theorem MDifferentiableWithinAt.congr_of_eventuallyEq (h : MDifferentiableWithinAt I I' f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : MDifferentiableWithinAt I I' f₁ s x :=
  (h.HasMFDerivWithinAt.congr_of_eventuallyEq h₁ hx).MDifferentiableWithinAt
#align mdifferentiable_within_at.congr_of_eventually_eq MDifferentiableWithinAt.congr_of_eventuallyEq
-/

variable (I I')

#print Filter.EventuallyEq.mdifferentiableWithinAt_iff /-
theorem Filter.EventuallyEq.mdifferentiableWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    MDifferentiableWithinAt I I' f s x ↔ MDifferentiableWithinAt I I' f₁ s x :=
  by
  constructor
  · intro h
    apply h.congr_of_eventually_eq h₁ hx
  · intro h
    apply h.congr_of_eventually_eq _ hx.symm
    apply h₁.mono
    intro y
    apply Eq.symm
#align filter.eventually_eq.mdifferentiable_within_at_iff Filter.EventuallyEq.mdifferentiableWithinAt_iff
-/

variable {I I'}

#print MDifferentiableWithinAt.congr_mono /-
theorem MDifferentiableWithinAt.congr_mono (h : MDifferentiableWithinAt I I' f s x)
    (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) :
    MDifferentiableWithinAt I I' f₁ t x :=
  (HasMFDerivWithinAt.congr_mono h.HasMFDerivWithinAt ht hx h₁).MDifferentiableWithinAt
#align mdifferentiable_within_at.congr_mono MDifferentiableWithinAt.congr_mono
-/

#print MDifferentiableWithinAt.congr /-
theorem MDifferentiableWithinAt.congr (h : MDifferentiableWithinAt I I' f s x)
    (ht : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) : MDifferentiableWithinAt I I' f₁ s x :=
  (HasMFDerivWithinAt.congr_mono h.HasMFDerivWithinAt ht hx (Subset.refl _)).MDifferentiableWithinAt
#align mdifferentiable_within_at.congr MDifferentiableWithinAt.congr
-/

#print MDifferentiableOn.congr_mono /-
theorem MDifferentiableOn.congr_mono (h : MDifferentiableOn I I' f s) (h' : ∀ x ∈ t, f₁ x = f x)
    (h₁ : t ⊆ s) : MDifferentiableOn I I' f₁ t := fun x hx =>
  (h x (h₁ hx)).congr_mono h' (h' x hx) h₁
#align mdifferentiable_on.congr_mono MDifferentiableOn.congr_mono
-/

#print MDifferentiableAt.congr_of_eventuallyEq /-
theorem MDifferentiableAt.congr_of_eventuallyEq (h : MDifferentiableAt I I' f x)
    (hL : f₁ =ᶠ[𝓝 x] f) : MDifferentiableAt I I' f₁ x :=
  (h.HasMFDerivAt.congr_of_eventuallyEq hL).MDifferentiableAt
#align mdifferentiable_at.congr_of_eventually_eq MDifferentiableAt.congr_of_eventuallyEq
-/

#print MDifferentiableWithinAt.mfderivWithin_congr_mono /-
theorem MDifferentiableWithinAt.mfderivWithin_congr_mono (h : MDifferentiableWithinAt I I' f s x)
    (hs : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : UniqueMDiffWithinAt I t x) (h₁ : t ⊆ s) :
    mfderivWithin I I' f₁ t x = (mfderivWithin I I' f s x : _) :=
  (HasMFDerivWithinAt.congr_mono h.HasMFDerivWithinAt hs hx h₁).mfderivWithin hxt
#align mdifferentiable_within_at.mfderiv_within_congr_mono MDifferentiableWithinAt.mfderivWithin_congr_mono
-/

#print Filter.EventuallyEq.mfderivWithin_eq /-
theorem Filter.EventuallyEq.mfderivWithin_eq (hs : UniqueMDiffWithinAt I s x) (hL : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : mfderivWithin I I' f₁ s x = (mfderivWithin I I' f s x : _) :=
  by
  by_cases h : MDifferentiableWithinAt I I' f s x
  · exact (h.has_mfderiv_within_at.congr_of_eventuallyEq hL hx).mfderivWithin hs
  · unfold mfderivWithin
    rw [if_neg h, if_neg]
    rwa [← hL.mdifferentiable_within_at_iff I I' hx]
#align filter.eventually_eq.mfderiv_within_eq Filter.EventuallyEq.mfderivWithin_eq
-/

#print mfderivWithin_congr /-
theorem mfderivWithin_congr (hs : UniqueMDiffWithinAt I s x) (hL : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : mfderivWithin I I' f₁ s x = (mfderivWithin I I' f s x : _) :=
  Filter.EventuallyEq.mfderivWithin_eq hs (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx
#align mfderiv_within_congr mfderivWithin_congr
-/

#print tangentMapWithin_congr /-
theorem tangentMapWithin_congr (h : ∀ x ∈ s, f x = f₁ x) (p : TangentBundle I M) (hp : p.1 ∈ s)
    (hs : UniqueMDiffWithinAt I s p.1) :
    tangentMapWithin I I' f s p = tangentMapWithin I I' f₁ s p :=
  by
  simp only [tangentMapWithin, h p.1 hp, true_and_iff, eq_self_iff_true, heq_iff_eq]
  congr 1
  exact mfderivWithin_congr hs h (h _ hp)
#align tangent_map_within_congr tangentMapWithin_congr
-/

#print Filter.EventuallyEq.mfderiv_eq /-
theorem Filter.EventuallyEq.mfderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) :
    mfderiv I I' f₁ x = (mfderiv I I' f x : _) :=
  by
  have A : f₁ x = f x := (mem_of_mem_nhds hL : _)
  rw [← mfderivWithin_univ, ← mfderivWithin_univ]
  rw [← nhdsWithin_univ] at hL
  exact hL.mfderiv_within_eq (uniqueMDiffWithinAt_univ I) A
#align filter.eventually_eq.mfderiv_eq Filter.EventuallyEq.mfderiv_eq
-/

#print mfderiv_congr_point /-
/-- A congruence lemma for `mfderiv`, (ab)using the fact that `tangent_space I' (f x)` is
definitionally equal to `E'`. -/
theorem mfderiv_congr_point {x' : M} (h : x = x') :
    @Eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f x') := by subst h
#align mfderiv_congr_point mfderiv_congr_point
-/

#print mfderiv_congr /-
/-- A congruence lemma for `mfderiv`, (ab)using the fact that `tangent_space I' (f x)` is
definitionally equal to `E'`. -/
theorem mfderiv_congr {f' : M → M'} (h : f = f') :
    @Eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f' x) := by subst h
#align mfderiv_congr mfderiv_congr
-/

/-! ### Composition lemmas -/


#print writtenInExtChartAt_comp /-
theorem writtenInExtChartAt_comp (h : ContinuousWithinAt f s x) :
    {y |
        writtenInExtChartAt I I'' x (g ∘ f) y =
          (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f) y} ∈
      𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
  by
  apply
    @Filter.mem_of_superset _ _ (f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source) _
      (extChartAt_preimage_mem_nhdsWithin I x
        (h.preimage_mem_nhds_within (extChartAt_source_mem_nhds _ _)))
  mfld_set_tac
#align written_in_ext_chart_comp writtenInExtChartAt_comp
-/

variable (x)

#print HasMFDerivWithinAt.comp /-
theorem HasMFDerivWithinAt.comp (hg : HasMFDerivWithinAt I' I'' g u (f x) g')
    (hf : HasMFDerivWithinAt I I' f s x f') (hst : s ⊆ f ⁻¹' u) :
    HasMFDerivWithinAt I I'' (g ∘ f) s x (g'.comp f') :=
  by
  refine' ⟨ContinuousWithinAt.comp hg.1 hf.1 hst, _⟩
  have A :
    HasFDerivWithinAt (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f)
      (ContinuousLinearMap.comp g' f' : E →L[𝕜] E'') ((extChartAt I x).symm ⁻¹' s ∩ range I)
      ((extChartAt I x) x) :=
    by
    have :
      (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' (f x)).source) ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin I x
        (hf.1.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _ _))
    unfold HasMFDerivWithinAt at *
    rw [← hasFDerivWithinAt_inter' this, ← extChartAt_preimage_inter_eq] at hf ⊢
    have : writtenInExtChartAt I I' x f ((extChartAt I x) x) = (extChartAt I' (f x)) (f x) := by
      simp only [mfld_simps]
    rw [← this] at hg
    apply HasFDerivWithinAt.comp ((extChartAt I x) x) hg.2 hf.2 _
    intro y hy
    simp only [mfld_simps] at hy
    have : f (((chart_at H x).symm : H → M) (I.symm y)) ∈ u := hst hy.1.1
    simp only [hy, this, mfld_simps]
  apply A.congr_of_eventually_eq (writtenInExtChartAt_comp hf.1)
  simp only [mfld_simps]
#align has_mfderiv_within_at.comp HasMFDerivWithinAt.comp
-/

#print HasMFDerivAt.comp /-
/-- The chain rule. -/
theorem HasMFDerivAt.comp (hg : HasMFDerivAt I' I'' g (f x) g') (hf : HasMFDerivAt I I' f x f') :
    HasMFDerivAt I I'' (g ∘ f) x (g'.comp f') :=
  by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ
#align has_mfderiv_at.comp HasMFDerivAt.comp
-/

#print HasMFDerivAt.comp_hasMFDerivWithinAt /-
theorem HasMFDerivAt.comp_hasMFDerivWithinAt (hg : HasMFDerivAt I' I'' g (f x) g')
    (hf : HasMFDerivWithinAt I I' f s x f') : HasMFDerivWithinAt I I'' (g ∘ f) s x (g'.comp f') :=
  by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ
#align has_mfderiv_at.comp_has_mfderiv_within_at HasMFDerivAt.comp_hasMFDerivWithinAt
-/

#print MDifferentiableWithinAt.comp /-
theorem MDifferentiableWithinAt.comp (hg : MDifferentiableWithinAt I' I'' g u (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x :=
  by
  rcases hf.2 with ⟨f', hf'⟩
  have F : HasMFDerivWithinAt I I' f s x f' := ⟨hf.1, hf'⟩
  rcases hg.2 with ⟨g', hg'⟩
  have G : HasMFDerivWithinAt I' I'' g u (f x) g' := ⟨hg.1, hg'⟩
  exact (HasMFDerivWithinAt.comp x G F h).MDifferentiableWithinAt
#align mdifferentiable_within_at.comp MDifferentiableWithinAt.comp
-/

#print MDifferentiableAt.comp /-
theorem MDifferentiableAt.comp (hg : MDifferentiableAt I' I'' g (f x))
    (hf : MDifferentiableAt I I' f x) : MDifferentiableAt I I'' (g ∘ f) x :=
  (hg.HasMFDerivAt.comp x hf.HasMFDerivAt).MDifferentiableAt
#align mdifferentiable_at.comp MDifferentiableAt.comp
-/

#print mfderivWithin_comp /-
theorem mfderivWithin_comp (hg : MDifferentiableWithinAt I' I'' g u (f x))
    (hf : MDifferentiableWithinAt I I' f s x) (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I'' (g ∘ f) s x =
      (mfderivWithin I' I'' g u (f x)).comp (mfderivWithin I I' f s x) :=
  by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact HasMFDerivWithinAt.comp x hg.has_mfderiv_within_at hf.has_mfderiv_within_at h
#align mfderiv_within_comp mfderivWithin_comp
-/

#print mfderiv_comp /-
theorem mfderiv_comp (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableAt I I' f x) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) :=
  by
  apply HasMFDerivAt.mfderiv
  exact HasMFDerivAt.comp x hg.has_mfderiv_at hf.has_mfderiv_at
#align mfderiv_comp mfderiv_comp
-/

#print mfderiv_comp_of_eq /-
theorem mfderiv_comp_of_eq {x : M} {y : M'} (hg : MDifferentiableAt I' I'' g y)
    (hf : MDifferentiableAt I I' f x) (hy : f x = y) :
    mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) := by subst hy;
  exact mfderiv_comp x hg hf
#align mfderiv_comp_of_eq mfderiv_comp_of_eq
-/

#print MDifferentiableOn.comp /-
theorem MDifferentiableOn.comp (hg : MDifferentiableOn I' I'' g u) (hf : MDifferentiableOn I I' f s)
    (st : s ⊆ f ⁻¹' u) : MDifferentiableOn I I'' (g ∘ f) s := fun x hx =>
  MDifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st
#align mdifferentiable_on.comp MDifferentiableOn.comp
-/

#print MDifferentiable.comp /-
theorem MDifferentiable.comp (hg : MDifferentiable I' I'' g) (hf : MDifferentiable I I' f) :
    MDifferentiable I I'' (g ∘ f) := fun x => MDifferentiableAt.comp x (hg (f x)) (hf x)
#align mdifferentiable.comp MDifferentiable.comp
-/

#print tangentMapWithin_comp_at /-
theorem tangentMapWithin_comp_at (p : TangentBundle I M)
    (hg : MDifferentiableWithinAt I' I'' g u (f p.1)) (hf : MDifferentiableWithinAt I I' f s p.1)
    (h : s ⊆ f ⁻¹' u) (hps : UniqueMDiffWithinAt I s p.1) :
    tangentMapWithin I I'' (g ∘ f) s p =
      tangentMapWithin I' I'' g u (tangentMapWithin I I' f s p) :=
  by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_comp p.1 hg hf h hps]
  rfl
#align tangent_map_within_comp_at tangentMapWithin_comp_at
-/

#print tangentMap_comp_at /-
theorem tangentMap_comp_at (p : TangentBundle I M) (hg : MDifferentiableAt I' I'' g (f p.1))
    (hf : MDifferentiableAt I I' f p.1) :
    tangentMap I I'' (g ∘ f) p = tangentMap I' I'' g (tangentMap I I' f p) :=
  by
  simp only [tangentMap, mfld_simps]
  rw [mfderiv_comp p.1 hg hf]
  rfl
#align tangent_map_comp_at tangentMap_comp_at
-/

#print tangentMap_comp /-
theorem tangentMap_comp (hg : MDifferentiable I' I'' g) (hf : MDifferentiable I I' f) :
    tangentMap I I'' (g ∘ f) = tangentMap I' I'' g ∘ tangentMap I I' f := by ext p : 1;
  exact tangentMap_comp_at _ (hg _) (hf _)
#align tangent_map_comp tangentMap_comp
-/

end DerivativesProperties

section MfderivFderiv

/-!
### Relations between vector space derivative and manifold derivative

The manifold derivative `mfderiv`, when considered on the model vector space with its trivial
manifold structure, coincides with the usual Frechet derivative `fderiv`. In this section, we prove
this and related statements.
-/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {f : E → E'}
  {s : Set E} {x : E}

#print uniqueMDiffWithinAt_iff_uniqueDiffWithinAt /-
theorem uniqueMDiffWithinAt_iff_uniqueDiffWithinAt :
    UniqueMDiffWithinAt 𝓘(𝕜, E) s x ↔ UniqueDiffWithinAt 𝕜 s x := by
  simp only [UniqueMDiffWithinAt, mfld_simps]
#align unique_mdiff_within_at_iff_unique_diff_within_at uniqueMDiffWithinAt_iff_uniqueDiffWithinAt
-/

alias ⟨UniqueMDiffWithinAt.uniqueDiffWithinAt, UniqueDiffWithinAt.uniqueMDiffWithinAt⟩ :=
  uniqueMDiffWithinAt_iff_uniqueDiffWithinAt
#align unique_mdiff_within_at.unique_diff_within_at UniqueMDiffWithinAt.uniqueDiffWithinAt
#align unique_diff_within_at.unique_mdiff_within_at UniqueDiffWithinAt.uniqueMDiffWithinAt

#print uniqueMDiffOn_iff_uniqueDiffOn /-
theorem uniqueMDiffOn_iff_uniqueDiffOn : UniqueMDiffOn 𝓘(𝕜, E) s ↔ UniqueDiffOn 𝕜 s := by
  simp [UniqueMDiffOn, UniqueDiffOn, uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
#align unique_mdiff_on_iff_unique_diff_on uniqueMDiffOn_iff_uniqueDiffOn
-/

alias ⟨UniqueMDiffOn.uniqueDiffOn, UniqueDiffOn.uniqueMDiffOn⟩ := uniqueMDiffOn_iff_uniqueDiffOn
#align unique_mdiff_on.unique_diff_on UniqueMDiffOn.uniqueDiffOn
#align unique_diff_on.unique_mdiff_on UniqueDiffOn.uniqueMDiffOn

#print writtenInExtChartAt_model_space /-
@[simp, mfld_simps]
theorem writtenInExtChartAt_model_space : writtenInExtChartAt 𝓘(𝕜, E) 𝓘(𝕜, E') x f = f :=
  rfl
#align written_in_ext_chart_model_space writtenInExtChartAt_model_space
-/

#print hasMFDerivWithinAt_iff_hasFDerivWithinAt /-
theorem hasMFDerivWithinAt_iff_hasFDerivWithinAt {f'} :
    HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f' ↔ HasFDerivWithinAt f f' s x := by
  simpa only [HasMFDerivWithinAt, and_iff_right_iff_imp, mfld_simps] using
    HasFDerivWithinAt.continuousWithinAt
#align has_mfderiv_within_at_iff_has_fderiv_within_at hasMFDerivWithinAt_iff_hasFDerivWithinAt
-/

alias ⟨HasMFDerivWithinAt.hasFDerivWithinAt, HasFDerivWithinAt.hasMFDerivWithinAt⟩ :=
  hasMFDerivWithinAt_iff_hasFDerivWithinAt
#align has_mfderiv_within_at.has_fderiv_within_at HasMFDerivWithinAt.hasFDerivWithinAt
#align has_fderiv_within_at.has_mfderiv_within_at HasFDerivWithinAt.hasMFDerivWithinAt

#print hasMFDerivAt_iff_hasFDerivAt /-
theorem hasMFDerivAt_iff_hasFDerivAt {f'} :
    HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f' ↔ HasFDerivAt f f' x := by
  rw [← hasMFDerivWithinAt_univ, hasMFDerivWithinAt_iff_hasFDerivWithinAt, hasFDerivWithinAt_univ]
#align has_mfderiv_at_iff_has_fderiv_at hasMFDerivAt_iff_hasFDerivAt
-/

alias ⟨HasMFDerivAt.hasFDerivAt, HasFDerivAt.hasMFDerivAt⟩ := hasMFDerivAt_iff_hasFDerivAt
#align has_mfderiv_at.has_fderiv_at HasMFDerivAt.hasFDerivAt
#align has_fderiv_at.has_mfderiv_at HasFDerivAt.hasMFDerivAt

#print mdifferentiableWithinAt_iff_differentiableWithinAt /-
/-- For maps between vector spaces, `mdifferentiable_within_at` and `fdifferentiable_within_at`
coincide -/
theorem mdifferentiableWithinAt_iff_differentiableWithinAt :
    MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  by
  simp only [MDifferentiableWithinAt, mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.ContinuousWithinAt, H⟩⟩
#align mdifferentiable_within_at_iff_differentiable_within_at mdifferentiableWithinAt_iff_differentiableWithinAt
-/

alias ⟨MDifferentiableWithinAt.differentiableWithinAt,
  DifferentiableWithinAt.mdifferentiableWithinAt⟩ :=
  mdifferentiableWithinAt_iff_differentiableWithinAt
#align mdifferentiable_within_at.differentiable_within_at MDifferentiableWithinAt.differentiableWithinAt
#align differentiable_within_at.mdifferentiable_within_at DifferentiableWithinAt.mdifferentiableWithinAt

#print mdifferentiableAt_iff_differentiableAt /-
/-- For maps between vector spaces, `mdifferentiable_at` and `differentiable_at` coincide -/
theorem mdifferentiableAt_iff_differentiableAt :
    MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x ↔ DifferentiableAt 𝕜 f x :=
  by
  simp only [MDifferentiableAt, differentiableWithinAt_univ, mfld_simps]
  exact ⟨fun H => H.2, fun H => ⟨H.ContinuousAt, H⟩⟩
#align mdifferentiable_at_iff_differentiable_at mdifferentiableAt_iff_differentiableAt
-/

alias ⟨MDifferentiableAt.differentiableAt, DifferentiableAt.mdifferentiableAt⟩ :=
  mdifferentiableAt_iff_differentiableAt
#align mdifferentiable_at.differentiable_at MDifferentiableAt.differentiableAt
#align differentiable_at.mdifferentiable_at DifferentiableAt.mdifferentiableAt

#print mdifferentiableOn_iff_differentiableOn /-
/-- For maps between vector spaces, `mdifferentiable_on` and `differentiable_on` coincide -/
theorem mdifferentiableOn_iff_differentiableOn :
    MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s ↔ DifferentiableOn 𝕜 f s := by
  simp only [MDifferentiableOn, DifferentiableOn,
    mdifferentiableWithinAt_iff_differentiableWithinAt]
#align mdifferentiable_on_iff_differentiable_on mdifferentiableOn_iff_differentiableOn
-/

alias ⟨MDifferentiableOn.differentiableOn, DifferentiableOn.mdifferentiableOn⟩ :=
  mdifferentiableOn_iff_differentiableOn
#align mdifferentiable_on.differentiable_on MDifferentiableOn.differentiableOn
#align differentiable_on.mdifferentiable_on DifferentiableOn.mdifferentiableOn

#print mdifferentiable_iff_differentiable /-
/-- For maps between vector spaces, `mdifferentiable` and `differentiable` coincide -/
theorem mdifferentiable_iff_differentiable :
    MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f ↔ Differentiable 𝕜 f := by
  simp only [MDifferentiable, Differentiable, mdifferentiableAt_iff_differentiableAt]
#align mdifferentiable_iff_differentiable mdifferentiable_iff_differentiable
-/

alias ⟨MDifferentiable.differentiable, Differentiable.mdifferentiable⟩ :=
  mdifferentiable_iff_differentiable
#align mdifferentiable.differentiable MDifferentiable.differentiable
#align differentiable.mdifferentiable Differentiable.mdifferentiable

#print mfderivWithin_eq_fderivWithin /-
/-- For maps between vector spaces, `mfderiv_within` and `fderiv_within` coincide -/
@[simp]
theorem mfderivWithin_eq_fderivWithin :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = fderivWithin 𝕜 f s x :=
  by
  by_cases h : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x
  · simp only [mfderivWithin, h, if_pos, mfld_simps]
  · simp only [mfderivWithin, h, if_neg, not_false_iff]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt] at h
    exact (fderivWithin_zero_of_not_differentiableWithinAt h).symm
#align mfderiv_within_eq_fderiv_within mfderivWithin_eq_fderivWithin
-/

#print mfderiv_eq_fderiv /-
/-- For maps between vector spaces, `mfderiv` and `fderiv` coincide -/
@[simp]
theorem mfderiv_eq_fderiv : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = fderiv 𝕜 f x :=
  by
  rw [← mfderivWithin_univ, ← fderivWithin_univ]
  exact mfderivWithin_eq_fderivWithin
#align mfderiv_eq_fderiv mfderiv_eq_fderiv
-/

end MfderivFderiv

section SpecificFunctions

/-! ### Differentiability of specific functions -/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M'] {E'' : Type _} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type _} [TopologicalSpace H''] (I'' : ModelWithCorners 𝕜 E'' H'') {M'' : Type _}
  [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I'' M'']

namespace ContinuousLinearMap

variable (f : E →L[𝕜] E') {s : Set E} {x : E}

#print ContinuousLinearMap.hasMFDerivWithinAt /-
protected theorem hasMFDerivWithinAt : HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f :=
  f.HasFDerivWithinAt.HasMFDerivWithinAt
#align continuous_linear_map.has_mfderiv_within_at ContinuousLinearMap.hasMFDerivWithinAt
-/

#print ContinuousLinearMap.hasMFDerivAt /-
protected theorem hasMFDerivAt : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x f :=
  f.HasFDerivAt.HasMFDerivAt
#align continuous_linear_map.has_mfderiv_at ContinuousLinearMap.hasMFDerivAt
-/

#print ContinuousLinearMap.mdifferentiableWithinAt /-
protected theorem mdifferentiableWithinAt : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
  f.DifferentiableWithinAt.MDifferentiableWithinAt
#align continuous_linear_map.mdifferentiable_within_at ContinuousLinearMap.mdifferentiableWithinAt
-/

#print ContinuousLinearMap.mdifferentiableOn /-
protected theorem mdifferentiableOn : MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  f.DifferentiableOn.MDifferentiableOn
#align continuous_linear_map.mdifferentiable_on ContinuousLinearMap.mdifferentiableOn
-/

#print ContinuousLinearMap.mdifferentiableAt /-
protected theorem mdifferentiableAt : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  f.DifferentiableAt.MDifferentiableAt
#align continuous_linear_map.mdifferentiable_at ContinuousLinearMap.mdifferentiableAt
-/

#print ContinuousLinearMap.mdifferentiable /-
protected theorem mdifferentiable : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  f.Differentiable.MDifferentiable
#align continuous_linear_map.mdifferentiable ContinuousLinearMap.mdifferentiable
-/

#print ContinuousLinearMap.mfderiv_eq /-
theorem mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = f :=
  f.HasMFDerivAt.mfderiv
#align continuous_linear_map.mfderiv_eq ContinuousLinearMap.mfderiv_eq
-/

#print ContinuousLinearMap.mfderivWithin_eq /-
theorem mfderivWithin_eq (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = f :=
  f.HasMFDerivWithinAt.mfderivWithin hs
#align continuous_linear_map.mfderiv_within_eq ContinuousLinearMap.mfderivWithin_eq
-/

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] E') {s : Set E} {x : E}

#print ContinuousLinearEquiv.hasMFDerivWithinAt /-
protected theorem hasMFDerivWithinAt : HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x (f : E →L[𝕜] E') :=
  f.HasFDerivWithinAt.HasMFDerivWithinAt
#align continuous_linear_equiv.has_mfderiv_within_at ContinuousLinearEquiv.hasMFDerivWithinAt
-/

#print ContinuousLinearEquiv.hasMFDerivAt /-
protected theorem hasMFDerivAt : HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x (f : E →L[𝕜] E') :=
  f.HasFDerivAt.HasMFDerivAt
#align continuous_linear_equiv.has_mfderiv_at ContinuousLinearEquiv.hasMFDerivAt
-/

#print ContinuousLinearEquiv.mdifferentiableWithinAt /-
protected theorem mdifferentiableWithinAt : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
  f.DifferentiableWithinAt.MDifferentiableWithinAt
#align continuous_linear_equiv.mdifferentiable_within_at ContinuousLinearEquiv.mdifferentiableWithinAt
-/

#print ContinuousLinearEquiv.mdifferentiableOn /-
protected theorem mdifferentiableOn : MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  f.DifferentiableOn.MDifferentiableOn
#align continuous_linear_equiv.mdifferentiable_on ContinuousLinearEquiv.mdifferentiableOn
-/

#print ContinuousLinearEquiv.mdifferentiableAt /-
protected theorem mdifferentiableAt : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  f.DifferentiableAt.MDifferentiableAt
#align continuous_linear_equiv.mdifferentiable_at ContinuousLinearEquiv.mdifferentiableAt
-/

#print ContinuousLinearEquiv.mdifferentiable /-
protected theorem mdifferentiable : MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  f.Differentiable.MDifferentiable
#align continuous_linear_equiv.mdifferentiable ContinuousLinearEquiv.mdifferentiable
-/

#print ContinuousLinearEquiv.mfderiv_eq /-
theorem mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = (f : E →L[𝕜] E') :=
  f.HasMFDerivAt.mfderiv
#align continuous_linear_equiv.mfderiv_eq ContinuousLinearEquiv.mfderiv_eq
-/

#print ContinuousLinearEquiv.mfderivWithin_eq /-
theorem mfderivWithin_eq (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) :
    mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = (f : E →L[𝕜] E') :=
  f.HasMFDerivWithinAt.mfderivWithin hs
#align continuous_linear_equiv.mfderiv_within_eq ContinuousLinearEquiv.mfderivWithin_eq
-/

end ContinuousLinearEquiv

variable {s : Set M} {x : M}

section id

/-! #### Identity -/


#print hasMFDerivAt_id /-
theorem hasMFDerivAt_id (x : M) :
    HasMFDerivAt I I (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) :=
  by
  refine' ⟨continuousAt_id, _⟩
  have : ∀ᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = id y :=
    by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin I x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _) this
  simp only [mfld_simps]
#align has_mfderiv_at_id hasMFDerivAt_id
-/

#print hasMFDerivWithinAt_id /-
theorem hasMFDerivWithinAt_id (s : Set M) (x : M) :
    HasMFDerivWithinAt I I (@id M) s x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) :=
  (hasMFDerivAt_id I x).HasMFDerivWithinAt
#align has_mfderiv_within_at_id hasMFDerivWithinAt_id
-/

#print mdifferentiableAt_id /-
theorem mdifferentiableAt_id : MDifferentiableAt I I (@id M) x :=
  (hasMFDerivAt_id I x).MDifferentiableAt
#align mdifferentiable_at_id mdifferentiableAt_id
-/

#print mdifferentiableWithinAt_id /-
theorem mdifferentiableWithinAt_id : MDifferentiableWithinAt I I (@id M) s x :=
  (mdifferentiableAt_id I).MDifferentiableWithinAt
#align mdifferentiable_within_at_id mdifferentiableWithinAt_id
-/

#print mdifferentiable_id /-
theorem mdifferentiable_id : MDifferentiable I I (@id M) := fun x => mdifferentiableAt_id I
#align mdifferentiable_id mdifferentiable_id
-/

#print mdifferentiableOn_id /-
theorem mdifferentiableOn_id : MDifferentiableOn I I (@id M) s :=
  (mdifferentiable_id I).MDifferentiableOn
#align mdifferentiable_on_id mdifferentiableOn_id
-/

#print mfderiv_id /-
@[simp, mfld_simps]
theorem mfderiv_id : mfderiv I I (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
  HasMFDerivAt.mfderiv (hasMFDerivAt_id I x)
#align mfderiv_id mfderiv_id
-/

#print mfderivWithin_id /-
theorem mfderivWithin_id (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I (@id M) s x = ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
  by
  rw [MDifferentiable.mfderivWithin (mdifferentiableAt_id I) hxs]
  exact mfderiv_id I
#align mfderiv_within_id mfderivWithin_id
-/

#print tangentMap_id /-
@[simp, mfld_simps]
theorem tangentMap_id : tangentMap I I (id : M → M) = id := by ext1 ⟨x, v⟩; simp [tangentMap]
#align tangent_map_id tangentMap_id
-/

#print tangentMapWithin_id /-
theorem tangentMapWithin_id {p : TangentBundle I M} (hs : UniqueMDiffWithinAt I s p.proj) :
    tangentMapWithin I I (id : M → M) s p = p :=
  by
  simp only [tangentMapWithin, id.def]
  rw [mfderivWithin_id]
  · rcases p with ⟨⟩; rfl
  · exact hs
#align tangent_map_within_id tangentMapWithin_id
-/

end id

section Const

/-! #### Constants -/


variable {c : M'}

#print hasMFDerivAt_const /-
theorem hasMFDerivAt_const (c : M') (x : M) :
    HasMFDerivAt I I' (fun y : M => c) x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  by
  refine' ⟨continuous_const.continuous_at, _⟩
  simp only [writtenInExtChartAt, (· ∘ ·), hasFDerivWithinAt_const]
#align has_mfderiv_at_const hasMFDerivAt_const
-/

#print hasMFDerivWithinAt_const /-
theorem hasMFDerivWithinAt_const (c : M') (s : Set M) (x : M) :
    HasMFDerivWithinAt I I' (fun y : M => c) s x (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  (hasMFDerivAt_const I I' c x).HasMFDerivWithinAt
#align has_mfderiv_within_at_const hasMFDerivWithinAt_const
-/

#print mdifferentiableAt_const /-
theorem mdifferentiableAt_const : MDifferentiableAt I I' (fun y : M => c) x :=
  (hasMFDerivAt_const I I' c x).MDifferentiableAt
#align mdifferentiable_at_const mdifferentiableAt_const
-/

#print mdifferentiableWithinAt_const /-
theorem mdifferentiableWithinAt_const : MDifferentiableWithinAt I I' (fun y : M => c) s x :=
  (mdifferentiableAt_const I I').MDifferentiableWithinAt
#align mdifferentiable_within_at_const mdifferentiableWithinAt_const
-/

#print mdifferentiable_const /-
theorem mdifferentiable_const : MDifferentiable I I' fun y : M => c := fun x =>
  mdifferentiableAt_const I I'
#align mdifferentiable_const mdifferentiable_const
-/

#print mdifferentiableOn_const /-
theorem mdifferentiableOn_const : MDifferentiableOn I I' (fun y : M => c) s :=
  (mdifferentiable_const I I').MDifferentiableOn
#align mdifferentiable_on_const mdifferentiableOn_const
-/

#print mfderiv_const /-
@[simp, mfld_simps]
theorem mfderiv_const :
    mfderiv I I' (fun y : M => c) x = (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  HasMFDerivAt.mfderiv (hasMFDerivAt_const I I' c x)
#align mfderiv_const mfderiv_const
-/

#print mfderivWithin_const /-
theorem mfderivWithin_const (hxs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I' (fun y : M => c) s x = (0 : TangentSpace I x →L[𝕜] TangentSpace I' c) :=
  (hasMFDerivWithinAt_const _ _ _ _ _).mfderivWithin hxs
#align mfderiv_within_const mfderivWithin_const
-/

end Const

section Prod

/-! Operations on the product of two manifolds-/


#print hasMFDerivAt_fst /-
theorem hasMFDerivAt_fst (x : M × M') :
    HasMFDerivAt (I.Prod I') I Prod.fst x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) :=
  by
  refine' ⟨continuous_fst.continuous_at, _⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I x.1 ∘ Prod.fst ∘ (extChartAt (I.prod I') x).symm) y = y.1 :=
    by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_fst this
  simp only [mfld_simps]
#align has_mfderiv_at_fst hasMFDerivAt_fst
-/

#print hasMFDerivWithinAt_fst /-
theorem hasMFDerivWithinAt_fst (s : Set (M × M')) (x : M × M') :
    HasMFDerivWithinAt (I.Prod I') I Prod.fst s x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) :=
  (hasMFDerivAt_fst I I' x).HasMFDerivWithinAt
#align has_mfderiv_within_at_fst hasMFDerivWithinAt_fst
-/

#print mdifferentiableAt_fst /-
theorem mdifferentiableAt_fst {x : M × M'} : MDifferentiableAt (I.Prod I') I Prod.fst x :=
  (hasMFDerivAt_fst I I' x).MDifferentiableAt
#align mdifferentiable_at_fst mdifferentiableAt_fst
-/

#print mdifferentiableWithinAt_fst /-
theorem mdifferentiableWithinAt_fst {s : Set (M × M')} {x : M × M'} :
    MDifferentiableWithinAt (I.Prod I') I Prod.fst s x :=
  (mdifferentiableAt_fst I I').MDifferentiableWithinAt
#align mdifferentiable_within_at_fst mdifferentiableWithinAt_fst
-/

#print mdifferentiable_fst /-
theorem mdifferentiable_fst : MDifferentiable (I.Prod I') I (Prod.fst : M × M' → M) := fun x =>
  mdifferentiableAt_fst I I'
#align mdifferentiable_fst mdifferentiable_fst
-/

#print mdifferentiableOn_fst /-
theorem mdifferentiableOn_fst {s : Set (M × M')} : MDifferentiableOn (I.Prod I') I Prod.fst s :=
  (mdifferentiable_fst I I').MDifferentiableOn
#align mdifferentiable_on_fst mdifferentiableOn_fst
-/

#print mfderiv_fst /-
@[simp, mfld_simps]
theorem mfderiv_fst {x : M × M'} :
    mfderiv (I.Prod I') I Prod.fst x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  (hasMFDerivAt_fst I I' x).mfderiv
#align mfderiv_fst mfderiv_fst
-/

#print mfderivWithin_fst /-
theorem mfderivWithin_fst {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffWithinAt (I.Prod I') s x) :
    mfderivWithin (I.Prod I') I Prod.fst s x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  by rw [MDifferentiable.mfderivWithin (mdifferentiableAt_fst I I') hxs]; exact mfderiv_fst I I'
#align mfderiv_within_fst mfderivWithin_fst
-/

#print tangentMap_prod_fst /-
@[simp, mfld_simps]
theorem tangentMap_prod_fst {p : TangentBundle (I.Prod I') (M × M')} :
    tangentMap (I.Prod I') I Prod.fst p = ⟨p.proj.1, p.2.1⟩ := by simp [tangentMap]
#align tangent_map_prod_fst tangentMap_prod_fst
-/

#print tangentMapWithin_prod_fst /-
theorem tangentMapWithin_prod_fst {s : Set (M × M')} {p : TangentBundle (I.Prod I') (M × M')}
    (hs : UniqueMDiffWithinAt (I.Prod I') s p.proj) :
    tangentMapWithin (I.Prod I') I Prod.fst s p = ⟨p.proj.1, p.2.1⟩ :=
  by
  simp only [tangentMapWithin]
  rw [mfderivWithin_fst _ _ hs]
  rcases p with ⟨⟩
  exact ⟨rfl, HEq.rfl⟩
#align tangent_map_within_prod_fst tangentMapWithin_prod_fst
-/

#print hasMFDerivAt_snd /-
theorem hasMFDerivAt_snd (x : M × M') :
    HasMFDerivAt (I.Prod I') I' Prod.snd x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) :=
  by
  refine' ⟨continuous_snd.continuous_at, _⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I' x.2 ∘ Prod.snd ∘ (extChartAt (I.prod I') x).symm) y = y.2 :=
    by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_snd this
  simp only [mfld_simps]
#align has_mfderiv_at_snd hasMFDerivAt_snd
-/

#print hasMFDerivWithinAt_snd /-
theorem hasMFDerivWithinAt_snd (s : Set (M × M')) (x : M × M') :
    HasMFDerivWithinAt (I.Prod I') I' Prod.snd s x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2)) :=
  (hasMFDerivAt_snd I I' x).HasMFDerivWithinAt
#align has_mfderiv_within_at_snd hasMFDerivWithinAt_snd
-/

#print mdifferentiableAt_snd /-
theorem mdifferentiableAt_snd {x : M × M'} : MDifferentiableAt (I.Prod I') I' Prod.snd x :=
  (hasMFDerivAt_snd I I' x).MDifferentiableAt
#align mdifferentiable_at_snd mdifferentiableAt_snd
-/

#print mdifferentiableWithinAt_snd /-
theorem mdifferentiableWithinAt_snd {s : Set (M × M')} {x : M × M'} :
    MDifferentiableWithinAt (I.Prod I') I' Prod.snd s x :=
  (mdifferentiableAt_snd I I').MDifferentiableWithinAt
#align mdifferentiable_within_at_snd mdifferentiableWithinAt_snd
-/

#print mdifferentiable_snd /-
theorem mdifferentiable_snd : MDifferentiable (I.Prod I') I' (Prod.snd : M × M' → M') := fun x =>
  mdifferentiableAt_snd I I'
#align mdifferentiable_snd mdifferentiable_snd
-/

#print mdifferentiableOn_snd /-
theorem mdifferentiableOn_snd {s : Set (M × M')} : MDifferentiableOn (I.Prod I') I' Prod.snd s :=
  (mdifferentiable_snd I I').MDifferentiableOn
#align mdifferentiable_on_snd mdifferentiableOn_snd
-/

#print mfderiv_snd /-
@[simp, mfld_simps]
theorem mfderiv_snd {x : M × M'} :
    mfderiv (I.Prod I') I' Prod.snd x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  (hasMFDerivAt_snd I I' x).mfderiv
#align mfderiv_snd mfderiv_snd
-/

#print mfderivWithin_snd /-
theorem mfderivWithin_snd {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffWithinAt (I.Prod I') s x) :
    mfderivWithin (I.Prod I') I' Prod.snd s x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace I x.1) (TangentSpace I' x.2) :=
  by rw [MDifferentiable.mfderivWithin (mdifferentiableAt_snd I I') hxs]; exact mfderiv_snd I I'
#align mfderiv_within_snd mfderivWithin_snd
-/

#print tangentMap_prod_snd /-
@[simp, mfld_simps]
theorem tangentMap_prod_snd {p : TangentBundle (I.Prod I') (M × M')} :
    tangentMap (I.Prod I') I' Prod.snd p = ⟨p.proj.2, p.2.2⟩ := by simp [tangentMap]
#align tangent_map_prod_snd tangentMap_prod_snd
-/

#print tangentMapWithin_prod_snd /-
theorem tangentMapWithin_prod_snd {s : Set (M × M')} {p : TangentBundle (I.Prod I') (M × M')}
    (hs : UniqueMDiffWithinAt (I.Prod I') s p.proj) :
    tangentMapWithin (I.Prod I') I' Prod.snd s p = ⟨p.proj.2, p.2.2⟩ :=
  by
  simp only [tangentMapWithin]
  rw [mfderivWithin_snd]
  · rcases p with ⟨⟩; constructor <;> rfl
  · exact hs
#align tangent_map_within_prod_snd tangentMapWithin_prod_snd
-/

variable {I I' I''}

#print MDifferentiableAt.mfderiv_prod /-
theorem MDifferentiableAt.mfderiv_prod {f : M → M'} {g : M → M''} {x : M}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I I'' g x) :
    mfderiv I (I'.Prod I'') (fun x => (f x, g x)) x = (mfderiv I I' f x).Prod (mfderiv I I'' g x) :=
  by
  classical
  simp_rw [mfderiv, if_pos (hf.prod_mk hg), if_pos hf, if_pos hg]
  exact hf.2.fderivWithin_prod hg.2 (I.unique_diff _ (mem_range_self _))
#align mdifferentiable_at.mfderiv_prod MDifferentiableAt.mfderiv_prod
-/

variable (I I' I'')

#print mfderiv_prod_left /-
theorem mfderiv_prod_left {x₀ : M} {y₀ : M'} :
    mfderiv I (I.Prod I') (fun x => (x, y₀)) x₀ =
      ContinuousLinearMap.inl 𝕜 (TangentSpace I x₀) (TangentSpace I' y₀) :=
  by
  refine' ((mdifferentiableAt_id I).mfderiv_prod (mdifferentiableAt_const I I')).trans _
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inl]
#align mfderiv_prod_left mfderiv_prod_left
-/

#print mfderiv_prod_right /-
theorem mfderiv_prod_right {x₀ : M} {y₀ : M'} :
    mfderiv I' (I.Prod I') (fun y => (x₀, y)) y₀ =
      ContinuousLinearMap.inr 𝕜 (TangentSpace I x₀) (TangentSpace I' y₀) :=
  by
  refine' ((mdifferentiableAt_const I' I).mfderiv_prod (mdifferentiableAt_id I')).trans _
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inr]
#align mfderiv_prod_right mfderiv_prod_right
-/

#print mfderiv_prod_eq_add /-
/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `tangent_space`. -/
theorem mfderiv_prod_eq_add {f : M × M' → M''} {p : M × M'}
    (hf : MDifferentiableAt (I.Prod I') I'' f p) :
    mfderiv (I.Prod I') I'' f p =
      show E × E' →L[𝕜] E'' from
        mfderiv (I.Prod I') I'' (fun z : M × M' => f (z.1, p.2)) p +
          mfderiv (I.Prod I') I'' (fun z : M × M' => f (p.1, z.2)) p :=
  by
  dsimp only
  rw [← @Prod.mk.eta _ _ p] at hf
  rw [mfderiv_comp_of_eq hf ((mdifferentiableAt_fst I I').prod_mk (mdifferentiableAt_const _ _))
      rfl,
    mfderiv_comp_of_eq hf ((mdifferentiableAt_const _ _).prod_mk (mdifferentiableAt_snd I I')) rfl,
    ← ContinuousLinearMap.comp_add,
    (mdifferentiableAt_fst I I').mfderiv_prod (mdifferentiableAt_const (I.prod I') I'),
    (mdifferentiableAt_const (I.prod I') I).mfderiv_prod (mdifferentiableAt_snd I I'), mfderiv_fst,
    mfderiv_snd, mfderiv_const, mfderiv_const]
  symm
  convert ContinuousLinearMap.comp_id _
  · exact ContinuousLinearMap.coprod_inl_inr
  simp_rw [Prod.mk.eta]
  all_goals infer_instance
#align mfderiv_prod_eq_add mfderiv_prod_eq_add
-/

end Prod

section Arithmetic

/-! #### Arithmetic

Note that in the in `has_mfderiv_at` lemmas there is an abuse of the defeq between `E'` and
`tangent_space 𝓘(𝕜, E') (f z)` (similarly for `g',F',p',q'`). In general this defeq is not
canonical, but in this case (the tangent space of a vector space) it is canonical.
 -/


section Group

variable {I} {z : M} {f g : M → E'} {f' g' : TangentSpace I z →L[𝕜] E'}

#print HasMFDerivAt.add /-
theorem HasMFDerivAt.add (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f')
    (hg : HasMFDerivAt I 𝓘(𝕜, E') g z g') : HasMFDerivAt I 𝓘(𝕜, E') (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩
#align has_mfderiv_at.add HasMFDerivAt.add
-/

#print MDifferentiableAt.add /-
theorem MDifferentiableAt.add (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) : MDifferentiableAt I 𝓘(𝕜, E') (f + g) z :=
  (hf.HasMFDerivAt.add hg.HasMFDerivAt).MDifferentiableAt
#align mdifferentiable_at.add MDifferentiableAt.add
-/

#print MDifferentiable.add /-
theorem MDifferentiable.add (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E') g) : MDifferentiable I 𝓘(𝕜, E') (f + g) := fun x =>
  (hf x).add (hg x)
#align mdifferentiable.add MDifferentiable.add
-/

#print mfderiv_add /-
theorem mfderiv_add (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) :
    (mfderiv I 𝓘(𝕜, E') (f + g) z : TangentSpace I z →L[𝕜] E') =
      (mfderiv I 𝓘(𝕜, E') f z + mfderiv I 𝓘(𝕜, E') g z : TangentSpace I z →L[𝕜] E') :=
  (hf.HasMFDerivAt.add hg.HasMFDerivAt).mfderiv
#align mfderiv_add mfderiv_add
-/

#print HasMFDerivAt.const_smul /-
theorem HasMFDerivAt.const_smul (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f') (s : 𝕜) :
    HasMFDerivAt I 𝓘(𝕜, E') (s • f) z (s • f') :=
  ⟨hf.1.const_smul s, hf.2.const_smul s⟩
#align has_mfderiv_at.const_smul HasMFDerivAt.const_smul
-/

#print MDifferentiableAt.const_smul /-
theorem MDifferentiableAt.const_smul (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) (s : 𝕜) :
    MDifferentiableAt I 𝓘(𝕜, E') (s • f) z :=
  (hf.HasMFDerivAt.const_smul s).MDifferentiableAt
#align mdifferentiable_at.const_smul MDifferentiableAt.const_smul
-/

#print MDifferentiable.const_smul /-
theorem MDifferentiable.const_smul (s : 𝕜) (hf : MDifferentiable I 𝓘(𝕜, E') f) :
    MDifferentiable I 𝓘(𝕜, E') (s • f) := fun x => (hf x).const_smul s
#align mdifferentiable.const_smul MDifferentiable.const_smul
-/

#print const_smul_mfderiv /-
theorem const_smul_mfderiv (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) (s : 𝕜) :
    (mfderiv I 𝓘(𝕜, E') (s • f) z : TangentSpace I z →L[𝕜] E') =
      (s • mfderiv I 𝓘(𝕜, E') f z : TangentSpace I z →L[𝕜] E') :=
  (hf.HasMFDerivAt.const_smul s).mfderiv
#align const_smul_mfderiv const_smul_mfderiv
-/

#print HasMFDerivAt.neg /-
theorem HasMFDerivAt.neg (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f') :
    HasMFDerivAt I 𝓘(𝕜, E') (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩
#align has_mfderiv_at.neg HasMFDerivAt.neg
-/

#print hasMFDerivAt_neg /-
theorem hasMFDerivAt_neg : HasMFDerivAt I 𝓘(𝕜, E') (-f) z (-f') ↔ HasMFDerivAt I 𝓘(𝕜, E') f z f' :=
  ⟨fun hf => by convert hf.neg <;> rw [neg_neg], fun hf => hf.neg⟩
#align has_mfderiv_at_neg hasMFDerivAt_neg
-/

#print MDifferentiableAt.neg /-
theorem MDifferentiableAt.neg (hf : MDifferentiableAt I 𝓘(𝕜, E') f z) :
    MDifferentiableAt I 𝓘(𝕜, E') (-f) z :=
  hf.HasMFDerivAt.neg.MDifferentiableAt
#align mdifferentiable_at.neg MDifferentiableAt.neg
-/

#print mdifferentiableAt_neg /-
theorem mdifferentiableAt_neg :
    MDifferentiableAt I 𝓘(𝕜, E') (-f) z ↔ MDifferentiableAt I 𝓘(𝕜, E') f z :=
  ⟨fun hf => by convert hf.neg <;> rw [neg_neg], fun hf => hf.neg⟩
#align mdifferentiable_at_neg mdifferentiableAt_neg
-/

#print MDifferentiable.neg /-
theorem MDifferentiable.neg (hf : MDifferentiable I 𝓘(𝕜, E') f) : MDifferentiable I 𝓘(𝕜, E') (-f) :=
  fun x => (hf x).neg
#align mdifferentiable.neg MDifferentiable.neg
-/

#print mfderiv_neg /-
theorem mfderiv_neg (f : M → E') (x : M) :
    (mfderiv I 𝓘(𝕜, E') (-f) x : TangentSpace I x →L[𝕜] E') =
      (-mfderiv I 𝓘(𝕜, E') f x : TangentSpace I x →L[𝕜] E') :=
  by
  simp_rw [mfderiv]
  by_cases hf : MDifferentiableAt I 𝓘(𝕜, E') f x
  · exact hf.has_mfderiv_at.neg.mfderiv
  · rw [if_neg hf]; rw [← mdifferentiableAt_neg] at hf; rw [if_neg hf, neg_zero]
#align mfderiv_neg mfderiv_neg
-/

#print HasMFDerivAt.sub /-
theorem HasMFDerivAt.sub (hf : HasMFDerivAt I 𝓘(𝕜, E') f z f')
    (hg : HasMFDerivAt I 𝓘(𝕜, E') g z g') : HasMFDerivAt I 𝓘(𝕜, E') (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩
#align has_mfderiv_at.sub HasMFDerivAt.sub
-/

#print MDifferentiableAt.sub /-
theorem MDifferentiableAt.sub (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) : MDifferentiableAt I 𝓘(𝕜, E') (f - g) z :=
  (hf.HasMFDerivAt.sub hg.HasMFDerivAt).MDifferentiableAt
#align mdifferentiable_at.sub MDifferentiableAt.sub
-/

#print MDifferentiable.sub /-
theorem MDifferentiable.sub (hf : MDifferentiable I 𝓘(𝕜, E') f)
    (hg : MDifferentiable I 𝓘(𝕜, E') g) : MDifferentiable I 𝓘(𝕜, E') (f - g) := fun x =>
  (hf x).sub (hg x)
#align mdifferentiable.sub MDifferentiable.sub
-/

#print mfderiv_sub /-
theorem mfderiv_sub (hf : MDifferentiableAt I 𝓘(𝕜, E') f z)
    (hg : MDifferentiableAt I 𝓘(𝕜, E') g z) :
    (mfderiv I 𝓘(𝕜, E') (f - g) z : TangentSpace I z →L[𝕜] E') =
      (mfderiv I 𝓘(𝕜, E') f z - mfderiv I 𝓘(𝕜, E') g z : TangentSpace I z →L[𝕜] E') :=
  (hf.HasMFDerivAt.sub hg.HasMFDerivAt).mfderiv
#align mfderiv_sub mfderiv_sub
-/

end Group

section AlgebraOverRing

variable {I} {z : M} {F' : Type _} [NormedRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace I z →L[𝕜] F'}

#print HasMFDerivWithinAt.mul' /-
theorem HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + p'.smul_right (q z) : E →L[𝕜] F') :=
  ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using hp.2.mul' hq.2⟩
#align has_mfderiv_within_at.mul' HasMFDerivWithinAt.mul'
-/

#print HasMFDerivAt.mul' /-
theorem HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + p'.smul_right (q z) : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.HasMFDerivWithinAt.mul' hq.HasMFDerivWithinAt
#align has_mfderiv_at.mul' HasMFDerivAt.mul'
-/

#print MDifferentiableWithinAt.mul /-
theorem MDifferentiableWithinAt.mul (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p * q) s z :=
  (hp.HasMFDerivWithinAt.mul' hq.HasMFDerivWithinAt).MDifferentiableWithinAt
#align mdifferentiable_within_at.mul MDifferentiableWithinAt.mul
-/

#print MDifferentiableAt.mul /-
theorem MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, F') (p * q) z :=
  (hp.HasMFDerivAt.mul' hq.HasMFDerivAt).MDifferentiableAt
#align mdifferentiable_at.mul MDifferentiableAt.mul
-/

#print MDifferentiableOn.mul /-
theorem MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) : MDifferentiableOn I 𝓘(𝕜, F') (p * q) s := fun x hx =>
  (hp x hx).mul <| hq x hx
#align mdifferentiable_on.mul MDifferentiableOn.mul
-/

#print MDifferentiable.mul /-
theorem MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) : MDifferentiable I 𝓘(𝕜, F') (p * q) := fun x =>
  (hp x).mul (hq x)
#align mdifferentiable.mul MDifferentiable.mul
-/

end AlgebraOverRing

section AlgebraOverCommRing

variable {I} {z : M} {F' : Type _} [NormedCommRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace I z →L[𝕜] F'}

#print HasMFDerivWithinAt.mul /-
theorem HasMFDerivWithinAt.mul (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + q z • p' : E →L[𝕜] F') := by
  convert hp.mul' hq; ext z; apply mul_comm
#align has_mfderiv_within_at.mul HasMFDerivWithinAt.mul
-/

#print HasMFDerivAt.mul /-
theorem HasMFDerivAt.mul (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + q z • p' : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.HasMFDerivWithinAt.mul hq.HasMFDerivWithinAt
#align has_mfderiv_at.mul HasMFDerivAt.mul
-/

end AlgebraOverCommRing

end Arithmetic

namespace ModelWithCorners

/-! #### Model with corners -/


#print ModelWithCorners.hasMFDerivAt /-
protected theorem hasMFDerivAt {x} : HasMFDerivAt I 𝓘(𝕜, E) I x (ContinuousLinearMap.id _ _) :=
  ⟨I.ContinuousAt, (hasFDerivWithinAt_id _ _).congr' I.RightInvOn (mem_range_self _)⟩
#align model_with_corners.has_mfderiv_at ModelWithCorners.hasMFDerivAt
-/

#print ModelWithCorners.hasMFDerivWithinAt /-
protected theorem hasMFDerivWithinAt {s x} :
    HasMFDerivWithinAt I 𝓘(𝕜, E) I s x (ContinuousLinearMap.id _ _) :=
  I.HasMFDerivAt.HasMFDerivWithinAt
#align model_with_corners.has_mfderiv_within_at ModelWithCorners.hasMFDerivWithinAt
-/

#print ModelWithCorners.mdifferentiableWithinAt /-
protected theorem mdifferentiableWithinAt {s x} : MDifferentiableWithinAt I 𝓘(𝕜, E) I s x :=
  I.HasMFDerivWithinAt.MDifferentiableWithinAt
#align model_with_corners.mdifferentiable_within_at ModelWithCorners.mdifferentiableWithinAt
-/

#print ModelWithCorners.mdifferentiableAt /-
protected theorem mdifferentiableAt {x} : MDifferentiableAt I 𝓘(𝕜, E) I x :=
  I.HasMFDerivAt.MDifferentiableAt
#align model_with_corners.mdifferentiable_at ModelWithCorners.mdifferentiableAt
-/

#print ModelWithCorners.mdifferentiableOn /-
protected theorem mdifferentiableOn {s} : MDifferentiableOn I 𝓘(𝕜, E) I s := fun x hx =>
  I.MDifferentiableWithinAt
#align model_with_corners.mdifferentiable_on ModelWithCorners.mdifferentiableOn
-/

#print ModelWithCorners.mdifferentiable /-
protected theorem mdifferentiable : MDifferentiable I 𝓘(𝕜, E) I := fun x => I.MDifferentiableAt
#align model_with_corners.mdifferentiable ModelWithCorners.mdifferentiable
-/

#print ModelWithCorners.hasMFDerivWithinAt_symm /-
theorem hasMFDerivWithinAt_symm {x} (hx : x ∈ range I) :
    HasMFDerivWithinAt 𝓘(𝕜, E) I I.symm (range I) x (ContinuousLinearMap.id _ _) :=
  ⟨I.continuousWithinAt_symm,
    (hasFDerivWithinAt_id _ _).congr' (fun y hy => I.RightInvOn hy.1) ⟨hx, mem_range_self _⟩⟩
#align model_with_corners.has_mfderiv_within_at_symm ModelWithCorners.hasMFDerivWithinAt_symm
-/

#print ModelWithCorners.mdifferentiableOn_symm /-
theorem mdifferentiableOn_symm : MDifferentiableOn 𝓘(𝕜, E) I I.symm (range I) := fun x hx =>
  (I.hasMFDerivWithinAt_symm hx).MDifferentiableWithinAt
#align model_with_corners.mdifferentiable_on_symm ModelWithCorners.mdifferentiableOn_symm
-/

end ModelWithCorners

section Charts

variable {e : PartialHomeomorph M H}

#print mdifferentiableAt_atlas /-
theorem mdifferentiableAt_atlas (h : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) :
    MDifferentiableAt I I e x :=
  by
  refine' ⟨(e.continuous_on x hx).ContinuousAt (IsOpen.mem_nhds e.open_source hx), _⟩
  have mem :
    I ((chart_at H x : M → H) x) ∈ I.symm ⁻¹' ((chart_at H x).symm ≫ₕ e).source ∩ range I := by
    simp only [hx, mfld_simps]
  have : (chart_at H x).symm.trans e ∈ contDiffGroupoid ∞ I :=
    HasGroupoid.compatible _ (chart_mem_atlas H x) h
  have A :
    ContDiffOn 𝕜 ∞ (I ∘ (chart_at H x).symm.trans e ∘ I.symm)
      (I.symm ⁻¹' ((chart_at H x).symm.trans e).source ∩ range I) :=
    this.1
  have B := A.differentiable_on le_top (I ((chart_at H x : M → H) x)) mem
  simp only [mfld_simps] at B
  rw [inter_comm, differentiableWithinAt_inter] at B
  · simpa only [mfld_simps]
  · apply IsOpen.mem_nhds ((PartialHomeomorph.open_source _).Preimage I.continuous_symm) mem.1
#align mdifferentiable_at_atlas mdifferentiableAt_atlas
-/

#print mdifferentiableOn_atlas /-
theorem mdifferentiableOn_atlas (h : e ∈ atlas H M) : MDifferentiableOn I I e e.source :=
  fun x hx => (mdifferentiableAt_atlas I h hx).MDifferentiableWithinAt
#align mdifferentiable_on_atlas mdifferentiableOn_atlas
-/

#print mdifferentiableAt_atlas_symm /-
theorem mdifferentiableAt_atlas_symm (h : e ∈ atlas H M) {x : H} (hx : x ∈ e.target) :
    MDifferentiableAt I I e.symm x :=
  by
  refine' ⟨(e.continuous_on_symm x hx).ContinuousAt (IsOpen.mem_nhds e.open_target hx), _⟩
  have mem : I x ∈ I.symm ⁻¹' (e.symm ≫ₕ chart_at H (e.symm x)).source ∩ range I := by
    simp only [hx, mfld_simps]
  have : e.symm.trans (chart_at H (e.symm x)) ∈ contDiffGroupoid ∞ I :=
    HasGroupoid.compatible _ h (chart_mem_atlas H _)
  have A :
    ContDiffOn 𝕜 ∞ (I ∘ e.symm.trans (chart_at H (e.symm x)) ∘ I.symm)
      (I.symm ⁻¹' (e.symm.trans (chart_at H (e.symm x))).source ∩ range I) :=
    this.1
  have B := A.differentiable_on le_top (I x) mem
  simp only [mfld_simps] at B
  rw [inter_comm, differentiableWithinAt_inter] at B
  · simpa only [mfld_simps]
  · apply IsOpen.mem_nhds ((PartialHomeomorph.open_source _).Preimage I.continuous_symm) mem.1
#align mdifferentiable_at_atlas_symm mdifferentiableAt_atlas_symm
-/

#print mdifferentiableOn_atlas_symm /-
theorem mdifferentiableOn_atlas_symm (h : e ∈ atlas H M) : MDifferentiableOn I I e.symm e.target :=
  fun x hx => (mdifferentiableAt_atlas_symm I h hx).MDifferentiableWithinAt
#align mdifferentiable_on_atlas_symm mdifferentiableOn_atlas_symm
-/

#print mdifferentiable_of_mem_atlas /-
theorem mdifferentiable_of_mem_atlas (h : e ∈ atlas H M) : e.MDifferentiable I I :=
  ⟨mdifferentiableOn_atlas I h, mdifferentiableOn_atlas_symm I h⟩
#align mdifferentiable_of_mem_atlas mdifferentiable_of_mem_atlas
-/

#print mdifferentiable_chart /-
theorem mdifferentiable_chart (x : M) : (chartAt H x).MDifferentiable I I :=
  mdifferentiable_of_mem_atlas _ (chart_mem_atlas _ _)
#align mdifferentiable_chart mdifferentiable_chart
-/

#print tangentMap_chart /-
/-- The derivative of the chart at a base point is the chart of the tangent bundle, composed with
the identification between the tangent bundle of the model space and the product space. -/
theorem tangentMap_chart {p q : TangentBundle I M} (h : q.1 ∈ (chartAt H p.1).source) :
    tangentMap I I (chartAt H p.1) q =
      (TotalSpace.toProd _ _).symm
        ((chartAt (ModelProd H E) p : TangentBundle I M → ModelProd H E) q) :=
  by
  dsimp [tangentMap]
  rw [MDifferentiableAt.mfderiv]
  · rfl
  · exact mdifferentiableAt_atlas _ (chart_mem_atlas _ _) h
#align tangent_map_chart tangentMap_chart
-/

#print tangentMap_chart_symm /-
/-- The derivative of the inverse of the chart at a base point is the inverse of the chart of the
tangent bundle, composed with the identification between the tangent bundle of the model space and
the product space. -/
theorem tangentMap_chart_symm {p : TangentBundle I M} {q : TangentBundle I H}
    (h : q.1 ∈ (chartAt H p.1).target) :
    tangentMap I I (chartAt H p.1).symm q =
      ((chartAt (ModelProd H E) p).symm : ModelProd H E → TangentBundle I M)
        ((TotalSpace.toProd H E) q) :=
  by
  dsimp only [tangentMap]
  rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas_symm _ (chart_mem_atlas _ _) h)]
  -- a trivial instance is needed after the rewrite, handle it right now.
  rotate_left;
  · infer_instance
  simp only [ContinuousLinearMap.coe_coe, TangentBundle.chartAt, h, tangentBundleCore, chart_at,
    total_space.to_prod_apply, mfld_simps]
#align tangent_map_chart_symm tangentMap_chart_symm
-/

end Charts

end SpecificFunctions

/-! ### Differentiable local homeomorphisms -/


namespace PartialHomeomorph.MDifferentiable

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type _} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type _}
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type _} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type _} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type _} [TopologicalSpace M''] [ChartedSpace H'' M''] {e : PartialHomeomorph M M'}
  (he : e.MDifferentiable I I') {e' : PartialHomeomorph M' M''}

#print PartialHomeomorph.MDifferentiable.symm /-
theorem symm : e.symm.MDifferentiable I' I :=
  ⟨he.2, he.1⟩
#align local_homeomorph.mdifferentiable.symm PartialHomeomorph.MDifferentiable.symm
-/

#print PartialHomeomorph.MDifferentiable.mdifferentiableAt /-
protected theorem mdifferentiableAt {x : M} (hx : x ∈ e.source) : MDifferentiableAt I I' e x :=
  (he.1 x hx).MDifferentiableAt (IsOpen.mem_nhds e.open_source hx)
#align local_homeomorph.mdifferentiable.mdifferentiable_at PartialHomeomorph.MDifferentiable.mdifferentiableAt
-/

#print PartialHomeomorph.MDifferentiable.mdifferentiableAt_symm /-
theorem mdifferentiableAt_symm {x : M'} (hx : x ∈ e.target) : MDifferentiableAt I' I e.symm x :=
  (he.2 x hx).MDifferentiableAt (IsOpen.mem_nhds e.open_target hx)
#align local_homeomorph.mdifferentiable.mdifferentiable_at_symm PartialHomeomorph.MDifferentiable.mdifferentiableAt_symm
-/

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M']
  [SmoothManifoldWithCorners I'' M'']

#print PartialHomeomorph.MDifferentiable.symm_comp_deriv /-
theorem symm_comp_deriv {x : M} (hx : x ∈ e.source) :
    (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x) :=
  by
  have : mfderiv I I (e.symm ∘ e) x = (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) :=
    mfderiv_comp x (he.mdifferentiable_at_symm (e.map_source hx)) (he.mdifferentiable_at hx)
  rw [← this]
  have : mfderiv I I (_root_.id : M → M) x = ContinuousLinearMap.id _ _ := mfderiv_id I
  rw [← this]
  apply Filter.EventuallyEq.mfderiv_eq
  have : e.source ∈ 𝓝 x := IsOpen.mem_nhds e.open_source hx
  exact Filter.mem_of_superset this (by mfld_set_tac)
#align local_homeomorph.mdifferentiable.symm_comp_deriv PartialHomeomorph.MDifferentiable.symm_comp_deriv
-/

#print PartialHomeomorph.MDifferentiable.comp_symm_deriv /-
theorem comp_symm_deriv {x : M'} (hx : x ∈ e.target) :
    (mfderiv I I' e (e.symm x)).comp (mfderiv I' I e.symm x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I' x) :=
  he.symm.symm_comp_deriv hx
#align local_homeomorph.mdifferentiable.comp_symm_deriv PartialHomeomorph.MDifferentiable.comp_symm_deriv
-/

#print PartialHomeomorph.MDifferentiable.mfderiv /-
/-- The derivative of a differentiable local homeomorphism, as a continuous linear equivalence
between the tangent spaces at `x` and `e x`. -/
protected def mfderiv {x : M} (hx : x ∈ e.source) : TangentSpace I x ≃L[𝕜] TangentSpace I' (e x) :=
  { mfderiv I I' e x with
    invFun := mfderiv I' I e.symm (e x)
    continuous_toFun := (mfderiv I I' e x).cont
    continuous_invFun := (mfderiv I' I e.symm (e x)).cont
    left_inv := fun y =>
      by
      have : (ContinuousLinearMap.id _ _ : TangentSpace I x →L[𝕜] TangentSpace I x) y = y := rfl
      conv_rhs => rw [← this, ← he.symm_comp_deriv hx]
      rfl
    right_inv := fun y =>
      by
      have :
        (ContinuousLinearMap.id 𝕜 _ : TangentSpace I' (e x) →L[𝕜] TangentSpace I' (e x)) y = y :=
        rfl
      conv_rhs => rw [← this, ← he.comp_symm_deriv (e.map_source hx)]
      rw [e.left_inv hx]
      rfl }
#align local_homeomorph.mdifferentiable.mfderiv PartialHomeomorph.MDifferentiable.mfderiv
-/

#print PartialHomeomorph.MDifferentiable.mfderiv_bijective /-
theorem mfderiv_bijective {x : M} (hx : x ∈ e.source) : Function.Bijective (mfderiv I I' e x) :=
  (he.mfderiv hx).Bijective
#align local_homeomorph.mdifferentiable.mfderiv_bijective PartialHomeomorph.MDifferentiable.mfderiv_bijective
-/

#print PartialHomeomorph.MDifferentiable.mfderiv_injective /-
theorem mfderiv_injective {x : M} (hx : x ∈ e.source) : Function.Injective (mfderiv I I' e x) :=
  (he.mfderiv hx).Injective
#align local_homeomorph.mdifferentiable.mfderiv_injective PartialHomeomorph.MDifferentiable.mfderiv_injective
-/

#print PartialHomeomorph.MDifferentiable.mfderiv_surjective /-
theorem mfderiv_surjective {x : M} (hx : x ∈ e.source) : Function.Surjective (mfderiv I I' e x) :=
  (he.mfderiv hx).Surjective
#align local_homeomorph.mdifferentiable.mfderiv_surjective PartialHomeomorph.MDifferentiable.mfderiv_surjective
-/

#print PartialHomeomorph.MDifferentiable.ker_mfderiv_eq_bot /-
theorem ker_mfderiv_eq_bot {x : M} (hx : x ∈ e.source) : LinearMap.ker (mfderiv I I' e x) = ⊥ :=
  (he.mfderiv hx).toLinearEquiv.ker
#align local_homeomorph.mdifferentiable.ker_mfderiv_eq_bot PartialHomeomorph.MDifferentiable.ker_mfderiv_eq_bot
-/

#print PartialHomeomorph.MDifferentiable.range_mfderiv_eq_top /-
theorem range_mfderiv_eq_top {x : M} (hx : x ∈ e.source) : LinearMap.range (mfderiv I I' e x) = ⊤ :=
  (he.mfderiv hx).toLinearEquiv.range
#align local_homeomorph.mdifferentiable.range_mfderiv_eq_top PartialHomeomorph.MDifferentiable.range_mfderiv_eq_top
-/

#print PartialHomeomorph.MDifferentiable.range_mfderiv_eq_univ /-
theorem range_mfderiv_eq_univ {x : M} (hx : x ∈ e.source) : range (mfderiv I I' e x) = univ :=
  (he.mfderiv_surjective hx).range_eq
#align local_homeomorph.mdifferentiable.range_mfderiv_eq_univ PartialHomeomorph.MDifferentiable.range_mfderiv_eq_univ
-/

#print PartialHomeomorph.MDifferentiable.trans /-
theorem trans (he' : e'.MDifferentiable I' I'') : (e.trans e').MDifferentiable I I'' :=
  by
  constructor
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he'.mdifferentiable_at hx.2).comp _ (he.mdifferentiable_at hx.1)).MDifferentiableWithinAt
  · intro x hx
    simp only [mfld_simps] at hx
    exact
      ((he.symm.mdifferentiable_at hx.2).comp _
          (he'.symm.mdifferentiable_at hx.1)).MDifferentiableWithinAt
#align local_homeomorph.mdifferentiable.trans PartialHomeomorph.MDifferentiable.trans
-/

end PartialHomeomorph.MDifferentiable

/-! ### Differentiability of `ext_chart_at` -/


section extChartAt

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {s : Set M} {x y : M}

#print hasMFDerivAt_extChartAt /-
theorem hasMFDerivAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivAt I 𝓘(𝕜, E) (extChartAt I x) y (mfderiv I I (chartAt H x) y : _) :=
  I.HasMFDerivAt.comp y ((mdifferentiable_chart I x).MDifferentiableAt h).HasMFDerivAt
#align has_mfderiv_at_ext_chart_at hasMFDerivAt_extChartAt
-/

#print hasMFDerivWithinAt_extChartAt /-
theorem hasMFDerivWithinAt_extChartAt (h : y ∈ (chartAt H x).source) :
    HasMFDerivWithinAt I 𝓘(𝕜, E) (extChartAt I x) s y (mfderiv I I (chartAt H x) y : _) :=
  (hasMFDerivAt_extChartAt I h).HasMFDerivWithinAt
#align has_mfderiv_within_at_ext_chart_at hasMFDerivWithinAt_extChartAt
-/

#print mdifferentiableAt_extChartAt /-
theorem mdifferentiableAt_extChartAt (h : y ∈ (chartAt H x).source) :
    MDifferentiableAt I 𝓘(𝕜, E) (extChartAt I x) y :=
  (hasMFDerivAt_extChartAt I h).MDifferentiableAt
#align mdifferentiable_at_ext_chart_at mdifferentiableAt_extChartAt
-/

#print mdifferentiableOn_extChartAt /-
theorem mdifferentiableOn_extChartAt :
    MDifferentiableOn I 𝓘(𝕜, E) (extChartAt I x) (chartAt H x).source := fun y hy =>
  (hasMFDerivWithinAt_extChartAt I hy).MDifferentiableWithinAt
#align mdifferentiable_on_ext_chart_at mdifferentiableOn_extChartAt
-/

end extChartAt

/-! ### Unique derivative sets in manifolds -/


section UniqueMdiff

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  {s : Set M}

#print UniqueMDiffOn.uniqueMDiffOn_preimage /-
/-- If a set has the unique differential property, then its image under a local
diffeomorphism also has the unique differential property. -/
theorem UniqueMDiffOn.uniqueMDiffOn_preimage [SmoothManifoldWithCorners I' M']
    (hs : UniqueMDiffOn I s) {e : PartialHomeomorph M M'} (he : e.MDifferentiable I I') :
    UniqueMDiffOn I' (e.target ∩ e.symm ⁻¹' s) :=
  by
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
  have B :
    UniqueDiffWithinAt 𝕜 (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' (extChartAt I' x).source)) ∩ F.target)
      (F z) :=
    by
    have : UniqueMDiffWithinAt I s z := hs _ hx.2
    have S : e.source ∩ e ⁻¹' (extChartAt I' x).source ∈ 𝓝 z :=
      by
      apply IsOpen.mem_nhds
      apply e.continuous_on.preimage_open_of_open e.open_source (isOpen_extChartAt_source I' x)
      simp only [z_source, zx, mfld_simps]
    have := this.inter S
    rw [uniqueMDiffWithinAt_iff] at this
    exact this
  -- denote by `G` the change of coordinate, i.e., the composition of the two extended charts and
  -- of `e`
  let G := F.symm ≫ e.to_local_equiv ≫ extChartAt I' x
  -- `G` is differentiable
  have Diff : ((chart_at H z).symm ≫ₕ e ≫ₕ chart_at H' x).MDifferentiable I I' :=
    by
    have A := mdifferentiable_of_mem_atlas I (chart_mem_atlas H z)
    have B := mdifferentiable_of_mem_atlas I' (chart_mem_atlas H' x)
    exact A.symm.trans (he.trans B)
  have Mmem : (chart_at H z : M → H) z ∈ ((chart_at H z).symm ≫ₕ e ≫ₕ chart_at H' x).source := by
    simp only [z_source, zx, mfld_simps]
  have A : DifferentiableWithinAt 𝕜 G (range I) (F z) := by
    refine' (Diff.mdifferentiable_at Mmem).2.congr (fun p hp => _) _ <;>
      simp only [G, F, mfld_simps]
  -- let `G'` be its derivative
  let G' := fderivWithin 𝕜 G (range I) (F z)
  have D₁ : HasFDerivWithinAt G G' (range I) (F z) := A.has_fderiv_within_at
  have D₂ :
    HasFDerivWithinAt G G' (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' (extChartAt I' x).source)) ∩ F.target)
      (F z) :=
    D₁.mono (by mfld_set_tac)
  -- The derivative `G'` is onto, as it is the derivative of a local diffeomorphism, the composition
  -- of the two charts and of `e`.
  have C : DenseRange (G' : E → E') :=
    by
    have :
      G' = mfderiv I I' ((chart_at H z).symm ≫ₕ e ≫ₕ chart_at H' x) ((chart_at H z : M → H) z) := by
      rw [(Diff.mdifferentiable_at Mmem).mfderiv]; rfl
    rw [this]
    exact (Diff.mfderiv_surjective Mmem).DenseRange
  -- key step: thanks to what we have proved about it, `G` preserves the unique derivative property
  have key :
    UniqueDiffWithinAt 𝕜
      (G '' (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' (extChartAt I' x).source)) ∩ F.target)) (G (F z)) :=
    D₂.unique_diff_within_at B C
  have : G (F z) = (extChartAt I' x) x := by dsimp [G, F]; simp only [hx.1, mfld_simps]
  rw [this] at key
  apply key.mono
  show
    G '' (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' (extChartAt I' x).source)) ∩ F.target) ⊆
      (extChartAt I' x).symm ⁻¹' e.target ∩ (extChartAt I' x).symm ⁻¹' (e.symm ⁻¹' s) ∩ range I'
  rw [image_subset_iff]
  mfld_set_tac
#align unique_mdiff_on.unique_mdiff_on_preimage UniqueMDiffOn.uniqueMDiffOn_preimage
-/

#print UniqueMDiffOn.uniqueDiffOn_target_inter /-
/-- If a set in a manifold has the unique derivative property, then its pullback by any extended
chart, in the vector space, also has the unique derivative property. -/
theorem UniqueMDiffOn.uniqueDiffOn_target_inter (hs : UniqueMDiffOn I s) (x : M) :
    UniqueDiffOn 𝕜 ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) :=
  by
  -- this is just a reformulation of `unique_mdiff_on.unique_mdiff_on_preimage`, using as `e`
  -- the local chart at `x`.
  intro z hz
  simp only [mfld_simps] at hz
  have : (chart_at H x).MDifferentiable I I := mdifferentiable_chart _ _
  have T := (hs.unique_mdiff_on_preimage this) (I.symm z)
  simp only [hz.left.left, hz.left.right, hz.right, UniqueMDiffWithinAt, mfld_simps] at T ⊢
  convert T using 1
  rw [@preimage_comp _ _ _ _ (chart_at H x).symm]
  mfld_set_tac
#align unique_mdiff_on.unique_diff_on_target_inter UniqueMDiffOn.uniqueDiffOn_target_inter
-/

#print UniqueMDiffOn.uniqueDiffOn_inter_preimage /-
/-- When considering functions between manifolds, this statement shows up often. It entails
the unique differential of the pullback in extended charts of the set where the function can
be read in the charts. -/
theorem UniqueMDiffOn.uniqueDiffOn_inter_preimage (hs : UniqueMDiffOn I s) (x : M) (y : M')
    {f : M → M'} (hf : ContinuousOn f s) :
    UniqueDiffOn 𝕜
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) :=
  haveI : UniqueMDiffOn I (s ∩ f ⁻¹' (extChartAt I' y).source) :=
    by
    intro z hz
    apply (hs z hz.1).inter'
    apply (hf z hz.1).preimage_mem_nhdsWithin
    exact (isOpen_extChartAt_source I' y).mem_nhds hz.2
  this.unique_diff_on_target_inter _
#align unique_mdiff_on.unique_diff_on_inter_preimage UniqueMDiffOn.uniqueDiffOn_inter_preimage
-/

open Bundle

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (Z : M → Type _)
  [TopologicalSpace (TotalSpace F Z)] [∀ b, TopologicalSpace (Z b)] [∀ b, AddCommMonoid (Z b)]
  [∀ b, Module 𝕜 (Z b)] [FiberBundle F Z] [VectorBundle 𝕜 F Z] [SmoothVectorBundle F Z I]

/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ././././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print UniqueMDiffOn.smooth_bundle_preimage /-
/-- In a smooth fiber bundle, the preimage under the projection of a set with
unique differential in the basis also has unique differential. -/
theorem UniqueMDiffOn.smooth_bundle_preimage (hs : UniqueMDiffOn I s) :
    UniqueMDiffOn (I.Prod 𝓘(𝕜, F)) (π F Z ⁻¹' s) :=
  by
  /- Using a chart (and the fact that unique differentiability is invariant under charts), we
    reduce the situation to the model space, where we can use the fact that products respect
    unique differentiability. -/
  intro p hp
  replace hp : p.1 ∈ s; · simpa only [mfld_simps] using hp
  let e₀ := chart_at H p.1
  let e := chart_at (ModelProd H F) p
  have h2s :
    ∀ x,
      x ∈ e.target ∩ e.symm ⁻¹' (π F Z ⁻¹' s) ↔
        (x.1 ∈ e₀.target ∧ e₀.symm x.1 ∈ (trivialization_at F Z p.1).baseSet) ∧ e₀.symm x.1 ∈ s :=
    by
    intro x
    have A : x ∈ e.target ↔ x.1 ∈ e₀.target ∧ e₀.symm x.1 ∈ (trivialization_at F Z p.1).baseSet :=
      by
      simp only [e, FiberBundle.chartedSpace_chartAt, Trivialization.mem_target,
        Bundle.TotalSpace.proj, mfld_simps]
    rw [← A, mem_inter_iff, and_congr_right_iff]
    intro hx
    simp only [FiberBundle.chartedSpace_chartAt_symm_fst p x hx, mfld_simps]
  -- It suffices to prove unique differentiability in a chart
  suffices h : UniqueMDiffOn (I.prod 𝓘(𝕜, F)) (e.target ∩ e.symm ⁻¹' (π F Z ⁻¹' s))
  · have A :
      UniqueMDiffOn (I.prod 𝓘(𝕜, F))
        (e.symm.target ∩ e.symm.symm ⁻¹' (e.target ∩ e.symm ⁻¹' (π F Z ⁻¹' s))) :=
      by
      apply h.unique_mdiff_on_preimage
      exact (mdifferentiable_of_mem_atlas _ (chart_mem_atlas _ _)).symm
      infer_instance
    have : p ∈ e.symm.target ∩ e.symm.symm ⁻¹' (e.target ∩ e.symm ⁻¹' (π F Z ⁻¹' s)) := by
      simp only [e, hp, mfld_simps]
    apply (A _ this).mono
    intro q hq
    simp only [e, PartialHomeomorph.left_inv _ hq.1, mfld_simps] at hq
    simp only [hq, mfld_simps]
  intro q hq
  simp only [UniqueMDiffWithinAt, ModelWithCorners.prod, -preimage_inter, mfld_simps]
  have :
    𝓝[(I.symm ⁻¹' (e₀.target ∩ e₀.symm ⁻¹' s) ∩ range I) ×ˢ univ] (I q.1, q.2) ≤
      𝓝[(fun p : E × F => (I.symm p.1, p.snd)) ⁻¹' (e.target ∩ e.symm ⁻¹' (π F Z ⁻¹' s)) ∩
          range I ×ˢ univ]
        (I q.1, q.2) :=
    by
    rw [nhdsWithin_le_iff, mem_nhdsWithin]
    refine' ⟨(fun p : E × F => (I.symm p.1, p.snd)) ⁻¹' e.target, _, _, _⟩
    · exact e.open_target.preimage (I.continuous_symm.prod_map continuous_id)
    · simp only [Prod.mk.eta, mfld_simps] at hq
      simp only [Prod.mk.eta, hq, mfld_simps]
    rintro x hx
    simp only [mfld_simps] at hx
    have h2x := hx
    simp only [e, FiberBundle.chartedSpace_chartAt, Trivialization.mem_target, mfld_simps] at h2x
    simp only [h2s, hx, h2x, -preimage_inter, mfld_simps]
  refine' UniqueDiffWithinAt.mono_nhds _ this
  rw [h2s] at hq
  -- apply unique differentiability of products to conclude
  apply UniqueDiffOn.prod _ uniqueDiffOn_univ
  · simp only [hq, mfld_simps]
  · intro x hx
    have A : UniqueMDiffOn I (e₀.target ∩ e₀.symm ⁻¹' s) :=
      by
      apply hs.unique_mdiff_on_preimage
      exact mdifferentiable_of_mem_atlas _ (chart_mem_atlas _ _)
      infer_instance
    simp only [UniqueMDiffOn, UniqueMDiffWithinAt, preimage_inter, mfld_simps] at A
    have B := A (I.symm x) hx.1.1 hx.1.2
    rwa [← preimage_inter, ModelWithCorners.right_inv _ hx.2] at B
#align unique_mdiff_on.smooth_bundle_preimage UniqueMDiffOn.smooth_bundle_preimage
-/

#print UniqueMDiffOn.tangentBundle_proj_preimage /-
theorem UniqueMDiffOn.tangentBundle_proj_preimage (hs : UniqueMDiffOn I s) :
    UniqueMDiffOn I.tangent (π E (TangentSpace I) ⁻¹' s) :=
  hs.smooth_bundle_preimage _
#align unique_mdiff_on.tangent_bundle_proj_preimage UniqueMDiffOn.tangentBundle_proj_preimage
-/

end UniqueMdiff

