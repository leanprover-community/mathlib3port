/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module geometry.manifold.smooth_manifold_with_corners
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.ContDiff
import Mathbin.Geometry.Manifold.ChartedSpace

/-!
# Smooth manifolds (possibly with boundary or corners)

A smooth manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which the changes of coordinates are smooth maps.
We define a model with corners as a map `I : H → E` embedding nicely the topological space `H` in
the vector space `E` (or more precisely as a structure containing all the relevant properties).
Given such a model with corners `I` on `(E, H)`, we define the groupoid of local
homeomorphisms of `H` which are smooth when read in `E` (for any regularity `n : ℕ∞`).
With this groupoid at hand and the general machinery of charted spaces, we thus get the notion
of `C^n` manifold with respect to any model with corners `I` on `(E, H)`. We also introduce a
specific type class for `C^∞` manifolds as these are the most commonly used.

## Main definitions

* `model_with_corners 𝕜 E H` :
  a structure containing informations on the way a space `H` embeds in a
  model vector space E over the field `𝕜`. This is all that is needed to
  define a smooth manifold with model space `H`, and model vector space `E`.
* `model_with_corners_self 𝕜 E` :
  trivial model with corners structure on the space `E` embedded in itself by the identity.
* `cont_diff_groupoid n I` :
  when `I` is a model with corners on `(𝕜, E, H)`, this is the groupoid of local homeos of `H`
  which are of class `C^n` over the normed field `𝕜`, when read in `E`.
* `smooth_manifold_with_corners I M` :
  a type class saying that the charted space `M`, modelled on the space `H`, has `C^∞` changes of
  coordinates with respect to the model with corners `I` on `(𝕜, E, H)`. This type class is just
  a shortcut for `has_groupoid M (cont_diff_groupoid ∞ I)`.
* `ext_chart_at I x`:
  in a smooth manifold with corners with the model `I` on `(E, H)`, the charts take values in `H`,
  but often we may want to use their `E`-valued version, obtained by composing the charts with `I`.
  Since the target is in general not open, we can not register them as local homeomorphisms, but
  we register them as local equivs. `ext_chart_at I x` is the canonical such local equiv around `x`.

As specific examples of models with corners, we define (in the file `real_instances.lean`)
* `model_with_corners_self ℝ (euclidean_space (fin n))` for the model space used to define
  `n`-dimensional real manifolds without boundary (with notation `𝓡 n` in the locale `manifold`)
* `model_with_corners ℝ (euclidean_space (fin n)) (euclidean_half_space n)` for the model space
  used to define `n`-dimensional real manifolds with boundary (with notation `𝓡∂ n` in the locale
  `manifold`)
* `model_with_corners ℝ (euclidean_space (fin n)) (euclidean_quadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

With these definitions at hand, to invoke an `n`-dimensional real manifold without boundary,
one could use

  `variables {n : ℕ} {M : Type*} [topological_space M] [charted_space (euclidean_space (fin n)) M]
   [smooth_manifold_with_corners (𝓡 n) M]`.

However, this is not the recommended way: a theorem proved using this assumption would not apply
for instance to the tangent space of such a manifold, which is modelled on
`(euclidean_space (fin n)) × (euclidean_space (fin n))` and not on `euclidean_space (fin (2 * n))`!
In the same way, it would not apply to product manifolds, modelled on
`(euclidean_space (fin n)) × (euclidean_space (fin m))`.
The right invocation does not focus on one specific construction, but on all constructions sharing
the right properties, like

  `variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {I : model_with_corners ℝ E E} [I.boundaryless]
  {M : Type*} [topological_space M] [charted_space E M] [smooth_manifold_with_corners I M]`

Here, `I.boundaryless` is a typeclass property ensuring that there is no boundary (this is for
instance the case for `model_with_corners_self`, or products of these). Note that one could consider
as a natural assumption to only use the trivial model with corners `model_with_corners_self ℝ E`,
but again in product manifolds the natural model with corners will not be this one but the product
one (and they are not defeq as `(λp : E × F, (p.1, p.2))` is not defeq to the identity). So, it is
important to use the above incantation to maximize the applicability of theorems.

## Implementation notes

We want to talk about manifolds modelled on a vector space, but also on manifolds with
boundary, modelled on a half space (or even manifolds with corners). For the latter examples,
we still want to define smooth functions, tangent bundles, and so on. As smooth functions are
well defined on vector spaces or subsets of these, one could take for model space a subtype of a
vector space. With the drawback that the whole vector space itself (which is the most basic
example) is not directly a subtype of itself: the inclusion of `univ : set E` in `set E` would
show up in the definition, instead of `id`.

A good abstraction covering both cases it to have a vector
space `E` (with basic example the Euclidean space), a model space `H` (with basic example the upper
half space), and an embedding of `H` into `E` (which can be the identity for `H = E`, or
`subtype.val` for manifolds with corners). We say that the pair `(E, H)` with their embedding is a
model with corners, and we encompass all the relevant properties (in particular the fact that the
image of `H` in `E` should have unique differentials) in the definition of `model_with_corners`.

We concentrate on `C^∞` manifolds: all the definitions work equally well for `C^n` manifolds, but
later on it is a pain to carry all over the smoothness parameter, especially when one wants to deal
with `C^k` functions as there would be additional conditions `k ≤ n` everywhere. Since one deals
almost all the time with `C^∞` (or analytic) manifolds, this seems to be a reasonable choice that
one could revisit later if needed. `C^k` manifolds are still available, but they should be called
using `has_groupoid M (cont_diff_groupoid k I)` where `I` is the model with corners.

I have considered using the model with corners `I` as a typeclass argument, possibly `out_param`, to
get lighter notations later on, but it did not turn out right, as on `E × F` there are two natural
model with corners, the trivial (identity) one, and the product one, and they are not defeq and one
needs to indicate to Lean which one we want to use.
This means that when talking on objects on manifolds one will most often need to specify the model
with corners one is using. For instance, the tangent bundle will be `tangent_bundle I M` and the
derivative will be `mfderiv I I' f`, instead of the more natural notations `tangent_bundle 𝕜 M` and
`mfderiv 𝕜 f` (the field has to be explicit anyway, as some manifolds could be considered both as
real and complex manifolds).
-/


noncomputable section

universe u v w u' v' w'

open Set Filter Function

open Manifold Filter TopologicalSpace

-- mathport name: with_top.nat.top
scoped[Manifold] notation "∞" => (⊤ : ℕ∞)

/-! ### Models with corners. -/


/-- A structure containing informations on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all what is needed to
define a smooth manifold with model space `H`, and model vector space `E`.
-/
@[ext, nolint has_nonempty_instance]
structure ModelWithCorners (𝕜 : Type _) [NontriviallyNormedField 𝕜] (E : Type _)
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (H : Type _) [TopologicalSpace H] extends
  LocalEquiv H E where
  source_eq : source = univ
  uniqueDiff' : UniqueDiffOn 𝕜 to_local_equiv.target
  continuous_to_fun : Continuous to_fun := by continuity
  continuous_inv_fun : Continuous inv_fun := by continuity
#align model_with_corners ModelWithCorners

attribute [simp, mfld_simps] ModelWithCorners.source_eq

/-- A vector space is a model with corners. -/
def modelWithCornersSelf (𝕜 : Type _) [NontriviallyNormedField 𝕜] (E : Type _)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : ModelWithCorners 𝕜 E E
    where
  toLocalEquiv := LocalEquiv.refl E
  source_eq := rfl
  uniqueDiff' := uniqueDiffOnUniv
  continuous_to_fun := continuous_id
  continuous_inv_fun := continuous_id
#align model_with_corners_self modelWithCornersSelf

-- mathport name: model_with_corners_self
scoped[Manifold] notation "𝓘(" 𝕜 ", " E ")" => modelWithCornersSelf 𝕜 E

-- mathport name: model_with_corners_self.self
scoped[Manifold] notation "𝓘(" 𝕜 ")" => modelWithCornersSelf 𝕜 𝕜

section

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)

namespace ModelWithCorners

instance : CoeFun (ModelWithCorners 𝕜 E H) fun _ => H → E :=
  ⟨fun e => e.toFun⟩

/-- The inverse to a model with corners, only registered as a local equiv. -/
protected def symm : LocalEquiv E H :=
  I.toLocalEquiv.symm
#align model_with_corners.symm ModelWithCorners.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (𝕜 : Type _) [NontriviallyNormedField 𝕜] (E : Type _) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type _) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : H → E :=
  I
#align model_with_corners.simps.apply ModelWithCorners.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symmApply (𝕜 : Type _) [NontriviallyNormedField 𝕜] (E : Type _) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (H : Type _) [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) : E → H :=
  I.symm
#align model_with_corners.simps.symm_apply ModelWithCorners.Simps.symmApply

initialize_simps_projections ModelWithCorners (to_local_equiv_to_fun → apply,
  to_local_equiv_inv_fun → symmApply, to_local_equiv_source → source, to_local_equiv_target →
  target, -toLocalEquiv)

-- Register a few lemmas to make sure that `simp` puts expressions in normal form
@[simp, mfld_simps]
theorem to_local_equiv_coe : (I.toLocalEquiv : H → E) = I :=
  rfl
#align model_with_corners.to_local_equiv_coe ModelWithCorners.to_local_equiv_coe

@[simp, mfld_simps]
theorem mk_coe (e : LocalEquiv H E) (a b c d) :
    ((ModelWithCorners.mk e a b c d : ModelWithCorners 𝕜 E H) : H → E) = (e : H → E) :=
  rfl
#align model_with_corners.mk_coe ModelWithCorners.mk_coe

@[simp, mfld_simps]
theorem to_local_equiv_coe_symm : (I.toLocalEquiv.symm : E → H) = I.symm :=
  rfl
#align model_with_corners.to_local_equiv_coe_symm ModelWithCorners.to_local_equiv_coe_symm

@[simp, mfld_simps]
theorem mk_symm (e : LocalEquiv H E) (a b c d) :
    (ModelWithCorners.mk e a b c d : ModelWithCorners 𝕜 E H).symm = e.symm :=
  rfl
#align model_with_corners.mk_symm ModelWithCorners.mk_symm

@[continuity]
protected theorem continuous : Continuous I :=
  I.continuous_to_fun
#align model_with_corners.continuous ModelWithCorners.continuous

protected theorem continuous_at {x} : ContinuousAt I x :=
  I.Continuous.ContinuousAt
#align model_with_corners.continuous_at ModelWithCorners.continuous_at

protected theorem continuous_within_at {s x} : ContinuousWithinAt I s x :=
  I.ContinuousAt.ContinuousWithinAt
#align model_with_corners.continuous_within_at ModelWithCorners.continuous_within_at

@[continuity]
theorem continuous_symm : Continuous I.symm :=
  I.continuous_inv_fun
#align model_with_corners.continuous_symm ModelWithCorners.continuous_symm

theorem continuous_at_symm {x} : ContinuousAt I.symm x :=
  I.continuous_symm.ContinuousAt
#align model_with_corners.continuous_at_symm ModelWithCorners.continuous_at_symm

theorem continuous_within_at_symm {s x} : ContinuousWithinAt I.symm s x :=
  I.continuous_symm.ContinuousWithinAt
#align model_with_corners.continuous_within_at_symm ModelWithCorners.continuous_within_at_symm

theorem continuous_on_symm {s} : ContinuousOn I.symm s :=
  I.continuous_symm.ContinuousOn
#align model_with_corners.continuous_on_symm ModelWithCorners.continuous_on_symm

@[simp, mfld_simps]
theorem target_eq : I.target = range (I : H → E) :=
  by
  rw [← image_univ, ← I.source_eq]
  exact I.to_local_equiv.image_source_eq_target.symm
#align model_with_corners.target_eq ModelWithCorners.target_eq

protected theorem uniqueDiff : UniqueDiffOn 𝕜 (range I) :=
  I.target_eq ▸ I.uniqueDiff'
#align model_with_corners.unique_diff ModelWithCorners.uniqueDiff

@[simp, mfld_simps]
protected theorem left_inv (x : H) : I.symm (I x) = x :=
  by
  refine' I.left_inv' _
  simp
#align model_with_corners.left_inv ModelWithCorners.left_inv

protected theorem left_inverse : LeftInverse I.symm I :=
  I.left_inv
#align model_with_corners.left_inverse ModelWithCorners.left_inverse

theorem injective : Injective I :=
  I.LeftInverse.Injective
#align model_with_corners.injective ModelWithCorners.injective

@[simp, mfld_simps]
theorem symm_comp_self : I.symm ∘ I = id :=
  I.LeftInverse.comp_eq_id
#align model_with_corners.symm_comp_self ModelWithCorners.symm_comp_self

protected theorem right_inv_on : RightInvOn I.symm I (range I) :=
  I.LeftInverse.right_inv_on_range
#align model_with_corners.right_inv_on ModelWithCorners.right_inv_on

@[simp, mfld_simps]
protected theorem right_inv {x : E} (hx : x ∈ range I) : I (I.symm x) = x :=
  I.RightInvOn hx
#align model_with_corners.right_inv ModelWithCorners.right_inv

theorem preimage_image (s : Set H) : I ⁻¹' (I '' s) = s :=
  I.Injective.preimage_image s
#align model_with_corners.preimage_image ModelWithCorners.preimage_image

protected theorem image_eq (s : Set H) : I '' s = I.symm ⁻¹' s ∩ range I :=
  by
  refine' (I.to_local_equiv.image_eq_target_inter_inv_preimage _).trans _
  · rw [I.source_eq]
    exact subset_univ _
  · rw [inter_comm, I.target_eq, I.to_local_equiv_coe_symm]
#align model_with_corners.image_eq ModelWithCorners.image_eq

protected theorem closed_embedding : ClosedEmbedding I :=
  I.LeftInverse.ClosedEmbedding I.continuous_symm I.Continuous
#align model_with_corners.closed_embedding ModelWithCorners.closed_embedding

theorem closed_range : IsClosed (range I) :=
  I.ClosedEmbedding.closed_range
#align model_with_corners.closed_range ModelWithCorners.closed_range

theorem map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[range I] I x :=
  I.ClosedEmbedding.toEmbedding.map_nhds_eq x
#align model_with_corners.map_nhds_eq ModelWithCorners.map_nhds_eq

theorem image_mem_nhds_within {x : H} {s : Set H} (hs : s ∈ 𝓝 x) : I '' s ∈ 𝓝[range I] I x :=
  I.map_nhds_eq x ▸ image_mem_map hs
#align model_with_corners.image_mem_nhds_within ModelWithCorners.image_mem_nhds_within

theorem symm_map_nhds_within_range (x : H) : map I.symm (𝓝[range I] I x) = 𝓝 x := by
  rw [← I.map_nhds_eq, map_map, I.symm_comp_self, map_id]
#align model_with_corners.symm_map_nhds_within_range ModelWithCorners.symm_map_nhds_within_range

theorem uniqueDiffPreimage {s : Set H} (hs : IsOpen s) : UniqueDiffOn 𝕜 (I.symm ⁻¹' s ∩ range I) :=
  by
  rw [inter_comm]
  exact I.unique_diff.inter (hs.preimage I.continuous_inv_fun)
#align model_with_corners.unique_diff_preimage ModelWithCorners.uniqueDiffPreimage

theorem uniqueDiffPreimageSource {β : Type _} [TopologicalSpace β] {e : LocalHomeomorph H β} :
    UniqueDiffOn 𝕜 (I.symm ⁻¹' e.source ∩ range I) :=
  I.uniqueDiffPreimage e.open_source
#align model_with_corners.unique_diff_preimage_source ModelWithCorners.uniqueDiffPreimageSource

theorem uniqueDiffAtImage {x : H} : UniqueDiffWithinAt 𝕜 (range I) (I x) :=
  I.uniqueDiff _ (mem_range_self _)
#align model_with_corners.unique_diff_at_image ModelWithCorners.uniqueDiffAtImage

protected theorem locally_compact [LocallyCompactSpace E] (I : ModelWithCorners 𝕜 E H) :
    LocallyCompactSpace H :=
  by
  have :
    ∀ x : H,
      (𝓝 x).HasBasis (fun s => s ∈ 𝓝 (I x) ∧ IsCompact s) fun s => I.symm '' (s ∩ range ⇑I) :=
    by
    intro x
    rw [← I.symm_map_nhds_within_range]
    exact ((compact_basis_nhds (I x)).inf_principal _).map _
  refine' locally_compact_space_of_has_basis this _
  rintro x s ⟨-, hsc⟩
  exact (hsc.inter_right I.closed_range).image I.continuous_symm
#align model_with_corners.locally_compact ModelWithCorners.locally_compact

open TopologicalSpace

protected theorem second_countable_topology [SecondCountableTopology E]
    (I : ModelWithCorners 𝕜 E H) : SecondCountableTopology H :=
  I.ClosedEmbedding.toEmbedding.SecondCountableTopology
#align model_with_corners.second_countable_topology ModelWithCorners.second_countable_topology

end ModelWithCorners

section

variable (𝕜 E)

/-- In the trivial model with corners, the associated local equiv is the identity. -/
@[simp, mfld_simps]
theorem model_with_corners_self_local_equiv : 𝓘(𝕜, E).toLocalEquiv = LocalEquiv.refl E :=
  rfl
#align model_with_corners_self_local_equiv model_with_corners_self_local_equiv

@[simp, mfld_simps]
theorem model_with_corners_self_coe : (𝓘(𝕜, E) : E → E) = id :=
  rfl
#align model_with_corners_self_coe model_with_corners_self_coe

@[simp, mfld_simps]
theorem model_with_corners_self_coe_symm : (𝓘(𝕜, E).symm : E → E) = id :=
  rfl
#align model_with_corners_self_coe_symm model_with_corners_self_coe_symm

end

end

section ModelWithCornersProd

/-- Given two model_with_corners `I` on `(E, H)` and `I'` on `(E', H')`, we define the model with
corners `I.prod I'` on `(E × E', model_prod H H')`. This appears in particular for the manifold
structure on the tangent bundle to a manifold modelled on `(E, H)`: it will be modelled on
`(E × E, H × E)`. See note [Manifold type tags] for explanation about `model_prod H H'`
vs `H × H'`. -/
@[simps (config := lemmasOnly)]
def ModelWithCorners.prod {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {E' : Type v'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') :
    ModelWithCorners 𝕜 (E × E') (ModelProd H H') :=
  {
    I.toLocalEquiv.Prod
      I'.toLocalEquiv with
    toFun := fun x => (I x.1, I' x.2)
    invFun := fun x => (I.symm x.1, I'.symm x.2)
    source := { x | x.1 ∈ I.source ∧ x.2 ∈ I'.source }
    source_eq := by simp only [set_of_true, mfld_simps]
    uniqueDiff' := I.uniqueDiff'.Prod I'.uniqueDiff'
    continuous_to_fun := I.continuous_to_fun.prod_map I'.continuous_to_fun
    continuous_inv_fun := I.continuous_inv_fun.prod_map I'.continuous_inv_fun }
#align model_with_corners.prod ModelWithCorners.prod

/-- Given a finite family of `model_with_corners` `I i` on `(E i, H i)`, we define the model with
corners `pi I` on `(Π i, E i, model_pi H)`. See note [Manifold type tags] for explanation about
`model_pi H`. -/
def ModelWithCorners.pi {𝕜 : Type u} [NontriviallyNormedField 𝕜] {ι : Type v} [Fintype ι]
    {E : ι → Type w} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] {H : ι → Type u'}
    [∀ i, TopologicalSpace (H i)] (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i)) :
    ModelWithCorners 𝕜 (∀ i, E i) (ModelPi H)
    where
  toLocalEquiv := LocalEquiv.pi fun i => (I i).toLocalEquiv
  source_eq := by simp only [Set.pi_univ, mfld_simps]
  uniqueDiff' := UniqueDiffOn.pi ι E _ _ fun i _ => (I i).uniqueDiff'
  continuous_to_fun := continuous_pi fun i => (I i).Continuous.comp (continuous_apply i)
  continuous_inv_fun := continuous_pi fun i => (I i).continuous_symm.comp (continuous_apply i)
#align model_with_corners.pi ModelWithCorners.pi

/-- Special case of product model with corners, which is trivial on the second factor. This shows up
as the model to tangent bundles. -/
@[reducible]
def ModelWithCorners.tangent {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) : ModelWithCorners 𝕜 (E × E) (ModelProd H E) :=
  I.Prod 𝓘(𝕜, E)
#align model_with_corners.tangent ModelWithCorners.tangent

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {F' : Type _} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type _} [TopologicalSpace H] {H' : Type _} [TopologicalSpace H'] {G : Type _}
  [TopologicalSpace G] {G' : Type _} [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 F G}

@[simp, mfld_simps]
theorem model_with_corners_prod_to_local_equiv :
    (I.Prod J).toLocalEquiv = I.toLocalEquiv.Prod J.toLocalEquiv :=
  rfl
#align model_with_corners_prod_to_local_equiv model_with_corners_prod_to_local_equiv

@[simp, mfld_simps]
theorem model_with_corners_prod_coe (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') :
    (I.Prod I' : _ × _ → _ × _) = Prod.map I I' :=
  rfl
#align model_with_corners_prod_coe model_with_corners_prod_coe

@[simp, mfld_simps]
theorem model_with_corners_prod_coe_symm (I : ModelWithCorners 𝕜 E H)
    (I' : ModelWithCorners 𝕜 E' H') :
    ((I.Prod I').symm : _ × _ → _ × _) = Prod.map I.symm I'.symm :=
  rfl
#align model_with_corners_prod_coe_symm model_with_corners_prod_coe_symm

theorem model_with_corners_self_prod : 𝓘(𝕜, E × F) = 𝓘(𝕜, E).Prod 𝓘(𝕜, F) :=
  by
  ext1
  simp
#align model_with_corners_self_prod model_with_corners_self_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem ModelWithCorners.range_prod : range (I.Prod J) = range I ×ˢ range J :=
  by
  simp_rw [← ModelWithCorners.target_eq]
  rfl
#align model_with_corners.range_prod ModelWithCorners.range_prod

end ModelWithCornersProd

section Boundaryless

/-- Property ensuring that the model with corners `I` defines manifolds without boundary. -/
class ModelWithCorners.Boundaryless {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) : Prop where
  range_eq_univ : range I = univ
#align model_with_corners.boundaryless ModelWithCorners.Boundaryless

/-- The trivial model with corners has no boundary -/
instance modelWithCornersSelfBoundaryless (𝕜 : Type _) [NontriviallyNormedField 𝕜] (E : Type _)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : (modelWithCornersSelf 𝕜 E).Boundaryless :=
  ⟨by simp⟩
#align model_with_corners_self_boundaryless modelWithCornersSelfBoundaryless

/-- If two model with corners are boundaryless, their product also is -/
instance ModelWithCorners.rangeEqUnivProd {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type w} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] {E' : Type v'} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type w'} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
    [I'.Boundaryless] : (I.Prod I').Boundaryless :=
  by
  constructor
  dsimp [ModelWithCorners.prod, ModelProd]
  rw [← prod_range_range_eq, ModelWithCorners.Boundaryless.range_eq_univ,
    ModelWithCorners.Boundaryless.range_eq_univ, univ_prod_univ]
#align model_with_corners.range_eq_univ_prod ModelWithCorners.rangeEqUnivProd

end Boundaryless

section contDiffGroupoid

/-! ### Smooth functions on models with corners -/


variable {m n : ℕ∞} {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
  [TopologicalSpace M]

variable (n)

/-- Given a model with corners `(E, H)`, we define the groupoid of `C^n` transformations of `H` as
the maps that are `C^n` when read in `E` through `I`. -/
def contDiffGroupoid : StructureGroupoid H :=
  Pregroupoid.groupoid
    { property := fun f s => ContDiffOn 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
      comp := fun f g u v hf hg hu hv huv =>
        by
        have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ I ∘ f ∘ I.symm :=
          by
          ext x
          simp
        rw [this]
        apply ContDiffOn.comp hg _
        · rintro x ⟨hx1, hx2⟩
          simp only [mfld_simps] at hx1⊢
          exact hx1.2
        · refine' hf.mono _
          rintro x ⟨hx1, hx2⟩
          exact ⟨hx1.1, hx2⟩
      id_mem := by
        apply ContDiffOn.congr cont_diff_id.cont_diff_on
        rintro x ⟨hx1, hx2⟩
        rcases mem_range.1 hx2 with ⟨y, hy⟩
        rw [← hy]
        simp only [mfld_simps]
      locality := fun f u hu H => by
        apply contDiffOnOfLocallyContDiffOn
        rintro y ⟨hy1, hy2⟩
        rcases mem_range.1 hy2 with ⟨x, hx⟩
        rw [← hx] at hy1⊢
        simp only [mfld_simps] at hy1⊢
        rcases H x hy1 with ⟨v, v_open, xv, hv⟩
        have : I.symm ⁻¹' (u ∩ v) ∩ range I = I.symm ⁻¹' u ∩ range I ∩ I.symm ⁻¹' v :=
          by
          rw [preimage_inter, inter_assoc, inter_assoc]
          congr 1
          rw [inter_comm]
        rw [this] at hv
        exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, hv⟩
      congr := fun f g u hu fg hf => by
        apply hf.congr
        rintro y ⟨hy1, hy2⟩
        rcases mem_range.1 hy2 with ⟨x, hx⟩
        rw [← hx] at hy1⊢
        simp only [mfld_simps] at hy1⊢
        rw [fg _ hy1] }
#align cont_diff_groupoid contDiffGroupoid

variable {n}

/-- Inclusion of the groupoid of `C^n` local diffeos in the groupoid of `C^m` local diffeos when
`m ≤ n` -/
theorem cont_diff_groupoid_le (h : m ≤ n) : contDiffGroupoid n I ≤ contDiffGroupoid m I :=
  by
  rw [contDiffGroupoid, contDiffGroupoid]
  apply groupoid_of_pregroupoid_le
  intro f s hfs
  exact ContDiffOn.ofLe hfs h
#align cont_diff_groupoid_le cont_diff_groupoid_le

/-- The groupoid of `0`-times continuously differentiable maps is just the groupoid of all
local homeomorphisms -/
theorem cont_diff_groupoid_zero_eq : contDiffGroupoid 0 I = continuousGroupoid H :=
  by
  apply le_antisymm le_top
  intro u hu
  -- we have to check that every local homeomorphism belongs to `cont_diff_groupoid 0 I`,
  -- by unfolding its definition
  change u ∈ contDiffGroupoid 0 I
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  simp only [cont_diff_on_zero]
  constructor
  · refine' I.continuous.comp_continuous_on (u.continuous_on.comp I.continuous_on_symm _)
    exact (maps_to_preimage _ _).mono_left (inter_subset_left _ _)
  · refine' I.continuous.comp_continuous_on (u.symm.continuous_on.comp I.continuous_on_symm _)
    exact (maps_to_preimage _ _).mono_left (inter_subset_left _ _)
#align cont_diff_groupoid_zero_eq cont_diff_groupoid_zero_eq

variable (n)

/-- An identity local homeomorphism belongs to the `C^n` groupoid. -/
theorem of_set_mem_cont_diff_groupoid {s : Set H} (hs : IsOpen s) :
    LocalHomeomorph.ofSet s hs ∈ contDiffGroupoid n I :=
  by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  suffices h : ContDiffOn 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
  · simp [h]
  have : ContDiffOn 𝕜 n id (univ : Set E) := cont_diff_id.cont_diff_on
  exact this.congr_mono (fun x hx => by simp [hx.2]) (subset_univ _)
#align of_set_mem_cont_diff_groupoid of_set_mem_cont_diff_groupoid

/-- The composition of a local homeomorphism from `H` to `M` and its inverse belongs to
the `C^n` groupoid. -/
theorem symm_trans_mem_cont_diff_groupoid (e : LocalHomeomorph M H) :
    e.symm.trans e ∈ contDiffGroupoid n I :=
  haveI : e.symm.trans e ≈ LocalHomeomorph.ofSet e.target e.open_target :=
    LocalHomeomorph.trans_symm_self _
  StructureGroupoid.eq_on_source _ (of_set_mem_cont_diff_groupoid n I e.open_target) this
#align symm_trans_mem_cont_diff_groupoid symm_trans_mem_cont_diff_groupoid

variable {E' H' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']

/-- The product of two smooth local homeomorphisms is smooth. -/
theorem cont_diff_groupoid_prod {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    {e : LocalHomeomorph H H} {e' : LocalHomeomorph H' H'} (he : e ∈ contDiffGroupoid ⊤ I)
    (he' : e' ∈ contDiffGroupoid ⊤ I') : e.Prod e' ∈ contDiffGroupoid ⊤ (I.Prod I') :=
  by
  cases' he with he he_symm
  cases' he' with he' he'_symm
  simp only at he he_symm he' he'_symm
  constructor <;> simp only [LocalEquiv.prod_source, LocalHomeomorph.prod_to_local_equiv]
  · have h3 := ContDiffOn.prodMap he he'
    rw [← I.image_eq, ← I'.image_eq, Set.prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3
  · have h3 := ContDiffOn.prodMap he_symm he'_symm
    rw [← I.image_eq, ← I'.image_eq, Set.prod_image_image_eq] at h3
    rw [← (I.prod I').image_eq]
    exact h3
#align cont_diff_groupoid_prod cont_diff_groupoid_prod

/-- The `C^n` groupoid is closed under restriction. -/
instance : ClosedUnderRestriction (contDiffGroupoid n I) :=
  (closed_under_restriction_iff_id_le _).mpr
    (by
      apply structure_groupoid.le_iff.mpr
      rintro e ⟨s, hs, hes⟩
      apply (contDiffGroupoid n I).eq_on_source' _ _ _ hes
      exact of_set_mem_cont_diff_groupoid n I hs)

end contDiffGroupoid

section SmoothManifoldWithCorners

/-! ### Smooth manifolds with corners -/


/-- Typeclass defining smooth manifolds with corners with respect to a model with corners, over a
field `𝕜` and with infinite smoothness to simplify typeclass search and statements later on. -/
class SmoothManifoldWithCorners {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M] extends
  HasGroupoid M (contDiffGroupoid ∞ I) : Prop
#align smooth_manifold_with_corners SmoothManifoldWithCorners

theorem SmoothManifoldWithCorners.mk' {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
    [gr : HasGroupoid M (contDiffGroupoid ∞ I)] : SmoothManifoldWithCorners I M :=
  { gr with }
#align smooth_manifold_with_corners.mk' SmoothManifoldWithCorners.mk'

theorem smoothManifoldWithCornersOfContDiffOn {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
    (h :
      ∀ e e' : LocalHomeomorph M H,
        e ∈ atlas H M →
          e' ∈ atlas H M →
            ContDiffOn 𝕜 ⊤ (I ∘ e.symm ≫ₕ e' ∘ I.symm)
              (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I)) :
    SmoothManifoldWithCorners I M :=
  {
    compatible :=
      by
      haveI : HasGroupoid M (contDiffGroupoid ∞ I) := has_groupoid_of_pregroupoid _ h
      apply StructureGroupoid.compatible }
#align smooth_manifold_with_corners_of_cont_diff_on smoothManifoldWithCornersOfContDiffOn

/-- For any model with corners, the model space is a smooth manifold -/
instance modelSpaceSmooth {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} : SmoothManifoldWithCorners I H :=
  { has_groupoid_model_space _ _ with }
#align model_space_smooth modelSpaceSmooth

end SmoothManifoldWithCorners

namespace SmoothManifoldWithCorners

/- We restate in the namespace `smooth_manifolds_with_corners` some lemmas that hold for general
charted space with a structure groupoid, avoiding the need to specify the groupoid
`cont_diff_groupoid ∞ I` explicitly. -/
variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type _)
  [TopologicalSpace M] [ChartedSpace H M]

/-- The maximal atlas of `M` for the smooth manifold with corners structure corresponding to the
model with corners `I`. -/
def maximalAtlas :=
  (contDiffGroupoid ∞ I).maximalAtlas M
#align smooth_manifold_with_corners.maximal_atlas SmoothManifoldWithCorners.maximalAtlas

variable {M}

theorem subset_maximal_atlas [SmoothManifoldWithCorners I M] : atlas H M ⊆ maximalAtlas I M :=
  StructureGroupoid.subset_maximal_atlas _
#align
  smooth_manifold_with_corners.subset_maximal_atlas SmoothManifoldWithCorners.subset_maximal_atlas

theorem chart_mem_maximal_atlas [SmoothManifoldWithCorners I M] (x : M) :
    chartAt H x ∈ maximalAtlas I M :=
  StructureGroupoid.chart_mem_maximal_atlas _ x
#align
  smooth_manifold_with_corners.chart_mem_maximal_atlas SmoothManifoldWithCorners.chart_mem_maximal_atlas

variable {I}

theorem compatible_of_mem_maximal_atlas {e e' : LocalHomeomorph M H} (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I M) : e.symm.trans e' ∈ contDiffGroupoid ∞ I :=
  StructureGroupoid.compatible_of_mem_maximal_atlas he he'
#align
  smooth_manifold_with_corners.compatible_of_mem_maximal_atlas SmoothManifoldWithCorners.compatible_of_mem_maximal_atlas

/-- The product of two smooth manifolds with corners is naturally a smooth manifold with corners. -/
instance prod {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type _}
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type _} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] (M' : Type _) [TopologicalSpace M'] [ChartedSpace H' M']
    [SmoothManifoldWithCorners I' M'] : SmoothManifoldWithCorners (I.Prod I') (M × M')
    where compatible :=
    by
    rintro f g ⟨f1, f2, hf1, hf2, rfl⟩ ⟨g1, g2, hg1, hg2, rfl⟩
    rw [LocalHomeomorph.prod_symm, LocalHomeomorph.prod_trans]
    have h1 := HasGroupoid.compatible (contDiffGroupoid ⊤ I) hf1 hg1
    have h2 := HasGroupoid.compatible (contDiffGroupoid ⊤ I') hf2 hg2
    exact cont_diff_groupoid_prod h1 h2
#align smooth_manifold_with_corners.prod SmoothManifoldWithCorners.prod

end SmoothManifoldWithCorners

theorem LocalHomeomorph.singletonSmoothManifoldWithCorners {𝕜 : Type _} [NontriviallyNormedField 𝕜]
    {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M] (e : LocalHomeomorph M H)
    (h : e.source = Set.univ) :
    @SmoothManifoldWithCorners 𝕜 _ E _ _ H _ I M _ (e.singletonChartedSpace h) :=
  @SmoothManifoldWithCorners.mk' _ _ _ _ _ _ _ _ _ _ (id _) <|
    e.singleton_has_groupoid h (contDiffGroupoid ∞ I)
#align
  local_homeomorph.singleton_smooth_manifold_with_corners LocalHomeomorph.singletonSmoothManifoldWithCorners

theorem OpenEmbedding.singletonSmoothManifoldWithCorners {𝕜 : Type _} [NontriviallyNormedField 𝕜]
    {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) {M : Type _} [TopologicalSpace M] [Nonempty M] {f : M → H}
    (h : OpenEmbedding f) :
    @SmoothManifoldWithCorners 𝕜 _ E _ _ H _ I M _ h.singletonChartedSpace :=
  (h.toLocalHomeomorph f).singletonSmoothManifoldWithCorners I (by simp)
#align
  open_embedding.singleton_smooth_manifold_with_corners OpenEmbedding.singletonSmoothManifoldWithCorners

namespace TopologicalSpace.Opens

open TopologicalSpace

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M] (s : Opens M)

instance : SmoothManifoldWithCorners I s :=
  { s.HasGroupoid (contDiffGroupoid ∞ I) with }

end TopologicalSpace.Opens

section ExtendedCharts

open TopologicalSpace

variable {𝕜 E M H E' M' H' : Type _} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] (f f' : LocalHomeomorph M H)
  (I : ModelWithCorners 𝕜 E H) [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  [TopologicalSpace M'] (I' : ModelWithCorners 𝕜 E' H') (x : M) {s t : Set M}

/-!
### Extended charts

In a smooth manifold with corners, the model space is the space `H`. However, we will also
need to use extended charts taking values in the model vector space `E`. These extended charts are
not `local_homeomorph` as the target is not open in `E` in general, but we can still register them
as `local_equiv`.
-/


namespace LocalHomeomorph

/-- Given a chart `f` on a manifold with corners, `f.extend I` is the extended chart to the model
vector space. -/
@[simp, mfld_simps]
def extend : LocalEquiv M E :=
  f.toLocalEquiv ≫ I.toLocalEquiv
#align local_homeomorph.extend LocalHomeomorph.extend

theorem extend_coe : ⇑(f.extend I) = I ∘ f :=
  rfl
#align local_homeomorph.extend_coe LocalHomeomorph.extend_coe

theorem extend_coe_symm : ⇑(f.extend I).symm = f.symm ∘ I.symm :=
  rfl
#align local_homeomorph.extend_coe_symm LocalHomeomorph.extend_coe_symm

theorem extend_source : (f.extend I).source = f.source := by
  rw [extend, LocalEquiv.trans_source, I.source_eq, preimage_univ, inter_univ]
#align local_homeomorph.extend_source LocalHomeomorph.extend_source

theorem is_open_extend_source : IsOpen (f.extend I).source :=
  by
  rw [extend_source]
  exact f.open_source
#align local_homeomorph.is_open_extend_source LocalHomeomorph.is_open_extend_source

theorem extend_target : (f.extend I).target = I.symm ⁻¹' f.target ∩ range I := by
  simp_rw [extend, LocalEquiv.trans_target, I.target_eq, I.to_local_equiv_coe_symm, inter_comm]
#align local_homeomorph.extend_target LocalHomeomorph.extend_target

theorem maps_to_extend (hs : s ⊆ f.source) :
    MapsTo (f.extend I) s ((f.extend I).symm ⁻¹' s ∩ range I) :=
  by
  rw [maps_to', extend_coe, extend_coe_symm, preimage_comp, ← I.image_eq, image_comp,
    f.image_eq_target_inter_inv_preimage hs]
  exact image_subset _ (inter_subset_right _ _)
#align local_homeomorph.maps_to_extend LocalHomeomorph.maps_to_extend

theorem extend_source_mem_nhds {x : M} (h : x ∈ f.source) : (f.extend I).source ∈ 𝓝 x :=
  (is_open_extend_source f I).mem_nhds <| by rwa [f.extend_source I]
#align local_homeomorph.extend_source_mem_nhds LocalHomeomorph.extend_source_mem_nhds

theorem extend_source_mem_nhds_within {x : M} (h : x ∈ f.source) : (f.extend I).source ∈ 𝓝[s] x :=
  mem_nhds_within_of_mem_nhds <| extend_source_mem_nhds f I h
#align local_homeomorph.extend_source_mem_nhds_within LocalHomeomorph.extend_source_mem_nhds_within

theorem continuous_on_extend : ContinuousOn (f.extend I) (f.extend I).source :=
  by
  refine' I.continuous.comp_continuous_on _
  rw [extend_source]
  exact f.continuous_on
#align local_homeomorph.continuous_on_extend LocalHomeomorph.continuous_on_extend

theorem continuous_at_extend {x : M} (h : x ∈ f.source) : ContinuousAt (f.extend I) x :=
  (continuous_on_extend f I).ContinuousAt <| extend_source_mem_nhds f I h
#align local_homeomorph.continuous_at_extend LocalHomeomorph.continuous_at_extend

theorem map_extend_nhds {x : M} (hy : x ∈ f.source) :
    map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x := by
  rwa [extend_coe, (· ∘ ·), ← I.map_nhds_eq, ← f.map_nhds_eq, map_map]
#align local_homeomorph.map_extend_nhds LocalHomeomorph.map_extend_nhds

theorem extend_target_mem_nhds_within {y : M} (hy : y ∈ f.source) :
    (f.extend I).target ∈ 𝓝[range I] f.extend I y :=
  by
  rw [← LocalEquiv.image_source_eq_target, ← map_extend_nhds f I hy]
  exact image_mem_map (extend_source_mem_nhds _ _ hy)
#align local_homeomorph.extend_target_mem_nhds_within LocalHomeomorph.extend_target_mem_nhds_within

theorem extend_target_subset_range : (f.extend I).target ⊆ range I := by simp only [mfld_simps]
#align local_homeomorph.extend_target_subset_range LocalHomeomorph.extend_target_subset_range

theorem nhds_within_extend_target_eq {y : M} (hy : y ∈ f.source) :
    𝓝[(f.extend I).target] f.extend I y = 𝓝[range I] f.extend I y :=
  (nhds_within_mono _ (extend_target_subset_range _ _)).antisymm <|
    nhds_within_le_of_mem (extend_target_mem_nhds_within _ _ hy)
#align local_homeomorph.nhds_within_extend_target_eq LocalHomeomorph.nhds_within_extend_target_eq

theorem continuous_at_extend_symm' {x : E} (h : x ∈ (f.extend I).target) :
    ContinuousAt (f.extend I).symm x :=
  ContinuousAt.comp (f.continuous_at_symm h.2) I.continuous_symm.ContinuousAt
#align local_homeomorph.continuous_at_extend_symm' LocalHomeomorph.continuous_at_extend_symm'

theorem continuous_at_extend_symm {x : M} (h : x ∈ f.source) :
    ContinuousAt (f.extend I).symm (f.extend I x) :=
  continuous_at_extend_symm' f I <| (f.extend I).map_source <| by rwa [f.extend_source]
#align local_homeomorph.continuous_at_extend_symm LocalHomeomorph.continuous_at_extend_symm

theorem continuous_on_extend_symm : ContinuousOn (f.extend I).symm (f.extend I).target :=
  fun y hy => (continuous_at_extend_symm' _ _ hy).ContinuousWithinAt
#align local_homeomorph.continuous_on_extend_symm LocalHomeomorph.continuous_on_extend_symm

theorem is_open_extend_preimage' {s : Set E} (hs : IsOpen s) :
    IsOpen ((f.extend I).source ∩ f.extend I ⁻¹' s) :=
  (continuous_on_extend f I).preimage_open_of_open (is_open_extend_source _ _) hs
#align local_homeomorph.is_open_extend_preimage' LocalHomeomorph.is_open_extend_preimage'

theorem is_open_extend_preimage {s : Set E} (hs : IsOpen s) :
    IsOpen (f.source ∩ f.extend I ⁻¹' s) :=
  by
  rw [← extend_source f I]
  exact is_open_extend_preimage' f I hs
#align local_homeomorph.is_open_extend_preimage LocalHomeomorph.is_open_extend_preimage

theorem map_extend_nhds_within_eq_image {y : M} (hy : y ∈ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I '' ((f.extend I).source ∩ s)] f.extend I y := by
  set e := f.extend I <;>
    calc
      map e (𝓝[s] y) = map e (𝓝[e.source ∩ s] y) :=
        congr_arg (map e) (nhds_within_inter_of_mem (extend_source_mem_nhds_within f I hy)).symm
      _ = 𝓝[e '' (e.source ∩ s)] e y :=
        ((f.extend I).LeftInvOn.mono <| inter_subset_left _ _).map_nhds_within_eq
          ((f.extend I).left_inv <| by rwa [f.extend_source])
          (continuous_at_extend_symm f I hy).ContinuousWithinAt
          (continuous_at_extend f I hy).ContinuousWithinAt
      
#align
  local_homeomorph.map_extend_nhds_within_eq_image LocalHomeomorph.map_extend_nhds_within_eq_image

theorem map_extend_nhds_within {y : M} (hy : y ∈ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I y := by
  rw [map_extend_nhds_within_eq_image f I hy, nhds_within_inter, ←
    nhds_within_extend_target_eq _ _ hy, ← nhds_within_inter, (f.extend I).image_source_inter_eq',
    inter_comm]
#align local_homeomorph.map_extend_nhds_within LocalHomeomorph.map_extend_nhds_within

theorem map_extend_symm_nhds_within {y : M} (hy : y ∈ f.source) :
    map (f.extend I).symm (𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I y) = 𝓝[s] y :=
  by
  rw [← map_extend_nhds_within f I hy, map_map, map_congr, map_id]
  exact (f.extend I).LeftInvOn.EqOn.eventually_eq_of_mem (extend_source_mem_nhds_within _ _ hy)
#align local_homeomorph.map_extend_symm_nhds_within LocalHomeomorph.map_extend_symm_nhds_within

theorem map_extend_symm_nhds_within_range {y : M} (hy : y ∈ f.source) :
    map (f.extend I).symm (𝓝[range I] f.extend I y) = 𝓝 y := by
  rw [← nhds_within_univ, ← map_extend_symm_nhds_within f I hy, preimage_univ, univ_inter]
#align
  local_homeomorph.map_extend_symm_nhds_within_range LocalHomeomorph.map_extend_symm_nhds_within_range

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
theorem extend_preimage_mem_nhds_within {x : M} (h : x ∈ f.source) (ht : t ∈ 𝓝[s] x) :
    (f.extend I).symm ⁻¹' t ∈ 𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I x := by
  rwa [← map_extend_symm_nhds_within f I h, mem_map] at ht
#align
  local_homeomorph.extend_preimage_mem_nhds_within LocalHomeomorph.extend_preimage_mem_nhds_within

theorem extend_preimage_mem_nhds {x : M} (h : x ∈ f.source) (ht : t ∈ 𝓝 x) :
    (f.extend I).symm ⁻¹' t ∈ 𝓝 (f.extend I x) :=
  by
  apply (continuous_at_extend_symm f I h).preimage_mem_nhds
  rwa [(f.extend I).left_inv]
  rwa [f.extend_source]
#align local_homeomorph.extend_preimage_mem_nhds LocalHomeomorph.extend_preimage_mem_nhds

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
theorem extend_preimage_inter_eq :
    (f.extend I).symm ⁻¹' (s ∩ t) ∩ range I =
      (f.extend I).symm ⁻¹' s ∩ range I ∩ (f.extend I).symm ⁻¹' t :=
  by mfld_set_tac
#align local_homeomorph.extend_preimage_inter_eq LocalHomeomorph.extend_preimage_inter_eq

theorem extend_symm_preimage_inter_range_eventually_eq_aux {s : Set M} {x : M} (hx : x ∈ f.source) :
    ((f.extend I).symm ⁻¹' s ∩ range I : Set _) =ᶠ[𝓝 (f.extend I x)]
      ((f.extend I).target ∩ (f.extend I).symm ⁻¹' s : Set _) :=
  by
  rw [f.extend_target, inter_assoc, inter_comm (range I)]
  conv =>
    congr
    skip
    rw [← @univ_inter _ (_ ∩ _)]
  refine' (eventually_eq_univ.mpr _).symm.inter eventually_eq.rfl
  refine' I.continuous_at_symm.preimage_mem_nhds (f.open_target.mem_nhds _)
  simp_rw [f.extend_coe, Function.comp_apply, I.left_inv, f.maps_to hx]
#align
  local_homeomorph.extend_symm_preimage_inter_range_eventually_eq_aux LocalHomeomorph.extend_symm_preimage_inter_range_eventually_eq_aux

theorem extend_symm_preimage_inter_range_eventually_eq {s : Set M} {x : M} (hs : s ⊆ f.source)
    (hx : x ∈ f.source) :
    ((f.extend I).symm ⁻¹' s ∩ range I : Set _) =ᶠ[𝓝 (f.extend I x)] f.extend I '' s :=
  by
  rw [← f.extend_source I] at hs
  rw [(f.extend I).image_eq_target_inter_inv_preimage hs]
  exact f.extend_symm_preimage_inter_range_eventually_eq_aux I hx
#align
  local_homeomorph.extend_symm_preimage_inter_range_eventually_eq LocalHomeomorph.extend_symm_preimage_inter_range_eventually_eq

/-! We use the name `extend_coord_change` for `(f'.extend I).symm ≫ f.extend I`. -/


theorem extend_coord_change_source :
    ((f.extend I).symm ≫ f'.extend I).source = I '' (f.symm ≫ₕ f').source :=
  by
  simp_rw [LocalEquiv.trans_source, I.image_eq, extend_source, LocalEquiv.symm_source,
    extend_target, inter_right_comm _ (range I)]
  rfl
#align local_homeomorph.extend_coord_change_source LocalHomeomorph.extend_coord_change_source

theorem extend_image_source_inter :
    f.extend I '' (f.source ∩ f'.source) = ((f.extend I).symm ≫ f'.extend I).source := by
  simp_rw [f.extend_coord_change_source, f.extend_coe, image_comp I f, trans_source'', symm_symm,
    symm_target]
#align local_homeomorph.extend_image_source_inter LocalHomeomorph.extend_image_source_inter

variable {f f'}

open SmoothManifoldWithCorners

theorem contDiffOnExtendCoordChange [ChartedSpace H M] (hf : f ∈ maximalAtlas I M)
    (hf' : f' ∈ maximalAtlas I M) :
    ContDiffOn 𝕜 ⊤ (f.extend I ∘ (f'.extend I).symm) ((f'.extend I).symm ≫ f.extend I).source :=
  by
  rw [extend_coord_change_source, I.image_eq]
  exact (StructureGroupoid.compatible_of_mem_maximal_atlas hf' hf).1
#align local_homeomorph.cont_diff_on_extend_coord_change LocalHomeomorph.contDiffOnExtendCoordChange

theorem contDiffWithinAtExtendCoordChange [ChartedSpace H M] (hf : f ∈ maximalAtlas I M)
    (hf' : f' ∈ maximalAtlas I M) {x : E} (hx : x ∈ ((f'.extend I).symm ≫ f.extend I).source) :
    ContDiffWithinAt 𝕜 ⊤ (f.extend I ∘ (f'.extend I).symm) (range I) x :=
  by
  apply (cont_diff_on_extend_coord_change I hf hf' x hx).mono_of_mem
  rw [extend_coord_change_source] at hx⊢
  obtain ⟨z, hz, rfl⟩ := hx
  exact I.image_mem_nhds_within ((LocalHomeomorph.open_source _).mem_nhds hz)
#align
  local_homeomorph.cont_diff_within_at_extend_coord_change LocalHomeomorph.contDiffWithinAtExtendCoordChange

end LocalHomeomorph

open LocalHomeomorph

variable [ChartedSpace H M] [ChartedSpace H' M']

/-- The preferred extended chart on a manifold with corners around a point `x`, from a neighborhood
of `x` to the model vector space. -/
@[simp, mfld_simps]
def extChartAt (x : M) : LocalEquiv M E :=
  (chartAt H x).extend I
#align ext_chart_at extChartAt

theorem ext_chart_at_coe : ⇑(extChartAt I x) = I ∘ chartAt H x :=
  rfl
#align ext_chart_at_coe ext_chart_at_coe

theorem ext_chart_at_coe_symm : ⇑(extChartAt I x).symm = (chartAt H x).symm ∘ I.symm :=
  rfl
#align ext_chart_at_coe_symm ext_chart_at_coe_symm

theorem ext_chart_at_source : (extChartAt I x).source = (chartAt H x).source :=
  extend_source _ _
#align ext_chart_at_source ext_chart_at_source

theorem is_open_ext_chart_at_source : IsOpen (extChartAt I x).source :=
  is_open_extend_source _ _
#align is_open_ext_chart_at_source is_open_ext_chart_at_source

theorem mem_ext_chart_source : x ∈ (extChartAt I x).source := by
  simp only [ext_chart_at_source, mem_chart_source]
#align mem_ext_chart_source mem_ext_chart_source

theorem ext_chart_at_target (x : M) :
    (extChartAt I x).target = I.symm ⁻¹' (chartAt H x).target ∩ range I :=
  extend_target _ _
#align ext_chart_at_target ext_chart_at_target

theorem ext_chart_at_to_inv : (extChartAt I x).symm ((extChartAt I x) x) = x :=
  (extChartAt I x).left_inv (mem_ext_chart_source I x)
#align ext_chart_at_to_inv ext_chart_at_to_inv

theorem maps_to_ext_chart_at (hs : s ⊆ (chartAt H x).source) :
    MapsTo (extChartAt I x) s ((extChartAt I x).symm ⁻¹' s ∩ range I) :=
  maps_to_extend _ _ hs
#align maps_to_ext_chart_at maps_to_ext_chart_at

theorem ext_chart_at_source_mem_nhds' {x' : M} (h : x' ∈ (extChartAt I x).source) :
    (extChartAt I x).source ∈ 𝓝 x' :=
  extend_source_mem_nhds _ _ <| by rwa [← ext_chart_at_source I]
#align ext_chart_at_source_mem_nhds' ext_chart_at_source_mem_nhds'

theorem ext_chart_at_source_mem_nhds : (extChartAt I x).source ∈ 𝓝 x :=
  ext_chart_at_source_mem_nhds' I x (mem_ext_chart_source I x)
#align ext_chart_at_source_mem_nhds ext_chart_at_source_mem_nhds

theorem ext_chart_at_source_mem_nhds_within' {x' : M} (h : x' ∈ (extChartAt I x).source) :
    (extChartAt I x).source ∈ 𝓝[s] x' :=
  mem_nhds_within_of_mem_nhds (ext_chart_at_source_mem_nhds' I x h)
#align ext_chart_at_source_mem_nhds_within' ext_chart_at_source_mem_nhds_within'

theorem ext_chart_at_source_mem_nhds_within : (extChartAt I x).source ∈ 𝓝[s] x :=
  mem_nhds_within_of_mem_nhds (ext_chart_at_source_mem_nhds I x)
#align ext_chart_at_source_mem_nhds_within ext_chart_at_source_mem_nhds_within

theorem continuous_on_ext_chart_at : ContinuousOn (extChartAt I x) (extChartAt I x).source :=
  continuous_on_extend _ _
#align continuous_on_ext_chart_at continuous_on_ext_chart_at

theorem continuous_at_ext_chart_at' {x' : M} (h : x' ∈ (extChartAt I x).source) :
    ContinuousAt (extChartAt I x) x' :=
  continuous_at_extend _ _ <| by rwa [← ext_chart_at_source I]
#align continuous_at_ext_chart_at' continuous_at_ext_chart_at'

theorem continuous_at_ext_chart_at : ContinuousAt (extChartAt I x) x :=
  continuous_at_ext_chart_at' _ _ (mem_ext_chart_source I x)
#align continuous_at_ext_chart_at continuous_at_ext_chart_at

theorem map_ext_chart_at_nhds' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝 y) = 𝓝[range I] extChartAt I x y :=
  map_extend_nhds _ _ <| by rwa [← ext_chart_at_source I]
#align map_ext_chart_at_nhds' map_ext_chart_at_nhds'

theorem map_ext_chart_at_nhds : map (extChartAt I x) (𝓝 x) = 𝓝[range I] extChartAt I x x :=
  map_ext_chart_at_nhds' I <| mem_ext_chart_source I x
#align map_ext_chart_at_nhds map_ext_chart_at_nhds

theorem ext_chart_at_target_mem_nhds_within' {y : M} (hy : y ∈ (extChartAt I x).source) :
    (extChartAt I x).target ∈ 𝓝[range I] extChartAt I x y :=
  extend_target_mem_nhds_within _ _ <| by rwa [← ext_chart_at_source I]
#align ext_chart_at_target_mem_nhds_within' ext_chart_at_target_mem_nhds_within'

theorem ext_chart_at_target_mem_nhds_within :
    (extChartAt I x).target ∈ 𝓝[range I] extChartAt I x x :=
  ext_chart_at_target_mem_nhds_within' I x (mem_ext_chart_source I x)
#align ext_chart_at_target_mem_nhds_within ext_chart_at_target_mem_nhds_within

theorem ext_chart_at_target_subset_range : (extChartAt I x).target ⊆ range I := by
  simp only [mfld_simps]
#align ext_chart_at_target_subset_range ext_chart_at_target_subset_range

theorem nhds_within_ext_chart_at_target_eq' {y : M} (hy : y ∈ (extChartAt I x).source) :
    𝓝[(extChartAt I x).target] extChartAt I x y = 𝓝[range I] extChartAt I x y :=
  nhds_within_extend_target_eq _ _ <| by rwa [← ext_chart_at_source I]
#align nhds_within_ext_chart_at_target_eq' nhds_within_ext_chart_at_target_eq'

theorem nhds_within_ext_chart_at_target_eq :
    𝓝[(extChartAt I x).target] (extChartAt I x) x = 𝓝[range I] (extChartAt I x) x :=
  nhds_within_ext_chart_at_target_eq' I x (mem_ext_chart_source I x)
#align nhds_within_ext_chart_at_target_eq nhds_within_ext_chart_at_target_eq

theorem continuous_at_ext_chart_at_symm'' {y : E} (h : y ∈ (extChartAt I x).target) :
    ContinuousAt (extChartAt I x).symm y :=
  continuous_at_extend_symm' _ _ h
#align continuous_at_ext_chart_at_symm'' continuous_at_ext_chart_at_symm''

theorem continuous_at_ext_chart_at_symm' {x' : M} (h : x' ∈ (extChartAt I x).source) :
    ContinuousAt (extChartAt I x).symm (extChartAt I x x') :=
  continuous_at_ext_chart_at_symm'' I _ <| (extChartAt I x).map_source h
#align continuous_at_ext_chart_at_symm' continuous_at_ext_chart_at_symm'

theorem continuous_at_ext_chart_at_symm : ContinuousAt (extChartAt I x).symm ((extChartAt I x) x) :=
  continuous_at_ext_chart_at_symm' I x (mem_ext_chart_source I x)
#align continuous_at_ext_chart_at_symm continuous_at_ext_chart_at_symm

theorem continuous_on_ext_chart_at_symm :
    ContinuousOn (extChartAt I x).symm (extChartAt I x).target := fun y hy =>
  (continuous_at_ext_chart_at_symm'' _ _ hy).ContinuousWithinAt
#align continuous_on_ext_chart_at_symm continuous_on_ext_chart_at_symm

theorem is_open_ext_chart_at_preimage' {s : Set E} (hs : IsOpen s) :
    IsOpen ((extChartAt I x).source ∩ extChartAt I x ⁻¹' s) :=
  is_open_extend_preimage' _ _ hs
#align is_open_ext_chart_at_preimage' is_open_ext_chart_at_preimage'

theorem is_open_ext_chart_at_preimage {s : Set E} (hs : IsOpen s) :
    IsOpen ((chartAt H x).source ∩ extChartAt I x ⁻¹' s) :=
  by
  rw [← ext_chart_at_source I]
  exact is_open_ext_chart_at_preimage' I x hs
#align is_open_ext_chart_at_preimage is_open_ext_chart_at_preimage

theorem map_ext_chart_at_nhds_within_eq_image' {y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝[s] y) =
      𝓝[extChartAt I x '' ((extChartAt I x).source ∩ s)] extChartAt I x y :=
  map_extend_nhds_within_eq_image _ _ <| by rwa [← ext_chart_at_source I]
#align map_ext_chart_at_nhds_within_eq_image' map_ext_chart_at_nhds_within_eq_image'

theorem map_ext_chart_at_nhds_within_eq_image :
    map (extChartAt I x) (𝓝[s] x) =
      𝓝[extChartAt I x '' ((extChartAt I x).source ∩ s)] extChartAt I x x :=
  map_ext_chart_at_nhds_within_eq_image' I x (mem_ext_chart_source I x)
#align map_ext_chart_at_nhds_within_eq_image map_ext_chart_at_nhds_within_eq_image

theorem map_ext_chart_at_nhds_within' {y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝[s] y) = 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x y :=
  map_extend_nhds_within _ _ <| by rwa [← ext_chart_at_source I]
#align map_ext_chart_at_nhds_within' map_ext_chart_at_nhds_within'

theorem map_ext_chart_at_nhds_within :
    map (extChartAt I x) (𝓝[s] x) = 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x x :=
  map_ext_chart_at_nhds_within' I x (mem_ext_chart_source I x)
#align map_ext_chart_at_nhds_within map_ext_chart_at_nhds_within

theorem map_ext_chart_at_symm_nhds_within' {y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x y) =
      𝓝[s] y :=
  map_extend_symm_nhds_within _ _ <| by rwa [← ext_chart_at_source I]
#align map_ext_chart_at_symm_nhds_within' map_ext_chart_at_symm_nhds_within'

theorem map_ext_chart_at_symm_nhds_within_range' {y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x).symm (𝓝[range I] extChartAt I x y) = 𝓝 y :=
  map_extend_symm_nhds_within_range _ _ <| by rwa [← ext_chart_at_source I]
#align map_ext_chart_at_symm_nhds_within_range' map_ext_chart_at_symm_nhds_within_range'

theorem map_ext_chart_at_symm_nhds_within :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x x) =
      𝓝[s] x :=
  map_ext_chart_at_symm_nhds_within' I x (mem_ext_chart_source I x)
#align map_ext_chart_at_symm_nhds_within map_ext_chart_at_symm_nhds_within

theorem map_ext_chart_at_symm_nhds_within_range :
    map (extChartAt I x).symm (𝓝[range I] extChartAt I x x) = 𝓝 x :=
  map_ext_chart_at_symm_nhds_within_range' I x (mem_ext_chart_source I x)
#align map_ext_chart_at_symm_nhds_within_range map_ext_chart_at_symm_nhds_within_range

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
theorem ext_chart_at_preimage_mem_nhds_within' {x' : M} (h : x' ∈ (extChartAt I x).source)
    (ht : t ∈ 𝓝[s] x') :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x' := by
  rwa [← map_ext_chart_at_symm_nhds_within' I x h, mem_map] at ht
#align ext_chart_at_preimage_mem_nhds_within' ext_chart_at_preimage_mem_nhds_within'

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of the
base point is a neighborhood of the preimage, within a set. -/
theorem ext_chart_at_preimage_mem_nhds_within (ht : t ∈ 𝓝[s] x) :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
  ext_chart_at_preimage_mem_nhds_within' I x (mem_ext_chart_source I x) ht
#align ext_chart_at_preimage_mem_nhds_within ext_chart_at_preimage_mem_nhds_within

theorem ext_chart_at_preimage_mem_nhds' {x' : M} (h : x' ∈ (extChartAt I x).source)
    (ht : t ∈ 𝓝 x') : (extChartAt I x).symm ⁻¹' t ∈ 𝓝 (extChartAt I x x') :=
  extend_preimage_mem_nhds _ _ (by rwa [← ext_chart_at_source I]) ht
#align ext_chart_at_preimage_mem_nhds' ext_chart_at_preimage_mem_nhds'

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
is a neighborhood of the preimage. -/
theorem ext_chart_at_preimage_mem_nhds (ht : t ∈ 𝓝 x) :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝 ((extChartAt I x) x) :=
  by
  apply (continuous_at_ext_chart_at_symm I x).preimage_mem_nhds
  rwa [(extChartAt I x).left_inv (mem_ext_chart_source _ _)]
#align ext_chart_at_preimage_mem_nhds ext_chart_at_preimage_mem_nhds

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
theorem ext_chart_at_preimage_inter_eq :
    (extChartAt I x).symm ⁻¹' (s ∩ t) ∩ range I =
      (extChartAt I x).symm ⁻¹' s ∩ range I ∩ (extChartAt I x).symm ⁻¹' t :=
  by mfld_set_tac
#align ext_chart_at_preimage_inter_eq ext_chart_at_preimage_inter_eq

/-! We use the name `ext_coord_change` for `(ext_chart_at I x').symm ≫ ext_chart_at I x`. -/


theorem ext_coord_change_source (x x' : M) :
    ((extChartAt I x').symm ≫ extChartAt I x).source =
      I '' ((chartAt H x').symm ≫ₕ chartAt H x).source :=
  extend_coord_change_source _ _ _
#align ext_coord_change_source ext_coord_change_source

open SmoothManifoldWithCorners

theorem contDiffOnExtCoordChange [SmoothManifoldWithCorners I M] (x x' : M) :
    ContDiffOn 𝕜 ⊤ (extChartAt I x ∘ (extChartAt I x').symm)
      ((extChartAt I x').symm ≫ extChartAt I x).source :=
  contDiffOnExtendCoordChange I (chart_mem_maximal_atlas I x) (chart_mem_maximal_atlas I x')
#align cont_diff_on_ext_coord_change contDiffOnExtCoordChange

theorem contDiffWithinAtExtCoordChange [SmoothManifoldWithCorners I M] (x x' : M) {y : E}
    (hy : y ∈ ((extChartAt I x').symm ≫ extChartAt I x).source) :
    ContDiffWithinAt 𝕜 ⊤ (extChartAt I x ∘ (extChartAt I x').symm) (range I) y :=
  contDiffWithinAtExtendCoordChange I (chart_mem_maximal_atlas I x) (chart_mem_maximal_atlas I x')
    hy
#align cont_diff_within_at_ext_coord_change contDiffWithinAtExtCoordChange

/-- Conjugating a function to write it in the preferred charts around `x`.
The manifold derivative of `f` will just be the derivative of this conjugated function. -/
@[simp, mfld_simps]
def writtenInExtChartAt (x : M) (f : M → M') : E → E' :=
  extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm
#align written_in_ext_chart_at writtenInExtChartAt

variable (𝕜)

theorem ext_chart_at_self_eq {x : H} : ⇑(extChartAt I x) = I :=
  rfl
#align ext_chart_at_self_eq ext_chart_at_self_eq

theorem ext_chart_at_self_apply {x y : H} : extChartAt I x y = I y :=
  rfl
#align ext_chart_at_self_apply ext_chart_at_self_apply

/-- In the case of the manifold structure on a vector space, the extended charts are just the
identity.-/
theorem ext_chart_at_model_space_eq_id (x : E) : extChartAt 𝓘(𝕜, E) x = LocalEquiv.refl E := by
  simp only [mfld_simps]
#align ext_chart_at_model_space_eq_id ext_chart_at_model_space_eq_id

theorem ext_chart_model_space_apply {x y : E} : extChartAt 𝓘(𝕜, E) x y = y :=
  rfl
#align ext_chart_model_space_apply ext_chart_model_space_apply

variable {𝕜}

theorem ext_chart_at_prod (x : M × M') :
    extChartAt (I.Prod I') x = (extChartAt I x.1).Prod (extChartAt I' x.2) := by
  simp only [mfld_simps]
#align ext_chart_at_prod ext_chart_at_prod

end ExtendedCharts

