/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Data.Bundle
import Mathbin.Topology.Algebra.Order.Basic
import Mathbin.Topology.LocalHomeomorph

/-!
# Fiber bundles

A topological fiber bundle with fiber `F` over a base `B` is a space projecting on `B` for which the
fibers are all homeomorphic to `F`, such that the local situation around each point is a direct
product. We define a predicate `is_topological_fiber_bundle F p` saying that `p : Z → B` is a
topological fiber bundle with fiber `F`.

It is in general nontrivial to construct a fiber bundle. A way is to start from the knowledge of
how changes of local trivializations act on the fiber. From this, one can construct the total space
of the bundle and its topology by a suitable gluing construction. The main content of this file is
an implementation of this construction: starting from an object of type
`topological_fiber_bundle_core` registering the trivialization changes, one gets the corresponding
fiber bundle and projection.

Similarly we implement the object `topological_fiber_prebundle` which allows to define a topological
fiber bundle from trivializations given as local equivalences with minimum additional properties.

## Main definitions

### Basic definitions

* `trivialization F p` : structure extending local homeomorphisms, defining a local
                  trivialization of a topological space `Z` with projection `p` and fiber `F`.

* `is_topological_fiber_bundle F p` : Prop saying that the map `p` between topological spaces is a
                  fiber bundle with fiber `F`.

* `is_trivial_topological_fiber_bundle F p` : Prop saying that the map `p : Z → B` between
  topological spaces is a trivial topological fiber bundle, i.e., there exists a homeomorphism
  `h : Z ≃ₜ B × F` such that `proj x = (h x).1`.

### Operations on bundles

We provide the following operations on `trivialization`s.

* `trivialization.comap`: given a local trivialization `e` of a fiber bundle `p : Z → B`, a
  continuous map `f : B' → B` and a point `b' : B'` such that `f b' ∈ e.base_set`,
  `e.comap f hf b' hb'` is a trivialization of the pullback bundle. The pullback bundle
  (a.k.a., the induced bundle) has total space `{(x, y) : B' × Z | f x = p y}`, and is given by
  `λ ⟨(x, y), h⟩, x`.

* `is_topological_fiber_bundle.comap`: if `p : Z → B` is a topological fiber bundle, then its
  pullback along a continuous map `f : B' → B` is a topological fiber bundle as well.

* `trivialization.comp_homeomorph`: given a local trivialization `e` of a fiber bundle
  `p : Z → B` and a homeomorphism `h : Z' ≃ₜ Z`, returns a local trivialization of the fiber bundle
  `p ∘ h`.

* `is_topological_fiber_bundle.comp_homeomorph`: if `p : Z → B` is a topological fiber bundle
  and `h : Z' ≃ₜ Z` is a homeomorphism, then `p ∘ h : Z' → B` is a topological fiber bundle with
  the same fiber.

### Construction of a bundle from trivializations

* `bundle.total_space E` is a type synonym for `Σ (x : B), E x`, that we can endow with a suitable
  topology.
* `topological_fiber_bundle_core ι B F` : structure registering how changes of coordinates act
  on the fiber `F` above open subsets of `B`, where local trivializations are indexed by `ι`.

Let `Z : topological_fiber_bundle_core ι B F`. Then we define

* `Z.fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.total_space` : the total space of `Z`, defined as a `Type` as `Σ (b : B), F`, but with a
  twisted topology coming from the fiber bundle structure. It is (reducibly) the same as
  `bundle.total_space Z.fiber`.
* `Z.proj`        : projection from `Z.total_space` to `B`. It is continuous.
* `Z.local_triv i`: for `i : ι`, bundle trivialization above the set `Z.base_set i`, which is an
                    open set in `B`.

* `pretrivialization F proj` : trivialization as a local equivalence, mainly used when the
                                      topology on the total space has not yet been defined.
* `topological_fiber_prebundle F proj` : structure registering a cover of prebundle trivializations
  and requiring that the relative transition maps are local homeomorphisms.
* `topological_fiber_prebundle.total_space_topology a` : natural topology of the total space, making
  the prebundle into a bundle.

## Implementation notes

A topological fiber bundle with fiber `F` over a base `B` is a family of spaces isomorphic to `F`,
indexed by `B`, which is locally trivial in the following sense: there is a covering of `B` by open
sets such that, on each such open set `s`, the bundle is isomorphic to `s × F`.

To construct a fiber bundle formally, the main data is what happens when one changes trivializations
from `s × F` to `s' × F` on `s ∩ s'`: one should get a family of homeomorphisms of `F`, depending
continuously on the base point, satisfying basic compatibility conditions (cocycle property).
Useful classes of bundles can then be specified by requiring that these homeomorphisms of `F`
belong to some subgroup, preserving some structure (the "structure group of the bundle"): then
these structures are inherited by the fibers of the bundle.

Given such trivialization change data (encoded below in a structure called
`topological_fiber_bundle_core`), one can construct the fiber bundle. The intrinsic canonical
mathematical construction is the following.
The fiber above `x` is the disjoint union of `F` over all trivializations, modulo the gluing
identifications: one gets a fiber which is isomorphic to `F`, but non-canonically
(each choice of one of the trivializations around `x` gives such an isomorphism). Given a
trivialization over a set `s`, one gets an isomorphism between `s × F` and `proj^{-1} s`, by using
the identification corresponding to this trivialization. One chooses the topology on the bundle that
makes all of these into homeomorphisms.

For the practical implementation, it turns out to be more convenient to avoid completely the
gluing and quotienting construction above, and to declare above each `x` that the fiber is `F`,
but thinking that it corresponds to the `F` coming from the choice of one trivialization around `x`.
This has several practical advantages:
* without any work, one gets a topological space structure on the fiber. And if `F` has more
structure it is inherited for free by the fiber.
* In the case of the tangent bundle of manifolds, this implies that on vector spaces the derivative
(from `F` to `F`) and the manifold derivative (from `tangent_space I x` to `tangent_space I' (f x)`)
are equal.

A drawback is that some silly constructions will typecheck: in the case of the tangent bundle, one
can add two vectors in different tangent spaces (as they both are elements of `F` from the point of
view of Lean). To solve this, one could mark the tangent space as irreducible, but then one would
lose the identification of the tangent space to `F` with `F`. There is however a big advantage of
this situation: even if Lean can not check that two basepoints are defeq, it will accept the fact
that the tangent spaces are the same. For instance, if two maps `f` and `g` are locally inverse to
each other, one can express that the composition of their derivatives is the identity of
`tangent_space I x`. One could fear issues as this composition goes from `tangent_space I x` to
`tangent_space I (g (f x))` (which should be the same, but should not be obvious to Lean
as it does not know that `g (f x) = x`). As these types are the same to Lean (equal to `F`), there
are in fact no dependent type difficulties here!

For this construction of a fiber bundle from a `topological_fiber_bundle_core`, we should thus
choose for each `x` one specific trivialization around it. We include this choice in the definition
of the `topological_fiber_bundle_core`, as it makes some constructions more
functorial and it is a nice way to say that the trivializations cover the whole space `B`.

With this definition, the type of the fiber bundle space constructed from the core data is just
`Σ (b : B), F `, but the topology is not the product one, in general.

We also take the indexing type (indexing all the trivializations) as a parameter to the fiber bundle
core: it could always be taken as a subtype of all the maps from open subsets of `B` to continuous
maps of `F`, but in practice it will sometimes be something else. For instance, on a manifold, one
will use the set of charts as a good parameterization for the trivializations of the tangent bundle.
Or for the pullback of a `topological_fiber_bundle_core`, the indexing type will be the same as
for the initial bundle.

## Tags
Fiber bundle, topological bundle, local trivialization, structure group
-/


variable {ι : Type _} {B : Type _} {F : Type _}

open TopologicalSpace Filter Set Bundle

open TopologicalSpace Classical

/-! ### General definition of topological fiber bundles -/


section TopologicalFiberBundle

variable (F) {Z : Type _} [TopologicalSpace B] [TopologicalSpace F] {proj : Z → B}

/-- This structure contains the information left for a local trivialization (which is implemented
below as `trivialization F proj`) if the total space has not been given a topology, but we
have a topology on both the fiber and the base space. Through the construction
`topological_fiber_prebundle F proj` it will be possible to promote a
`pretrivialization F proj` to a `trivialization F proj`. -/
@[nolint has_inhabited_instance]
structure TopologicalFiberBundle.Pretrivialization (proj : Z → B) extends LocalEquiv Z (B × F) where
  open_target : IsOpen target
  BaseSet : Set B
  open_base_set : IsOpen base_set
  source_eq : source = proj ⁻¹' base_set
  target_eq : target = base_set ×ˢ (Univ : Set F)
  proj_to_fun : ∀, ∀ p ∈ source, ∀, (to_fun p).1 = proj p

open TopologicalFiberBundle

namespace TopologicalFiberBundle.Pretrivialization

instance : CoeFun (Pretrivialization F proj) fun _ => Z → B × F :=
  ⟨fun e => e.toFun⟩

variable {F} (e : Pretrivialization F proj) {x : Z}

@[simp, mfld_simps]
theorem coe_coe : ⇑e.toLocalEquiv = e :=
  rfl

@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.Source) : (e x).1 = proj x :=
  e.proj_to_fun x ex

theorem mem_source : x ∈ e.Source ↔ proj x ∈ e.BaseSet := by
  rw [e.source_eq, mem_preimage]

theorem coe_fst' (ex : proj x ∈ e.BaseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)

protected theorem eq_on : EqOn (Prod.fst ∘ e) proj e.Source := fun x hx => e.coe_fst hx

theorem mk_proj_snd (ex : x ∈ e.Source) : (proj x, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst ex).symm rfl

theorem mk_proj_snd' (ex : proj x ∈ e.BaseSet) : (proj x, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst' ex).symm rfl

/-- Composition of inverse and coercion from the subtype of the target. -/
def setSymm : e.Target → Z :=
  e.Target.restrict e.toLocalEquiv.symm

theorem mem_target {x : B × F} : x ∈ e.Target ↔ x.1 ∈ e.BaseSet := by
  rw [e.target_eq, prod_univ, mem_preimage]

theorem proj_symm_apply {x : B × F} (hx : x ∈ e.Target) : proj (e.toLocalEquiv.symm x) = x.1 := by
  have := (e.coe_fst (e.to_local_equiv.map_target hx)).symm
  rwa [← e.coe_coe, e.to_local_equiv.right_inv hx] at this

theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.BaseSet) : proj (e.toLocalEquiv.symm (b, x)) = b :=
  e.proj_symm_apply (e.mem_target.2 hx)

theorem proj_surj_on_base_set [Nonempty F] : Set.SurjOn proj e.Source e.BaseSet := fun b hb =>
  let ⟨y⟩ := ‹Nonempty F›
  ⟨e.toLocalEquiv.symm (b, y), e.toLocalEquiv.map_target <| e.mem_target.2 hb, e.proj_symm_apply' hb⟩

theorem apply_symm_apply {x : B × F} (hx : x ∈ e.Target) : e (e.toLocalEquiv.symm x) = x :=
  e.toLocalEquiv.right_inv hx

theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.BaseSet) : e (e.toLocalEquiv.symm (b, x)) = (b, x) :=
  e.apply_symm_apply (e.mem_target.2 hx)

theorem symm_apply_apply {x : Z} (hx : x ∈ e.Source) : e.toLocalEquiv.symm (e x) = x :=
  e.toLocalEquiv.left_inv hx

@[simp, mfld_simps]
theorem symm_apply_mk_proj {x : Z} (ex : x ∈ e.Source) : e.toLocalEquiv.symm (proj x, (e x).2) = x := by
  rw [← e.coe_fst ex, Prod.mk.eta, ← e.coe_coe, e.to_local_equiv.left_inv ex]

@[simp, mfld_simps]
theorem preimage_symm_proj_base_set : e.toLocalEquiv.symm ⁻¹' (proj ⁻¹' e.BaseSet) ∩ e.Target = e.Target := by
  refine' inter_eq_right_iff_subset.mpr fun x hx => _
  simp only [← mem_preimage, ← LocalEquiv.inv_fun_as_coe, ← e.proj_symm_apply hx]
  exact e.mem_target.mp hx

@[simp, mfld_simps]
theorem preimage_symm_proj_inter (s : Set B) :
    e.toLocalEquiv.symm ⁻¹' (proj ⁻¹' s) ∩ e.BaseSet ×ˢ (Univ : Set F) = (s ∩ e.BaseSet) ×ˢ (Univ : Set F) := by
  ext ⟨x, y⟩
  suffices x ∈ e.base_set → (proj (e.to_local_equiv.symm (x, y)) ∈ s ↔ x ∈ s) by
    simpa only [← prod_mk_mem_set_prod_eq, ← mem_inter_eq, ← and_trueₓ, ← mem_univ, ← And.congr_left_iff]
  intro h
  rw [e.proj_symm_apply' h]

theorem target_inter_preimage_symm_source_eq (e f : Pretrivialization F proj) :
    f.Target ∩ f.toLocalEquiv.symm ⁻¹' e.Source = (e.BaseSet ∩ f.BaseSet) ×ˢ (Univ : Set F) := by
  rw [inter_comm, f.target_eq, e.source_eq, f.preimage_symm_proj_inter]

theorem trans_source (e f : Pretrivialization F proj) :
    (f.toLocalEquiv.symm.trans e.toLocalEquiv).Source = (e.BaseSet ∩ f.BaseSet) ×ˢ (Univ : Set F) := by
  rw [LocalEquiv.trans_source, LocalEquiv.symm_source, e.target_inter_preimage_symm_source_eq]

theorem symm_trans_symm (e e' : Pretrivialization F proj) :
    (e.toLocalEquiv.symm.trans e'.toLocalEquiv).symm = e'.toLocalEquiv.symm.trans e.toLocalEquiv := by
  rw [LocalEquiv.trans_symm_eq_symm_trans_symm, LocalEquiv.symm_symm]

theorem symm_trans_source_eq (e e' : Pretrivialization F proj) :
    (e.toLocalEquiv.symm.trans e'.toLocalEquiv).Source = (e.BaseSet ∩ e'.BaseSet) ×ˢ (Univ : Set F) := by
  rw [LocalEquiv.trans_source, e'.source_eq, LocalEquiv.symm_source, e.target_eq, inter_comm,
    e.preimage_symm_proj_inter, inter_comm]

theorem symm_trans_target_eq (e e' : Pretrivialization F proj) :
    (e.toLocalEquiv.symm.trans e'.toLocalEquiv).Target = (e.BaseSet ∩ e'.BaseSet) ×ˢ (Univ : Set F) := by
  rw [← LocalEquiv.symm_source, symm_trans_symm, symm_trans_source_eq, inter_comm]

end TopologicalFiberBundle.Pretrivialization

variable [TopologicalSpace Z]

/-- A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
@[nolint has_inhabited_instance]
structure TopologicalFiberBundle.Trivialization (proj : Z → B) extends LocalHomeomorph Z (B × F) where
  BaseSet : Set B
  open_base_set : IsOpen base_set
  source_eq : source = proj ⁻¹' base_set
  target_eq : target = base_set ×ˢ (Univ : Set F)
  proj_to_fun : ∀, ∀ p ∈ source, ∀, (to_local_homeomorph p).1 = proj p

open TopologicalFiberBundle

namespace TopologicalFiberBundle.Trivialization

variable {F} (e : Trivialization F proj) {x : Z}

/-- Natural identification as a `pretrivialization`. -/
def toPretrivialization : TopologicalFiberBundle.Pretrivialization F proj :=
  { e with }

instance : CoeFun (Trivialization F proj) fun _ => Z → B × F :=
  ⟨fun e => e.toFun⟩

instance : Coe (Trivialization F proj) (Pretrivialization F proj) :=
  ⟨toPretrivialization⟩

@[simp, mfld_simps]
theorem coe_coe : ⇑e.toLocalHomeomorph = e :=
  rfl

@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.Source) : (e x).1 = proj x :=
  e.proj_to_fun x ex

protected theorem eq_on : EqOn (Prod.fst ∘ e) proj e.Source := fun x hx => e.coe_fst hx

theorem mem_source : x ∈ e.Source ↔ proj x ∈ e.BaseSet := by
  rw [e.source_eq, mem_preimage]

theorem coe_fst' (ex : proj x ∈ e.BaseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)

theorem mk_proj_snd (ex : x ∈ e.Source) : (proj x, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst ex).symm rfl

theorem mk_proj_snd' (ex : proj x ∈ e.BaseSet) : (proj x, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst' ex).symm rfl

theorem source_inter_preimage_target_inter (s : Set (B × F)) : e.Source ∩ e ⁻¹' (e.Target ∩ s) = e.Source ∩ e ⁻¹' s :=
  e.toLocalHomeomorph.source_inter_preimage_target_inter s

@[simp, mfld_simps]
theorem coe_mk (e : LocalHomeomorph Z (B × F)) i j k l m (x : Z) :
    (Trivialization.mk e i j k l m : Trivialization F proj) x = e x :=
  rfl

theorem mem_target {x : B × F} : x ∈ e.Target ↔ x.1 ∈ e.BaseSet :=
  e.toPretrivialization.mem_target

theorem map_target {x : B × F} (hx : x ∈ e.Target) : e.toLocalHomeomorph.symm x ∈ e.Source :=
  e.toLocalHomeomorph.map_target hx

theorem proj_symm_apply {x : B × F} (hx : x ∈ e.Target) : proj (e.toLocalHomeomorph.symm x) = x.1 :=
  e.toPretrivialization.proj_symm_apply hx

theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.BaseSet) : proj (e.toLocalHomeomorph.symm (b, x)) = b :=
  e.toPretrivialization.proj_symm_apply' hx

theorem proj_surj_on_base_set [Nonempty F] : Set.SurjOn proj e.Source e.BaseSet :=
  e.toPretrivialization.proj_surj_on_base_set

theorem apply_symm_apply {x : B × F} (hx : x ∈ e.Target) : e (e.toLocalHomeomorph.symm x) = x :=
  e.toLocalHomeomorph.right_inv hx

theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.BaseSet) : e (e.toLocalHomeomorph.symm (b, x)) = (b, x) :=
  e.toPretrivialization.apply_symm_apply' hx

@[simp, mfld_simps]
theorem symm_apply_mk_proj (ex : x ∈ e.Source) : e.toLocalHomeomorph.symm (proj x, (e x).2) = x :=
  e.toPretrivialization.symm_apply_mk_proj ex

theorem symm_trans_source_eq (e e' : Trivialization F proj) :
    (e.toLocalEquiv.symm.trans e'.toLocalEquiv).Source = (e.BaseSet ∩ e'.BaseSet) ×ˢ (Univ : Set F) :=
  Pretrivialization.symm_trans_source_eq e.toPretrivialization e'

theorem symm_trans_target_eq (e e' : Trivialization F proj) :
    (e.toLocalEquiv.symm.trans e'.toLocalEquiv).Target = (e.BaseSet ∩ e'.BaseSet) ×ˢ (Univ : Set F) :=
  Pretrivialization.symm_trans_target_eq e.toPretrivialization e'

theorem coe_fst_eventually_eq_proj (ex : x ∈ e.Source) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  mem_nhds_iff.2 ⟨e.Source, fun y hy => e.coe_fst hy, e.open_source, ex⟩

theorem coe_fst_eventually_eq_proj' (ex : proj x ∈ e.BaseSet) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  e.coe_fst_eventually_eq_proj (e.mem_source.2 ex)

theorem map_proj_nhds (ex : x ∈ e.Source) : map proj (𝓝 x) = 𝓝 (proj x) := by
  rw [← e.coe_fst ex, ← map_congr (e.coe_fst_eventually_eq_proj ex), ← map_map, ← e.coe_coe,
    e.to_local_homeomorph.map_nhds_eq ex, map_fst_nhds]

/-- In the domain of a bundle trivialization, the projection is continuous-/
theorem continuous_at_proj (ex : x ∈ e.Source) : ContinuousAt proj x :=
  (e.map_proj_nhds ex).le

/-- Composition of a `trivialization` and a `homeomorph`. -/
def compHomeomorph {Z' : Type _} [TopologicalSpace Z'] (h : Z' ≃ₜ Z) : Trivialization F (proj ∘ h) where
  toLocalHomeomorph := h.toLocalHomeomorph.trans e.toLocalHomeomorph
  BaseSet := e.BaseSet
  open_base_set := e.open_base_set
  source_eq := by
    simp [← e.source_eq, ← preimage_preimage]
  target_eq := by
    simp [← e.target_eq]
  proj_to_fun := fun p hp => by
    have hp : h p ∈ e.Source := by
      simpa using hp
    simp [← hp]

/-- Read off the continuity of a function `f : Z → X` at `z : Z` by transferring via a
trivialization of `Z` containing `z`. -/
theorem continuous_at_of_comp_right {X : Type _} [TopologicalSpace X] {f : Z → X} {z : Z} (e : Trivialization F proj)
    (he : proj z ∈ e.BaseSet) (hf : ContinuousAt (f ∘ e.toLocalEquiv.symm) (e z)) : ContinuousAt f z := by
  have hez : z ∈ e.to_local_equiv.symm.target := by
    rw [LocalEquiv.symm_target, e.mem_source]
    exact he
  rwa [e.to_local_homeomorph.symm.continuous_at_iff_continuous_at_comp_right hez, LocalHomeomorph.symm_symm]

/-- Read off the continuity of a function `f : X → Z` at `x : X` by transferring via a
trivialization of `Z` containing `f x`. -/
theorem continuous_at_of_comp_left {X : Type _} [TopologicalSpace X] {f : X → Z} {x : X} (e : Trivialization F proj)
    (hf_proj : ContinuousAt (proj ∘ f) x) (he : proj (f x) ∈ e.BaseSet) (hf : ContinuousAt (e ∘ f) x) :
    ContinuousAt f x := by
  rw [e.to_local_homeomorph.continuous_at_iff_continuous_at_comp_left]
  · exact hf
    
  rw [e.source_eq, ← preimage_comp]
  exact hf_proj.preimage_mem_nhds (e.open_base_set.mem_nhds he)

end TopologicalFiberBundle.Trivialization

/-- A topological fiber bundle with fiber `F` over a base `B` is a space projecting on `B`
for which the fibers are all homeomorphic to `F`, such that the local situation around each point
is a direct product. -/
def IsTopologicalFiberBundle (proj : Z → B) : Prop :=
  ∀ x : B, ∃ e : Trivialization F proj, x ∈ e.BaseSet

/-- A trivial topological fiber bundle with fiber `F` over a base `B` is a space `Z`
projecting on `B` for which there exists a homeomorphism to `B × F` that sends `proj`
to `prod.fst`. -/
def IsTrivialTopologicalFiberBundle (proj : Z → B) : Prop :=
  ∃ e : Z ≃ₜ B × F, ∀ x, (e x).1 = proj x

variable {F}

theorem IsTrivialTopologicalFiberBundle.is_topological_fiber_bundle (h : IsTrivialTopologicalFiberBundle F proj) :
    IsTopologicalFiberBundle F proj :=
  let ⟨e, he⟩ := h
  fun x => ⟨⟨e.toLocalHomeomorph, Univ, is_open_univ, rfl, univ_prod_univ.symm, fun x _ => he x⟩, mem_univ x⟩

theorem IsTopologicalFiberBundle.map_proj_nhds (h : IsTopologicalFiberBundle F proj) (x : Z) :
    map proj (𝓝 x) = 𝓝 (proj x) :=
  let ⟨e, ex⟩ := h (proj x)
  e.map_proj_nhds <| e.mem_source.2 ex

/-- The projection from a topological fiber bundle to its base is continuous. -/
theorem IsTopologicalFiberBundle.continuous_proj (h : IsTopologicalFiberBundle F proj) : Continuous proj :=
  continuous_iff_continuous_at.2 fun x => (h.map_proj_nhds _).le

/-- The projection from a topological fiber bundle to its base is an open map. -/
theorem IsTopologicalFiberBundle.is_open_map_proj (h : IsTopologicalFiberBundle F proj) : IsOpenMap proj :=
  IsOpenMap.of_nhds_le fun x => (h.map_proj_nhds x).Ge

/-- The projection from a topological fiber bundle with a nonempty fiber to its base is a surjective
map. -/
theorem IsTopologicalFiberBundle.surjective_proj [Nonempty F] (h : IsTopologicalFiberBundle F proj) :
    Function.Surjective proj := fun b =>
  let ⟨e, eb⟩ := h b
  let ⟨x, _, hx⟩ := e.proj_surj_on_base_set eb
  ⟨x, hx⟩

/-- The projection from a topological fiber bundle with a nonempty fiber to its base is a quotient
map. -/
theorem IsTopologicalFiberBundle.quotient_map_proj [Nonempty F] (h : IsTopologicalFiberBundle F proj) :
    QuotientMap proj :=
  h.is_open_map_proj.to_quotient_map h.continuous_proj h.surjective_proj

/-- The first projection in a product is a trivial topological fiber bundle. -/
theorem is_trivial_topological_fiber_bundle_fst : IsTrivialTopologicalFiberBundle F (Prod.fst : B × F → B) :=
  ⟨Homeomorph.refl _, fun x => rfl⟩

/-- The first projection in a product is a topological fiber bundle. -/
theorem is_topological_fiber_bundle_fst : IsTopologicalFiberBundle F (Prod.fst : B × F → B) :=
  is_trivial_topological_fiber_bundle_fst.IsTopologicalFiberBundle

/-- The second projection in a product is a trivial topological fiber bundle. -/
theorem is_trivial_topological_fiber_bundle_snd : IsTrivialTopologicalFiberBundle F (Prod.snd : F × B → B) :=
  ⟨Homeomorph.prodComm _ _, fun x => rfl⟩

/-- The second projection in a product is a topological fiber bundle. -/
theorem is_topological_fiber_bundle_snd : IsTopologicalFiberBundle F (Prod.snd : F × B → B) :=
  is_trivial_topological_fiber_bundle_snd.IsTopologicalFiberBundle

theorem IsTopologicalFiberBundle.comp_homeomorph {Z' : Type _} [TopologicalSpace Z']
    (e : IsTopologicalFiberBundle F proj) (h : Z' ≃ₜ Z) : IsTopologicalFiberBundle F (proj ∘ h) := fun x =>
  let ⟨e, he⟩ := e x
  ⟨e.comp_homeomorph h, by
    simpa [← TopologicalFiberBundle.Trivialization.compHomeomorph] using he⟩

namespace TopologicalFiberBundle.Trivialization

/-- If `e` is a `trivialization` of `proj : Z → B` with fiber `F` and `h` is a homeomorphism
`F ≃ₜ F'`, then `e.trans_fiber_homeomorph h` is the trivialization of `proj` with the fiber `F'`
that sends `p : Z` to `((e p).1, h (e p).2)`. -/
def transFiberHomeomorph {F' : Type _} [TopologicalSpace F'] (e : Trivialization F proj) (h : F ≃ₜ F') :
    Trivialization F' proj where
  toLocalHomeomorph := e.toLocalHomeomorph.transHomeomorph <| (Homeomorph.refl _).prodCongr h
  BaseSet := e.BaseSet
  open_base_set := e.open_base_set
  source_eq := e.source_eq
  target_eq := by
    simp [← e.target_eq, ← prod_univ, ← preimage_preimage]
  proj_to_fun := e.proj_to_fun

@[simp]
theorem trans_fiber_homeomorph_apply {F' : Type _} [TopologicalSpace F'] (e : Trivialization F proj) (h : F ≃ₜ F')
    (x : Z) : e.transFiberHomeomorph h x = ((e x).1, h (e x).2) :=
  rfl

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations. See also
`trivialization.coord_change_homeomorph` for a version bundled as `F ≃ₜ F`. -/
def coordChange (e₁ e₂ : Trivialization F proj) (b : B) (x : F) : F :=
  (e₂ <| e₁.toLocalHomeomorph.symm (b, x)).2

theorem mk_coord_change (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.BaseSet) (h₂ : b ∈ e₂.BaseSet) (x : F) :
    (b, e₁.coordChange e₂ b x) = e₂ (e₁.toLocalHomeomorph.symm (b, x)) := by
  refine' Prod.extₓ _ rfl
  rw [e₂.coe_fst', ← e₁.coe_fst', e₁.apply_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]
    
  · rwa [e₁.proj_symm_apply' h₁]
    

theorem coord_change_apply_snd (e₁ e₂ : Trivialization F proj) {p : Z} (h : proj p ∈ e₁.BaseSet) :
    e₁.coordChange e₂ (proj p) (e₁ p).snd = (e₂ p).snd := by
  rw [coord_change, e₁.symm_apply_mk_proj (e₁.mem_source.2 h)]

theorem coord_change_same_apply (e : Trivialization F proj) {b : B} (h : b ∈ e.BaseSet) (x : F) :
    e.coordChange e b x = x := by
  rw [coord_change, e.apply_symm_apply' h]

theorem coord_change_same (e : Trivialization F proj) {b : B} (h : b ∈ e.BaseSet) : e.coordChange e b = id :=
  funext <| e.coord_change_same_apply h

theorem coord_change_coord_change (e₁ e₂ e₃ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.BaseSet) (h₂ : b ∈ e₂.BaseSet)
    (x : F) : e₂.coordChange e₃ b (e₁.coordChange e₂ b x) = e₁.coordChange e₃ b x := by
  rw [coord_change, e₁.mk_coord_change _ h₁ h₂, ← e₂.coe_coe, e₂.to_local_homeomorph.left_inv, coord_change]
  rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

theorem continuous_coord_change (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.BaseSet) (h₂ : b ∈ e₂.BaseSet) :
    Continuous (e₁.coordChange e₂ b) := by
  refine'
    continuous_snd.comp
      (e₂.to_local_homeomorph.continuous_on.comp_continuous
        (e₁.to_local_homeomorph.continuous_on_symm.comp_continuous _ _) _)
  · exact continuous_const.prod_mk continuous_id
    
  · exact fun x => e₁.mem_target.2 h₁
    
  · intro x
    rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]
    

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations,
as a homeomorphism. -/
def coordChangeHomeomorph (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.BaseSet) (h₂ : b ∈ e₂.BaseSet) :
    F ≃ₜ F where
  toFun := e₁.coordChange e₂ b
  invFun := e₂.coordChange e₁ b
  left_inv := fun x => by
    simp only [*, ← coord_change_coord_change, ← coord_change_same_apply]
  right_inv := fun x => by
    simp only [*, ← coord_change_coord_change, ← coord_change_same_apply]
  continuous_to_fun := e₁.continuous_coord_change e₂ h₁ h₂
  continuous_inv_fun := e₂.continuous_coord_change e₁ h₂ h₁

@[simp]
theorem coord_change_homeomorph_coe (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.BaseSet)
    (h₂ : b ∈ e₂.BaseSet) : ⇑(e₁.coordChangeHomeomorph e₂ h₁ h₂) = e₁.coordChange e₂ b :=
  rfl

end TopologicalFiberBundle.Trivialization

section Comap

open Classical

variable {B' : Type _} [TopologicalSpace B']

/-- Given a bundle trivialization of `proj : Z → B` and a continuous map `f : B' → B`,
construct a bundle trivialization of `φ : {p : B' × Z | f p.1 = proj p.2} → B'`
given by `φ x = (x : B' × Z).1`. -/
noncomputable def TopologicalFiberBundle.Trivialization.comap (e : Trivialization F proj) (f : B' → B)
    (hf : Continuous f) (b' : B') (hb' : f b' ∈ e.BaseSet) :
    Trivialization F fun x : { p : B' × Z | f p.1 = proj p.2 } => (x : B' × Z).1 where
  toFun := fun p => ((p : B' × Z).1, (e (p : B' × Z).2).2)
  invFun := fun p =>
    if h : f p.1 ∈ e.BaseSet then
      ⟨⟨p.1, e.toLocalHomeomorph.symm (f p.1, p.2)⟩, by
        simp [← e.proj_symm_apply' h]⟩
    else
      ⟨⟨b', e.toLocalHomeomorph.symm (f b', p.2)⟩, by
        simp [← e.proj_symm_apply' hb']⟩
  Source := { p | f (p : B' × Z).1 ∈ e.BaseSet }
  Target := { p | f p.1 ∈ e.BaseSet }
  map_source' := fun p hp => hp
  map_target' := fun p hp : f p.1 ∈ e.BaseSet => by
    simp [← hp]
  left_inv' := by
    rintro ⟨⟨b, x⟩, hbx⟩ hb
    dsimp'  at *
    have hx : x ∈ e.source := e.mem_source.2 (hbx ▸ hb)
    ext <;> simp [*]
  right_inv' := fun p hp : f p.1 ∈ e.BaseSet => by
    simp [*, ← e.apply_symm_apply']
  open_source := e.open_base_set.Preimage (hf.comp <| continuous_fst.comp continuous_subtype_coe)
  open_target := e.open_base_set.Preimage (hf.comp continuous_fst)
  continuous_to_fun :=
    (continuous_fst.comp continuous_subtype_coe).ContinuousOn.Prod <|
      continuous_snd.comp_continuous_on <|
        e.continuous_to_fun.comp (continuous_snd.comp continuous_subtype_coe).ContinuousOn <| by
          rintro ⟨⟨b, x⟩, hbx : f b = proj x⟩ (hb : f b ∈ e.base_set)
          rw [hbx] at hb
          exact e.mem_source.2 hb
  continuous_inv_fun := by
    rw [embedding_subtype_coe.continuous_on_iff]
    suffices
      ContinuousOn (fun p : B' × F => (p.1, e.to_local_homeomorph.symm (f p.1, p.2)))
        { p : B' × F | f p.1 ∈ e.base_set }
      by
      refine' this.congr fun p hp : f p.1 ∈ e.base_set => _
      simp [← hp]
    · refine' continuous_on_fst.prod (e.to_local_homeomorph.symm.continuous_on.comp _ _)
      · exact ((hf.comp continuous_fst).prod_mk continuous_snd).ContinuousOn
        
      · exact fun p hp => e.mem_target.2 hp
        
      
  BaseSet := f ⁻¹' e.BaseSet
  source_eq := rfl
  target_eq := by
    ext
    simp
  open_base_set := e.open_base_set.Preimage hf
  proj_to_fun := fun _ _ => rfl

/-- If `proj : Z → B` is a topological fiber bundle with fiber `F` and `f : B' → B` is a continuous
map, then the pullback bundle (a.k.a. induced bundle) is the topological bundle with the total space
`{(x, y) : B' × Z | f x = proj y}` given by `λ ⟨(x, y), h⟩, x`. -/
theorem IsTopologicalFiberBundle.comap (h : IsTopologicalFiberBundle F proj) {f : B' → B} (hf : Continuous f) :
    IsTopologicalFiberBundle F fun x : { p : B' × Z | f p.1 = proj p.2 } => (x : B' × Z).1 := fun x =>
  let ⟨e, he⟩ := h (f x)
  ⟨e.comap f hf x he, he⟩

end Comap

namespace TopologicalFiberBundle.Trivialization

theorem is_image_preimage_prod (e : Trivialization F proj) (s : Set B) :
    e.toLocalHomeomorph.IsImage (proj ⁻¹' s) (s ×ˢ (Univ : Set F)) := fun x hx => by
  simp [← e.coe_fst', ← hx]

/-- Restrict a `trivialization` to an open set in the base. `-/
def restrOpen (e : Trivialization F proj) (s : Set B) (hs : IsOpen s) : Trivialization F proj where
  toLocalHomeomorph :=
    ((e.is_image_preimage_prod s).symm.restr (IsOpen.inter e.open_target (hs.Prod is_open_univ))).symm
  BaseSet := e.BaseSet ∩ s
  open_base_set := IsOpen.inter e.open_base_set hs
  source_eq := by
    simp [← e.source_eq]
  target_eq := by
    simp [← e.target_eq, ← prod_univ]
  proj_to_fun := fun p hp => e.proj_to_fun p hp.1

section Piecewise

theorem frontier_preimage (e : Trivialization F proj) (s : Set B) :
    e.Source ∩ Frontier (proj ⁻¹' s) = proj ⁻¹' (e.BaseSet ∩ Frontier s) := by
  rw [← (e.is_image_preimage_prod s).Frontier.preimage_eq, frontier_prod_univ_eq,
    (e.is_image_preimage_prod _).preimage_eq, e.source_eq, preimage_inter]

/-- Given two bundle trivializations `e`, `e'` of `proj : Z → B` and a set `s : set B` such that
the base sets of `e` and `e'` intersect `frontier s` on the same set and `e p = e' p` whenever
`proj p ∈ e.base_set ∩ frontier s`, `e.piecewise e' s Hs Heq` is the bundle trivialization over
`set.ite s e.base_set e'.base_set` that is equal to `e` on `proj ⁻¹ s` and is equal to `e'`
otherwise. -/
noncomputable def piecewise (e e' : Trivialization F proj) (s : Set B)
    (Hs : e.BaseSet ∩ Frontier s = e'.BaseSet ∩ Frontier s) (Heq : EqOn e e' <| proj ⁻¹' (e.BaseSet ∩ Frontier s)) :
    Trivialization F proj where
  toLocalHomeomorph :=
    e.toLocalHomeomorph.piecewise e'.toLocalHomeomorph (proj ⁻¹' s) (s ×ˢ (Univ : Set F)) (e.is_image_preimage_prod s)
      (e'.is_image_preimage_prod s)
      (by
        rw [e.frontier_preimage, e'.frontier_preimage, Hs])
      (by
        rwa [e.frontier_preimage])
  BaseSet := s.ite e.BaseSet e'.BaseSet
  open_base_set := e.open_base_set.ite e'.open_base_set Hs
  source_eq := by
    simp [← e.source_eq, ← e'.source_eq]
  target_eq := by
    simp [← e.target_eq, ← e'.target_eq, ← prod_univ]
  proj_to_fun := by
    rintro p (⟨he, hs⟩ | ⟨he, hs⟩) <;> simp [*]

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B`
over a linearly ordered base `B` and a point `a ∈ e.base_set ∩ e'.base_set` such that
`e` equals `e'` on `proj ⁻¹' {a}`, `e.piecewise_le_of_eq e' a He He' Heq` is the bundle
trivialization over `set.ite (Iic a) e.base_set e'.base_set` that is equal to `e` on points `p`
such that `proj p ≤ a` and is equal to `e'` otherwise. -/
noncomputable def piecewiseLeOfEq [LinearOrderₓ B] [OrderTopology B] (e e' : Trivialization F proj) (a : B)
    (He : a ∈ e.BaseSet) (He' : a ∈ e'.BaseSet) (Heq : ∀ p, proj p = a → e p = e' p) : Trivialization F proj :=
  e.piecewise e' (Iic a)
    (Set.ext fun x =>
      And.congr_left_iff.2 fun hx => by
        simp [← He, ← He', ← mem_singleton_iff.1 (frontier_Iic_subset _ hx)])
    fun p hp => Heq p <| frontier_Iic_subset _ hp.2

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B` over a
linearly ordered base `B` and a point `a ∈ e.base_set ∩ e'.base_set`, `e.piecewise_le e' a He He'`
is the bundle trivialization over `set.ite (Iic a) e.base_set e'.base_set` that is equal to `e` on
points `p` such that `proj p ≤ a` and is equal to `((e' p).1, h (e' p).2)` otherwise, where
`h = `e'.coord_change_homeomorph e _ _` is the homeomorphism of the fiber such that
`h (e' p).2 = (e p).2` whenever `e p = a`. -/
noncomputable def piecewiseLe [LinearOrderₓ B] [OrderTopology B] (e e' : Trivialization F proj) (a : B)
    (He : a ∈ e.BaseSet) (He' : a ∈ e'.BaseSet) : Trivialization F proj :=
  e.piecewiseLeOfEq (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e He' He)) a He He' <| by
    rintro p rfl
    ext1
    · simp [← e.coe_fst', ← e'.coe_fst', *]
      
    · simp [← e'.coord_change_apply_snd, *]
      

/-- Given two bundle trivializations `e`, `e'` over disjoint sets, `e.disjoint_union e' H` is the
bundle trivialization over the union of the base sets that agrees with `e` and `e'` over their
base sets. -/
noncomputable def disjointUnion (e e' : Trivialization F proj) (H : Disjoint e.BaseSet e'.BaseSet) :
    Trivialization F proj where
  toLocalHomeomorph :=
    e.toLocalHomeomorph.disjointUnion e'.toLocalHomeomorph
      (fun x hx => by
        rw [e.source_eq, e'.source_eq] at hx
        exact H hx)
      fun x hx => by
      rw [e.target_eq, e'.target_eq] at hx
      exact H ⟨hx.1.1, hx.2.1⟩
  BaseSet := e.BaseSet ∪ e'.BaseSet
  open_base_set := IsOpen.union e.open_base_set e'.open_base_set
  source_eq := congr_arg2ₓ (· ∪ ·) e.source_eq e'.source_eq
  target_eq := (congr_arg2ₓ (· ∪ ·) e.target_eq e'.target_eq).trans union_prod.symm
  proj_to_fun := by
    rintro p (hp | hp')
    · show (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_mem, e.coe_fst] <;> exact hp
      
    · show (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_not_mem, e'.coe_fst hp']
      simp only [← e.source_eq, ← e'.source_eq] at hp'⊢
      exact fun h => H ⟨h, hp'⟩
      

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
/-- If `h` is a topological fiber bundle over a conditionally complete linear order,
then it is trivial over any closed interval. -/
theorem _root_.is_topological_fiber_bundle.exists_trivialization_Icc_subset [ConditionallyCompleteLinearOrder B]
    [OrderTopology B] (h : IsTopologicalFiberBundle F proj) (a b : B) :
    ∃ e : Trivialization F proj, Icc a b ⊆ e.BaseSet := by
  classical
  obtain ⟨ea, hea⟩ : ∃ ea : trivialization F proj, a ∈ ea.BaseSet := h a
  -- If `a < b`, then `[a, b] = ∅`, and the statement is trivial
    cases' le_or_ltₓ a b with hab hab <;>
    [skip,
    exact
      ⟨ea, by
        simp [*]⟩]
  /- Let `s` be the set of points `x ∈ [a, b]` such that `proj` is trivializable over `[a, x]`.
    We need to show that `b ∈ s`. Let `c = Sup s`. We will show that `c ∈ s` and `c = b`. -/
  set s : Set B := { x ∈ Icc a b | ∃ e : trivialization F proj, Icc a x ⊆ e.BaseSet }
  have ha : a ∈ s :=
    ⟨left_mem_Icc.2 hab, ea, by
      simp [← hea]⟩
  have sne : s.nonempty := ⟨a, ha⟩
  have hsb : b ∈ UpperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  set c := Sup s
  have hsc : IsLub s c := is_lub_cSup sne sbd
  have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  obtain ⟨-, ec : trivialization F proj, hec : Icc a c ⊆ ec.base_set⟩ : c ∈ s := by
    cases' hc.1.eq_or_lt with heq hlt
    · rwa [← HEq]
      
    refine' ⟨hc, _⟩
    /- In order to show that `c ∈ s`, consider a trivialization `ec` of `proj` over a neighborhood
        of `c`. Its base set includes `(c', c]` for some `c' ∈ [a, c)`. -/
    rcases h c with ⟨ec, hc⟩
    obtain ⟨c', hc', hc'e⟩ : ∃ c' ∈ Ico a c, Ioc c' c ⊆ ec.base_set :=
      (mem_nhds_within_Iic_iff_exists_mem_Ico_Ioc_subset hlt).1
        (mem_nhds_within_of_mem_nhds <| IsOpen.mem_nhds ec.open_base_set hc)
    /- Since `c' < c = Sup s`, there exists `d ∈ s ∩ (c', c]`. Let `ead` be a trivialization of
        `proj` over `[a, d]`. Then we can glue `ead` and `ec` into a trivialization over `[a, c]`. -/
    obtain ⟨d, ⟨hdab, ead, had⟩, hd⟩ : ∃ d ∈ s, d ∈ Ioc c' c := hsc.exists_between hc'.2
    refine' ⟨ead.piecewise_le ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 _⟩
    refine' ⟨fun x hx => had ⟨hx.1.1, hx.2⟩, fun x hx => hc'e ⟨hd.1.trans (not_leₓ.1 hx.2), hx.1.2⟩⟩
  /- So, `c ∈ s`. Let `ec` be a trivialization of `proj` over `[a, c]`.  If `c = b`, then we are
    done. Otherwise we show that `proj` can be trivialized over a larger interval `[a, d]`,
    `d ∈ (c, b]`, hence `c` is not an upper bound of `s`. -/
  cases' hc.2.eq_or_lt with heq hlt
  · exact ⟨ec, HEq ▸ hec⟩
    
  suffices ∃ d ∈ Ioc c b, ∃ e : trivialization F proj, Icc a d ⊆ e.BaseSet by
    rcases this with ⟨d, hdcb, hd⟩
    exact ((hsc.1 ⟨⟨hc.1.trans hdcb.1.le, hdcb.2⟩, hd⟩).not_lt hdcb.1).elim
  /- Since the base set of `ec` is open, it includes `[c, d)` (hence, `[a, d)`) for some
    `d ∈ (c, b]`. -/
  obtain ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, Ico c d ⊆ ec.base_set :=
    (mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hlt).1
      (mem_nhds_within_of_mem_nhds <| IsOpen.mem_nhds ec.open_base_set (hec ⟨hc.1, le_rfl⟩))
  have had : Ico a d ⊆ ec.base_set := Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
  by_cases' he : Disjoint (Iio d) (Ioi c)
  · /- If `(c, d) = ∅`, then let `ed` be a trivialization of `proj` over a neighborhood of `d`.
        Then the disjoint union of `ec` restricted to `(-∞, d)` and `ed` restricted to `(c, ∞)` is
        a trivialization over `[a, d]`. -/
    rcases h d with ⟨ed, hed⟩
    refine'
      ⟨d, hdcb,
        (ec.restr_open (Iio d) is_open_Iio).disjointUnion (ed.restr_open (Ioi c) is_open_Ioi)
          (he.mono (inter_subset_right _ _) (inter_subset_right _ _)),
        fun x hx => _⟩
    rcases hx.2.eq_or_lt with (rfl | hxd)
    exacts[Or.inr ⟨hed, hdcb.1⟩, Or.inl ⟨had ⟨hx.1, hxd⟩, hxd⟩]
    
  · /- If `(c, d)` is nonempty, then take `d' ∈ (c, d)`. Since the base set of `ec` includes
        `[a, d)`, it includes `[a, d'] ⊆ [a, d)` as well. -/
    rw [disjoint_left] at he
    push_neg  at he
    rcases he with ⟨d', hdd' : d' < d, hd'c⟩
    exact ⟨d', ⟨hd'c, hdd'.le.trans hdcb.2⟩, ec, (Icc_subset_Ico_right hdd').trans had⟩
    

end Piecewise

end TopologicalFiberBundle.Trivialization

end TopologicalFiberBundle

/-! ### Constructing topological fiber bundles -/


namespace Bundle

variable (E : B → Type _)

attribute [mfld_simps]
  total_space.proj total_space_mk coe_fst coe_snd coe_snd_map_apply coe_snd_map_smul total_space.mk_cast

instance [I : TopologicalSpace F] : ∀ x : B, TopologicalSpace (Trivial B F x) := fun x => I

instance [t₁ : TopologicalSpace B] [t₂ : TopologicalSpace F] : TopologicalSpace (TotalSpace (Trivial B F)) :=
  induced TotalSpace.proj t₁⊓induced (Trivial.projSnd B F) t₂

end Bundle

/-- Core data defining a locally trivial topological bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type `ι`, on open subsets `base_set i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coord_change i j` from
`base_set i ∩ base_set j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(base_set i ∩ base_set j) × F` to avoid the topology on the
space of continuous maps on `F`. -/
@[nolint has_inhabited_instance]
structure TopologicalFiberBundleCore (ι : Type _) (B : Type _) [TopologicalSpace B] (F : Type _)
  [TopologicalSpace F] where
  BaseSet : ι → Set B
  is_open_base_set : ∀ i, IsOpen (base_set i)
  indexAt : B → ι
  mem_base_set_at : ∀ x, x ∈ base_set (index_at x)
  coordChange : ι → ι → B → F → F
  coord_change_self : ∀ i, ∀, ∀ x ∈ base_set i, ∀, ∀ v, coord_change i i x v = v
  coord_change_continuous :
    ∀ i j, ContinuousOn (fun p : B × F => coord_change i j p.1 p.2) ((base_set i ∩ base_set j) ×ˢ (Univ : Set F))
  coord_change_comp :
    ∀ i j k,
      ∀,
        ∀ x ∈ base_set i ∩ base_set j ∩ base_set k,
          ∀, ∀ v, (coord_change j k x) (coord_change i j x v) = coord_change i k x v

namespace TopologicalFiberBundleCore

variable [TopologicalSpace B] [TopologicalSpace F] (Z : TopologicalFiberBundleCore ι B F)

include Z

/-- The index set of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_inhabited_instance]
def Index :=
  ι

/-- The base space of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments, reducible]
def Base :=
  B

/-- The fiber of a topological fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_inhabited_instance]
def Fiber (x : B) :=
  F

section FiberInstances

attribute [local reducible] fiber

instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) := by
  infer_instance

end FiberInstances

/-- The total space of the topological fiber bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`, a.k.a. `Σ x, Z.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def TotalSpace :=
  Bundle.TotalSpace Z.Fiber

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
def proj : Z.TotalSpace → B :=
  Bundle.TotalSpace.proj

/-- Local homeomorphism version of the trivialization change. -/
def trivChange (i j : ι) : LocalHomeomorph (B × F) (B × F) where
  Source := (Z.BaseSet i ∩ Z.BaseSet j) ×ˢ (Univ : Set F)
  Target := (Z.BaseSet i ∩ Z.BaseSet j) ×ˢ (Univ : Set F)
  toFun := fun p => ⟨p.1, Z.coordChange i j p.1 p.2⟩
  invFun := fun p => ⟨p.1, Z.coordChange j i p.1 p.2⟩
  map_source' := fun p hp => by
    simpa using hp
  map_target' := fun p hp => by
    simpa using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [← prod_mk_mem_set_prod_eq, ← mem_inter_eq, ← and_trueₓ, ← mem_univ] at hx
    rw [Z.coord_change_comp, Z.coord_change_self]
    · exact hx.1
      
    · simp [← hx]
      
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [← prod_mk_mem_set_prod_eq, ← mem_inter_eq, ← and_trueₓ, ← mem_univ] at hx
    rw [Z.coord_change_comp, Z.coord_change_self]
    · exact hx.2
      
    · simp [← hx]
      
  open_source := (IsOpen.inter (Z.is_open_base_set i) (Z.is_open_base_set j)).Prod is_open_univ
  open_target := (IsOpen.inter (Z.is_open_base_set i) (Z.is_open_base_set j)).Prod is_open_univ
  continuous_to_fun := ContinuousOn.prod continuous_fst.ContinuousOn (Z.coord_change_continuous i j)
  continuous_inv_fun := by
    simpa [← inter_comm] using ContinuousOn.prod continuous_fst.continuous_on (Z.coord_change_continuous j i)

@[simp, mfld_simps]
theorem mem_triv_change_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).Source ↔ p.1 ∈ Z.BaseSet i ∩ Z.BaseSet j := by
  erw [mem_prod]
  simp

/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (base_set i)` and `base_set i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be a local homeomorphism. For now, we only introduce the
local equiv version, denoted with a prime. In further developments, avoid this auxiliary version,
and use `Z.local_triv` instead.
-/
def localTrivAsLocalEquiv (i : ι) : LocalEquiv Z.TotalSpace (B × F) where
  Source := Z.proj ⁻¹' Z.BaseSet i
  Target := Z.BaseSet i ×ˢ (Univ : Set F)
  invFun := fun p => ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩
  toFun := fun p => ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩
  map_source' := fun p hp => by
    simpa only [← Set.mem_preimage, ← and_trueₓ, ← Set.mem_univ, ← Set.prod_mk_mem_set_prod_eq] using hp
  map_target' := fun p hp => by
    simpa only [← Set.mem_preimage, ← and_trueₓ, ← Set.mem_univ, ← Set.mem_prod] using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    change x ∈ Z.base_set i at hx
    dsimp' only
    rw [Z.coord_change_comp, Z.coord_change_self]
    · exact Z.mem_base_set_at _
      
    · simp only [← hx, ← mem_inter_eq, ← and_selfₓ, ← mem_base_set_at]
      
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [← prod_mk_mem_set_prod_eq, ← and_trueₓ, ← mem_univ] at hx
    rw [Z.coord_change_comp, Z.coord_change_self]
    · exact hx
      
    · simp only [← hx, ← mem_inter_eq, ← and_selfₓ, ← mem_base_set_at]
      

variable (i : ι)

theorem mem_local_triv_as_local_equiv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTrivAsLocalEquiv i).Source ↔ p.1 ∈ Z.BaseSet i :=
  Iff.rfl

theorem mem_local_triv_as_local_equiv_target (p : B × F) : p ∈ (Z.localTrivAsLocalEquiv i).Target ↔ p.1 ∈ Z.BaseSet i :=
  by
  erw [mem_prod]
  simp only [← and_trueₓ, ← mem_univ]

theorem local_triv_as_local_equiv_apply (p : Z.TotalSpace) :
    (Z.localTrivAsLocalEquiv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

/-- The composition of two local trivializations is the trivialization change Z.triv_change i j. -/
theorem local_triv_as_local_equiv_trans (i j : ι) :
    (Z.localTrivAsLocalEquiv i).symm.trans (Z.localTrivAsLocalEquiv j) ≈ (Z.trivChange i j).toLocalEquiv := by
  constructor
  · ext x
    simp' only [← mem_local_triv_as_local_equiv_target] with mfld_simps
    rfl
    
  · rintro ⟨x, v⟩ hx
    simp only [← triv_change, ← local_triv_as_local_equiv, ← LocalEquiv.symm, ← true_andₓ, ← Prod.mk.inj_iff, ←
      prod_mk_mem_set_prod_eq, ← LocalEquiv.trans_source, ← mem_inter_eq, ← and_trueₓ, ← mem_preimage, ← proj, ←
      mem_univ, ← LocalEquiv.coe_mk, ← eq_self_iff_true, ← LocalEquiv.coe_trans, ← total_space.proj] at hx⊢
    simp only [← Z.coord_change_comp, ← hx, ← mem_inter_eq, ← and_selfₓ, ← mem_base_set_at]
    

variable (ι)

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance toTopologicalSpace : TopologicalSpace (Bundle.TotalSpace Z.Fiber) :=
  TopologicalSpace.generateFrom <| ⋃ (i : ι) (s : Set (B × F)) (s_open : IsOpen s), {(Z i).Source ∩ Z i ⁻¹' s}

variable {ι}

theorem open_source' (i : ι) : IsOpen (Z.localTrivAsLocalEquiv i).Source := by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [← exists_prop, ← mem_Union, ← mem_singleton_iff]
  refine' ⟨i, Z.base_set i ×ˢ (univ : Set F), (Z.is_open_base_set i).Prod is_open_univ, _⟩
  ext p
  simp only [← local_triv_as_local_equiv_apply, ← prod_mk_mem_set_prod_eq, ← mem_inter_eq, ← and_selfₓ, ←
    mem_local_triv_as_local_equiv_source, ← and_trueₓ, ← mem_univ, ← mem_preimage]

open TopologicalFiberBundle

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def localTriv (i : ι) : Trivialization F Z.proj where
  BaseSet := Z.BaseSet i
  open_base_set := Z.is_open_base_set i
  source_eq := rfl
  target_eq := rfl
  proj_to_fun := fun p hp => by
    simp' only with mfld_simps
    rfl
  open_source := Z.open_source' i
  open_target := (Z.is_open_base_set i).Prod is_open_univ
  continuous_to_fun := by
    rw [continuous_on_open_iff (Z.open_source' i)]
    intro s s_open
    apply TopologicalSpace.GenerateOpen.basic
    simp only [← exists_prop, ← mem_Union, ← mem_singleton_iff]
    exact ⟨i, s, s_open, rfl⟩
  continuous_inv_fun := by
    apply continuous_on_open_of_generate_from ((Z.is_open_base_set i).Prod is_open_univ)
    intro t ht
    simp only [← exists_prop, ← mem_Union, ← mem_singleton_iff] at ht
    obtain ⟨j, s, s_open, ts⟩ :
      ∃ j s, IsOpen s ∧ t = (local_triv_as_local_equiv Z j).Source ∩ local_triv_as_local_equiv Z j ⁻¹' s := ht
    rw [ts]
    simp only [← LocalEquiv.right_inv, ← preimage_inter, ← LocalEquiv.left_inv]
    let e := Z.local_triv_as_local_equiv i
    let e' := Z.local_triv_as_local_equiv j
    let f := e.symm.trans e'
    have : IsOpen (f.source ∩ f ⁻¹' s) := by
      rw [(Z.local_triv_as_local_equiv_trans i j).source_inter_preimage_eq]
      exact (continuous_on_open_iff (Z.triv_change i j).open_source).1 (Z.triv_change i j).ContinuousOn _ s_open
    convert this using 1
    dsimp' [← LocalEquiv.trans_source]
    rw [← preimage_comp, inter_assoc]
    rfl
  toLocalEquiv := Z.localTrivAsLocalEquiv i

/-- A topological fiber bundle constructed from core is indeed a topological fiber bundle. -/
protected theorem is_topological_fiber_bundle : IsTopologicalFiberBundle F Z.proj := fun x =>
  ⟨Z.localTriv (Z.indexAt x), Z.mem_base_set_at x⟩

/-- The projection on the base of a topological bundle created from core is continuous -/
theorem continuous_proj : Continuous Z.proj :=
  Z.IsTopologicalFiberBundle.continuous_proj

/-- The projection on the base of a topological bundle created from core is an open map -/
theorem is_open_map_proj : IsOpenMap Z.proj :=
  Z.IsTopologicalFiberBundle.is_open_map_proj

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def localTrivAt (b : B) : Trivialization F Z.proj :=
  Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]
theorem local_triv_at_def (b : B) : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl

/-- If an element of `F` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is continuous. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
theorem continuous_const_section (v : F) (h : ∀ i j, ∀, ∀ x ∈ Z.BaseSet i ∩ Z.BaseSet j, ∀, Z.coordChange i j x v = v) :
    Continuous (show B → Z.TotalSpace from fun x => ⟨x, v⟩) := by
  apply continuous_iff_continuous_at.2 fun x => _
  have A : Z.base_set (Z.index_at x) ∈ 𝓝 x := IsOpen.mem_nhds (Z.is_open_base_set (Z.index_at x)) (Z.mem_base_set_at x)
  apply ((Z.local_triv_at x).toLocalHomeomorph.continuous_at_iff_continuous_at_comp_left _).2
  · simp' only [← (· ∘ ·)] with mfld_simps
    apply continuous_at_id.prod
    have : ContinuousOn (fun y : B => v) (Z.base_set (Z.index_at x)) := continuous_on_const
    apply (this.congr _).ContinuousAt A
    intro y hy
    simp' only [← h, ← hy, ← mem_base_set_at] with mfld_simps
    
  · exact A
    

@[simp, mfld_simps]
theorem local_triv_as_local_equiv_coe : ⇑(Z.localTrivAsLocalEquiv i) = Z.localTriv i :=
  rfl

@[simp, mfld_simps]
theorem local_triv_as_local_equiv_source : (Z.localTrivAsLocalEquiv i).Source = (Z.localTriv i).Source :=
  rfl

@[simp, mfld_simps]
theorem local_triv_as_local_equiv_target : (Z.localTrivAsLocalEquiv i).Target = (Z.localTriv i).Target :=
  rfl

@[simp, mfld_simps]
theorem local_triv_as_local_equiv_symm : (Z.localTrivAsLocalEquiv i).symm = (Z.localTriv i).toLocalEquiv.symm :=
  rfl

@[simp, mfld_simps]
theorem base_set_at : Z.BaseSet i = (Z.localTriv i).BaseSet :=
  rfl

@[simp, mfld_simps]
theorem local_triv_apply (p : Z.TotalSpace) : (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem local_triv_at_apply (p : Z.TotalSpace) : (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩ := by
  rw [local_triv_at, local_triv_apply, coord_change_self]
  exact Z.mem_base_set_at p.1

@[simp, mfld_simps]
theorem local_triv_at_apply_mk (b : B) (a : F) : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.local_triv_at_apply _

@[simp, mfld_simps]
theorem mem_local_triv_source (p : Z.TotalSpace) : p ∈ (Z.localTriv i).Source ↔ p.1 ∈ (Z.localTriv i).BaseSet :=
  Iff.rfl

@[simp, mfld_simps]
theorem mem_local_triv_at_source (p : Z.TotalSpace) (b : B) :
    p ∈ (Z.localTrivAt b).Source ↔ p.1 ∈ (Z.localTrivAt b).BaseSet :=
  Iff.rfl

@[simp, mfld_simps]
theorem mem_local_triv_target (p : B × F) : p ∈ (Z.localTriv i).Target ↔ p.1 ∈ (Z.localTriv i).BaseSet :=
  Trivialization.mem_target _

@[simp, mfld_simps]
theorem mem_local_triv_at_target (p : B × F) (b : B) : p ∈ (Z.localTrivAt b).Target ↔ p.1 ∈ (Z.localTrivAt b).BaseSet :=
  Trivialization.mem_target _

@[simp, mfld_simps]
theorem local_triv_symm_apply (p : B × F) :
    (Z.localTriv i).toLocalHomeomorph.symm p = ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem mem_local_triv_at_base_set (b : B) : b ∈ (Z.localTrivAt b).BaseSet := by
  rw [local_triv_at, ← base_set_at]
  exact Z.mem_base_set_at b

/-- The inclusion of a fiber into the total space is a continuous map. -/
@[continuity]
theorem continuous_total_space_mk (b : B) : Continuous (totalSpaceMk b : Z.Fiber b → Bundle.TotalSpace Z.Fiber) := by
  rw [continuous_iff_le_induced, TopologicalFiberBundleCore.toTopologicalSpace]
  apply le_induced_generate_from
  simp only [← total_space_mk, ← mem_Union, ← mem_singleton_iff, ← local_triv_as_local_equiv_source, ←
    local_triv_as_local_equiv_coe]
  rintro s ⟨i, t, ht, rfl⟩
  rw [← (Z.local_triv i).source_inter_preimage_target_inter t, preimage_inter, ← preimage_comp,
    trivialization.source_eq]
  apply IsOpen.inter
  · simp only [← total_space.proj, ← proj, preimage_comp]
    by_cases' b ∈ (Z.local_triv i).BaseSet
    · rw [preimage_const_of_mem h]
      exact is_open_univ
      
    · rw [preimage_const_of_not_mem h]
      exact is_open_empty
      
    
  · simp only [← Function.comp, ← local_triv_apply]
    rw [preimage_inter, preimage_comp]
    by_cases' b ∈ Z.base_set i
    · have hc : Continuous fun x : Z.fiber b => (Z.coord_change (Z.index_at b) i b) x :=
        (Z.coord_change_continuous (Z.index_at b) i).comp_continuous (continuous_const.prod_mk continuous_id) fun x =>
          ⟨⟨Z.mem_base_set_at b, h⟩, mem_univ x⟩
      exact (((Z.local_triv i).open_target.inter ht).Preimage (Continuous.Prod.mk b)).Preimage hc
      
    · rw [(Z.local_triv i).target_eq, ← base_set_at, mk_preimage_prod_right_eq_empty h, preimage_empty, empty_inter]
      exact is_open_empty
      
    

end TopologicalFiberBundleCore

variable (F) {Z : Type _} [TopologicalSpace B] [TopologicalSpace F] {proj : Z → B}

open TopologicalFiberBundle

-- ./././Mathport/Syntax/Translate/Basic.lean:701:2: warning: expanding binder collection (e e' «expr ∈ » pretrivialization_atlas)
/-- This structure permits to define a fiber bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphism and hence local trivializations. -/
@[nolint has_inhabited_instance]
structure TopologicalFiberPrebundle (proj : Z → B) where
  PretrivializationAtlas : Set (Pretrivialization F proj)
  pretrivializationAt : B → Pretrivialization F proj
  mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).BaseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas
  continuous_triv_change :
    ∀ e e' _ : e ∈ pretrivialization_atlas _ : e' ∈ pretrivialization_atlas,
      ContinuousOn (e ∘ e'.toLocalEquiv.symm) (e'.Target ∩ e'.toLocalEquiv.symm ⁻¹' e.Source)

namespace TopologicalFiberPrebundle

variable {F} (a : TopologicalFiberPrebundle F proj) {e : Pretrivialization F proj}

/-- Topology on the total space that will make the prebundle into a bundle. -/
def totalSpaceTopology (a : TopologicalFiberPrebundle F proj) : TopologicalSpace Z :=
  ⨆ (e : Pretrivialization F proj) (he : e ∈ a.PretrivializationAtlas), coinduced e.setSymm Subtype.topologicalSpace

theorem continuous_symm_of_mem_pretrivialization_atlas (he : e ∈ a.PretrivializationAtlas) :
    @ContinuousOn _ _ _ a.totalSpaceTopology e.toLocalEquiv.symm e.Target := by
  refine' id fun z H => id fun U h => preimage_nhds_within_coinduced' H e.open_target (le_def.1 (nhds_mono _) U h)
  exact le_supr₂ e he

theorem is_open_source (e : Pretrivialization F proj) : @IsOpen _ a.totalSpaceTopology e.Source := by
  let this := a.total_space_topology
  refine' is_open_supr_iff.mpr fun e' => _
  refine' is_open_supr_iff.mpr fun he' => _
  refine' is_open_coinduced.mpr (is_open_induced_iff.mpr ⟨e.target, e.open_target, _⟩)
  rw [pretrivialization.set_symm, restrict, e.target_eq, e.source_eq, preimage_comp,
    Subtype.preimage_coe_eq_preimage_coe_iff, e'.target_eq, prod_inter_prod, inter_univ,
    pretrivialization.preimage_symm_proj_inter]

theorem is_open_target_of_mem_pretrivialization_atlas_inter (e e' : Pretrivialization F proj)
    (he' : e' ∈ a.PretrivializationAtlas) : IsOpen (e'.toLocalEquiv.Target ∩ e'.toLocalEquiv.symm ⁻¹' e.Source) := by
  let this := a.total_space_topology
  obtain ⟨u, hu1, hu2⟩ :=
    continuous_on_iff'.mp (a.continuous_symm_of_mem_pretrivialization_atlas he') e.source (a.is_open_source e)
  rw [inter_comm, hu2]
  exact hu1.inter e'.open_target

/-- Promotion from a `pretrivialization` to a `trivialization`. -/
def trivializationOfMemPretrivializationAtlas (he : e ∈ a.PretrivializationAtlas) :
    @Trivialization B F Z _ _ a.totalSpaceTopology proj :=
  { e with open_source := a.is_open_source e,
    continuous_to_fun := by
      let this := a.total_space_topology
      refine'
        continuous_on_iff'.mpr fun s hs =>
          ⟨e ⁻¹' s ∩ e.source, is_open_supr_iff.mpr fun e' => _, by
            rw [inter_assoc, inter_self]
            rfl⟩
      refine' is_open_supr_iff.mpr fun he' => _
      rw [is_open_coinduced, is_open_induced_iff]
      obtain ⟨u, hu1, hu2⟩ := continuous_on_iff'.mp (a.continuous_triv_change _ he _ he') s hs
      have hu3 := congr_arg (fun s => (fun x : e'.target => (x : B × F)) ⁻¹' s) hu2
      simp only [← Subtype.coe_preimage_self, ← preimage_inter, ← univ_inter] at hu3
      refine'
        ⟨u ∩ e'.to_local_equiv.target ∩ e'.to_local_equiv.symm ⁻¹' e.source, _, by
          simp only [← preimage_inter, ← inter_univ, ← Subtype.coe_preimage_self, ← hu3.symm]
          rfl⟩
      rw [inter_assoc]
      exact hu1.inter (a.is_open_target_of_mem_pretrivialization_atlas_inter e e' he'),
    continuous_inv_fun := a.continuous_symm_of_mem_pretrivialization_atlas he }

theorem is_topological_fiber_bundle : @IsTopologicalFiberBundle B F Z _ _ a.totalSpaceTopology proj := fun x =>
  ⟨a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x), a.mem_base_pretrivialization_at x⟩

theorem continuous_proj : @Continuous _ _ a.totalSpaceTopology _ proj := by
  let this := a.total_space_topology
  exact a.is_topological_fiber_bundle.continuous_proj

/-- For a fiber bundle `Z` over `B` constructed using the `topological_fiber_prebundle` mechanism,
continuity of a function `Z → X` on an open set `s` can be checked by precomposing at each point
with the pretrivialization used for the construction at that point. -/
theorem continuous_on_of_comp_right {X : Type _} [TopologicalSpace X] {f : Z → X} {s : Set B} (hs : IsOpen s)
    (hf :
      ∀,
        ∀ b ∈ s,
          ∀,
            ContinuousOn (f ∘ (a.pretrivializationAt b).toLocalEquiv.symm)
              ((s ∩ (a.pretrivializationAt b).BaseSet) ×ˢ (Set.Univ : Set F))) :
    @ContinuousOn _ _ a.totalSpaceTopology _ f (proj ⁻¹' s) := by
  let this := a.total_space_topology
  intro z hz
  let e : trivialization F proj :=
    a.trivialization_of_mem_pretrivialization_atlas (a.pretrivialization_mem_atlas (proj z))
  refine' (e.continuous_at_of_comp_right _ ((hf (proj z) hz).ContinuousAt (IsOpen.mem_nhds _ _))).ContinuousWithinAt
  · exact a.mem_base_pretrivialization_at (proj z)
    
  · exact (hs.inter (a.pretrivialization_at (proj z)).open_base_set).Prod is_open_univ
    
  refine' ⟨_, mem_univ _⟩
  rw [e.coe_fst]
  · exact ⟨hz, a.mem_base_pretrivialization_at (proj z)⟩
    
  · rw [e.mem_source]
    exact a.mem_base_pretrivialization_at (proj z)
    

end TopologicalFiberPrebundle

