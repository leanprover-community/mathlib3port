import Mathbin.Topology.LocalHomeomorph 
import Mathbin.Topology.Algebra.Ordered.Basic 
import Mathbin.Data.Bundle

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


variable{ι : Type _}{B : Type _}{F : Type _}

open TopologicalSpace Filter Set

open_locale TopologicalSpace Classical

/-! ### General definition of topological fiber bundles -/


section TopologicalFiberBundle

variable(F){Z : Type _}[TopologicalSpace B][TopologicalSpace F]{proj : Z → B}

/-- This structure contains the information left for a local trivialization (which is implemented
below as `trivialization F proj`) if the total space has not been given a topology, but we
have a topology on both the fiber and the base space. Through the construction
`topological_fiber_prebundle F proj` it will be possible to promote a
`pretrivialization F proj` to a `trivialization F proj`. -/
@[nolint has_inhabited_instance]
structure TopologicalFiberBundle.Pretrivialization(proj : Z → B) extends LocalEquiv Z (B × F) where 
  open_target : IsOpen target 
  BaseSet : Set B 
  open_base_set : IsOpen base_set 
  source_eq : source = proj ⁻¹' base_set 
  target_eq : target = Set.Prod base_set univ 
  proj_to_fun : ∀ p _ : p ∈ source, (to_fun p).1 = proj p

open TopologicalFiberBundle

namespace TopologicalFiberBundle.Pretrivialization

instance  : CoeFun (pretrivialization F proj) fun _ => Z → B × F :=
  ⟨fun e => e.to_fun⟩

variable{F}(e : pretrivialization F proj){x : Z}

@[simp, mfld_simps]
theorem coe_coe : «expr⇑ » e.to_local_equiv = e :=
  rfl

@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.source) : (e x).1 = proj x :=
  e.proj_to_fun x ex

theorem mem_source : x ∈ e.source ↔ proj x ∈ e.base_set :=
  by 
    rw [e.source_eq, mem_preimage]

theorem coe_fst' (ex : proj x ∈ e.base_set) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)

protected theorem eq_on : eq_on (Prod.fst ∘ e) proj e.source :=
  fun x hx => e.coe_fst hx

theorem mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst ex).symm rfl

theorem mk_proj_snd' (ex : proj x ∈ e.base_set) : (proj x, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst' ex).symm rfl

/-- Composition of inverse and coercion from the subtype of the target. -/
def set_symm : e.target → Z :=
  Set.restrict e.to_local_equiv.symm e.target

theorem mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
  by 
    rw [e.target_eq, prod_univ, mem_preimage]

-- error in Topology.FiberBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem proj_symm_apply
{x : «expr × »(B, F)}
(hx : «expr ∈ »(x, e.target)) : «expr = »(proj (e.to_local_equiv.symm x), x.1) :=
begin
  have [] [] [":=", expr (e.coe_fst (e.to_local_equiv.map_target hx)).symm],
  rwa ["[", "<-", expr e.coe_coe, ",", expr e.to_local_equiv.right_inv hx, "]"] ["at", ident this]
end

theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) : proj (e.to_local_equiv.symm (b, x)) = b :=
  e.proj_symm_apply (e.mem_target.2 hx)

theorem apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_equiv.symm x) = x :=
  e.to_local_equiv.right_inv hx

theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) : e (e.to_local_equiv.symm (b, x)) = (b, x) :=
  e.apply_symm_apply (e.mem_target.2 hx)

@[simp, mfld_simps]
theorem symm_apply_mk_proj {x : Z} (ex : x ∈ e.source) : e.to_local_equiv.symm (proj x, (e x).2) = x :=
  by 
    rw [←e.coe_fst ex, Prod.mk.eta, ←e.coe_coe, e.to_local_equiv.left_inv ex]

@[simp, mfld_simps]
theorem preimage_symm_proj_base_set : e.to_local_equiv.symm ⁻¹' (proj ⁻¹' e.base_set) ∩ e.target = e.target :=
  by 
    refine' inter_eq_right_iff_subset.mpr fun x hx => _ 
    simp only [mem_preimage, LocalEquiv.inv_fun_as_coe, e.proj_symm_apply hx]
    exact e.mem_target.mp hx

@[simp, mfld_simps]
theorem preimage_symm_proj_inter (s : Set B) :
  e.to_local_equiv.symm ⁻¹' (proj ⁻¹' s) ∩ e.base_set.prod univ = (s ∩ e.base_set).Prod univ :=
  by 
    refine' subset.antisymm_iff.mpr ⟨fun x hx => _, fun x hx => mem_inter _ _⟩
    ·
      rw [←e.target_eq] at hx 
      simp only [mem_inter_iff, mem_preimage, e.proj_symm_apply hx.2] at hx 
      simp only [mem_inter_eq, and_trueₓ, mem_univ, mem_prod]
      exact ⟨hx.1, e.mem_target.mp hx.2⟩
    ·
      simp only [mem_inter_eq, and_trueₓ, mem_univ, mem_prod, e.mem_target.symm] at hx 
      simp only [mem_preimage, e.proj_symm_apply hx.2]
      exact hx.1
    ·
      rw [←inter_univ univ, ←prod_inter_prod, mem_inter_eq] at hx 
      exact hx.2

end TopologicalFiberBundle.Pretrivialization

variable[TopologicalSpace Z]

/--
A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
@[nolint has_inhabited_instance]
structure TopologicalFiberBundle.Trivialization(proj : Z → B) extends LocalHomeomorph Z (B × F) where 
  BaseSet : Set B 
  open_base_set : IsOpen base_set 
  source_eq : source = proj ⁻¹' base_set 
  target_eq : target = Set.Prod base_set univ 
  proj_to_fun : ∀ p _ : p ∈ source, (to_local_homeomorph p).1 = proj p

open TopologicalFiberBundle

namespace TopologicalFiberBundle.Trivialization

variable{F}(e : trivialization F proj){x : Z}

/-- Natural identification as a `pretrivialization`. -/
def to_pretrivialization : TopologicalFiberBundle.Pretrivialization F proj :=
  { e with  }

instance  : CoeFun (trivialization F proj) fun _ => Z → B × F :=
  ⟨fun e => e.to_fun⟩

instance  : Coe (trivialization F proj) (pretrivialization F proj) :=
  ⟨to_pretrivialization⟩

@[simp, mfld_simps]
theorem coe_coe : «expr⇑ » e.to_local_homeomorph = e :=
  rfl

@[simp, mfld_simps]
theorem coe_fst (ex : x ∈ e.source) : (e x).1 = proj x :=
  e.proj_to_fun x ex

protected theorem eq_on : eq_on (Prod.fst ∘ e) proj e.source :=
  fun x hx => e.coe_fst hx

theorem mem_source : x ∈ e.source ↔ proj x ∈ e.base_set :=
  by 
    rw [e.source_eq, mem_preimage]

theorem coe_fst' (ex : proj x ∈ e.base_set) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)

theorem mk_proj_snd (ex : x ∈ e.source) : (proj x, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst ex).symm rfl

theorem mk_proj_snd' (ex : proj x ∈ e.base_set) : (proj x, (e x).2) = e x :=
  Prod.extₓ (e.coe_fst' ex).symm rfl

theorem source_inter_preimage_target_inter (s : Set (B × F)) : e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.to_local_homeomorph.source_inter_preimage_target_inter s

@[simp, mfld_simps]
theorem coe_mk (e : LocalHomeomorph Z (B × F)) i j k l m (x : Z) :
  (trivialization.mk e i j k l m : trivialization F proj) x = e x :=
  rfl

theorem mem_target {x : B × F} : x ∈ e.target ↔ x.1 ∈ e.base_set :=
  e.to_pretrivialization.mem_target

theorem map_target {x : B × F} (hx : x ∈ e.target) : e.to_local_homeomorph.symm x ∈ e.source :=
  e.to_local_homeomorph.map_target hx

theorem proj_symm_apply {x : B × F} (hx : x ∈ e.target) : proj (e.to_local_homeomorph.symm x) = x.1 :=
  e.to_pretrivialization.proj_symm_apply hx

theorem proj_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) : proj (e.to_local_homeomorph.symm (b, x)) = b :=
  e.to_pretrivialization.proj_symm_apply' hx

theorem apply_symm_apply {x : B × F} (hx : x ∈ e.target) : e (e.to_local_homeomorph.symm x) = x :=
  e.to_local_homeomorph.right_inv hx

theorem apply_symm_apply' {b : B} {x : F} (hx : b ∈ e.base_set) : e (e.to_local_homeomorph.symm (b, x)) = (b, x) :=
  e.to_pretrivialization.apply_symm_apply' hx

@[simp, mfld_simps]
theorem symm_apply_mk_proj (ex : x ∈ e.source) : e.to_local_homeomorph.symm (proj x, (e x).2) = x :=
  e.to_pretrivialization.symm_apply_mk_proj ex

theorem coe_fst_eventually_eq_proj (ex : x ∈ e.source) : (Prod.fst ∘ e) =ᶠ[𝓝 x] proj :=
  mem_nhds_iff.2 ⟨e.source, fun y hy => e.coe_fst hy, e.open_source, ex⟩

theorem coe_fst_eventually_eq_proj' (ex : proj x ∈ e.base_set) : (Prod.fst ∘ e) =ᶠ[𝓝 x] proj :=
  e.coe_fst_eventually_eq_proj (e.mem_source.2 ex)

theorem map_proj_nhds (ex : x ∈ e.source) : map proj (𝓝 x) = 𝓝 (proj x) :=
  by 
    rw [←e.coe_fst ex, ←map_congr (e.coe_fst_eventually_eq_proj ex), ←map_map, ←e.coe_coe,
      e.to_local_homeomorph.map_nhds_eq ex, map_fst_nhds]

/-- In the domain of a bundle trivialization, the projection is continuous-/
theorem continuous_at_proj (ex : x ∈ e.source) : ContinuousAt proj x :=
  (e.map_proj_nhds ex).le

/-- Composition of a `trivialization` and a `homeomorph`. -/
def comp_homeomorph {Z' : Type _} [TopologicalSpace Z'] (h : Z' ≃ₜ Z) : trivialization F (proj ∘ h) :=
  { toLocalHomeomorph := h.to_local_homeomorph.trans e.to_local_homeomorph, BaseSet := e.base_set,
    open_base_set := e.open_base_set,
    source_eq :=
      by 
        simp [e.source_eq, preimage_preimage],
    target_eq :=
      by 
        simp [e.target_eq],
    proj_to_fun :=
      fun p hp =>
        have hp : h p ∈ e.source :=
          by 
            simpa using hp 
        by 
          simp [hp] }

end TopologicalFiberBundle.Trivialization

/-- A topological fiber bundle with fiber `F` over a base `B` is a space projecting on `B`
for which the fibers are all homeomorphic to `F`, such that the local situation around each point
is a direct product. -/
def IsTopologicalFiberBundle (proj : Z → B) : Prop :=
  ∀ x : B, ∃ e : trivialization F proj, x ∈ e.base_set

/-- A trivial topological fiber bundle with fiber `F` over a base `B` is a space `Z`
projecting on `B` for which there exists a homeomorphism to `B × F` that sends `proj`
to `prod.fst`. -/
def IsTrivialTopologicalFiberBundle (proj : Z → B) : Prop :=
  ∃ e : Z ≃ₜ B × F, ∀ x, (e x).1 = proj x

variable{F}

theorem IsTrivialTopologicalFiberBundle.is_topological_fiber_bundle (h : IsTrivialTopologicalFiberBundle F proj) :
  IsTopologicalFiberBundle F proj :=
  let ⟨e, he⟩ := h 
  fun x => ⟨⟨e.to_local_homeomorph, univ, is_open_univ, rfl, univ_prod_univ.symm, fun x _ => he x⟩, mem_univ x⟩

/-- The projection from a topological fiber bundle to its base is continuous. -/
theorem IsTopologicalFiberBundle.continuous_proj (h : IsTopologicalFiberBundle F proj) : Continuous proj :=
  by 
    rw [continuous_iff_continuous_at]
    intro x 
    rcases h (proj x) with ⟨e, ex⟩
    apply e.continuous_at_proj 
    rwa [e.source_eq]

/-- The projection from a topological fiber bundle to its base is an open map. -/
theorem IsTopologicalFiberBundle.is_open_map_proj (h : IsTopologicalFiberBundle F proj) : IsOpenMap proj :=
  by 
    refine' is_open_map_iff_nhds_le.2 fun x => _ 
    rcases h (proj x) with ⟨e, ex⟩
    refine' (e.map_proj_nhds _).Ge 
    rwa [e.source_eq]

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
  (e : IsTopologicalFiberBundle F proj) (h : Z' ≃ₜ Z) : IsTopologicalFiberBundle F (proj ∘ h) :=
  fun x =>
    let ⟨e, he⟩ := e x
    ⟨e.comp_homeomorph h,
      by 
        simpa [TopologicalFiberBundle.Trivialization.compHomeomorph] using he⟩

namespace TopologicalFiberBundle.Trivialization

/-- If `e` is a `trivialization` of `proj : Z → B` with fiber `F` and `h` is a homeomorphism
`F ≃ₜ F'`, then `e.trans_fiber_homeomorph h` is the trivialization of `proj` with the fiber `F'`
that sends `p : Z` to `((e p).1, h (e p).2)`. -/
def trans_fiber_homeomorph {F' : Type _} [TopologicalSpace F'] (e : trivialization F proj) (h : F ≃ₜ F') :
  trivialization F' proj :=
  { toLocalHomeomorph := e.to_local_homeomorph.trans ((Homeomorph.refl _).prodCongr h).toLocalHomeomorph,
    BaseSet := e.base_set, open_base_set := e.open_base_set,
    source_eq :=
      by 
        simp [e.source_eq],
    target_eq :=
      by 
        ext 
        simp [e.target_eq],
    proj_to_fun :=
      fun p hp =>
        have  : p ∈ e.source :=
          by 
            simpa using hp 
        by 
          simp [this] }

@[simp]
theorem trans_fiber_homeomorph_apply {F' : Type _} [TopologicalSpace F'] (e : trivialization F proj) (h : F ≃ₜ F')
  (x : Z) : e.trans_fiber_homeomorph h x = ((e x).1, h (e x).2) :=
  rfl

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations. See also
`trivialization.coord_change_homeomorph` for a version bundled as `F ≃ₜ F`. -/
def coord_change (e₁ e₂ : trivialization F proj) (b : B) (x : F) : F :=
  (e₂$ e₁.to_local_homeomorph.symm (b, x)).2

theorem mk_coord_change (e₁ e₂ : trivialization F proj) {b : B} (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) (x : F) :
  (b, e₁.coord_change e₂ b x) = e₂ (e₁.to_local_homeomorph.symm (b, x)) :=
  by 
    refine' Prod.extₓ _ rfl 
    rw [e₂.coe_fst', ←e₁.coe_fst', e₁.apply_symm_apply' h₁]
    ·
      rwa [e₁.proj_symm_apply' h₁]
    ·
      rwa [e₁.proj_symm_apply' h₁]

theorem coord_change_apply_snd (e₁ e₂ : trivialization F proj) {p : Z} (h : proj p ∈ e₁.base_set) :
  e₁.coord_change e₂ (proj p) (e₁ p).snd = (e₂ p).snd :=
  by 
    rw [coord_change, e₁.symm_apply_mk_proj (e₁.mem_source.2 h)]

theorem coord_change_same_apply (e : trivialization F proj) {b : B} (h : b ∈ e.base_set) (x : F) :
  e.coord_change e b x = x :=
  by 
    rw [coord_change, e.apply_symm_apply' h]

theorem coord_change_same (e : trivialization F proj) {b : B} (h : b ∈ e.base_set) : e.coord_change e b = id :=
  funext$ e.coord_change_same_apply h

theorem coord_change_coord_change (e₁ e₂ e₃ : trivialization F proj) {b : B} (h₁ : b ∈ e₁.base_set)
  (h₂ : b ∈ e₂.base_set) (x : F) : e₂.coord_change e₃ b (e₁.coord_change e₂ b x) = e₁.coord_change e₃ b x :=
  by 
    rw [coord_change, e₁.mk_coord_change _ h₁ h₂, ←e₂.coe_coe, e₂.to_local_homeomorph.left_inv, coord_change]
    rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

theorem continuous_coord_change (e₁ e₂ : trivialization F proj) {b : B} (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) :
  Continuous (e₁.coord_change e₂ b) :=
  by 
    refine'
      continuous_snd.comp
        (e₂.to_local_homeomorph.continuous_on.comp_continuous
          (e₁.to_local_homeomorph.continuous_on_symm.comp_continuous _ _) _)
    ·
      exact continuous_const.prod_mk continuous_id
    ·
      exact fun x => e₁.mem_target.2 h₁
    ·
      intro x 
      rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

/-- Coordinate transformation in the fiber induced by a pair of bundle trivializations,
as a homeomorphism. -/
def coord_change_homeomorph (e₁ e₂ : trivialization F proj) {b : B} (h₁ : b ∈ e₁.base_set) (h₂ : b ∈ e₂.base_set) :
  F ≃ₜ F :=
  { toFun := e₁.coord_change e₂ b, invFun := e₂.coord_change e₁ b,
    left_inv :=
      fun x =>
        by 
          simp only [coord_change_coord_change, coord_change_same_apply],
    right_inv :=
      fun x =>
        by 
          simp only [coord_change_coord_change, coord_change_same_apply],
    continuous_to_fun := e₁.continuous_coord_change e₂ h₁ h₂,
    continuous_inv_fun := e₂.continuous_coord_change e₁ h₂ h₁ }

@[simp]
theorem coord_change_homeomorph_coe (e₁ e₂ : trivialization F proj) {b : B} (h₁ : b ∈ e₁.base_set)
  (h₂ : b ∈ e₂.base_set) : «expr⇑ » (e₁.coord_change_homeomorph e₂ h₁ h₂) = e₁.coord_change e₂ b :=
  rfl

end TopologicalFiberBundle.Trivialization

section Comap

open_locale Classical

variable{B' : Type _}[TopologicalSpace B']

-- error in Topology.FiberBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a bundle trivialization of `proj : Z → B` and a continuous map `f : B' → B`,
construct a bundle trivialization of `φ : {p : B' × Z | f p.1 = proj p.2} → B'`
given by `φ x = (x : B' × Z).1`. -/
noncomputable
def topological_fiber_bundle.trivialization.comap
(e : trivialization F proj)
(f : B' → B)
(hf : continuous f)
(b' : B')
(hb' : «expr ∈ »(f b', e.base_set)) : trivialization F (λ
 x : {p : «expr × »(B', Z) | «expr = »(f p.1, proj p.2)}, (x : «expr × »(B', Z)).1) :=
{ to_fun := λ p, ((p : «expr × »(B', Z)).1, (e (p : «expr × »(B', Z)).2).2),
  inv_fun := λ
  p, if h : «expr ∈ »(f p.1, e.base_set) then ⟨⟨p.1, e.to_local_homeomorph.symm (f p.1, p.2)⟩, by simp [] [] [] ["[", expr e.proj_symm_apply' h, "]"] [] []⟩ else ⟨⟨b', e.to_local_homeomorph.symm (f b', p.2)⟩, by simp [] [] [] ["[", expr e.proj_symm_apply' hb', "]"] [] []⟩,
  source := {p | «expr ∈ »(f (p : «expr × »(B', Z)).1, e.base_set)},
  target := {p | «expr ∈ »(f p.1, e.base_set)},
  map_source' := λ p hp, hp,
  map_target' := λ (p) (hp : «expr ∈ »(f p.1, e.base_set)), by simp [] [] [] ["[", expr hp, "]"] [] [],
  left_inv' := begin
    rintro ["⟨", "⟨", ident b, ",", ident x, "⟩", ",", ident hbx, "⟩", ident hb],
    dsimp [] [] [] ["at", "*"],
    have [ident hx] [":", expr «expr ∈ »(x, e.source)] [],
    from [expr e.mem_source.2 «expr ▸ »(hbx, hb)],
    ext [] [] []; simp [] [] [] ["*"] [] []
  end,
  right_inv' := λ
  (p)
  (hp : «expr ∈ »(f p.1, e.base_set)), by simp [] [] [] ["[", "*", ",", expr e.apply_symm_apply', "]"] [] [],
  open_source := e.open_base_set.preimage «expr $ »(hf.comp, continuous_fst.comp continuous_subtype_coe),
  open_target := e.open_base_set.preimage (hf.comp continuous_fst),
  continuous_to_fun := «expr $ »((continuous_fst.comp continuous_subtype_coe).continuous_on.prod, «expr $ »(continuous_snd.comp_continuous_on, «expr $ »(e.continuous_to_fun.comp (continuous_snd.comp continuous_subtype_coe).continuous_on, by { rintro ["⟨", "⟨", ident b, ",", ident x, "⟩", ",", "(", ident hbx, ":", expr «expr = »(f b, proj x), ")", "⟩", "(", ident hb, ":", expr «expr ∈ »(f b, e.base_set), ")"],
       rw [expr hbx] ["at", ident hb],
       exact [expr e.mem_source.2 hb] }))),
  continuous_inv_fun := begin
    rw ["[", expr embedding_subtype_coe.continuous_on_iff, "]"] [],
    suffices [] [":", expr continuous_on (λ
      p : «expr × »(B', F), (p.1, e.to_local_homeomorph.symm (f p.1, p.2))) {p : «expr × »(B', F) | «expr ∈ »(f p.1, e.base_set)}],
    { refine [expr this.congr (λ (p) (hp : «expr ∈ »(f p.1, e.base_set)), _)],
      simp [] [] [] ["[", expr hp, "]"] [] [] },
    { refine [expr continuous_on_fst.prod (e.to_local_homeomorph.symm.continuous_on.comp _ _)],
      { exact [expr ((hf.comp continuous_fst).prod_mk continuous_snd).continuous_on] },
      { exact [expr λ p hp, e.mem_target.2 hp] } }
  end,
  base_set := «expr ⁻¹' »(f, e.base_set),
  source_eq := rfl,
  target_eq := by { ext [] [] [],
    simp [] [] [] [] [] [] },
  open_base_set := e.open_base_set.preimage hf,
  proj_to_fun := λ _ _, rfl }

/-- If `proj : Z → B` is a topological fiber bundle with fiber `F` and `f : B' → B` is a continuous
map, then the pullback bundle (a.k.a. induced bundle) is the topological bundle with the total space
`{(x, y) : B' × Z | f x = proj y}` given by `λ ⟨(x, y), h⟩, x`. -/
theorem IsTopologicalFiberBundle.comap (h : IsTopologicalFiberBundle F proj) {f : B' → B} (hf : Continuous f) :
  IsTopologicalFiberBundle F fun x : { p:B' × Z | f p.1 = proj p.2 } => (x : B' × Z).1 :=
  fun x =>
    let ⟨e, he⟩ := h (f x)
    ⟨e.comap f hf x he, he⟩

end Comap

namespace TopologicalFiberBundle.Trivialization

theorem is_image_preimage_prod (e : trivialization F proj) (s : Set B) :
  e.to_local_homeomorph.is_image (proj ⁻¹' s) (s.prod univ) :=
  fun x hx =>
    by 
      simp [e.coe_fst', hx]

/-- Restrict a `trivialization` to an open set in the base. `-/
def restr_open (e : trivialization F proj) (s : Set B) (hs : IsOpen s) : trivialization F proj :=
  { toLocalHomeomorph :=
      ((e.is_image_preimage_prod s).symm.restr (IsOpen.inter e.open_target (hs.prod is_open_univ))).symm,
    BaseSet := e.base_set ∩ s, open_base_set := IsOpen.inter e.open_base_set hs,
    source_eq :=
      by 
        simp [e.source_eq],
    target_eq :=
      by 
        simp [e.target_eq, prod_univ],
    proj_to_fun := fun p hp => e.proj_to_fun p hp.1 }

section Piecewise

theorem frontier_preimage (e : trivialization F proj) (s : Set B) :
  e.source ∩ Frontier (proj ⁻¹' s) = proj ⁻¹' (e.base_set ∩ Frontier s) :=
  by 
    rw [←(e.is_image_preimage_prod s).Frontier.preimage_eq, frontier_prod_univ_eq,
      (e.is_image_preimage_prod _).preimage_eq, e.source_eq, preimage_inter]

/-- Given two bundle trivializations `e`, `e'` of `proj : Z → B` and a set `s : set B` such that
the base sets of `e` and `e'` intersect `frontier s` on the same set and `e p = e' p` whenever
`proj p ∈ e.base_set ∩ frontier s`, `e.piecewise e' s Hs Heq` is the bundle trivialization over
`set.ite s e.base_set e'.base_set` that is equal to `e` on `proj ⁻¹ s` and is equal to `e'`
otherwise. -/
noncomputable def piecewise (e e' : trivialization F proj) (s : Set B)
  (Hs : e.base_set ∩ Frontier s = e'.base_set ∩ Frontier s) (Heq : eq_on e e'$ proj ⁻¹' (e.base_set ∩ Frontier s)) :
  trivialization F proj :=
  { toLocalHomeomorph :=
      e.to_local_homeomorph.piecewise e'.to_local_homeomorph (proj ⁻¹' s) (s.prod univ) (e.is_image_preimage_prod s)
        (e'.is_image_preimage_prod s)
        (by 
          rw [e.frontier_preimage, e'.frontier_preimage, Hs])
        (by 
          rwa [e.frontier_preimage]),
    BaseSet := s.ite e.base_set e'.base_set, open_base_set := e.open_base_set.ite e'.open_base_set Hs,
    source_eq :=
      by 
        simp [e.source_eq, e'.source_eq],
    target_eq :=
      by 
        simp [e.target_eq, e'.target_eq, prod_univ],
    proj_to_fun :=
      by 
        rintro p (⟨he, hs⟩ | ⟨he, hs⟩) <;> simp  }

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B`
over a linearly ordered base `B` and a point `a ∈ e.base_set ∩ e'.base_set` such that
`e` equals `e'` on `proj ⁻¹' {a}`, `e.piecewise_le_of_eq e' a He He' Heq` is the bundle
trivialization over `set.ite (Iic a) e.base_set e'.base_set` that is equal to `e` on points `p`
such that `proj p ≤ a` and is equal to `e'` otherwise. -/
noncomputable def piecewise_le_of_eq [LinearOrderₓ B] [OrderTopology B] (e e' : trivialization F proj) (a : B)
  (He : a ∈ e.base_set) (He' : a ∈ e'.base_set) (Heq : ∀ p, proj p = a → e p = e' p) : trivialization F proj :=
  e.piecewise e' (Iic a)
    (Set.ext$
      fun x =>
        And.congr_left_iff.2$
          fun hx =>
            by 
              simp [He, He', mem_singleton_iff.1 (frontier_Iic_subset _ hx)])
    fun p hp => Heq p$ frontier_Iic_subset _ hp.2

/-- Given two bundle trivializations `e`, `e'` of a topological fiber bundle `proj : Z → B` over a
linearly ordered base `B` and a point `a ∈ e.base_set ∩ e'.base_set`, `e.piecewise_le e' a He He'`
is the bundle trivialization over `set.ite (Iic a) e.base_set e'.base_set` that is equal to `e` on
points `p` such that `proj p ≤ a` and is equal to `((e' p).1, h (e' p).2)` otherwise, where
`h = `e'.coord_change_homeomorph e _ _` is the homeomorphism of the fiber such that
`h (e' p).2 = (e p).2` whenever `e p = a`. -/
noncomputable def piecewise_le [LinearOrderₓ B] [OrderTopology B] (e e' : trivialization F proj) (a : B)
  (He : a ∈ e.base_set) (He' : a ∈ e'.base_set) : trivialization F proj :=
  e.piecewise_le_of_eq (e'.trans_fiber_homeomorph (e'.coord_change_homeomorph e He' He)) a He He'$
    by 
      (
        rintro p rfl)
      ext1
      ·
        simp [e.coe_fst', e'.coe_fst']
      ·
        simp [e'.coord_change_apply_snd]

/-- Given two bundle trivializations `e`, `e'` over disjoint sets, `e.disjoint_union e' H` is the
bundle trivialization over the union of the base sets that agrees with `e` and `e'` over their
base sets. -/
noncomputable def disjoint_union (e e' : trivialization F proj) (H : Disjoint e.base_set e'.base_set) :
  trivialization F proj :=
  { toLocalHomeomorph :=
      e.to_local_homeomorph.disjoint_union e'.to_local_homeomorph
        (fun x hx =>
          by 
            rw [e.source_eq, e'.source_eq] at hx 
            exact H hx)
        fun x hx =>
          by 
            rw [e.target_eq, e'.target_eq] at hx 
            exact H ⟨hx.1.1, hx.2.1⟩,
    BaseSet := e.base_set ∪ e'.base_set, open_base_set := IsOpen.union e.open_base_set e'.open_base_set,
    source_eq := congr_arg2 (· ∪ ·) e.source_eq e'.source_eq,
    target_eq := (congr_arg2 (· ∪ ·) e.target_eq e'.target_eq).trans union_prod.symm,
    proj_to_fun :=
      by 
        rintro p (hp | hp')
        ·
          show (e.source.piecewise e e' p).1 = proj p 
          rw [piecewise_eq_of_mem, e.coe_fst] <;> exact hp
        ·
          show (e.source.piecewise e e' p).1 = proj p 
          rw [piecewise_eq_of_not_mem, e'.coe_fst hp']
          simp only [e.source_eq, e'.source_eq] at hp'⊢
          exact fun h => H ⟨h, hp'⟩ }

-- error in Topology.FiberBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `h` is a topological fiber bundle over a conditionally complete linear order,
then it is trivial over any closed interval. -/
theorem _root_.is_topological_fiber_bundle.exists_trivialization_Icc_subset
[conditionally_complete_linear_order B]
[order_topology B]
(h : is_topological_fiber_bundle F proj)
(a b : B) : «expr∃ , »((e : trivialization F proj), «expr ⊆ »(Icc a b, e.base_set)) :=
begin
  classical,
  obtain ["⟨", ident ea, ",", ident hea, "⟩", ":", expr «expr∃ , »((ea : trivialization F proj), «expr ∈ »(a, ea.base_set)), ":=", expr h a],
  cases [expr le_or_lt a b] ["with", ident hab, ident hab]; [skip, exact [expr ⟨ea, by simp [] [] [] ["*"] [] []⟩]],
  set [] [ident s] [":", expr set B] [":="] [expr {x ∈ Icc a b | «expr∃ , »((e : trivialization F proj), «expr ⊆ »(Icc a x, e.base_set))}] [],
  have [ident ha] [":", expr «expr ∈ »(a, s)] [],
  from [expr ⟨left_mem_Icc.2 hab, ea, by simp [] [] [] ["[", expr hea, "]"] [] []⟩],
  have [ident sne] [":", expr s.nonempty] [":=", expr ⟨a, ha⟩],
  have [ident hsb] [":", expr «expr ∈ »(b, upper_bounds s)] [],
  from [expr λ x hx, hx.1.2],
  have [ident sbd] [":", expr bdd_above s] [":=", expr ⟨b, hsb⟩],
  set [] [ident c] [] [":="] [expr Sup s] [],
  have [ident hsc] [":", expr is_lub s c] [],
  from [expr is_lub_cSup sne sbd],
  have [ident hc] [":", expr «expr ∈ »(c, Icc a b)] [],
  from [expr ⟨hsc.1 ha, hsc.2 hsb⟩],
  obtain ["⟨", "-", ",", ident ec, ":", expr trivialization F proj, ",", ident hec, ":", expr «expr ⊆ »(Icc a c, ec.base_set), "⟩", ":", expr «expr ∈ »(c, s)],
  { cases [expr hc.1.eq_or_lt] ["with", ident heq, ident hlt],
    { rwa ["<-", expr heq] [] },
    refine [expr ⟨hc, _⟩],
    rcases [expr h c, "with", "⟨", ident ec, ",", ident hc, "⟩"],
    obtain ["⟨", ident c', ",", ident hc', ",", ident hc'e, "⟩", ":", expr «expr∃ , »((c' «expr ∈ » Ico a c), «expr ⊆ »(Ioc c' c, ec.base_set)), ":=", expr (mem_nhds_within_Iic_iff_exists_mem_Ico_Ioc_subset hlt).1 «expr $ »(mem_nhds_within_of_mem_nhds, is_open.mem_nhds ec.open_base_set hc)],
    obtain ["⟨", ident d, ",", "⟨", ident hdab, ",", ident ead, ",", ident had, "⟩", ",", ident hd, "⟩", ":", expr «expr∃ , »((d «expr ∈ » s), «expr ∈ »(d, Ioc c' c)), ":=", expr hsc.exists_between hc'.2],
    refine [expr ⟨ead.piecewise_le ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 _⟩],
    refine [expr ⟨λ x hx, had ⟨hx.1.1, hx.2⟩, λ x hx, hc'e ⟨hd.1.trans (not_le.1 hx.2), hx.1.2⟩⟩] },
  cases [expr hc.2.eq_or_lt] ["with", ident heq, ident hlt],
  { exact [expr ⟨ec, «expr ▸ »(heq, hec)⟩] },
  suffices [] [":", expr «expr∃ , »((d «expr ∈ » Ioc c b) (e : trivialization F proj), «expr ⊆ »(Icc a d, e.base_set))],
  { rcases [expr this, "with", "⟨", ident d, ",", ident hdcb, ",", ident hd, "⟩"],
    exact [expr ((hsc.1 ⟨⟨hc.1.trans hdcb.1.le, hdcb.2⟩, hd⟩).not_lt hdcb.1).elim] },
  obtain ["⟨", ident d, ",", ident hdcb, ",", ident hd, "⟩", ":", expr «expr∃ , »((d «expr ∈ » Ioc c b), «expr ⊆ »(Ico c d, ec.base_set)), ":=", expr (mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hlt).1 «expr $ »(mem_nhds_within_of_mem_nhds, is_open.mem_nhds ec.open_base_set (hec ⟨hc.1, le_rfl⟩))],
  have [ident had] [":", expr «expr ⊆ »(Ico a d, ec.base_set)] [],
  from [expr subset.trans Ico_subset_Icc_union_Ico (union_subset hec hd)],
  by_cases [expr he, ":", expr disjoint (Iio d) (Ioi c)],
  { rcases [expr h d, "with", "⟨", ident ed, ",", ident hed, "⟩"],
    refine [expr ⟨d, hdcb, (ec.restr_open (Iio d) is_open_Iio).disjoint_union (ed.restr_open (Ioi c) is_open_Ioi) (he.mono (inter_subset_right _ _) (inter_subset_right _ _)), λ
      x hx, _⟩],
    rcases [expr hx.2.eq_or_lt, "with", ident rfl, "|", ident hxd],
    exacts ["[", expr or.inr ⟨hed, hdcb.1⟩, ",", expr or.inl ⟨had ⟨hx.1, hxd⟩, hxd⟩, "]"] },
  { rw ["[", expr disjoint_left, "]"] ["at", ident he],
    push_neg ["at", ident he],
    rcases [expr he, "with", "⟨", ident d', ",", ident hdd', ":", expr «expr < »(d', d), ",", ident hd'c, "⟩"],
    exact [expr ⟨d', ⟨hd'c, hdd'.le.trans hdcb.2⟩, ec, subset.trans (Icc_subset_Ico_right hdd') had⟩] }
end

end Piecewise

end TopologicalFiberBundle.Trivialization

end TopologicalFiberBundle

/-! ### Constructing topological fiber bundles -/


namespace Bundle

variable(E : B → Type _)

attribute [mfld_simps] proj total_space_mk coe_fst coe_snd_map_apply coe_snd_map_smul

instance  [I : TopologicalSpace F] : ∀ x : B, TopologicalSpace (trivialₓ B F x) :=
  fun x => I

instance  [t₁ : TopologicalSpace B] [t₂ : TopologicalSpace F] : TopologicalSpace (total_space (trivialₓ B F)) :=
  TopologicalSpace.induced (proj (trivialₓ B F)) t₁⊓TopologicalSpace.induced (trivial.proj_snd B F) t₂

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
structure TopologicalFiberBundleCore(ι : Type _)(B : Type _)[TopologicalSpace B](F : Type _)[TopologicalSpace F] where 
  BaseSet : ι → Set B 
  is_open_base_set : ∀ i, IsOpen (base_set i)
  indexAt : B → ι 
  mem_base_set_at : ∀ x, x ∈ base_set (index_at x)
  coordChange : ι → ι → B → F → F 
  coord_change_self : ∀ i, ∀ x _ : x ∈ base_set i, ∀ v, coord_change i i x v = v 
  coord_change_continuous :
  ∀ i j, ContinuousOn (fun p : B × F => coord_change i j p.1 p.2) (Set.Prod (base_set i ∩ base_set j) univ)
  coord_change_comp :
  ∀ i j k,
    ∀ x _ : x ∈ base_set i ∩ base_set j ∩ base_set k,
      ∀ v, (coord_change j k x) (coord_change i j x v) = coord_change i k x v

namespace TopologicalFiberBundleCore

variable[TopologicalSpace B][TopologicalSpace F](Z : TopologicalFiberBundleCore ι B F)

include Z

/-- The index set of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_inhabited_instance]
def index :=
  ι

/-- The base space of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments, reducible]
def base :=
  B

/-- The fiber of a topological fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_inhabited_instance]
def fiber (x : B) :=
  F

section FiberInstances

attribute [local reducible] fiber

instance topological_space_fiber (x : B) : TopologicalSpace (Z.fiber x) :=
  by 
    infer_instance

end FiberInstances

/-- The total space of the topological fiber bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`, a.k.a. `Σ x, Z.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def total_space :=
  Bundle.TotalSpace Z.fiber

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
def proj : Z.total_space → B :=
  Bundle.proj Z.fiber

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : LocalHomeomorph (B × F) (B × F) :=
  { Source := Set.Prod (Z.base_set i ∩ Z.base_set j) univ, Target := Set.Prod (Z.base_set i ∩ Z.base_set j) univ,
    toFun := fun p => ⟨p.1, Z.coord_change i j p.1 p.2⟩, invFun := fun p => ⟨p.1, Z.coord_change j i p.1 p.2⟩,
    map_source' :=
      fun p hp =>
        by 
          simpa using hp,
    map_target' :=
      fun p hp =>
        by 
          simpa using hp,
    left_inv' :=
      by 
        rintro ⟨x, v⟩ hx 
        simp only [prod_mk_mem_set_prod_eq, mem_inter_eq, and_trueₓ, mem_univ] at hx 
        rw [Z.coord_change_comp, Z.coord_change_self]
        ·
          exact hx.1
        ·
          simp [hx],
    right_inv' :=
      by 
        rintro ⟨x, v⟩ hx 
        simp only [prod_mk_mem_set_prod_eq, mem_inter_eq, and_trueₓ, mem_univ] at hx 
        rw [Z.coord_change_comp, Z.coord_change_self]
        ·
          exact hx.2
        ·
          simp [hx],
    open_source := (IsOpen.inter (Z.is_open_base_set i) (Z.is_open_base_set j)).Prod is_open_univ,
    open_target := (IsOpen.inter (Z.is_open_base_set i) (Z.is_open_base_set j)).Prod is_open_univ,
    continuous_to_fun := ContinuousOn.prod continuous_fst.ContinuousOn (Z.coord_change_continuous i j),
    continuous_inv_fun :=
      by 
        simpa [inter_comm] using ContinuousOn.prod continuous_fst.continuous_on (Z.coord_change_continuous j i) }

@[simp, mfld_simps]
theorem mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (Z.triv_change i j).Source ↔ p.1 ∈ Z.base_set i ∩ Z.base_set j :=
  by 
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
def local_triv_as_local_equiv (i : ι) : LocalEquiv Z.total_space (B × F) :=
  { Source := Z.proj ⁻¹' Z.base_set i, Target := Set.Prod (Z.base_set i) univ,
    invFun := fun p => ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩,
    toFun := fun p => ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩,
    map_source' :=
      fun p hp =>
        by 
          simpa only [Set.mem_preimage, and_trueₓ, Set.mem_univ, Set.prod_mk_mem_set_prod_eq] using hp,
    map_target' :=
      fun p hp =>
        by 
          simpa only [Set.mem_preimage, and_trueₓ, Set.mem_univ, Set.mem_prod] using hp,
    left_inv' :=
      by 
        rintro ⟨x, v⟩ hx 
        change x ∈ Z.base_set i at hx 
        dsimp only 
        rw [Z.coord_change_comp, Z.coord_change_self]
        ·
          exact Z.mem_base_set_at _
        ·
          simp only [hx, mem_inter_eq, and_selfₓ, mem_base_set_at],
    right_inv' :=
      by 
        rintro ⟨x, v⟩ hx 
        simp only [prod_mk_mem_set_prod_eq, and_trueₓ, mem_univ] at hx 
        rw [Z.coord_change_comp, Z.coord_change_self]
        ·
          exact hx
        ·
          simp only [hx, mem_inter_eq, and_selfₓ, mem_base_set_at] }

variable(i : ι)

theorem mem_local_triv_as_local_equiv_source (p : Z.total_space) :
  p ∈ (Z.local_triv_as_local_equiv i).Source ↔ p.1 ∈ Z.base_set i :=
  Iff.rfl

theorem mem_local_triv_as_local_equiv_target (p : B × F) :
  p ∈ (Z.local_triv_as_local_equiv i).Target ↔ p.1 ∈ Z.base_set i :=
  by 
    erw [mem_prod]
    simp only [and_trueₓ, mem_univ]

theorem local_triv_as_local_equiv_apply (p : Z.total_space) :
  (Z.local_triv_as_local_equiv i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ :=
  rfl

/-- The composition of two local trivializations is the trivialization change Z.triv_change i j. -/
theorem local_triv_as_local_equiv_trans (i j : ι) :
  (Z.local_triv_as_local_equiv i).symm.trans (Z.local_triv_as_local_equiv j) ≈ (Z.triv_change i j).toLocalEquiv :=
  by 
    split 
    ·
      ext x 
      simp' only [mem_local_triv_as_local_equiv_target] with mfld_simps 
      rfl
    ·
      rintro ⟨x, v⟩ hx 
      simp only [triv_change, local_triv_as_local_equiv, LocalEquiv.symm, true_andₓ, Prod.mk.inj_iffₓ,
        prod_mk_mem_set_prod_eq, LocalEquiv.trans_source, mem_inter_eq, and_trueₓ, mem_preimage, proj, mem_univ,
        LocalEquiv.coe_mk, eq_self_iff_true, LocalEquiv.coe_trans, Bundle.proj] at hx⊢
      simp only [Z.coord_change_comp, hx, mem_inter_eq, and_selfₓ, mem_base_set_at]

variable(ι)

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : TopologicalSpace (Bundle.TotalSpace Z.fiber) :=
  TopologicalSpace.generateFrom$
    ⋃(i : ι)(s : Set (B × F))(s_open : IsOpen s),
      {(Z.local_triv_as_local_equiv i).Source ∩ Z.local_triv_as_local_equiv i ⁻¹' s}

variable{ι}

theorem open_source' (i : ι) : IsOpen (Z.local_triv_as_local_equiv i).Source :=
  by 
    apply TopologicalSpace.GenerateOpen.basic 
    simp only [exists_prop, mem_Union, mem_singleton_iff]
    refine' ⟨i, Set.Prod (Z.base_set i) univ, (Z.is_open_base_set i).Prod is_open_univ, _⟩
    ext p 
    simp only [local_triv_as_local_equiv_apply, prod_mk_mem_set_prod_eq, mem_inter_eq, and_selfₓ,
      mem_local_triv_as_local_equiv_source, and_trueₓ, mem_univ, mem_preimage]

open TopologicalFiberBundle

-- error in Topology.FiberBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : ι) : trivialization F Z.proj :=
{ base_set := Z.base_set i,
  open_base_set := Z.is_open_base_set i,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ p hp, by { simp [] [] ["only"] [] ["with", ident mfld_simps] [],
    refl },
  open_source := Z.open_source' i,
  open_target := (Z.is_open_base_set i).prod is_open_univ,
  continuous_to_fun := begin
    rw [expr continuous_on_open_iff (Z.open_source' i)] [],
    assume [binders (s s_open)],
    apply [expr topological_space.generate_open.basic],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_Union, ",", expr mem_singleton_iff, "]"] [] [],
    exact [expr ⟨i, s, s_open, rfl⟩]
  end,
  continuous_inv_fun := begin
    apply [expr continuous_on_open_of_generate_from ((Z.is_open_base_set i).prod is_open_univ)],
    assume [binders (t ht)],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_Union, ",", expr mem_singleton_iff, "]"] [] ["at", ident ht],
    obtain ["⟨", ident j, ",", ident s, ",", ident s_open, ",", ident ts, "⟩", ":", expr «expr∃ , »((j
       s), «expr ∧ »(is_open s, «expr = »(t, «expr ∩ »((local_triv_as_local_equiv Z j).source, «expr ⁻¹' »(local_triv_as_local_equiv Z j, s))))), ":=", expr ht],
    rw [expr ts] [],
    simp [] [] ["only"] ["[", expr local_equiv.right_inv, ",", expr preimage_inter, ",", expr local_equiv.left_inv, "]"] [] [],
    let [ident e] [] [":=", expr Z.local_triv_as_local_equiv i],
    let [ident e'] [] [":=", expr Z.local_triv_as_local_equiv j],
    let [ident f] [] [":=", expr e.symm.trans e'],
    have [] [":", expr is_open «expr ∩ »(f.source, «expr ⁻¹' »(f, s))] [],
    { rw ["[", expr (Z.local_triv_as_local_equiv_trans i j).source_inter_preimage_eq, "]"] [],
      exact [expr (continuous_on_open_iff (Z.triv_change i j).open_source).1 (Z.triv_change i j).continuous_on _ s_open] },
    convert [] [expr this] ["using", 1],
    dsimp [] ["[", expr local_equiv.trans_source, "]"] [] [],
    rw ["[", "<-", expr preimage_comp, ",", expr inter_assoc, "]"] [],
    refl
  end,
  to_local_equiv := Z.local_triv_as_local_equiv i }

/-- A topological fiber bundle constructed from core is indeed a topological fiber bundle. -/
protected theorem IsTopologicalFiberBundle : IsTopologicalFiberBundle F Z.proj :=
  fun x => ⟨Z.local_triv (Z.index_at x), Z.mem_base_set_at x⟩

/-- The projection on the base of a topological bundle created from core is continuous -/
theorem continuous_proj : Continuous Z.proj :=
  Z.is_topological_fiber_bundle.continuous_proj

/-- The projection on the base of a topological bundle created from core is an open map -/
theorem is_open_map_proj : IsOpenMap Z.proj :=
  Z.is_topological_fiber_bundle.is_open_map_proj

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : trivialization F Z.proj :=
  Z.local_triv (Z.index_at b)

@[simp, mfld_simps]
theorem local_triv_at_def (b : B) : Z.local_triv (Z.index_at b) = Z.local_triv_at b :=
  rfl

-- error in Topology.FiberBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If an element of `F` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is continuous. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
theorem continuous_const_section
(v : F)
(h : ∀
 i
 j, ∀
 x «expr ∈ » «expr ∩ »(Z.base_set i, Z.base_set j), «expr = »(Z.coord_change i j x v, v)) : continuous (show B → Z.total_space, from λ
 x, ⟨x, v⟩) :=
begin
  apply [expr continuous_iff_continuous_at.2 (λ x, _)],
  have [ident A] [":", expr «expr ∈ »(Z.base_set (Z.index_at x), expr𝓝() x)] [":=", expr is_open.mem_nhds (Z.is_open_base_set (Z.index_at x)) (Z.mem_base_set_at x)],
  apply [expr ((Z.local_triv_at x).to_local_homeomorph.continuous_at_iff_continuous_at_comp_left _).2],
  { simp [] [] ["only"] ["[", expr («expr ∘ »), "]"] ["with", ident mfld_simps] [],
    apply [expr continuous_at_id.prod],
    have [] [":", expr continuous_on (λ y : B, v) (Z.base_set (Z.index_at x))] [":=", expr continuous_on_const],
    apply [expr (this.congr _).continuous_at A],
    assume [binders (y hy)],
    simp [] [] ["only"] ["[", expr h, ",", expr hy, ",", expr mem_base_set_at, "]"] ["with", ident mfld_simps] [] },
  { exact [expr A] }
end

@[simp, mfld_simps]
theorem local_triv_as_local_equiv_coe : «expr⇑ » (Z.local_triv_as_local_equiv i) = Z.local_triv i :=
  rfl

@[simp, mfld_simps]
theorem local_triv_as_local_equiv_source : (Z.local_triv_as_local_equiv i).Source = (Z.local_triv i).Source :=
  rfl

@[simp, mfld_simps]
theorem local_triv_as_local_equiv_target : (Z.local_triv_as_local_equiv i).Target = (Z.local_triv i).Target :=
  rfl

@[simp, mfld_simps]
theorem local_triv_as_local_equiv_symm : (Z.local_triv_as_local_equiv i).symm = (Z.local_triv i).toLocalEquiv.symm :=
  rfl

@[simp, mfld_simps]
theorem base_set_at : Z.base_set i = (Z.local_triv i).BaseSet :=
  rfl

@[simp, mfld_simps]
theorem local_triv_apply (p : Z.total_space) : (Z.local_triv i) p = ⟨p.1, Z.coord_change (Z.index_at p.1) i p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem mem_local_triv_source (p : Z.total_space) : p ∈ (Z.local_triv i).Source ↔ p.1 ∈ (Z.local_triv i).BaseSet :=
  Iff.rfl

@[simp, mfld_simps]
theorem mem_local_triv_target (p : B × F) : p ∈ (Z.local_triv i).Target ↔ p.1 ∈ (Z.local_triv i).BaseSet :=
  trivialization.mem_target _

@[simp, mfld_simps]
theorem local_triv_symm_fst (p : B × F) :
  (Z.local_triv i).toLocalHomeomorph.symm p = ⟨p.1, Z.coord_change i (Z.index_at p.1) p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem local_triv_at_apply (b : B) (a : F) : (Z.local_triv_at b) ⟨b, a⟩ = ⟨b, a⟩ :=
  by 
    rw [local_triv_at, local_triv_apply, coord_change_self]
    exact Z.mem_base_set_at b

@[simp, mfld_simps]
theorem mem_local_triv_at_base_set (b : B) : b ∈ (Z.local_triv_at b).BaseSet :=
  by 
    rw [local_triv_at, ←base_set_at]
    exact Z.mem_base_set_at b

open Bundle

-- error in Topology.FiberBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inclusion of a fiber into the total space is a continuous map. -/
theorem continuous_total_space_mk (b : B) : continuous (λ a, total_space_mk Z.fiber b a) :=
begin
  rw ["[", expr continuous_iff_le_induced, ",", expr topological_fiber_bundle_core.to_topological_space, "]"] [],
  apply [expr le_induced_generate_from],
  simp [] [] ["only"] ["[", expr total_space_mk, ",", expr mem_Union, ",", expr mem_singleton_iff, ",", expr local_triv_as_local_equiv_source, ",", expr local_triv_as_local_equiv_coe, "]"] [] [],
  rintros [ident s, "⟨", ident i, ",", ident t, ",", ident ht, ",", ident rfl, "⟩"],
  rw ["[", "<-", expr (Z.local_triv i).source_inter_preimage_target_inter t, ",", expr preimage_inter, ",", "<-", expr preimage_comp, ",", expr trivialization.source_eq, "]"] [],
  apply [expr is_open.inter],
  { simp [] [] ["only"] ["[", expr bundle.proj, ",", expr proj, ",", "<-", expr preimage_comp, "]"] [] [],
    by_cases [expr «expr ∈ »(b, (Z.local_triv i).base_set)],
    { rw [expr preimage_const_of_mem h] [],
      exact [expr is_open_univ] },
    { rw [expr preimage_const_of_not_mem h] [],
      exact [expr is_open_empty] } },
  { simp [] [] ["only"] ["[", expr function.comp, ",", expr local_triv_apply, "]"] [] [],
    rw ["[", expr preimage_inter, ",", expr preimage_comp, "]"] [],
    by_cases [expr «expr ∈ »(b, Z.base_set i)],
    { have [ident hc] [":", expr continuous (λ
        x : Z.fiber b, Z.coord_change (Z.index_at b) i b x)] [":=", expr begin
         rw [expr continuous_iff_continuous_on_univ] [],
         refine [expr (Z.coord_change_continuous (Z.index_at b) i).comp (continuous_const.prod_mk continuous_id).continuous_on (by { convert [] [expr subset_univ univ] [],
             exact [expr mk_preimage_prod_right (mem_inter (Z.mem_base_set_at b) h)] })]
       end],
      exact [expr hc.is_open_preimage _ ((continuous.prod.mk b).is_open_preimage _ ((Z.local_triv i).open_target.inter ht))] },
    { rw ["[", expr (Z.local_triv i).target_eq, ",", "<-", expr base_set_at, ",", expr mk_preimage_prod_right_eq_empty h, ",", expr preimage_empty, ",", expr empty_inter, "]"] [],
      exact [expr is_open_empty] } }
end

end TopologicalFiberBundleCore

variable(F){Z : Type _}[TopologicalSpace B][TopologicalSpace F]{proj : Z → B}

open TopologicalFiberBundle

/-- This structure permits to define a fiber bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphism and hence local trivializations. -/
@[nolint has_inhabited_instance]
structure TopologicalFiberPrebundle(proj : Z → B) where 
  pretrivializationAt : B → pretrivialization F proj 
  mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).BaseSet 
  continuous_triv_change :
  ∀ x y : B,
    ContinuousOn (pretrivialization_at x ∘ (pretrivialization_at y).toLocalEquiv.symm)
      ((pretrivialization_at y).Target ∩ (pretrivialization_at y).toLocalEquiv.symm ⁻¹' (pretrivialization_at x).Source)

namespace TopologicalFiberPrebundle

variable{F}(a : TopologicalFiberPrebundle F proj)(x : B)

/-- Topology on the total space that will make the prebundle into a bundle. -/
def total_space_topology (a : TopologicalFiberPrebundle F proj) : TopologicalSpace Z :=
  ⨆x : B, coinduced (a.pretrivialization_at x).setSymm Subtype.topologicalSpace

theorem continuous_symm_pretrivialization_at :
  @ContinuousOn _ _ _ a.total_space_topology (a.pretrivialization_at x).toLocalEquiv.symm
    (a.pretrivialization_at x).Target :=
  by 
    refine'
      id
        fun z H =>
          id
            fun U h =>
              preimage_nhds_within_coinduced' H (a.pretrivialization_at x).open_target (le_def.1 (nhds_mono _) U h)
    exact le_supr _ x

-- error in Topology.FiberBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_open_source_pretrivialization_at : @is_open _ a.total_space_topology (a.pretrivialization_at x).source :=
begin
  letI [] [] [":=", expr a.total_space_topology],
  refine [expr is_open_supr_iff.mpr (λ
    y, is_open_coinduced.mpr (is_open_induced_iff.mpr ⟨(a.pretrivialization_at x).target, (a.pretrivialization_at x).open_target, _⟩))],
  rw ["[", expr pretrivialization.set_symm, ",", expr restrict, ",", expr (a.pretrivialization_at x).target_eq, ",", expr (a.pretrivialization_at x).source_eq, ",", expr preimage_comp, ",", expr subtype.preimage_coe_eq_preimage_coe_iff, ",", expr (a.pretrivialization_at y).target_eq, ",", expr prod_inter_prod, ",", expr inter_univ, ",", expr pretrivialization.preimage_symm_proj_inter, "]"] []
end

-- error in Topology.FiberBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_open_target_pretrivialization_at_inter
(x
 y : B) : is_open «expr ∩ »((a.pretrivialization_at y).to_local_equiv.target, «expr ⁻¹' »((a.pretrivialization_at y).to_local_equiv.symm, (a.pretrivialization_at x).source)) :=
begin
  letI [] [] [":=", expr a.total_space_topology],
  obtain ["⟨", ident u, ",", ident hu1, ",", ident hu2, "⟩", ":=", expr continuous_on_iff'.mp (a.continuous_symm_pretrivialization_at y) (a.pretrivialization_at x).source (a.is_open_source_pretrivialization_at x)],
  rw ["[", expr inter_comm, ",", expr hu2, "]"] [],
  exact [expr hu1.inter (a.pretrivialization_at y).open_target]
end

-- error in Topology.FiberBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Promotion from a `pretrivialization` to a `trivialization`. -/
def trivialization_at
(a : topological_fiber_prebundle F proj)
(x : B) : @trivialization B F Z _ _ a.total_space_topology proj :=
{ open_source := a.is_open_source_pretrivialization_at x,
  continuous_to_fun := begin
    letI [] [] [":=", expr a.total_space_topology],
    refine [expr continuous_on_iff'.mpr (λ
      s
      hs, ⟨«expr ∩ »(«expr ⁻¹' »(a.pretrivialization_at x, s), (a.pretrivialization_at x).source), is_open_supr_iff.mpr (λ
        y, _), by { rw ["[", expr inter_assoc, ",", expr inter_self, "]"] [],
         refl }⟩)],
    rw ["[", expr is_open_coinduced, ",", expr is_open_induced_iff, "]"] [],
    obtain ["⟨", ident u, ",", ident hu1, ",", ident hu2, "⟩", ":=", expr continuous_on_iff'.mp (a.continuous_triv_change x y) s hs],
    have [ident hu3] [] [":=", expr congr_arg (λ
      s, «expr ⁻¹' »(λ x : (a.pretrivialization_at y).target, (x : «expr × »(B, F)), s)) hu2],
    simp [] [] ["only"] ["[", expr subtype.coe_preimage_self, ",", expr preimage_inter, ",", expr univ_inter, "]"] [] ["at", ident hu3],
    refine [expr ⟨«expr ∩ »(«expr ∩ »(u, (a.pretrivialization_at y).to_local_equiv.target), «expr ⁻¹' »((a.pretrivialization_at y).to_local_equiv.symm, (a.pretrivialization_at x).source)), _, by { simp [] [] ["only"] ["[", expr preimage_inter, ",", expr inter_univ, ",", expr subtype.coe_preimage_self, ",", expr hu3.symm, "]"] [] [],
        refl }⟩],
    rw [expr inter_assoc] [],
    exact [expr hu1.inter (a.is_open_target_pretrivialization_at_inter x y)]
  end,
  continuous_inv_fun := a.continuous_symm_pretrivialization_at x,
  ..a.pretrivialization_at x }

theorem IsTopologicalFiberBundle : @IsTopologicalFiberBundle B F Z _ _ a.total_space_topology proj :=
  fun x => ⟨a.trivialization_at x, a.mem_base_pretrivialization_at x⟩

-- error in Topology.FiberBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_proj : @continuous _ _ a.total_space_topology _ proj :=
by { letI [] [] [":=", expr a.total_space_topology],
  exact [expr a.is_topological_fiber_bundle.continuous_proj] }

end TopologicalFiberPrebundle

