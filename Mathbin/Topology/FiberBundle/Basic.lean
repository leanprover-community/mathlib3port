/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Heather Macbeth
-/
import Topology.FiberBundle.Trivialization

#align_import topology.fiber_bundle.basic from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Fiber bundles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Mathematically, a (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on
`B` for which the fibers are all homeomorphic to `F`, such that the local situation around each
point is a direct product.

In our formalism, a fiber bundle is by definition the type
`bundle.total_space F E` where `E : B → Type*` is a function associating to `x : B` the fiber over
`x`. This type `bundle.total_space F E` is a type of pairs `(proj : B, snd : E proj)`.

To have a fiber bundle structure on `bundle.total_space F E`, one should
additionally have the following data:

* `F` should be a topological space;
* There should be a topology on `bundle.total_space F E`, for which the projection to `B` is
a fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological space, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* There should be a distinguished set of bundle trivializations, the "trivialization atlas"
* There should be a choice of bundle trivialization at each point, which belongs to this atlas.

If all these conditions are satisfied, we register the typeclass `fiber_bundle F E`.

It is in general nontrivial to construct a fiber bundle. A way is to start from the knowledge of
how changes of local trivializations act on the fiber. From this, one can construct the total space
of the bundle and its topology by a suitable gluing construction. The main content of this file is
an implementation of this construction: starting from an object of type
`fiber_bundle_core` registering the trivialization changes, one gets the corresponding
fiber bundle and projection.

Similarly we implement the object `fiber_prebundle` which allows to define a topological
fiber bundle from trivializations given as local equivalences with minimum additional properties.

## Main definitions

### Basic definitions

* `fiber_bundle F E` : Structure saying that `E : B → Type*` is a fiber bundle with fiber `F`.

### Construction of a bundle from trivializations

* `bundle.total_space F E` is the type of pairs `(proj : B, snd : E proj)`. We can use the extra
  argument `F` to construct topology on the total space.
* `fiber_bundle_core ι B F` : structure registering how changes of coordinates act
  on the fiber `F` above open subsets of `B`, where local trivializations are indexed by `ι`.

Let `Z : fiber_bundle_core ι B F`. Then we define

* `Z.fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.total_space` : the total space of `Z`, defined as a `Type*` as `bundle.total_space F Z.fiber`
                    with a custom topology.
* `Z.proj`        : projection from `Z.total_space` to `B`. It is continuous.
* `Z.local_triv i`: for `i : ι`, bundle trivialization above the set `Z.base_set i`, which is an
                    open set in `B`.

* `fiber_prebundle F E` : structure registering a cover of prebundle trivializations
  and requiring that the relative transition maps are local homeomorphisms.
* `fiber_prebundle.total_space_topology a` : natural topology of the total space, making
  the prebundle into a bundle.

## Implementation notes

### Data vs mixins

For both fiber and vector bundles, one faces a choice: should the definition state the *existence*
of local trivializations (a propositional typeclass), or specify a fixed atlas of trivializations (a
typeclass containing data)?

In their initial mathlib implementations, both fiber and vector bundles were defined
propositionally. For vector bundles, this turns out to be mathematically wrong: in infinite
dimension, the transition function between two trivializations is not automatically continuous as a
map from the base `B` to the endomorphisms `F →L[R] F` of the fiber (considered with the
operator-norm topology), and so the definition needs to be modified by restricting consideration to
a family of trivializations (constituting the data) which are all mutually-compatible in this sense.
The PRs #13052 and #13175 implemented this change.

There is still the choice about whether to hold this data at the level of fiber bundles or of vector
bundles. As of PR #17505, the data is all held in `fiber_bundle`, with `vector_bundle` a
(propositional) mixin stating fiberwise-linearity.

This allows bundles to carry instances of typeclasses in which the scalar field, `R`, does not
appear as a parameter. Notably, we would like a vector bundle over `R` with fiber `F` over base `B`
to be a `charted_space (B × F)`, with the trivializations providing the charts. This would be a
dangerous instance for typeclass inference, because `R` does not appear as a parameter in
`charted_space (B × F)`. But if the data of the trivializations is held in `fiber_bundle`, then a
fiber bundle with fiber `F` over base `B` can be a `charted_space (B × F)`, and this is safe for
typeclass inference.

We expect that this choice of definition will also streamline constructions of fiber bundles with
similar underlying structure (e.g., the same bundle being both a real and complex vector bundle).

### Core construction

A fiber bundle with fiber `F` over a base `B` is a family of spaces isomorphic to `F`,
indexed by `B`, which is locally trivial in the following sense: there is a covering of `B` by open
sets such that, on each such open set `s`, the bundle is isomorphic to `s × F`.

To construct a fiber bundle formally, the main data is what happens when one changes trivializations
from `s × F` to `s' × F` on `s ∩ s'`: one should get a family of homeomorphisms of `F`, depending
continuously on the base point, satisfying basic compatibility conditions (cocycle property).
Useful classes of bundles can then be specified by requiring that these homeomorphisms of `F`
belong to some subgroup, preserving some structure (the "structure group of the bundle"): then
these structures are inherited by the fibers of the bundle.

Given such trivialization change data (encoded below in a structure called
`fiber_bundle_core`), one can construct the fiber bundle. The intrinsic canonical
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

For this construction of a fiber bundle from a `fiber_bundle_core`, we should thus
choose for each `x` one specific trivialization around it. We include this choice in the definition
of the `fiber_bundle_core`, as it makes some constructions more
functorial and it is a nice way to say that the trivializations cover the whole space `B`.

With this definition, the type of the fiber bundle space constructed from the core data is
`bundle.total_space F (λ b : B, F)`, but the topology is not the product one, in general.

We also take the indexing type (indexing all the trivializations) as a parameter to the fiber bundle
core: it could always be taken as a subtype of all the maps from open subsets of `B` to continuous
maps of `F`, but in practice it will sometimes be something else. For instance, on a manifold, one
will use the set of charts as a good parameterization for the trivializations of the tangent bundle.
Or for the pullback of a `fiber_bundle_core`, the indexing type will be the same as
for the initial bundle.

## Tags
Fiber bundle, topological bundle, structure group
-/


variable {ι B F X : Type _} [TopologicalSpace X]

open TopologicalSpace Filter Set Bundle

open scoped Topology Classical Bundle

attribute [mfld_simps] total_space.coe_proj total_space.coe_snd coe_snd_map_apply coe_snd_map_smul
  total_space.mk_cast

/-! ### General definition of fiber bundles -/


section FiberBundle

variable (F) [TopologicalSpace B] [TopologicalSpace F] (E : B → Type _)
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]

#print FiberBundle /-
/- ./././Mathport/Syntax/Translate/Command.lean:404:30: infer kinds are unsupported in Lean 4: #[`totalSpace_mk_inducing] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:404:30: infer kinds are unsupported in Lean 4: #[`trivializationAtlas] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:404:30: infer kinds are unsupported in Lean 4: #[`trivializationAt] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:404:30: infer kinds are unsupported in Lean 4: #[`mem_baseSet_trivializationAt] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:404:30: infer kinds are unsupported in Lean 4: #[`trivialization_mem_atlas] [] -/
/-- A (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on `B`
for which the fibers are all homeomorphic to `F`, such that the local situation around each point
is a direct product. -/
class FiberBundle where
  totalSpace_mk_inducing : ∀ b : B, Inducing (@TotalSpace.mk B F E b)
  trivializationAtlas : Set (Trivialization F (π F E))
  trivializationAt : B → Trivialization F (π F E)
  mem_baseSet_trivializationAt : ∀ b : B, b ∈ (trivialization_at b).baseSet
  trivialization_mem_atlas : ∀ b : B, trivialization_at b ∈ trivialization_atlas
#align fiber_bundle FiberBundle
-/

export FiberBundle ()

variable {F E}

#print MemTrivializationAtlas /-
/-- Given a type `E` equipped with a fiber bundle structure, this is a `Prop` typeclass
for trivializations of `E`, expressing that a trivialization is in the designated atlas for the
bundle.  This is needed because lemmas about the linearity of trivializations or the continuity (as
functions to `F →L[R] F`, where `F` is the model fiber) of the transition functions are only
expected to hold for trivializations in the designated atlas. -/
@[mk_iff]
class MemTrivializationAtlas [FiberBundle F E] (e : Trivialization F (π F E)) : Prop where
  out : e ∈ trivializationAtlas F E
#align mem_trivialization_atlas MemTrivializationAtlas
-/

instance [FiberBundle F E] (b : B) : MemTrivializationAtlas (trivializationAt F E b)
    where out := trivialization_mem_atlas F E b

namespace FiberBundle

variable (F) {E} [FiberBundle F E]

#print FiberBundle.map_proj_nhds /-
theorem map_proj_nhds (x : TotalSpace F E) : map (π F E) (𝓝 x) = 𝓝 x.proj :=
  (trivializationAt F E x.proj).map_proj_nhds <|
    (trivializationAt F E x.proj).mem_source.2 <| mem_baseSet_trivializationAt F E x.proj
#align fiber_bundle.map_proj_nhds FiberBundle.map_proj_nhds
-/

variable (E)

#print FiberBundle.continuous_proj /-
/-- The projection from a fiber bundle to its base is continuous. -/
@[continuity]
theorem continuous_proj : Continuous (π F E) :=
  continuous_iff_continuousAt.2 fun x => (map_proj_nhds F x).le
#align fiber_bundle.continuous_proj FiberBundle.continuous_proj
-/

#print FiberBundle.isOpenMap_proj /-
/-- The projection from a fiber bundle to its base is an open map. -/
theorem isOpenMap_proj : IsOpenMap (π F E) :=
  IsOpenMap.of_nhds_le fun x => (map_proj_nhds F x).ge
#align fiber_bundle.is_open_map_proj FiberBundle.isOpenMap_proj
-/

#print FiberBundle.surjective_proj /-
/-- The projection from a fiber bundle with a nonempty fiber to its base is a surjective
map. -/
theorem surjective_proj [Nonempty F] : Function.Surjective (π F E) := fun b =>
  let ⟨p, _, hpb⟩ :=
    (trivializationAt F E b).proj_surjOn_baseSet (mem_baseSet_trivializationAt F E b)
  ⟨p, hpb⟩
#align fiber_bundle.surjective_proj FiberBundle.surjective_proj
-/

#print FiberBundle.quotientMap_proj /-
/-- The projection from a fiber bundle with a nonempty fiber to its base is a quotient
map. -/
theorem quotientMap_proj [Nonempty F] : QuotientMap (π F E) :=
  (isOpenMap_proj F E).to_quotientMap (continuous_proj F E) (surjective_proj F E)
#align fiber_bundle.quotient_map_proj FiberBundle.quotientMap_proj
-/

#print FiberBundle.continuous_totalSpaceMk /-
theorem continuous_totalSpaceMk (x : B) : Continuous (@TotalSpace.mk B F E x) :=
  (totalSpace_mk_inducing F E x).Continuous
#align fiber_bundle.continuous_total_space_mk FiberBundle.continuous_totalSpaceMk
-/

variable {E F}

#print FiberBundle.mem_trivializationAt_proj_source /-
@[simp, mfld_simps]
theorem mem_trivializationAt_proj_source {x : TotalSpace F E} :
    x ∈ (trivializationAt F E x.proj).source :=
  (Trivialization.mem_source _).mpr <| mem_baseSet_trivializationAt F E x.proj
#align fiber_bundle.mem_trivialization_at_proj_source FiberBundle.mem_trivializationAt_proj_source
-/

#print FiberBundle.trivializationAt_proj_fst /-
@[simp, mfld_simps]
theorem trivializationAt_proj_fst {x : TotalSpace F E} :
    ((trivializationAt F E x.proj) x).1 = x.proj :=
  Trivialization.coe_fst' _ <| mem_baseSet_trivializationAt F E x.proj
#align fiber_bundle.trivialization_at_proj_fst FiberBundle.trivializationAt_proj_fst
-/

variable (F)

open Trivialization

#print FiberBundle.continuousWithinAt_totalSpace /-
/-- Characterization of continuous functions (at a point, within a set) into a fiber bundle. -/
theorem continuousWithinAt_totalSpace (f : X → TotalSpace F E) {s : Set X} {x₀ : X} :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x => (f x).proj) s x₀ ∧
        ContinuousWithinAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) s x₀ :=
  by
  refine' (and_iff_right_iff_imp.2 fun hf => _).symm.trans (and_congr_right fun hf => _)
  · refine' (continuous_proj F E).ContinuousWithinAt.comp hf (maps_to_image f s)
  have h1 : (fun x => (f x).proj) ⁻¹' (trivialization_at F E (f x₀).proj).baseSet ∈ 𝓝[s] x₀ :=
    hf.preimage_mem_nhds_within ((open_base_set _).mem_nhds (mem_base_set_trivialization_at F E _))
  have h2 : ContinuousWithinAt (fun x => (trivialization_at F E (f x₀).proj (f x)).1) s x₀ :=
    by
    refine'
      hf.congr_of_eventually_eq (eventually_of_mem h1 fun x hx => _) trivialization_at_proj_fst
    rw [coe_fst']
    exact hx
  rw [(trivialization_at F E (f x₀).proj).continuousWithinAt_iff_continuousWithinAt_comp_left]
  · simp_rw [continuousWithinAt_prod_iff, Function.comp, Trivialization.coe_coe, h2, true_and_iff]
  · apply mem_trivialization_at_proj_source
  · rwa [source_eq, preimage_preimage]
#align fiber_bundle.continuous_within_at_total_space FiberBundle.continuousWithinAt_totalSpace
-/

#print FiberBundle.continuousAt_totalSpace /-
/-- Characterization of continuous functions (at a point) into a fiber bundle. -/
theorem continuousAt_totalSpace (f : X → TotalSpace F E) {x₀ : X} :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x => (f x).proj) x₀ ∧
        ContinuousAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) x₀ :=
  by simp_rw [← continuousWithinAt_univ]; exact continuous_within_at_total_space F f
#align fiber_bundle.continuous_at_total_space FiberBundle.continuousAt_totalSpace
-/

end FiberBundle

variable (F E)

#print FiberBundle.exists_trivialization_Icc_subset /-
/-- If `E` is a fiber bundle over a conditionally complete linear order,
then it is trivial over any closed interval. -/
theorem FiberBundle.exists_trivialization_Icc_subset [ConditionallyCompleteLinearOrder B]
    [OrderTopology B] [FiberBundle F E] (a b : B) :
    ∃ e : Trivialization F (π F E), Icc a b ⊆ e.baseSet := by
  classical
  obtain ⟨ea, hea⟩ : ∃ ea : Trivialization F (π F E), a ∈ ea.baseSet :=
    ⟨trivialization_at F E a, mem_base_set_trivialization_at F E a⟩
  -- If `a < b`, then `[a, b] = ∅`, and the statement is trivial
    cases' le_or_lt a b with hab hab <;>
    [skip; exact ⟨ea, by simp [*]⟩]
  /- Let `s` be the set of points `x ∈ [a, b]` such that `E` is trivializable over `[a, x]`.
    We need to show that `b ∈ s`. Let `c = Sup s`. We will show that `c ∈ s` and `c = b`. -/
  set s : Set B := {x ∈ Icc a b | ∃ e : Trivialization F (π F E), Icc a x ⊆ e.baseSet}
  have ha : a ∈ s := ⟨left_mem_Icc.2 hab, ea, by simp [hea]⟩
  have sne : s.nonempty := ⟨a, ha⟩
  have hsb : b ∈ upperBounds s := fun x hx => hx.1.2
  have sbd : BddAbove s := ⟨b, hsb⟩
  set c := Sup s
  have hsc : IsLUB s c := isLUB_csSup sne sbd
  have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  obtain ⟨-, ec : Trivialization F (π F E), hec : Icc a c ⊆ ec.base_set⟩ : c ∈ s :=
    by
    cases' hc.1.eq_or_lt with heq hlt; · rwa [← HEq]
    refine' ⟨hc, _⟩
    /- In order to show that `c ∈ s`, consider a trivialization `ec` of `proj` over a neighborhood
        of `c`. Its base set includes `(c', c]` for some `c' ∈ [a, c)`. -/
    obtain ⟨ec, hc⟩ : ∃ ec : Trivialization F (π F E), c ∈ ec.baseSet :=
      ⟨trivialization_at F E c, mem_base_set_trivialization_at F E c⟩
    obtain ⟨c', hc', hc'e⟩ : ∃ c' ∈ Ico a c, Ioc c' c ⊆ ec.base_set :=
      (mem_nhdsWithin_Iic_iff_exists_mem_Ico_Ioc_subset hlt).1
        (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_base_set hc)
    /- Since `c' < c = Sup s`, there exists `d ∈ s ∩ (c', c]`. Let `ead` be a trivialization of
        `proj` over `[a, d]`. Then we can glue `ead` and `ec` into a trivialization over `[a, c]`. -/
    obtain ⟨d, ⟨hdab, ead, had⟩, hd⟩ : ∃ d ∈ s, d ∈ Ioc c' c := hsc.exists_between hc'.2
    refine' ⟨ead.piecewise_le ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 _⟩
    refine' ⟨fun x hx => had ⟨hx.1.1, hx.2⟩, fun x hx => hc'e ⟨hd.1.trans (not_le.1 hx.2), hx.1.2⟩⟩
  /- So, `c ∈ s`. Let `ec` be a trivialization of `proj` over `[a, c]`.  If `c = b`, then we are
    done. Otherwise we show that `proj` can be trivialized over a larger interval `[a, d]`,
    `d ∈ (c, b]`, hence `c` is not an upper bound of `s`. -/
  cases' hc.2.eq_or_lt with heq hlt
  · exact ⟨ec, HEq ▸ hec⟩
  rsuffices ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, ∃ e : Trivialization F (π F E), Icc a d ⊆ e.baseSet
  · exact ((hsc.1 ⟨⟨hc.1.trans hdcb.1.le, hdcb.2⟩, hd⟩).not_lt hdcb.1).elim
  /- Since the base set of `ec` is open, it includes `[c, d)` (hence, `[a, d)`) for some
    `d ∈ (c, b]`. -/
  obtain ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, Ico c d ⊆ ec.base_set :=
    (mem_nhdsWithin_Ici_iff_exists_mem_Ioc_Ico_subset hlt).1
      (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_base_set (hec ⟨hc.1, le_rfl⟩))
  have had : Ico a d ⊆ ec.base_set := Ico_subset_Icc_union_Ico.trans (union_subset hec hd)
  by_cases he : Disjoint (Iio d) (Ioi c)
  · /- If `(c, d) = ∅`, then let `ed` be a trivialization of `proj` over a neighborhood of `d`.
        Then the disjoint union of `ec` restricted to `(-∞, d)` and `ed` restricted to `(c, ∞)` is
        a trivialization over `[a, d]`. -/
    obtain ⟨ed, hed⟩ : ∃ ed : Trivialization F (π F E), d ∈ ed.baseSet :=
      ⟨trivialization_at F E d, mem_base_set_trivialization_at F E d⟩
    refine'
      ⟨d, hdcb,
        (ec.restr_open (Iio d) isOpen_Iio).disjointUnion (ed.restr_open (Ioi c) isOpen_Ioi)
          (he.mono (inter_subset_right _ _) (inter_subset_right _ _)),
        fun x hx => _⟩
    rcases hx.2.eq_or_lt with (rfl | hxd)
    exacts [Or.inr ⟨hed, hdcb.1⟩, Or.inl ⟨had ⟨hx.1, hxd⟩, hxd⟩]
  · /- If `(c, d)` is nonempty, then take `d' ∈ (c, d)`. Since the base set of `ec` includes
        `[a, d)`, it includes `[a, d'] ⊆ [a, d)` as well. -/
    rw [disjoint_left] at he ; push_neg at he ; rcases he with ⟨d', hdd' : d' < d, hd'c⟩
    exact ⟨d', ⟨hd'c, hdd'.le.trans hdcb.2⟩, ec, (Icc_subset_Ico_right hdd').trans had⟩
#align fiber_bundle.exists_trivialization_Icc_subset FiberBundle.exists_trivialization_Icc_subset
-/

end FiberBundle

/-! ### Core construction for constructing fiber bundles -/


#print FiberBundleCore /-
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Core data defining a locally trivial bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type `ι`, on open subsets `base_set i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coord_change i j` from
`base_set i ∩ base_set j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(base_set i ∩ base_set j) × F` to avoid the topology on the
space of continuous maps on `F`. -/
@[nolint has_nonempty_instance]
structure FiberBundleCore (ι : Type _) (B : Type _) [TopologicalSpace B] (F : Type _)
    [TopologicalSpace F] where
  baseSet : ι → Set B
  isOpen_baseSet : ∀ i, IsOpen (base_set i)
  indexAt : B → ι
  mem_baseSet_at : ∀ x, x ∈ base_set (index_at x)
  coordChange : ι → ι → B → F → F
  coordChange_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v
  continuousOn_coordChange :
    ∀ i j,
      ContinuousOn (fun p : B × F => coord_change i j p.1 p.2) ((base_set i ∩ base_set j) ×ˢ univ)
  coordChange_comp :
    ∀ i j k,
      ∀ x ∈ base_set i ∩ base_set j ∩ base_set k,
        ∀ v, (coord_change j k x) (coord_change i j x v) = coord_change i k x v
#align fiber_bundle_core FiberBundleCore
-/

namespace FiberBundleCore

variable [TopologicalSpace B] [TopologicalSpace F] (Z : FiberBundleCore ι B F)

#print FiberBundleCore.Index /-
/-- The index set of a fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_nonempty_instance]
def Index :=
  ι
#align fiber_bundle_core.index FiberBundleCore.Index
-/

#print FiberBundleCore.Base /-
/-- The base space of a fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments, reducible]
def Base :=
  B
#align fiber_bundle_core.base FiberBundleCore.Base
-/

#print FiberBundleCore.Fiber /-
/-- The fiber of a fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_nonempty_instance]
def Fiber (x : B) :=
  F
#align fiber_bundle_core.fiber FiberBundleCore.Fiber
-/

#print FiberBundleCore.topologicalSpaceFiber /-
instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) :=
  ‹TopologicalSpace F›
#align fiber_bundle_core.topological_space_fiber FiberBundleCore.topologicalSpaceFiber
-/

#print FiberBundleCore.TotalSpace /-
/-- The total space of the fiber bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber` -/
@[nolint unused_arguments, reducible]
def TotalSpace :=
  Bundle.TotalSpace F Z.Fiber
#align fiber_bundle_core.total_space FiberBundleCore.TotalSpace
-/

#print FiberBundleCore.proj /-
/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
def proj : Z.TotalSpace → B :=
  Bundle.TotalSpace.proj
#align fiber_bundle_core.proj FiberBundleCore.proj
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FiberBundleCore.trivChange /-
/-- Local homeomorphism version of the trivialization change. -/
def trivChange (i j : ι) : PartialHomeomorph (B × F) (B × F)
    where
  source := (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ
  target := (Z.baseSet i ∩ Z.baseSet j) ×ˢ univ
  toFun p := ⟨p.1, Z.coordChange i j p.1 p.2⟩
  invFun p := ⟨p.1, Z.coordChange j i p.1 p.2⟩
  map_source' p hp := by simpa using hp
  map_target' p hp := by simpa using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true_iff, mem_univ] at hx 
    rw [Z.coord_change_comp, Z.coord_change_self]
    · exact hx.1
    · simp [hx]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true_iff, mem_univ] at hx 
    rw [Z.coord_change_comp, Z.coord_change_self]
    · exact hx.2
    · simp [hx]
  open_source := (IsOpen.inter (Z.isOpen_baseSet i) (Z.isOpen_baseSet j)).Prod isOpen_univ
  open_target := (IsOpen.inter (Z.isOpen_baseSet i) (Z.isOpen_baseSet j)).Prod isOpen_univ
  continuous_toFun := ContinuousOn.prod continuous_fst.ContinuousOn (Z.continuousOn_coordChange i j)
  continuous_invFun := by
    simpa [inter_comm] using
      ContinuousOn.prod continuous_fst.continuous_on (Z.continuous_on_coord_change j i)
#align fiber_bundle_core.triv_change FiberBundleCore.trivChange
-/

#print FiberBundleCore.mem_trivChange_source /-
@[simp, mfld_simps]
theorem mem_trivChange_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).source ↔ p.1 ∈ Z.baseSet i ∩ Z.baseSet j := by erw [mem_prod]; simp
#align fiber_bundle_core.mem_triv_change_source FiberBundleCore.mem_trivChange_source
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FiberBundleCore.localTrivAsPartialEquiv /-
/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (base_set i)` and `base_set i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be a local homeomorphism. For now, we only introduce the
local equiv version, denoted with a prime. In further developments, avoid this auxiliary version,
and use `Z.local_triv` instead.
-/
def localTrivAsPartialEquiv (i : ι) : PartialEquiv Z.TotalSpace (B × F)
    where
  source := Z.proj ⁻¹' Z.baseSet i
  target := Z.baseSet i ×ˢ univ
  invFun p := ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩
  toFun p := ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩
  map_source' p hp := by
    simpa only [Set.mem_preimage, and_true_iff, Set.mem_univ, Set.prod_mk_mem_set_prod_eq] using hp
  map_target' p hp := by
    simpa only [Set.mem_preimage, and_true_iff, Set.mem_univ, Set.mem_prod] using hp
  left_inv' := by
    rintro ⟨x, v⟩ hx
    change x ∈ Z.base_set i at hx 
    dsimp only
    rw [Z.coord_change_comp, Z.coord_change_self]
    · exact Z.mem_base_set_at _
    · simp only [hx, mem_inter_iff, and_self_iff, mem_base_set_at]
  right_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [prod_mk_mem_set_prod_eq, and_true_iff, mem_univ] at hx 
    rw [Z.coord_change_comp, Z.coord_change_self]
    · exact hx
    · simp only [hx, mem_inter_iff, and_self_iff, mem_base_set_at]
#align fiber_bundle_core.local_triv_as_local_equiv FiberBundleCore.localTrivAsPartialEquiv
-/

variable (i : ι)

#print FiberBundleCore.mem_localTrivAsPartialEquiv_source /-
theorem mem_localTrivAsPartialEquiv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTrivAsPartialEquiv i).source ↔ p.1 ∈ Z.baseSet i :=
  Iff.rfl
#align fiber_bundle_core.mem_local_triv_as_local_equiv_source FiberBundleCore.mem_localTrivAsPartialEquiv_source
-/

#print FiberBundleCore.mem_localTrivAsPartialEquiv_target /-
theorem mem_localTrivAsPartialEquiv_target (p : B × F) :
    p ∈ (Z.localTrivAsPartialEquiv i).target ↔ p.1 ∈ Z.baseSet i := by erw [mem_prod];
  simp only [and_true_iff, mem_univ]
#align fiber_bundle_core.mem_local_triv_as_local_equiv_target FiberBundleCore.mem_localTrivAsPartialEquiv_target
-/

#print FiberBundleCore.localTrivAsPartialEquiv_apply /-
theorem localTrivAsPartialEquiv_apply (p : Z.TotalSpace) :
    (Z.localTrivAsPartialEquiv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl
#align fiber_bundle_core.local_triv_as_local_equiv_apply FiberBundleCore.localTrivAsPartialEquiv_apply
-/

#print FiberBundleCore.localTrivAsPartialEquiv_trans /-
/-- The composition of two local trivializations is the trivialization change Z.triv_change i j. -/
theorem localTrivAsPartialEquiv_trans (i j : ι) :
    (Z.localTrivAsPartialEquiv i).symm.trans (Z.localTrivAsPartialEquiv j) ≈
      (Z.trivChange i j).toPartialEquiv :=
  by
  constructor
  · ext x; simp only [mem_local_triv_as_local_equiv_target, mfld_simps]; rfl
  · rintro ⟨x, v⟩ hx
    simp only [triv_change, local_triv_as_local_equiv, PartialEquiv.symm, true_and_iff,
      Prod.mk.inj_iff, prod_mk_mem_set_prod_eq, PartialEquiv.trans_source, mem_inter_iff,
      and_true_iff, mem_preimage, proj, mem_univ, PartialEquiv.coe_mk, eq_self_iff_true,
      PartialEquiv.coe_trans, total_space.proj] at hx ⊢
    simp only [Z.coord_change_comp, hx, mem_inter_iff, and_self_iff, mem_base_set_at]
#align fiber_bundle_core.local_triv_as_local_equiv_trans FiberBundleCore.localTrivAsPartialEquiv_trans
-/

#print FiberBundleCore.toTopologicalSpace /-
/-- Topological structure on the total space of a fiber bundle created from core, designed so
that all the local trivialization are continuous. -/
instance toTopologicalSpace : TopologicalSpace Z.TotalSpace :=
  TopologicalSpace.generateFrom <|
    ⋃ (i : ι) (s : Set (B × F)) (s_open : IsOpen s), {(Z i).source ∩ Z i ⁻¹' s}
#align fiber_bundle_core.to_topological_space FiberBundleCore.toTopologicalSpace
-/

variable (b : B) (a : F)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FiberBundleCore.open_source' /-
theorem open_source' (i : ι) : IsOpen (Z.localTrivAsPartialEquiv i).source :=
  by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_Union, mem_singleton_iff]
  refine' ⟨i, Z.base_set i ×ˢ univ, (Z.is_open_base_set i).Prod isOpen_univ, _⟩
  ext p
  simp only [local_triv_as_local_equiv_apply, prod_mk_mem_set_prod_eq, mem_inter_iff, and_self_iff,
    mem_local_triv_as_local_equiv_source, and_true_iff, mem_univ, mem_preimage]
#align fiber_bundle_core.open_source' FiberBundleCore.open_source'
-/

#print FiberBundleCore.localTriv /-
/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def localTriv (i : ι) : Trivialization F Z.proj
    where
  baseSet := Z.baseSet i
  open_baseSet := Z.isOpen_baseSet i
  source_eq := rfl
  target_eq := rfl
  proj_toFun p hp := by simp only [mfld_simps]; rfl
  open_source := Z.open_source' i
  open_target := (Z.isOpen_baseSet i).Prod isOpen_univ
  continuous_toFun := by
    rw [continuousOn_open_iff (Z.open_source' i)]
    intro s s_open
    apply TopologicalSpace.GenerateOpen.basic
    simp only [exists_prop, mem_Union, mem_singleton_iff]
    exact ⟨i, s, s_open, rfl⟩
  continuous_invFun :=
    by
    apply continuousOn_isOpen_of_generateFrom ((Z.is_open_base_set i).Prod isOpen_univ)
    intro t ht
    simp only [exists_prop, mem_Union, mem_singleton_iff] at ht 
    obtain ⟨j, s, s_open, ts⟩ :
      ∃ j s,
        IsOpen s ∧
          t = (local_triv_as_local_equiv Z j).source ∩ local_triv_as_local_equiv Z j ⁻¹' s :=
      ht
    rw [ts]
    simp only [PartialEquiv.right_inv, preimage_inter, PartialEquiv.left_inv]
    let e := Z.local_triv_as_local_equiv i
    let e' := Z.local_triv_as_local_equiv j
    let f := e.symm.trans e'
    have : IsOpen (f.source ∩ f ⁻¹' s) :=
      by
      rw [(Z.local_triv_as_local_equiv_trans i j).source_inter_preimage_eq]
      exact
        (continuousOn_open_iff (Z.triv_change i j).open_source).1 (Z.triv_change i j).ContinuousOn _
          s_open
    convert this using 1
    dsimp [PartialEquiv.trans_source]
    rw [← preimage_comp, inter_assoc]
    rfl
  toPartialEquiv := Z.localTrivAsPartialEquiv i
#align fiber_bundle_core.local_triv FiberBundleCore.localTriv
-/

#print FiberBundleCore.localTrivAt /-
/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def localTrivAt (b : B) : Trivialization F (π F Z.Fiber) :=
  Z.localTriv (Z.indexAt b)
#align fiber_bundle_core.local_triv_at FiberBundleCore.localTrivAt
-/

#print FiberBundleCore.localTrivAt_def /-
@[simp, mfld_simps]
theorem localTrivAt_def (b : B) : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl
#align fiber_bundle_core.local_triv_at_def FiberBundleCore.localTrivAt_def
-/

#print FiberBundleCore.continuous_const_section /-
/-- If an element of `F` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is continuous. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
theorem continuous_const_section (v : F)
    (h : ∀ i j, ∀ x ∈ Z.baseSet i ∩ Z.baseSet j, Z.coordChange i j x v = v) :
    Continuous (show B → Z.TotalSpace from fun x => ⟨x, v⟩) :=
  by
  apply continuous_iff_continuousAt.2 fun x => _
  have A : Z.base_set (Z.index_at x) ∈ 𝓝 x :=
    IsOpen.mem_nhds (Z.is_open_base_set (Z.index_at x)) (Z.mem_base_set_at x)
  apply ((Z.local_triv_at x).toPartialHomeomorph.continuousAt_iff_continuousAt_comp_left _).2
  · simp only [(· ∘ ·), mfld_simps]
    apply continuous_at_id.prod
    have : ContinuousOn (fun y : B => v) (Z.base_set (Z.index_at x)) := continuousOn_const
    apply (this.congr _).ContinuousAt A
    intro y hy
    simp only [h, hy, mem_base_set_at, mfld_simps]
  · exact A
#align fiber_bundle_core.continuous_const_section FiberBundleCore.continuous_const_section
-/

#print FiberBundleCore.localTrivAsPartialEquiv_coe /-
@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_coe : ⇑(Z.localTrivAsPartialEquiv i) = Z.localTriv i :=
  rfl
#align fiber_bundle_core.local_triv_as_local_equiv_coe FiberBundleCore.localTrivAsPartialEquiv_coe
-/

#print FiberBundleCore.localTrivAsPartialEquiv_source /-
@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_source :
    (Z.localTrivAsPartialEquiv i).source = (Z.localTriv i).source :=
  rfl
#align fiber_bundle_core.local_triv_as_local_equiv_source FiberBundleCore.localTrivAsPartialEquiv_source
-/

#print FiberBundleCore.localTrivAsPartialEquiv_target /-
@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_target :
    (Z.localTrivAsPartialEquiv i).target = (Z.localTriv i).target :=
  rfl
#align fiber_bundle_core.local_triv_as_local_equiv_target FiberBundleCore.localTrivAsPartialEquiv_target
-/

#print FiberBundleCore.localTrivAsPartialEquiv_symm /-
@[simp, mfld_simps]
theorem localTrivAsPartialEquiv_symm :
    (Z.localTrivAsPartialEquiv i).symm = (Z.localTriv i).toPartialEquiv.symm :=
  rfl
#align fiber_bundle_core.local_triv_as_local_equiv_symm FiberBundleCore.localTrivAsPartialEquiv_symm
-/

#print FiberBundleCore.baseSet_at /-
@[simp, mfld_simps]
theorem baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet :=
  rfl
#align fiber_bundle_core.base_set_at FiberBundleCore.baseSet_at
-/

#print FiberBundleCore.localTriv_apply /-
@[simp, mfld_simps]
theorem localTriv_apply (p : Z.TotalSpace) :
    (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl
#align fiber_bundle_core.local_triv_apply FiberBundleCore.localTriv_apply
-/

#print FiberBundleCore.localTrivAt_apply /-
@[simp, mfld_simps]
theorem localTrivAt_apply (p : Z.TotalSpace) : (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩ := by
  rw [local_triv_at, local_triv_apply, coord_change_self]; exact Z.mem_base_set_at p.1
#align fiber_bundle_core.local_triv_at_apply FiberBundleCore.localTrivAt_apply
-/

#print FiberBundleCore.localTrivAt_apply_mk /-
@[simp, mfld_simps]
theorem localTrivAt_apply_mk (b : B) (a : F) : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.localTrivAt_apply _
#align fiber_bundle_core.local_triv_at_apply_mk FiberBundleCore.localTrivAt_apply_mk
-/

#print FiberBundleCore.mem_localTriv_source /-
@[simp, mfld_simps]
theorem mem_localTriv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTriv i).source ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Iff.rfl
#align fiber_bundle_core.mem_local_triv_source FiberBundleCore.mem_localTriv_source
-/

#print FiberBundleCore.mem_localTrivAt_source /-
@[simp, mfld_simps]
theorem mem_localTrivAt_source (p : Z.TotalSpace) (b : B) :
    p ∈ (Z.localTrivAt b).source ↔ p.1 ∈ (Z.localTrivAt b).baseSet :=
  Iff.rfl
#align fiber_bundle_core.mem_local_triv_at_source FiberBundleCore.mem_localTrivAt_source
-/

/- warning: fiber_bundle_core.mem_source_at clashes with fiber_bundle_core.mem_local_triv_at_source -> FiberBundleCore.mem_localTrivAt_source
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.mem_source_at FiberBundleCore.mem_localTrivAt_sourceₓ'. -/
#print FiberBundleCore.mem_localTrivAt_source /-
@[simp, mfld_simps]
theorem mem_localTrivAt_source : (⟨b, a⟩ : Z.TotalSpace) ∈ (Z.localTrivAt b).source := by
  rw [local_triv_at, mem_local_triv_source]; exact Z.mem_base_set_at b
#align fiber_bundle_core.mem_source_at FiberBundleCore.mem_localTrivAt_source
-/

#print FiberBundleCore.mem_localTriv_target /-
@[simp, mfld_simps]
theorem mem_localTriv_target (p : B × F) :
    p ∈ (Z.localTriv i).target ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Trivialization.mem_target _
#align fiber_bundle_core.mem_local_triv_target FiberBundleCore.mem_localTriv_target
-/

#print FiberBundleCore.mem_localTrivAt_target /-
@[simp, mfld_simps]
theorem mem_localTrivAt_target (p : B × F) (b : B) :
    p ∈ (Z.localTrivAt b).target ↔ p.1 ∈ (Z.localTrivAt b).baseSet :=
  Trivialization.mem_target _
#align fiber_bundle_core.mem_local_triv_at_target FiberBundleCore.mem_localTrivAt_target
-/

#print FiberBundleCore.localTriv_symm_apply /-
@[simp, mfld_simps]
theorem localTriv_symm_apply (p : B × F) :
    (Z.localTriv i).toPartialHomeomorph.symm p = ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl
#align fiber_bundle_core.local_triv_symm_apply FiberBundleCore.localTriv_symm_apply
-/

#print FiberBundleCore.mem_localTrivAt_baseSet /-
@[simp, mfld_simps]
theorem mem_localTrivAt_baseSet (b : B) : b ∈ (Z.localTrivAt b).baseSet := by
  rw [local_triv_at, ← base_set_at]; exact Z.mem_base_set_at b
#align fiber_bundle_core.mem_local_triv_at_base_set FiberBundleCore.mem_localTrivAt_baseSet
-/

#print FiberBundleCore.continuous_totalSpaceMk /-
/-- The inclusion of a fiber into the total space is a continuous map. -/
@[continuity]
theorem continuous_totalSpaceMk (b : B) : Continuous (TotalSpace.mk b : Z.Fiber b → Z.TotalSpace) :=
  by
  rw [continuous_iff_le_induced, FiberBundleCore.toTopologicalSpace]
  apply le_induced_generateFrom
  simp only [mem_Union, mem_singleton_iff, local_triv_as_local_equiv_source,
    local_triv_as_local_equiv_coe]
  rintro s ⟨i, t, ht, rfl⟩
  rw [← (Z.local_triv i).source_inter_preimage_target_inter t, preimage_inter, ← preimage_comp,
    Trivialization.source_eq]
  apply IsOpen.inter
  · simp only [total_space.proj, proj, ← preimage_comp]
    by_cases b ∈ (Z.local_triv i).baseSet
    · rw [preimage_const_of_mem h]; exact isOpen_univ
    · rw [preimage_const_of_not_mem h]; exact isOpen_empty
  · simp only [Function.comp, local_triv_apply]
    rw [preimage_inter, preimage_comp]
    by_cases b ∈ Z.base_set i
    · have hc : Continuous fun x : Z.fiber b => (Z.coord_change (Z.index_at b) i b) x :=
        (Z.continuous_on_coord_change (Z.index_at b) i).comp_continuous
          (continuous_const.prod_mk continuous_id) fun x => ⟨⟨Z.mem_base_set_at b, h⟩, mem_univ x⟩
      exact (((Z.local_triv i).open_target.inter ht).Preimage (Continuous.Prod.mk b)).Preimage hc
    · rw [(Z.local_triv i).target_eq, ← base_set_at, mk_preimage_prod_right_eq_empty h,
        preimage_empty, empty_inter]
      exact isOpen_empty
#align fiber_bundle_core.continuous_total_space_mk FiberBundleCore.continuous_totalSpaceMk
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FiberBundleCore.fiberBundle /-
/-- A fiber bundle constructed from core is indeed a fiber bundle. -/
instance fiberBundle : FiberBundle F Z.Fiber
    where
  totalSpace_mk_inducing b :=
    ⟨by
      refine' le_antisymm _ fun s h => _
      · rw [← continuous_iff_le_induced]
        exact continuous_total_space_mk Z b
      · refine'
          is_open_induced_iff.mpr
            ⟨(Z.local_triv_at b).source ∩ Z.local_triv_at b ⁻¹' (Z.local_triv_at b).baseSet ×ˢ s,
              (continuousOn_open_iff (Z.local_triv_at b).open_source).mp
                (Z.local_triv_at b).continuous_toFun _ ((Z.local_triv_at b).open_baseSet.Prod h),
              _⟩
        rw [preimage_inter, ← preimage_comp, Function.comp]
        refine' ext_iff.mpr fun a => ⟨fun ha => _, fun ha => ⟨Z.mem_base_set_at b, _⟩⟩
        · simp only [mem_prod, mem_preimage, mem_inter_iff, local_triv_at_apply_mk] at ha 
          exact ha.2.2
        · simp only [mem_prod, mem_preimage, mem_inter_iff, local_triv_at_apply_mk]
          exact ⟨Z.mem_base_set_at b, ha⟩⟩
  trivializationAtlas := Set.range Z.localTriv
  trivializationAt := Z.localTrivAt
  mem_baseSet_trivializationAt := Z.mem_baseSet_at
  trivialization_mem_atlas b := ⟨Z.indexAt b, rfl⟩
#align fiber_bundle_core.fiber_bundle FiberBundleCore.fiberBundle
-/

#print FiberBundleCore.continuous_proj /-
/-- The projection on the base of a fiber bundle created from core is continuous -/
theorem continuous_proj : Continuous Z.proj :=
  continuous_proj F Z.Fiber
#align fiber_bundle_core.continuous_proj FiberBundleCore.continuous_proj
-/

#print FiberBundleCore.isOpenMap_proj /-
/-- The projection on the base of a fiber bundle created from core is an open map -/
theorem isOpenMap_proj : IsOpenMap Z.proj :=
  isOpenMap_proj F Z.Fiber
#align fiber_bundle_core.is_open_map_proj FiberBundleCore.isOpenMap_proj
-/

end FiberBundleCore

/-! ### Prebundle construction for constructing fiber bundles -/


variable (F) (E : B → Type _) [TopologicalSpace B] [TopologicalSpace F]
  [∀ x, TopologicalSpace (E x)]

#print FiberPrebundle /-
/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (e e' «expr ∈ » pretrivialization_atlas) -/
/-- This structure permits to define a fiber bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphism and hence local trivializations. -/
@[nolint has_nonempty_instance]
structure FiberPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π F E))
  pretrivializationAt : B → Pretrivialization F (π F E)
  mem_base_pretrivializationAt : ∀ x : B, x ∈ (pretrivialization_at x).baseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas
  continuous_triv_change :
    ∀ (e) (_ : e ∈ pretrivialization_atlas) (e') (_ : e' ∈ pretrivialization_atlas),
      ContinuousOn (e ∘ e'.toPartialEquiv.symm) (e'.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source)
  totalSpace_mk_inducing : ∀ b : B, Inducing (pretrivialization_at b ∘ TotalSpace.mk b)
#align fiber_prebundle FiberPrebundle
-/

namespace FiberPrebundle

variable {F E} (a : FiberPrebundle F E) {e : Pretrivialization F (π F E)}

#print FiberPrebundle.totalSpaceTopology /-
/-- Topology on the total space that will make the prebundle into a bundle. -/
def totalSpaceTopology (a : FiberPrebundle F E) : TopologicalSpace (TotalSpace F E) :=
  ⨆ (e : Pretrivialization F (π F E)) (he : e ∈ a.pretrivializationAtlas),
    coinduced e.setSymm Subtype.topologicalSpace
#align fiber_prebundle.total_space_topology FiberPrebundle.totalSpaceTopology
-/

#print FiberPrebundle.continuous_symm_of_mem_pretrivializationAtlas /-
theorem continuous_symm_of_mem_pretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @ContinuousOn _ _ _ a.totalSpaceTopology e.toPartialEquiv.symm e.target :=
  by
  refine'
    id fun z H =>
      id fun U h => preimage_nhdsWithin_coinduced' H e.open_target (le_def.1 (nhds_mono _) U h)
  exact le_iSup₂ e he
#align fiber_prebundle.continuous_symm_of_mem_pretrivialization_atlas FiberPrebundle.continuous_symm_of_mem_pretrivializationAtlas
-/

#print FiberPrebundle.isOpen_source /-
theorem isOpen_source (e : Pretrivialization F (π F E)) : is_open[a.totalSpaceTopology] e.source :=
  by
  letI := a.total_space_topology
  refine' is_open_supr_iff.mpr fun e' => _
  refine' is_open_supr_iff.mpr fun he' => _
  refine' is_open_coinduced.mpr (is_open_induced_iff.mpr ⟨e.target, e.open_target, _⟩)
  rw [Pretrivialization.setSymm, restrict, e.target_eq, e.source_eq, preimage_comp,
    Subtype.preimage_coe_eq_preimage_coe_iff, e'.target_eq, prod_inter_prod, inter_univ,
    Pretrivialization.preimage_symm_proj_inter]
#align fiber_prebundle.is_open_source FiberPrebundle.isOpen_source
-/

#print FiberPrebundle.isOpen_target_of_mem_pretrivializationAtlas_inter /-
theorem isOpen_target_of_mem_pretrivializationAtlas_inter (e e' : Pretrivialization F (π F E))
    (he' : e' ∈ a.pretrivializationAtlas) :
    IsOpen (e'.toPartialEquiv.target ∩ e'.toPartialEquiv.symm ⁻¹' e.source) :=
  by
  letI := a.total_space_topology
  obtain ⟨u, hu1, hu2⟩ :=
    continuous_on_iff'.mp (a.continuous_symm_of_mem_pretrivialization_atlas he') e.source
      (a.is_open_source e)
  rw [inter_comm, hu2]
  exact hu1.inter e'.open_target
#align fiber_prebundle.is_open_target_of_mem_pretrivialization_atlas_inter FiberPrebundle.isOpen_target_of_mem_pretrivializationAtlas_inter
-/

#print FiberPrebundle.trivializationOfMemPretrivializationAtlas /-
/-- Promotion from a `pretrivialization` to a `trivialization`. -/
def trivializationOfMemPretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π F E) :=
  { e with
    open_source := a.isOpen_source e
    continuous_toFun := by
      letI := a.total_space_topology
      refine'
        continuous_on_iff'.mpr fun s hs =>
          ⟨e ⁻¹' s ∩ e.source, is_open_supr_iff.mpr fun e' => _, by rw [inter_assoc, inter_self];
            rfl⟩
      refine' is_open_supr_iff.mpr fun he' => _
      rw [isOpen_coinduced, isOpen_induced_iff]
      obtain ⟨u, hu1, hu2⟩ := continuous_on_iff'.mp (a.continuous_triv_change _ he _ he') s hs
      have hu3 := congr_arg (fun s => (fun x : e'.target => (x : B × F)) ⁻¹' s) hu2
      simp only [Subtype.coe_preimage_self, preimage_inter, univ_inter] at hu3 
      refine'
        ⟨u ∩ e'.to_local_equiv.target ∩ e'.to_local_equiv.symm ⁻¹' e.source, _, by
          simp only [preimage_inter, inter_univ, Subtype.coe_preimage_self, hu3.symm]; rfl⟩
      rw [inter_assoc]
      exact hu1.inter (a.is_open_target_of_mem_pretrivialization_atlas_inter e e' he')
    continuous_invFun := a.continuous_symm_of_mem_pretrivializationAtlas he }
#align fiber_prebundle.trivialization_of_mem_pretrivialization_atlas FiberPrebundle.trivializationOfMemPretrivializationAtlas
-/

#print FiberPrebundle.mem_pretrivializationAt_source /-
theorem mem_pretrivializationAt_source (b : B) (x : E b) :
    TotalSpace.mk b x ∈ (a.pretrivializationAt b).source :=
  by
  simp only [(a.pretrivialization_at b).source_eq, mem_preimage, total_space.proj]
  exact a.mem_base_pretrivialization_at b
#align fiber_prebundle.mem_trivialization_at_source FiberPrebundle.mem_pretrivializationAt_source
-/

#print FiberPrebundle.totalSpaceMk_preimage_source /-
@[simp]
theorem totalSpaceMk_preimage_source (b : B) :
    TotalSpace.mk b ⁻¹' (a.pretrivializationAt b).source = univ :=
  by
  apply eq_univ_of_univ_subset
  rw [(a.pretrivialization_at b).source_eq, ← preimage_comp, Function.comp]
  simp only [total_space.proj]
  rw [preimage_const_of_mem _]
  exact a.mem_base_pretrivialization_at b
#align fiber_prebundle.total_space_mk_preimage_source FiberPrebundle.totalSpaceMk_preimage_source
-/

#print FiberPrebundle.continuous_totalSpaceMk /-
@[continuity]
theorem continuous_totalSpaceMk (b : B) :
    @Continuous _ _ _ a.totalSpaceTopology (TotalSpace.mk b) :=
  by
  letI := a.total_space_topology
  let e := a.trivialization_of_mem_pretrivialization_atlas (a.pretrivialization_mem_atlas b)
  rw [e.to_local_homeomorph.continuous_iff_continuous_comp_left
      (a.total_space_mk_preimage_source b)]
  exact continuous_iff_le_induced.mpr (le_antisymm_iff.mp (a.total_space_mk_inducing b).induced).1
#align fiber_prebundle.continuous_total_space_mk FiberPrebundle.continuous_totalSpaceMk
-/

#print FiberPrebundle.inducing_totalSpaceMk_of_inducing_comp /-
theorem inducing_totalSpaceMk_of_inducing_comp (b : B)
    (h : Inducing (a.pretrivializationAt b ∘ TotalSpace.mk b)) :
    @Inducing _ _ _ a.totalSpaceTopology (TotalSpace.mk b) :=
  by
  letI := a.total_space_topology
  rw [← restrict_comp_cod_restrict (a.mem_trivialization_at_source b)] at h 
  apply Inducing.of_codRestrict (a.mem_trivialization_at_source b)
  refine'
    inducing_of_inducing_compose _
      (continuous_on_iff_continuous_restrict.mp
        (a.trivialization_of_mem_pretrivialization_atlas
            (a.pretrivialization_mem_atlas b)).continuous_toFun)
      h
  exact (a.continuous_total_space_mk b).codRestrict (a.mem_trivialization_at_source b)
#align fiber_prebundle.inducing_total_space_mk_of_inducing_comp FiberPrebundle.inducing_totalSpaceMk_of_inducing_comp
-/

#print FiberPrebundle.toFiberBundle /-
/-- Make a `fiber_bundle` from a `fiber_prebundle`.  Concretely this means
that, given a `fiber_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`fiber_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
def toFiberBundle : @FiberBundle B F _ _ E a.totalSpaceTopology _
    where
  totalSpace_mk_inducing b :=
    a.inducing_totalSpaceMk_of_inducing_comp b (a.totalSpace_mk_inducing b)
  trivializationAtlas :=
    {e |
      ∃ (e₀ : _) (he₀ : e₀ ∈ a.pretrivializationAtlas),
        e = a.trivializationOfMemPretrivializationAtlas he₀}
  trivializationAt x :=
    a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x)
  mem_baseSet_trivializationAt := a.mem_base_pretrivializationAt
  trivialization_mem_atlas x := ⟨_, a.pretrivialization_mem_atlas x, rfl⟩
#align fiber_prebundle.to_fiber_bundle FiberPrebundle.toFiberBundle
-/

#print FiberPrebundle.continuous_proj /-
theorem continuous_proj : @Continuous _ _ a.totalSpaceTopology _ (π F E) :=
  by
  letI := a.total_space_topology
  letI := a.to_fiber_bundle
  exact continuous_proj F E
#align fiber_prebundle.continuous_proj FiberPrebundle.continuous_proj
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FiberPrebundle.continuousOn_of_comp_right /-
/-- For a fiber bundle `E` over `B` constructed using the `fiber_prebundle` mechanism,
continuity of a function `total_space F E → X` on an open set `s` can be checked by precomposing at
each point with the pretrivialization used for the construction at that point. -/
theorem continuousOn_of_comp_right {X : Type _} [TopologicalSpace X] {f : TotalSpace F E → X}
    {s : Set B} (hs : IsOpen s)
    (hf :
      ∀ b ∈ s,
        ContinuousOn (f ∘ (a.pretrivializationAt b).toPartialEquiv.symm)
          ((s ∩ (a.pretrivializationAt b).baseSet) ×ˢ (Set.univ : Set F))) :
    @ContinuousOn _ _ a.totalSpaceTopology _ f (π F E ⁻¹' s) :=
  by
  letI := a.total_space_topology
  intro z hz
  let e : Trivialization F (π F E) :=
    a.trivialization_of_mem_pretrivialization_atlas (a.pretrivialization_mem_atlas z.proj)
  refine'
    (e.continuous_at_of_comp_right _
        ((hf z.proj hz).ContinuousAt (IsOpen.mem_nhds _ _))).ContinuousWithinAt
  · exact a.mem_base_pretrivialization_at z.proj
  · exact (hs.inter (a.pretrivialization_at z.proj).open_baseSet).Prod isOpen_univ
  refine' ⟨_, mem_univ _⟩
  rw [e.coe_fst]
  · exact ⟨hz, a.mem_base_pretrivialization_at z.proj⟩
  · rw [e.mem_source]
    exact a.mem_base_pretrivialization_at z.proj
#align fiber_prebundle.continuous_on_of_comp_right FiberPrebundle.continuousOn_of_comp_right
-/

end FiberPrebundle

