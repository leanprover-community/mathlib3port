/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Heather Macbeth

! This file was ported from Lean 3 source module topology.fiber_bundle.basic
! leanprover-community/mathlib commit 0187644979f2d3e10a06e916a869c994facd9a87
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.FiberBundle.Trivialization

/-!
# Fiber bundles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Mathematically, a (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on
`B` for which the fibers are all homeomorphic to `F`, such that the local situation around each
point is a direct product.

In our formalism, a fiber bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.

To have a fiber bundle structure on `bundle.total_space E`, one should
additionally have the following data:

* `F` should be a topological space;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
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

* `bundle.total_space E` is a type synonym for `Σ (x : B), E x`, that we can endow with a suitable
  topology.
* `fiber_bundle_core ι B F` : structure registering how changes of coordinates act
  on the fiber `F` above open subsets of `B`, where local trivializations are indexed by `ι`.

Let `Z : fiber_bundle_core ι B F`. Then we define

* `Z.fiber x`     : the fiber above `x`, homeomorphic to `F` (and defeq to `F` as a type).
* `Z.total_space` : the total space of `Z`, defined as a `Type` as `Σ (b : B), F`, but with a
  twisted topology coming from the fiber bundle structure. It is (reducibly) the same as
  `bundle.total_space Z.fiber`.
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

With this definition, the type of the fiber bundle space constructed from the core data is just
`Σ (b : B), F `, but the topology is not the product one, in general.

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

open Topology Classical Bundle

attribute [mfld_simps]
  total_space_mk coe_fst coe_snd coe_snd_map_apply coe_snd_map_smul total_space.mk_cast

/-! ### General definition of fiber bundles -/


section FiberBundle

variable (F) [TopologicalSpace B] [TopologicalSpace F] (E : B → Type _)
  [TopologicalSpace (TotalSpace E)] [∀ b, TopologicalSpace (E b)]

#print FiberBundle /-
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`totalSpaceMk_inducing] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`trivializationAtlas] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`trivializationAt] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`mem_baseSet_trivializationAt] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`trivialization_mem_atlas] [] -/
/-- A (topological) fiber bundle with fiber `F` over a base `B` is a space projecting on `B`
for which the fibers are all homeomorphic to `F`, such that the local situation around each point
is a direct product. -/
class FiberBundle where
  totalSpaceMk_inducing : ∀ b : B, Inducing (@totalSpaceMk B E b)
  trivializationAtlas : Set (Trivialization F (π E))
  trivializationAt : B → Trivialization F (π E)
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
class MemTrivializationAtlas [FiberBundle F E] (e : Trivialization F (π E)) : Prop where
  out : e ∈ trivializationAtlas F E
#align mem_trivialization_atlas MemTrivializationAtlas
-/

instance [FiberBundle F E] (b : B) : MemTrivializationAtlas (trivializationAt F E b)
    where out := trivialization_mem_atlas F E b

namespace FiberBundle

variable (F) {E} [FiberBundle F E]

/- warning: fiber_bundle.map_proj_nhds -> FiberBundle.map_proj_nhds is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} (F : Type.{u2}) [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] {E : B -> Type.{u3}} [_inst_4 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u3} (E b)] [_inst_6 : FiberBundle.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] (x : Bundle.TotalSpace.{u1, u3} B E), Eq.{succ u1} (Filter.{u1} B) (Filter.map.{max u1 u3, u1} (Bundle.TotalSpace.{u1, u3} B E) B (Bundle.TotalSpace.proj.{u1, u3} B E) (nhds.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E) _inst_4 x)) (nhds.{u1} B _inst_2 (Bundle.TotalSpace.proj.{u1, u3} B E x))
but is expected to have type
  forall {B : Type.{u2}} (F : Type.{u3}) [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] {E : B -> Type.{u1}} [_inst_4 : TopologicalSpace.{max u1 u2} (Bundle.TotalSpace.{u2, u1} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u1} (E b)] [_inst_6 : FiberBundle.{u2, u3, u1} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] (x : Bundle.TotalSpace.{u2, u1} B E), Eq.{succ u2} (Filter.{u2} B) (Filter.map.{max u2 u1, u2} (Bundle.TotalSpace.{u2, u1} B E) B (Bundle.TotalSpace.proj.{u2, u1} B E) (nhds.{max u2 u1} (Bundle.TotalSpace.{u2, u1} B E) _inst_4 x)) (nhds.{u2} B _inst_2 (Bundle.TotalSpace.proj.{u2, u1} B E x))
Case conversion may be inaccurate. Consider using '#align fiber_bundle.map_proj_nhds FiberBundle.map_proj_nhdsₓ'. -/
theorem map_proj_nhds (x : TotalSpace E) : map (π E) (𝓝 x) = 𝓝 x.proj :=
  (trivializationAt F E x.proj).map_proj_nhds <|
    (trivializationAt F E x.proj).mem_source.2 <| mem_baseSet_trivializationAt F E x.proj
#align fiber_bundle.map_proj_nhds FiberBundle.map_proj_nhds

variable (E)

/- warning: fiber_bundle.continuous_proj -> FiberBundle.continuous_proj is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} (F : Type.{u2}) [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (E : B -> Type.{u3}) [_inst_4 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u3} (E b)] [_inst_6 : FiberBundle.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)], Continuous.{max u1 u3, u1} (Bundle.TotalSpace.{u1, u3} B E) B _inst_4 _inst_2 (Bundle.TotalSpace.proj.{u1, u3} B E)
but is expected to have type
  forall {B : Type.{u2}} (F : Type.{u3}) [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (E : B -> Type.{u1}) [_inst_4 : TopologicalSpace.{max u1 u2} (Bundle.TotalSpace.{u2, u1} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u1} (E b)] [_inst_6 : FiberBundle.{u2, u3, u1} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)], Continuous.{max u2 u1, u2} (Bundle.TotalSpace.{u2, u1} B E) B _inst_4 _inst_2 (Bundle.TotalSpace.proj.{u2, u1} B E)
Case conversion may be inaccurate. Consider using '#align fiber_bundle.continuous_proj FiberBundle.continuous_projₓ'. -/
/-- The projection from a fiber bundle to its base is continuous. -/
@[continuity]
theorem continuous_proj : Continuous (π E) :=
  continuous_iff_continuousAt.2 fun x => (map_proj_nhds F x).le
#align fiber_bundle.continuous_proj FiberBundle.continuous_proj

/- warning: fiber_bundle.is_open_map_proj -> FiberBundle.isOpenMap_proj is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} (F : Type.{u2}) [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (E : B -> Type.{u3}) [_inst_4 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u3} (E b)] [_inst_6 : FiberBundle.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)], IsOpenMap.{max u1 u3, u1} (Bundle.TotalSpace.{u1, u3} B E) B _inst_4 _inst_2 (Bundle.TotalSpace.proj.{u1, u3} B E)
but is expected to have type
  forall {B : Type.{u2}} (F : Type.{u3}) [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (E : B -> Type.{u1}) [_inst_4 : TopologicalSpace.{max u1 u2} (Bundle.TotalSpace.{u2, u1} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u1} (E b)] [_inst_6 : FiberBundle.{u2, u3, u1} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)], IsOpenMap.{max u2 u1, u2} (Bundle.TotalSpace.{u2, u1} B E) B _inst_4 _inst_2 (Bundle.TotalSpace.proj.{u2, u1} B E)
Case conversion may be inaccurate. Consider using '#align fiber_bundle.is_open_map_proj FiberBundle.isOpenMap_projₓ'. -/
/-- The projection from a fiber bundle to its base is an open map. -/
theorem isOpenMap_proj : IsOpenMap (π E) :=
  IsOpenMap.of_nhds_le fun x => (map_proj_nhds F x).ge
#align fiber_bundle.is_open_map_proj FiberBundle.isOpenMap_proj

/- warning: fiber_bundle.surjective_proj -> FiberBundle.surjective_proj is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} (F : Type.{u2}) [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (E : B -> Type.{u3}) [_inst_4 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u3} (E b)] [_inst_6 : FiberBundle.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] [_inst_7 : Nonempty.{succ u2} F], Function.Surjective.{max (succ u1) (succ u3), succ u1} (Bundle.TotalSpace.{u1, u3} B E) B (Bundle.TotalSpace.proj.{u1, u3} B E)
but is expected to have type
  forall {B : Type.{u2}} (F : Type.{u3}) [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (E : B -> Type.{u1}) [_inst_4 : TopologicalSpace.{max u1 u2} (Bundle.TotalSpace.{u2, u1} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u1} (E b)] [_inst_6 : FiberBundle.{u2, u3, u1} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] [_inst_7 : Nonempty.{succ u3} F], Function.Surjective.{max (succ u2) (succ u1), succ u2} (Bundle.TotalSpace.{u2, u1} B E) B (Bundle.TotalSpace.proj.{u2, u1} B E)
Case conversion may be inaccurate. Consider using '#align fiber_bundle.surjective_proj FiberBundle.surjective_projₓ'. -/
/-- The projection from a fiber bundle with a nonempty fiber to its base is a surjective
map. -/
theorem surjective_proj [Nonempty F] : Function.Surjective (π E) := fun b =>
  let ⟨p, _, hpb⟩ :=
    (trivializationAt F E b).proj_surjOn_baseSet (mem_baseSet_trivializationAt F E b)
  ⟨p, hpb⟩
#align fiber_bundle.surjective_proj FiberBundle.surjective_proj

/- warning: fiber_bundle.quotient_map_proj -> FiberBundle.quotientMap_proj is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} (F : Type.{u2}) [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (E : B -> Type.{u3}) [_inst_4 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u3} (E b)] [_inst_6 : FiberBundle.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] [_inst_7 : Nonempty.{succ u2} F], QuotientMap.{max u1 u3, u1} (Bundle.TotalSpace.{u1, u3} B E) B _inst_4 _inst_2 (Bundle.TotalSpace.proj.{u1, u3} B E)
but is expected to have type
  forall {B : Type.{u2}} (F : Type.{u3}) [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (E : B -> Type.{u1}) [_inst_4 : TopologicalSpace.{max u1 u2} (Bundle.TotalSpace.{u2, u1} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u1} (E b)] [_inst_6 : FiberBundle.{u2, u3, u1} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] [_inst_7 : Nonempty.{succ u3} F], QuotientMap.{max u2 u1, u2} (Bundle.TotalSpace.{u2, u1} B E) B _inst_4 _inst_2 (Bundle.TotalSpace.proj.{u2, u1} B E)
Case conversion may be inaccurate. Consider using '#align fiber_bundle.quotient_map_proj FiberBundle.quotientMap_projₓ'. -/
/-- The projection from a fiber bundle with a nonempty fiber to its base is a quotient
map. -/
theorem quotientMap_proj [Nonempty F] : QuotientMap (π E) :=
  (isOpenMap_proj F E).to_quotientMap (continuous_proj F E) (surjective_proj F E)
#align fiber_bundle.quotient_map_proj FiberBundle.quotientMap_proj

/- warning: fiber_bundle.continuous_total_space_mk -> FiberBundle.continuous_totalSpaceMk is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} (F : Type.{u2}) [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (E : B -> Type.{u3}) [_inst_4 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u3} (E b)] [_inst_6 : FiberBundle.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] (x : B), Continuous.{u3, max u1 u3} (E x) (Bundle.TotalSpace.{u1, u3} B E) (_inst_5 x) _inst_4 (Bundle.totalSpaceMk.{u1, u3} B E x)
but is expected to have type
  forall {B : Type.{u1}} (F : Type.{u3}) [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u3} F] (E : B -> Type.{u2}) [_inst_4 : TopologicalSpace.{max u2 u1} (Bundle.TotalSpace.{u1, u2} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u2} (E b)] [_inst_6 : FiberBundle.{u1, u3, u2} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] (x : B), Continuous.{u2, max u1 u2} (E x) (Bundle.TotalSpace.{u1, u2} B E) (_inst_5 x) _inst_4 (Bundle.totalSpaceMk.{u1, u2} B E x)
Case conversion may be inaccurate. Consider using '#align fiber_bundle.continuous_total_space_mk FiberBundle.continuous_totalSpaceMkₓ'. -/
theorem continuous_totalSpaceMk (x : B) : Continuous (@totalSpaceMk B E x) :=
  (totalSpaceMk_inducing F E x).Continuous
#align fiber_bundle.continuous_total_space_mk FiberBundle.continuous_totalSpaceMk

variable {E F}

/- warning: fiber_bundle.mem_trivialization_at_proj_source -> FiberBundle.mem_trivializationAt_proj_source is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] {E : B -> Type.{u3}} [_inst_4 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u3} (E b)] [_inst_6 : FiberBundle.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] {x : Bundle.TotalSpace.{u1, u3} B E}, Membership.Mem.{max u1 u3, max u1 u3} (Bundle.TotalSpace.{u1, u3} B E) (Set.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)) (Set.hasMem.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)) x (LocalEquiv.source.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) (LocalHomeomorph.toLocalEquiv.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) _inst_4 (Prod.topologicalSpace.{u1, u2} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u1, u3} B E) (FiberBundle.trivializationAt.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b) _inst_6 (Bundle.TotalSpace.proj.{u1, u3} B E x)))))
but is expected to have type
  forall {B : Type.{u3}} {F : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u1} F] {E : B -> Type.{u2}} [_inst_4 : TopologicalSpace.{max u2 u3} (Bundle.TotalSpace.{u3, u2} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u2} (E b)] [_inst_6 : FiberBundle.{u3, u1, u2} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] {x : Bundle.TotalSpace.{u3, u2} B E}, Membership.mem.{max u3 u2, max u3 u2} (Bundle.TotalSpace.{u3, u2} B E) (Set.{max u3 u2} (Bundle.TotalSpace.{u3, u2} B E)) (Set.instMembershipSet.{max u3 u2} (Bundle.TotalSpace.{u3, u2} B E)) x (LocalEquiv.source.{max u3 u2, max u3 u1} (Bundle.TotalSpace.{u3, u2} B E) (Prod.{u3, u1} B F) (LocalHomeomorph.toLocalEquiv.{max u3 u2, max u3 u1} (Bundle.TotalSpace.{u3, u2} B E) (Prod.{u3, u1} B F) _inst_4 (instTopologicalSpaceProd.{u3, u1} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u3, u1, max u3 u2} B F (Bundle.TotalSpace.{u3, u2} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u3, u2} B E) (FiberBundle.trivializationAt.{u3, u1, u2} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b) _inst_6 (Bundle.TotalSpace.proj.{u3, u2} B E x)))))
Case conversion may be inaccurate. Consider using '#align fiber_bundle.mem_trivialization_at_proj_source FiberBundle.mem_trivializationAt_proj_sourceₓ'. -/
@[simp, mfld_simps]
theorem mem_trivializationAt_proj_source {x : TotalSpace E} :
    x ∈ (trivializationAt F E x.proj).source :=
  (Trivialization.mem_source _).mpr <| mem_baseSet_trivializationAt F E x.proj
#align fiber_bundle.mem_trivialization_at_proj_source FiberBundle.mem_trivializationAt_proj_source

/- warning: fiber_bundle.trivialization_at_proj_fst -> FiberBundle.trivializationAt_proj_fst is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] {E : B -> Type.{u3}} [_inst_4 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u3} (E b)] [_inst_6 : FiberBundle.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] {x : Bundle.TotalSpace.{u1, u3} B E}, Eq.{succ u1} B (Prod.fst.{u1, u2} B F (coeFn.{max (succ u1) (succ u2) (succ (max u1 u3)), max (succ (max u1 u3)) (succ u1) (succ u2)} (Trivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u1, u3} B E)) (fun (_x : Trivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u1, u3} B E)) => (Bundle.TotalSpace.{u1, u3} B E) -> (Prod.{u1, u2} B F)) (Trivialization.hasCoeToFun.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) _inst_4) (FiberBundle.trivializationAt.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b) _inst_6 (Bundle.TotalSpace.proj.{u1, u3} B E x)) x)) (Bundle.TotalSpace.proj.{u1, u3} B E x)
but is expected to have type
  forall {B : Type.{u3}} {F : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u1} F] {E : B -> Type.{u2}} [_inst_4 : TopologicalSpace.{max u2 u3} (Bundle.TotalSpace.{u3, u2} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u2} (E b)] [_inst_6 : FiberBundle.{u3, u1, u2} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] {x : Bundle.TotalSpace.{u3, u2} B E}, Eq.{succ u3} B (Prod.fst.{u3, u1} B F (Trivialization.toFun'.{u3, u1, max u3 u2} B F (Bundle.TotalSpace.{u3, u2} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u2} B E) _inst_4 (FiberBundle.trivializationAt.{u3, u1, u2} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b) _inst_6 (Bundle.TotalSpace.proj.{u3, u2} B E x)) x)) (Bundle.TotalSpace.proj.{u3, u2} B E x)
Case conversion may be inaccurate. Consider using '#align fiber_bundle.trivialization_at_proj_fst FiberBundle.trivializationAt_proj_fstₓ'. -/
@[simp, mfld_simps]
theorem trivializationAt_proj_fst {x : TotalSpace E} :
    ((trivializationAt F E x.proj) x).1 = x.proj :=
  Trivialization.coe_fst' _ <| mem_baseSet_trivializationAt F E x.proj
#align fiber_bundle.trivialization_at_proj_fst FiberBundle.trivializationAt_proj_fst

variable (F)

open Trivialization

/- warning: fiber_bundle.continuous_within_at_total_space -> FiberBundle.continuousWithinAt_totalSpace is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fiber_bundle.continuous_within_at_total_space FiberBundle.continuousWithinAt_totalSpaceₓ'. -/
/-- Characterization of continuous functions (at a point, within a set) into a fiber bundle. -/
theorem continuousWithinAt_totalSpace (f : X → TotalSpace E) {s : Set X} {x₀ : X} :
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

/- warning: fiber_bundle.continuous_at_total_space -> FiberBundle.continuousAt_totalSpace is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} (F : Type.{u2}) {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] {E : B -> Type.{u4}} [_inst_4 : TopologicalSpace.{max u1 u4} (Bundle.TotalSpace.{u1, u4} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u4} (E b)] [_inst_6 : FiberBundle.{u1, u2, u4} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] (f : X -> (Bundle.TotalSpace.{u1, u4} B E)) {x₀ : X}, Iff (ContinuousAt.{u3, max u1 u4} X (Bundle.TotalSpace.{u1, u4} B E) _inst_1 _inst_4 f x₀) (And (ContinuousAt.{u3, u1} X B _inst_1 _inst_2 (fun (x : X) => Bundle.TotalSpace.proj.{u1, u4} B E (f x)) x₀) (ContinuousAt.{u3, u2} X F _inst_1 _inst_3 (fun (x : X) => Prod.snd.{u1, u2} B F (coeFn.{max (succ u1) (succ u2) (succ (max u1 u4)), max (succ (max u1 u4)) (succ u1) (succ u2)} (Trivialization.{u1, u2, max u1 u4} B F (Bundle.TotalSpace.{u1, u4} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u1, u4} B E)) (fun (_x : Trivialization.{u1, u2, max u1 u4} B F (Bundle.TotalSpace.{u1, u4} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u1, u4} B E)) => (Bundle.TotalSpace.{u1, u4} B E) -> (Prod.{u1, u2} B F)) (Trivialization.hasCoeToFun.{u1, u2, max u1 u4} B F (Bundle.TotalSpace.{u1, u4} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u4} B E) _inst_4) (FiberBundle.trivializationAt.{u1, u2, u4} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b) _inst_6 (Bundle.TotalSpace.proj.{u1, u4} B E (f x₀))) (f x))) x₀))
but is expected to have type
  forall {B : Type.{u4}} (F : Type.{u1}) {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u4} B] [_inst_3 : TopologicalSpace.{u1} F] {E : B -> Type.{u3}} [_inst_4 : TopologicalSpace.{max u3 u4} (Bundle.TotalSpace.{u4, u3} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u3} (E b)] [_inst_6 : FiberBundle.{u4, u1, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] (f : X -> (Bundle.TotalSpace.{u4, u3} B E)) {x₀ : X}, Iff (ContinuousAt.{u2, max u4 u3} X (Bundle.TotalSpace.{u4, u3} B E) _inst_1 _inst_4 f x₀) (And (ContinuousAt.{u2, u4} X B _inst_1 _inst_2 (fun (x : X) => Bundle.TotalSpace.proj.{u4, u3} B E (f x)) x₀) (ContinuousAt.{u2, u1} X F _inst_1 _inst_3 (fun (x : X) => Prod.snd.{u4, u1} B F (Trivialization.toFun'.{u4, u1, max u4 u3} B F (Bundle.TotalSpace.{u4, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u4, u3} B E) _inst_4 (FiberBundle.trivializationAt.{u4, u1, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b) _inst_6 (Bundle.TotalSpace.proj.{u4, u3} B E (f x₀))) (f x))) x₀))
Case conversion may be inaccurate. Consider using '#align fiber_bundle.continuous_at_total_space FiberBundle.continuousAt_totalSpaceₓ'. -/
/-- Characterization of continuous functions (at a point) into a fiber bundle. -/
theorem continuousAt_totalSpace (f : X → TotalSpace E) {x₀ : X} :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x => (f x).proj) x₀ ∧
        ContinuousAt (fun x => ((trivializationAt F E (f x₀).proj) (f x)).2) x₀ :=
  by simp_rw [← continuousWithinAt_univ]; exact continuous_within_at_total_space F f
#align fiber_bundle.continuous_at_total_space FiberBundle.continuousAt_totalSpace

end FiberBundle

variable (F E)

/- warning: fiber_bundle.exists_trivialization_Icc_subset -> FiberBundle.exists_trivialization_Icc_subset is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} (F : Type.{u2}) [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (E : B -> Type.{u3}) [_inst_4 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u3} (E b)] [_inst_6 : ConditionallyCompleteLinearOrder.{u1} B] [_inst_7 : OrderTopology.{u1} B _inst_2 (PartialOrder.toPreorder.{u1} B (SemilatticeInf.toPartialOrder.{u1} B (Lattice.toSemilatticeInf.{u1} B (ConditionallyCompleteLattice.toLattice.{u1} B (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} B _inst_6)))))] [_inst_8 : FiberBundle.{u1, u2, u3} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] (a : B) (b : B), Exists.{max (succ u1) (succ u2) (succ (max u1 u3))} (Trivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u1, u3} B E)) (fun (e : Trivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u1, u3} B E)) => HasSubset.Subset.{u1} (Set.{u1} B) (Set.hasSubset.{u1} B) (Set.Icc.{u1} B (PartialOrder.toPreorder.{u1} B (SemilatticeInf.toPartialOrder.{u1} B (Lattice.toSemilatticeInf.{u1} B (ConditionallyCompleteLattice.toLattice.{u1} B (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} B _inst_6))))) a b) (Trivialization.baseSet.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u1, u3} B E) e))
but is expected to have type
  forall {B : Type.{u3}} (F : Type.{u2}) [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (E : B -> Type.{u1}) [_inst_4 : TopologicalSpace.{max u1 u3} (Bundle.TotalSpace.{u3, u1} B E)] [_inst_5 : forall (b : B), TopologicalSpace.{u1} (E b)] [_inst_6 : ConditionallyCompleteLinearOrder.{u3} B] [_inst_7 : OrderTopology.{u3} B _inst_2 (PartialOrder.toPreorder.{u3} B (SemilatticeInf.toPartialOrder.{u3} B (Lattice.toSemilatticeInf.{u3} B (ConditionallyCompleteLattice.toLattice.{u3} B (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} B _inst_6)))))] [_inst_8 : FiberBundle.{u3, u2, u1} B F _inst_2 _inst_3 E _inst_4 (fun (b : B) => _inst_5 b)] (a : B) (b : B), Exists.{max (max (succ u3) (succ u2)) (succ u1)} (Trivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u3, u1} B E)) (fun (e : Trivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u3, u1} B E)) => HasSubset.Subset.{u3} (Set.{u3} B) (Set.instHasSubsetSet.{u3} B) (Set.Icc.{u3} B (PartialOrder.toPreorder.{u3} B (SemilatticeInf.toPartialOrder.{u3} B (Lattice.toSemilatticeInf.{u3} B (ConditionallyCompleteLattice.toLattice.{u3} B (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} B _inst_6))))) a b) (Trivialization.baseSet.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 _inst_4 (Bundle.TotalSpace.proj.{u3, u1} B E) e))
Case conversion may be inaccurate. Consider using '#align fiber_bundle.exists_trivialization_Icc_subset FiberBundle.exists_trivialization_Icc_subsetₓ'. -/
/-- If `E` is a fiber bundle over a conditionally complete linear order,
then it is trivial over any closed interval. -/
theorem FiberBundle.exists_trivialization_Icc_subset [ConditionallyCompleteLinearOrder B]
    [OrderTopology B] [FiberBundle F E] (a b : B) :
    ∃ e : Trivialization F (π E), Icc a b ⊆ e.baseSet := by
  classical
    obtain ⟨ea, hea⟩ : ∃ ea : Trivialization F (π E), a ∈ ea.baseSet :=
      ⟨trivialization_at F E a, mem_base_set_trivialization_at F E a⟩
    -- If `a < b`, then `[a, b] = ∅`, and the statement is trivial
      cases' le_or_lt a b with hab hab <;>
      [skip;exact ⟨ea, by simp [*]⟩]
    /- Let `s` be the set of points `x ∈ [a, b]` such that `E` is trivializable over `[a, x]`.
      We need to show that `b ∈ s`. Let `c = Sup s`. We will show that `c ∈ s` and `c = b`. -/
    set s : Set B := { x ∈ Icc a b | ∃ e : Trivialization F (π E), Icc a x ⊆ e.baseSet }
    have ha : a ∈ s := ⟨left_mem_Icc.2 hab, ea, by simp [hea]⟩
    have sne : s.nonempty := ⟨a, ha⟩
    have hsb : b ∈ upperBounds s := fun x hx => hx.1.2
    have sbd : BddAbove s := ⟨b, hsb⟩
    set c := Sup s
    have hsc : IsLUB s c := isLUB_csSup sne sbd
    have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
    obtain ⟨-, ec : Trivialization F (π E), hec : Icc a c ⊆ ec.base_set⟩ : c ∈ s :=
      by
      cases' hc.1.eq_or_lt with heq hlt; · rwa [← HEq]
      refine' ⟨hc, _⟩
      /- In order to show that `c ∈ s`, consider a trivialization `ec` of `proj` over a neighborhood
          of `c`. Its base set includes `(c', c]` for some `c' ∈ [a, c)`. -/
      obtain ⟨ec, hc⟩ : ∃ ec : Trivialization F (π E), c ∈ ec.baseSet :=
        ⟨trivialization_at F E c, mem_base_set_trivialization_at F E c⟩
      obtain ⟨c', hc', hc'e⟩ : ∃ c' ∈ Ico a c, Ioc c' c ⊆ ec.base_set :=
        (mem_nhdsWithin_Iic_iff_exists_mem_Ico_Ioc_subset hlt).1
          (mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds ec.open_base_set hc)
      /- Since `c' < c = Sup s`, there exists `d ∈ s ∩ (c', c]`. Let `ead` be a trivialization of
          `proj` over `[a, d]`. Then we can glue `ead` and `ec` into a trivialization over `[a, c]`. -/
      obtain ⟨d, ⟨hdab, ead, had⟩, hd⟩ : ∃ d ∈ s, d ∈ Ioc c' c := hsc.exists_between hc'.2
      refine' ⟨ead.piecewise_le ec d (had ⟨hdab.1, le_rfl⟩) (hc'e hd), subset_ite.2 _⟩
      refine'
        ⟨fun x hx => had ⟨hx.1.1, hx.2⟩, fun x hx => hc'e ⟨hd.1.trans (not_le.1 hx.2), hx.1.2⟩⟩
    /- So, `c ∈ s`. Let `ec` be a trivialization of `proj` over `[a, c]`.  If `c = b`, then we are
      done. Otherwise we show that `proj` can be trivialized over a larger interval `[a, d]`,
      `d ∈ (c, b]`, hence `c` is not an upper bound of `s`. -/
    cases' hc.2.eq_or_lt with heq hlt
    · exact ⟨ec, HEq ▸ hec⟩
    rsuffices ⟨d, hdcb, hd⟩ : ∃ d ∈ Ioc c b, ∃ e : Trivialization F (π E), Icc a d ⊆ e.baseSet
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
      obtain ⟨ed, hed⟩ : ∃ ed : Trivialization F (π E), d ∈ ed.baseSet :=
        ⟨trivialization_at F E d, mem_base_set_trivialization_at F E d⟩
      refine'
        ⟨d, hdcb,
          (ec.restr_open (Iio d) isOpen_Iio).disjointUnion (ed.restr_open (Ioi c) isOpen_Ioi)
            (he.mono (inter_subset_right _ _) (inter_subset_right _ _)),
          fun x hx => _⟩
      rcases hx.2.eq_or_lt with (rfl | hxd)
      exacts[Or.inr ⟨hed, hdcb.1⟩, Or.inl ⟨had ⟨hx.1, hxd⟩, hxd⟩]
    · /- If `(c, d)` is nonempty, then take `d' ∈ (c, d)`. Since the base set of `ec` includes
          `[a, d)`, it includes `[a, d'] ⊆ [a, d)` as well. -/
      rw [disjoint_left] at he; push_neg  at he; rcases he with ⟨d', hdd' : d' < d, hd'c⟩
      exact ⟨d', ⟨hd'c, hdd'.le.trans hdcb.2⟩, ec, (Icc_subset_Ico_right hdd').trans had⟩
#align fiber_bundle.exists_trivialization_Icc_subset FiberBundle.exists_trivialization_Icc_subset

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

include Z

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

section FiberInstances

attribute [local reducible] fiber

#print FiberBundleCore.topologicalSpaceFiber /-
instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) := by infer_instance
#align fiber_bundle_core.topological_space_fiber FiberBundleCore.topologicalSpaceFiber
-/

end FiberInstances

#print FiberBundleCore.TotalSpace /-
/-- The total space of the fiber bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`, a.k.a. `Σ x, Z.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def TotalSpace :=
  Bundle.TotalSpace Z.Fiber
#align fiber_bundle_core.total_space FiberBundleCore.TotalSpace
-/

#print FiberBundleCore.proj /-
/-- The projection from the total space of a fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
def proj : Z.TotalSpace → B :=
  Bundle.TotalSpace.proj
#align fiber_bundle_core.proj FiberBundleCore.proj
-/

/- warning: fiber_bundle_core.triv_change -> FiberBundleCore.trivChange is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F], (FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) -> ι -> ι -> (LocalHomeomorph.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Prod.{u2, u3} B F) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F], (FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) -> ι -> ι -> (LocalHomeomorph.{max u3 u2, max u3 u2} (Prod.{u2, u3} B F) (Prod.{u2, u3} B F) (instTopologicalSpaceProd.{u2, u3} B F _inst_2 _inst_3) (instTopologicalSpaceProd.{u2, u3} B F _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.triv_change FiberBundleCore.trivChangeₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Local homeomorphism version of the trivialization change. -/
def trivChange (i j : ι) : LocalHomeomorph (B × F) (B × F)
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

/- warning: fiber_bundle_core.mem_triv_change_source -> FiberBundleCore.mem_trivChange_source is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι) (j : ι) (p : Prod.{u2, u3} B F), Iff (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Set.{max u2 u3} (Prod.{u2, u3} B F)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} B F)) p (LocalEquiv.source.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Prod.{u2, u3} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Prod.{u2, u3} B F) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (FiberBundleCore.trivChange.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i j)))) (Membership.Mem.{u2, u2} B (Set.{u2} B) (Set.hasMem.{u2} B) (Prod.fst.{u2, u3} B F p) (Inter.inter.{u2} (Set.{u2} B) (Set.hasInter.{u2} B) (FiberBundleCore.baseSet.{u1, u2, u3} ι B _inst_2 F _inst_3 Z i) (FiberBundleCore.baseSet.{u1, u2, u3} ι B _inst_2 F _inst_3 Z j)))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (i : ι) (j : ι) (p : Prod.{u3, u2} B F), Iff (Membership.mem.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (Set.{max u3 u2} (Prod.{u3, u2} B F)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} B F)) p (LocalEquiv.source.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (Prod.{u3, u2} B F) (LocalHomeomorph.toLocalEquiv.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (Prod.{u3, u2} B F) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (FiberBundleCore.trivChange.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i j)))) (Membership.mem.{u3, u3} B (Set.{u3} B) (Set.instMembershipSet.{u3} B) (Prod.fst.{u3, u2} B F p) (Inter.inter.{u3} (Set.{u3} B) (Set.instInterSet.{u3} B) (FiberBundleCore.baseSet.{u1, u3, u2} ι B _inst_2 F _inst_3 Z i) (FiberBundleCore.baseSet.{u1, u3, u2} ι B _inst_2 F _inst_3 Z j)))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.mem_triv_change_source FiberBundleCore.mem_trivChange_sourceₓ'. -/
@[simp, mfld_simps]
theorem mem_trivChange_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).source ↔ p.1 ∈ Z.baseSet i ∩ Z.baseSet j := by erw [mem_prod]; simp
#align fiber_bundle_core.mem_triv_change_source FiberBundleCore.mem_trivChange_source

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print FiberBundleCore.localTrivAsLocalEquiv /-
/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (base_set i)` and `base_set i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be a local homeomorphism. For now, we only introduce the
local equiv version, denoted with a prime. In further developments, avoid this auxiliary version,
and use `Z.local_triv` instead.
-/
def localTrivAsLocalEquiv (i : ι) : LocalEquiv Z.TotalSpace (B × F)
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
#align fiber_bundle_core.local_triv_as_local_equiv FiberBundleCore.localTrivAsLocalEquiv
-/

variable (i : ι)

/- warning: fiber_bundle_core.mem_local_triv_as_local_equiv_source -> FiberBundleCore.mem_localTrivAsLocalEquiv_source is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι) (p : FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z), Iff (Membership.Mem.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Set.{max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (Set.hasMem.{max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) p (LocalEquiv.source.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))) (Membership.Mem.{u2, u2} B (Set.{u2} B) (Set.hasMem.{u2} B) (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p) (FiberBundleCore.baseSet.{u1, u2, u3} ι B _inst_2 F _inst_3 Z i))
but is expected to have type
  forall {ι : Type.{u3}} {B : Type.{u2}} {F : Type.{u1}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u1} F] (Z : FiberBundleCore.{u3, u2, u1} ι B _inst_2 F _inst_3) (i : ι) (p : FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z), Iff (Membership.mem.{max u2 u1, max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (Set.{max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) (Set.instMembershipSet.{max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) p (LocalEquiv.source.{max u2 u1, max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u1} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u3, u2, u1} ι B F _inst_2 _inst_3 Z i))) (Membership.mem.{u2, u2} B (Set.{u2} B) (Set.instMembershipSet.{u2} B) (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p) (FiberBundleCore.baseSet.{u3, u2, u1} ι B _inst_2 F _inst_3 Z i))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.mem_local_triv_as_local_equiv_source FiberBundleCore.mem_localTrivAsLocalEquiv_sourceₓ'. -/
theorem mem_localTrivAsLocalEquiv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTrivAsLocalEquiv i).source ↔ p.1 ∈ Z.baseSet i :=
  Iff.rfl
#align fiber_bundle_core.mem_local_triv_as_local_equiv_source FiberBundleCore.mem_localTrivAsLocalEquiv_source

/- warning: fiber_bundle_core.mem_local_triv_as_local_equiv_target -> FiberBundleCore.mem_localTrivAsLocalEquiv_target is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι) (p : Prod.{u2, u3} B F), Iff (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Set.{max u2 u3} (Prod.{u2, u3} B F)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} B F)) p (LocalEquiv.target.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))) (Membership.Mem.{u2, u2} B (Set.{u2} B) (Set.hasMem.{u2} B) (Prod.fst.{u2, u3} B F p) (FiberBundleCore.baseSet.{u1, u2, u3} ι B _inst_2 F _inst_3 Z i))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (i : ι) (p : Prod.{u3, u2} B F), Iff (Membership.mem.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (Set.{max u3 u2} (Prod.{u3, u2} B F)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} B F)) p (LocalEquiv.target.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i))) (Membership.mem.{u3, u3} B (Set.{u3} B) (Set.instMembershipSet.{u3} B) (Prod.fst.{u3, u2} B F p) (FiberBundleCore.baseSet.{u1, u3, u2} ι B _inst_2 F _inst_3 Z i))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.mem_local_triv_as_local_equiv_target FiberBundleCore.mem_localTrivAsLocalEquiv_targetₓ'. -/
theorem mem_localTrivAsLocalEquiv_target (p : B × F) :
    p ∈ (Z.localTrivAsLocalEquiv i).target ↔ p.1 ∈ Z.baseSet i := by erw [mem_prod];
  simp only [and_true_iff, mem_univ]
#align fiber_bundle_core.mem_local_triv_as_local_equiv_target FiberBundleCore.mem_localTrivAsLocalEquiv_target

/- warning: fiber_bundle_core.local_triv_as_local_equiv_apply -> FiberBundleCore.localTrivAsLocalEquiv_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι) (p : FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z), Eq.{max (succ u2) (succ u3)} (Prod.{u2, u3} B F) (coeFn.{succ (max u2 u3), succ (max u2 u3)} (LocalEquiv.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F)) (fun (_x : LocalEquiv.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F)) => (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) -> (Prod.{u2, u3} B F)) (LocalEquiv.hasCoeToFun.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F)) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i) p) (Prod.mk.{u2, u3} B F (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p) (FiberBundleCore.coordChange.{u1, u2, u3} ι B _inst_2 F _inst_3 Z (FiberBundleCore.indexAt.{u1, u2, u3} ι B _inst_2 F _inst_3 Z (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p)) i (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p) (Sigma.snd.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p)))
but is expected to have type
  forall {ι : Type.{u3}} {B : Type.{u2}} {F : Type.{u1}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u1} F] (Z : FiberBundleCore.{u3, u2, u1} ι B _inst_2 F _inst_3) (i : ι) (p : FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} B F) (LocalEquiv.toFun.{max u2 u1, max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u1} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u3, u2, u1} ι B F _inst_2 _inst_3 Z i) p) (Prod.mk.{u2, u1} B F (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p) (FiberBundleCore.coordChange.{u3, u2, u1} ι B _inst_2 F _inst_3 Z (FiberBundleCore.indexAt.{u3, u2, u1} ι B _inst_2 F _inst_3 Z (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p)) i (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p) (Sigma.snd.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p)))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_as_local_equiv_apply FiberBundleCore.localTrivAsLocalEquiv_applyₓ'. -/
theorem localTrivAsLocalEquiv_apply (p : Z.TotalSpace) :
    (Z.localTrivAsLocalEquiv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl
#align fiber_bundle_core.local_triv_as_local_equiv_apply FiberBundleCore.localTrivAsLocalEquiv_apply

/- warning: fiber_bundle_core.local_triv_as_local_equiv_trans -> FiberBundleCore.localTrivAsLocalEquiv_trans is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι) (j : ι), HasEquivₓ.Equiv.{succ (max u2 u3)} (LocalEquiv.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Prod.{u2, u3} B F)) (setoidHasEquiv.{succ (max u2 u3)} (LocalEquiv.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Prod.{u2, u3} B F)) (LocalEquiv.eqOnSourceSetoid.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Prod.{u2, u3} B F))) (LocalEquiv.trans.{max u2 u3, max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (LocalEquiv.symm.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i)) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z j)) (LocalHomeomorph.toLocalEquiv.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Prod.{u2, u3} B F) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (FiberBundleCore.trivChange.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i j))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (i : ι) (j : ι), HasEquiv.Equiv.{max (max (succ u3) (succ u2)) (succ (max u3 u2)), 0} (LocalEquiv.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (Prod.{u3, u2} B F)) (instHasEquiv.{max (succ u3) (succ u2)} (LocalEquiv.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (Prod.{u3, u2} B F)) (LocalEquiv.eqOnSourceSetoid.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (Prod.{u3, u2} B F))) (LocalEquiv.trans.{max u3 u2, max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (LocalEquiv.symm.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i)) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z j)) (LocalHomeomorph.toLocalEquiv.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (Prod.{u3, u2} B F) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (FiberBundleCore.trivChange.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i j))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_as_local_equiv_trans FiberBundleCore.localTrivAsLocalEquiv_transₓ'. -/
/-- The composition of two local trivializations is the trivialization change Z.triv_change i j. -/
theorem localTrivAsLocalEquiv_trans (i j : ι) :
    (Z.localTrivAsLocalEquiv i).symm.trans (Z.localTrivAsLocalEquiv j) ≈
      (Z.trivChange i j).toLocalEquiv :=
  by
  constructor
  · ext x; simp only [mem_local_triv_as_local_equiv_target, mfld_simps]; rfl
  · rintro ⟨x, v⟩ hx
    simp only [triv_change, local_triv_as_local_equiv, LocalEquiv.symm, true_and_iff,
      Prod.mk.inj_iff, prod_mk_mem_set_prod_eq, LocalEquiv.trans_source, mem_inter_iff,
      and_true_iff, mem_preimage, proj, mem_univ, [anonymous], eq_self_iff_true,
      LocalEquiv.coe_trans, total_space.proj] at hx⊢
    simp only [Z.coord_change_comp, hx, mem_inter_iff, and_self_iff, mem_base_set_at]
#align fiber_bundle_core.local_triv_as_local_equiv_trans FiberBundleCore.localTrivAsLocalEquiv_trans

#print FiberBundleCore.toTopologicalSpace /-
/-- Topological structure on the total space of a fiber bundle created from core, designed so
that all the local trivialization are continuous. -/
instance toTopologicalSpace : TopologicalSpace (Bundle.TotalSpace Z.Fiber) :=
  TopologicalSpace.generateFrom <|
    ⋃ (i : ι) (s : Set (B × F)) (s_open : IsOpen s), {(Z i).source ∩ Z i ⁻¹' s}
#align fiber_bundle_core.to_topological_space FiberBundleCore.toTopologicalSpace
-/

variable (b : B) (a : F)

/- warning: fiber_bundle_core.open_source' -> FiberBundleCore.open_source' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι), IsOpen.{max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (LocalEquiv.source.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (i : ι), IsOpen.{max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (LocalEquiv.source.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.open_source' FiberBundleCore.open_source'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem open_source' (i : ι) : IsOpen (Z.localTrivAsLocalEquiv i).source :=
  by
  apply TopologicalSpace.GenerateOpen.basic
  simp only [exists_prop, mem_Union, mem_singleton_iff]
  refine' ⟨i, Z.base_set i ×ˢ univ, (Z.is_open_base_set i).Prod isOpen_univ, _⟩
  ext p
  simp only [local_triv_as_local_equiv_apply, prod_mk_mem_set_prod_eq, mem_inter_iff, and_self_iff,
    mem_local_triv_as_local_equiv_source, and_true_iff, mem_univ, mem_preimage]
#align fiber_bundle_core.open_source' FiberBundleCore.open_source'

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
    apply continuousOn_open_of_generateFrom ((Z.is_open_base_set i).Prod isOpen_univ)
    intro t ht
    simp only [exists_prop, mem_Union, mem_singleton_iff] at ht
    obtain ⟨j, s, s_open, ts⟩ :
      ∃ j s,
        IsOpen s ∧
          t = (local_triv_as_local_equiv Z j).source ∩ local_triv_as_local_equiv Z j ⁻¹' s :=
      ht
    rw [ts]
    simp only [LocalEquiv.right_inv, preimage_inter, LocalEquiv.left_inv]
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
    dsimp [LocalEquiv.trans_source]
    rw [← preimage_comp, inter_assoc]
    rfl
  toLocalEquiv := Z.localTrivAsLocalEquiv i
#align fiber_bundle_core.local_triv FiberBundleCore.localTriv
-/

#print FiberBundleCore.localTrivAt /-
/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def localTrivAt (b : B) : Trivialization F (π Z.Fiber) :=
  Z.localTriv (Z.indexAt b)
#align fiber_bundle_core.local_triv_at FiberBundleCore.localTrivAt
-/

/- warning: fiber_bundle_core.local_triv_at_def -> FiberBundleCore.localTrivAt_def is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (b : B), Eq.{max (succ u2) (succ u3) (succ (max u2 u3))} (Trivialization.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z (FiberBundleCore.indexAt.{u1, u2, u3} ι B _inst_2 F _inst_3 Z b)) (FiberBundleCore.localTrivAt.{u1, u2, u3} ι B F _inst_2 _inst_3 Z b)
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (b : B), Eq.{max (succ u3) (succ u2)} (Trivialization.{u3, u2, max u3 u2} B F (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTriv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z (FiberBundleCore.indexAt.{u1, u3, u2} ι B _inst_2 F _inst_3 Z b)) (FiberBundleCore.localTrivAt.{u1, u3, u2} ι B F _inst_2 _inst_3 Z b)
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_at_def FiberBundleCore.localTrivAt_defₓ'. -/
@[simp, mfld_simps]
theorem localTrivAt_def (b : B) : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl
#align fiber_bundle_core.local_triv_at_def FiberBundleCore.localTrivAt_def

/- warning: fiber_bundle_core.continuous_const_section -> FiberBundleCore.continuous_const_section is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (v : F), (forall (i : ι) (j : ι) (x : B), (Membership.Mem.{u2, u2} B (Set.{u2} B) (Set.hasMem.{u2} B) x (Inter.inter.{u2} (Set.{u2} B) (Set.hasInter.{u2} B) (FiberBundleCore.baseSet.{u1, u2, u3} ι B _inst_2 F _inst_3 Z i) (FiberBundleCore.baseSet.{u1, u2, u3} ι B _inst_2 F _inst_3 Z j))) -> (Eq.{succ u3} F (FiberBundleCore.coordChange.{u1, u2, u3} ι B _inst_2 F _inst_3 Z i j x v) v)) -> (Continuous.{u2, max u2 u3} B (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) ((fun (this : B -> (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) => this) (fun (x : B) => Sigma.mk.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) x v)))
but is expected to have type
  forall {ι : Type.{u2}} {B : Type.{u3}} {F : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u1} F] (Z : FiberBundleCore.{u2, u3, u1} ι B _inst_2 F _inst_3) (v : F), (forall (i : ι) (j : ι) (x : B), (Membership.mem.{u3, u3} B (Set.{u3} B) (Set.instMembershipSet.{u3} B) x (Inter.inter.{u3} (Set.{u3} B) (Set.instInterSet.{u3} B) (FiberBundleCore.baseSet.{u2, u3, u1} ι B _inst_2 F _inst_3 Z i) (FiberBundleCore.baseSet.{u2, u3, u1} ι B _inst_2 F _inst_3 Z j))) -> (Eq.{succ u1} F (FiberBundleCore.coordChange.{u2, u3, u1} ι B _inst_2 F _inst_3 Z i j x v) v)) -> (Continuous.{u3, max u3 u1} B (FiberBundleCore.TotalSpace.{u2, u3, u1} ι B F _inst_2 _inst_3 Z) _inst_2 (FiberBundleCore.toTopologicalSpace.{u2, u3, u1} ι B F _inst_2 _inst_3 Z) ([mdata let_fun:1 (fun (this : B -> (FiberBundleCore.TotalSpace.{u2, u3, u1} ι B F _inst_2 _inst_3 Z)) => this) (fun (x : B) => Sigma.mk.{u3, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u2, u3, u1} ι B F _inst_2 _inst_3 Z x) x v)]))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.continuous_const_section FiberBundleCore.continuous_const_sectionₓ'. -/
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
  apply ((Z.local_triv_at x).toLocalHomeomorph.continuousAt_iff_continuousAt_comp_left _).2
  · simp only [(· ∘ ·), mfld_simps]
    apply continuous_at_id.prod
    have : ContinuousOn (fun y : B => v) (Z.base_set (Z.index_at x)) := continuousOn_const
    apply (this.congr _).ContinuousAt A
    intro y hy
    simp only [h, hy, mem_base_set_at, mfld_simps]
  · exact A
#align fiber_bundle_core.continuous_const_section FiberBundleCore.continuous_const_section

/- warning: fiber_bundle_core.local_triv_as_local_equiv_coe -> FiberBundleCore.localTrivAsLocalEquiv_coe is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι), Eq.{succ (max u2 u3)} ((FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) -> (Prod.{u2, u3} B F)) (coeFn.{succ (max u2 u3), succ (max u2 u3)} (LocalEquiv.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F)) (fun (_x : LocalEquiv.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F)) => (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) -> (Prod.{u2, u3} B F)) (LocalEquiv.hasCoeToFun.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F)) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i)) (coeFn.{max (succ u2) (succ u3) (succ (max u2 u3)), max (succ (max u2 u3)) (succ u2) (succ u3)} (Trivialization.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (fun (_x : Trivialization.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) => (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) -> (Prod.{u2, u3} B F)) (Trivialization.hasCoeToFun.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (i : ι), Eq.{max (succ u3) (succ u2)} ((FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) -> (Prod.{u3, u2} B F)) (LocalEquiv.toFun.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i)) (Trivialization.toFun'.{u3, u2, max u3 u2} B F (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.proj.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_as_local_equiv_coe FiberBundleCore.localTrivAsLocalEquiv_coeₓ'. -/
@[simp, mfld_simps]
theorem localTrivAsLocalEquiv_coe : ⇑(Z.localTrivAsLocalEquiv i) = Z.localTriv i :=
  rfl
#align fiber_bundle_core.local_triv_as_local_equiv_coe FiberBundleCore.localTrivAsLocalEquiv_coe

/- warning: fiber_bundle_core.local_triv_as_local_equiv_source -> FiberBundleCore.localTrivAsLocalEquiv_source is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι), Eq.{succ (max u2 u3)} (Set.{max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (LocalEquiv.source.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i)) (LocalEquiv.source.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (i : ι), Eq.{max (succ u3) (succ u2)} (Set.{max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (LocalEquiv.source.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i)) (LocalEquiv.source.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (LocalHomeomorph.toLocalEquiv.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u3, u2, max u3 u2} B F (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i))))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_as_local_equiv_source FiberBundleCore.localTrivAsLocalEquiv_sourceₓ'. -/
@[simp, mfld_simps]
theorem localTrivAsLocalEquiv_source :
    (Z.localTrivAsLocalEquiv i).source = (Z.localTriv i).source :=
  rfl
#align fiber_bundle_core.local_triv_as_local_equiv_source FiberBundleCore.localTrivAsLocalEquiv_source

/- warning: fiber_bundle_core.local_triv_as_local_equiv_target -> FiberBundleCore.localTrivAsLocalEquiv_target is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι), Eq.{succ (max u2 u3)} (Set.{max u2 u3} (Prod.{u2, u3} B F)) (LocalEquiv.target.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i)) (LocalEquiv.target.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (i : ι), Eq.{max (succ u3) (succ u2)} (Set.{max u3 u2} (Prod.{u3, u2} B F)) (LocalEquiv.target.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i)) (LocalEquiv.target.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (LocalHomeomorph.toLocalEquiv.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u3, u2, max u3 u2} B F (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i))))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_as_local_equiv_target FiberBundleCore.localTrivAsLocalEquiv_targetₓ'. -/
@[simp, mfld_simps]
theorem localTrivAsLocalEquiv_target :
    (Z.localTrivAsLocalEquiv i).target = (Z.localTriv i).target :=
  rfl
#align fiber_bundle_core.local_triv_as_local_equiv_target FiberBundleCore.localTrivAsLocalEquiv_target

/- warning: fiber_bundle_core.local_triv_as_local_equiv_symm -> FiberBundleCore.localTrivAsLocalEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι), Eq.{succ (max u2 u3)} (LocalEquiv.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (LocalEquiv.symm.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i)) (LocalEquiv.symm.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (i : ι), Eq.{max (succ u3) (succ u2)} (LocalEquiv.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (LocalEquiv.symm.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.localTrivAsLocalEquiv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i)) (LocalEquiv.symm.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (LocalHomeomorph.toLocalEquiv.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u3, u2, max u3 u2} B F (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i))))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_as_local_equiv_symm FiberBundleCore.localTrivAsLocalEquiv_symmₓ'. -/
@[simp, mfld_simps]
theorem localTrivAsLocalEquiv_symm :
    (Z.localTrivAsLocalEquiv i).symm = (Z.localTriv i).toLocalEquiv.symm :=
  rfl
#align fiber_bundle_core.local_triv_as_local_equiv_symm FiberBundleCore.localTrivAsLocalEquiv_symm

/- warning: fiber_bundle_core.base_set_at -> FiberBundleCore.baseSet_at is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι), Eq.{succ u2} (Set.{u2} B) (FiberBundleCore.baseSet.{u1, u2, u3} ι B _inst_2 F _inst_3 Z i) (Trivialization.baseSet.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))
but is expected to have type
  forall {ι : Type.{u2}} {B : Type.{u3}} {F : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u1} F] (Z : FiberBundleCore.{u2, u3, u1} ι B _inst_2 F _inst_3) (i : ι), Eq.{succ u3} (Set.{u3} B) (FiberBundleCore.baseSet.{u2, u3, u1} ι B _inst_2 F _inst_3 Z i) (Trivialization.baseSet.{u3, u1, max u3 u1} B F (FiberBundleCore.TotalSpace.{u2, u3, u1} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u2, u3, u1} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u2, u3, u1} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u2, u3, u1} ι B F _inst_2 _inst_3 Z i))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.base_set_at FiberBundleCore.baseSet_atₓ'. -/
@[simp, mfld_simps]
theorem baseSet_at : Z.baseSet i = (Z.localTriv i).baseSet :=
  rfl
#align fiber_bundle_core.base_set_at FiberBundleCore.baseSet_at

/- warning: fiber_bundle_core.local_triv_apply -> FiberBundleCore.localTriv_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι) (p : FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z), Eq.{max (succ u2) (succ u3)} (Prod.{u2, u3} B F) (coeFn.{max (succ u2) (succ u3) (succ (max u2 u3)), max (succ (max u2 u3)) (succ u2) (succ u3)} (Trivialization.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (fun (_x : Trivialization.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) => (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) -> (Prod.{u2, u3} B F)) (Trivialization.hasCoeToFun.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i) p) (Prod.mk.{u2, u3} B F (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p) (FiberBundleCore.coordChange.{u1, u2, u3} ι B _inst_2 F _inst_3 Z (FiberBundleCore.indexAt.{u1, u2, u3} ι B _inst_2 F _inst_3 Z (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p)) i (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p) (Sigma.snd.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p)))
but is expected to have type
  forall {ι : Type.{u3}} {B : Type.{u2}} {F : Type.{u1}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u1} F] (Z : FiberBundleCore.{u3, u2, u1} ι B _inst_2 F _inst_3) (i : ι) (p : FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} B F) (Trivialization.toFun'.{u2, u1, max u2 u1} B F (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.proj.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.toTopologicalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u3, u2, u1} ι B F _inst_2 _inst_3 Z i) p) (Prod.mk.{u2, u1} B F (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p) (FiberBundleCore.coordChange.{u3, u2, u1} ι B _inst_2 F _inst_3 Z (FiberBundleCore.indexAt.{u3, u2, u1} ι B _inst_2 F _inst_3 Z (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p)) i (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p) (Sigma.snd.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p)))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_apply FiberBundleCore.localTriv_applyₓ'. -/
@[simp, mfld_simps]
theorem localTriv_apply (p : Z.TotalSpace) :
    (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl
#align fiber_bundle_core.local_triv_apply FiberBundleCore.localTriv_apply

/- warning: fiber_bundle_core.local_triv_at_apply -> FiberBundleCore.localTrivAt_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (p : FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z), Eq.{max (succ u2) (succ u3)} (Prod.{u2, u3} B F) (coeFn.{max (succ u2) (succ u3) (succ (max u2 u3)), max (succ (max u2 u3)) (succ u2) (succ u3)} (Trivialization.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z))) (fun (_x : Trivialization.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z))) => (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) -> (Prod.{u2, u3} B F)) (Trivialization.hasCoeToFun.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u2, u3} ι B F _inst_2 _inst_3 Z (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p)) p) (Prod.mk.{u2, u3} B F (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p) (Sigma.snd.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p))
but is expected to have type
  forall {ι : Type.{u3}} {B : Type.{u2}} {F : Type.{u1}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u1} F] (Z : FiberBundleCore.{u3, u2, u1} ι B _inst_2 F _inst_3) (p : FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z), Eq.{max (succ u2) (succ u1)} (Prod.{u2, u1} B F) (Trivialization.toFun'.{u2, u1, max u2 u1} B F (Bundle.TotalSpace.{u2, u1} B (FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u2, u1} B (FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.toTopologicalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTrivAt.{u3, u2, u1} ι B F _inst_2 _inst_3 Z (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p)) p) (Prod.mk.{u2, u1} B F (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p) (Sigma.snd.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_at_apply FiberBundleCore.localTrivAt_applyₓ'. -/
@[simp, mfld_simps]
theorem localTrivAt_apply (p : Z.TotalSpace) : (Z.localTrivAt p.1) p = ⟨p.1, p.2⟩ := by
  rw [local_triv_at, local_triv_apply, coord_change_self]; exact Z.mem_base_set_at p.1
#align fiber_bundle_core.local_triv_at_apply FiberBundleCore.localTrivAt_apply

/- warning: fiber_bundle_core.local_triv_at_apply_mk -> FiberBundleCore.localTrivAt_apply_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (b : B) (a : F), Eq.{max (succ u2) (succ u3)} (Prod.{u2, u3} B F) (coeFn.{max (succ u2) (succ u3) (succ (max u2 u3)), max (succ (max u2 u3)) (succ u2) (succ u3)} (Trivialization.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z))) (fun (_x : Trivialization.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z))) => (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) -> (Prod.{u2, u3} B F)) (Trivialization.hasCoeToFun.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u2, u3} ι B F _inst_2 _inst_3 Z b) (Sigma.mk.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) b a)) (Prod.mk.{u2, u3} B F b a)
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (b : B) (a : F), Eq.{max (succ u3) (succ u2)} (Prod.{u3, u2} B F) (Trivialization.toFun'.{u3, u2, max u3 u2} B F (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTrivAt.{u1, u3, u2} ι B F _inst_2 _inst_3 Z b) (Sigma.mk.{u3, u2} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z x) b a)) (Prod.mk.{u3, u2} B F b a)
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_at_apply_mk FiberBundleCore.localTrivAt_apply_mkₓ'. -/
@[simp, mfld_simps]
theorem localTrivAt_apply_mk (b : B) (a : F) : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  Z.localTrivAt_apply _
#align fiber_bundle_core.local_triv_at_apply_mk FiberBundleCore.localTrivAt_apply_mk

/- warning: fiber_bundle_core.mem_local_triv_source -> FiberBundleCore.mem_localTriv_source is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι) (p : FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z), Iff (Membership.Mem.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Set.{max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (Set.hasMem.{max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) p (LocalEquiv.source.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))))) (Membership.Mem.{u2, u2} B (Set.{u2} B) (Set.hasMem.{u2} B) (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p) (Trivialization.baseSet.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i)))
but is expected to have type
  forall {ι : Type.{u3}} {B : Type.{u2}} {F : Type.{u1}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u1} F] (Z : FiberBundleCore.{u3, u2, u1} ι B _inst_2 F _inst_3) (i : ι) (p : FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z), Iff (Membership.mem.{max u2 u1, max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (Set.{max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) (Set.instMembershipSet.{max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) p (LocalEquiv.source.{max u2 u1, max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u1} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u1, max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u1} B F) (FiberBundleCore.toTopologicalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (instTopologicalSpaceProd.{u2, u1} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u1, max u2 u1} B F (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u3, u2, u1} ι B F _inst_2 _inst_3 Z i))))) (Membership.mem.{u2, u2} B (Set.{u2} B) (Set.instMembershipSet.{u2} B) (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p) (Trivialization.baseSet.{u2, u1, max u2 u1} B F (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u3, u2, u1} ι B F _inst_2 _inst_3 Z i)))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.mem_local_triv_source FiberBundleCore.mem_localTriv_sourceₓ'. -/
@[simp, mfld_simps]
theorem mem_localTriv_source (p : Z.TotalSpace) :
    p ∈ (Z.localTriv i).source ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Iff.rfl
#align fiber_bundle_core.mem_local_triv_source FiberBundleCore.mem_localTriv_source

/- warning: fiber_bundle_core.mem_local_triv_at_source -> FiberBundleCore.mem_localTrivAt_source is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (p : FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (b : B), Iff (Membership.Mem.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Set.{max u2 u3} (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z))) (Set.hasMem.{max u2 u3} (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z))) p (LocalEquiv.source.{max u2 u3, max u2 u3} (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (Prod.{u2, u3} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u3, max u2 u3} (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (Prod.{u2, u3} B F) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u2, u3} ι B F _inst_2 _inst_3 Z b))))) (Membership.Mem.{u2, u2} B (Set.{u2} B) (Set.hasMem.{u2} B) (Sigma.fst.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) p) (Trivialization.baseSet.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u2, u3} ι B F _inst_2 _inst_3 Z b)))
but is expected to have type
  forall {ι : Type.{u3}} {B : Type.{u2}} {F : Type.{u1}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u1} F] (Z : FiberBundleCore.{u3, u2, u1} ι B _inst_2 F _inst_3) (p : FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (b : B), Iff (Membership.mem.{max u2 u1, max u2 u1} (FiberBundleCore.TotalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (Set.{max u2 u1} (Bundle.TotalSpace.{u2, u1} B (FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z))) (Set.instMembershipSet.{max u2 u1} (Bundle.TotalSpace.{u2, u1} B (FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z))) p (LocalEquiv.source.{max u2 u1, max u2 u1} (Bundle.TotalSpace.{u2, u1} B (FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) (Prod.{u2, u1} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u1, max u2 u1} (Bundle.TotalSpace.{u2, u1} B (FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) (Prod.{u2, u1} B F) (FiberBundleCore.toTopologicalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (instTopologicalSpaceProd.{u2, u1} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u1, max u2 u1} B F (Bundle.TotalSpace.{u2, u1} B (FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u1} B (FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u3, u2, u1} ι B F _inst_2 _inst_3 Z b))))) (Membership.mem.{u2, u2} B (Set.{u2} B) (Set.instMembershipSet.{u2} B) (Sigma.fst.{u2, u1} B (fun (x : B) => FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z x) p) (Trivialization.baseSet.{u2, u1, max u2 u1} B F (Bundle.TotalSpace.{u2, u1} B (FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u3, u2, u1} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u1} B (FiberBundleCore.Fiber.{u3, u2, u1} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u3, u2, u1} ι B F _inst_2 _inst_3 Z b)))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.mem_local_triv_at_source FiberBundleCore.mem_localTrivAt_sourceₓ'. -/
@[simp, mfld_simps]
theorem mem_localTrivAt_source (p : Z.TotalSpace) (b : B) :
    p ∈ (Z.localTrivAt b).source ↔ p.1 ∈ (Z.localTrivAt b).baseSet :=
  Iff.rfl
#align fiber_bundle_core.mem_local_triv_at_source FiberBundleCore.mem_localTrivAt_source

/- warning: fiber_bundle_core.mem_source_at -> FiberBundleCore.mem_source_at is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (b : B) (a : F), Membership.Mem.{max u2 u3, max u2 u3} (Sigma.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x)) (Set.{max u2 u3} (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z))) (Set.hasMem.{max u2 u3} (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z))) (Sigma.mk.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) b a) (LocalEquiv.source.{max u2 u3, max u2 u3} (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (Prod.{u2, u3} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u3, max u2 u3} (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (Prod.{u2, u3} B F) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u2, u3} ι B F _inst_2 _inst_3 Z b))))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (b : B) (a : F), Membership.mem.{max u3 u2, max u3 u2} (Sigma.{u3, u2} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z x)) (Set.{max u3 u2} (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z))) (Set.instMembershipSet.{max u3 u2} (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z))) (Sigma.mk.{u3, u2} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z x) b a) (LocalEquiv.source.{max u3 u2, max u3 u2} (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (Prod.{u3, u2} B F) (LocalHomeomorph.toLocalEquiv.{max u3 u2, max u3 u2} (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (Prod.{u3, u2} B F) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u3, u2, max u3 u2} B F (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u3, u2} ι B F _inst_2 _inst_3 Z b))))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.mem_source_at FiberBundleCore.mem_source_atₓ'. -/
@[simp, mfld_simps]
theorem mem_source_at : (⟨b, a⟩ : Z.TotalSpace) ∈ (Z.localTrivAt b).source := by
  rw [local_triv_at, mem_local_triv_source]; exact Z.mem_base_set_at b
#align fiber_bundle_core.mem_source_at FiberBundleCore.mem_source_at

/- warning: fiber_bundle_core.mem_local_triv_target -> FiberBundleCore.mem_localTriv_target is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι) (p : Prod.{u2, u3} B F), Iff (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Set.{max u2 u3} (Prod.{u2, u3} B F)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} B F)) p (LocalEquiv.target.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))))) (Membership.Mem.{u2, u2} B (Set.{u2} B) (Set.hasMem.{u2} B) (Prod.fst.{u2, u3} B F p) (Trivialization.baseSet.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i)))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (i : ι) (p : Prod.{u3, u2} B F), Iff (Membership.mem.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (Set.{max u3 u2} (Prod.{u3, u2} B F)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} B F)) p (LocalEquiv.target.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (LocalHomeomorph.toLocalEquiv.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u3, u2, max u3 u2} B F (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i))))) (Membership.mem.{u3, u3} B (Set.{u3} B) (Set.instMembershipSet.{u3} B) (Prod.fst.{u3, u2} B F p) (Trivialization.baseSet.{u3, u2, max u3 u2} B F (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i)))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.mem_local_triv_target FiberBundleCore.mem_localTriv_targetₓ'. -/
@[simp, mfld_simps]
theorem mem_localTriv_target (p : B × F) :
    p ∈ (Z.localTriv i).target ↔ p.1 ∈ (Z.localTriv i).baseSet :=
  Trivialization.mem_target _
#align fiber_bundle_core.mem_local_triv_target FiberBundleCore.mem_localTriv_target

/- warning: fiber_bundle_core.mem_local_triv_at_target -> FiberBundleCore.mem_localTrivAt_target is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (p : Prod.{u2, u3} B F) (b : B), Iff (Membership.Mem.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (Set.{max u2 u3} (Prod.{u2, u3} B F)) (Set.hasMem.{max u2 u3} (Prod.{u2, u3} B F)) p (LocalEquiv.target.{max u2 u3, max u2 u3} (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (Prod.{u2, u3} B F) (LocalHomeomorph.toLocalEquiv.{max u2 u3, max u2 u3} (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (Prod.{u2, u3} B F) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u2, u3} ι B F _inst_2 _inst_3 Z b))))) (Membership.Mem.{u2, u2} B (Set.{u2} B) (Set.hasMem.{u2} B) (Prod.fst.{u2, u3} B F p) (Trivialization.baseSet.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u2, u3} ι B F _inst_2 _inst_3 Z b)))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (p : Prod.{u3, u2} B F) (b : B), Iff (Membership.mem.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (Set.{max u3 u2} (Prod.{u3, u2} B F)) (Set.instMembershipSet.{max u3 u2} (Prod.{u3, u2} B F)) p (LocalEquiv.target.{max u3 u2, max u3 u2} (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (Prod.{u3, u2} B F) (LocalHomeomorph.toLocalEquiv.{max u3 u2, max u3 u2} (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (Prod.{u3, u2} B F) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u3, u2, max u3 u2} B F (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u3, u2} ι B F _inst_2 _inst_3 Z b))))) (Membership.mem.{u3, u3} B (Set.{u3} B) (Set.instMembershipSet.{u3} B) (Prod.fst.{u3, u2} B F p) (Trivialization.baseSet.{u3, u2, max u3 u2} B F (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u3, u2} ι B F _inst_2 _inst_3 Z b)))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.mem_local_triv_at_target FiberBundleCore.mem_localTrivAt_targetₓ'. -/
@[simp, mfld_simps]
theorem mem_localTrivAt_target (p : B × F) (b : B) :
    p ∈ (Z.localTrivAt b).target ↔ p.1 ∈ (Z.localTrivAt b).baseSet :=
  Trivialization.mem_target _
#align fiber_bundle_core.mem_local_triv_at_target FiberBundleCore.mem_localTrivAt_target

/- warning: fiber_bundle_core.local_triv_symm_apply -> FiberBundleCore.localTriv_symm_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (i : ι) (p : Prod.{u2, u3} B F), Eq.{max (succ u2) (succ u3)} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (coeFn.{succ (max u2 u3), succ (max u2 u3)} (LocalHomeomorph.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (fun (_x : LocalHomeomorph.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) => (Prod.{u2, u3} B F) -> (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (LocalHomeomorph.hasCoeToFun.{max u2 u3, max u2 u3} (Prod.{u2, u3} B F) (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (LocalHomeomorph.symm.{max u2 u3, max u2 u3} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.{u2, u3} B F) (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Prod.topologicalSpace.{u2, u3} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u2, u3, max u2 u3} B F (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u2, u3} ι B F _inst_2 _inst_3 Z i))) p) (Sigma.mk.{u2, u3} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z x) (Prod.fst.{u2, u3} B F p) (FiberBundleCore.coordChange.{u1, u2, u3} ι B _inst_2 F _inst_3 Z i (FiberBundleCore.indexAt.{u1, u2, u3} ι B _inst_2 F _inst_3 Z (Prod.fst.{u2, u3} B F p)) (Prod.fst.{u2, u3} B F p) (Prod.snd.{u2, u3} B F p)))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (i : ι) (p : Prod.{u3, u2} B F), Eq.{max (succ u3) (succ u2)} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (LocalHomeomorph.toFun'.{max u3 u2, max u3 u2} (Prod.{u3, u2} B F) (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (LocalHomeomorph.symm.{max u3 u2, max u3 u2} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Prod.{u3, u2} B F) (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (Trivialization.toLocalHomeomorph.{u3, u2, max u3 u2} B F (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.proj.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (FiberBundleCore.localTriv.{u1, u3, u2} ι B F _inst_2 _inst_3 Z i))) p) (Sigma.mk.{u3, u2} B (fun (x : B) => FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z x) (Prod.fst.{u3, u2} B F p) (FiberBundleCore.coordChange.{u1, u3, u2} ι B _inst_2 F _inst_3 Z i (FiberBundleCore.indexAt.{u1, u3, u2} ι B _inst_2 F _inst_3 Z (Prod.fst.{u3, u2} B F p)) (Prod.fst.{u3, u2} B F p) (Prod.snd.{u3, u2} B F p)))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.local_triv_symm_apply FiberBundleCore.localTriv_symm_applyₓ'. -/
@[simp, mfld_simps]
theorem localTriv_symm_apply (p : B × F) :
    (Z.localTriv i).toLocalHomeomorph.symm p = ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl
#align fiber_bundle_core.local_triv_symm_apply FiberBundleCore.localTriv_symm_apply

/- warning: fiber_bundle_core.mem_local_triv_at_base_set -> FiberBundleCore.mem_localTrivAt_baseSet is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3) (b : B), Membership.Mem.{u2, u2} B (Set.{u2} B) (Set.hasMem.{u2} B) b (Trivialization.baseSet.{u2, u3, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u2, u3} B (FiberBundleCore.Fiber.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u2, u3} ι B F _inst_2 _inst_3 Z b))
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3) (b : B), Membership.mem.{u3, u3} B (Set.{u3} B) (Set.instMembershipSet.{u3} B) b (Trivialization.baseSet.{u3, u2, max u3 u2} B F (Bundle.TotalSpace.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) _inst_2 _inst_3 (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) (Bundle.TotalSpace.proj.{u3, u2} B (FiberBundleCore.Fiber.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)) (FiberBundleCore.localTrivAt.{u1, u3, u2} ι B F _inst_2 _inst_3 Z b))
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.mem_local_triv_at_base_set FiberBundleCore.mem_localTrivAt_baseSetₓ'. -/
@[simp, mfld_simps]
theorem mem_localTrivAt_baseSet (b : B) : b ∈ (Z.localTrivAt b).baseSet := by
  rw [local_triv_at, ← base_set_at]; exact Z.mem_base_set_at b
#align fiber_bundle_core.mem_local_triv_at_base_set FiberBundleCore.mem_localTrivAt_baseSet

#print FiberBundleCore.continuous_totalSpaceMk /-
/-- The inclusion of a fiber into the total space is a continuous map. -/
@[continuity]
theorem continuous_totalSpaceMk (b : B) :
    Continuous (totalSpaceMk b : Z.Fiber b → Bundle.TotalSpace Z.Fiber) :=
  by
  rw [continuous_iff_le_induced, FiberBundleCore.toTopologicalSpace]
  apply le_induced_generateFrom
  simp only [total_space_mk, mem_Union, mem_singleton_iff, local_triv_as_local_equiv_source,
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
  totalSpaceMk_inducing b :=
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
        simp only [total_space_mk]
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

/- warning: fiber_bundle_core.continuous_proj -> FiberBundleCore.continuous_proj is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3), Continuous.{max u2 u3, u2} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) B (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3), Continuous.{max u3 u2, u3} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) B (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) _inst_2 (FiberBundleCore.proj.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.continuous_proj FiberBundleCore.continuous_projₓ'. -/
/-- The projection on the base of a fiber bundle created from core is continuous -/
theorem continuous_proj : Continuous Z.proj :=
  continuous_proj F Z.Fiber
#align fiber_bundle_core.continuous_proj FiberBundleCore.continuous_proj

/- warning: fiber_bundle_core.is_open_map_proj -> FiberBundleCore.isOpenMap_proj is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {B : Type.{u2}} {F : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u3} F] (Z : FiberBundleCore.{u1, u2, u3} ι B _inst_2 F _inst_3), IsOpenMap.{max u2 u3, u2} (FiberBundleCore.TotalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) B (FiberBundleCore.toTopologicalSpace.{u1, u2, u3} ι B F _inst_2 _inst_3 Z) _inst_2 (FiberBundleCore.proj.{u1, u2, u3} ι B F _inst_2 _inst_3 Z)
but is expected to have type
  forall {ι : Type.{u1}} {B : Type.{u3}} {F : Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (Z : FiberBundleCore.{u1, u3, u2} ι B _inst_2 F _inst_3), IsOpenMap.{max u3 u2, u3} (FiberBundleCore.TotalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) B (FiberBundleCore.toTopologicalSpace.{u1, u3, u2} ι B F _inst_2 _inst_3 Z) _inst_2 (FiberBundleCore.proj.{u1, u3, u2} ι B F _inst_2 _inst_3 Z)
Case conversion may be inaccurate. Consider using '#align fiber_bundle_core.is_open_map_proj FiberBundleCore.isOpenMap_projₓ'. -/
/-- The projection on the base of a fiber bundle created from core is an open map -/
theorem isOpenMap_proj : IsOpenMap Z.proj :=
  isOpenMap_proj F Z.Fiber
#align fiber_bundle_core.is_open_map_proj FiberBundleCore.isOpenMap_proj

end FiberBundleCore

/-! ### Prebundle construction for constructing fiber bundles -/


variable (F) (E : B → Type _) [TopologicalSpace B] [TopologicalSpace F]

#print FiberPrebundle /-
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (e e' «expr ∈ » pretrivialization_atlas) -/
/-- This structure permits to define a fiber bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphism and hence local trivializations. -/
@[nolint has_nonempty_instance]
structure FiberPrebundle where
  pretrivializationAtlas : Set (Pretrivialization F (π E))
  pretrivializationAt : B → Pretrivialization F (π E)
  mem_base_pretrivializationAt : ∀ x : B, x ∈ (pretrivialization_at x).baseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas
  continuous_triv_change :
    ∀ (e) (_ : e ∈ pretrivialization_atlas) (e') (_ : e' ∈ pretrivialization_atlas),
      ContinuousOn (e ∘ e'.toLocalEquiv.symm) (e'.target ∩ e'.toLocalEquiv.symm ⁻¹' e.source)
#align fiber_prebundle FiberPrebundle
-/

namespace FiberPrebundle

variable {F E} (a : FiberPrebundle F E) {e : Pretrivialization F (π E)}

#print FiberPrebundle.totalSpaceTopology /-
/-- Topology on the total space that will make the prebundle into a bundle. -/
def totalSpaceTopology (a : FiberPrebundle F E) : TopologicalSpace (TotalSpace E) :=
  ⨆ (e : Pretrivialization F (π E)) (he : e ∈ a.pretrivializationAtlas),
    coinduced e.setSymm Subtype.topologicalSpace
#align fiber_prebundle.total_space_topology FiberPrebundle.totalSpaceTopology
-/

/- warning: fiber_prebundle.continuous_symm_of_mem_pretrivialization_atlas -> FiberPrebundle.continuous_symm_of_mem_pretrivializationAtlas is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u1, u2, u3} B F E _inst_2 _inst_3) {e : Pretrivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E)}, (Membership.Mem.{max u1 u2 u1 u3, max u1 u2 u1 u3} (Pretrivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E)) (Set.{max u1 u2 u1 u3} (Pretrivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E))) (Set.hasMem.{max u1 u2 u1 u3} (Pretrivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E))) e (FiberPrebundle.pretrivializationAtlas.{u1, u2, u3} B F E _inst_2 _inst_3 a)) -> (ContinuousOn.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E) (Prod.topologicalSpace.{u1, u2} B F _inst_2 _inst_3) (FiberPrebundle.totalSpaceTopology.{u1, u2, u3} B F E _inst_2 _inst_3 a) (coeFn.{max (succ (max u1 u2)) (succ (max u1 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (LocalEquiv.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E)) (fun (_x : LocalEquiv.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E)) => (Prod.{u1, u2} B F) -> (Bundle.TotalSpace.{u1, u3} B E)) (LocalEquiv.hasCoeToFun.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E)) (LocalEquiv.symm.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) (Pretrivialization.toLocalEquiv.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) e))) (LocalEquiv.target.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) (Pretrivialization.toLocalEquiv.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) e)))
but is expected to have type
  forall {B : Type.{u3}} {F : Type.{u2}} {E : B -> Type.{u1}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u3, u2, u1} B F E _inst_2 _inst_3) {e : Pretrivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E)}, (Membership.mem.{max (max u3 u2) u1, max (max u3 u2) u1} (Pretrivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E)) (Set.{max (max (max u3 u1) u2) u3} (Pretrivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E))) (Set.instMembershipSet.{max (max u3 u2) u1} (Pretrivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E))) e (FiberPrebundle.pretrivializationAtlas.{u3, u2, u1} B F E _inst_2 _inst_3 a)) -> (ContinuousOn.{max u3 u2, max u3 u1} (Prod.{u3, u2} B F) (Bundle.TotalSpace.{u3, u1} B E) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (FiberPrebundle.totalSpaceTopology.{u3, u2, u1} B F E _inst_2 _inst_3 a) (LocalEquiv.toFun.{max u3 u2, max u3 u1} (Prod.{u3, u2} B F) (Bundle.TotalSpace.{u3, u1} B E) (LocalEquiv.symm.{max u3 u1, max u3 u2} (Bundle.TotalSpace.{u3, u1} B E) (Prod.{u3, u2} B F) (Pretrivialization.toLocalEquiv.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E) e))) (LocalEquiv.target.{max u3 u1, max u3 u2} (Bundle.TotalSpace.{u3, u1} B E) (Prod.{u3, u2} B F) (Pretrivialization.toLocalEquiv.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E) e)))
Case conversion may be inaccurate. Consider using '#align fiber_prebundle.continuous_symm_of_mem_pretrivialization_atlas FiberPrebundle.continuous_symm_of_mem_pretrivializationAtlasₓ'. -/
theorem continuous_symm_of_mem_pretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @ContinuousOn _ _ _ a.totalSpaceTopology e.toLocalEquiv.symm e.target :=
  by
  refine'
    id fun z H =>
      id fun U h => preimage_nhdsWithin_coinduced' H e.open_target (le_def.1 (nhds_mono _) U h)
  exact le_iSup₂ e he
#align fiber_prebundle.continuous_symm_of_mem_pretrivialization_atlas FiberPrebundle.continuous_symm_of_mem_pretrivializationAtlas

/- warning: fiber_prebundle.is_open_source -> FiberPrebundle.isOpen_source is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u1, u2, u3} B F E _inst_2 _inst_3) (e : Pretrivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E)), IsOpen.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E) (FiberPrebundle.totalSpaceTopology.{u1, u2, u3} B F E _inst_2 _inst_3 a) (LocalEquiv.source.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) (Pretrivialization.toLocalEquiv.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) e))
but is expected to have type
  forall {B : Type.{u3}} {F : Type.{u2}} {E : B -> Type.{u1}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u3, u2, u1} B F E _inst_2 _inst_3) (e : Pretrivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E)), IsOpen.{max u3 u1} (Bundle.TotalSpace.{u3, u1} B E) (FiberPrebundle.totalSpaceTopology.{u3, u2, u1} B F E _inst_2 _inst_3 a) (LocalEquiv.source.{max u3 u1, max u3 u2} (Bundle.TotalSpace.{u3, u1} B E) (Prod.{u3, u2} B F) (Pretrivialization.toLocalEquiv.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E) e))
Case conversion may be inaccurate. Consider using '#align fiber_prebundle.is_open_source FiberPrebundle.isOpen_sourceₓ'. -/
theorem isOpen_source (e : Pretrivialization F (π E)) : is_open[a.totalSpaceTopology] e.source :=
  by
  letI := a.total_space_topology
  refine' is_open_supr_iff.mpr fun e' => _
  refine' is_open_supr_iff.mpr fun he' => _
  refine' is_open_coinduced.mpr (is_open_induced_iff.mpr ⟨e.target, e.open_target, _⟩)
  rw [Pretrivialization.setSymm, restrict, e.target_eq, e.source_eq, preimage_comp,
    Subtype.preimage_coe_eq_preimage_coe_iff, e'.target_eq, prod_inter_prod, inter_univ,
    Pretrivialization.preimage_symm_proj_inter]
#align fiber_prebundle.is_open_source FiberPrebundle.isOpen_source

/- warning: fiber_prebundle.is_open_target_of_mem_pretrivialization_atlas_inter -> FiberPrebundle.isOpen_target_of_mem_pretrivializationAtlas_inter is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u1, u2, u3} B F E _inst_2 _inst_3) (e : Pretrivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E)) (e' : Pretrivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E)), (Membership.Mem.{max u1 u2 u1 u3, max u1 u2 u1 u3} (Pretrivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E)) (Set.{max u1 u2 u1 u3} (Pretrivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E))) (Set.hasMem.{max u1 u2 u1 u3} (Pretrivialization.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E))) e' (FiberPrebundle.pretrivializationAtlas.{u1, u2, u3} B F E _inst_2 _inst_3 a)) -> (IsOpen.{max u1 u2} (Prod.{u1, u2} B F) (Prod.topologicalSpace.{u1, u2} B F _inst_2 _inst_3) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} B F)) (Set.hasInter.{max u1 u2} (Prod.{u1, u2} B F)) (LocalEquiv.target.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) (Pretrivialization.toLocalEquiv.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) e')) (Set.preimage.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E) (coeFn.{max (succ (max u1 u2)) (succ (max u1 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (LocalEquiv.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E)) (fun (_x : LocalEquiv.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E)) => (Prod.{u1, u2} B F) -> (Bundle.TotalSpace.{u1, u3} B E)) (LocalEquiv.hasCoeToFun.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E)) (LocalEquiv.symm.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) (Pretrivialization.toLocalEquiv.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) e'))) (LocalEquiv.source.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) (Pretrivialization.toLocalEquiv.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) e)))))
but is expected to have type
  forall {B : Type.{u3}} {F : Type.{u2}} {E : B -> Type.{u1}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u3, u2, u1} B F E _inst_2 _inst_3) (e : Pretrivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E)) (e' : Pretrivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E)), (Membership.mem.{max (max u3 u2) u1, max (max u3 u2) u1} (Pretrivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E)) (Set.{max (max (max u3 u1) u2) u3} (Pretrivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E))) (Set.instMembershipSet.{max (max u3 u2) u1} (Pretrivialization.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E))) e' (FiberPrebundle.pretrivializationAtlas.{u3, u2, u1} B F E _inst_2 _inst_3 a)) -> (IsOpen.{max u3 u2} (Prod.{u3, u2} B F) (instTopologicalSpaceProd.{u3, u2} B F _inst_2 _inst_3) (Inter.inter.{max u3 u2} (Set.{max u3 u2} (Prod.{u3, u2} B F)) (Set.instInterSet.{max u3 u2} (Prod.{u3, u2} B F)) (LocalEquiv.target.{max u3 u1, max u3 u2} (Bundle.TotalSpace.{u3, u1} B E) (Prod.{u3, u2} B F) (Pretrivialization.toLocalEquiv.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E) e')) (Set.preimage.{max u3 u2, max u3 u1} (Prod.{u3, u2} B F) (Bundle.TotalSpace.{u3, u1} B E) (LocalEquiv.toFun.{max u3 u2, max u3 u1} (Prod.{u3, u2} B F) (Bundle.TotalSpace.{u3, u1} B E) (LocalEquiv.symm.{max u3 u1, max u3 u2} (Bundle.TotalSpace.{u3, u1} B E) (Prod.{u3, u2} B F) (Pretrivialization.toLocalEquiv.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E) e'))) (LocalEquiv.source.{max u3 u1, max u3 u2} (Bundle.TotalSpace.{u3, u1} B E) (Prod.{u3, u2} B F) (Pretrivialization.toLocalEquiv.{u3, u2, max u3 u1} B F (Bundle.TotalSpace.{u3, u1} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u1} B E) e)))))
Case conversion may be inaccurate. Consider using '#align fiber_prebundle.is_open_target_of_mem_pretrivialization_atlas_inter FiberPrebundle.isOpen_target_of_mem_pretrivializationAtlas_interₓ'. -/
theorem isOpen_target_of_mem_pretrivializationAtlas_inter (e e' : Pretrivialization F (π E))
    (he' : e' ∈ a.pretrivializationAtlas) :
    IsOpen (e'.toLocalEquiv.target ∩ e'.toLocalEquiv.symm ⁻¹' e.source) :=
  by
  letI := a.total_space_topology
  obtain ⟨u, hu1, hu2⟩ :=
    continuous_on_iff'.mp (a.continuous_symm_of_mem_pretrivialization_atlas he') e.source
      (a.is_open_source e)
  rw [inter_comm, hu2]
  exact hu1.inter e'.open_target
#align fiber_prebundle.is_open_target_of_mem_pretrivialization_atlas_inter FiberPrebundle.isOpen_target_of_mem_pretrivializationAtlas_inter

#print FiberPrebundle.trivializationOfMemPretrivializationAtlas /-
/-- Promotion from a `pretrivialization` to a `trivialization`. -/
def trivializationOfMemPretrivializationAtlas (he : e ∈ a.pretrivializationAtlas) :
    @Trivialization B F _ _ _ a.totalSpaceTopology (π E) :=
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

/- warning: fiber_prebundle.mem_trivialization_at_source -> FiberPrebundle.mem_pretrivializationAt_source is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u1, u2, u3} B F E _inst_2 _inst_3) (b : B) (x : E b), Membership.Mem.{max u1 u3, max u1 u3} (Bundle.TotalSpace.{u1, u3} B (fun (b : B) => E b)) (Set.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)) (Set.hasMem.{max u1 u3} (Bundle.TotalSpace.{u1, u3} B E)) (Bundle.totalSpaceMk.{u1, u3} B (fun (b : B) => E b) b x) (LocalEquiv.source.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) (Pretrivialization.toLocalEquiv.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) (FiberPrebundle.pretrivializationAt.{u1, u2, u3} B F E _inst_2 _inst_3 a b)))
but is expected to have type
  forall {B : Type.{u2}} {F : Type.{u1}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u1} F] (a : FiberPrebundle.{u2, u1, u3} B F E _inst_2 _inst_3) (b : B) (x : E b), Membership.mem.{max u3 u2, max u2 u3} (Bundle.TotalSpace.{u2, u3} B E) (Set.{max u2 u3} (Bundle.TotalSpace.{u2, u3} B E)) (Set.instMembershipSet.{max u2 u3} (Bundle.TotalSpace.{u2, u3} B E)) (Bundle.totalSpaceMk.{u2, u3} B E b x) (LocalEquiv.source.{max u2 u3, max u2 u1} (Bundle.TotalSpace.{u2, u3} B E) (Prod.{u2, u1} B F) (Pretrivialization.toLocalEquiv.{u2, u1, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u2, u3} B E) (FiberPrebundle.pretrivializationAt.{u2, u1, u3} B F E _inst_2 _inst_3 a b)))
Case conversion may be inaccurate. Consider using '#align fiber_prebundle.mem_trivialization_at_source FiberPrebundle.mem_pretrivializationAt_sourceₓ'. -/
theorem mem_pretrivializationAt_source (b : B) (x : E b) :
    totalSpaceMk b x ∈ (a.pretrivializationAt b).source :=
  by
  simp only [(a.pretrivialization_at b).source_eq, mem_preimage, total_space.proj]
  exact a.mem_base_pretrivialization_at b
#align fiber_prebundle.mem_trivialization_at_source FiberPrebundle.mem_pretrivializationAt_source

/- warning: fiber_prebundle.total_space_mk_preimage_source -> FiberPrebundle.totalSpaceMk_preimage_source is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u1, u2, u3} B F E _inst_2 _inst_3) (b : B), Eq.{succ u3} (Set.{u3} (E b)) (Set.preimage.{u3, max u1 u3} (E b) (Bundle.TotalSpace.{u1, u3} B E) (Bundle.totalSpaceMk.{u1, u3} B E b) (LocalEquiv.source.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) (Pretrivialization.toLocalEquiv.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) (FiberPrebundle.pretrivializationAt.{u1, u2, u3} B F E _inst_2 _inst_3 a b)))) (Set.univ.{u3} (E b))
but is expected to have type
  forall {B : Type.{u2}} {F : Type.{u1}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u1} F] (a : FiberPrebundle.{u2, u1, u3} B F E _inst_2 _inst_3) (b : B), Eq.{succ u3} (Set.{u3} (E b)) (Set.preimage.{u3, max u2 u3} (E b) (Bundle.TotalSpace.{u2, u3} B E) (Bundle.totalSpaceMk.{u2, u3} B E b) (LocalEquiv.source.{max u2 u3, max u2 u1} (Bundle.TotalSpace.{u2, u3} B E) (Prod.{u2, u1} B F) (Pretrivialization.toLocalEquiv.{u2, u1, max u2 u3} B F (Bundle.TotalSpace.{u2, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u2, u3} B E) (FiberPrebundle.pretrivializationAt.{u2, u1, u3} B F E _inst_2 _inst_3 a b)))) (Set.univ.{u3} (E b))
Case conversion may be inaccurate. Consider using '#align fiber_prebundle.total_space_mk_preimage_source FiberPrebundle.totalSpaceMk_preimage_sourceₓ'. -/
@[simp]
theorem totalSpaceMk_preimage_source (b : B) :
    totalSpaceMk b ⁻¹' (a.pretrivializationAt b).source = univ :=
  by
  apply eq_univ_of_univ_subset
  rw [(a.pretrivialization_at b).source_eq, ← preimage_comp, Function.comp]
  simp only [total_space.proj]
  rw [preimage_const_of_mem _]
  exact a.mem_base_pretrivialization_at b
#align fiber_prebundle.total_space_mk_preimage_source FiberPrebundle.totalSpaceMk_preimage_source

#print FiberPrebundle.fiberTopology /-
/-- Topology on the fibers `E b` induced by the map `E b → E.total_space`. -/
def fiberTopology (b : B) : TopologicalSpace (E b) :=
  TopologicalSpace.induced (totalSpaceMk b) a.totalSpaceTopology
#align fiber_prebundle.fiber_topology FiberPrebundle.fiberTopology
-/

/- warning: fiber_prebundle.inducing_total_space_mk -> FiberPrebundle.inducing_totalSpaceMk is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u1, u2, u3} B F E _inst_2 _inst_3) (b : B), Inducing.{u3, max u1 u3} (E b) (Bundle.TotalSpace.{u1, u3} B E) (FiberPrebundle.fiberTopology.{u1, u2, u3} B F E _inst_2 _inst_3 a b) (FiberPrebundle.totalSpaceTopology.{u1, u2, u3} B F E _inst_2 _inst_3 a) (Bundle.totalSpaceMk.{u1, u3} B E b)
but is expected to have type
  forall {B : Type.{u2}} {F : Type.{u1}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u1} F] (a : FiberPrebundle.{u2, u1, u3} B F E _inst_2 _inst_3) (b : B), Inducing.{u3, max u2 u3} (E b) (Bundle.TotalSpace.{u2, u3} B E) (FiberPrebundle.fiberTopology.{u2, u1, u3} B F E _inst_2 _inst_3 a b) (FiberPrebundle.totalSpaceTopology.{u2, u1, u3} B F E _inst_2 _inst_3 a) (Bundle.totalSpaceMk.{u2, u3} B E b)
Case conversion may be inaccurate. Consider using '#align fiber_prebundle.inducing_total_space_mk FiberPrebundle.inducing_totalSpaceMkₓ'. -/
@[continuity]
theorem inducing_totalSpaceMk (b : B) :
    @Inducing _ _ (a.fiberTopology b) a.totalSpaceTopology (totalSpaceMk b) := by
  letI := a.total_space_topology; letI := a.fiber_topology b; exact ⟨rfl⟩
#align fiber_prebundle.inducing_total_space_mk FiberPrebundle.inducing_totalSpaceMk

/- warning: fiber_prebundle.continuous_total_space_mk -> FiberPrebundle.continuous_totalSpaceMk is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u1, u2, u3} B F E _inst_2 _inst_3) (b : B), Continuous.{u3, max u1 u3} (E b) (Bundle.TotalSpace.{u1, u3} B E) (FiberPrebundle.fiberTopology.{u1, u2, u3} B F E _inst_2 _inst_3 a b) (FiberPrebundle.totalSpaceTopology.{u1, u2, u3} B F E _inst_2 _inst_3 a) (Bundle.totalSpaceMk.{u1, u3} B E b)
but is expected to have type
  forall {B : Type.{u2}} {F : Type.{u1}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u2} B] [_inst_3 : TopologicalSpace.{u1} F] (a : FiberPrebundle.{u2, u1, u3} B F E _inst_2 _inst_3) (b : B), Continuous.{u3, max u2 u3} (E b) (Bundle.TotalSpace.{u2, u3} B E) (FiberPrebundle.fiberTopology.{u2, u1, u3} B F E _inst_2 _inst_3 a b) (FiberPrebundle.totalSpaceTopology.{u2, u1, u3} B F E _inst_2 _inst_3 a) (Bundle.totalSpaceMk.{u2, u3} B E b)
Case conversion may be inaccurate. Consider using '#align fiber_prebundle.continuous_total_space_mk FiberPrebundle.continuous_totalSpaceMkₓ'. -/
@[continuity]
theorem continuous_totalSpaceMk (b : B) :
    @Continuous _ _ (a.fiberTopology b) a.totalSpaceTopology (totalSpaceMk b) :=
  by
  letI := a.total_space_topology; letI := a.fiber_topology b
  exact (a.inducing_total_space_mk b).Continuous
#align fiber_prebundle.continuous_total_space_mk FiberPrebundle.continuous_totalSpaceMk

#print FiberPrebundle.toFiberBundle /-
/-- Make a `fiber_bundle` from a `fiber_prebundle`.  Concretely this means
that, given a `fiber_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`fiber_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
def toFiberBundle : @FiberBundle B F _ _ E a.totalSpaceTopology a.fiberTopology
    where
  totalSpaceMk_inducing := a.inducing_totalSpaceMk
  trivializationAtlas :=
    { e |
      ∃ (e₀ : _)(he₀ : e₀ ∈ a.pretrivializationAtlas),
        e = a.trivializationOfMemPretrivializationAtlas he₀ }
  trivializationAt x :=
    a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x)
  mem_baseSet_trivializationAt := a.mem_base_pretrivializationAt
  trivialization_mem_atlas x := ⟨_, a.pretrivialization_mem_atlas x, rfl⟩
#align fiber_prebundle.to_fiber_bundle FiberPrebundle.toFiberBundle
-/

/- warning: fiber_prebundle.continuous_proj -> FiberPrebundle.continuous_proj is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u1, u2, u3} B F E _inst_2 _inst_3), Continuous.{max u1 u3, u1} (Bundle.TotalSpace.{u1, u3} B E) B (FiberPrebundle.totalSpaceTopology.{u1, u2, u3} B F E _inst_2 _inst_3 a) _inst_2 (Bundle.TotalSpace.proj.{u1, u3} B E)
but is expected to have type
  forall {B : Type.{u3}} {F : Type.{u1}} {E : B -> Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u1} F] (a : FiberPrebundle.{u3, u1, u2} B F E _inst_2 _inst_3), Continuous.{max u3 u2, u3} (Bundle.TotalSpace.{u3, u2} B E) B (FiberPrebundle.totalSpaceTopology.{u3, u1, u2} B F E _inst_2 _inst_3 a) _inst_2 (Bundle.TotalSpace.proj.{u3, u2} B E)
Case conversion may be inaccurate. Consider using '#align fiber_prebundle.continuous_proj FiberPrebundle.continuous_projₓ'. -/
theorem continuous_proj : @Continuous _ _ a.totalSpaceTopology _ (π E) :=
  by
  letI := a.total_space_topology
  letI := a.fiber_topology
  letI := a.to_fiber_bundle
  exact continuous_proj F E
#align fiber_prebundle.continuous_proj FiberPrebundle.continuous_proj

/- warning: fiber_prebundle.continuous_on_of_comp_right -> FiberPrebundle.continuousOn_of_comp_right is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {F : Type.{u2}} {E : B -> Type.{u3}} [_inst_2 : TopologicalSpace.{u1} B] [_inst_3 : TopologicalSpace.{u2} F] (a : FiberPrebundle.{u1, u2, u3} B F E _inst_2 _inst_3) {X : Type.{u4}} [_inst_4 : TopologicalSpace.{u4} X] {f : (Bundle.TotalSpace.{u1, u3} B E) -> X} {s : Set.{u1} B}, (IsOpen.{u1} B _inst_2 s) -> (forall (b : B), (Membership.Mem.{u1, u1} B (Set.{u1} B) (Set.hasMem.{u1} B) b s) -> (ContinuousOn.{max u1 u2, u4} (Prod.{u1, u2} B F) X (Prod.topologicalSpace.{u1, u2} B F _inst_2 _inst_3) _inst_4 (Function.comp.{succ (max u1 u2), max (succ u1) (succ u3), succ u4} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E) X f (coeFn.{max (succ (max u1 u2)) (succ (max u1 u3)), max (succ (max u1 u2)) (succ (max u1 u3))} (LocalEquiv.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E)) (fun (_x : LocalEquiv.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E)) => (Prod.{u1, u2} B F) -> (Bundle.TotalSpace.{u1, u3} B E)) (LocalEquiv.hasCoeToFun.{max u1 u2, max u1 u3} (Prod.{u1, u2} B F) (Bundle.TotalSpace.{u1, u3} B E)) (LocalEquiv.symm.{max u1 u3, max u1 u2} (Bundle.TotalSpace.{u1, u3} B E) (Prod.{u1, u2} B F) (Pretrivialization.toLocalEquiv.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) (FiberPrebundle.pretrivializationAt.{u1, u2, u3} B F E _inst_2 _inst_3 a b))))) (Set.prod.{u1, u2} B F (Inter.inter.{u1} (Set.{u1} B) (Set.hasInter.{u1} B) s (Pretrivialization.baseSet.{u1, u2, max u1 u3} B F (Bundle.TotalSpace.{u1, u3} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u1, u3} B E) (FiberPrebundle.pretrivializationAt.{u1, u2, u3} B F E _inst_2 _inst_3 a b))) (Set.univ.{u2} F)))) -> (ContinuousOn.{max u1 u3, u4} (Bundle.TotalSpace.{u1, u3} B E) X (FiberPrebundle.totalSpaceTopology.{u1, u2, u3} B F E _inst_2 _inst_3 a) _inst_4 f (Set.preimage.{max u1 u3, u1} (Bundle.TotalSpace.{u1, u3} B E) B (Bundle.TotalSpace.proj.{u1, u3} B E) s))
but is expected to have type
  forall {B : Type.{u3}} {F : Type.{u1}} {E : B -> Type.{u2}} [_inst_2 : TopologicalSpace.{u3} B] [_inst_3 : TopologicalSpace.{u1} F] (a : FiberPrebundle.{u3, u1, u2} B F E _inst_2 _inst_3) {X : Type.{u4}} [_inst_4 : TopologicalSpace.{u4} X] {f : (Bundle.TotalSpace.{u3, u2} B E) -> X} {s : Set.{u3} B}, (IsOpen.{u3} B _inst_2 s) -> (forall (b : B), (Membership.mem.{u3, u3} B (Set.{u3} B) (Set.instMembershipSet.{u3} B) b s) -> (ContinuousOn.{max u3 u1, u4} (Prod.{u3, u1} B F) X (instTopologicalSpaceProd.{u3, u1} B F _inst_2 _inst_3) _inst_4 (Function.comp.{succ (max u3 u1), max (succ u3) (succ u2), succ u4} (Prod.{u3, u1} B F) (Bundle.TotalSpace.{u3, u2} B E) X f (LocalEquiv.toFun.{max u3 u1, max u3 u2} (Prod.{u3, u1} B F) (Bundle.TotalSpace.{u3, u2} B E) (LocalEquiv.symm.{max u3 u2, max u3 u1} (Bundle.TotalSpace.{u3, u2} B E) (Prod.{u3, u1} B F) (Pretrivialization.toLocalEquiv.{u3, u1, max u3 u2} B F (Bundle.TotalSpace.{u3, u2} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u2} B E) (FiberPrebundle.pretrivializationAt.{u3, u1, u2} B F E _inst_2 _inst_3 a b))))) (Set.prod.{u3, u1} B F (Inter.inter.{u3} (Set.{u3} B) (Set.instInterSet.{u3} B) s (Pretrivialization.baseSet.{u3, u1, max u3 u2} B F (Bundle.TotalSpace.{u3, u2} B E) _inst_2 _inst_3 (Bundle.TotalSpace.proj.{u3, u2} B E) (FiberPrebundle.pretrivializationAt.{u3, u1, u2} B F E _inst_2 _inst_3 a b))) (Set.univ.{u1} F)))) -> (ContinuousOn.{max u3 u2, u4} (Bundle.TotalSpace.{u3, u2} B E) X (FiberPrebundle.totalSpaceTopology.{u3, u1, u2} B F E _inst_2 _inst_3 a) _inst_4 f (Set.preimage.{max u3 u2, u3} (Bundle.TotalSpace.{u3, u2} B E) B (Bundle.TotalSpace.proj.{u3, u2} B E) s))
Case conversion may be inaccurate. Consider using '#align fiber_prebundle.continuous_on_of_comp_right FiberPrebundle.continuousOn_of_comp_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- For a fiber bundle `E` over `B` constructed using the `fiber_prebundle` mechanism,
continuity of a function `total_space E → X` on an open set `s` can be checked by precomposing at
each point with the pretrivialization used for the construction at that point. -/
theorem continuousOn_of_comp_right {X : Type _} [TopologicalSpace X] {f : TotalSpace E → X}
    {s : Set B} (hs : IsOpen s)
    (hf :
      ∀ b ∈ s,
        ContinuousOn (f ∘ (a.pretrivializationAt b).toLocalEquiv.symm)
          ((s ∩ (a.pretrivializationAt b).baseSet) ×ˢ (Set.univ : Set F))) :
    @ContinuousOn _ _ a.totalSpaceTopology _ f (π E ⁻¹' s) :=
  by
  letI := a.total_space_topology
  intro z hz
  let e : Trivialization F (π E) :=
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

end FiberPrebundle

