import Mathbin.Topology.LocalHomeomorph

/-!
# Charted spaces

A smooth manifold is a topological space `M` locally modelled on a euclidean space (or a euclidean
half-space for manifolds with boundaries, or an infinite dimensional vector space for more general
notions of manifolds), i.e., the manifold is covered by open subsets on which there are local
homeomorphisms (the charts) going to a model space `H`, and the changes of charts should be smooth
maps.

In this file, we introduce a general framework describing these notions, where the model space is an
arbitrary topological space. We avoid the word *manifold*, which should be reserved for the
situation where the model space is a (subset of a) vector space, and use the terminology
*charted space* instead.

If the changes of charts satisfy some additional property (for instance if they are smooth), then
`M` inherits additional structure (it makes sense to talk about smooth manifolds). There are
therefore two different ingredients in a charted space:
* the set of charts, which is data
* the fact that changes of charts belong to some group (in fact groupoid), which is additional Prop.

We separate these two parts in the definition: the charted space structure is just the set of
charts, and then the different smoothness requirements (smooth manifold, orientable manifold,
contact manifold, and so on) are additional properties of these charts. These properties are
formalized through the notion of structure groupoid, i.e., a set of local homeomorphisms stable
under composition and inverse, to which the change of coordinates should belong.

## Main definitions

* `structure_groupoid H` : a subset of local homeomorphisms of `H` stable under composition,
  inverse and restriction (ex: local diffeos).
* `continuous_groupoid H` : the groupoid of all local homeomorphisms of `H`
* `charted_space H M` : charted space structure on `M` modelled on `H`, given by an atlas of
  local homeomorphisms from `M` to `H` whose sources cover `M`. This is a type class.
* `has_groupoid M G` : when `G` is a structure groupoid on `H` and `M` is a charted space
  modelled on `H`, require that all coordinate changes belong to `G`. This is a type class.
* `atlas H M` : when `M` is a charted space modelled on `H`, the atlas of this charted
  space structure, i.e., the set of charts.
* `G.maximal_atlas M` : when `M` is a charted space modelled on `H` and admitting `G` as a
  structure groupoid, one can consider all the local homeomorphisms from `M` to `H` such that
  changing coordinate from any chart to them belongs to `G`. This is a larger atlas, called the
  maximal atlas (for the groupoid `G`).
* `structomorph G M M'` : the type of diffeomorphisms between the charted spaces `M` and `M'` for
  the groupoid `G`. We avoid the word diffeomorphism, keeping it for the smooth category.

As a basic example, we give the instance
`instance charted_space_model_space (H : Type*) [topological_space H] : charted_space H H`
saying that a topological space is a charted space over itself, with the identity as unique chart.
This charted space structure is compatible with any groupoid.

Additional useful definitions:

* `pregroupoid H` : a subset of local mas of `H` stable under composition and
  restriction, but not inverse (ex: smooth maps)
* `groupoid_of_pregroupoid` : construct a groupoid from a pregroupoid, by requiring that a map and
  its inverse both belong to the pregroupoid (ex: construct diffeos from smooth maps)
* `chart_at H x` is a preferred chart at `x : M` when `M` has a charted space structure modelled on
  `H`.
* `G.compatible he he'` states that, for any two charts `e` and `e'` in the atlas, the composition
  of `e.symm` and `e'` belongs to the groupoid `G` when `M` admits `G` as a structure groupoid.
* `G.compatible_of_mem_maximal_atlas he he'` states that, for any two charts `e` and `e'` in the
  maximal atlas associated to the groupoid `G`, the composition of `e.symm` and `e'` belongs to the
  `G` if `M` admits `G` as a structure groupoid.
* `charted_space_core.to_charted_space`: consider a space without a topology, but endowed with a set
  of charts (which are local equivs) for which the change of coordinates are local homeos. Then
  one can construct a topology on the space for which the charts become local homeos, defining
  a genuine charted space structure.

## Implementation notes

The atlas in a charted space is *not* a maximal atlas in general: the notion of maximality depends
on the groupoid one considers, and changing groupoids changes the maximal atlas. With the current
formalization, it makes sense first to choose the atlas, and then to ask whether this precise atlas
defines a smooth manifold, an orientable manifold, and so on. A consequence is that structomorphisms
between `M` and `M'` do *not* induce a bijection between the atlases of `M` and `M'`: the
definition is only that, read in charts, the structomorphism locally belongs to the groupoid under
consideration. (This is equivalent to inducing a bijection between elements of the maximal atlas).
A consequence is that the invariance under structomorphisms of properties defined in terms of the
atlas is not obvious in general, and could require some work in theory (amounting to the fact
that these properties only depend on the maximal atlas, for instance). In practice, this does not
create any real difficulty.

We use the letter `H` for the model space thinking of the case of manifolds with boundary, where the
model space is a half space.

Manifolds are sometimes defined as topological spaces with an atlas of local diffeomorphisms, and
sometimes as spaces with an atlas from which a topology is deduced. We use the former approach:
otherwise, there would be an instance from manifolds to topological spaces, which means that any
instance search for topological spaces would try to find manifold structures involving a yet
unknown model space, leading to problems. However, we also introduce the latter approach,
through a structure `charted_space_core` making it possible to construct a topology out of a set of
local equivs with compatibility conditions (but we do not register it as an instance).

In the definition of a charted space, the model space is written as an explicit parameter as there
can be several model spaces for a given topological space. For instance, a complex manifold
(modelled over `ℂ^n`) will also be seen sometimes as a real manifold modelled over `ℝ^(2n)`.

## Notations

In the locale `manifold`, we denote the composition of local homeomorphisms with `≫ₕ`, and the
composition of local equivs with `≫`.
-/


noncomputable theory

open_locale Classical TopologicalSpace

open Filter

universe u

variable{H : Type u}{H' : Type _}{M : Type _}{M' : Type _}{M'' : Type _}

localized [Manifold] infixr:100 " ≫ₕ " => LocalHomeomorph.trans

localized [Manifold] infixr:100 " ≫ " => LocalEquiv.trans

localized [Manifold] attribute [-instance] Unique.subsingleton Pi.subsingleton

open Set LocalHomeomorph

/-! ### Structure groupoids-/


section Groupoid

/-! One could add to the definition of a structure groupoid the fact that the restriction of an
element of the groupoid to any open set still belongs to the groupoid.
(This is in Kobayashi-Nomizu.)
I am not sure I want this, for instance on `H × E` where `E` is a vector space, and the groupoid is
made of functions respecting the fibers and linear in the fibers (so that a charted space over this
groupoid is naturally a vector bundle) I prefer that the members of the groupoid are always
defined on sets of the form `s × E`.  There is a typeclass `closed_under_restriction` for groupoids
which have the restriction property.

The only nontrivial requirement is locality: if a local homeomorphism belongs to the groupoid
around each point in its domain of definition, then it belongs to the groupoid. Without this
requirement, the composition of structomorphisms does not have to be a structomorphism. Note that
this implies that a local homeomorphism with empty source belongs to any structure groupoid, as
it trivially satisfies this condition.

There is also a technical point, related to the fact that a local homeomorphism is by definition a
global map which is a homeomorphism when restricted to its source subset (and its values outside
of the source are not relevant). Therefore, we also require that being a member of the groupoid only
depends on the values on the source.

We use primes in the structure names as we will reformulate them below (without primes) using a
`has_mem` instance, writing `e ∈ G` instead of `e ∈ G.members`.
-/


/-- A structure groupoid is a set of local homeomorphisms of a topological space stable under
composition and inverse. They appear in the definition of the smoothness class of a manifold. -/
structure StructureGroupoid(H : Type u)[TopologicalSpace H] where 
  Members : Set (LocalHomeomorph H H)
  trans' : ∀ e e' : LocalHomeomorph H H, e ∈ members → e' ∈ members → e ≫ₕ e' ∈ members 
  symm' : ∀ e : LocalHomeomorph H H, e ∈ members → e.symm ∈ members 
  id_mem' : LocalHomeomorph.refl H ∈ members 
  locality' :
  ∀ e : LocalHomeomorph H H, (∀ x _ : x ∈ e.source, ∃ s, IsOpen s ∧ x ∈ s ∧ e.restr s ∈ members) → e ∈ members 
  eq_on_source' : ∀ e e' : LocalHomeomorph H H, e ∈ members → e' ≈ e → e' ∈ members

variable[TopologicalSpace H]

instance  : HasMem (LocalHomeomorph H H) (StructureGroupoid H) :=
  ⟨fun e : LocalHomeomorph H H G : StructureGroupoid H => e ∈ G.members⟩

theorem StructureGroupoid.trans (G : StructureGroupoid H) {e e' : LocalHomeomorph H H} (he : e ∈ G) (he' : e' ∈ G) :
  e ≫ₕ e' ∈ G :=
  G.trans' e e' he he'

theorem StructureGroupoid.symm (G : StructureGroupoid H) {e : LocalHomeomorph H H} (he : e ∈ G) : e.symm ∈ G :=
  G.symm' e he

theorem StructureGroupoid.id_mem (G : StructureGroupoid H) : LocalHomeomorph.refl H ∈ G :=
  G.id_mem'

theorem StructureGroupoid.locality (G : StructureGroupoid H) {e : LocalHomeomorph H H}
  (h : ∀ x _ : x ∈ e.source, ∃ s, IsOpen s ∧ x ∈ s ∧ e.restr s ∈ G) : e ∈ G :=
  G.locality' e h

theorem StructureGroupoid.eq_on_source (G : StructureGroupoid H) {e e' : LocalHomeomorph H H} (he : e ∈ G)
  (h : e' ≈ e) : e' ∈ G :=
  G.eq_on_source' e e' he h

/-- Partial order on the set of groupoids, given by inclusion of the members of the groupoid -/
instance StructureGroupoid.partialOrder : PartialOrderₓ (StructureGroupoid H) :=
  PartialOrderₓ.lift StructureGroupoid.Members
    fun a b h =>
      by 
        cases a 
        cases b 
        dsimp  at h 
        induction h 
        rfl

theorem StructureGroupoid.le_iff {G₁ G₂ : StructureGroupoid H} : G₁ ≤ G₂ ↔ ∀ e, e ∈ G₁ → e ∈ G₂ :=
  Iff.rfl

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The trivial groupoid, containing only the identity (and maps with empty source, as this is
necessary from the definition) -/ def id_groupoid (H : Type u) [topological_space H] : structure_groupoid H :=
{ members := «expr ∪ »({local_homeomorph.refl H}, {e : local_homeomorph H H | «expr = »(e.source, «expr∅»())}),
  trans' := λ e e' he he', begin
    cases [expr he] []; simp [] [] [] [] [] ["at", ident he, ident he'],
    { simpa [] [] ["only"] ["[", expr he, ",", expr refl_trans, "]"] [] [] },
    { have [] [":", expr «expr ⊆ »(«expr ≫ₕ »(e, e').source, e.source)] [":=", expr sep_subset _ _],
      rw [expr he] ["at", ident this],
      have [] [":", expr «expr ∈ »(«expr ≫ₕ »(e, e'), {e : local_homeomorph H H | «expr = »(e.source, «expr∅»())})] [":=", expr disjoint_iff.1 this],
      exact [expr (mem_union _ _ _).2 (or.inr this)] }
  end,
  symm' := λ e he, begin
    cases [expr (mem_union _ _ _).1 he] ["with", ident E, ident E],
    { finish [] [] },
    { right,
      simpa [] [] ["only"] ["[", expr e.to_local_equiv.image_source_eq_target.symm, "]"] ["with", ident mfld_simps] ["using", expr E] }
  end,
  id_mem' := mem_union_left _ rfl,
  locality' := λ e he, begin
    cases [expr e.source.eq_empty_or_nonempty] ["with", ident h, ident h],
    { right,
      exact [expr h] },
    { left,
      rcases [expr h, "with", "⟨", ident x, ",", ident hx, "⟩"],
      rcases [expr he x hx, "with", "⟨", ident s, ",", ident open_s, ",", ident xs, ",", ident hs, "⟩"],
      have [ident x's] [":", expr «expr ∈ »(x, (e.restr s).source)] [],
      { rw ["[", expr restr_source, ",", expr open_s.interior_eq, "]"] [],
        exact [expr ⟨hx, xs⟩] },
      cases [expr hs] [],
      { replace [ident hs] [":", expr «expr = »(local_homeomorph.restr e s, local_homeomorph.refl H)] [],
        by simpa [] [] ["only"] [] [] ["using", expr hs],
        have [] [":", expr «expr = »((e.restr s).source, univ)] [],
        by { rw [expr hs] [],
          simp [] [] [] [] [] [] },
        change [expr «expr = »(«expr ∩ »(e.to_local_equiv.source, interior s), univ)] [] ["at", ident this],
        have [] [":", expr «expr ⊆ »(univ, interior s)] [],
        by { rw ["<-", expr this] [],
          exact [expr inter_subset_right _ _] },
        have [] [":", expr «expr = »(s, univ)] [],
        by rwa ["[", expr open_s.interior_eq, ",", expr univ_subset_iff, "]"] ["at", ident this],
        simpa [] [] ["only"] ["[", expr this, ",", expr restr_univ, "]"] [] ["using", expr hs] },
      { exfalso,
        rw [expr mem_set_of_eq] ["at", ident hs],
        rwa [expr hs] ["at", ident x's] } }
  end,
  eq_on_source' := λ e e' he he'e, begin
    cases [expr he] [],
    { left,
      have [] [":", expr «expr = »(e, e')] [],
      { refine [expr eq_of_eq_on_source_univ (setoid.symm he'e) _ _]; rw [expr set.mem_singleton_iff.1 he] []; refl },
      rwa ["<-", expr this] [] },
    { right,
      change [expr «expr = »(e.to_local_equiv.source, «expr∅»())] [] ["at", ident he],
      rwa ["[", expr set.mem_set_of_eq, ",", expr he'e.source_eq, "]"] [] }
  end }

/-- Every structure groupoid contains the identity groupoid -/
instance  : OrderBot (StructureGroupoid H) :=
  { bot := idGroupoid H,
    bot_le :=
      by 
        intro u f hf 
        change f ∈ {LocalHomeomorph.refl H} ∪ { e:LocalHomeomorph H H | e.source = ∅ } at hf 
        simp only [singleton_union, mem_set_of_eq, mem_insert_iff] at hf 
        cases hf
        ·
          rw [hf]
          apply u.id_mem
        ·
          apply u.locality 
          intro x hx 
          rw [hf, mem_empty_eq] at hx 
          exact hx.elim }

instance  (H : Type u) [TopologicalSpace H] : Inhabited (StructureGroupoid H) :=
  ⟨idGroupoid H⟩

/-- To construct a groupoid, one may consider classes of local homeos such that both the function
and its inverse have some property. If this property is stable under composition,
one gets a groupoid. `pregroupoid` bundles the properties needed for this construction, with the
groupoid of smooth functions with smooth inverses as an application. -/
structure Pregroupoid(H : Type _)[TopologicalSpace H] where 
  property : (H → H) → Set H → Prop 
  comp :
  ∀ {f g u v}, property f u → property g v → IsOpen u → IsOpen v → IsOpen (u ∩ f ⁻¹' v) → property (g ∘ f) (u ∩ f ⁻¹' v)
  id_mem : property id univ 
  locality : ∀ {f u}, IsOpen u → (∀ x _ : x ∈ u, ∃ v, IsOpen v ∧ x ∈ v ∧ property f (u ∩ v)) → property f u 
  congr : ∀ {f g : H → H} {u}, IsOpen u → (∀ x _ : x ∈ u, g x = f x) → property f u → property g u

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Construct a groupoid of local homeos for which the map and its inverse have some property,
from a pregroupoid asserting that this property is stable under composition. -/
def pregroupoid.groupoid (PG : pregroupoid H) : structure_groupoid H :=
{ members := {e : local_homeomorph H H | «expr ∧ »(PG.property e e.source, PG.property e.symm e.target)},
  trans' := λ e e' he he', begin
    split,
    { apply [expr PG.comp he.1 he'.1 e.open_source e'.open_source],
      apply [expr e.continuous_to_fun.preimage_open_of_open e.open_source e'.open_source] },
    { apply [expr PG.comp he'.2 he.2 e'.open_target e.open_target],
      apply [expr e'.continuous_inv_fun.preimage_open_of_open e'.open_target e.open_target] }
  end,
  symm' := λ e he, ⟨he.2, he.1⟩,
  id_mem' := ⟨PG.id_mem, PG.id_mem⟩,
  locality' := λ e he, begin
    split,
    { apply [expr PG.locality e.open_source (λ x xu, _)],
      rcases [expr he x xu, "with", "⟨", ident s, ",", ident s_open, ",", ident xs, ",", ident hs, "⟩"],
      refine [expr ⟨s, s_open, xs, _⟩],
      convert [] [expr hs.1] ["using", 1],
      dsimp [] ["[", expr local_homeomorph.restr, "]"] [] [],
      rw [expr s_open.interior_eq] [] },
    { apply [expr PG.locality e.open_target (λ x xu, _)],
      rcases [expr he (e.symm x) (e.map_target xu), "with", "⟨", ident s, ",", ident s_open, ",", ident xs, ",", ident hs, "⟩"],
      refine [expr ⟨«expr ∩ »(e.target, «expr ⁻¹' »(e.symm, s)), _, ⟨xu, xs⟩, _⟩],
      { exact [expr continuous_on.preimage_open_of_open e.continuous_inv_fun e.open_target s_open] },
      { rw ["[", "<-", expr inter_assoc, ",", expr inter_self, "]"] [],
        convert [] [expr hs.2] ["using", 1],
        dsimp [] ["[", expr local_homeomorph.restr, "]"] [] [],
        rw [expr s_open.interior_eq] [] } }
  end,
  eq_on_source' := λ e e' he ee', begin
    split,
    { apply [expr PG.congr e'.open_source ee'.2],
      simp [] [] ["only"] ["[", expr ee'.1, ",", expr he.1, "]"] [] [] },
    { have [ident A] [] [":=", expr ee'.symm'],
      apply [expr PG.congr e'.symm.open_source A.2],
      convert [] [expr he.2] [],
      rw [expr A.1] [],
      refl }
  end }

theorem mem_groupoid_of_pregroupoid {PG : Pregroupoid H} {e : LocalHomeomorph H H} :
  e ∈ PG.groupoid ↔ PG.property e e.source ∧ PG.property e.symm e.target :=
  Iff.rfl

theorem groupoid_of_pregroupoid_le (PG₁ PG₂ : Pregroupoid H) (h : ∀ f s, PG₁.property f s → PG₂.property f s) :
  PG₁.groupoid ≤ PG₂.groupoid :=
  by 
    refine' StructureGroupoid.le_iff.2 fun e he => _ 
    rw [mem_groupoid_of_pregroupoid] at he⊢
    exact ⟨h _ _ he.1, h _ _ he.2⟩

theorem mem_pregroupoid_of_eq_on_source (PG : Pregroupoid H) {e e' : LocalHomeomorph H H} (he' : e ≈ e')
  (he : PG.property e e.source) : PG.property e' e'.source :=
  by 
    rw [←he'.1]
    exact PG.congr e.open_source he'.eq_on.symm he

/-- The pregroupoid of all local maps on a topological space `H` -/
@[reducible]
def continuousPregroupoid (H : Type _) [TopologicalSpace H] : Pregroupoid H :=
  { property := fun f s => True, comp := fun f g u v hf hg hu hv huv => trivialₓ, id_mem := trivialₓ,
    locality := fun f u u_open h => trivialₓ, congr := fun f g u u_open hcongr hf => trivialₓ }

instance  (H : Type _) [TopologicalSpace H] : Inhabited (Pregroupoid H) :=
  ⟨continuousPregroupoid H⟩

/-- The groupoid of all local homeomorphisms on a topological space `H` -/
def continuousGroupoid (H : Type _) [TopologicalSpace H] : StructureGroupoid H :=
  Pregroupoid.groupoid (continuousPregroupoid H)

/-- Every structure groupoid is contained in the groupoid of all local homeomorphisms -/
instance  : OrderTop (StructureGroupoid H) :=
  { top := continuousGroupoid H,
    le_top :=
      fun u f hf =>
        by 
          split  <;>
            exact
              by 
                decide }

/-- A groupoid is closed under restriction if it contains all restrictions of its element local
homeomorphisms to open subsets of the source. -/
class ClosedUnderRestriction(G : StructureGroupoid H) : Prop where 
  ClosedUnderRestriction : ∀ {e : LocalHomeomorph H H}, e ∈ G → ∀ s : Set H, IsOpen s → e.restr s ∈ G

theorem closed_under_restriction' {G : StructureGroupoid H} [ClosedUnderRestriction G] {e : LocalHomeomorph H H}
  (he : e ∈ G) {s : Set H} (hs : IsOpen s) : e.restr s ∈ G :=
  ClosedUnderRestriction.closed_under_restriction he s hs

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The trivial restriction-closed groupoid, containing only local homeomorphisms equivalent to the
restriction of the identity to the various open subsets. -/ def id_restr_groupoid : structure_groupoid H :=
{ members := {e | «expr∃ , »({s : set H} (h : is_open s), «expr ≈ »(e, local_homeomorph.of_set s h))},
  trans' := begin
    rintros [ident e, ident e', "⟨", ident s, ",", ident hs, ",", ident hse, "⟩", "⟨", ident s', ",", ident hs', ",", ident hse', "⟩"],
    refine [expr ⟨«expr ∩ »(s, s'), is_open.inter hs hs', _⟩],
    have [] [] [":=", expr local_homeomorph.eq_on_source.trans' hse hse'],
    rwa [expr local_homeomorph.of_set_trans_of_set] ["at", ident this]
  end,
  symm' := begin
    rintros [ident e, "⟨", ident s, ",", ident hs, ",", ident hse, "⟩"],
    refine [expr ⟨s, hs, _⟩],
    rw ["[", "<-", expr of_set_symm, "]"] [],
    exact [expr local_homeomorph.eq_on_source.symm' hse]
  end,
  id_mem' := ⟨univ, is_open_univ, by simp [] [] ["only"] [] ["with", ident mfld_simps] []⟩,
  locality' := begin
    intros [ident e, ident h],
    refine [expr ⟨e.source, e.open_source, by simp [] [] ["only"] [] ["with", ident mfld_simps] [], _⟩],
    intros [ident x, ident hx],
    rcases [expr h x hx, "with", "⟨", ident s, ",", ident hs, ",", ident hxs, ",", ident s', ",", ident hs', ",", ident hes', "⟩"],
    have [ident hes] [":", expr «expr ∈ »(x, (e.restr s).source)] [],
    { rw [expr e.restr_source] [],
      refine [expr ⟨hx, _⟩],
      rw [expr hs.interior_eq] [],
      exact [expr hxs] },
    simpa [] [] ["only"] [] ["with", ident mfld_simps] ["using", expr local_homeomorph.eq_on_source.eq_on hes' hes]
  end,
  eq_on_source' := begin
    rintros [ident e, ident e', "⟨", ident s, ",", ident hs, ",", ident hse, "⟩", ident hee'],
    exact [expr ⟨s, hs, setoid.trans hee' hse⟩]
  end }

theorem id_restr_groupoid_mem {s : Set H} (hs : IsOpen s) : of_set s hs ∈ @idRestrGroupoid H _ :=
  ⟨s, hs,
    by 
      rfl⟩

/-- The trivial restriction-closed groupoid is indeed `closed_under_restriction`. -/
instance closed_under_restriction_id_restr_groupoid : ClosedUnderRestriction (@idRestrGroupoid H _) :=
  ⟨by 
      rintro e ⟨s', hs', he⟩ s hs 
      use s' ∩ s, IsOpen.inter hs' hs 
      refine' Setoidₓ.trans (LocalHomeomorph.EqOnSource.restr he s) _ 
      exact
        ⟨by 
            simp' only [hs.interior_eq] with mfld_simps,
          by 
            simp' only with mfld_simps⟩⟩

/-- A groupoid is closed under restriction if and only if it contains the trivial restriction-closed
groupoid. -/
theorem closed_under_restriction_iff_id_le (G : StructureGroupoid H) : ClosedUnderRestriction G ↔ idRestrGroupoid ≤ G :=
  by 
    split 
    ·
      intros _i 
      apply structure_groupoid.le_iff.mpr 
      rintro e ⟨s, hs, hes⟩
      refine' G.eq_on_source _ hes 
      convert closed_under_restriction' G.id_mem hs 
      change s = _ ∩ _ 
      rw [hs.interior_eq]
      simp' only with mfld_simps
    ·
      intro h 
      split 
      intro e he s hs 
      rw [←of_set_trans (e : LocalHomeomorph H H) hs]
      refine' G.trans _ he 
      apply structure_groupoid.le_iff.mp h 
      exact id_restr_groupoid_mem hs

/-- The groupoid of all local homeomorphisms on a topological space `H` is closed under restriction.
-/
instance  : ClosedUnderRestriction (continuousGroupoid H) :=
  (closed_under_restriction_iff_id_le _).mpr
    (by 
      convert le_top)

end Groupoid

/-! ### Charted spaces -/


/-- A charted space is a topological space endowed with an atlas, i.e., a set of local
homeomorphisms taking value in a model space `H`, called charts, such that the domains of the charts
cover the whole space. We express the covering property by chosing for each `x` a member
`chart_at H x` of the atlas containing `x` in its source: in the smooth case, this is convenient to
construct the tangent bundle in an efficient way.
The model space is written as an explicit parameter as there can be several model spaces for a
given topological space. For instance, a complex manifold (modelled over `ℂ^n`) will also be seen
sometimes as a real manifold over `ℝ^(2n)`.
-/
class ChartedSpace(H : Type _)[TopologicalSpace H](M : Type _)[TopologicalSpace M] where 
  Atlas{} : Set (LocalHomeomorph M H)
  chartAt{} : M → LocalHomeomorph M H 
  mem_chart_source{} : ∀ x, x ∈ (chart_at x).Source 
  chart_mem_atlas{} : ∀ x, chart_at x ∈ atlas

export ChartedSpace()

attribute [simp, mfld_simps] mem_chart_source chart_mem_atlas

section ChartedSpace

/-- Any space is a charted_space modelled over itself, by just using the identity chart -/
instance chartedSpaceSelf (H : Type _) [TopologicalSpace H] : ChartedSpace H H :=
  { Atlas := {LocalHomeomorph.refl H}, chartAt := fun x => LocalHomeomorph.refl H,
    mem_chart_source := fun x => mem_univ x, chart_mem_atlas := fun x => mem_singleton _ }

/-- In the trivial charted_space structure of a space modelled over itself through the identity, the
atlas members are just the identity -/
@[simp, mfld_simps]
theorem charted_space_self_atlas {H : Type _} [TopologicalSpace H] {e : LocalHomeomorph H H} :
  e ∈ atlas H H ↔ e = LocalHomeomorph.refl H :=
  by 
    simp [atlas, ChartedSpace.Atlas]

/-- In the model space, chart_at is always the identity -/
theorem chart_at_self_eq {H : Type _} [TopologicalSpace H] {x : H} : chart_at H x = LocalHomeomorph.refl H :=
  by 
    simpa using chart_mem_atlas H x

section 

variable(H)[TopologicalSpace H][TopologicalSpace M][ChartedSpace H M]

theorem mem_chart_target (x : M) : chart_at H x x ∈ (chart_at H x).Target :=
  (chart_at H x).map_source (mem_chart_source _ _)

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a topological space admits an atlas with locally compact charts, then the space itself
is locally compact. -/ theorem charted_space.locally_compact [locally_compact_space H] : locally_compact_space M :=
begin
  have [] [":", expr ∀
   x : M, (expr𝓝() x).has_basis (λ
    s, «expr ∧ »(«expr ∈ »(s, expr𝓝() (chart_at H x x)), «expr ∧ »(is_compact s, «expr ⊆ »(s, (chart_at H x).target)))) (λ
    s, «expr '' »((chart_at H x).symm, s))] [],
  { intro [ident x],
    rw ["[", "<-", expr (chart_at H x).symm_map_nhds_eq (mem_chart_source H x), "]"] [],
    exact [expr ((compact_basis_nhds (chart_at H x x)).has_basis_self_subset (is_open.mem_nhds (chart_at H x).open_target (mem_chart_target H x))).map _] },
  refine [expr locally_compact_space_of_has_basis this _],
  rintro [ident x, ident s, "⟨", ident h₁, ",", ident h₂, ",", ident h₃, "⟩"],
  exact [expr h₂.image_of_continuous_on ((chart_at H x).continuous_on_symm.mono h₃)]
end

open TopologicalSpace

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem charted_space.second_countable_of_countable_cover
[second_countable_topology H]
{s : set M}
(hs : «expr = »(«expr⋃ , »((x) (hx : «expr ∈ »(x, s)), (chart_at H x).source), univ))
(hsc : countable s) : second_countable_topology M :=
begin
  haveI [] [":", expr ∀
   x : M, second_countable_topology (chart_at H x).source] [":=", expr λ
   x, (chart_at H x).second_countable_topology_source],
  haveI [] [] [":=", expr hsc.to_encodable],
  rw [expr bUnion_eq_Union] ["at", ident hs],
  exact [expr second_countable_topology_of_countable_cover (λ x : s, (chart_at H (x : M)).open_source) hs]
end

theorem ChartedSpace.second_countable_of_sigma_compact [second_countable_topology H] [SigmaCompactSpace M] :
  second_countable_topology M :=
  by 
    obtain ⟨s, hsc, hsU⟩ : ∃ s, countable s ∧ (⋃(x : _)(hx : x ∈ s), (chart_at H x).Source) = univ :=
      countable_cover_nhds_of_sigma_compact
        fun x : M => IsOpen.mem_nhds (chart_at H x).open_source (mem_chart_source H x)
    exact ChartedSpace.second_countable_of_countable_cover H hsU hsc

end 

/-- For technical reasons we introduce two type tags:

* `model_prod H H'` is the same as `H × H'`;
* `model_pi H` is the same as `Π i, H i`, where `H : ι → Type*` and `ι` is a finite type.

In both cases the reason is the same, so we explain it only in the case of the product. A charted
space `M` with model `H` is a set of local charts from `M` to `H` covering the space. Every space is
registered as a charted space over itself, using the only chart `id`, in `manifold_model_space`. You
can also define a product of charted space `M` and `M'` (with model space `H × H'`) by taking the
products of the charts. Now, on `H × H'`, there are two charted space structures with model space
`H × H'` itself, the one coming from `manifold_model_space`, and the one coming from the product of
the two `manifold_model_space` on each component. They are equal, but not defeq (because the product
of `id` and `id` is not defeq to `id`), which is bad as we know. This expedient of renaming `H × H'`
solves this problem. -/
library_note "Manifold type tags"

/-- Same thing as `H × H'` We introduce it for technical reasons,
see note [Manifold type tags]. -/
def ModelProd (H : Type _) (H' : Type _) :=
  H × H'

/-- Same thing as `Π i, H i` We introduce it for technical reasons,
see note [Manifold type tags]. -/
def ModelPi {ι : Type _} (H : ι → Type _) :=
  ∀ i, H i

section 

attribute [local reducible] ModelProd

instance modelProdInhabited [Inhabited H] [Inhabited H'] : Inhabited (ModelProd H H') :=
  Prod.inhabited

instance  (H : Type _) [TopologicalSpace H] (H' : Type _) [TopologicalSpace H'] : TopologicalSpace (ModelProd H H') :=
  Prod.topologicalSpace

@[simp, mfld_simps]
theorem model_prod_range_prod_id {H : Type _} {H' : Type _} {α : Type _} (f : H → α) :
  (range fun p : ModelProd H H' => (f p.1, p.2)) = Set.Prod (range f) univ :=
  by 
    rw [prod_range_univ_eq]

end 

section 

variable{ι : Type _}{Hi : ι → Type _}

instance modelPiInhabited [∀ i, Inhabited (Hi i)] : Inhabited (ModelPi Hi) :=
  Pi.inhabited _

instance  [∀ i, TopologicalSpace (Hi i)] : TopologicalSpace (ModelPi Hi) :=
  Pi.topologicalSpace

end 

/-- The product of two charted spaces is naturally a charted space, with the canonical
construction of the atlas of product maps. -/
instance prodChartedSpace (H : Type _) [TopologicalSpace H] (M : Type _) [TopologicalSpace M] [ChartedSpace H M]
  (H' : Type _) [TopologicalSpace H'] (M' : Type _) [TopologicalSpace M'] [ChartedSpace H' M'] :
  ChartedSpace (ModelProd H H') (M × M') :=
  { Atlas := image2 LocalHomeomorph.prod (atlas H M) (atlas H' M'),
    chartAt := fun x : M × M' => (chart_at H x.1).Prod (chart_at H' x.2),
    mem_chart_source := fun x => ⟨mem_chart_source _ _, mem_chart_source _ _⟩,
    chart_mem_atlas := fun x => mem_image2_of_mem (chart_mem_atlas _ _) (chart_mem_atlas _ _) }

section prodChartedSpace

variable[TopologicalSpace
      H][TopologicalSpace M][ChartedSpace H M][TopologicalSpace H'][TopologicalSpace M'][ChartedSpace H' M']{x : M × M'}

@[simp, mfld_simps]
theorem prod_charted_space_chart_at : chart_at (ModelProd H H') x = (chart_at H x.fst).Prod (chart_at H' x.snd) :=
  rfl

end prodChartedSpace

/-- The product of a finite family of charted spaces is naturally a charted space, with the
canonical construction of the atlas of finite product maps. -/
instance piChartedSpace {ι : Type _} [Fintype ι] (H : ι → Type _) [∀ i, TopologicalSpace (H i)] (M : ι → Type _)
  [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)] : ChartedSpace (ModelPi H) (∀ i, M i) :=
  { Atlas := LocalHomeomorph.pi '' (Set.Pi univ$ fun i => atlas (H i) (M i)),
    chartAt := fun f => LocalHomeomorph.pi$ fun i => chart_at (H i) (f i),
    mem_chart_source := fun f i hi => mem_chart_source (H i) (f i),
    chart_mem_atlas := fun f => mem_image_of_mem _$ fun i hi => chart_mem_atlas (H i) (f i) }

@[simp, mfld_simps]
theorem pi_charted_space_chart_at {ι : Type _} [Fintype ι] (H : ι → Type _) [∀ i, TopologicalSpace (H i)]
  (M : ι → Type _) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)] (f : ∀ i, M i) :
  chart_at (ModelPi H) f = LocalHomeomorph.pi fun i => chart_at (H i) (f i) :=
  rfl

end ChartedSpace

/-! ### Constructing a topology from an atlas -/


/-- Sometimes, one may want to construct a charted space structure on a space which does not yet
have a topological structure, where the topology would come from the charts. For this, one needs
charts that are only local equivs, and continuity properties for their composition.
This is formalised in `charted_space_core`. -/
@[nolint has_inhabited_instance]
structure ChartedSpaceCore(H : Type _)[TopologicalSpace H](M : Type _) where 
  Atlas : Set (LocalEquiv M H)
  chartAt : M → LocalEquiv M H 
  mem_chart_source : ∀ x, x ∈ (chart_at x).Source 
  chart_mem_atlas : ∀ x, chart_at x ∈ atlas 
  open_source : ∀ e e' : LocalEquiv M H, e ∈ atlas → e' ∈ atlas → IsOpen (e.symm.trans e').Source 
  continuous_to_fun :
  ∀ e e' : LocalEquiv M H, e ∈ atlas → e' ∈ atlas → ContinuousOn (e.symm.trans e') (e.symm.trans e').Source

namespace ChartedSpaceCore

variable[TopologicalSpace H](c : ChartedSpaceCore H M){e : LocalEquiv M H}

/-- Topology generated by a set of charts on a Type. -/
protected def to_topological_space : TopologicalSpace M :=
  TopologicalSpace.generateFrom$
    ⋃(e : LocalEquiv M H)(he : e ∈ c.atlas)(s : Set H)(s_open : IsOpen s), {e ⁻¹' s ∩ e.source}

theorem open_source' (he : e ∈ c.atlas) : @IsOpen M c.to_topological_space e.source :=
  by 
    apply TopologicalSpace.GenerateOpen.basic 
    simp only [exists_prop, mem_Union, mem_singleton_iff]
    refine' ⟨e, he, univ, is_open_univ, _⟩
    simp only [Set.univ_inter, Set.preimage_univ]

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem open_target (he : «expr ∈ »(e, c.atlas)) : is_open e.target :=
begin
  have [ident E] [":", expr «expr = »(«expr ∩ »(e.target, «expr ⁻¹' »(e.symm, e.source)), e.target)] [":=", expr subset.antisymm (inter_subset_left _ _) (λ
    x hx, ⟨hx, local_equiv.target_subset_preimage_source _ hx⟩)],
  simpa [] [] [] ["[", expr local_equiv.trans_source, ",", expr E, "]"] [] ["using", expr c.open_source e e he he]
end

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An element of the atlas in a charted space without topology becomes a local homeomorphism
for the topology constructed from this atlas. The `local_homeomorph` version is given in this
definition. -/
protected
def local_homeomorph
(e : local_equiv M H)
(he : «expr ∈ »(e, c.atlas)) : @local_homeomorph M H c.to_topological_space _ :=
{ open_source := by convert [] [expr c.open_source' he] [],
  open_target := by convert [] [expr c.open_target he] [],
  continuous_to_fun := begin
    letI [] [":", expr topological_space M] [":=", expr c.to_topological_space],
    rw [expr continuous_on_open_iff (c.open_source' he)] [],
    assume [binders (s s_open)],
    rw [expr inter_comm] [],
    apply [expr topological_space.generate_open.basic],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_Union, ",", expr mem_singleton_iff, "]"] [] [],
    exact [expr ⟨e, he, ⟨s, s_open, rfl⟩⟩]
  end,
  continuous_inv_fun := begin
    letI [] [":", expr topological_space M] [":=", expr c.to_topological_space],
    apply [expr continuous_on_open_of_generate_from (c.open_target he)],
    assume [binders (t ht)],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_Union, ",", expr mem_singleton_iff, "]"] [] ["at", ident ht],
    rcases [expr ht, "with", "⟨", ident e', ",", ident e'_atlas, ",", ident s, ",", ident s_open, ",", ident ts, "⟩"],
    rw [expr ts] [],
    let [ident f] [] [":=", expr e.symm.trans e'],
    have [] [":", expr is_open «expr ∩ »(«expr ⁻¹' »(f, s), f.source)] [],
    by simpa [] [] [] ["[", expr inter_comm, "]"] [] ["using", expr (continuous_on_open_iff (c.open_source e e' he e'_atlas)).1 (c.continuous_to_fun e e' he e'_atlas) s s_open],
    have [ident A] [":", expr «expr = »(«expr ∩ »(«expr ⁻¹' »(«expr ∘ »(e', e.symm), s), «expr ∩ »(e.target, «expr ⁻¹' »(e.symm, e'.source))), «expr ∩ »(e.target, «expr ∩ »(«expr ⁻¹' »(«expr ∘ »(e', e.symm), s), «expr ⁻¹' »(e.symm, e'.source))))] [],
    by { rw ["[", "<-", expr inter_assoc, ",", "<-", expr inter_assoc, "]"] [],
      congr' [1] [],
      exact [expr inter_comm _ _] },
    simpa [] [] [] ["[", expr local_equiv.trans_source, ",", expr preimage_inter, ",", expr preimage_comp.symm, ",", expr A, "]"] [] ["using", expr this]
  end,
  ..e }

/-- Given a charted space without topology, endow it with a genuine charted space structure with
respect to the topology constructed from the atlas. -/
def to_charted_space : @ChartedSpace H _ M c.to_topological_space :=
  { Atlas := ⋃(e : LocalEquiv M H)(he : e ∈ c.atlas), {c.local_homeomorph e he},
    chartAt := fun x => c.local_homeomorph (c.chart_at x) (c.chart_mem_atlas x),
    mem_chart_source := fun x => c.mem_chart_source x,
    chart_mem_atlas :=
      fun x =>
        by 
          simp only [mem_Union, mem_singleton_iff]
          exact ⟨c.chart_at x, c.chart_mem_atlas x, rfl⟩ }

end ChartedSpaceCore

/-! ### Charted space with a given structure groupoid -/


section HasGroupoid

variable[TopologicalSpace H][TopologicalSpace M][ChartedSpace H M]

/-- A charted space has an atlas in a groupoid `G` if the change of coordinates belong to the
groupoid -/
class
  HasGroupoid{H :
    Type _}[TopologicalSpace H](M : Type _)[TopologicalSpace M][ChartedSpace H M](G : StructureGroupoid H) :
  Prop where 
  compatible{} : ∀ {e e' : LocalHomeomorph M H}, e ∈ atlas H M → e' ∈ atlas H M → e.symm ≫ₕ e' ∈ G

/-- Reformulate in the `structure_groupoid` namespace the compatibility condition of charts in a
charted space admitting a structure groupoid, to make it more easily accessible with dot
notation. -/
theorem StructureGroupoid.compatible {H : Type _} [TopologicalSpace H] (G : StructureGroupoid H) {M : Type _}
  [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G] {e e' : LocalHomeomorph M H} (he : e ∈ atlas H M)
  (he' : e' ∈ atlas H M) : e.symm ≫ₕ e' ∈ G :=
  HasGroupoid.compatible G he he'

theorem has_groupoid_of_le {G₁ G₂ : StructureGroupoid H} (h : HasGroupoid M G₁) (hle : G₁ ≤ G₂) : HasGroupoid M G₂ :=
  ⟨fun e e' he he' => hle ((h.compatible : _) he he')⟩

theorem has_groupoid_of_pregroupoid (PG : Pregroupoid H)
  (h :
    ∀ {e e' : LocalHomeomorph M H}, e ∈ atlas H M → e' ∈ atlas H M → PG.property (e.symm ≫ₕ e') (e.symm ≫ₕ e').Source) :
  HasGroupoid M PG.groupoid :=
  ⟨fun e e' he he' => mem_groupoid_of_pregroupoid.mpr ⟨h he he', h he' he⟩⟩

/-- The trivial charted space structure on the model space is compatible with any groupoid -/
instance has_groupoid_model_space (H : Type _) [TopologicalSpace H] (G : StructureGroupoid H) : HasGroupoid H G :=
  { compatible :=
      fun e e' he he' =>
        by 
          replace he : e ∈ atlas H H := he 
          replace he' : e' ∈ atlas H H := he' 
          rw [charted_space_self_atlas] at he he' 
          simp [he, he', StructureGroupoid.id_mem] }

/-- Any charted space structure is compatible with the groupoid of all local homeomorphisms -/
instance has_groupoid_continuous_groupoid : HasGroupoid M (continuousGroupoid H) :=
  ⟨by 
      intro e e' he he' 
      rw [continuousGroupoid, mem_groupoid_of_pregroupoid]
      simp only [and_selfₓ]⟩

section MaximalAtlas

variable(M)(G : StructureGroupoid H)

/-- Given a charted space admitting a structure groupoid, the maximal atlas associated to this
structure groupoid is the set of all local charts that are compatible with the atlas, i.e., such
that changing coordinates with an atlas member gives an element of the groupoid. -/
def StructureGroupoid.MaximalAtlas : Set (LocalHomeomorph M H) :=
  { e | ∀ e' _ : e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G }

variable{M}

/-- The elements of the atlas belong to the maximal atlas for any structure groupoid -/
theorem StructureGroupoid.mem_maximal_atlas_of_mem_atlas [HasGroupoid M G] {e : LocalHomeomorph M H}
  (he : e ∈ atlas H M) : e ∈ G.maximal_atlas M :=
  fun e' he' => ⟨G.compatible he he', G.compatible he' he⟩

theorem StructureGroupoid.chart_mem_maximal_atlas [HasGroupoid M G] (x : M) : chart_at H x ∈ G.maximal_atlas M :=
  G.mem_maximal_atlas_of_mem_atlas (chart_mem_atlas H x)

variable{G}

theorem mem_maximal_atlas_iff {e : LocalHomeomorph M H} :
  e ∈ G.maximal_atlas M ↔ ∀ e' _ : e' ∈ atlas H M, e.symm ≫ₕ e' ∈ G ∧ e'.symm ≫ₕ e ∈ G :=
  Iff.rfl

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Changing coordinates between two elements of the maximal atlas gives rise to an element
of the structure groupoid. -/
theorem structure_groupoid.compatible_of_mem_maximal_atlas
{e e' : local_homeomorph M H}
(he : «expr ∈ »(e, G.maximal_atlas M))
(he' : «expr ∈ »(e', G.maximal_atlas M)) : «expr ∈ »(«expr ≫ₕ »(e.symm, e'), G) :=
begin
  apply [expr G.locality (λ x hx, _)],
  set [] [ident f] [] [":="] [expr chart_at H (e.symm x)] ["with", ident hf],
  let [ident s] [] [":=", expr «expr ∩ »(e.target, «expr ⁻¹' »(e.symm, f.source))],
  have [ident hs] [":", expr is_open s] [],
  { apply [expr e.symm.continuous_to_fun.preimage_open_of_open]; apply [expr open_source] },
  have [ident xs] [":", expr «expr ∈ »(x, s)] [],
  by { dsimp [] [] [] ["at", ident hx],
    simp [] [] [] ["[", expr s, ",", expr hx, "]"] [] [] },
  refine [expr ⟨s, hs, xs, _⟩],
  have [ident A] [":", expr «expr ∈ »(«expr ≫ₕ »(e.symm, f), G)] [":=", expr (mem_maximal_atlas_iff.1 he f (chart_mem_atlas _ _)).1],
  have [ident B] [":", expr «expr ∈ »(«expr ≫ₕ »(f.symm, e'), G)] [":=", expr (mem_maximal_atlas_iff.1 he' f (chart_mem_atlas _ _)).2],
  have [ident C] [":", expr «expr ∈ »(«expr ≫ₕ »(«expr ≫ₕ »(e.symm, f), «expr ≫ₕ »(f.symm, e')), G)] [":=", expr G.trans A B],
  have [ident D] [":", expr «expr ≈ »(«expr ≫ₕ »(«expr ≫ₕ »(e.symm, f), «expr ≫ₕ »(f.symm, e')), «expr ≫ₕ »(e.symm, e').restr s)] [":=", expr calc
     «expr = »(«expr ≫ₕ »(«expr ≫ₕ »(e.symm, f), «expr ≫ₕ »(f.symm, e')), «expr ≫ₕ »(e.symm, «expr ≫ₕ »(«expr ≫ₕ »(f, f.symm), e'))) : by simp [] [] [] ["[", expr trans_assoc, "]"] [] []
     «expr ≈ »(..., «expr ≫ₕ »(e.symm, «expr ≫ₕ »(of_set f.source f.open_source, e'))) : by simp [] [] [] ["[", expr eq_on_source.trans', ",", expr trans_self_symm, "]"] [] []
     «expr ≈ »(..., «expr ≫ₕ »(«expr ≫ₕ »(e.symm, of_set f.source f.open_source), e')) : by simp [] [] [] ["[", expr trans_assoc, "]"] [] []
     «expr ≈ »(..., «expr ≫ₕ »(e.symm.restr s, e')) : by simp [] [] [] ["[", expr s, ",", expr trans_of_set', "]"] [] []
     «expr ≈ »(..., «expr ≫ₕ »(e.symm, e').restr s) : by simp [] [] [] ["[", expr restr_trans, "]"] [] []],
  exact [expr G.eq_on_source C (setoid.symm D)]
end

variable(G)

/-- In the model space, the identity is in any maximal atlas. -/
theorem StructureGroupoid.id_mem_maximal_atlas : LocalHomeomorph.refl H ∈ G.maximal_atlas H :=
  G.mem_maximal_atlas_of_mem_atlas
    (by 
      simp )

end MaximalAtlas

section Singleton

variable{α : Type _}[TopologicalSpace α]

namespace LocalHomeomorph

variable(e : LocalHomeomorph α H)

/-- If a single local homeomorphism `e` from a space `α` into `H` has source covering the whole
space `α`, then that local homeomorphism induces an `H`-charted space structure on `α`.
(This condition is equivalent to `e` being an open embedding of `α` into `H`; see
`open_embedding.singleton_charted_space`.) -/
def singleton_charted_space (h : e.source = Set.Univ) : ChartedSpace H α :=
  { Atlas := {e}, chartAt := fun _ => e,
    mem_chart_source :=
      fun _ =>
        by 
          simp' only [h] with mfld_simps,
    chart_mem_atlas :=
      fun _ =>
        by 
          tauto }

@[simp, mfld_simps]
theorem singleton_charted_space_chart_at_eq (h : e.source = Set.Univ) {x : α} :
  @chart_at H _ α _ (e.singleton_charted_space h) x = e :=
  rfl

theorem singleton_charted_space_chart_at_source (h : e.source = Set.Univ) {x : α} :
  (@chart_at H _ α _ (e.singleton_charted_space h) x).Source = Set.Univ :=
  h

theorem singleton_charted_space_mem_atlas_eq (h : e.source = Set.Univ) (e' : LocalHomeomorph α H)
  (h' : e' ∈ (e.singleton_charted_space h).Atlas) : e' = e :=
  h'

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a local homeomorphism `e` from a space `α` into `H`, if its source covers the whole
space `α`, then the induced charted space structure on `α` is `has_groupoid G` for any structure
groupoid `G` which is closed under restrictions. -/
theorem singleton_has_groupoid
(h : «expr = »(e.source, set.univ))
(G : structure_groupoid H)
[closed_under_restriction G] : @has_groupoid _ _ _ _ (e.singleton_charted_space h) G :=
{ compatible := begin
    intros [ident e', ident e'', ident he', ident he''],
    rw [expr e.singleton_charted_space_mem_atlas_eq h e' he'] [],
    rw [expr e.singleton_charted_space_mem_atlas_eq h e'' he''] [],
    refine [expr G.eq_on_source _ e.trans_symm_self],
    have [ident hle] [":", expr «expr ≤ »(id_restr_groupoid, G)] [":=", expr (closed_under_restriction_iff_id_le G).mp (by assumption)],
    exact [expr structure_groupoid.le_iff.mp hle _ (id_restr_groupoid_mem _)]
  end }

end LocalHomeomorph

namespace OpenEmbedding

variable[Nonempty α]

/-- An open embedding of `α` into `H` induces an `H`-charted space structure on `α`.
See `local_homeomorph.singleton_charted_space` -/
def singleton_charted_space {f : α → H} (h : OpenEmbedding f) : ChartedSpace H α :=
  (h.to_local_homeomorph f).singletonChartedSpace
    (by 
      simp )

theorem singleton_charted_space_chart_at_eq {f : α → H} (h : OpenEmbedding f) {x : α} :
  «expr⇑ » (@chart_at H _ α _ h.singleton_charted_space x) = f :=
  rfl

theorem singleton_has_groupoid {f : α → H} (h : OpenEmbedding f) (G : StructureGroupoid H) [ClosedUnderRestriction G] :
  @HasGroupoid _ _ _ _ h.singleton_charted_space G :=
  (h.to_local_homeomorph f).singleton_has_groupoid
    (by 
      simp )
    G

end OpenEmbedding

end Singleton

namespace TopologicalSpace.Opens

open TopologicalSpace

variable(G : StructureGroupoid H)[HasGroupoid M G]

variable(s : opens M)

/-- An open subset of a charted space is naturally a charted space. -/
instance  : ChartedSpace H s :=
  { Atlas := ⋃x : s, {@LocalHomeomorph.subtypeRestr _ _ _ _ (chart_at H x.1) s ⟨x⟩},
    chartAt := fun x => @LocalHomeomorph.subtypeRestr _ _ _ _ (chart_at H x.1) s ⟨x⟩,
    mem_chart_source :=
      fun x =>
        by 
          simp' only with mfld_simps 
          exact mem_chart_source H x.1,
    chart_mem_atlas :=
      fun x =>
        by 
          simp only [mem_Union, mem_singleton_iff]
          use x }

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a groupoid `G` is `closed_under_restriction`, then an open subset of a space which is
`has_groupoid G` is naturally `has_groupoid G`. -/ instance [closed_under_restriction G] : has_groupoid s G :=
{ compatible := begin
    rintros [ident e, ident e', "⟨", "_", ",", "⟨", ident x, ",", ident hc, "⟩", ",", ident he, "⟩", "⟨", "_", ",", "⟨", ident x', ",", ident hc', "⟩", ",", ident he', "⟩"],
    haveI [] [":", expr nonempty s] [":=", expr ⟨x⟩],
    simp [] [] ["only"] ["[", expr hc.symm, ",", expr mem_singleton_iff, ",", expr subtype.val_eq_coe, "]"] [] ["at", ident he],
    simp [] [] ["only"] ["[", expr hc'.symm, ",", expr mem_singleton_iff, ",", expr subtype.val_eq_coe, "]"] [] ["at", ident he'],
    rw ["[", expr he, ",", expr he', "]"] [],
    convert [] [expr G.eq_on_source _ (subtype_restr_symm_trans_subtype_restr s (chart_at H x) (chart_at H x'))] [],
    apply [expr closed_under_restriction'],
    { exact [expr G.compatible (chart_mem_atlas H x) (chart_mem_atlas H x')] },
    { exact [expr preimage_open_of_open_symm (chart_at H x) s.2] }
  end }

end TopologicalSpace.Opens

/-! ### Structomorphisms -/


/-- A `G`-diffeomorphism between two charted spaces is a homeomorphism which, when read in the
charts, belongs to `G`. We avoid the word diffeomorph as it is too related to the smooth category,
and use structomorph instead. -/
@[nolint has_inhabited_instance]
structure
  Structomorph(G :
    StructureGroupoid
      H)(M : Type _)(M' : Type _)[TopologicalSpace M][TopologicalSpace M'][ChartedSpace H M][ChartedSpace H M'] extends
  Homeomorph M M' where 
  mem_groupoid :
  ∀ c : LocalHomeomorph M H,
    ∀ c' : LocalHomeomorph M' H, c ∈ atlas H M → c' ∈ atlas H M' → c.symm ≫ₕ to_homeomorph.to_local_homeomorph ≫ₕ c' ∈ G

variable[TopologicalSpace M'][TopologicalSpace M'']{G : StructureGroupoid H}[ChartedSpace H M'][ChartedSpace H M'']

/-- The identity is a diffeomorphism of any charted space, for any groupoid. -/
def Structomorph.refl (M : Type _) [TopologicalSpace M] [ChartedSpace H M] [HasGroupoid M G] : Structomorph G M M :=
  { Homeomorph.refl M with
    mem_groupoid :=
      fun c c' hc hc' =>
        by 
          change LocalHomeomorph.symm c ≫ₕ LocalHomeomorph.refl M ≫ₕ c' ∈ G 
          rw [LocalHomeomorph.refl_trans]
          exact HasGroupoid.compatible G hc hc' }

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inverse of a structomorphism is a structomorphism -/
def structomorph.symm (e : structomorph G M M') : structomorph G M' M :=
{ mem_groupoid := begin
    assume [binders (c c' hc hc')],
    have [] [":", expr «expr ∈ »(«expr ≫ₕ »(c'.symm, «expr ≫ₕ »(e.to_homeomorph.to_local_homeomorph, c)).symm, G)] [":=", expr G.symm (e.mem_groupoid c' c hc' hc)],
    rwa ["[", expr trans_symm_eq_symm_trans_symm, ",", expr trans_symm_eq_symm_trans_symm, ",", expr symm_symm, ",", expr trans_assoc, "]"] ["at", ident this]
  end,
  ..e.to_homeomorph.symm }

-- error in Geometry.Manifold.ChartedSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The composition of structomorphisms is a structomorphism -/
def structomorph.trans (e : structomorph G M M') (e' : structomorph G M' M'') : structomorph G M M'' :=
{ mem_groupoid := begin
    assume [binders (c c' hc hc')],
    refine [expr G.locality (λ x hx, _)],
    let [ident f₁] [] [":=", expr e.to_homeomorph.to_local_homeomorph],
    let [ident f₂] [] [":=", expr e'.to_homeomorph.to_local_homeomorph],
    let [ident f] [] [":=", expr (e.to_homeomorph.trans e'.to_homeomorph).to_local_homeomorph],
    have [ident feq] [":", expr «expr = »(f, «expr ≫ₕ »(f₁, f₂))] [":=", expr homeomorph.trans_to_local_homeomorph _ _],
    let [ident y] [] [":=", expr «expr ≫ₕ »(c.symm, f₁) x],
    let [ident g] [] [":=", expr chart_at H y],
    have [ident hg₁] [] [":=", expr chart_mem_atlas H y],
    have [ident hg₂] [] [":=", expr mem_chart_source H y],
    let [ident s] [] [":=", expr «expr ∩ »(«expr ≫ₕ »(c.symm, f₁).source, «expr ⁻¹' »(«expr ≫ₕ »(c.symm, f₁), g.source))],
    have [ident open_s] [":", expr is_open s] [],
    by apply [expr «expr ≫ₕ »(c.symm, f₁).continuous_to_fun.preimage_open_of_open]; apply [expr open_source],
    have [] [":", expr «expr ∈ »(x, s)] [],
    { split,
      { simp [] [] ["only"] ["[", expr trans_source, ",", expr preimage_univ, ",", expr inter_univ, ",", expr homeomorph.to_local_homeomorph_source, "]"] [] [],
        rw [expr trans_source] ["at", ident hx],
        exact [expr hx.1] },
      { exact [expr hg₂] } },
    refine [expr ⟨s, open_s, this, _⟩],
    let [ident F₁] [] [":=", expr «expr ≫ₕ »(«expr ≫ₕ »(c.symm, «expr ≫ₕ »(f₁, g)), «expr ≫ₕ »(g.symm, «expr ≫ₕ »(f₂, c')))],
    have [ident A] [":", expr «expr ∈ »(F₁, G)] [":=", expr G.trans (e.mem_groupoid c g hc hg₁) (e'.mem_groupoid g c' hg₁ hc')],
    let [ident F₂] [] [":=", expr «expr ≫ₕ »(c.symm, «expr ≫ₕ »(f, c')).restr s],
    have [] [":", expr «expr ≈ »(F₁, F₂)] [":=", expr calc
       «expr ≈ »(F₁, «expr ≫ₕ »(c.symm, «expr ≫ₕ »(f₁, «expr ≫ₕ »(«expr ≫ₕ »(g, g.symm), «expr ≫ₕ »(f₂, c'))))) : by simp [] [] [] ["[", expr F₁, ",", expr trans_assoc, "]"] [] []
       «expr ≈ »(..., «expr ≫ₕ »(c.symm, «expr ≫ₕ »(f₁, «expr ≫ₕ »(of_set g.source g.open_source, «expr ≫ₕ »(f₂, c'))))) : by simp [] [] [] ["[", expr eq_on_source.trans', ",", expr trans_self_symm g, "]"] [] []
       «expr ≈ »(..., «expr ≫ₕ »(«expr ≫ₕ »(«expr ≫ₕ »(c.symm, f₁), of_set g.source g.open_source), «expr ≫ₕ »(f₂, c'))) : by simp [] [] [] ["[", expr trans_assoc, "]"] [] []
       «expr ≈ »(..., «expr ≫ₕ »(«expr ≫ₕ »(c.symm, f₁).restr s, «expr ≫ₕ »(f₂, c'))) : by simp [] [] [] ["[", expr s, ",", expr trans_of_set', "]"] [] []
       «expr ≈ »(..., «expr ≫ₕ »(«expr ≫ₕ »(c.symm, f₁), «expr ≫ₕ »(f₂, c')).restr s) : by simp [] [] [] ["[", expr restr_trans, "]"] [] []
       «expr ≈ »(..., «expr ≫ₕ »(c.symm, «expr ≫ₕ »(«expr ≫ₕ »(f₁, f₂), c')).restr s) : by simp [] [] [] ["[", expr eq_on_source.restr, ",", expr trans_assoc, "]"] [] []
       «expr ≈ »(..., F₂) : by simp [] [] [] ["[", expr F₂, ",", expr feq, "]"] [] []],
    have [] [":", expr «expr ∈ »(F₂, G)] [":=", expr G.eq_on_source A (setoid.symm this)],
    exact [expr this]
  end,
  ..homeomorph.trans e.to_homeomorph e'.to_homeomorph }

end HasGroupoid

