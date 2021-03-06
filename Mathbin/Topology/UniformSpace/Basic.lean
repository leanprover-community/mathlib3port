/-
Copyright (c) 2017 Johannes HΓΆlzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes HΓΆlzl, Mario Carneiro, Patrick Massot
-/
import Mathbin.Order.Filter.SmallSets
import Mathbin.Topology.SubsetProperties

/-!
# Uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups. Many concepts directly
generalize to uniform spaces, e.g.

* uniform continuity (in this file)
* completeness (in `cauchy.lean`)
* extension of uniform continuous functions to complete spaces (in `uniform_embedding.lean`)
* totally bounded sets (in `cauchy.lean`)
* totally bounded complete sets are compact (in `cauchy.lean`)

A uniform structure on a type `X` is a filter `π€ X` on `X Γ X` satisfying some conditions
which makes it reasonable to say that `βαΆ  (p : X Γ X) in π€ X, ...` means
"for all p.1 and p.2 in X close enough, ...". Elements of this filter are called entourages
of `X`. The two main examples are:

* If `X` is a metric space, `V β π€ X β β Ξ΅ > 0, { p | dist p.1 p.2 < Ξ΅ } β V`
* If `G` is an additive topological group, `V β π€ G β β U β π (0 : G), {p | p.2 - p.1 β U} β V`

Those examples are generalizations in two different directions of the elementary example where
`X = β` and `V β π€ β β β Ξ΅ > 0, { p | |p.2 - p.1| < Ξ΅ } β V` which features both the topological
group structure on `β` and its metric space structure.

Each uniform structure on `X` induces a topology on `X` characterized by

> `nhds_eq_comap_uniformity : β {x : X}, π x = comap (prod.mk x) (π€ X)`

where `prod.mk x : X β X Γ X := (Ξ» y, (x, y))` is the partial evaluation of the product
constructor.

The dictionary with metric spaces includes:
* an upper bound for `dist x y` translates into `(x, y) β V` for some `V β π€ X`
* a ball `ball x r` roughly corresponds to `uniform_space.ball x V := {y | (x, y) β V}`
  for some `V β π€ X`, but the later is more general (it includes in
  particular both open and closed balls for suitable `V`).
  In particular we have:
  `is_open_iff_ball_subset {s : set X} : is_open s β β x β s, β V β π€ X, ball x V β s`

The triangle inequality is abstracted to a statement involving the composition of relations in `X`.
First note that the triangle inequality in a metric space is equivalent to
`β (x y z : X) (r r' : β), dist x y β€ r β dist y z β€ r' β dist x z β€ r + r'`.
Then, for any `V` and `W` with type `set (X Γ X)`, the composition `V β W : set (X Γ X)` is
defined as `{ p : X Γ X | β z, (p.1, z) β V β§ (z, p.2) β W }`.
In the metric space case, if `V = { p | dist p.1 p.2 β€ r }` and `W = { p | dist p.1 p.2 β€ r' }`
then the triangle inequality, as reformulated above, says `V β W` is contained in
`{p | dist p.1 p.2 β€ r + r'}` which is the entourage associated to the radius `r + r'`.
In general we have `mem_ball_comp (h : y β ball x V) (h' : z β ball y W) : z β ball x (V β W)`.
Note that this discussion does not depend on any axiom imposed on the uniformity filter,
it is simply captured by the definition of composition.

The uniform space axioms ask the filter `π€ X` to satisfy the following:
* every `V β π€ X` contains the diagonal `id_rel = { p | p.1 = p.2 }`. This abstracts the fact
  that `dist x x β€ r` for every non-negative radius `r` in the metric space case and also that
  `x - x` belongs to every neighborhood of zero in the topological group case.
* `V β π€ X β prod.swap '' V β π€ X`. This is tightly related the fact that `dist x y = dist y x`
  in a metric space, and to continuity of negation in the topological group case.
* `β V β π€ X, β W β π€ X, W β W β V`. In the metric space case, it corresponds
  to cutting the radius of a ball in half and applying the triangle inequality.
  In the topological group case, it comes from continuity of addition at `(0, 0)`.

These three axioms are stated more abstractly in the definition below, in terms of
operations on filters, without directly manipulating entourages.

##Β Main definitions

* `uniform_space X` is a uniform space structure on a type `X`
* `uniform_continuous f` is a predicate saying a function `f : Ξ± β Ξ²` between uniform spaces
  is uniformly continuous : `β r β π€ Ξ², βαΆ  (x : Ξ± Γ Ξ±) in π€ Ξ±, (f x.1, f x.2) β r`

In this file we also define a complete lattice structure on the type `uniform_space X`
of uniform structures on `X`, as well as the pullback (`uniform_space.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notations

Localized in `uniformity`, we have the notation `π€ X` for the uniformity on a uniform space `X`,
and `β` for composition of relations, seen as terms with type `set (X Γ X)`.

## Implementation notes

There is already a theory of relations in `data/rel.lean` where the main definition is
`def rel (Ξ± Ξ² : Type*) := Ξ± β Ξ² β Prop`.
The relations used in the current file involve only one type, but this is not the reason why
we don't reuse `data/rel.lean`. We use `set (Ξ± Γ Ξ±)`
instead of `rel Ξ± Ξ±` because we really need sets to use the filter library, and elements
of filters on `Ξ± Γ Ξ±` have type `set (Ξ± Γ Ξ±)`.

The structure `uniform_space X` bundles a uniform structure on `X`, a topology on `X` and
an assumption saying those are compatible. This may not seem mathematically reasonable at first,
but is in fact an instance of the forgetful inheritance pattern. See Note [forgetful inheritance]
below.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/


open Set Filter Classical

open Classical TopologicalSpace Filter

-- ./././Mathport/Syntax/Translate/Basic.lean:304:40: warning: unsupported option eqn_compiler.zeta
set_option eqn_compiler.zeta true

universe u

/-!
### Relations, seen as `set (Ξ± Γ Ξ±)`
-/


variable {Ξ± : Type _} {Ξ² : Type _} {Ξ³ : Type _} {Ξ΄ : Type _} {ΞΉ : Sort _}

/-- The identity relation, or the graph of the identity function -/
def IdRel {Ξ± : Type _} :=
  { p : Ξ± Γ Ξ± | p.1 = p.2 }

@[simp]
theorem mem_id_rel {a b : Ξ±} : (a, b) β @IdRel Ξ± β a = b :=
  Iff.rfl

@[simp]
theorem id_rel_subset {s : Set (Ξ± Γ Ξ±)} : IdRel β s β β a, (a, a) β s := by
  simp [β subset_def] <;>
    exact
      forall_congrβ fun a => by
        simp

/-- The composition of relations -/
def CompRel {Ξ± : Type u} (rβ rβ : Set (Ξ± Γ Ξ±)) :=
  { p : Ξ± Γ Ξ± | β z : Ξ±, (p.1, z) β rβ β§ (z, p.2) β rβ }

-- mathport name: Β«expr β Β»
localized [uniformity] infixl:55 " β " => CompRel

@[simp]
theorem mem_comp_rel {rβ rβ : Set (Ξ± Γ Ξ±)} {x y : Ξ±} : (x, y) β rβ β rβ β β z, (x, z) β rβ β§ (z, y) β rβ :=
  Iff.rfl

@[simp]
theorem swap_id_rel : Prod.swap '' IdRel = @IdRel Ξ± :=
  Set.ext fun β¨a, bβ© => by
    simp [β image_swap_eq_preimage_swap] <;> exact eq_comm

theorem monotone_comp_rel [Preorderβ Ξ²] {f g : Ξ² β Set (Ξ± Γ Ξ±)} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x β g x := fun a b h p β¨z, hβ, hββ© => β¨z, hf h hβ, hg h hββ©

@[mono]
theorem comp_rel_mono {f g h k : Set (Ξ± Γ Ξ±)} (hβ : f β h) (hβ : g β k) : f β g β h β k := fun β¨x, yβ© β¨z, h, h'β© =>
  β¨z, hβ h, hβ h'β©

theorem prod_mk_mem_comp_rel {a b c : Ξ±} {s t : Set (Ξ± Γ Ξ±)} (hβ : (a, c) β s) (hβ : (c, b) β t) : (a, b) β s β t :=
  β¨c, hβ, hββ©

@[simp]
theorem id_comp_rel {r : Set (Ξ± Γ Ξ±)} : IdRel β r = r :=
  Set.ext fun β¨a, bβ© => by
    simp

theorem comp_rel_assoc {r s t : Set (Ξ± Γ Ξ±)} : r β s β t = r β (s β t) := by
  ext p <;> cases p <;> simp only [β mem_comp_rel] <;> tauto

theorem left_subset_comp_rel {s t : Set (Ξ± Γ Ξ±)} (h : IdRel β t) : s β s β t := fun β¨x, yβ© xy_in => β¨y, xy_in, h <| rflβ©

theorem right_subset_comp_rel {s t : Set (Ξ± Γ Ξ±)} (h : IdRel β s) : t β s β t := fun β¨x, yβ© xy_in =>
  β¨x, h <| rfl, xy_inβ©

theorem subset_comp_self {s : Set (Ξ± Γ Ξ±)} (h : IdRel β s) : s β s β s :=
  left_subset_comp_rel h

theorem subset_iterate_comp_rel {s t : Set (Ξ± Γ Ξ±)} (h : IdRel β s) (n : β) : t β ((Β· β Β·) s^[n]) t := by
  induction' n with n ihn generalizing t
  exacts[subset.rfl, (right_subset_comp_rel h).trans ihn]

/-- The relation is invariant under swapping factors. -/
def SymmetricRel (V : Set (Ξ± Γ Ξ±)) : Prop :=
  Prod.swap β»ΒΉ' V = V

/-- The maximal symmetric relation contained in a given relation. -/
def SymmetrizeRel (V : Set (Ξ± Γ Ξ±)) : Set (Ξ± Γ Ξ±) :=
  V β© Prod.swap β»ΒΉ' V

theorem symmetric_symmetrize_rel (V : Set (Ξ± Γ Ξ±)) : SymmetricRel (SymmetrizeRel V) := by
  simp [β SymmetricRel, β SymmetrizeRel, β preimage_inter, β inter_comm, preimage_comp]

theorem symmetrize_rel_subset_self (V : Set (Ξ± Γ Ξ±)) : SymmetrizeRel V β V :=
  sep_subset _ _

@[mono]
theorem symmetrize_mono {V W : Set (Ξ± Γ Ξ±)} (h : V β W) : SymmetrizeRel V β SymmetrizeRel W :=
  inter_subset_inter h <| preimage_mono h

theorem SymmetricRel.mk_mem_comm {V : Set (Ξ± Γ Ξ±)} (hV : SymmetricRel V) {x y : Ξ±} : (x, y) β V β (y, x) β V :=
  Set.ext_iff.1 hV (y, x)

theorem symmetric_rel_inter {U V : Set (Ξ± Γ Ξ±)} (hU : SymmetricRel U) (hV : SymmetricRel V) : SymmetricRel (U β© V) := by
  unfold SymmetricRel  at *
  rw [preimage_inter, hU, hV]

/-- This core description of a uniform space is outside of the type class hierarchy. It is useful
  for constructions of uniform spaces, when the topology is derived from the uniform space. -/
structure UniformSpace.Core (Ξ± : Type u) where
  uniformity : Filter (Ξ± Γ Ξ±)
  refl : π IdRel β€ uniformity
  symm : Tendsto Prod.swap uniformity uniformity
  comp : (uniformity.lift' fun s => s β s) β€ uniformity

/-- An alternative constructor for `uniform_space.core`. This version unfolds various
`filter`-related definitions. -/
def UniformSpace.Core.mk' {Ξ± : Type u} (U : Filter (Ξ± Γ Ξ±)) (refl : β, β r β U, β (x), (x, x) β r)
    (symm : β, β r β U, β, Prod.swap β»ΒΉ' r β U) (comp : β, β r β U, β, β t β U, t β t β r) : UniformSpace.Core Ξ± :=
  β¨U, fun r ru => id_rel_subset.2 (refl _ ru), symm, by
    intro r ru
    rw [mem_lift'_sets]
    exact comp _ ru
    apply monotone_comp_rel <;> exact monotone_idβ©

/-- Defining an `uniform_space.core` from a filter basis satisfying some uniformity-like axioms. -/
def UniformSpace.Core.mkOfBasis {Ξ± : Type u} (B : FilterBasis (Ξ± Γ Ξ±)) (refl : β, β r β B, β (x), (x, x) β r)
    (symm : β, β r β B, β, β t β B, t β Prod.swap β»ΒΉ' r) (comp : β, β r β B, β, β t β B, t β t β r) :
    UniformSpace.Core Ξ± where
  uniformity := B.filter
  refl := B.HasBasis.ge_iff.mpr fun r ru => id_rel_subset.2 <| refl _ ru
  symm := (B.HasBasis.tendsto_iff B.HasBasis).mpr symm
  comp := (HasBasis.le_basis_iff (B.HasBasis.lift' (monotone_comp_rel monotone_id monotone_id)) B.HasBasis).mpr comp

/-- A uniform space generates a topological space -/
def UniformSpace.Core.toTopologicalSpace {Ξ± : Type u} (u : UniformSpace.Core Ξ±) : TopologicalSpace Ξ± where
  IsOpen := fun s => β, β x β s, β, { p : Ξ± Γ Ξ± | p.1 = x β p.2 β s } β u.uniformity
  is_open_univ := by
    simp <;> intro <;> exact univ_mem
  is_open_inter := fun s t hs ht x β¨xs, xtβ© => by
    filter_upwards [hs x xs, ht x xt] <;> simp (config := { contextual := true })
  is_open_sUnion := fun s hs x β¨t, ts, xtβ© => by
    filter_upwards [hs t ts x xt] with p ph h usingβ¨t, ts, ph hβ©

theorem UniformSpace.core_eq : β {uβ uβ : UniformSpace.Core Ξ±}, uβ.uniformity = uβ.uniformity β uβ = uβ
  | β¨uβ, _, _, _β©, β¨uβ, _, _, _β©, h => by
    congr
    exact h

/-- A uniform space is a generalization of the "uniform" topological aspects of a
  metric space. It consists of a filter on `Ξ± Γ Ξ±` called the "uniformity", which
  satisfies properties analogous to the reflexivity, symmetry, and triangle properties
  of a metric.

  A metric space has a natural uniformity, and a uniform space has a natural topology.
  A topological group also has a natural uniformity, even when it is not metrizable. -/
-- the topological structure is embedded in the uniform structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].
class UniformSpace (Ξ± : Type u) extends TopologicalSpace Ξ±, UniformSpace.Core Ξ± where
  is_open_uniformity : β s, IsOpen s β β, β x β s, β, { p : Ξ± Γ Ξ± | p.1 = x β p.2 β s } β uniformity

/-- Alternative constructor for `uniform_space Ξ±` when a topology is already given. -/
@[matchPattern]
def UniformSpace.mk' {Ξ±} (t : TopologicalSpace Ξ±) (c : UniformSpace.Core Ξ±)
    (is_open_uniformity : β s : Set Ξ±, t.IsOpen s β β, β x β s, β, { p : Ξ± Γ Ξ± | p.1 = x β p.2 β s } β c.uniformity) :
    UniformSpace Ξ± :=
  β¨c, is_open_uniformityβ©

/-- Construct a `uniform_space` from a `uniform_space.core`. -/
def UniformSpace.ofCore {Ξ± : Type u} (u : UniformSpace.Core Ξ±) : UniformSpace Ξ± where
  toCore := u
  toTopologicalSpace := u.toTopologicalSpace
  is_open_uniformity := fun a => Iff.rfl

/-- Construct a `uniform_space` from a `u : uniform_space.core` and a `topological_space` structure
that is equal to `u.to_topological_space`. -/
def UniformSpace.ofCoreEq {Ξ± : Type u} (u : UniformSpace.Core Ξ±) (t : TopologicalSpace Ξ±)
    (h : t = u.toTopologicalSpace) : UniformSpace Ξ± where
  toCore := u
  toTopologicalSpace := t
  is_open_uniformity := fun a => h.symm βΈ Iff.rfl

theorem UniformSpace.to_core_to_topological_space (u : UniformSpace Ξ±) :
    u.toCore.toTopologicalSpace = u.toTopologicalSpace :=
  topological_space_eq <|
    funext fun s => by
      rw [UniformSpace.Core.toTopologicalSpace, UniformSpace.is_open_uniformity]

@[ext]
theorem uniform_space_eq : β {uβ uβ : UniformSpace Ξ±}, uβ.uniformity = uβ.uniformity β uβ = uβ
  | UniformSpace.mk' tβ uβ oβ, UniformSpace.mk' tβ uβ oβ, h => by
    have : uβ = uβ := UniformSpace.core_eq h
    have : tβ = tβ :=
      topological_space_eq <|
        funext fun s => by
          rw [oβ, oβ] <;> simp [β this]
    simp [*]

theorem UniformSpace.of_core_eq_to_core (u : UniformSpace Ξ±) (t : TopologicalSpace Ξ±)
    (h : t = u.toCore.toTopologicalSpace) : UniformSpace.ofCoreEq u.toCore t h = u :=
  uniform_space_eq rfl

/-- Replace topology in a `uniform_space` instance with a propositionally (but possibly not
definitionally) equal one. -/
@[reducible]
def UniformSpace.replaceTopology {Ξ± : Type _} [i : TopologicalSpace Ξ±] (u : UniformSpace Ξ±)
    (h : i = u.toTopologicalSpace) : UniformSpace Ξ± :=
  UniformSpace.ofCoreEq u.toCore i <| h.trans u.to_core_to_topological_space.symm

theorem UniformSpace.replace_topology_eq {Ξ± : Type _} [i : TopologicalSpace Ξ±] (u : UniformSpace Ξ±)
    (h : i = u.toTopologicalSpace) : u.replaceTopology h = u :=
  u.of_core_eq_to_core _ _

section UniformSpace

variable [UniformSpace Ξ±]

/-- The uniformity is a filter on Ξ± Γ Ξ± (inferred from an ambient uniform space
  structure on Ξ±). -/
def uniformity (Ξ± : Type u) [UniformSpace Ξ±] : Filter (Ξ± Γ Ξ±) :=
  (@UniformSpace.toCore Ξ± _).uniformity

-- mathport name: Β«exprπ€Β»
localized [uniformity] notation "π€" => uniformity

theorem is_open_uniformity {s : Set Ξ±} : IsOpen s β β, β x β s, β, { p : Ξ± Γ Ξ± | p.1 = x β p.2 β s } β π€ Ξ± :=
  UniformSpace.is_open_uniformity s

theorem refl_le_uniformity : π IdRel β€ π€ Ξ± :=
  (@UniformSpace.toCore Ξ± _).refl

instance uniformity.ne_bot [Nonempty Ξ±] : NeBot (π€ Ξ±) := by
  inhabit Ξ±
  refine' (principal_ne_bot_iff.2 _).mono refl_le_uniformity
  exact β¨(default, default), rflβ©

theorem refl_mem_uniformity {x : Ξ±} {s : Set (Ξ± Γ Ξ±)} (h : s β π€ Ξ±) : (x, x) β s :=
  refl_le_uniformity h rfl

theorem mem_uniformity_of_eq {x y : Ξ±} {s : Set (Ξ± Γ Ξ±)} (h : s β π€ Ξ±) (hx : x = y) : (x, y) β s :=
  hx βΈ refl_mem_uniformity h

theorem symm_le_uniformity : map (@Prod.swap Ξ± Ξ±) (π€ _) β€ π€ _ :=
  (@UniformSpace.toCore Ξ± _).symm

theorem comp_le_uniformity : ((π€ Ξ±).lift' fun s : Set (Ξ± Γ Ξ±) => s β s) β€ π€ Ξ± :=
  (@UniformSpace.toCore Ξ± _).comp

theorem tendsto_swap_uniformity : Tendsto (@Prod.swap Ξ± Ξ±) (π€ Ξ±) (π€ Ξ±) :=
  symm_le_uniformity

theorem comp_mem_uniformity_sets {s : Set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) : β t β π€ Ξ±, t β t β s :=
  have : s β (π€ Ξ±).lift' fun t : Set (Ξ± Γ Ξ±) => t β t := comp_le_uniformity hs
  (mem_lift'_sets <| monotone_comp_rel monotone_id monotone_id).mp this

/-- If `s β π€ Ξ±`, then for any natural `n`, for a subset `t` of a sufficiently small set in `π€ Ξ±`,
we have `t β t β ... β t β s` (`n` compositions). -/
theorem eventually_uniformity_iterate_comp_subset {s : Set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) (n : β) :
    βαΆ  t in (π€ Ξ±).smallSets, ((Β· β Β·) t^[n]) t β s := by
  suffices : βαΆ  t in (π€ Ξ±).smallSets, t β s β§ ((Β· β Β·) t^[n]) t β s
  exact (eventually_and.1 this).2
  induction' n with n ihn generalizing s
  Β· simpa
    
  rcases comp_mem_uniformity_sets hs with β¨t, htU, htsβ©
  refine' (ihn htU).mono fun U hU => _
  rw [Function.iterate_succ_apply']
  exact β¨hU.1.trans <| (subset_comp_self <| refl_le_uniformity htU).trans hts, (comp_rel_mono hU.1 hU.2).trans htsβ©

/-- If `s β π€ Ξ±`, then for any natural `n`, for a subset `t` of a sufficiently small set in `π€ Ξ±`,
we have `t β t β s`. -/
theorem eventually_uniformity_comp_subset {s : Set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) : βαΆ  t in (π€ Ξ±).smallSets, t β t β s :=
  eventually_uniformity_iterate_comp_subset hs 1

/-- Relation `Ξ» f g, tendsto (Ξ» x, (f x, g x)) l (π€ Ξ±)` is transitive. -/
theorem Filter.Tendsto.uniformity_trans {l : Filter Ξ²} {fβ fβ fβ : Ξ² β Ξ±}
    (hββ : Tendsto (fun x => (fβ x, fβ x)) l (π€ Ξ±)) (hββ : Tendsto (fun x => (fβ x, fβ x)) l (π€ Ξ±)) :
    Tendsto (fun x => (fβ x, fβ x)) l (π€ Ξ±) := by
  refine' le_transβ (le_lift' fun s hs => mem_map.2 _) comp_le_uniformity
  filter_upwards [hββ hs, hββ hs] with x hxββ hxββ usingβ¨_, hxββ, hxβββ©

/-- Relation `Ξ» f g, tendsto (Ξ» x, (f x, g x)) l (π€ Ξ±)` is symmetric -/
theorem Filter.Tendsto.uniformity_symm {l : Filter Ξ²} {f : Ξ² β Ξ± Γ Ξ±} (h : Tendsto f l (π€ Ξ±)) :
    Tendsto (fun x => ((f x).2, (f x).1)) l (π€ Ξ±) :=
  tendsto_swap_uniformity.comp h

/-- Relation `Ξ» f g, tendsto (Ξ» x, (f x, g x)) l (π€ Ξ±)` is reflexive. -/
theorem tendsto_diag_uniformity (f : Ξ² β Ξ±) (l : Filter Ξ²) : Tendsto (fun x => (f x, f x)) l (π€ Ξ±) := fun s hs =>
  mem_map.2 <| univ_mem' fun x => refl_mem_uniformity hs

theorem tendsto_const_uniformity {a : Ξ±} {f : Filter Ξ²} : Tendsto (fun _ => (a, a)) f (π€ Ξ±) :=
  tendsto_diag_uniformity (fun _ => a) f

theorem symm_of_uniformity {s : Set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) : β t β π€ Ξ±, (β a b, (a, b) β t β (b, a) β t) β§ t β s :=
  have : Preimage Prod.swap s β π€ Ξ± := symm_le_uniformity hs
  β¨s β© Preimage Prod.swap s, inter_mem hs this, fun a b β¨hβ, hββ© => β¨hβ, hββ©, inter_subset_left _ _β©

theorem comp_symm_of_uniformity {s : Set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) :
    β t β π€ Ξ±, (β {a b}, (a, b) β t β (b, a) β t) β§ t β t β s :=
  let β¨t, htβ, htββ© := comp_mem_uniformity_sets hs
  let β¨t', ht', ht'β, ht'ββ© := symm_of_uniformity htβ
  β¨t', ht', ht'β, Subset.trans (monotone_comp_rel monotone_id monotone_id ht'β) htββ©

theorem uniformity_le_symm : π€ Ξ± β€ @Prod.swap Ξ± Ξ± <$> π€ Ξ± := by
  rw [map_swap_eq_comap_swap] <;> exact map_le_iff_le_comap.1 tendsto_swap_uniformity

theorem uniformity_eq_symm : π€ Ξ± = @Prod.swap Ξ± Ξ± <$> π€ Ξ± :=
  le_antisymmβ uniformity_le_symm symm_le_uniformity

@[simp]
theorem comap_swap_uniformity : comap (@Prod.swap Ξ± Ξ±) (π€ Ξ±) = π€ Ξ± :=
  (congr_arg _ uniformity_eq_symm).trans <| comap_map Prod.swap_injective

theorem symmetrize_mem_uniformity {V : Set (Ξ± Γ Ξ±)} (h : V β π€ Ξ±) : SymmetrizeRel V β π€ Ξ± := by
  apply (π€ Ξ±).inter_sets h
  rw [β image_swap_eq_preimage_swap, uniformity_eq_symm]
  exact image_mem_map h

theorem uniformity_lift_le_swap {g : Set (Ξ± Γ Ξ±) β Filter Ξ²} {f : Filter Ξ²} (hg : Monotone g)
    (h : ((π€ Ξ±).lift fun s => g (Preimage Prod.swap s)) β€ f) : (π€ Ξ±).lift g β€ f :=
  calc
    (π€ Ξ±).lift g β€ (Filter.map (@Prod.swap Ξ± Ξ±) <| π€ Ξ±).lift g := lift_mono uniformity_le_symm le_rfl
    _ β€ _ := by
      rw [map_lift_eq2 hg, image_swap_eq_preimage_swap] <;> exact h
    

theorem uniformity_lift_le_comp {f : Set (Ξ± Γ Ξ±) β Filter Ξ²} (h : Monotone f) :
    ((π€ Ξ±).lift fun s => f (s β s)) β€ (π€ Ξ±).lift f :=
  calc
    ((π€ Ξ±).lift fun s => f (s β s)) = ((π€ Ξ±).lift' fun s : Set (Ξ± Γ Ξ±) => s β s).lift f := by
      rw [lift_lift'_assoc]
      exact monotone_comp_rel monotone_id monotone_id
      exact h
    _ β€ (π€ Ξ±).lift f := lift_mono comp_le_uniformity le_rfl
    

theorem comp_le_uniformity3 : ((π€ Ξ±).lift' fun s : Set (Ξ± Γ Ξ±) => s β (s β s)) β€ π€ Ξ± :=
  calc
    ((π€ Ξ±).lift' fun d => d β (d β d)) = (π€ Ξ±).lift fun s => (π€ Ξ±).lift' fun t : Set (Ξ± Γ Ξ±) => s β (t β t) := by
      rw [lift_lift'_same_eq_lift']
      exact fun x => monotone_comp_rel monotone_const <| monotone_comp_rel monotone_id monotone_id
      exact fun x => monotone_comp_rel monotone_id monotone_const
    _ β€ (π€ Ξ±).lift fun s => (π€ Ξ±).lift' fun t : Set (Ξ± Γ Ξ±) => s β t :=
      lift_mono' fun s hs =>
        @uniformity_lift_le_comp Ξ± _ _ (π β (Β· β Β·) s) <|
          monotone_principal.comp (monotone_comp_rel monotone_const monotone_id)
    _ = (π€ Ξ±).lift' fun s : Set (Ξ± Γ Ξ±) => s β s :=
      lift_lift'_same_eq_lift' (fun s => monotone_comp_rel monotone_const monotone_id) fun s =>
        monotone_comp_rel monotone_id monotone_const
    _ β€ π€ Ξ± := comp_le_uniformity
    

/-- See also `comp_open_symm_mem_uniformity_sets`. -/
theorem comp_symm_mem_uniformity_sets {s : Set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) : β t β π€ Ξ±, SymmetricRel t β§ t β t β s := by
  obtain β¨w, w_in, w_subβ© : β w β π€ Ξ±, w β w β s := comp_mem_uniformity_sets hs
  use SymmetrizeRel w, symmetrize_mem_uniformity w_in, symmetric_symmetrize_rel w
  have : SymmetrizeRel w β w := symmetrize_rel_subset_self w
  calc SymmetrizeRel w β SymmetrizeRel w β w β w := by
      mono _ β s := w_sub

theorem subset_comp_self_of_mem_uniformity {s : Set (Ξ± Γ Ξ±)} (h : s β π€ Ξ±) : s β s β s :=
  subset_comp_self (refl_le_uniformity h)

theorem comp_comp_symm_mem_uniformity_sets {s : Set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) :
    β t β π€ Ξ±, SymmetricRel t β§ t β t β t β s := by
  rcases comp_symm_mem_uniformity_sets hs with β¨w, w_in, w_symm, w_subβ©
  rcases comp_symm_mem_uniformity_sets w_in with β¨t, t_in, t_symm, t_subβ©
  use t, t_in, t_symm
  have : t β t β t := subset_comp_self_of_mem_uniformity t_in
  calc t β t β t β w β t := by
      mono _ β w β (t β t) := by
      mono _ β w β w := by
      mono _ β s := w_sub

/-!
###Β Balls in uniform spaces
-/


/-- The ball around `(x : Ξ²)` with respect to `(V : set (Ξ² Γ Ξ²))`. Intended to be
used for `V β π€ Ξ²`, but this is not needed for the definition. Recovers the
notions of metric space ball when `V = {p | dist p.1 p.2 < r }`.  -/
def UniformSpace.Ball (x : Ξ²) (V : Set (Ξ² Γ Ξ²)) : Set Ξ² :=
  Prod.mk x β»ΒΉ' V

open UniformSpace (ball)

theorem UniformSpace.mem_ball_self (x : Ξ±) {V : Set (Ξ± Γ Ξ±)} (hV : V β π€ Ξ±) : x β Ball x V :=
  refl_mem_uniformity hV

/-- The triangle inequality for `uniform_space.ball` -/
theorem mem_ball_comp {V W : Set (Ξ² Γ Ξ²)} {x y z} (h : y β Ball x V) (h' : z β Ball y W) : z β Ball x (V β W) :=
  prod_mk_mem_comp_rel h h'

theorem ball_subset_of_comp_subset {V W : Set (Ξ² Γ Ξ²)} {x y} (h : x β Ball y W) (h' : W β W β V) :
    Ball x W β Ball y V := fun z z_in => h' (mem_ball_comp h z_in)

theorem ball_mono {V W : Set (Ξ² Γ Ξ²)} (h : V β W) (x : Ξ²) : Ball x V β Ball x W :=
  preimage_mono h

theorem ball_inter (x : Ξ²) (V W : Set (Ξ² Γ Ξ²)) : Ball x (V β© W) = Ball x V β© Ball x W :=
  preimage_inter

theorem ball_inter_left (x : Ξ²) (V W : Set (Ξ² Γ Ξ²)) : Ball x (V β© W) β Ball x V :=
  ball_mono (inter_subset_left V W) x

theorem ball_inter_right (x : Ξ²) (V W : Set (Ξ² Γ Ξ²)) : Ball x (V β© W) β Ball x W :=
  ball_mono (inter_subset_right V W) x

theorem mem_ball_symmetry {V : Set (Ξ² Γ Ξ²)} (hV : SymmetricRel V) {x y} : x β Ball y V β y β Ball x V :=
  show (x, y) β Prod.swap β»ΒΉ' V β (x, y) β V by
    unfold SymmetricRel  at hV
    rw [hV]

theorem ball_eq_of_symmetry {V : Set (Ξ² Γ Ξ²)} (hV : SymmetricRel V) {x} : Ball x V = { y | (y, x) β V } := by
  ext y
  rw [mem_ball_symmetry hV]
  exact Iff.rfl

theorem mem_comp_of_mem_ball {V W : Set (Ξ² Γ Ξ²)} {x y z : Ξ²} (hV : SymmetricRel V) (hx : x β Ball z V)
    (hy : y β Ball z W) : (x, y) β V β W := by
  rw [mem_ball_symmetry hV] at hx
  exact β¨z, hx, hyβ©

theorem UniformSpace.is_open_ball (x : Ξ±) {V : Set (Ξ± Γ Ξ±)} (hV : IsOpen V) : IsOpen (Ball x V) :=
  hV.Preimage <| continuous_const.prod_mk continuous_id

theorem mem_comp_comp {V W M : Set (Ξ² Γ Ξ²)} (hW' : SymmetricRel W) {p : Ξ² Γ Ξ²} :
    p β V β M β W β (Ball p.1 V ΓΛ’ Ball p.2 W β© M).Nonempty := by
  cases' p with x y
  constructor
  Β· rintro β¨z, β¨w, hpw, hwzβ©, hzyβ©
    exact
      β¨(w, z),
        β¨hpw, by
          rwa [mem_ball_symmetry hW']β©,
        hwzβ©
    
  Β· rintro β¨β¨w, zβ©, β¨w_in, z_inβ©, hwzβ©
    rwa [mem_ball_symmetry hW'] at z_in
    use z, w <;> tauto
    

/-!
### Neighborhoods in uniform spaces
-/


theorem mem_nhds_uniformity_iff_right {x : Ξ±} {s : Set Ξ±} : s β π x β { p : Ξ± Γ Ξ± | p.1 = x β p.2 β s } β π€ Ξ± := by
  refine' β¨_, fun hs => _β©
  Β· simp only [β mem_nhds_iff, β is_open_uniformity, β and_imp, β exists_imp_distrib]
    intro t ts ht xt
    filter_upwards [ht x xt] using fun y h eq => ts (h Eq)
    
  Β· refine' mem_nhds_iff.mpr β¨{ x | { p : Ξ± Γ Ξ± | p.1 = x β p.2 β s } β π€ Ξ± }, _, _, hsβ©
    Β· exact fun y hy => refl_mem_uniformity hy rfl
      
    Β· refine' is_open_uniformity.mpr fun y hy => _
      rcases comp_mem_uniformity_sets hy with β¨t, ht, trβ©
      filter_upwards [ht]
      rintro β¨a, bβ© hp' rfl
      filter_upwards [ht]
      rintro β¨a', b'β© hp'' rfl
      exact @tr (a, b') β¨a', hp', hp''β© rfl
      
    

theorem mem_nhds_uniformity_iff_left {x : Ξ±} {s : Set Ξ±} : s β π x β { p : Ξ± Γ Ξ± | p.2 = x β p.1 β s } β π€ Ξ± := by
  rw [uniformity_eq_symm, mem_nhds_uniformity_iff_right]
  rfl

theorem nhds_eq_comap_uniformity_aux {Ξ± : Type u} {x : Ξ±} {s : Set Ξ±} {F : Filter (Ξ± Γ Ξ±)} :
    { p : Ξ± Γ Ξ± | p.fst = x β p.snd β s } β F β s β comap (Prod.mk x) F := by
  rw [mem_comap] <;>
    exact
      Iff.intro (fun hs => β¨_, hs, fun x hx => hx rflβ©) fun β¨t, h, htβ© =>
        (F.sets_of_superset h) fun β¨pβ, pββ© hp (h : pβ = x) =>
          ht <| by
            simp [β h.symm, β hp]

theorem nhds_eq_comap_uniformity {x : Ξ±} : π x = (π€ Ξ±).comap (Prod.mk x) := by
  ext s
  rw [mem_nhds_uniformity_iff_right]
  exact nhds_eq_comap_uniformity_aux

/-- See also `is_open_iff_open_ball_subset`. -/
theorem is_open_iff_ball_subset {s : Set Ξ±} : IsOpen s β β, β x β s, β, β V β π€ Ξ±, Ball x V β s := by
  simp_rw [is_open_iff_mem_nhds, nhds_eq_comap_uniformity]
  exact Iff.rfl

theorem nhds_basis_uniformity' {p : ΞΉ β Prop} {s : ΞΉ β Set (Ξ± Γ Ξ±)} (h : (π€ Ξ±).HasBasis p s) {x : Ξ±} :
    (π x).HasBasis p fun i => Ball x (s i) := by
  rw [nhds_eq_comap_uniformity]
  exact h.comap (Prod.mk x)

theorem nhds_basis_uniformity {p : ΞΉ β Prop} {s : ΞΉ β Set (Ξ± Γ Ξ±)} (h : (π€ Ξ±).HasBasis p s) {x : Ξ±} :
    (π x).HasBasis p fun i => { y | (y, x) β s i } := by
  replace h := h.comap Prod.swap
  rw [β map_swap_eq_comap_swap, β uniformity_eq_symm] at h
  exact nhds_basis_uniformity' h

theorem UniformSpace.mem_nhds_iff {x : Ξ±} {s : Set Ξ±} : s β π x β β V β π€ Ξ±, Ball x V β s := by
  rw [nhds_eq_comap_uniformity, mem_comap]
  exact Iff.rfl

theorem UniformSpace.ball_mem_nhds (x : Ξ±) β¦V : Set (Ξ± Γ Ξ±)β¦ (V_in : V β π€ Ξ±) : Ball x V β π x := by
  rw [UniformSpace.mem_nhds_iff]
  exact β¨V, V_in, subset.refl _β©

theorem UniformSpace.mem_nhds_iff_symm {x : Ξ±} {s : Set Ξ±} : s β π x β β V β π€ Ξ±, SymmetricRel V β§ Ball x V β s := by
  rw [UniformSpace.mem_nhds_iff]
  constructor
  Β· rintro β¨V, V_in, V_subβ©
    use SymmetrizeRel V, symmetrize_mem_uniformity V_in, symmetric_symmetrize_rel V
    exact subset.trans (ball_mono (symmetrize_rel_subset_self V) x) V_sub
    
  Β· rintro β¨V, V_in, V_symm, V_subβ©
    exact β¨V, V_in, V_subβ©
    

theorem UniformSpace.has_basis_nhds (x : Ξ±) :
    HasBasis (π x) (fun s : Set (Ξ± Γ Ξ±) => s β π€ Ξ± β§ SymmetricRel s) fun s => Ball x s :=
  β¨fun t => by
    simp [β UniformSpace.mem_nhds_iff_symm, β and_assoc]β©

open UniformSpace

theorem UniformSpace.mem_closure_iff_symm_ball {s : Set Ξ±} {x} :
    x β Closure s β β {V}, V β π€ Ξ± β SymmetricRel V β (s β© Ball x V).Nonempty := by
  simp [β mem_closure_iff_nhds_basis (has_basis_nhds x), β Set.Nonempty]

theorem UniformSpace.mem_closure_iff_ball {s : Set Ξ±} {x} : x β Closure s β β {V}, V β π€ Ξ± β (Ball x V β© s).Nonempty :=
  by
  simp [β mem_closure_iff_nhds_basis' (nhds_basis_uniformity' (π€ Ξ±).basis_sets)]

theorem UniformSpace.has_basis_nhds_prod (x y : Ξ±) :
    (HasBasis (π (x, y)) fun s => s β π€ Ξ± β§ SymmetricRel s) fun s => Ball x s ΓΛ’ Ball y s := by
  rw [nhds_prod_eq]
  apply (has_basis_nhds x).prod' (has_basis_nhds y)
  rintro U V β¨U_in, U_symmβ© β¨V_in, V_symmβ©
  exact
    β¨U β© V, β¨(π€ Ξ±).inter_sets U_in V_in, symmetric_rel_inter U_symm V_symmβ©, ball_inter_left x U V,
      ball_inter_right y U Vβ©

theorem nhds_eq_uniformity {x : Ξ±} : π x = (π€ Ξ±).lift' (Ball x) :=
  (nhds_basis_uniformity' (π€ Ξ±).basis_sets).eq_binfi

theorem nhds_eq_uniformity' {x : Ξ±} : π x = (π€ Ξ±).lift' fun s => { y | (y, x) β s } :=
  (nhds_basis_uniformity (π€ Ξ±).basis_sets).eq_binfi

theorem mem_nhds_left (x : Ξ±) {s : Set (Ξ± Γ Ξ±)} (h : s β π€ Ξ±) : { y : Ξ± | (x, y) β s } β π x :=
  ball_mem_nhds x h

theorem mem_nhds_right (y : Ξ±) {s : Set (Ξ± Γ Ξ±)} (h : s β π€ Ξ±) : { x : Ξ± | (x, y) β s } β π y :=
  mem_nhds_left _ (symm_le_uniformity h)

theorem tendsto_right_nhds_uniformity {a : Ξ±} : Tendsto (fun a' => (a', a)) (π a) (π€ Ξ±) := fun s => mem_nhds_right a

theorem tendsto_left_nhds_uniformity {a : Ξ±} : Tendsto (fun a' => (a, a')) (π a) (π€ Ξ±) := fun s => mem_nhds_left a

theorem lift_nhds_left {x : Ξ±} {g : Set Ξ± β Filter Ξ²} (hg : Monotone g) :
    (π x).lift g = (π€ Ξ±).lift fun s : Set (Ξ± Γ Ξ±) => g { y | (x, y) β s } :=
  Eq.trans
    (by
      rw [nhds_eq_uniformity]
      exact Filter.lift_assoc <| monotone_principal.comp <| monotone_preimage.comp monotone_preimage)
    (congr_arg _ <| funext fun s => Filter.lift_principal hg)

theorem lift_nhds_right {x : Ξ±} {g : Set Ξ± β Filter Ξ²} (hg : Monotone g) :
    (π x).lift g = (π€ Ξ±).lift fun s : Set (Ξ± Γ Ξ±) => g { y | (y, x) β s } :=
  calc
    (π x).lift g = (π€ Ξ±).lift fun s : Set (Ξ± Γ Ξ±) => g { y | (x, y) β s } := lift_nhds_left hg
    _ = (@Prod.swap Ξ± Ξ± <$> π€ Ξ±).lift fun s : Set (Ξ± Γ Ξ±) => g { y | (x, y) β s } := by
      rw [β uniformity_eq_symm]
    _ = (π€ Ξ±).lift fun s : Set (Ξ± Γ Ξ±) => g { y | (x, y) β Image Prod.swap s } :=
      map_lift_eq2 <| hg.comp monotone_preimage
    _ = _ := by
      simp [β image_swap_eq_preimage_swap]
    

theorem nhds_nhds_eq_uniformity_uniformity_prod {a b : Ξ±} :
    π a ΓαΆ  π b =
      (π€ Ξ±).lift fun s : Set (Ξ± Γ Ξ±) =>
        (π€ Ξ±).lift' fun t : Set (Ξ± Γ Ξ±) => { y : Ξ± | (y, a) β s } ΓΛ’ { y : Ξ± | (b, y) β t } :=
  by
  rw [nhds_eq_uniformity', nhds_eq_uniformity, prod_lift'_lift']
  Β· rfl
    
  Β· exact monotone_preimage
    
  Β· exact monotone_preimage
    

theorem nhds_eq_uniformity_prod {a b : Ξ±} :
    π (a, b) = (π€ Ξ±).lift' fun s : Set (Ξ± Γ Ξ±) => { y : Ξ± | (y, a) β s } ΓΛ’ { y : Ξ± | (b, y) β s } := by
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift']
  Β· intro s
    exact monotone_const.set_prod monotone_preimage
    
  Β· intro t
    exact monotone_preimage.set_prod monotone_const
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (t Β«expr β Β» cl_d)
theorem nhdset_of_mem_uniformity {d : Set (Ξ± Γ Ξ±)} (s : Set (Ξ± Γ Ξ±)) (hd : d β π€ Ξ±) :
    β t : Set (Ξ± Γ Ξ±), IsOpen t β§ s β t β§ t β { p | β x y, (p.1, x) β d β§ (x, y) β s β§ (y, p.2) β d } :=
  let cl_d := { p : Ξ± Γ Ξ± | β x y, (p.1, x) β d β§ (x, y) β s β§ (y, p.2) β d }
  have : β, β p β s, β, β (t : _)(_ : t β cl_d), IsOpen t β§ p β t := fun β¨x, yβ© hp =>
    mem_nhds_iff.mp <|
      show cl_d β π (x, y) by
        rw [nhds_eq_uniformity_prod, mem_lift'_sets]
        exact β¨d, hd, fun β¨a, bβ© β¨ha, hbβ© => β¨x, y, ha, hp, hbβ©β©
        exact monotone_preimage.set_prod monotone_preimage
  have : β t : β (p : Ξ± Γ Ξ±) (h : p β s), Set (Ξ± Γ Ξ±), β p, β h : p β s, t p h β cl_d β§ IsOpen (t p h) β§ p β t p h := by
    simp [β Classical.skolem] at this <;> simp <;> assumption
  match this with
  | β¨t, htβ© =>
    β¨(β p : Ξ± Γ Ξ±, β h : p β s, t p h : Set (Ξ± Γ Ξ±)),
      is_open_Union fun p : Ξ± Γ Ξ± => is_open_Union fun hp => (ht p hp).right.left, fun β¨a, bβ© hp => by
      simp <;> exact β¨a, b, hp, (ht (a, b) hp).right.rightβ©,
      Union_subset fun p => Union_subset fun hp => (ht p hp).leftβ©

/-- Entourages are neighborhoods of the diagonal. -/
theorem nhds_le_uniformity (x : Ξ±) : π (x, x) β€ π€ Ξ± := by
  intro V V_in
  rcases comp_symm_mem_uniformity_sets V_in with β¨w, w_in, w_symm, w_subβ©
  have : ball x w ΓΛ’ ball x w β π (x, x) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in)
  apply mem_of_superset this
  rintro β¨u, vβ© β¨u_in, v_inβ©
  exact w_sub (mem_comp_of_mem_ball w_symm u_in v_in)

/-- Entourages are neighborhoods of the diagonal. -/
theorem supr_nhds_le_uniformity : (β¨ x : Ξ±, π (x, x)) β€ π€ Ξ± :=
  supr_le nhds_le_uniformity

/-!
### Closure and interior in uniform spaces
-/


theorem closure_eq_uniformity (s : Set <| Ξ± Γ Ξ±) : Closure s = β V β { V | V β π€ Ξ± β§ SymmetricRel V }, V β s β V := by
  ext β¨x, yβ©
  simp_rw [mem_closure_iff_nhds_basis (UniformSpace.has_basis_nhds_prod x y), mem_Inter, mem_set_of_eq]
  refine' forallβ_congrβ fun V => _
  rintro β¨V_in, V_symmβ©
  simp_rw [mem_comp_comp V_symm, inter_comm, exists_prop]
  exact Iff.rfl

theorem uniformity_has_basis_closed : HasBasis (π€ Ξ±) (fun V : Set (Ξ± Γ Ξ±) => V β π€ Ξ± β§ IsClosed V) id := by
  refine' Filter.has_basis_self.2 fun t h => _
  rcases comp_comp_symm_mem_uniformity_sets h with β¨w, w_in, w_symm, rβ©
  refine' β¨Closure w, mem_of_superset w_in subset_closure, is_closed_closure, _β©
  refine' subset.trans _ r
  rw [closure_eq_uniformity]
  apply Inter_subset_of_subset
  apply Inter_subset
  exact β¨w_in, w_symmβ©

/-- Closed entourages form a basis of the uniformity filter. -/
theorem uniformity_has_basis_closure : HasBasis (π€ Ξ±) (fun V : Set (Ξ± Γ Ξ±) => V β π€ Ξ±) Closure :=
  β¨by
    intro t
    rw [uniformity_has_basis_closed.mem_iff]
    constructor
    Β· rintro β¨r, β¨r_in, r_closedβ©, r_subβ©
      use r, r_in
      convert r_sub
      rw [r_closed.closure_eq]
      rfl
      
    Β· rintro β¨r, r_in, r_subβ©
      exact β¨Closure r, β¨mem_of_superset r_in subset_closure, is_closed_closureβ©, r_subβ©
      β©

theorem closure_eq_inter_uniformity {t : Set (Ξ± Γ Ξ±)} : Closure t = β d β π€ Ξ±, d β (t β d) :=
  Set.ext fun β¨a, bβ© =>
    calc
      (a, b) β Closure t β π (a, b)βπ t β  β₯ := mem_closure_iff_nhds_ne_bot
      _ β
          ((@Prod.swap Ξ± Ξ± <$> π€ Ξ±).lift' fun s : Set (Ξ± Γ Ξ±) => { x : Ξ± | (x, a) β s } ΓΛ’ { y : Ξ± | (b, y) β s })βπ t β 
            β₯ :=
        by
        rw [β uniformity_eq_symm, nhds_eq_uniformity_prod]
      _ β
          ((map (@Prod.swap Ξ± Ξ±) (π€ Ξ±)).lift' fun s : Set (Ξ± Γ Ξ±) =>
                { x : Ξ± | (x, a) β s } ΓΛ’ { y : Ξ± | (b, y) β s })βπ t β 
            β₯ :=
        by
        rfl
      _ β ((π€ Ξ±).lift' fun s : Set (Ξ± Γ Ξ±) => { y : Ξ± | (a, y) β s } ΓΛ’ { x : Ξ± | (x, b) β s })βπ t β  β₯ := by
        rw [map_lift'_eq2]
        simp [β image_swap_eq_preimage_swap, β Function.comp]
        exact monotone_preimage.set_prod monotone_preimage
      _ β β, β s β π€ Ξ±, β, ({ y : Ξ± | (a, y) β s } ΓΛ’ { x : Ξ± | (x, b) β s } β© t).Nonempty := by
        rw [lift'_inf_principal_eq, β ne_bot_iff, lift'_ne_bot_iff]
        exact (monotone_preimage.set_prod monotone_preimage).inter monotone_const
      _ β β, β s β π€ Ξ±, β, (a, b) β s β (t β s) :=
        forallβ_congrβ fun s hs =>
          β¨fun β¨β¨x, yβ©, β¨β¨hx, hyβ©, hxytβ©β© => β¨x, hx, y, hxyt, hyβ©, fun β¨x, hx, y, hxyt, hyβ© =>
            β¨β¨x, yβ©, β¨β¨hx, hyβ©, hxytβ©β©β©
      _ β _ := by
        simp
      

theorem uniformity_eq_uniformity_closure : π€ Ξ± = (π€ Ξ±).lift' Closure :=
  le_antisymmβ
    (le_infi fun s =>
      le_infi fun hs => by
        simp <;> filter_upwards [hs] using subset_closure)
    (calc
      (π€ Ξ±).lift' Closure β€ (π€ Ξ±).lift' fun d => d β (d β d) :=
        lift'_mono'
          (by
            intro s hs <;> rw [closure_eq_inter_uniformity] <;> exact bInter_subset_of_mem hs)
      _ β€ π€ Ξ± := comp_le_uniformity3
      )

theorem uniformity_eq_uniformity_interior : π€ Ξ± = (π€ Ξ±).lift' Interior :=
  le_antisymmβ
    (le_infi fun d =>
      le_infi fun hd => by
        let β¨s, hs, hs_compβ© :=
          (mem_lift'_sets <| monotone_comp_rel monotone_id <| monotone_comp_rel monotone_id monotone_id).mp
            (comp_le_uniformity3 hd)
        let β¨t, ht, hst, ht_compβ© := nhdset_of_mem_uniformity s hs
        have : s β Interior d :=
          calc
            s β t := hst
            _ β Interior d :=
              (subset_interior_iff_subset_of_open ht).mpr fun x (hx : x β t) =>
                let β¨x, y, hβ, hβ, hββ© := ht_comp hx
                hs_comp β¨x, hβ, y, hβ, hββ©
            
        have : Interior d β π€ Ξ± := by
          filter_upwards [hs] using this
        simp [β this])
    fun s hs => ((π€ Ξ±).lift' Interior).sets_of_superset (mem_lift' hs) interior_subset

theorem interior_mem_uniformity {s : Set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) : Interior s β π€ Ξ± := by
  rw [uniformity_eq_uniformity_interior] <;> exact mem_lift' hs

theorem mem_uniformity_is_closed {s : Set (Ξ± Γ Ξ±)} (h : s β π€ Ξ±) : β t β π€ Ξ±, IsClosed t β§ t β s :=
  let β¨t, β¨ht_mem, htcβ©, htsβ© := uniformity_has_basis_closed.mem_iff.1 h
  β¨t, ht_mem, htc, htsβ©

theorem is_open_iff_open_ball_subset {s : Set Ξ±} : IsOpen s β β, β x β s, β, β V β π€ Ξ±, IsOpen V β§ Ball x V β s := by
  rw [is_open_iff_ball_subset]
  constructor <;> intro h x hx
  Β· obtain β¨V, hV, hV'β© := h x hx
    exact β¨Interior V, interior_mem_uniformity hV, is_open_interior, (ball_mono interior_subset x).trans hV'β©
    
  Β· obtain β¨V, hV, -, hV'β© := h x hx
    exact β¨V, hV, hV'β©
    

/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
theorem Dense.bUnion_uniformity_ball {s : Set Ξ±} {U : Set (Ξ± Γ Ξ±)} (hs : Dense s) (hU : U β π€ Ξ±) :
    (β x β s, Ball x U) = univ := by
  refine' Unionβ_eq_univ_iff.2 fun y => _
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with β¨x, hxs, hxy : (x, y) β Uβ©
  exact β¨x, hxs, hxyβ©

/-!
### Uniformity bases
-/


/-- Open elements of `π€ Ξ±` form a basis of `π€ Ξ±`. -/
theorem uniformity_has_basis_open : HasBasis (π€ Ξ±) (fun V : Set (Ξ± Γ Ξ±) => V β π€ Ξ± β§ IsOpen V) id :=
  has_basis_self.2 fun s hs => β¨Interior s, interior_mem_uniformity hs, is_open_interior, interior_subsetβ©

theorem Filter.HasBasis.mem_uniformity_iff {p : Ξ² β Prop} {s : Ξ² β Set (Ξ± Γ Ξ±)} (h : (π€ Ξ±).HasBasis p s)
    {t : Set (Ξ± Γ Ξ±)} : t β π€ Ξ± β β (i : _)(hi : p i), β a b, (a, b) β s i β (a, b) β t :=
  h.mem_iff.trans <| by
    simp only [β Prod.forall, β subset_def]

/-- Symmetric entourages form a basis of `π€ Ξ±` -/
theorem UniformSpace.has_basis_symmetric : (π€ Ξ±).HasBasis (fun s : Set (Ξ± Γ Ξ±) => s β π€ Ξ± β§ SymmetricRel s) id :=
  has_basis_self.2 fun t t_in =>
    β¨SymmetrizeRel t, symmetrize_mem_uniformity t_in, symmetric_symmetrize_rel t, symmetrize_rel_subset_self tβ©

/-- Open elements `s : set (Ξ± Γ Ξ±)` of `π€ Ξ±` such that `(x, y) β s β (y, x) β s` form a basis
of `π€ Ξ±`. -/
theorem uniformity_has_basis_open_symmetric :
    HasBasis (π€ Ξ±) (fun V : Set (Ξ± Γ Ξ±) => V β π€ Ξ± β§ IsOpen V β§ SymmetricRel V) id := by
  simp only [and_assoc]
  refine' uniformity_has_basis_open.restrict fun s hs => β¨SymmetrizeRel s, _β©
  exact
    β¨β¨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.Preimage continuous_swap)β©, symmetric_symmetrize_rel s,
      symmetrize_rel_subset_self sβ©

theorem comp_open_symm_mem_uniformity_sets {s : Set (Ξ± Γ Ξ±)} (hs : s β π€ Ξ±) :
    β t β π€ Ξ±, IsOpen t β§ SymmetricRel t β§ t β t β s := by
  obtain β¨t, htβ, htββ© := comp_mem_uniformity_sets hs
  obtain β¨u, β¨huβ, huβ, huββ©, huβ : u β tβ© := uniformity_has_basis_open_symmetric.mem_iff.mp htβ
  exact β¨u, huβ, huβ, huβ, (comp_rel_mono huβ huβ).trans htββ©

section

variable (Ξ±)

theorem UniformSpace.has_seq_basis [is_countably_generated <| π€ Ξ±] :
    β V : β β Set (Ξ± Γ Ξ±), HasAntitoneBasis (π€ Ξ±) V β§ β n, SymmetricRel (V n) :=
  let β¨U, hsym, hbasisβ© := UniformSpace.has_basis_symmetric.exists_antitone_subbasis
  β¨U, hbasis, fun n => (hsym n).2β©

end

theorem Filter.HasBasis.bInter_bUnion_ball {p : ΞΉ β Prop} {U : ΞΉ β Set (Ξ± Γ Ξ±)} (h : HasBasis (π€ Ξ±) p U) (s : Set Ξ±) :
    (β (i) (hi : p i), β x β s, Ball x (U i)) = Closure s := by
  ext x
  simp [β mem_closure_iff_nhds_basis (nhds_basis_uniformity h), β ball]

/-! ### Uniform continuity -/


/-- A function `f : Ξ± β Ξ²` is *uniformly continuous* if `(f x, f y)` tends to the diagonal
as `(x, y)` tends to the diagonal. In other words, if `x` is sufficiently close to `y`, then
`f x` is close to `f y` no matter where `x` and `y` are located in `Ξ±`. -/
def UniformContinuous [UniformSpace Ξ²] (f : Ξ± β Ξ²) :=
  Tendsto (fun x : Ξ± Γ Ξ± => (f x.1, f x.2)) (π€ Ξ±) (π€ Ξ²)

/-- A function `f : Ξ± β Ξ²` is *uniformly continuous* on `s : set Ξ±` if `(f x, f y)` tends to
the diagonal as `(x, y)` tends to the diagonal while remaining in `s ΓΛ’ s`.
In other words, if `x` is sufficiently close to `y`, then `f x` is close to
`f y` no matter where `x` and `y` are located in `s`.-/
def UniformContinuousOn [UniformSpace Ξ²] (f : Ξ± β Ξ²) (s : Set Ξ±) : Prop :=
  Tendsto (fun x : Ξ± Γ Ξ± => (f x.1, f x.2)) (π€ Ξ±βprincipal (s ΓΛ’ s)) (π€ Ξ²)

theorem uniform_continuous_def [UniformSpace Ξ²] {f : Ξ± β Ξ²} :
    UniformContinuous f β β, β r β π€ Ξ², β, { x : Ξ± Γ Ξ± | (f x.1, f x.2) β r } β π€ Ξ± :=
  Iff.rfl

theorem uniform_continuous_iff_eventually [UniformSpace Ξ²] {f : Ξ± β Ξ²} :
    UniformContinuous f β β, β r β π€ Ξ², β, βαΆ  x : Ξ± Γ Ξ± in π€ Ξ±, (f x.1, f x.2) β r :=
  Iff.rfl

theorem uniform_continuous_on_univ [UniformSpace Ξ²] {f : Ξ± β Ξ²} : UniformContinuousOn f Univ β UniformContinuous f := by
  rw [UniformContinuousOn, UniformContinuous, univ_prod_univ, principal_univ, inf_top_eq]

theorem uniform_continuous_of_const [UniformSpace Ξ²] {c : Ξ± β Ξ²} (h : β a b, c a = c b) : UniformContinuous c :=
  have : (fun x : Ξ± Γ Ξ± => (c x.fst, c x.snd)) β»ΒΉ' IdRel = univ := eq_univ_iff_forall.2 fun β¨a, bβ© => h a b
  le_transβ
    (map_le_iff_le_comap.2 <| by
      simp [β comap_principal, β this, β univ_mem])
    refl_le_uniformity

theorem uniform_continuous_id : UniformContinuous (@id Ξ±) := by
  simp [β UniformContinuous] <;> exact tendsto_id

theorem uniform_continuous_const [UniformSpace Ξ²] {b : Ξ²} : UniformContinuous fun a : Ξ± => b :=
  uniform_continuous_of_const fun _ _ => rfl

theorem UniformContinuous.comp [UniformSpace Ξ²] [UniformSpace Ξ³] {g : Ξ² β Ξ³} {f : Ξ± β Ξ²} (hg : UniformContinuous g)
    (hf : UniformContinuous f) : UniformContinuous (g β f) :=
  hg.comp hf

theorem Filter.HasBasis.uniform_continuous_iff [UniformSpace Ξ²] {p : Ξ³ β Prop} {s : Ξ³ β Set (Ξ± Γ Ξ±)}
    (ha : (π€ Ξ±).HasBasis p s) {q : Ξ΄ β Prop} {t : Ξ΄ β Set (Ξ² Γ Ξ²)} (hb : (π€ Ξ²).HasBasis q t) {f : Ξ± β Ξ²} :
    UniformContinuous f β β (i) (hi : q i), β (j : _)(hj : p j), β x y, (x, y) β s j β (f x, f y) β t i :=
  (ha.tendsto_iff hb).trans <| by
    simp only [β Prod.forall]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x y Β«expr β Β» S)
theorem Filter.HasBasis.uniform_continuous_on_iff [UniformSpace Ξ²] {p : Ξ³ β Prop} {s : Ξ³ β Set (Ξ± Γ Ξ±)}
    (ha : (π€ Ξ±).HasBasis p s) {q : Ξ΄ β Prop} {t : Ξ΄ β Set (Ξ² Γ Ξ²)} (hb : (π€ Ξ²).HasBasis q t) {f : Ξ± β Ξ²} {S : Set Ξ±} :
    UniformContinuousOn f S β
      β (i) (hi : q i), β (j : _)(hj : p j), β (x y) (_ : x β S) (_ : y β S), (x, y) β s j β (f x, f y) β t i :=
  ((ha.inf_principal (S ΓΛ’ S)).tendsto_iff hb).trans <| by
    simp [β Prod.forall, β Set.inter_comm (s _), β ball_mem_comm]

end UniformSpace

open uniformity

section Constructions

instance : PartialOrderβ (UniformSpace Ξ±) where
  le := fun t s => t.uniformity β€ s.uniformity
  le_antisymm := fun t s hβ hβ => uniform_space_eq <| le_antisymmβ hβ hβ
  le_refl := fun t => le_rfl
  le_trans := fun a b c hβ hβ => le_transβ hβ hβ

instance : HasInfβ (UniformSpace Ξ±) :=
  β¨fun s =>
    UniformSpace.ofCore
      { uniformity := β¨ u β s, @uniformity Ξ± u, refl := le_infi fun u => le_infi fun hu => u.refl,
        symm := le_infi fun u => le_infi fun hu => le_transβ (map_mono <| infi_le_of_le _ <| infi_le _ hu) u.symm,
        comp :=
          le_infi fun u =>
            le_infi fun hu => le_transβ (lift'_mono (infi_le_of_le _ <| infi_le _ hu) <| le_rfl) u.comp }β©

private theorem Inf_le {tt : Set (UniformSpace Ξ±)} {t : UniformSpace Ξ±} (h : t β tt) : inf tt β€ t :=
  show (β¨ u β tt, @uniformity Ξ± u) β€ t.uniformity from infi_le_of_le t <| infi_le _ h

private theorem le_Inf {tt : Set (UniformSpace Ξ±)} {t : UniformSpace Ξ±} (h : β, β t' β tt, β, t β€ t') : t β€ inf tt :=
  show t.uniformity β€ β¨ u β tt, @uniformity Ξ± u from le_infi fun t' => le_infi fun ht' => h t' ht'

instance : HasTop (UniformSpace Ξ±) :=
  β¨UniformSpace.ofCore { uniformity := β€, refl := le_top, symm := le_top, comp := le_top }β©

instance : HasBot (UniformSpace Ξ±) :=
  β¨{ toTopologicalSpace := β₯, uniformity := π IdRel, refl := le_rfl,
      symm := by
        simp [β tendsto] <;> apply subset.refl,
      comp := by
        rw [lift'_principal]
        Β· simp
          
        exact monotone_comp_rel monotone_id monotone_id,
      is_open_uniformity := fun s => by
        simp (config := { contextual := true })[β is_open_fold, β subset_def, β IdRel] }β©

instance : HasInf (UniformSpace Ξ±) :=
  β¨fun uβ uβ =>
    @UniformSpace.replaceTopology _ (uβ.toTopologicalSpaceβuβ.toTopologicalSpace)
        (UniformSpace.ofCore
          { uniformity := uβ.uniformityβuβ.uniformity, refl := le_inf uβ.refl uβ.refl, symm := uβ.symm.inf uβ.symm,
            comp := (lift'_inf_le _ _ _).trans <| inf_le_inf uβ.comp uβ.comp }) <|
      eq_of_nhds_eq_nhds fun a => by
        simpa only [β nhds_inf, β nhds_eq_comap_uniformity] using comap_inf.symmβ©

instance : CompleteLattice (UniformSpace Ξ±) :=
  { UniformSpace.partialOrder with sup := fun a b => inf { x | a β€ x β§ b β€ x },
    le_sup_left := fun a b => le_Inf fun _ β¨h, _β© => h, le_sup_right := fun a b => le_Inf fun _ β¨_, hβ© => h,
    sup_le := fun a b c hβ hβ => Inf_le β¨hβ, hββ©, inf := (Β·βΒ·),
    le_inf := fun a b c hβ hβ => show a.uniformity β€ _ from le_inf hβ hβ,
    inf_le_left := fun a b => show _ β€ a.uniformity from inf_le_left,
    inf_le_right := fun a b => show _ β€ b.uniformity from inf_le_right, top := β€,
    le_top := fun a => show a.uniformity β€ β€ from le_top, bot := β₯, bot_le := fun u => u.refl,
    sup := fun tt => inf { t | β, β t' β tt, β, t' β€ t }, le_Sup := fun s u h => le_Inf fun u' h' => h' u h,
    Sup_le := fun s u h => Inf_le h, inf := inf, le_Inf := fun s a hs => le_Inf hs, Inf_le := fun s a ha => Inf_le ha }

theorem infi_uniformity {ΞΉ : Sort _} {u : ΞΉ β UniformSpace Ξ±} : (infi u).uniformity = β¨ i, (u i).uniformity :=
  show (β¨ (a) (h : β i : ΞΉ, u i = a), a.uniformity) = _ from
    le_antisymmβ (le_infi fun i => infi_le_of_le (u i) <| infi_le _ β¨i, rflβ©)
      (le_infi fun a => le_infi fun β¨i, (ha : u i = a)β© => ha βΈ infi_le _ _)

theorem infi_uniformity' {ΞΉ : Sort _} {u : ΞΉ β UniformSpace Ξ±} : @uniformity Ξ± (infi u) = β¨ i, @uniformity Ξ± (u i) :=
  infi_uniformity

theorem inf_uniformity {u v : UniformSpace Ξ±} : (uβv).uniformity = u.uniformityβv.uniformity :=
  rfl

theorem inf_uniformity' {u v : UniformSpace Ξ±} : @uniformity Ξ± (uβv) = @uniformity Ξ± uβ@uniformity Ξ± v :=
  rfl

instance inhabitedUniformSpace : Inhabited (UniformSpace Ξ±) :=
  β¨β₯β©

instance inhabitedUniformSpaceCore : Inhabited (UniformSpace.Core Ξ±) :=
  β¨@UniformSpace.toCore _ defaultβ©

/-- Given `f : Ξ± β Ξ²` and a uniformity `u` on `Ξ²`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `Ξ± Γ Ξ± β Ξ² Γ Ξ²`. -/
def UniformSpace.comap (f : Ξ± β Ξ²) (u : UniformSpace Ξ²) : UniformSpace Ξ± where
  uniformity := u.uniformity.comap fun p : Ξ± Γ Ξ± => (f p.1, f p.2)
  toTopologicalSpace := u.toTopologicalSpace.induced f
  refl :=
    le_transβ
      (by
        simp <;> exact fun β¨a, bβ© (h : a = b) => h βΈ rfl)
      (comap_mono u.refl)
  symm := by
    simp [β tendsto_comap_iff, β Prod.swap, β (Β· β Β·)] <;> exact tendsto_swap_uniformity.comp tendsto_comap
  comp :=
    le_transβ
      (by
        rw [comap_lift'_eq, comap_lift'_eq2]
        exact lift'_mono' fun s hs β¨aβ, aββ© β¨x, hβ, hββ© => β¨f x, hβ, hββ©
        exact monotone_comp_rel monotone_id monotone_id)
      (comap_mono u.comp)
  is_open_uniformity := fun s => by
    change @IsOpen Ξ± (u.to_topological_space.induced f) s β _
    simp [β is_open_iff_nhds, β nhds_induced, β mem_nhds_uniformity_iff_right, β Filter.comap, β and_comm]
    refine' ball_congr fun x hx => β¨_, _β©
    Β· rintro β¨t, hts, htβ©
      refine' β¨_, ht, _β©
      rintro β¨xβ, xββ© h rfl
      exact hts (h rfl)
      
    Β· rintro β¨t, ht, htsβ©
      exact
        β¨{ y | (f x, y) β t }, fun y hy => @hts (x, y) hy rfl, mem_nhds_uniformity_iff_right.1 <| mem_nhds_left _ htβ©
      

theorem uniformity_comap [UniformSpace Ξ±] [UniformSpace Ξ²] {f : Ξ± β Ξ²}
    (h : βΉUniformSpace Ξ±βΊ = UniformSpace.comap f βΉUniformSpace Ξ²βΊ) : π€ Ξ± = comap (Prod.map f f) (π€ Ξ²) := by
  rw [h]
  rfl

theorem uniform_space_comap_id {Ξ± : Type _} : UniformSpace.comap (id : Ξ± β Ξ±) = id := by
  ext u <;> dsimp' only [β UniformSpace.comap, β id] <;> rw [Prod.id_prodβ, Filter.comap_id]

theorem UniformSpace.comap_comap {Ξ± Ξ² Ξ³} [uΞ³ : UniformSpace Ξ³] {f : Ξ± β Ξ²} {g : Ξ² β Ξ³} :
    UniformSpace.comap (g β f) uΞ³ = UniformSpace.comap f (UniformSpace.comap g uΞ³) := by
  ext <;> dsimp' only [β UniformSpace.comap] <;> rw [Filter.comap_comap]

theorem UniformSpace.comap_inf {Ξ± Ξ³} {uβ uβ : UniformSpace Ξ³} {f : Ξ± β Ξ³} : (uββuβ).comap f = uβ.comap fβuβ.comap f :=
  uniform_space_eq comap_inf

theorem UniformSpace.comap_infi {ΞΉ Ξ± Ξ³} {u : ΞΉ β UniformSpace Ξ³} {f : Ξ± β Ξ³} :
    (β¨ i, u i).comap f = β¨ i, (u i).comap f := by
  ext : 1
  change π€ _ = π€ _
  simp [β uniformity_comap rfl, β infi_uniformity']

theorem UniformSpace.comap_mono {Ξ± Ξ³} {f : Ξ± β Ξ³} : Monotone fun u : UniformSpace Ξ³ => u.comap f := by
  intro uβ uβ hu
  change π€ _ β€ π€ _
  rw [uniformity_comap rfl]
  exact comap_mono hu

theorem uniform_continuous_iff {Ξ± Ξ²} {uΞ± : UniformSpace Ξ±} {uΞ² : UniformSpace Ξ²} {f : Ξ± β Ξ²} :
    UniformContinuous f β uΞ± β€ uΞ².comap f :=
  Filter.map_le_iff_le_comap

theorem le_iff_uniform_continuous_id {u v : UniformSpace Ξ±} : u β€ v β @UniformContinuous _ _ u v id := by
  rw [uniform_continuous_iff, uniform_space_comap_id, id]

theorem uniform_continuous_comap {f : Ξ± β Ξ²} [u : UniformSpace Ξ²] :
    @UniformContinuous Ξ± Ξ² (UniformSpace.comap f u) u f :=
  tendsto_comap

theorem to_topological_space_comap {f : Ξ± β Ξ²} {u : UniformSpace Ξ²} :
    @UniformSpace.toTopologicalSpace _ (UniformSpace.comap f u) =
      TopologicalSpace.induced f (@UniformSpace.toTopologicalSpace Ξ² u) :=
  rfl

theorem uniform_continuous_comap' {f : Ξ³ β Ξ²} {g : Ξ± β Ξ³} [v : UniformSpace Ξ²] [u : UniformSpace Ξ±]
    (h : UniformContinuous (f β g)) : @UniformContinuous Ξ± Ξ³ u (UniformSpace.comap f v) g :=
  tendsto_comap_iff.2 h

theorem to_nhds_mono {uβ uβ : UniformSpace Ξ±} (h : uβ β€ uβ) (a : Ξ±) :
    @nhds _ (@UniformSpace.toTopologicalSpace _ uβ) a β€ @nhds _ (@UniformSpace.toTopologicalSpace _ uβ) a := by
  rw [@nhds_eq_uniformity Ξ± uβ a, @nhds_eq_uniformity Ξ± uβ a] <;> exact lift'_mono h le_rfl

theorem to_topological_space_mono {uβ uβ : UniformSpace Ξ±} (h : uβ β€ uβ) :
    @UniformSpace.toTopologicalSpace _ uβ β€ @UniformSpace.toTopologicalSpace _ uβ :=
  le_of_nhds_le_nhds <| to_nhds_mono h

theorem UniformContinuous.continuous [UniformSpace Ξ±] [UniformSpace Ξ²] {f : Ξ± β Ξ²} (hf : UniformContinuous f) :
    Continuous f :=
  continuous_iff_le_induced.mpr <| to_topological_space_mono <| uniform_continuous_iff.1 hf

theorem to_topological_space_bot : @UniformSpace.toTopologicalSpace Ξ± β₯ = β₯ :=
  rfl

theorem to_topological_space_top : @UniformSpace.toTopologicalSpace Ξ± β€ = β€ :=
  top_unique fun s hs =>
    s.eq_empty_or_nonempty.elim (fun this : s = β => this.symm βΈ @is_open_empty _ β€) fun β¨x, hxβ© =>
      have : s = univ := top_unique fun y hy => hs x hx (x, y) rfl
      this.symm βΈ @is_open_univ _ β€

theorem to_topological_space_infi {ΞΉ : Sort _} {u : ΞΉ β UniformSpace Ξ±} :
    (infi u).toTopologicalSpace = β¨ i, (u i).toTopologicalSpace := by
  refine' eq_of_nhds_eq_nhds fun a => _
  rw [nhds_infi, nhds_eq_uniformity]
  change (infi u).uniformity.lift' (preimage <| Prod.mk a) = _
  rw [infi_uniformity, lift'_infi_of_map_univ _ preimage_univ]
  Β· simp only [β nhds_eq_uniformity]
    rfl
    
  Β· exact ball_inter _
    

theorem to_topological_space_Inf {s : Set (UniformSpace Ξ±)} :
    (inf s).toTopologicalSpace = β¨ i β s, @UniformSpace.toTopologicalSpace Ξ± i := by
  rw [Inf_eq_infi]
  simp only [to_topological_space_infi]

theorem to_topological_space_inf {u v : UniformSpace Ξ±} :
    (uβv).toTopologicalSpace = u.toTopologicalSpaceβv.toTopologicalSpace :=
  rfl

section UniformContinuousInfi

theorem uniform_continuous_inf_rng {f : Ξ± β Ξ²} {uβ : UniformSpace Ξ±} {uβ uβ : UniformSpace Ξ²}
    (hβ : @UniformContinuous uβ uβ f) (hβ : @UniformContinuous uβ uβ f) : @UniformContinuous uβ (uββuβ) f :=
  tendsto_inf.mpr β¨hβ, hββ©

theorem uniform_continuous_inf_dom_left {f : Ξ± β Ξ²} {uβ uβ : UniformSpace Ξ±} {uβ : UniformSpace Ξ²}
    (hf : @UniformContinuous uβ uβ f) : @UniformContinuous (uββuβ) uβ f :=
  tendsto_inf_left hf

theorem uniform_continuous_inf_dom_right {f : Ξ± β Ξ²} {uβ uβ : UniformSpace Ξ±} {uβ : UniformSpace Ξ²}
    (hf : @UniformContinuous uβ uβ f) : @UniformContinuous (uββuβ) uβ f :=
  tendsto_inf_right hf

theorem uniform_continuous_Inf_dom {f : Ξ± β Ξ²} {uβ : Set (UniformSpace Ξ±)} {uβ : UniformSpace Ξ²} {u : UniformSpace Ξ±}
    (hβ : u β uβ) (hf : @UniformContinuous u uβ f) : @UniformContinuous (inf uβ) uβ f := by
  rw [UniformContinuous, Inf_eq_infi', infi_uniformity']
  exact tendsto_infi' β¨u, hββ© hf

theorem uniform_continuous_Inf_rng {f : Ξ± β Ξ²} {uβ : UniformSpace Ξ±} {uβ : Set (UniformSpace Ξ²)}
    (h : β, β u β uβ, β, @UniformContinuous uβ u f) : @UniformContinuous uβ (inf uβ) f := by
  rw [UniformContinuous, Inf_eq_infi', infi_uniformity']
  exact tendsto_infi.mpr fun β¨u, huβ© => h u hu

theorem uniform_continuous_infi_dom {f : Ξ± β Ξ²} {uβ : ΞΉ β UniformSpace Ξ±} {uβ : UniformSpace Ξ²} {i : ΞΉ}
    (hf : @UniformContinuous (uβ i) uβ f) : @UniformContinuous (infi uβ) uβ f := by
  rw [UniformContinuous, infi_uniformity']
  exact tendsto_infi' i hf

theorem uniform_continuous_infi_rng {f : Ξ± β Ξ²} {uβ : UniformSpace Ξ±} {uβ : ΞΉ β UniformSpace Ξ²}
    (h : β i, @UniformContinuous uβ (uβ i) f) : @UniformContinuous uβ (infi uβ) f := by
  rwa [UniformContinuous, infi_uniformity', tendsto_infi]

end UniformContinuousInfi

/-- A uniform space with the discrete uniformity has the discrete topology. -/
theorem discrete_topology_of_discrete_uniformity [hΞ± : UniformSpace Ξ±] (h : uniformity Ξ± = π IdRel) :
    DiscreteTopology Ξ± :=
  β¨(uniform_space_eq h.symm : β₯ = hΞ±) βΈ rflβ©

instance : UniformSpace Empty :=
  β₯

instance : UniformSpace PUnit :=
  β₯

instance : UniformSpace Bool :=
  β₯

instance : UniformSpace β :=
  β₯

instance : UniformSpace β€ :=
  β₯

instance {p : Ξ± β Prop} [t : UniformSpace Ξ±] : UniformSpace (Subtype p) :=
  UniformSpace.comap Subtype.val t

theorem uniformity_subtype {p : Ξ± β Prop} [t : UniformSpace Ξ±] :
    π€ (Subtype p) = comap (fun q : Subtype p Γ Subtype p => (q.1.1, q.2.1)) (π€ Ξ±) :=
  rfl

theorem uniform_continuous_subtype_val {p : Ξ± β Prop} [UniformSpace Ξ±] :
    UniformContinuous (Subtype.val : { a : Ξ± // p a } β Ξ±) :=
  uniform_continuous_comap

theorem uniform_continuous_subtype_coe {p : Ξ± β Prop} [UniformSpace Ξ±] :
    UniformContinuous (coe : { a : Ξ± // p a } β Ξ±) :=
  uniform_continuous_subtype_val

theorem uniform_continuous_subtype_mk {p : Ξ± β Prop} [UniformSpace Ξ±] [UniformSpace Ξ²] {f : Ξ² β Ξ±}
    (hf : UniformContinuous f) (h : β x, p (f x)) : UniformContinuous (fun x => β¨f x, h xβ© : Ξ² β Subtype p) :=
  uniform_continuous_comap' hf

theorem uniform_continuous_on_iff_restrict [UniformSpace Ξ±] [UniformSpace Ξ²] {f : Ξ± β Ξ²} {s : Set Ξ±} :
    UniformContinuousOn f s β UniformContinuous (s.restrict f) := by
  unfold UniformContinuousOn Set.restrict UniformContinuous tendsto
  rw
    [show (fun x : s Γ s => (f x.1, f x.2)) = Prod.map f f β coe by
      ext x <;> cases x <;> rfl,
    uniformity_comap rfl,
    show Prod.map Subtype.val Subtype.val = (coe : s Γ s β Ξ± Γ Ξ±) by
      ext x <;> cases x <;> rfl]
  conv in map _ (comap _ _) => rw [β Filter.map_map]
  rw [subtype_coe_map_comap_prod]
  rfl

theorem tendsto_of_uniform_continuous_subtype [UniformSpace Ξ±] [UniformSpace Ξ²] {f : Ξ± β Ξ²} {s : Set Ξ±} {a : Ξ±}
    (hf : UniformContinuous fun x : s => f x.val) (ha : s β π a) : Tendsto f (π a) (π (f a)) := by
  rw [(@map_nhds_subtype_coe_eq Ξ± _ s a (mem_of_mem_nhds ha) ha).symm] <;>
    exact tendsto_map' (continuous_iff_continuous_at.mp hf.continuous _)

theorem UniformContinuousOn.continuous_on [UniformSpace Ξ±] [UniformSpace Ξ²] {f : Ξ± β Ξ²} {s : Set Ξ±}
    (h : UniformContinuousOn f s) : ContinuousOn f s := by
  rw [uniform_continuous_on_iff_restrict] at h
  rw [continuous_on_iff_continuous_restrict]
  exact h.continuous

@[to_additive]
instance [UniformSpace Ξ±] : UniformSpace Ξ±α΅α΅α΅ :=
  UniformSpace.comap MulOpposite.unop βΉ_βΊ

@[to_additive]
theorem uniformity_mul_opposite [UniformSpace Ξ±] : π€ Ξ±α΅α΅α΅ = comap (fun q : Ξ±α΅α΅α΅ Γ Ξ±α΅α΅α΅ => (q.1.unop, q.2.unop)) (π€ Ξ±) :=
  rfl

@[simp, to_additive]
theorem comap_uniformity_mul_opposite [UniformSpace Ξ±] :
    comap (fun p : Ξ± Γ Ξ± => (MulOpposite.op p.1, MulOpposite.op p.2)) (π€ Ξ±α΅α΅α΅) = π€ Ξ± := by
  simpa [β uniformity_mul_opposite, β comap_comap, β (Β· β Β·)] using comap_id

namespace MulOpposite

@[to_additive]
theorem uniform_continuous_unop [UniformSpace Ξ±] : UniformContinuous (unop : Ξ±α΅α΅α΅ β Ξ±) :=
  uniform_continuous_comap

@[to_additive]
theorem uniform_continuous_op [UniformSpace Ξ±] : UniformContinuous (op : Ξ± β Ξ±α΅α΅α΅) :=
  uniform_continuous_comap' uniform_continuous_id

end MulOpposite

section Prod

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/
instance [uβ : UniformSpace Ξ±] [uβ : UniformSpace Ξ²] : UniformSpace (Ξ± Γ Ξ²) :=
  uβ.comap Prod.fstβuβ.comap Prod.snd

-- check the above produces no diamond
example [uβ : UniformSpace Ξ±] [uβ : UniformSpace Ξ²] :
    (Prod.topologicalSpace : TopologicalSpace (Ξ± Γ Ξ²)) = UniformSpace.toTopologicalSpace :=
  rfl

theorem uniformity_prod [UniformSpace Ξ±] [UniformSpace Ξ²] :
    π€ (Ξ± Γ Ξ²) =
      ((π€ Ξ±).comap fun p : (Ξ± Γ Ξ²) Γ Ξ± Γ Ξ² => (p.1.1, p.2.1))β(π€ Ξ²).comap fun p : (Ξ± Γ Ξ²) Γ Ξ± Γ Ξ² => (p.1.2, p.2.2) :=
  rfl

theorem uniformity_prod_eq_prod [UniformSpace Ξ±] [UniformSpace Ξ²] :
    π€ (Ξ± Γ Ξ²) = map (fun p : (Ξ± Γ Ξ±) Γ Ξ² Γ Ξ² => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (π€ Ξ± ΓαΆ  π€ Ξ²) := by
  rw [map_swap4_eq_comap, uniformity_prod, Filter.prod, comap_inf, comap_comap, comap_comap]

theorem mem_map_iff_exists_image' {Ξ± : Type _} {Ξ² : Type _} {f : Filter Ξ±} {m : Ξ± β Ξ²} {t : Set Ξ²} :
    t β (map m f).Sets β β s β f, m '' s β t :=
  mem_map_iff_exists_image

theorem mem_uniformity_of_uniform_continuous_invariant [UniformSpace Ξ±] {s : Set (Ξ± Γ Ξ±)} {f : Ξ± β Ξ± β Ξ±}
    (hf : UniformContinuous fun p : Ξ± Γ Ξ± => f p.1 p.2) (hs : s β π€ Ξ±) :
    β u β π€ Ξ±, β a b c, (a, b) β u β (f a c, f b c) β s := by
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff, (Β· β Β·)] at hf
  rcases mem_map_iff_exists_image'.1 (hf hs) with β¨t, ht, htsβ©
  clear hf
  rcases mem_prod_iff.1 ht with β¨u, hu, v, hv, huvtβ©
  clear ht
  refine' β¨u, hu, fun a b c hab => hts <| (mem_image _ _ _).2 β¨β¨β¨a, bβ©, β¨c, cβ©β©, huvt β¨_, _β©, _β©β©
  exact hab
  exact refl_mem_uniformity hv
  rfl

theorem mem_uniform_prod [tβ : UniformSpace Ξ±] [tβ : UniformSpace Ξ²] {a : Set (Ξ± Γ Ξ±)} {b : Set (Ξ² Γ Ξ²)} (ha : a β π€ Ξ±)
    (hb : b β π€ Ξ²) : { p : (Ξ± Γ Ξ²) Γ Ξ± Γ Ξ² | (p.1.1, p.2.1) β a β§ (p.1.2, p.2.2) β b } β @uniformity (Ξ± Γ Ξ²) _ := by
  rw [uniformity_prod] <;> exact inter_mem_inf (preimage_mem_comap ha) (preimage_mem_comap hb)

theorem tendsto_prod_uniformity_fst [UniformSpace Ξ±] [UniformSpace Ξ²] :
    Tendsto (fun p : (Ξ± Γ Ξ²) Γ Ξ± Γ Ξ² => (p.1.1, p.2.1)) (π€ (Ξ± Γ Ξ²)) (π€ Ξ±) :=
  le_transβ (map_mono inf_le_left) map_comap_le

theorem tendsto_prod_uniformity_snd [UniformSpace Ξ±] [UniformSpace Ξ²] :
    Tendsto (fun p : (Ξ± Γ Ξ²) Γ Ξ± Γ Ξ² => (p.1.2, p.2.2)) (π€ (Ξ± Γ Ξ²)) (π€ Ξ²) :=
  le_transβ (map_mono inf_le_right) map_comap_le

theorem uniform_continuous_fst [UniformSpace Ξ±] [UniformSpace Ξ²] : UniformContinuous fun p : Ξ± Γ Ξ² => p.1 :=
  tendsto_prod_uniformity_fst

theorem uniform_continuous_snd [UniformSpace Ξ±] [UniformSpace Ξ²] : UniformContinuous fun p : Ξ± Γ Ξ² => p.2 :=
  tendsto_prod_uniformity_snd

variable [UniformSpace Ξ±] [UniformSpace Ξ²] [UniformSpace Ξ³]

theorem UniformContinuous.prod_mk {fβ : Ξ± β Ξ²} {fβ : Ξ± β Ξ³} (hβ : UniformContinuous fβ) (hβ : UniformContinuous fβ) :
    UniformContinuous fun a => (fβ a, fβ a) := by
  rw [UniformContinuous, uniformity_prod] <;> exact tendsto_inf.2 β¨tendsto_comap_iff.2 hβ, tendsto_comap_iff.2 hββ©

theorem UniformContinuous.prod_mk_left {f : Ξ± Γ Ξ² β Ξ³} (h : UniformContinuous f) (b) :
    UniformContinuous fun a => f (a, b) :=
  h.comp (uniform_continuous_id.prod_mk uniform_continuous_const)

theorem UniformContinuous.prod_mk_right {f : Ξ± Γ Ξ² β Ξ³} (h : UniformContinuous f) (a) :
    UniformContinuous fun b => f (a, b) :=
  h.comp (uniform_continuous_const.prod_mk uniform_continuous_id)

theorem UniformContinuous.prod_map [UniformSpace Ξ΄] {f : Ξ± β Ξ³} {g : Ξ² β Ξ΄} (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous (Prod.map f g) :=
  (hf.comp uniform_continuous_fst).prod_mk (hg.comp uniform_continuous_snd)

theorem to_topological_space_prod {Ξ±} {Ξ²} [u : UniformSpace Ξ±] [v : UniformSpace Ξ²] :
    @UniformSpace.toTopologicalSpace (Ξ± Γ Ξ²) Prod.uniformSpace =
      @Prod.topologicalSpace Ξ± Ξ² u.toTopologicalSpace v.toTopologicalSpace :=
  rfl

/-- A version of `uniform_continuous_inf_dom_left` for binary functions -/
theorem uniform_continuous_inf_dom_leftβ {Ξ± Ξ² Ξ³} {f : Ξ± β Ξ² β Ξ³} {ua1 ua2 : UniformSpace Ξ±} {ub1 ub2 : UniformSpace Ξ²}
    {uc1 : UniformSpace Ξ³}
    (h : by
      have := ua1 <;> have := ub1 <;> exact UniformContinuous fun p : Ξ± Γ Ξ² => f p.1 p.2) :
    by
    have := ua1βua2 <;> have := ub1βub2 <;> exact UniformContinuous fun p : Ξ± Γ Ξ² => f p.1 p.2 := by
  -- proof essentially copied from ``continuous_inf_dom_leftβ`
  have ha := @uniform_continuous_inf_dom_left _ _ id ua1 ua2 ua1 (@uniform_continuous_id _ (id _))
  have hb := @uniform_continuous_inf_dom_left _ _ id ub1 ub2 ub1 (@uniform_continuous_id _ (id _))
  have h_unif_cont_id := @UniformContinuous.prod_map _ _ _ _ (ua1βua2) (ub1βub2) ua1 ub1 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

/-- A version of `uniform_continuous_inf_dom_right` for binary functions -/
theorem uniform_continuous_inf_dom_rightβ {Ξ± Ξ² Ξ³} {f : Ξ± β Ξ² β Ξ³} {ua1 ua2 : UniformSpace Ξ±} {ub1 ub2 : UniformSpace Ξ²}
    {uc1 : UniformSpace Ξ³}
    (h : by
      have := ua2 <;> have := ub2 <;> exact UniformContinuous fun p : Ξ± Γ Ξ² => f p.1 p.2) :
    by
    have := ua1βua2 <;> have := ub1βub2 <;> exact UniformContinuous fun p : Ξ± Γ Ξ² => f p.1 p.2 := by
  -- proof essentially copied from ``continuous_inf_dom_rightβ`
  have ha := @uniform_continuous_inf_dom_right _ _ id ua1 ua2 ua2 (@uniform_continuous_id _ (id _))
  have hb := @uniform_continuous_inf_dom_right _ _ id ub1 ub2 ub2 (@uniform_continuous_id _ (id _))
  have h_unif_cont_id := @UniformContinuous.prod_map _ _ _ _ (ua1βua2) (ub1βub2) ua2 ub2 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

/-- A version of `uniform_continuous_Inf_dom` for binary functions -/
theorem uniform_continuous_Inf_domβ {Ξ± Ξ² Ξ³} {f : Ξ± β Ξ² β Ξ³} {uas : Set (UniformSpace Ξ±)} {ubs : Set (UniformSpace Ξ²)}
    {ua : UniformSpace Ξ±} {ub : UniformSpace Ξ²} {uc : UniformSpace Ξ³} (ha : ua β uas) (hb : ub β ubs)
    (hf : UniformContinuous fun p : Ξ± Γ Ξ² => f p.1 p.2) : by
    have := Inf uas <;> have := Inf ubs <;> exact @UniformContinuous _ _ _ uc fun p : Ξ± Γ Ξ² => f p.1 p.2 := by
  -- proof essentially copied from ``continuous_Inf_dom`
  let t : UniformSpace (Ξ± Γ Ξ²) := Prod.uniformSpace
  have ha := uniform_continuous_Inf_dom ha uniform_continuous_id
  have hb := uniform_continuous_Inf_dom hb uniform_continuous_id
  have h_unif_cont_id := @UniformContinuous.prod_map _ _ _ _ (Inf uas) (Inf ubs) ua ub _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ hf h_unif_cont_id

end Prod

section

open UniformSpace Function

variable {Ξ΄' : Type _} [UniformSpace Ξ±] [UniformSpace Ξ²] [UniformSpace Ξ³] [UniformSpace Ξ΄] [UniformSpace Ξ΄']

-- mathport name: Β«expr ββ Β»
local notation f "ββ" g => Function.bicompr f g

/-- Uniform continuity for functions of two variables. -/
def UniformContinuousβ (f : Ξ± β Ξ² β Ξ³) :=
  UniformContinuous (uncurry f)

theorem uniform_continuousβ_def (f : Ξ± β Ξ² β Ξ³) : UniformContinuousβ f β UniformContinuous (uncurry f) :=
  Iff.rfl

theorem UniformContinuousβ.uniform_continuous {f : Ξ± β Ξ² β Ξ³} (h : UniformContinuousβ f) :
    UniformContinuous (uncurry f) :=
  h

theorem uniform_continuousβ_curry (f : Ξ± Γ Ξ² β Ξ³) : UniformContinuousβ (Function.curry f) β UniformContinuous f := by
  rw [UniformContinuousβ, uncurry_curry]

theorem UniformContinuousβ.comp {f : Ξ± β Ξ² β Ξ³} {g : Ξ³ β Ξ΄} (hg : UniformContinuous g) (hf : UniformContinuousβ f) :
    UniformContinuousβ (gββf) :=
  hg.comp hf

theorem UniformContinuousβ.bicompl {f : Ξ± β Ξ² β Ξ³} {ga : Ξ΄ β Ξ±} {gb : Ξ΄' β Ξ²} (hf : UniformContinuousβ f)
    (hga : UniformContinuous ga) (hgb : UniformContinuous gb) : UniformContinuousβ (bicompl f ga gb) :=
  hf.UniformContinuous.comp (hga.prod_map hgb)

end

theorem to_topological_space_subtype [u : UniformSpace Ξ±] {p : Ξ± β Prop} :
    @UniformSpace.toTopologicalSpace (Subtype p) Subtype.uniformSpace =
      @Subtype.topologicalSpace Ξ± p u.toTopologicalSpace :=
  rfl

section Sum

variable [UniformSpace Ξ±] [UniformSpace Ξ²]

open Sum

/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
def UniformSpace.Core.sum : UniformSpace.Core (Sum Ξ± Ξ²) :=
  UniformSpace.Core.mk'
    (map (fun p : Ξ± Γ Ξ± => (inl p.1, inl p.2)) (π€ Ξ±)βmap (fun p : Ξ² Γ Ξ² => (inr p.1, inr p.2)) (π€ Ξ²))
    (fun r β¨Hβ, Hββ© x => by
      cases x <;> [apply refl_mem_uniformity Hβ, apply refl_mem_uniformity Hβ])
    (fun r β¨Hβ, Hββ© => β¨symm_le_uniformity Hβ, symm_le_uniformity Hββ©) fun r β¨HrΞ±, HrΞ²β© => by
    rcases comp_mem_uniformity_sets HrΞ± with β¨tΞ±, htΞ±, HtΞ±β©
    rcases comp_mem_uniformity_sets HrΞ² with β¨tΞ², htΞ², HtΞ²β©
    refine'
      β¨_,
        β¨mem_map_iff_exists_image.2 β¨tΞ±, htΞ±, subset_union_left _ _β©,
          mem_map_iff_exists_image.2 β¨tΞ², htΞ², subset_union_right _ _β©β©,
        _β©
    rintro β¨_, _β© β¨z, β¨β¨a, bβ©, hab, β¨β©β© | β¨β¨a, bβ©, hab, β¨β©β©, β¨β¨_, cβ©, hbc, β¨β©β© | β¨β¨_, cβ©, hbc, β¨β©β©β©
    Β· have A : (a, c) β tΞ± β tΞ± := β¨b, hab, hbcβ©
      exact HtΞ± A
      
    Β· have A : (a, c) β tΞ² β tΞ² := β¨b, hab, hbcβ©
      exact HtΞ² A
      

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
theorem union_mem_uniformity_sum {a : Set (Ξ± Γ Ξ±)} (ha : a β π€ Ξ±) {b : Set (Ξ² Γ Ξ²)} (hb : b β π€ Ξ²) :
    (fun p : Ξ± Γ Ξ± => (inl p.1, inl p.2)) '' a βͺ (fun p : Ξ² Γ Ξ² => (inr p.1, inr p.2)) '' b β
      (@UniformSpace.Core.sum Ξ± Ξ² _ _).uniformity :=
  β¨mem_map_iff_exists_image.2 β¨_, ha, subset_union_left _ _β©,
    mem_map_iff_exists_image.2 β¨_, hb, subset_union_right _ _β©β©

/- To prove that the topology defined by the uniform structure on the disjoint union coincides with
the disjoint union topology, we need two lemmas saying that open sets can be characterized by
the uniform structure -/
theorem uniformity_sum_of_open_aux {s : Set (Sum Ξ± Ξ²)} (hs : IsOpen s) {x : Sum Ξ± Ξ²} (xs : x β s) :
    { p : Sum Ξ± Ξ² Γ Sum Ξ± Ξ² | p.1 = x β p.2 β s } β (@UniformSpace.Core.sum Ξ± Ξ² _ _).uniformity := by
  cases x
  Β· refine'
        mem_of_superset (union_mem_uniformity_sum (mem_nhds_uniformity_iff_right.1 (IsOpen.mem_nhds hs.1 xs)) univ_mem)
          (union_subset _ _) <;>
      rintro _ β¨β¨_, bβ©, h, β¨β©β© β¨β©
    exact h rfl
    
  Β· refine'
        mem_of_superset (union_mem_uniformity_sum univ_mem (mem_nhds_uniformity_iff_right.1 (IsOpen.mem_nhds hs.2 xs)))
          (union_subset _ _) <;>
      rintro _ β¨β¨a, _β©, h, β¨β©β© β¨β©
    exact h rfl
    

theorem open_of_uniformity_sum_aux {s : Set (Sum Ξ± Ξ²)}
    (hs : β, β x β s, β, { p : Sum Ξ± Ξ² Γ Sum Ξ± Ξ² | p.1 = x β p.2 β s } β (@UniformSpace.Core.sum Ξ± Ξ² _ _).uniformity) :
    IsOpen s := by
  constructor
  Β· refine' (@is_open_iff_mem_nhds Ξ± _ _).2 fun a ha => mem_nhds_uniformity_iff_right.2 _
    rcases mem_map_iff_exists_image.1 (hs _ ha).1 with β¨t, ht, stβ©
    refine' mem_of_superset ht _
    rintro p pt rfl
    exact st β¨_, pt, rflβ© rfl
    
  Β· refine' (@is_open_iff_mem_nhds Ξ² _ _).2 fun b hb => mem_nhds_uniformity_iff_right.2 _
    rcases mem_map_iff_exists_image.1 (hs _ hb).2 with β¨t, ht, stβ©
    refine' mem_of_superset ht _
    rintro p pt rfl
    exact st β¨_, pt, rflβ© rfl
    

-- We can now define the uniform structure on the disjoint union
instance Sum.uniformSpace : UniformSpace (Sum Ξ± Ξ²) where
  toCore := UniformSpace.Core.sum
  is_open_uniformity := fun s => β¨uniformity_sum_of_open_aux, open_of_uniformity_sum_auxβ©

theorem Sum.uniformity :
    π€ (Sum Ξ± Ξ²) = map (fun p : Ξ± Γ Ξ± => (inl p.1, inl p.2)) (π€ Ξ±)βmap (fun p : Ξ² Γ Ξ² => (inr p.1, inr p.2)) (π€ Ξ²) :=
  rfl

end Sum

end Constructions

/-- Let `c : ΞΉ β set Ξ±` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x β s` its `n`-neighborhood is contained in some `c i`. -/
-- For a version of the Lebesgue number lemma assuming only a sequentially compact space,
-- see topology/sequences.lean
theorem lebesgue_number_lemma {Ξ± : Type u} [UniformSpace Ξ±] {s : Set Ξ±} {ΞΉ} {c : ΞΉ β Set Ξ±} (hs : IsCompact s)
    (hcβ : β i, IsOpen (c i)) (hcβ : s β β i, c i) : β n β π€ Ξ±, β, β x β s, β, β i, { y | (x, y) β n } β c i := by
  let u := fun n => { x | β i, β m β π€ Ξ±, { y | (x, y) β m β n } β c i }
  have huβ : β, β n β π€ Ξ±, β, IsOpen (u n) := by
    refine' fun n hn => is_open_uniformity.2 _
    rintro x β¨i, m, hm, hβ©
    rcases comp_mem_uniformity_sets hm with β¨m', hm', mm'β©
    apply (π€ Ξ±).sets_of_superset hm'
    rintro β¨x, yβ© hp rfl
    refine' β¨i, m', hm', fun z hz => h (monotone_comp_rel monotone_id monotone_const mm' _)β©
    dsimp' [-mem_comp_rel]  at hzβ’
    rw [comp_rel_assoc]
    exact β¨y, hp, hzβ©
  have huβ : s β β n β π€ Ξ±, u n := by
    intro x hx
    rcases mem_Union.1 (hcβ hx) with β¨i, hβ©
    rcases comp_mem_uniformity_sets (is_open_uniformity.1 (hcβ i) x h) with β¨m', hm', mm'β©
    exact mem_bUnion hm' β¨i, _, hm', fun y hy => mm' hy rflβ©
  rcases hs.elim_finite_subcover_image huβ huβ with β¨b, bu, b_fin, b_coverβ©
  refine' β¨_, (bInter_mem b_fin).2 bu, fun x hx => _β©
  rcases mem_Unionβ.1 (b_cover hx) with β¨n, bn, i, m, hm, hβ©
  refine' β¨i, fun y hy => h _β©
  exact prod_mk_mem_comp_rel (refl_mem_uniformity hm) (bInter_subset_of_mem bn hy)

/-- Let `c : set (set Ξ±)` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x β s` its `n`-neighborhood is contained in some `t β c`. -/
theorem lebesgue_number_lemma_sUnion {Ξ± : Type u} [UniformSpace Ξ±] {s : Set Ξ±} {c : Set (Set Ξ±)} (hs : IsCompact s)
    (hcβ : β, β t β c, β, IsOpen t) (hcβ : s β ββc) : β n β π€ Ξ±, β, β x β s, β, β t β c, β y, (x, y) β n β y β t := by
  rw [sUnion_eq_Union] at hcβ <;>
    simpa using
      lebesgue_number_lemma hs
        (by
          simpa)
        hcβ

/-- A useful consequence of the Lebesgue number lemma: given any compact set `K` contained in an
open set `U`, we can find an (open) entourage `V` such that the ball of size `V` about any point of
`K` is contained in `U`. -/
theorem lebesgue_number_of_compact_open [UniformSpace Ξ±] {K U : Set Ξ±} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K β U) : β V β π€ Ξ±, IsOpen V β§ β, β x β K, β, UniformSpace.Ball x V β U := by
  let W : K β Set (Ξ± Γ Ξ±) := fun k => Classical.some <| is_open_iff_open_ball_subset.mp hU k.1 <| hKU k.2
  have hW : β k, W k β π€ Ξ± β§ IsOpen (W k) β§ UniformSpace.Ball k.1 (W k) β U := by
    intro k
    obtain β¨hβ, hβ, hββ© := Classical.some_spec (is_open_iff_open_ball_subset.mp hU k.1 (hKU k.2))
    exact β¨hβ, hβ, hββ©
  let c : K β Set Ξ± := fun k => UniformSpace.Ball k.1 (W k)
  have hcβ : β k, IsOpen (c k) := fun k => UniformSpace.is_open_ball k.1 (hW k).2.1
  have hcβ : K β β i, c i := by
    intro k hk
    simp only [β mem_Union, β SetCoe.exists]
    exact β¨k, hk, UniformSpace.mem_ball_self k (hW β¨k, hkβ©).1β©
  have hcβ : β k, c k β U := fun k => (hW k).2.2
  obtain β¨V, hV, hV'β© := lebesgue_number_lemma hK hcβ hcβ
  refine' β¨Interior V, interior_mem_uniformity hV, is_open_interior, _β©
  intro k hk
  obtain β¨k', hk'β© := hV' k hk
  exact ((ball_mono interior_subset k).trans hk').trans (hcβ k')

/-!
### Expressing continuity properties in uniform spaces

We reformulate the various continuity properties of functions taking values in a uniform space
in terms of the uniformity in the target. Since the same lemmas (essentially with the same names)
also exist for metric spaces and emetric spaces (reformulating things in terms of the distance or
the edistance in the target), we put them in a namespace `uniform` here.

In the metric and emetric space setting, there are also similar lemmas where one assumes that
both the source and the target are metric spaces, reformulating things in terms of the distance
on both sides. These lemmas are generally written without primes, and the versions where only
the target is a metric space is primed. We follow the same convention here, thus giving lemmas
with primes.
-/


namespace Uniform

variable [UniformSpace Ξ±]

theorem tendsto_nhds_right {f : Filter Ξ²} {u : Ξ² β Ξ±} {a : Ξ±} :
    Tendsto u f (π a) β Tendsto (fun x => (a, u x)) f (π€ Ξ±) :=
  β¨fun H => tendsto_left_nhds_uniformity.comp H, fun H s hs => by
    simpa [β mem_of_mem_nhds hs] using H (mem_nhds_uniformity_iff_right.1 hs)β©

theorem tendsto_nhds_left {f : Filter Ξ²} {u : Ξ² β Ξ±} {a : Ξ±} :
    Tendsto u f (π a) β Tendsto (fun x => (u x, a)) f (π€ Ξ±) :=
  β¨fun H => tendsto_right_nhds_uniformity.comp H, fun H s hs => by
    simpa [β mem_of_mem_nhds hs] using H (mem_nhds_uniformity_iff_left.1 hs)β©

theorem continuous_at_iff'_right [TopologicalSpace Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} :
    ContinuousAt f b β Tendsto (fun x => (f b, f x)) (π b) (π€ Ξ±) := by
  rw [ContinuousAt, tendsto_nhds_right]

theorem continuous_at_iff'_left [TopologicalSpace Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} :
    ContinuousAt f b β Tendsto (fun x => (f x, f b)) (π b) (π€ Ξ±) := by
  rw [ContinuousAt, tendsto_nhds_left]

theorem continuous_at_iff_prod [TopologicalSpace Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} :
    ContinuousAt f b β Tendsto (fun x : Ξ² Γ Ξ² => (f x.1, f x.2)) (π (b, b)) (π€ Ξ±) :=
  β¨fun H => le_transβ (H.prod_map' H) (nhds_le_uniformity _), fun H =>
    continuous_at_iff'_left.2 <| H.comp <| tendsto_id.prod_mk_nhds tendsto_const_nhdsβ©

theorem continuous_within_at_iff'_right [TopologicalSpace Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} {s : Set Ξ²} :
    ContinuousWithinAt f s b β Tendsto (fun x => (f b, f x)) (π[s] b) (π€ Ξ±) := by
  rw [ContinuousWithinAt, tendsto_nhds_right]

theorem continuous_within_at_iff'_left [TopologicalSpace Ξ²] {f : Ξ² β Ξ±} {b : Ξ²} {s : Set Ξ²} :
    ContinuousWithinAt f s b β Tendsto (fun x => (f x, f b)) (π[s] b) (π€ Ξ±) := by
  rw [ContinuousWithinAt, tendsto_nhds_left]

theorem continuous_on_iff'_right [TopologicalSpace Ξ²] {f : Ξ² β Ξ±} {s : Set Ξ²} :
    ContinuousOn f s β β, β b β s, β, Tendsto (fun x => (f b, f x)) (π[s] b) (π€ Ξ±) := by
  simp [β ContinuousOn, β continuous_within_at_iff'_right]

theorem continuous_on_iff'_left [TopologicalSpace Ξ²] {f : Ξ² β Ξ±} {s : Set Ξ²} :
    ContinuousOn f s β β, β b β s, β, Tendsto (fun x => (f x, f b)) (π[s] b) (π€ Ξ±) := by
  simp [β ContinuousOn, β continuous_within_at_iff'_left]

theorem continuous_iff'_right [TopologicalSpace Ξ²] {f : Ξ² β Ξ±} :
    Continuous f β β b, Tendsto (fun x => (f b, f x)) (π b) (π€ Ξ±) :=
  continuous_iff_continuous_at.trans <| forall_congrβ fun b => tendsto_nhds_right

theorem continuous_iff'_left [TopologicalSpace Ξ²] {f : Ξ² β Ξ±} :
    Continuous f β β b, Tendsto (fun x => (f x, f b)) (π b) (π€ Ξ±) :=
  continuous_iff_continuous_at.trans <| forall_congrβ fun b => tendsto_nhds_left

end Uniform

theorem Filter.Tendsto.congr_uniformity {Ξ± Ξ²} [UniformSpace Ξ²] {f g : Ξ± β Ξ²} {l : Filter Ξ±} {b : Ξ²}
    (hf : Tendsto f l (π b)) (hg : Tendsto (fun x => (f x, g x)) l (π€ Ξ²)) : Tendsto g l (π b) :=
  Uniform.tendsto_nhds_right.2 <| (Uniform.tendsto_nhds_right.1 hf).uniformity_trans hg

theorem Uniform.tendsto_congr {Ξ± Ξ²} [UniformSpace Ξ²] {f g : Ξ± β Ξ²} {l : Filter Ξ±} {b : Ξ²}
    (hfg : Tendsto (fun x => (f x, g x)) l (π€ Ξ²)) : Tendsto f l (π b) β Tendsto g l (π b) :=
  β¨fun h => h.congr_uniformity hfg, fun h => h.congr_uniformity hfg.uniformity_symmβ©

