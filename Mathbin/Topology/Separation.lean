import Mathbin.Topology.SubsetProperties 
import Mathbin.Topology.Connected

/-!
# Separation properties of topological spaces.

This file defines the predicate `separated`, and common separation axioms
(under the Kolmogorov classification).

## Main definitions

* `separated`: Two `set`s are separated if they are contained in disjoint open sets.
* `t0_space`: A T₀/Kolmogorov space is a space where, for every two points `x ≠ y`,
  there is an open set that contains one, but not the other.
* `t1_space`: A T₁/Fréchet space is a space where every singleton set is closed.
  This is equivalent to, for every pair `x ≠ y`, there existing an open set containing `x`
  but not `y` (`t1_iff_exists_open` shows that these conditions are equivalent.)
* `t2_space`: A T₂/Hausdorff space is a space where, for every two points `x ≠ y`,
  there is two disjoint open sets, one containing `x`, and the other `y`.
* `t2_5_space`: A T₂.₅/Urysohn space is a space where, for every two points `x ≠ y`,
  there is two open sets, one containing `x`, and the other `y`, whose closures are disjoint.
* `regular_space`: A T₃ space (sometimes referred to as regular, but authors vary on
  whether this includes T₂; `mathlib` does), is one where given any closed `C` and `x ∉ C`,
  there is disjoint open sets containing `x` and `C` respectively. In `mathlib`, T₃ implies T₂.₅.
* `normal_space`: A T₄ space (sometimes referred to as normal, but authors vary on
  whether this includes T₂; `mathlib` does), is one where given two disjoint closed sets,
  we can find two open sets that separate them. In `mathlib`, T₄ implies T₃.

## Main results

### T₀ spaces

* `is_closed.exists_closed_singleton` Given a closed set `S` in a compact T₀ space,
  there is some `x ∈ S` such that `{x}` is closed.
* `exists_open_singleton_of_open_finset` Given an open `finset` `S` in a T₀ space,
  there is some `x ∈ S` such that `{x}` is open.

### T₁ spaces

* `is_closed_map_const`: The constant map is a closed map.
* `discrete_of_t1_of_finite`: A finite T₁ space must have the discrete topology.

### T₂ spaces

* `t2_iff_nhds`: A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter.
* `t2_iff_is_closed_diagonal`: A space is T₂ iff the `diagonal` of `α` (that is, the set of all
  points of the form `(a, a) : α × α`) is closed under the product topology.
* `finset_disjoint_finset_opens_of_t2`: Any two disjoint finsets are `separated`.
* Most topological constructions preserve Hausdorffness;
  these results are part of the typeclass inference system (e.g. `embedding.t2_space`)
* `set.eq_on.closure`: If two functions are equal on some set `s`, they are equal on its closure.
* `is_compact.is_closed`: All compact sets are closed.
* `locally_compact_of_compact_nhds`: If every point has a compact neighbourhood,
  then the space is locally compact.
* `tot_sep_of_zero_dim`: If `α` has a clopen basis, it is a `totally_separated_space`.
* `loc_compact_t2_tot_disc_iff_tot_sep`: A locally compact T₂ space is totally disconnected iff
  it is totally separated.

If the space is also compact:

* `normal_of_compact_t2`: A compact T₂ space is a `normal_space`.
* `connected_components_eq_Inter_clopen`: The connected component of a point
  is the intersection of all its clopen neighbourhoods.
* `compact_t2_tot_disc_iff_tot_sep`: Being a `totally_disconnected_space`
  is equivalent to being a `totally_separated_space`.
* `connected_components.t2`: `connected_components α` is T₂ for `α` T₂ and compact.

### T₃ spaces

* `disjoint_nested_nhds`: Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and
  `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint.

### Discrete spaces

* `discrete_topology_iff_nhds`: Discrete topological spaces are those whose neighbourhood
  filters are the `pure` filter (which is the principal filter at a singleton).
* `induced_bot`/`discrete_topology_induced`: The pullback of the discrete topology
  under an inclusion is the discrete topology.

## References

https://en.wikipedia.org/wiki/Separation_axiom
-/


open Set Filter

open_locale TopologicalSpace Filter Classical

universe u v

variable {α : Type u} {β : Type v} [TopologicalSpace α]

section Separation

/--
`separated` is a predicate on pairs of sub`set`s of a topological space.  It holds if the two
sub`set`s are contained in disjoint open sets.
-/
def Separated : Set α → Set α → Prop :=
  fun s t : Set α => ∃ U V : Set α, IsOpen U ∧ IsOpen V ∧ s ⊆ U ∧ t ⊆ V ∧ Disjoint U V

namespace Separated

open Separated

@[symm]
theorem symm {s t : Set α} : Separated s t → Separated t s :=
  fun ⟨U, V, oU, oV, aU, bV, UV⟩ => ⟨V, U, oV, oU, bV, aU, Disjoint.symm UV⟩

theorem comm (s t : Set α) : Separated s t ↔ Separated t s :=
  ⟨symm, symm⟩

theorem empty_right (a : Set α) : Separated a ∅ :=
  ⟨_, _, is_open_univ, is_open_empty, fun a h => mem_univ a,
    fun a h =>
      by 
        cases h,
    disjoint_empty _⟩

theorem empty_left (a : Set α) : Separated ∅ a :=
  (empty_right _).symm

theorem union_left {a b c : Set α} : Separated a c → Separated b c → Separated (a ∪ b) c :=
  fun ⟨U, V, oU, oV, aU, bV, UV⟩ ⟨W, X, oW, oX, aW, bX, WX⟩ =>
    ⟨U ∪ W, V ∩ X, IsOpen.union oU oW, IsOpen.inter oV oX, union_subset_union aU aW, subset_inter bV bX,
      Set.disjoint_union_left.mpr
        ⟨disjoint_of_subset_right (inter_subset_left _ _) UV, disjoint_of_subset_right (inter_subset_right _ _) WX⟩⟩

theorem union_right {a b c : Set α} (ab : Separated a b) (ac : Separated a c) : Separated a (b ∪ c) :=
  (ab.symm.union_left ac.symm).symm

end Separated

/-- A T₀ space, also known as a Kolmogorov space, is a topological space
  where for every pair `x ≠ y`, there is an open set containing one but not the other. -/
class T0Space (α : Type u) [TopologicalSpace α] : Prop where 
  t0 : ∀ x y, x ≠ y → ∃ U : Set α, IsOpen U ∧ Xorₓ (x ∈ U) (y ∈ U)

/-- Given a closed set `S` in a compact T₀ space,
there is some `x ∈ S` such that `{x}` is closed. -/
theorem IsClosed.exists_closed_singleton {α : Type _} [TopologicalSpace α] [T0Space α] [CompactSpace α] {S : Set α}
  (hS : IsClosed S) (hne : S.nonempty) : ∃ x : α, x ∈ S ∧ IsClosed ({x} : Set α) :=
  by 
    obtain ⟨V, Vsub, Vne, Vcls, hV⟩ := hS.exists_minimal_nonempty_closed_subset hne 
    byCases' hnt : ∃ (x y : α)(hx : x ∈ V)(hy : y ∈ V), x ≠ y
    ·
      exfalso 
      obtain ⟨x, y, hx, hy, hne⟩ := hnt 
      obtain ⟨U, hU, hsep⟩ := T0Space.t0 _ _ hne 
      have  : ∀ z w : α hz : z ∈ V hw : w ∈ V hz' : z ∈ U hw' : ¬w ∈ U, False
      ·
        intro z w hz hw hz' hw' 
        have uvne : (V ∩ Uᶜ).Nonempty
        ·
          use w 
          simp only [hw, hw', Set.mem_inter_eq, not_false_iff, and_selfₓ, Set.mem_compl_eq]
        specialize hV (V ∩ Uᶜ) (Set.inter_subset_left _ _) uvne (IsClosed.inter Vcls (is_closed_compl_iff.mpr hU))
        have  : V ⊆ Uᶜ
        ·
          rw [←hV]
          exact Set.inter_subset_right _ _ 
        exact this hz hz' 
      cases hsep
      ·
        exact this x y hx hy hsep.1 hsep.2
      ·
        exact this y x hy hx hsep.1 hsep.2
    ·
      pushNeg  at hnt 
      obtain ⟨z, hz⟩ := Vne 
      refine' ⟨z, Vsub hz, _⟩
      convert Vcls 
      ext 
      simp only [Set.mem_singleton_iff, Set.mem_compl_eq]
      constructor
      ·
        rintro rfl 
        exact hz
      ·
        exact fun hx => hnt x z hx hz

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (z «expr ∈ » s.filter (λ z, «expr ∈ »(z, U)))
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
/-- Given an open `finset` `S` in a T₀ space, there is some `x ∈ S` such that `{x}` is open. -/
theorem exists_open_singleton_of_open_finset [T0Space α] (s : Finset α) (sne : s.nonempty) (hso : IsOpen (s : Set α)) :
  ∃ (x : _)(_ : x ∈ s), IsOpen ({x} : Set α) :=
  by 
    induction' s using Finset.strongInductionOn with s ihs 
    byCases' hs : Set.Subsingleton (s : Set α)
    ·
      rcases sne with ⟨x, hx⟩
      refine' ⟨x, hx, _⟩
      have  : (s : Set α) = {x}
      exact hs.eq_singleton_of_mem hx 
      rwa [this] at hso
    ·
      dunfold Set.Subsingleton  at hs 
      pushNeg  at hs 
      rcases hs with ⟨x, hx, y, hy, hxy⟩
      rcases T0Space.t0 x y hxy with ⟨U, hU, hxyU⟩
      wlog H : x ∈ U ∧ y ∉ U := hxyU using x y, y x 
      obtain ⟨z, hzs, hz⟩ : ∃ (z : _)(_ : z ∈ s.filter fun z => z ∈ U), IsOpen ({z} : Set α)
      ·
        refine' ihs _ (Finset.filter_ssubset.2 ⟨y, hy, H.2⟩) ⟨x, Finset.mem_filter.2 ⟨hx, H.1⟩⟩ _ 
        rw [Finset.coe_filter]
        exact IsOpen.inter hso hU 
      exact ⟨z, (Finset.mem_filter.1 hzs).1, hz⟩

theorem exists_open_singleton_of_fintype [T0Space α] [f : Fintype α] [ha : Nonempty α] :
  ∃ x : α, IsOpen ({x} : Set α) :=
  by 
    refine' ha.elim fun x => _ 
    have  : IsOpen ((Finset.univ : Finset α) : Set α)
    ·
      simp 
    rcases exists_open_singleton_of_open_finset _ ⟨x, Finset.mem_univ x⟩ this with ⟨x, _, hx⟩
    exact ⟨x, hx⟩

instance Subtype.t0_space [T0Space α] {p : α → Prop} : T0Space (Subtype p) :=
  ⟨fun x y hxy =>
      let ⟨U, hU, hxyU⟩ := T0Space.t0 (x : α) y ((not_congr Subtype.ext_iff_val).1 hxy)
      ⟨(coeₓ : Subtype p → α) ⁻¹' U, is_open_induced hU, hxyU⟩⟩

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class T1Space (α : Type u) [TopologicalSpace α] : Prop where 
  t1 : ∀ x, IsClosed ({x} : Set α)

theorem is_closed_singleton [T1Space α] {x : α} : IsClosed ({x} : Set α) :=
  T1Space.t1 x

theorem is_open_compl_singleton [T1Space α] {x : α} : IsOpen ({x}ᶜ : Set α) :=
  is_closed_singleton.is_open_compl

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem is_open_ne [ T1Space α ] { x : α } : IsOpen { y | y ≠ x } := is_open_compl_singleton

theorem Ne.nhds_within_compl_singleton [T1Space α] {x y : α} (h : x ≠ y) : 𝓝[{y}ᶜ] x = 𝓝 x :=
  is_open_ne.nhds_within_eq h

theorem continuous_within_at_update_of_ne [T1Space α] [DecidableEq α] [TopologicalSpace β] {f : α → β} {s : Set α}
  {x y : α} {z : β} (hne : y ≠ x) : ContinuousWithinAt (Function.update f x z) s y ↔ ContinuousWithinAt f s y :=
  eventually_eq.congr_continuous_within_at
    (mem_nhds_within_of_mem_nhds$
      mem_of_superset (is_open_ne.mem_nhds hne)$ fun y' hy' => Function.update_noteq hy' _ _)
    (Function.update_noteq hne _ _)

theorem continuous_on_update_iff [T1Space α] [DecidableEq α] [TopologicalSpace β] {f : α → β} {s : Set α} {x : α}
  {y : β} :
  ContinuousOn (Function.update f x y) s ↔ ContinuousOn f (s \ {x}) ∧ (x ∈ s → tendsto f (𝓝[s \ {x}] x) (𝓝 y)) :=
  by 
    rw [ContinuousOn, ←and_forall_ne x, and_comm]
    refine' and_congr ⟨fun H z hz => _, fun H z hzx hzs => _⟩ (forall_congrₓ$ fun hxs => _)
    ·
      specialize H z hz.2 hz.1
      rw [continuous_within_at_update_of_ne hz.2] at H 
      exact H.mono (diff_subset _ _)
    ·
      rw [continuous_within_at_update_of_ne hzx]
      refine' (H z ⟨hzs, hzx⟩).mono_of_mem (inter_mem_nhds_within _ _)
      exact is_open_ne.mem_nhds hzx
    ·
      exact continuous_within_at_update_same

instance Subtype.t1_space {α : Type u} [TopologicalSpace α] [T1Space α] {p : α → Prop} : T1Space (Subtype p) :=
  ⟨fun ⟨x, hx⟩ =>
      is_closed_induced_iff.2$
        ⟨{x}, is_closed_singleton,
          Set.ext$
            fun y =>
              by 
                simp [Subtype.ext_iff_val]⟩⟩

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 100 )
  T1Space.t0_space
  [ T1Space α ] : T0Space α
  := ⟨ fun x y h => ⟨ { z | z ≠ y } , is_open_ne , Or.inl ⟨ h , not_not_intro rfl ⟩ ⟩ ⟩

theorem t1_iff_exists_open : T1Space α ↔ ∀ x y, x ≠ y → ∃ (U : Set α)(hU : IsOpen U), x ∈ U ∧ y ∉ U :=
  by 
    constructor
    ·
      intros t1 x y hxy 
      exact ⟨{y}ᶜ, is_open_compl_iff.mpr (T1Space.t1 y), mem_compl_singleton_iff.mpr hxy, not_not.mpr rfl⟩
    ·
      intro h 
      constructor 
      intro x 
      rw [←is_open_compl_iff]
      have p : ⋃₀{ U : Set α | x ∉ U ∧ IsOpen U } = {x}ᶜ
      ·
        apply subset.antisymm <;> intro t ht
        ·
          rcases ht with ⟨A, ⟨hxA, hA⟩, htA⟩
          rw [mem_compl_eq, mem_singleton_iff]
          rintro rfl 
          contradiction
        ·
          obtain ⟨U, hU, hh⟩ := h t x (mem_compl_singleton_iff.mp ht)
          exact ⟨U, ⟨hh.2, hU⟩, hh.1⟩
      rw [←p]
      exact is_open_sUnion fun B hB => hB.2

theorem compl_singleton_mem_nhds [T1Space α] {x y : α} (h : y ≠ x) : {x}ᶜ ∈ 𝓝 y :=
  IsOpen.mem_nhds is_open_compl_singleton$
    by 
      rwa [mem_compl_eq, mem_singleton_iff]

@[simp]
theorem closure_singleton [T1Space α] {a : α} : Closure ({a} : Set α) = {a} :=
  is_closed_singleton.closure_eq

theorem Set.Subsingleton.closure [T1Space α] {s : Set α} (hs : s.subsingleton) : (Closure s).Subsingleton :=
  hs.induction_on
      (by 
        simp )$
    fun x =>
      by 
        simp 

@[simp]
theorem subsingleton_closure [T1Space α] {s : Set α} : (Closure s).Subsingleton ↔ s.subsingleton :=
  ⟨fun h => h.mono subset_closure, fun h => h.closure⟩

theorem is_closed_map_const {α β} [TopologicalSpace α] [TopologicalSpace β] [T1Space β] {y : β} :
  IsClosedMap (Function.const α y) :=
  by 
    apply IsClosedMap.of_nonempty 
    intro s hs h2s 
    simpRw [h2s.image_const, is_closed_singleton]

theorem Finite.is_closed [T1Space α] {s : Set α} (hs : Set.Finite s) : IsClosed s :=
  by 
    rw [←bUnion_of_singleton s]
    exact is_closed_bUnion hs fun i hi => is_closed_singleton

theorem bInter_basis_nhds [T1Space α] {ι : Sort _} {p : ι → Prop} {s : ι → Set α} {x : α} (h : (𝓝 x).HasBasis p s) :
  (⋂ (i : _)(h : p i), s i) = {x} :=
  by 
    simp only [eq_singleton_iff_unique_mem, mem_Inter]
    refine' ⟨fun i hi => mem_of_mem_nhds$ h.mem_of_mem hi, fun y hy => _⟩
    contrapose! hy 
    rcases h.mem_iff.1 (compl_singleton_mem_nhds hy.symm) with ⟨i, hi, hsub⟩
    exact ⟨i, hi, fun h => hsub h rfl⟩

/-- Removing a non-isolated point from a dense set, one still obtains a dense set. -/
theorem Dense.diff_singleton [T1Space α] {s : Set α} (hs : Dense s) (x : α) [ne_bot (𝓝[{x}ᶜ] x)] : Dense (s \ {x}) :=
  hs.inter_of_open_right (dense_compl_singleton x) is_open_compl_singleton

/-- Removing a finset from a dense set in a space without isolated points, one still
obtains a dense set. -/
theorem Dense.diff_finset [T1Space α] [∀ x : α, ne_bot (𝓝[{x}ᶜ] x)] {s : Set α} (hs : Dense s) (t : Finset α) :
  Dense (s \ t) :=
  by 
    induction' t using Finset.induction_on with x s hxs ih hd
    ·
      simpa using hs
    ·
      rw [Finset.coe_insert, ←union_singleton, ←diff_diff]
      exact ih.diff_singleton _

/-- Removing a finite set from a dense set in a space without isolated points, one still
obtains a dense set. -/
theorem Dense.diff_finite [T1Space α] [∀ x : α, ne_bot (𝓝[{x}ᶜ] x)] {s : Set α} (hs : Dense s) {t : Set α}
  (ht : finite t) : Dense (s \ t) :=
  by 
    convert hs.diff_finset ht.to_finset 
    exact (finite.coe_to_finset _).symm

/-- If a function to a `t1_space` tends to some limit `b` at some point `a`, then necessarily
`b = f a`. -/
theorem eq_of_tendsto_nhds [TopologicalSpace β] [T1Space β] {f : α → β} {a : α} {b : β} (h : tendsto f (𝓝 a) (𝓝 b)) :
  f a = b :=
  by_contra$
    fun hfa : f a ≠ b =>
      have fact₁ : {f a}ᶜ ∈ 𝓝 b := compl_singleton_mem_nhds hfa.symm 
      have fact₂ : tendsto f (pure a) (𝓝 b) := h.comp (tendsto_id'$ pure_le_nhds a)
      fact₂ fact₁ (Eq.refl$ f a)

/-- To prove a function to a `t1_space` is continuous at some point `a`, it suffices to prove that
`f` admits *some* limit at `a`. -/
theorem continuous_at_of_tendsto_nhds [TopologicalSpace β] [T1Space β] {f : α → β} {a : α} {b : β}
  (h : tendsto f (𝓝 a) (𝓝 b)) : ContinuousAt f a :=
  show tendsto f (𝓝 a) (𝓝$ f a)by 
    rwa [eq_of_tendsto_nhds h]

/-- If the punctured neighborhoods of a point form a nontrivial filter, then any neighborhood is
infinite. -/
theorem infinite_of_mem_nhds {α} [TopologicalSpace α] [T1Space α] (x : α) [hx : ne_bot (𝓝[{x}ᶜ] x)] {s : Set α}
  (hs : s ∈ 𝓝 x) : Set.Infinite s :=
  by 
    (
      contrapose! hx)
    rw [Set.not_infinite] at hx 
    have A : IsClosed (s \ {x}) := Finite.is_closed (hx.subset (diff_subset _ _))
    have B : (s \ {x})ᶜ ∈ 𝓝 x
    ·
      apply IsOpen.mem_nhds
      ·
        apply is_open_compl_iff.2 A
      ·
        simp only [not_true, not_false_iff, mem_diff, and_falseₓ, mem_compl_eq, mem_singleton]
    have C : {x} ∈ 𝓝 x
    ·
      apply Filter.mem_of_superset (Filter.inter_mem hs B)
      intro y hy 
      simp only [mem_singleton_iff, mem_inter_eq, not_and, not_not, mem_diff, mem_compl_eq] at hy 
      simp only [hy.right hy.left, mem_singleton]
    have D : {x}ᶜ ∈ 𝓝[{x}ᶜ] x := self_mem_nhds_within 
    simpa [←empty_mem_iff_bot] using Filter.inter_mem (mem_nhds_within_of_mem_nhds C) D

theorem discrete_of_t1_of_finite {X : Type _} [TopologicalSpace X] [T1Space X] [Fintype X] : DiscreteTopology X :=
  by 
    apply singletons_open_iff_discrete.mp 
    intro x 
    rw [←is_closed_compl_iff]
    exact Finite.is_closed (finite.of_fintype _)

theorem singleton_mem_nhds_within_of_mem_discrete {s : Set α} [DiscreteTopology s] {x : α} (hx : x ∈ s) :
  {x} ∈ 𝓝[s] x :=
  by 
    have  : ({⟨x, hx⟩} : Set s) ∈ 𝓝 (⟨x, hx⟩ : s)
    ·
      simp [nhds_discrete]
    simpa only [nhds_within_eq_map_subtype_coe hx, image_singleton] using @image_mem_map _ _ _ (coeₓ : s → α) _ this

/-- The neighbourhoods filter of `x` within `s`, under the discrete topology, is equal to
the pure `x` filter (which is the principal filter at the singleton `{x}`.) -/
theorem nhds_within_of_mem_discrete {s : Set α} [DiscreteTopology s] {x : α} (hx : x ∈ s) : 𝓝[s] x = pure x :=
  le_antisymmₓ (le_pure_iff.2$ singleton_mem_nhds_within_of_mem_discrete hx) (pure_le_nhds_within hx)

theorem Filter.HasBasis.exists_inter_eq_singleton_of_mem_discrete {ι : Type _} {p : ι → Prop} {t : ι → Set α}
  {s : Set α} [DiscreteTopology s] {x : α} (hb : (𝓝 x).HasBasis p t) (hx : x ∈ s) :
  ∃ (i : _)(hi : p i), t i ∩ s = {x} :=
  by 
    rcases(nhds_within_has_basis hb s).mem_iff.1 (singleton_mem_nhds_within_of_mem_discrete hx) with ⟨i, hi, hix⟩
    exact ⟨i, hi, subset.antisymm hix$ singleton_subset_iff.2 ⟨mem_of_mem_nhds$ hb.mem_of_mem hi, hx⟩⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (U «expr ∈ » expr𝓝() x)
/-- A point `x` in a discrete subset `s` of a topological space admits a neighbourhood
that only meets `s` at `x`.  -/
theorem nhds_inter_eq_singleton_of_mem_discrete {s : Set α} [DiscreteTopology s] {x : α} (hx : x ∈ s) :
  ∃ (U : _)(_ : U ∈ 𝓝 x), U ∩ s = {x} :=
  by 
    simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hx

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (U «expr ∈ » «expr𝓝[ ] »(«expr ᶜ»({x}), x))
/-- For point `x` in a discrete subset `s` of a topological space, there is a set `U`
such that
1. `U` is a punctured neighborhood of `x` (ie. `U ∪ {x}` is a neighbourhood of `x`),
2. `U` is disjoint from `s`.
-/
theorem disjoint_nhds_within_of_mem_discrete {s : Set α} [DiscreteTopology s] {x : α} (hx : x ∈ s) :
  ∃ (U : _)(_ : U ∈ 𝓝[{x}ᶜ] x), Disjoint U s :=
  let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hx
  ⟨{x}ᶜ ∩ V, inter_mem_nhds_within _ h,
    disjoint_iff_inter_eq_empty.mpr
      (by 
        rw [inter_assoc, h', compl_inter_self])⟩

/-- Let `X` be a topological space and let `s, t ⊆ X` be two subsets.  If there is an inclusion
`t ⊆ s`, then the topological space structure on `t` induced by `X` is the same as the one
obtained by the induced topological space structure on `s`. -/
theorem TopologicalSpace.subset_trans {X : Type _} [tX : TopologicalSpace X] {s t : Set X} (ts : t ⊆ s) :
  (Subtype.topologicalSpace : TopologicalSpace t) =
    (Subtype.topologicalSpace : TopologicalSpace s).induced (Set.inclusion ts) :=
  by 
    change tX.induced ((coeₓ : s → X) ∘ Set.inclusion ts) = TopologicalSpace.induced (Set.inclusion ts) (tX.induced _)
    rw [←induced_compose]

/-- This lemma characterizes discrete topological spaces as those whose singletons are
neighbourhoods. -/
theorem discrete_topology_iff_nhds {X : Type _} [TopologicalSpace X] :
  DiscreteTopology X ↔ (nhds : X → Filter X) = pure :=
  by 
    constructor
    ·
      intro hX 
      exact nhds_discrete X
    ·
      intro h 
      constructor 
      apply eq_of_nhds_eq_nhds 
      simp [h, nhds_bot]

/-- The topology pulled-back under an inclusion `f : X → Y` from the discrete topology (`⊥`) is the
discrete topology.
This version does not assume the choice of a topology on either the source `X`
nor the target `Y` of the inclusion `f`. -/
theorem induced_bot {X Y : Type _} {f : X → Y} (hf : Function.Injective f) : TopologicalSpace.induced f ⊥ = ⊥ :=
  eq_of_nhds_eq_nhds
    (by 
      simp [nhds_induced, ←Set.image_singleton, hf.preimage_image, nhds_bot])

/-- The topology induced under an inclusion `f : X → Y` from the discrete topological space `Y`
is the discrete topology on `X`. -/
theorem discrete_topology_induced {X Y : Type _} [tY : TopologicalSpace Y] [DiscreteTopology Y] {f : X → Y}
  (hf : Function.Injective f) : @DiscreteTopology X (TopologicalSpace.induced f tY) :=
  by 
    constructor 
    rw [DiscreteTopology.eq_bot Y]
    exact induced_bot hf

/-- Let `s, t ⊆ X` be two subsets of a topological space `X`.  If `t ⊆ s` and the topology induced
by `X`on `s` is discrete, then also the topology induces on `t` is discrete.  -/
theorem DiscreteTopology.of_subset {X : Type _} [TopologicalSpace X] {s t : Set X} (ds : DiscreteTopology s)
  (ts : t ⊆ s) : DiscreteTopology t :=
  by 
    rw [TopologicalSpace.subset_trans ts, ds.eq_bot]
    exact { eq_bot := induced_bot (Set.inclusion_injective ts) }

/-- A T₂ space, also known as a Hausdorff space, is one in which for every
  `x ≠ y` there exists disjoint open sets around `x` and `y`. This is
  the most widely used of the separation axioms. -/
class T2Space (α : Type u) [TopologicalSpace α] : Prop where 
  t2 : ∀ x y, x ≠ y → ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅

theorem t2_separation [T2Space α] {x y : α} (h : x ≠ y) :
  ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
  T2Space.t2 x y h

instance (priority := 100) T2Space.t1_space [T2Space α] : T1Space α :=
  ⟨fun x =>
      is_open_compl_iff.1$
        is_open_iff_forall_mem_open.2$
          fun y hxy =>
            let ⟨u, v, hu, hv, hyu, hxv, huv⟩ := t2_separation (mt mem_singleton_of_eq hxy)
            ⟨u, fun z hz1 hz2 => (ext_iff.1 huv x).1 ⟨mem_singleton_iff.1 hz2 ▸ hz1, hxv⟩, hu, hyu⟩⟩

theorem eq_of_nhds_ne_bot [ht : T2Space α] {x y : α} (h : ne_bot (𝓝 x⊓𝓝 y)) : x = y :=
  Classical.by_contradiction$
    fun this : x ≠ y =>
      let ⟨u, v, hu, hv, hx, hy, huv⟩ := T2Space.t2 x y this 
      absurd huv$ (inf_ne_bot_iff.1 h (IsOpen.mem_nhds hu hx) (IsOpen.mem_nhds hv hy)).ne_empty

/-- A space is T₂ iff the neighbourhoods of distinct points generate the bottom filter. -/
theorem t2_iff_nhds : T2Space α ↔ ∀ {x y : α}, ne_bot (𝓝 x⊓𝓝 y) → x = y :=
  ⟨fun h =>
      by 
        exact fun x y => eq_of_nhds_ne_bot,
    fun h =>
      ⟨fun x y xy =>
          have  : 𝓝 x⊓𝓝 y = ⊥ := not_ne_bot.1$ mt h xy 
          let ⟨u', hu', v', hv', u'v'⟩ := empty_mem_iff_bot.mpr this 
          let ⟨u, uu', uo, hu⟩ := mem_nhds_iff.mp hu' 
          let ⟨v, vv', vo, hv⟩ := mem_nhds_iff.mp hv'
          ⟨u, v, uo, vo, hu, hv,
            by 
              rw [←subset_empty_iff, u'v']
              exact inter_subset_inter uu' vv'⟩⟩⟩

theorem t2_iff_ultrafilter : T2Space α ↔ ∀ {x y : α} f : Ultrafilter α, ↑f ≤ 𝓝 x → ↑f ≤ 𝓝 y → x = y :=
  t2_iff_nhds.trans$
    by 
      simp only [←exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp_distrib]

theorem is_closed_diagonal [T2Space α] : IsClosed (diagonal α) :=
  by 
    refine' is_closed_iff_cluster_pt.mpr _ 
    rintro ⟨a₁, a₂⟩ h 
    refine' eq_of_nhds_ne_bot ⟨fun this : 𝓝 a₁⊓𝓝 a₂ = ⊥ => h.ne _⟩
    obtain ⟨t₁, ht₁ : t₁ ∈ 𝓝 a₁, t₂, ht₂ : t₂ ∈ 𝓝 a₂, h' : t₁ ∩ t₂ = ∅⟩ := inf_eq_bot_iff.1 this 
    rw [inf_principal_eq_bot, nhds_prod_eq]
    apply mem_of_superset (prod_mem_prod ht₁ ht₂)
    rintro ⟨x, y⟩ ⟨x_in, y_in⟩ (heq : x = y)
    rw [←HEq] at *
    have  : x ∈ t₁ ∩ t₂ := ⟨x_in, y_in⟩
    rwa [h'] at this

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ⊆ » «expr ᶜ»(diagonal α))
theorem t2_iff_is_closed_diagonal : T2Space α ↔ IsClosed (diagonal α) :=
  by 
    constructor
    ·
      intro h 
      exact is_closed_diagonal
    ·
      intro h 
      constructor 
      intro x y hxy 
      have  : (x, y) ∈ diagonal αᶜ
      ·
        rwa [mem_compl_iff]
      obtain ⟨t, t_sub, t_op, xyt⟩ : ∃ (t : _)(_ : t ⊆ diagonal αᶜ), IsOpen t ∧ (x, y) ∈ t :=
        is_open_iff_forall_mem_open.mp h.is_open_compl _ this 
      rcases is_open_prod_iff.mp t_op x y xyt with ⟨U, V, U_op, V_op, xU, yV, H⟩
      use U, V, U_op, V_op, xU, yV 
      have  := subset.trans H t_sub 
      rw [eq_empty_iff_forall_not_mem]
      rintro z ⟨zU, zV⟩
      have  : ¬(z, z) ∈ diagonal α := this (mk_mem_prod zU zV)
      exact this rfl

section Separated

open Separated Finset

theorem finset_disjoint_finset_opens_of_t2 [T2Space α] : ∀ s t : Finset α, Disjoint s t → Separated (s : Set α) t :=
  by 
    refine' induction_on_union _ (fun a b hi d => (hi d.symm).symm) (fun a d => empty_right a) (fun a b ab => _) _
    ·
      obtain ⟨U, V, oU, oV, aU, bV, UV⟩ := t2_separation (Finset.disjoint_singleton.1 ab)
      refine' ⟨U, V, oU, oV, _, _, set.disjoint_iff_inter_eq_empty.mpr UV⟩ <;> exact singleton_subset_set_iff.mpr ‹_›
    ·
      intro a b c ac bc d 
      applyModCast union_left (ac (disjoint_of_subset_left (a.subset_union_left b) d)) (bc _)
      exact disjoint_of_subset_left (a.subset_union_right b) d

theorem point_disjoint_finset_opens_of_t2 [T2Space α] {x : α} {s : Finset α} (h : x ∉ s) : Separated ({x} : Set α) s :=
  by 
    exactModCast finset_disjoint_finset_opens_of_t2 {x} s (finset.disjoint_singleton_left.mpr h)

end Separated

@[simp]
theorem nhds_eq_nhds_iff {a b : α} [T2Space α] : 𝓝 a = 𝓝 b ↔ a = b :=
  ⟨fun h =>
      eq_of_nhds_ne_bot$
        by 
          rw [h, inf_idem] <;> exact nhds_ne_bot,
    fun h => h ▸ rfl⟩

@[simp]
theorem nhds_le_nhds_iff {a b : α} [T2Space α] : 𝓝 a ≤ 𝓝 b ↔ a = b :=
  ⟨fun h =>
      eq_of_nhds_ne_bot$
        by 
          rw [inf_of_le_left h] <;> exact nhds_ne_bot,
    fun h => h ▸ le_reflₓ _⟩

theorem tendsto_nhds_unique [T2Space α] {f : β → α} {l : Filter β} {a b : α} [ne_bot l] (ha : tendsto f l (𝓝 a))
  (hb : tendsto f l (𝓝 b)) : a = b :=
  eq_of_nhds_ne_bot$ ne_bot_of_le$ le_inf ha hb

theorem tendsto_nhds_unique' [T2Space α] {f : β → α} {l : Filter β} {a b : α} (hl : ne_bot l) (ha : tendsto f l (𝓝 a))
  (hb : tendsto f l (𝓝 b)) : a = b :=
  eq_of_nhds_ne_bot$ ne_bot_of_le$ le_inf ha hb

theorem tendsto_nhds_unique_of_eventually_eq [T2Space α] {f g : β → α} {l : Filter β} {a b : α} [ne_bot l]
  (ha : tendsto f l (𝓝 a)) (hb : tendsto g l (𝓝 b)) (hfg : f =ᶠ[l] g) : a = b :=
  tendsto_nhds_unique (ha.congr' hfg) hb

theorem tendsto_const_nhds_iff [T2Space α] {l : Filter α} [ne_bot l] {c d : α} : tendsto (fun x => c) l (𝓝 d) ↔ c = d :=
  ⟨fun h => tendsto_nhds_unique tendsto_const_nhds h, fun h => h ▸ tendsto_const_nhds⟩

/-- A T₂.₅ space, also known as a Urysohn space, is a topological space
  where for every pair `x ≠ y`, there are two open sets, with the intersection of closures
  empty, one containing `x` and the other `y` . -/
class T25Space (α : Type u) [TopologicalSpace α] : Prop where 
  t2_5 : ∀ x y h : x ≠ y, ∃ U V : Set α, IsOpen U ∧ IsOpen V ∧ Closure U ∩ Closure V = ∅ ∧ x ∈ U ∧ y ∈ V

instance (priority := 100) T25Space.t2_space [T25Space α] : T2Space α :=
  ⟨fun x y hxy =>
      let ⟨U, V, hU, hV, hUV, hh⟩ := T25Space.t2_5 x y hxy
      ⟨U, V, hU, hV, hh.1, hh.2,
        subset_eq_empty (powerset_mono.mpr (closure_inter_subset_inter_closure U V) subset_closure) hUV⟩⟩

section limₓ

variable [T2Space α] {f : Filter α}

/-!
### Properties of `Lim` and `lim`

In this section we use explicit `nonempty α` instances for `Lim` and `lim`. This way the lemmas
are useful without a `nonempty α` instance.
-/


theorem Lim_eq {a : α} [ne_bot f] (h : f ≤ 𝓝 a) : @lim _ _ ⟨a⟩ f = a :=
  tendsto_nhds_unique (le_nhds_Lim ⟨a, h⟩) h

theorem Lim_eq_iff [ne_bot f] (h : ∃ a : α, f ≤ nhds a) {a} : @lim _ _ ⟨a⟩ f = a ↔ f ≤ 𝓝 a :=
  ⟨fun c => c ▸ le_nhds_Lim h, Lim_eq⟩

theorem Ultrafilter.Lim_eq_iff_le_nhds [CompactSpace α] {x : α} {F : Ultrafilter α} : F.Lim = x ↔ ↑F ≤ 𝓝 x :=
  ⟨fun h => h ▸ F.le_nhds_Lim, Lim_eq⟩

theorem is_open_iff_ultrafilter' [CompactSpace α] (U : Set α) : IsOpen U ↔ ∀ F : Ultrafilter α, F.Lim ∈ U → U ∈ F.1 :=
  by 
    rw [is_open_iff_ultrafilter]
    refine' ⟨fun h F hF => h F.Lim hF F F.le_nhds_Lim, _⟩
    intro cond x hx f h 
    rw [←Ultrafilter.Lim_eq_iff_le_nhds.2 h] at hx 
    exact cond _ hx

theorem Filter.Tendsto.lim_eq {a : α} {f : Filter β} [ne_bot f] {g : β → α} (h : tendsto g f (𝓝 a)) :
  @limₓ _ _ _ ⟨a⟩ f g = a :=
  Lim_eq h

theorem Filter.lim_eq_iff {f : Filter β} [ne_bot f] {g : β → α} (h : ∃ a, tendsto g f (𝓝 a)) {a} :
  @limₓ _ _ _ ⟨a⟩ f g = a ↔ tendsto g f (𝓝 a) :=
  ⟨fun c => c ▸ tendsto_nhds_lim h, Filter.Tendsto.lim_eq⟩

theorem Continuous.lim_eq [TopologicalSpace β] {f : β → α} (h : Continuous f) (a : β) :
  @limₓ _ _ _ ⟨f a⟩ (𝓝 a) f = f a :=
  (h.tendsto a).lim_eq

@[simp]
theorem Lim_nhds (a : α) : @lim _ _ ⟨a⟩ (𝓝 a) = a :=
  Lim_eq (le_reflₓ _)

@[simp]
theorem lim_nhds_id (a : α) : @limₓ _ _ _ ⟨a⟩ (𝓝 a) id = a :=
  Lim_nhds a

@[simp]
theorem Lim_nhds_within {a : α} {s : Set α} (h : a ∈ Closure s) : @lim _ _ ⟨a⟩ (𝓝[s] a) = a :=
  by 
    have  : ne_bot (𝓝[s] a) := mem_closure_iff_cluster_pt.1 h <;> exact Lim_eq inf_le_left

@[simp]
theorem lim_nhds_within_id {a : α} {s : Set α} (h : a ∈ Closure s) : @limₓ _ _ _ ⟨a⟩ (𝓝[s] a) id = a :=
  Lim_nhds_within h

end limₓ

/-!
### `t2_space` constructions

We use two lemmas to prove that various standard constructions generate Hausdorff spaces from
Hausdorff spaces:

* `separated_by_continuous` says that two points `x y : α` can be separated by open neighborhoods
  provided that there exists a continuous map `f : α → β` with a Hausdorff codomain such that
  `f x ≠ f y`. We use this lemma to prove that topological spaces defined using `induced` are
  Hausdorff spaces.

* `separated_by_open_embedding` says that for an open embedding `f : α → β` of a Hausdorff space
  `α`, the images of two distinct points `x y : α`, `x ≠ y` can be separated by open neighborhoods.
  We use this lemma to prove that topological spaces defined using `coinduced` are Hausdorff spaces.
-/


instance (priority := 100) t2_space_discrete {α : Type _} [TopologicalSpace α] [DiscreteTopology α] : T2Space α :=
  { t2 :=
      fun x y hxy =>
        ⟨{x}, {y}, is_open_discrete _, is_open_discrete _, rfl, rfl,
          eq_empty_iff_forall_not_mem.2$
            by 
              intro z hz <;> cases eq_of_mem_singleton hz.1 <;> cases eq_of_mem_singleton hz.2 <;> cc⟩ }

theorem separated_by_continuous {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
  {f : α → β} (hf : Continuous f) {x y : α} (h : f x ≠ f y) :
  ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f ⁻¹' u, f ⁻¹' v, uo.preimage hf, vo.preimage hf, xu, yv,
    by 
      rw [←preimage_inter, uv, preimage_empty]⟩

theorem separated_by_open_embedding {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] [T2Space α] {f : α → β}
  (hf : OpenEmbedding f) {x y : α} (h : x ≠ y) : ∃ u v : Set β, IsOpen u ∧ IsOpen v ∧ f x ∈ u ∧ f y ∈ v ∧ u ∩ v = ∅ :=
  let ⟨u, v, uo, vo, xu, yv, uv⟩ := t2_separation h
  ⟨f '' u, f '' v, hf.is_open_map _ uo, hf.is_open_map _ vo, mem_image_of_mem _ xu, mem_image_of_mem _ yv,
    by 
      rw [image_inter hf.inj, uv, image_empty]⟩

instance {α : Type _} {p : α → Prop} [t : TopologicalSpace α] [T2Space α] : T2Space (Subtype p) :=
  ⟨fun x y h => separated_by_continuous continuous_subtype_val (mt Subtype.eq h)⟩

instance {α : Type _} {β : Type _} [t₁ : TopologicalSpace α] [T2Space α] [t₂ : TopologicalSpace β] [T2Space β] :
  T2Space (α × β) :=
  ⟨fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h =>
      Or.elim (not_and_distrib.mp (mt Prod.ext_iff.mpr h)) (fun h₁ => separated_by_continuous continuous_fst h₁)
        fun h₂ => separated_by_continuous continuous_snd h₂⟩

theorem Embedding.t2_space [TopologicalSpace β] [T2Space β] {f : α → β} (hf : Embedding f) : T2Space α :=
  ⟨fun x y h => separated_by_continuous hf.continuous (hf.inj.ne h)⟩

instance {α : Type _} {β : Type _} [t₁ : TopologicalSpace α] [T2Space α] [t₂ : TopologicalSpace β] [T2Space β] :
  T2Space (Sum α β) :=
  by 
    constructor 
    rintro (x | x) (y | y) h
    ·
      replace h : x ≠ y := fun c => (c.subst h) rfl 
      exact separated_by_open_embedding open_embedding_inl h
    ·
      exact ⟨_, _, is_open_range_inl, is_open_range_inr, ⟨x, rfl⟩, ⟨y, rfl⟩, range_inl_inter_range_inr⟩
    ·
      exact ⟨_, _, is_open_range_inr, is_open_range_inl, ⟨x, rfl⟩, ⟨y, rfl⟩, range_inr_inter_range_inl⟩
    ·
      replace h : x ≠ y := fun c => (c.subst h) rfl 
      exact separated_by_open_embedding open_embedding_inr h

instance Pi.t2_space {α : Type _} {β : α → Type v} [t₂ : ∀ a, TopologicalSpace (β a)] [∀ a, T2Space (β a)] :
  T2Space (∀ a, β a) :=
  ⟨fun x y h =>
      let ⟨i, hi⟩ := not_forall.mp (mt funext h)
      separated_by_continuous (continuous_apply i) hi⟩

instance Sigma.t2_space {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] [∀ a, T2Space (α a)] :
  T2Space (Σ i, α i) :=
  by 
    constructor 
    rintro ⟨i, x⟩ ⟨j, y⟩ neq 
    rcases em (i = j) with (rfl | h)
    ·
      replace neq : x ≠ y := fun c => (c.subst neq) rfl 
      exact separated_by_open_embedding open_embedding_sigma_mk neq
    ·
      exact
        ⟨_, _, is_open_range_sigma_mk, is_open_range_sigma_mk, ⟨x, rfl⟩, ⟨y, rfl⟩,
          by 
            tidy⟩

variable [TopologicalSpace β]

theorem is_closed_eq [T2Space α] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
  IsClosed { x : β | f x = g x } :=
  continuous_iff_is_closed.mp (hf.prod_mk hg) _ is_closed_diagonal

/-- If two continuous maps are equal on `s`, then they are equal on the closure of `s`. -/
theorem Set.EqOn.closure [T2Space α] {s : Set β} {f g : β → α} (h : eq_on f g s) (hf : Continuous f)
  (hg : Continuous g) : eq_on f g (Closure s) :=
  closure_minimal h (is_closed_eq hf hg)

/-- If two continuous functions are equal on a dense set, then they are equal. -/
theorem Continuous.ext_on [T2Space α] {s : Set β} (hs : Dense s) {f g : β → α} (hf : Continuous f) (hg : Continuous g)
  (h : eq_on f g s) : f = g :=
  funext$ fun x => h.closure hf hg (hs x)

theorem Function.LeftInverse.closed_range [T2Space α] {f : α → β} {g : β → α} (h : Function.LeftInverse f g)
  (hf : Continuous f) (hg : Continuous g) : IsClosed (range g) :=
  have  : eq_on (g ∘ f) id (Closure$ range g) := h.right_inv_on_range.eq_on.closure (hg.comp hf) continuous_id 
  is_closed_of_closure_subset$
    fun x hx =>
      calc x = g (f x) := (this hx).symm 
        _ ∈ _ := mem_range_self _
        

theorem Function.LeftInverse.closed_embedding [T2Space α] {f : α → β} {g : β → α} (h : Function.LeftInverse f g)
  (hf : Continuous f) (hg : Continuous g) : ClosedEmbedding g :=
  ⟨h.embedding hf hg, h.closed_range hf hg⟩

theorem diagonal_eq_range_diagonal_map {α : Type _} : { p : α × α | p.1 = p.2 } = range fun x => (x, x) :=
  ext$
    fun p =>
      Iff.intro (fun h => ⟨p.1, Prod.ext_iff.2 ⟨rfl, h⟩⟩)
        fun ⟨x, hx⟩ =>
          show p.1 = p.2by 
            rw [←hx]

theorem prod_subset_compl_diagonal_iff_disjoint {α : Type _} {s t : Set α} :
  Set.Prod s t ⊆ { p : α × α | p.1 = p.2 }ᶜ ↔ s ∩ t = ∅ :=
  by 
    rw [eq_empty_iff_forall_not_mem, subset_compl_comm, diagonal_eq_range_diagonal_map, range_subset_iff] <;> simp 

theorem compact_compact_separated [T2Space α] {s t : Set α} (hs : IsCompact s) (ht : IsCompact t) (hst : s ∩ t = ∅) :
  ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅ :=
  by 
    simp only [prod_subset_compl_diagonal_iff_disjoint.symm] at hst⊢ <;>
      exact generalized_tube_lemma hs ht is_closed_diagonal.is_open_compl hst

/-- In a `t2_space`, every compact set is closed. -/
theorem IsCompact.is_closed [T2Space α] {s : Set α} (hs : IsCompact s) : IsClosed s :=
  is_open_compl_iff.1$
    is_open_iff_forall_mem_open.mpr$
      fun x hx =>
        let ⟨u, v, uo, vo, su, xv, uv⟩ :=
          compact_compact_separated hs (is_compact_singleton : IsCompact {x})
            (by 
              rwa [inter_comm, ←subset_compl_iff_disjoint, singleton_subset_iff])
        have  : v ⊆ sᶜ := subset_compl_comm.mp (subset.trans su (subset_compl_iff_disjoint.mpr uv))
        ⟨v, this, vo,
          by 
            simpa using xv⟩

@[simp]
theorem Filter.coclosed_compact_eq_cocompact [T2Space α] : coclosed_compact α = cocompact α :=
  by 
    simp [coclosed_compact, cocompact, infi_and', and_iff_right_of_imp IsCompact.is_closed]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » «expr⋂ , »((i), V i))
/-- If `V : ι → set α` is a decreasing family of compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. This is a version of `exists_subset_nhd_of_compact'` where we
don't need to assume each `V i` closed because it follows from compactness since `α` is
assumed to be Hausdorff. -/
theorem exists_subset_nhd_of_compact [T2Space α] {ι : Type _} [Nonempty ι] {V : ι → Set α} (hV : Directed (· ⊇ ·) V)
  (hV_cpct : ∀ i, IsCompact (V i)) {U : Set α} (hU : ∀ x _ : x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
  exists_subset_nhd_of_compact' hV hV_cpct (fun i => (hV_cpct i).IsClosed) hU

theorem CompactExhaustion.is_closed [T2Space α] (K : CompactExhaustion α) (n : ℕ) : IsClosed (K n) :=
  (K.is_compact n).IsClosed

theorem IsCompact.inter [T2Space α] {s t : Set α} (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∩ t) :=
  hs.inter_right$ ht.is_closed

theorem compact_closure_of_subset_compact [T2Space α] {s t : Set α} (ht : IsCompact t) (h : s ⊆ t) :
  IsCompact (Closure s) :=
  compact_of_is_closed_subset ht is_closed_closure (closure_minimal h ht.is_closed)

theorem image_closure_of_compact [T2Space β] {s : Set α} (hs : IsCompact (Closure s)) {f : α → β}
  (hf : ContinuousOn f (Closure s)) : f '' Closure s = Closure (f '' s) :=
  subset.antisymm hf.image_closure$
    closure_minimal (image_subset f subset_closure) (hs.image_of_continuous_on hf).IsClosed

/-- If a compact set is covered by two open sets, then we can cover it by two compact subsets. -/
theorem IsCompact.binary_compact_cover [T2Space α] {K U V : Set α} (hK : IsCompact K) (hU : IsOpen U) (hV : IsOpen V)
  (h2K : K ⊆ U ∪ V) : ∃ K₁ K₂ : Set α, IsCompact K₁ ∧ IsCompact K₂ ∧ K₁ ⊆ U ∧ K₂ ⊆ V ∧ K = K₁ ∪ K₂ :=
  by 
    rcases
      compact_compact_separated (hK.diff hU) (hK.diff hV)
        (by 
          rwa [diff_inter_diff, diff_eq_empty]) with
      ⟨O₁, O₂, h1O₁, h1O₂, h2O₁, h2O₂, hO⟩
    refine'
      ⟨_, _, hK.diff h1O₁, hK.diff h1O₂,
        by 
          rwa [diff_subset_comm],
        by 
          rwa [diff_subset_comm],
        by 
          rw [←diff_inter, hO, diff_empty]⟩

theorem Continuous.is_closed_map [CompactSpace α] [T2Space β] {f : α → β} (h : Continuous f) : IsClosedMap f :=
  fun s hs => (hs.is_compact.image h).IsClosed

theorem Continuous.closed_embedding [CompactSpace α] [T2Space β] {f : α → β} (h : Continuous f)
  (hf : Function.Injective f) : ClosedEmbedding f :=
  closed_embedding_of_continuous_injective_closed h hf h.is_closed_map

section 

open Finset Function

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr ∈ » t)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr ∈ » t)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr ∈ » t)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr ∈ » t)
/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
theorem IsCompact.finite_compact_cover [T2Space α] {s : Set α} (hs : IsCompact s) {ι} (t : Finset ι) (U : ι → Set α)
  (hU : ∀ i _ : i ∈ t, IsOpen (U i)) (hsC : s ⊆ ⋃ (i : _)(_ : i ∈ t), U i) :
  ∃ K : ι → Set α, (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U i) ∧ s = ⋃ (i : _)(_ : i ∈ t), K i :=
  by 
    classical 
    induction' t using Finset.induction with x t hx ih generalizing U hU s hs hsC
    ·
      refine' ⟨fun _ => ∅, fun i => is_compact_empty, fun i => empty_subset _, _⟩
      simpa only [subset_empty_iff, Union_false, Union_empty] using hsC 
    simp only [Finset.set_bUnion_insert] at hsC 
    simp only [Finset.mem_insert] at hU 
    have hU' : ∀ i _ : i ∈ t, IsOpen (U i) := fun i hi => hU i (Or.inr hi)
    rcases hs.binary_compact_cover (hU x (Or.inl rfl)) (is_open_bUnion hU') hsC with
      ⟨K₁, K₂, h1K₁, h1K₂, h2K₁, h2K₂, hK⟩
    rcases ih U hU' h1K₂ h2K₂ with ⟨K, h1K, h2K, h3K⟩
    refine' ⟨update K x K₁, _, _, _⟩
    ·
      intro i 
      byCases' hi : i = x
      ·
        simp only [update_same, hi, h1K₁]
      ·
        rw [←Ne.def] at hi 
        simp only [update_noteq hi, h1K]
    ·
      intro i 
      byCases' hi : i = x
      ·
        simp only [update_same, hi, h2K₁]
      ·
        rw [←Ne.def] at hi 
        simp only [update_noteq hi, h2K]
    ·
      simp only [set_bUnion_insert_update _ hx, hK, h3K]

end 

theorem locally_compact_of_compact_nhds [T2Space α] (h : ∀ x : α, ∃ s, s ∈ 𝓝 x ∧ IsCompact s) : LocallyCompactSpace α :=
  ⟨fun x n hn =>
      let ⟨u, un, uo, xu⟩ := mem_nhds_iff.mp hn 
      let ⟨k, kx, kc⟩ := h x 
      let ⟨v, w, vo, wo, xv, kuw, vw⟩ :=
        compact_compact_separated is_compact_singleton (IsCompact.diff kc uo)
          (by 
            rw [singleton_inter_eq_empty] <;> exact fun h => h.2 xu)
      have wn : wᶜ ∈ 𝓝 x := mem_nhds_iff.mpr ⟨v, subset_compl_iff_disjoint.mpr vw, vo, singleton_subset_iff.mp xv⟩
      ⟨k \ w, Filter.inter_mem kx wn, subset.trans (diff_subset_comm.mp kuw) un, kc.diff wo⟩⟩

instance (priority := 100) locally_compact_of_compact [T2Space α] [CompactSpace α] : LocallyCompactSpace α :=
  locally_compact_of_compact_nhds fun x => ⟨univ, is_open_univ.mem_nhds trivialₓ, compact_univ⟩

/-- In a locally compact T₂ space, every point has an open neighborhood with compact closure -/
theorem exists_open_with_compact_closure [LocallyCompactSpace α] [T2Space α] (x : α) :
  ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ IsCompact (Closure U) :=
  by 
    rcases exists_compact_mem_nhds x with ⟨K, hKc, hxK⟩
    rcases mem_nhds_iff.1 hxK with ⟨t, h1t, h2t, h3t⟩
    exact ⟨t, h2t, h3t, compact_closure_of_subset_compact hKc h1t⟩

end Separation

section Regularity

/-- A T₃ space, also known as a regular space (although this condition sometimes
  omits T₂), is one in which for every closed `C` and `x ∉ C`, there exist
  disjoint open sets containing `x` and `C` respectively. -/
class RegularSpace (α : Type u) [TopologicalSpace α] extends T0Space α : Prop where 
  regular : ∀ {s : Set α} {a}, IsClosed s → a ∉ s → ∃ t, IsOpen t ∧ s ⊆ t ∧ 𝓝[t] a = ⊥

instance (priority := 100) RegularSpace.t1_space [RegularSpace α] : T1Space α :=
  by 
    rw [t1_iff_exists_open]
    intro x y hxy 
    obtain ⟨U, hU, h⟩ := T0Space.t0 x y hxy 
    cases h
    ·
      exact ⟨U, hU, h⟩
    ·
      obtain ⟨R, hR, hh⟩ := RegularSpace.regular (is_closed_compl_iff.mpr hU) (not_not.mpr h.1)
      obtain ⟨V, hV, hhh⟩ := mem_nhds_iff.1 (Filter.inf_principal_eq_bot.1 hh.2)
      exact ⟨R, hR, hh.1 (mem_compl h.2), hV hhh.2⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » expr𝓝() a)
theorem nhds_is_closed [RegularSpace α] {a : α} {s : Set α} (h : s ∈ 𝓝 a) :
  ∃ (t : _)(_ : t ∈ 𝓝 a), t ⊆ s ∧ IsClosed t :=
  let ⟨s', h₁, h₂, h₃⟩ := mem_nhds_iff.mp h 
  have  : ∃ t, IsOpen t ∧ s'ᶜ ⊆ t ∧ 𝓝[t] a = ⊥ := RegularSpace.regular h₂.is_closed_compl (not_not_intro h₃)
  let ⟨t, ht₁, ht₂, ht₃⟩ := this
  ⟨tᶜ,
    mem_of_eq_bot$
      by 
        rwa [compl_compl],
    subset.trans (compl_subset_comm.1 ht₂) h₁, is_closed_compl_iff.mpr ht₁⟩

theorem closed_nhds_basis [RegularSpace α] (a : α) : (𝓝 a).HasBasis (fun s : Set α => s ∈ 𝓝 a ∧ IsClosed s) id :=
  ⟨fun t =>
      ⟨fun t_in =>
          let ⟨s, s_in, h_st, h⟩ := nhds_is_closed t_in
          ⟨s, ⟨s_in, h⟩, h_st⟩,
        fun ⟨s, ⟨s_in, hs⟩, hst⟩ => mem_of_superset s_in hst⟩⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (t «expr ∈ » B)
theorem TopologicalSpace.IsTopologicalBasis.exists_closure_subset [RegularSpace α] {B : Set (Set α)}
  (hB : TopologicalSpace.IsTopologicalBasis B) {a : α} {s : Set α} (h : s ∈ 𝓝 a) :
  ∃ (t : _)(_ : t ∈ B), a ∈ t ∧ Closure t ⊆ s :=
  by 
    rcases nhds_is_closed h with ⟨t, hat, hts, htc⟩
    rcases hB.mem_nhds_iff.1 hat with ⟨u, huB, hau, hut⟩
    exact ⟨u, huB, hau, (closure_minimal hut htc).trans hts⟩

theorem TopologicalSpace.IsTopologicalBasis.nhds_basis_closure [RegularSpace α] {B : Set (Set α)}
  (hB : TopologicalSpace.IsTopologicalBasis B) (a : α) : (𝓝 a).HasBasis (fun s : Set α => a ∈ s ∧ s ∈ B) Closure :=
  ⟨fun s =>
      ⟨fun h =>
          let ⟨t, htB, hat, hts⟩ := hB.exists_closure_subset h
          ⟨t, ⟨hat, htB⟩, hts⟩,
        fun ⟨t, ⟨hat, htB⟩, hts⟩ => mem_of_superset (hB.mem_nhds htB hat) (subset_closure.trans hts)⟩⟩

instance Subtype.regular_space [RegularSpace α] {p : α → Prop} : RegularSpace (Subtype p) :=
  ⟨by 
      intro s a hs ha 
      rcases is_closed_induced_iff.1 hs with ⟨s, hs', rfl⟩
      rcases RegularSpace.regular hs' ha with ⟨t, ht, hst, hat⟩
      refine' ⟨coeₓ ⁻¹' t, is_open_induced ht, preimage_mono hst, _⟩
      rw [nhdsWithin, nhds_induced, ←comap_principal, ←comap_inf, ←nhdsWithin, hat, comap_bot]⟩

variable (α)

instance (priority := 100) RegularSpace.t2_space [RegularSpace α] : T2Space α :=
  ⟨fun x y hxy =>
      let ⟨s, hs, hys, hxs⟩ := RegularSpace.regular is_closed_singleton (mt mem_singleton_iff.1 hxy)
      let ⟨t, hxt, u, hsu, htu⟩ := empty_mem_iff_bot.2 hxs 
      let ⟨v, hvt, hv, hxv⟩ := mem_nhds_iff.1 hxt
      ⟨v, s, hv, hs, hxv, singleton_subset_iff.1 hys,
        eq_empty_of_subset_empty$
          fun z ⟨hzv, hzs⟩ =>
            by 
              rw [htu]
              exact ⟨hvt hzv, hsu hzs⟩⟩⟩

instance (priority := 100) RegularSpace.t2_5_space [RegularSpace α] : T25Space α :=
  ⟨fun x y hxy =>
      let ⟨U, V, hU, hV, hh_1, hh_2, hUV⟩ := T2Space.t2 x y hxy 
      let hxcV := not_not.mpr ((interior_maximal (subset_compl_iff_disjoint.mpr hUV) hU) hh_1)
      let ⟨R, hR, hh⟩ :=
        RegularSpace.regular is_closed_closure
          (by 
            rwa [closure_eq_compl_interior_compl])
      let ⟨A, hA, hhh⟩ := mem_nhds_iff.1 (Filter.inf_principal_eq_bot.1 hh.2)
      ⟨A, V, hhh.1, hV,
        subset_eq_empty
          ((Closure V).inter_subset_inter_left
            (subset.trans (closure_minimal hA (is_closed_compl_iff.mpr hR)) (compl_subset_compl.mpr hh.1)))
          (compl_inter_self (Closure V)),
        hhh.2, hh_2⟩⟩

variable {α}

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (U₁ V₁ «expr ∈ » expr𝓝() x)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (U₂ V₂ «expr ∈ » expr𝓝() y)
/-- Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆ U₂`,
with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint. -/
theorem disjoint_nested_nhds [RegularSpace α] {x y : α} (h : x ≠ y) :
  ∃ (U₁ V₁ : _)(_ : U₁ ∈ 𝓝 x)(_ : V₁ ∈ 𝓝 x)(U₂ V₂ : _)(_ : U₂ ∈ 𝓝 y)(_ : V₂ ∈ 𝓝 y),
    IsClosed V₁ ∧ IsClosed V₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ U₁ ∩ U₂ = ∅ :=
  by 
    rcases t2_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩
    rcases nhds_is_closed (IsOpen.mem_nhds U₁_op x_in) with ⟨V₁, V₁_in, h₁, V₁_closed⟩
    rcases nhds_is_closed (IsOpen.mem_nhds U₂_op y_in) with ⟨V₂, V₂_in, h₂, V₂_closed⟩
    use U₁, V₁, mem_of_superset V₁_in h₁, V₁_in, U₂, V₂, mem_of_superset V₂_in h₂, V₂_in 
    tauto

end Regularity

section Normality

/-- A T₄ space, also known as a normal space (although this condition sometimes
  omits T₂), is one in which for every pair of disjoint closed sets `C` and `D`,
  there exist disjoint open sets containing `C` and `D` respectively. -/
class NormalSpace (α : Type u) [TopologicalSpace α] extends T1Space α : Prop where 
  normal :
  ∀ s t : Set α, IsClosed s → IsClosed t → Disjoint s t → ∃ u v, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v

theorem normal_separation [NormalSpace α] {s t : Set α} (H1 : IsClosed s) (H2 : IsClosed t) (H3 : Disjoint s t) :
  ∃ u v, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v :=
  NormalSpace.normal s t H1 H2 H3

theorem normal_exists_closure_subset [NormalSpace α] {s t : Set α} (hs : IsClosed s) (ht : IsOpen t) (hst : s ⊆ t) :
  ∃ u, IsOpen u ∧ s ⊆ u ∧ Closure u ⊆ t :=
  by 
    have  : Disjoint s (tᶜ)
    exact fun x ⟨hxs, hxt⟩ => hxt (hst hxs)
    rcases normal_separation hs (is_closed_compl_iff.2 ht) this with ⟨s', t', hs', ht', hss', htt', hs't'⟩
    refine' ⟨s', hs', hss', subset.trans (closure_minimal _ (is_closed_compl_iff.2 ht')) (compl_subset_comm.1 htt')⟩
    exact fun x hxs hxt => hs't' ⟨hxs, hxt⟩

instance (priority := 100) NormalSpace.regular_space [NormalSpace α] : RegularSpace α :=
  { regular :=
      fun s x hs hxs =>
        let ⟨u, v, hu, hv, hsu, hxv, huv⟩ :=
          normal_separation hs is_closed_singleton
            fun _ ⟨hx, hy⟩ => hxs$ mem_of_eq_of_mem (eq_of_mem_singleton hy).symm hx
        ⟨u, hu, hsu,
          Filter.empty_mem_iff_bot.1$
            Filter.mem_inf_iff.2
              ⟨v, IsOpen.mem_nhds hv (singleton_subset_iff.1 hxv), u, Filter.mem_principal_self u,
                by 
                  rwa [eq_comm, inter_comm, ←disjoint_iff_inter_eq_empty]⟩⟩ }

theorem normal_of_compact_t2 [CompactSpace α] [T2Space α] : NormalSpace α :=
  by 
    refine' ⟨fun s t hs ht st => _⟩
    simp only [disjoint_iff]
    exact compact_compact_separated hs.is_compact ht.is_compact st.eq_bot

open TopologicalSpace

variable (α)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (u «expr ∈ » U)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (u «expr ∈ » U)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (u «expr ∈ » U)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (U «expr ∈ » countable_basis α)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (u «expr ∈ » U)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (v «expr ∈ » V)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (v «expr ∈ » V)
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (u «expr ∈ » U)
/-- A regular topological space with second countable topology is a normal space.
This lemma is not an instance to avoid a loop. -/
theorem normal_space_of_regular_second_countable [second_countable_topology α] [RegularSpace α] : NormalSpace α :=
  by 
    have key :
      ∀ {s t : Set α},
        IsClosed t →
          Disjoint s t →
            ∃ U : Set (countable_basis α),
              (s ⊆ ⋃ (u : _)(_ : u ∈ U), ↑u) ∧
                (∀ u _ : u ∈ U, Disjoint (Closure (↑u)) t) ∧
                  ∀ n : ℕ, IsClosed (⋃ (u : _)(_ : u ∈ U)(h : Encodable.encode u ≤ n), Closure (u : Set α))
    ·
      intro s t hc hd 
      rw [disjoint_left] at hd 
      have  : ∀ x _ : x ∈ s, ∃ (U : _)(_ : U ∈ countable_basis α), x ∈ U ∧ Disjoint (Closure U) t
      ·
        intro x hx 
        rcases(is_basis_countable_basis α).exists_closure_subset (hc.is_open_compl.mem_nhds (hd hx)) with
          ⟨u, hu, hxu, hut⟩
        exact ⟨u, hu, hxu, disjoint_left.2 hut⟩
      choose! U hu hxu hd 
      set V : s → countable_basis α := maps_to.restrict _ _ _ hu 
      refine' ⟨range V, _, forall_range_iff.2$ Subtype.forall.2 hd, fun n => _⟩
      ·
        rw [bUnion_range]
        exact fun x hx => mem_Union.2 ⟨⟨x, hx⟩, hxu x hx⟩
      ·
        simp only [←supr_eq_Union, supr_and']
        exact
          is_closed_bUnion (((finite_le_nat n).preimage_embedding (Encodable.encode' _)).Subset$ inter_subset_right _ _)
            fun u hu => is_closed_closure 
    refine' ⟨fun s t hs ht hd => _⟩
    rcases key ht hd with ⟨U, hsU, hUd, hUc⟩
    rcases key hs hd.symm with ⟨V, htV, hVd, hVc⟩
    refine'
      ⟨⋃ (u : _)(_ : u ∈ U), ↑u \ ⋃ (v : _)(_ : v ∈ V)(hv : Encodable.encode v ≤ Encodable.encode u), Closure (↑v),
        ⋃ (v : _)(_ : v ∈ V), ↑v \ ⋃ (u : _)(_ : u ∈ U)(hu : Encodable.encode u ≤ Encodable.encode v), Closure (↑u),
        is_open_bUnion$ fun u hu => (is_open_of_mem_countable_basis u.2).sdiff (hVc _),
        is_open_bUnion$ fun v hv => (is_open_of_mem_countable_basis v.2).sdiff (hUc _), fun x hx => _, fun x hx => _, _⟩
    ·
      rcases mem_bUnion_iff.1 (hsU hx) with ⟨u, huU, hxu⟩
      refine' mem_bUnion huU ⟨hxu, _⟩
      simp only [mem_Union]
      rintro ⟨v, hvV, -, hxv⟩
      exact hVd v hvV ⟨hxv, hx⟩
    ·
      rcases mem_bUnion_iff.1 (htV hx) with ⟨v, hvV, hxv⟩
      refine' mem_bUnion hvV ⟨hxv, _⟩
      simp only [mem_Union]
      rintro ⟨u, huU, -, hxu⟩
      exact hUd u huU ⟨hxu, hx⟩
    ·
      simp only [disjoint_left, mem_Union, mem_diff, not_exists, not_and, not_forall, not_not]
      rintro a ⟨u, huU, hau, haV⟩ v hvV hav 
      cases' le_totalₓ (Encodable.encode u) (Encodable.encode v) with hle hle 
      exacts[⟨u, huU, hle, subset_closure hau⟩, (haV _ hvV hle$ subset_closure hav).elim]

end Normality

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (U «expr ∈ » Zi)
/-- In a compact t2 space, the connected component of a point equals the intersection of all
its clopen neighbourhoods. -/
theorem connected_component_eq_Inter_clopen [T2Space α] [CompactSpace α] {x : α} :
  ConnectedComponent x = ⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z :=
  by 
    apply eq_of_subset_of_subset connected_component_subset_Inter_clopen 
    refine' IsPreconnected.subset_connected_component _ (mem_Inter.2 fun Z => Z.2.2)
    have hs : @IsClosed _ _inst_1 (⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z) := is_closed_Inter fun Z => Z.2.1.2
    rw [is_preconnected_iff_subset_of_fully_disjoint_closed hs]
    intro a b ha hb hab ab_empty 
    have  := @normal_of_compact_t2 α _ _ _ 
    rcases normal_separation ha hb (disjoint_iff.2 ab_empty) with ⟨u, v, hu, hv, hau, hbv, huv⟩
    suffices  : ∃ Z : Set α, IsClopen Z ∧ x ∈ Z ∧ Z ⊆ u ∪ v
    ·
      cases' this with Z H 
      rw [disjoint_iff_inter_eq_empty] at huv 
      have H1 := is_clopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hu hv huv 
      rw [union_comm] at H 
      have H2 := is_clopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hv hu (inter_comm u v ▸ huv)
      byCases' x ∈ u
      ·
        left 
        suffices  : (⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, ↑Z) ⊆ u
        ·
          rw [←Set.disjoint_iff_inter_eq_empty] at huv 
          replace hab : (⋂ Z : { Z // IsClopen Z ∧ x ∈ Z }, ↑Z) ≤ a ∪ b := hab 
          replace this : (⋂ Z : { Z // IsClopen Z ∧ x ∈ Z }, ↑Z) ≤ u := this 
          exact Disjoint.left_le_of_le_sup_right hab (huv.mono this hbv)
        ·
          apply subset.trans _ (inter_subset_right Z u)
          apply Inter_subset (fun Z : { Z : Set α // IsClopen Z ∧ x ∈ Z } => ↑Z) ⟨Z ∩ u, H1, mem_inter H.2.1 h⟩
      have h1 : x ∈ v
      ·
        cases'
          (mem_union x u v).1
            (mem_of_subset_of_mem (subset.trans hab (union_subset_union hau hbv)) (mem_Inter.2 fun i => i.2.2)) with
          h1 h1
        ·
          exfalso 
          exact h h1
        ·
          exact h1 
      right 
      suffices  : (⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, ↑Z) ⊆ v
      ·
        rw [inter_comm, ←Set.disjoint_iff_inter_eq_empty] at huv 
        replace hab : (⋂ Z : { Z // IsClopen Z ∧ x ∈ Z }, ↑Z) ≤ a ∪ b := hab 
        replace this : (⋂ Z : { Z // IsClopen Z ∧ x ∈ Z }, ↑Z) ≤ v := this 
        exact Disjoint.left_le_of_le_sup_left hab (huv.mono this hau)
      ·
        apply subset.trans _ (inter_subset_right Z v)
        apply Inter_subset (fun Z : { Z : Set α // IsClopen Z ∧ x ∈ Z } => ↑Z) ⟨Z ∩ v, H2, mem_inter H.2.1 h1⟩
    have H1 :=
      (is_closed_compl_iff.2 (hu.union hv)).IsCompact.inter_Inter_nonempty
        (fun Z : { Z : Set α // IsClopen Z ∧ x ∈ Z } => Z) fun Z => Z.2.1.2
    rw [←not_imp_not, not_forall, not_nonempty_iff_eq_empty, inter_comm] at H1 
    have huv_union := subset.trans hab (union_subset_union hau hbv)
    rw [←compl_compl (u ∪ v), subset_compl_iff_disjoint] at huv_union 
    cases' H1 huv_union with Zi H2 
    refine' ⟨⋂ (U : _)(_ : U ∈ Zi), Subtype.val U, _, _, _⟩
    ·
      exact is_clopen_bInter fun Z hZ => Z.2.1
    ·
      exact mem_bInter_iff.2 fun Z hZ => Z.2.2
    ·
      rwa [not_nonempty_iff_eq_empty, inter_comm, ←subset_compl_iff_disjoint, compl_compl] at H2

section Profinite

open TopologicalSpace

variable [T2Space α]

/-- A Hausdorff space with a clopen basis is totally separated. -/
theorem tot_sep_of_zero_dim (h : is_topological_basis { s : Set α | IsClopen s }) : TotallySeparatedSpace α :=
  by 
    constructor 
    rintro x - y - hxy 
    obtain ⟨u, v, hu, hv, xu, yv, disj⟩ := t2_separation hxy 
    obtain ⟨w, hw : IsClopen w, xw, wu⟩ := (is_topological_basis.mem_nhds_iff h).1 (IsOpen.mem_nhds hu xu)
    refine' ⟨w, wᶜ, hw.1, (is_clopen_compl_iff.2 hw).1, xw, _, _, Set.inter_compl_self w⟩
    ·
      intro h 
      have  : y ∈ u ∩ v := ⟨wu h, yv⟩
      rwa [disj] at this 
    rw [Set.union_compl_self]

variable [CompactSpace α]

/-- A compact Hausdorff space is totally disconnected if and only if it is totally separated, this
  is also true for locally compact spaces. -/
theorem compact_t2_tot_disc_iff_tot_sep : TotallyDisconnectedSpace α ↔ TotallySeparatedSpace α :=
  by 
    constructor
    ·
      intro h 
      constructor 
      rintro x - y -
      contrapose! 
      intro hyp 
      suffices  : x ∈ ConnectedComponent y
      ·
        simpa [totally_disconnected_space_iff_connected_component_singleton.1 h y, mem_singleton_iff]
      rw [connected_component_eq_Inter_clopen, mem_Inter]
      rintro ⟨w : Set α, hw : IsClopen w, hy : y ∈ w⟩
      byContra hx 
      simpa using hyp (wᶜ) w (is_open_compl_iff.mpr hw.2) hw.1 hx hy 
    apply TotallySeparatedSpace.totally_disconnected_space

variable [TotallyDisconnectedSpace α]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » «expr⋂ , »((Z : N), Z.val))
theorem nhds_basis_clopen (x : α) : (𝓝 x).HasBasis (fun s : Set α => x ∈ s ∧ IsClopen s) id :=
  ⟨fun U =>
      by 
        constructor
        ·
          have  : ConnectedComponent x = {x}
          exact totally_disconnected_space_iff_connected_component_singleton.mp ‹_› x 
          rw [connected_component_eq_Inter_clopen] at this 
          intro hU 
          let N := { Z // IsClopen Z ∧ x ∈ Z }
          suffices  : ∃ Z : N, Z.val ⊆ U
          ·
            rcases this with ⟨⟨s, hs, hs'⟩, hs''⟩
            exact ⟨s, ⟨hs', hs⟩, hs''⟩
          have  : Nonempty N := ⟨⟨univ, is_clopen_univ, mem_univ x⟩⟩
          have hNcl : ∀ Z : N, IsClosed Z.val := fun Z => Z.property.1.2
          have hdir : Directed Superset fun Z : N => Z.val
          ·
            rintro ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩
            exact ⟨⟨s ∩ t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left s t, inter_subset_right s t⟩
          have h_nhd : ∀ y _ : y ∈ ⋂ Z : N, Z.val, U ∈ 𝓝 y
          ·
            intro y y_in 
            erw [this, mem_singleton_iff] at y_in 
            rwa [y_in]
          exact exists_subset_nhd_of_compact_space hdir hNcl h_nhd
        ·
          rintro ⟨V, ⟨hxV, V_op, -⟩, hUV : V ⊆ U⟩
          rw [mem_nhds_iff]
          exact ⟨V, hUV, V_op, hxV⟩⟩

theorem is_topological_basis_clopen : is_topological_basis { s : Set α | IsClopen s } :=
  by 
    apply is_topological_basis_of_open_of_nhds fun U hU : IsClopen U => hU.1
    intro x U hxU U_op 
    have  : U ∈ 𝓝 x 
    exact IsOpen.mem_nhds U_op hxU 
    rcases(nhds_basis_clopen x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V ⊆ U⟩
    use V 
    tauto

/-- Every member of an open set in a compact Hausdorff totally disconnected space
  is contained in a clopen set contained in the open set.  -/
theorem compact_exists_clopen_in_open {x : α} {U : Set α} (is_open : IsOpen U) (memU : x ∈ U) :
  ∃ (V : Set α)(hV : IsClopen V), x ∈ V ∧ V ⊆ U :=
  (is_topological_basis.mem_nhds_iff is_topological_basis_clopen).1 (IsOpen.mem_nhds memU)

end Profinite

section LocallyCompact

open TopologicalSpace

variable {H : Type _} [TopologicalSpace H] [LocallyCompactSpace H] [T2Space H]

/-- A locally compact Hausdorff totally disconnected space has a basis with clopen elements. -/
theorem loc_compact_Haus_tot_disc_of_zero_dim [TotallyDisconnectedSpace H] :
  is_topological_basis { s : Set H | IsClopen s } :=
  by 
    refine' is_topological_basis_of_open_of_nhds (fun u hu => hu.1) _ 
    rintro x U memU hU 
    obtain ⟨s, comp, xs, sU⟩ := exists_compact_subset hU memU 
    obtain ⟨t, h, ht, xt⟩ := mem_interior.1 xs 
    let u : Set s := (coeₓ : s → H) ⁻¹' Interior s 
    have u_open_in_s : IsOpen u := is_open_interior.preimage continuous_subtype_coe 
    let X : s := ⟨x, h xt⟩
    have Xu : X ∈ u := xs 
    have  : CompactSpace s := is_compact_iff_compact_space.1 comp 
    obtain ⟨V : Set s, clopen_in_s, Vx, V_sub⟩ := compact_exists_clopen_in_open u_open_in_s Xu 
    have V_clopen : IsClopen ((coeₓ : s → H) '' V)
    ·
      refine' ⟨_, comp.is_closed.closed_embedding_subtype_coe.closed_iff_image_closed.1 clopen_in_s.2⟩
      let v : Set u := (coeₓ : u → s) ⁻¹' V 
      have  : (coeₓ : u → H) = ((coeₓ : s → H) ∘ (coeₓ : u → s)) := rfl 
      have f0 : Embedding (coeₓ : u → H) := embedding_subtype_coe.comp embedding_subtype_coe 
      have f1 : OpenEmbedding (coeₓ : u → H)
      ·
        refine' ⟨f0, _⟩
        ·
          have  : Set.Range (coeₓ : u → H) = Interior s
          ·
            rw [this, Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe]
            apply Set.inter_eq_self_of_subset_left interior_subset 
          rw [this]
          apply is_open_interior 
      have f2 : IsOpen v := clopen_in_s.1.Preimage continuous_subtype_coe 
      have f3 : (coeₓ : s → H) '' V = (coeₓ : u → H) '' v
      ·
        rw [this, image_comp coeₓ coeₓ, Subtype.image_preimage_coe, inter_eq_self_of_subset_left V_sub]
      rw [f3]
      apply f1.is_open_map v f2 
    refine'
      ⟨coeₓ '' V, V_clopen,
        by 
          simp [Vx, h xt],
        _⟩
    trans s
    ·
      simp 
    assumption

/-- A locally compact Hausdorff space is totally disconnected
  if and only if it is totally separated. -/
theorem loc_compact_t2_tot_disc_iff_tot_sep : TotallyDisconnectedSpace H ↔ TotallySeparatedSpace H :=
  by 
    constructor
    ·
      intro h 
      exact tot_sep_of_zero_dim loc_compact_Haus_tot_disc_of_zero_dim 
    apply TotallySeparatedSpace.totally_disconnected_space

end LocallyCompact

section connectedComponentSetoid

attribute [local instance] connectedComponentSetoid

/-- `connected_components α` is Hausdorff when `α` is Hausdorff and compact -/
instance ConnectedComponents.t2 [T2Space α] [CompactSpace α] : T2Space (ConnectedComponents α) :=
  by 
    refine' ⟨fun x y => Quotientₓ.induction_on x (Quotientₓ.induction_on y fun a b ne => _)⟩
    rw [connected_component_nrel_iff] at ne 
    have h := connected_component_disjoint Ne 
    rw [connected_component_eq_Inter_clopen, disjoint_iff_inter_eq_empty, inter_comm] at h 
    cases' is_closed_connected_component.is_compact.elim_finite_subfamily_closed _ _ h with fin_a ha 
    swap
    ·
      exact fun Z => Z.2.1.2
    set U : Set α := ⋂ (i : { Z // IsClopen Z ∧ b ∈ Z })(H : i ∈ fin_a), i with hU 
    rw [←hU] at ha 
    have hu_clopen : IsClopen U := is_clopen_bInter fun i j => i.2.1
    use Quotientₓ.mk '' U, Quotientₓ.mk '' Uᶜ
    have hu : Quotientₓ.mk ⁻¹' (Quotientₓ.mk '' U) = U :=
      (connected_components_preimage_image U ▸ Eq.symm) hu_clopen.eq_union_connected_components 
    have huc : Quotientₓ.mk ⁻¹' (Quotientₓ.mk '' Uᶜ) = Uᶜ :=
      (connected_components_preimage_image (Uᶜ) ▸ Eq.symm) (IsClopen.compl hu_clopen).eq_union_connected_components 
    refine' ⟨_, _, _, _, _⟩
    ·
      rw [(quotient_map_iff.1 quotient_map_quotient_mk).2 _, hu]
      exact hu_clopen.1
    ·
      rw [(quotient_map_iff.1 quotient_map_quotient_mk).2 _, huc]
      exact is_open_compl_iff.2 hu_clopen.2
    ·
      exact mem_image_of_mem _ (mem_Inter.2 fun Z => mem_Inter.2 fun Zmem => Z.2.2)
    ·
      apply mem_image_of_mem 
      exact mem_of_subset_of_mem (subset_compl_iff_disjoint.2 ha) (@mem_connected_component _ _ a)
    apply preimage_injective.2 (@surjective_quotient_mk _ _)
    rw [preimage_inter, preimage_empty, hu, huc, inter_compl_self _]

end connectedComponentSetoid

