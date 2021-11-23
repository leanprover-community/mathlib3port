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

variable{α : Type u}{β : Type v}[TopologicalSpace α]

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
class T0Space(α : Type u)[TopologicalSpace α] : Prop where 
  t0 : ∀ x y, x ≠ y → ∃ U : Set α, IsOpen U ∧ Xorₓ (x ∈ U) (y ∈ U)

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a closed set `S` in a compact T₀ space,
there is some `x ∈ S` such that `{x}` is closed. -/
theorem is_closed.exists_closed_singleton
{α : Type*}
[topological_space α]
[t0_space α]
[compact_space α]
{S : set α}
(hS : is_closed S)
(hne : S.nonempty) : «expr∃ , »((x : α), «expr ∧ »(«expr ∈ »(x, S), is_closed ({x} : set α))) :=
begin
  obtain ["⟨", ident V, ",", ident Vsub, ",", ident Vne, ",", ident Vcls, ",", ident hV, "⟩", ":=", expr hS.exists_minimal_nonempty_closed_subset hne],
  by_cases [expr hnt, ":", expr «expr∃ , »((x y : α) (hx : «expr ∈ »(x, V)) (hy : «expr ∈ »(y, V)), «expr ≠ »(x, y))],
  { exfalso,
    obtain ["⟨", ident x, ",", ident y, ",", ident hx, ",", ident hy, ",", ident hne, "⟩", ":=", expr hnt],
    obtain ["⟨", ident U, ",", ident hU, ",", ident hsep, "⟩", ":=", expr t0_space.t0 _ _ hne],
    have [] [":", expr ∀
     (z w : α)
     (hz : «expr ∈ »(z, V))
     (hw : «expr ∈ »(w, V))
     (hz' : «expr ∈ »(z, U))
     (hw' : «expr¬ »(«expr ∈ »(w, U))), false] [],
    { intros [ident z, ident w, ident hz, ident hw, ident hz', ident hw'],
      have [ident uvne] [":", expr «expr ∩ »(V, «expr ᶜ»(U)).nonempty] [],
      { use [expr w],
        simp [] [] ["only"] ["[", expr hw, ",", expr hw', ",", expr set.mem_inter_eq, ",", expr not_false_iff, ",", expr and_self, ",", expr set.mem_compl_eq, "]"] [] [] },
      specialize [expr hV «expr ∩ »(V, «expr ᶜ»(U)) (set.inter_subset_left _ _) uvne (is_closed.inter Vcls (is_closed_compl_iff.mpr hU))],
      have [] [":", expr «expr ⊆ »(V, «expr ᶜ»(U))] [],
      { rw ["<-", expr hV] [],
        exact [expr set.inter_subset_right _ _] },
      exact [expr this hz hz'] },
    cases [expr hsep] [],
    { exact [expr this x y hx hy hsep.1 hsep.2] },
    { exact [expr this y x hy hx hsep.1 hsep.2] } },
  { push_neg ["at", ident hnt],
    obtain ["⟨", ident z, ",", ident hz, "⟩", ":=", expr Vne],
    refine [expr ⟨z, Vsub hz, _⟩],
    convert [] [expr Vcls] [],
    ext [] [] [],
    simp [] [] ["only"] ["[", expr set.mem_singleton_iff, ",", expr set.mem_compl_eq, "]"] [] [],
    split,
    { rintro [ident rfl],
      exact [expr hz] },
    { exact [expr λ hx, hnt x z hx hz] } }
end

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given an open `finset` `S` in a T₀ space, there is some `x ∈ S` such that `{x}` is open. -/
theorem exists_open_singleton_of_open_finset
[t0_space α]
(s : finset α)
(sne : s.nonempty)
(hso : is_open (s : set α)) : «expr∃ , »((x «expr ∈ » s), is_open ({x} : set α)) :=
begin
  induction [expr s] ["using", ident finset.strong_induction_on] ["with", ident s, ident ihs] [],
  by_cases [expr hs, ":", expr set.subsingleton (s : set α)],
  { rcases [expr sne, "with", "⟨", ident x, ",", ident hx, "⟩"],
    refine [expr ⟨x, hx, _⟩],
    have [] [":", expr «expr = »((s : set α), {x})] [],
    from [expr hs.eq_singleton_of_mem hx],
    rwa [expr this] ["at", ident hso] },
  { dunfold [ident set.subsingleton] ["at", ident hs],
    push_neg ["at", ident hs],
    rcases [expr hs, "with", "⟨", ident x, ",", ident hx, ",", ident y, ",", ident hy, ",", ident hxy, "⟩"],
    rcases [expr t0_space.t0 x y hxy, "with", "⟨", ident U, ",", ident hU, ",", ident hxyU, "⟩"],
    wlog [ident H] [":", expr «expr ∧ »(«expr ∈ »(x, U), «expr ∉ »(y, U))] [":=", expr hxyU] ["using", "[", ident x, ident y, ",", ident y, ident x, "]"],
    obtain ["⟨", ident z, ",", ident hzs, ",", ident hz, "⟩", ":", expr «expr∃ , »((z «expr ∈ » s.filter (λ
        z, «expr ∈ »(z, U))), is_open ({z} : set α))],
    { refine [expr ihs _ (finset.filter_ssubset.2 ⟨y, hy, H.2⟩) ⟨x, finset.mem_filter.2 ⟨hx, H.1⟩⟩ _],
      rw ["[", expr finset.coe_filter, "]"] [],
      exact [expr is_open.inter hso hU] },
    exact [expr ⟨z, (finset.mem_filter.1 hzs).1, hz⟩] }
end

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_open_singleton_of_fintype
[t0_space α]
[f : fintype α]
[ha : nonempty α] : «expr∃ , »((x : α), is_open ({x} : set α)) :=
begin
  refine [expr ha.elim (λ x, _)],
  have [] [":", expr is_open ((finset.univ : finset α) : set α)] [],
  { simp [] [] [] [] [] [] },
  rcases [expr exists_open_singleton_of_open_finset _ ⟨x, finset.mem_univ x⟩ this, "with", "⟨", ident x, ",", "_", ",", ident hx, "⟩"],
  exact [expr ⟨x, hx⟩]
end

instance Subtype.t0_space [T0Space α] {p : α → Prop} : T0Space (Subtype p) :=
  ⟨fun x y hxy =>
      let ⟨U, hU, hxyU⟩ := T0Space.t0 (x : α) y ((not_congr Subtype.ext_iff_val).1 hxy)
      ⟨(coeₓ : Subtype p → α) ⁻¹' U, is_open_induced hU, hxyU⟩⟩

/-- A T₁ space, also known as a Fréchet space, is a topological space
  where every singleton set is closed. Equivalently, for every pair
  `x ≠ y`, there is an open set containing `x` and not `y`. -/
class T1Space(α : Type u)[TopologicalSpace α] : Prop where 
  t1 : ∀ x, IsClosed ({x} : Set α)

theorem is_closed_singleton [T1Space α] {x : α} : IsClosed ({x} : Set α) :=
  T1Space.t1 x

theorem is_open_compl_singleton [T1Space α] {x : α} : IsOpen («expr ᶜ» {x} : Set α) :=
  is_closed_singleton.is_open_compl

theorem is_open_ne [T1Space α] {x : α} : IsOpen { y | y ≠ x } :=
  is_open_compl_singleton

theorem Ne.nhds_within_compl_singleton [T1Space α] {x y : α} (h : x ≠ y) : 𝓝[«expr ᶜ» {y}] x = 𝓝 x :=
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

instance (priority := 100)T1Space.t0_space [T1Space α] : T0Space α :=
  ⟨fun x y h => ⟨{ z | z ≠ y }, is_open_ne, Or.inl ⟨h, not_not_intro rfl⟩⟩⟩

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem t1_iff_exists_open : «expr ↔ »(t1_space α, ∀
 x y, «expr ≠ »(x, y) → «expr∃ , »((U : set α) (hU : is_open U), «expr ∧ »(«expr ∈ »(x, U), «expr ∉ »(y, U)))) :=
begin
  split,
  { introsI [ident t1, ident x, ident y, ident hxy],
    exact [expr ⟨«expr ᶜ»({y}), is_open_compl_iff.mpr (t1_space.t1 y), mem_compl_singleton_iff.mpr hxy, not_not.mpr rfl⟩] },
  { intro [ident h],
    constructor,
    intro [ident x],
    rw ["<-", expr is_open_compl_iff] [],
    have [ident p] [":", expr «expr = »(«expr⋃₀ »({U : set α | «expr ∧ »(«expr ∉ »(x, U), is_open U)}), «expr ᶜ»({x}))] [],
    { apply [expr subset.antisymm]; intros [ident t, ident ht],
      { rcases [expr ht, "with", "⟨", ident A, ",", "⟨", ident hxA, ",", ident hA, "⟩", ",", ident htA, "⟩"],
        rw ["[", expr mem_compl_eq, ",", expr mem_singleton_iff, "]"] [],
        rintro [ident rfl],
        contradiction },
      { obtain ["⟨", ident U, ",", ident hU, ",", ident hh, "⟩", ":=", expr h t x (mem_compl_singleton_iff.mp ht)],
        exact [expr ⟨U, ⟨hh.2, hU⟩, hh.1⟩] } },
    rw ["<-", expr p] [],
    exact [expr is_open_sUnion (λ B hB, hB.2)] }
end

theorem compl_singleton_mem_nhds [T1Space α] {x y : α} (h : y ≠ x) : «expr ᶜ» {x} ∈ 𝓝 y :=
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
  (⋂(i : _)(h : p i), s i) = {x} :=
  by 
    simp only [eq_singleton_iff_unique_mem, mem_Inter]
    refine' ⟨fun i hi => mem_of_mem_nhds$ h.mem_of_mem hi, fun y hy => _⟩
    contrapose! hy 
    rcases h.mem_iff.1 (compl_singleton_mem_nhds hy.symm) with ⟨i, hi, hsub⟩
    exact ⟨i, hi, fun h => hsub h rfl⟩

/-- Removing a non-isolated point from a dense set, one still obtains a dense set. -/
theorem Dense.diff_singleton [T1Space α] {s : Set α} (hs : Dense s) (x : α) [ne_bot (𝓝[«expr ᶜ» {x}] x)] :
  Dense (s \ {x}) :=
  hs.inter_of_open_right (dense_compl_singleton x) is_open_compl_singleton

/-- Removing a finset from a dense set in a space without isolated points, one still
obtains a dense set. -/
theorem Dense.diff_finset [T1Space α] [∀ x : α, ne_bot (𝓝[«expr ᶜ» {x}] x)] {s : Set α} (hs : Dense s) (t : Finset α) :
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
theorem Dense.diff_finite [T1Space α] [∀ x : α, ne_bot (𝓝[«expr ᶜ» {x}] x)] {s : Set α} (hs : Dense s) {t : Set α}
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
      have fact₁ : «expr ᶜ» {f a} ∈ 𝓝 b := compl_singleton_mem_nhds hfa.symm 
      have fact₂ : tendsto f (pure a) (𝓝 b) := h.comp (tendsto_id'$ pure_le_nhds a)
      fact₂ fact₁ (Eq.refl$ f a)

/-- To prove a function to a `t1_space` is continuous at some point `a`, it suffices to prove that
`f` admits *some* limit at `a`. -/
theorem continuous_at_of_tendsto_nhds [TopologicalSpace β] [T1Space β] {f : α → β} {a : α} {b : β}
  (h : tendsto f (𝓝 a) (𝓝 b)) : ContinuousAt f a :=
  show tendsto f (𝓝 a) (𝓝$ f a)by 
    rwa [eq_of_tendsto_nhds h]

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the punctured neighborhoods of a point form a nontrivial filter, then any neighborhood is
infinite. -/
theorem infinite_of_mem_nhds
{α}
[topological_space α]
[t1_space α]
(x : α)
[hx : ne_bot «expr𝓝[ ] »(«expr ᶜ»({x}), x)]
{s : set α}
(hs : «expr ∈ »(s, expr𝓝() x)) : set.infinite s :=
begin
  unfreezingI { contrapose ["!"] [ident hx] },
  rw [expr set.not_infinite] ["at", ident hx],
  have [ident A] [":", expr is_closed «expr \ »(s, {x})] [":=", expr finite.is_closed (hx.subset (diff_subset _ _))],
  have [ident B] [":", expr «expr ∈ »(«expr ᶜ»(«expr \ »(s, {x})), expr𝓝() x)] [],
  { apply [expr is_open.mem_nhds],
    { apply [expr is_open_compl_iff.2 A] },
    { simp [] [] ["only"] ["[", expr not_true, ",", expr not_false_iff, ",", expr mem_diff, ",", expr and_false, ",", expr mem_compl_eq, ",", expr mem_singleton, "]"] [] [] } },
  have [ident C] [":", expr «expr ∈ »({x}, expr𝓝() x)] [],
  { apply [expr filter.mem_of_superset (filter.inter_mem hs B)],
    assume [binders (y hy)],
    simp [] [] ["only"] ["[", expr mem_singleton_iff, ",", expr mem_inter_eq, ",", expr not_and, ",", expr not_not, ",", expr mem_diff, ",", expr mem_compl_eq, "]"] [] ["at", ident hy],
    simp [] [] ["only"] ["[", expr hy.right hy.left, ",", expr mem_singleton, "]"] [] [] },
  have [ident D] [":", expr «expr ∈ »(«expr ᶜ»({x}), «expr𝓝[ ] »(«expr ᶜ»({x}), x))] [":=", expr self_mem_nhds_within],
  simpa [] [] [] ["[", "<-", expr empty_mem_iff_bot, "]"] [] ["using", expr filter.inter_mem (mem_nhds_within_of_mem_nhds C) D]
end

theorem discrete_of_t1_of_finite {X : Type _} [TopologicalSpace X] [T1Space X] [Fintype X] : DiscreteTopology X :=
  by 
    apply singletons_open_iff_discrete.mp 
    intro x 
    rw [←is_closed_compl_iff]
    exact Finite.is_closed (finite.of_fintype _)

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem singleton_mem_nhds_within_of_mem_discrete
{s : set α}
[discrete_topology s]
{x : α}
(hx : «expr ∈ »(x, s)) : «expr ∈ »({x}, «expr𝓝[ ] »(s, x)) :=
begin
  have [] [":", expr «expr ∈ »(({⟨x, hx⟩} : set s), expr𝓝() (⟨x, hx⟩ : s))] [],
  by simp [] [] [] ["[", expr nhds_discrete, "]"] [] [],
  simpa [] [] ["only"] ["[", expr nhds_within_eq_map_subtype_coe hx, ",", expr image_singleton, "]"] [] ["using", expr @image_mem_map _ _ _ (coe : s → α) _ this]
end

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

/-- A point `x` in a discrete subset `s` of a topological space admits a neighbourhood
that only meets `s` at `x`.  -/
theorem nhds_inter_eq_singleton_of_mem_discrete {s : Set α} [DiscreteTopology s] {x : α} (hx : x ∈ s) :
  ∃ (U : _)(_ : U ∈ 𝓝 x), U ∩ s = {x} :=
  by 
    simpa using (𝓝 x).basis_sets.exists_inter_eq_singleton_of_mem_discrete hx

/-- For point `x` in a discrete subset `s` of a topological space, there is a set `U`
such that
1. `U` is a punctured neighborhood of `x` (ie. `U ∪ {x}` is a neighbourhood of `x`),
2. `U` is disjoint from `s`.
-/
theorem disjoint_nhds_within_of_mem_discrete {s : Set α} [DiscreteTopology s] {x : α} (hx : x ∈ s) :
  ∃ (U : _)(_ : U ∈ 𝓝[«expr ᶜ» {x}] x), Disjoint U s :=
  let ⟨V, h, h'⟩ := nhds_inter_eq_singleton_of_mem_discrete hx
  ⟨«expr ᶜ» {x} ∩ V, inter_mem_nhds_within _ h,
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
    split 
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
class T2Space(α : Type u)[TopologicalSpace α] : Prop where 
  t2 : ∀ x y, x ≠ y → ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅

theorem t2_separation [T2Space α] {x y : α} (h : x ≠ y) :
  ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
  T2Space.t2 x y h

instance (priority := 100)T2Space.t1_space [T2Space α] : T1Space α :=
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

theorem t2_iff_ultrafilter : T2Space α ↔ ∀ {x y : α} f : Ultrafilter α, «expr↑ » f ≤ 𝓝 x → «expr↑ » f ≤ 𝓝 y → x = y :=
  t2_iff_nhds.trans$
    by 
      simp only [←exists_ultrafilter_iff, and_imp, le_inf_iff, exists_imp_distrib]

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_closed_diagonal [t2_space α] : is_closed (diagonal α) :=
begin
  refine [expr is_closed_iff_cluster_pt.mpr _],
  rintro ["⟨", ident a₁, ",", ident a₂, "⟩", ident h],
  refine [expr eq_of_nhds_ne_bot ⟨λ this : «expr = »(«expr ⊓ »(expr𝓝() a₁, expr𝓝() a₂), «expr⊥»()), h.ne _⟩],
  obtain ["⟨", ident t₁, ",", "(", ident ht₁, ":", expr «expr ∈ »(t₁, expr𝓝() a₁), ")", ",", ident t₂, ",", "(", ident ht₂, ":", expr «expr ∈ »(t₂, expr𝓝() a₂), ")", ",", "(", ident h', ":", expr «expr = »(«expr ∩ »(t₁, t₂), «expr∅»()), ")", "⟩", ":=", expr inf_eq_bot_iff.1 this],
  rw ["[", expr inf_principal_eq_bot, ",", expr nhds_prod_eq, "]"] [],
  apply [expr mem_of_superset (prod_mem_prod ht₁ ht₂)],
  rintro ["⟨", ident x, ",", ident y, "⟩", "⟨", ident x_in, ",", ident y_in, "⟩", "(", ident heq, ":", expr «expr = »(x, y), ")"],
  rw ["<-", expr heq] ["at", "*"],
  have [] [":", expr «expr ∈ »(x, «expr ∩ »(t₁, t₂))] [":=", expr ⟨x_in, y_in⟩],
  rwa [expr h'] ["at", ident this]
end

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem t2_iff_is_closed_diagonal : «expr ↔ »(t2_space α, is_closed (diagonal α)) :=
begin
  split,
  { introI [ident h],
    exact [expr is_closed_diagonal] },
  { intro [ident h],
    constructor,
    intros [ident x, ident y, ident hxy],
    have [] [":", expr «expr ∈ »((x, y), «expr ᶜ»(diagonal α))] [],
    by rwa ["[", expr mem_compl_iff, "]"] [],
    obtain ["⟨", ident t, ",", ident t_sub, ",", ident t_op, ",", ident xyt, "⟩", ":", expr «expr∃ , »((t «expr ⊆ » «expr ᶜ»(diagonal α)), «expr ∧ »(is_open t, «expr ∈ »((x, y), t))), ":=", expr is_open_iff_forall_mem_open.mp h.is_open_compl _ this],
    rcases [expr is_open_prod_iff.mp t_op x y xyt, "with", "⟨", ident U, ",", ident V, ",", ident U_op, ",", ident V_op, ",", ident xU, ",", ident yV, ",", ident H, "⟩"],
    use ["[", expr U, ",", expr V, ",", expr U_op, ",", expr V_op, ",", expr xU, ",", expr yV, "]"],
    have [] [] [":=", expr subset.trans H t_sub],
    rw [expr eq_empty_iff_forall_not_mem] [],
    rintros [ident z, "⟨", ident zU, ",", ident zV, "⟩"],
    have [] [":", expr «expr¬ »(«expr ∈ »((z, z), diagonal α))] [":=", expr this (mk_mem_prod zU zV)],
    exact [expr this rfl] }
end

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
class T25Space(α : Type u)[TopologicalSpace α] : Prop where 
  t2_5 : ∀ x y h : x ≠ y, ∃ U V : Set α, IsOpen U ∧ IsOpen V ∧ Closure U ∩ Closure V = ∅ ∧ x ∈ U ∧ y ∈ V

instance (priority := 100)T25Space.t2_space [T25Space α] : T2Space α :=
  ⟨fun x y hxy =>
      let ⟨U, V, hU, hV, hUV, hh⟩ := T25Space.t2_5 x y hxy
      ⟨U, V, hU, hV, hh.1, hh.2,
        subset_eq_empty (powerset_mono.mpr (closure_inter_subset_inter_closure U V) subset_closure) hUV⟩⟩

section limₓ

variable[T2Space α]{f : Filter α}

/-!
### Properties of `Lim` and `lim`

In this section we use explicit `nonempty α` instances for `Lim` and `lim`. This way the lemmas
are useful without a `nonempty α` instance.
-/


theorem Lim_eq {a : α} [ne_bot f] (h : f ≤ 𝓝 a) : @lim _ _ ⟨a⟩ f = a :=
  tendsto_nhds_unique (le_nhds_Lim ⟨a, h⟩) h

theorem Lim_eq_iff [ne_bot f] (h : ∃ a : α, f ≤ nhds a) {a} : @lim _ _ ⟨a⟩ f = a ↔ f ≤ 𝓝 a :=
  ⟨fun c => c ▸ le_nhds_Lim h, Lim_eq⟩

theorem Ultrafilter.Lim_eq_iff_le_nhds [CompactSpace α] {x : α} {F : Ultrafilter α} : F.Lim = x ↔ «expr↑ » F ≤ 𝓝 x :=
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

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem Lim_nhds_within
{a : α}
{s : set α}
(h : «expr ∈ »(a, closure s)) : «expr = »(@Lim _ _ ⟨a⟩ «expr𝓝[ ] »(s, a), a) :=
by haveI [] [":", expr ne_bot «expr𝓝[ ] »(s, a)] [":=", expr mem_closure_iff_cluster_pt.1 h]; exact [expr Lim_eq inf_le_left]

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


instance (priority := 100)t2_space_discrete {α : Type _} [TopologicalSpace α] [DiscreteTopology α] : T2Space α :=
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

instance  {α : Type _} {p : α → Prop} [t : TopologicalSpace α] [T2Space α] : T2Space (Subtype p) :=
  ⟨fun x y h => separated_by_continuous continuous_subtype_val (mt Subtype.eq h)⟩

instance  {α : Type _} {β : Type _} [t₁ : TopologicalSpace α] [T2Space α] [t₂ : TopologicalSpace β] [T2Space β] :
  T2Space (α × β) :=
  ⟨fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h =>
      Or.elim (not_and_distrib.mp (mt Prod.ext_iff.mpr h)) (fun h₁ => separated_by_continuous continuous_fst h₁)
        fun h₂ => separated_by_continuous continuous_snd h₂⟩

theorem Embedding.t2_space [TopologicalSpace β] [T2Space β] {f : α → β} (hf : Embedding f) : T2Space α :=
  ⟨fun x y h => separated_by_continuous hf.continuous (hf.inj.ne h)⟩

instance  {α : Type _} {β : Type _} [t₁ : TopologicalSpace α] [T2Space α] [t₂ : TopologicalSpace β] [T2Space β] :
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
  T2Space (Σi, α i) :=
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

variable[TopologicalSpace β]

theorem is_closed_eq [T2Space α] {f g : β → α} (hf : Continuous f) (hg : Continuous g) : IsClosed { x:β | f x = g x } :=
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

theorem diagonal_eq_range_diagonal_map {α : Type _} : { p:α × α | p.1 = p.2 } = range fun x => (x, x) :=
  ext$
    fun p =>
      Iff.intro (fun h => ⟨p.1, Prod.ext_iff.2 ⟨rfl, h⟩⟩)
        fun ⟨x, hx⟩ =>
          show p.1 = p.2by 
            rw [←hx]

theorem prod_subset_compl_diagonal_iff_disjoint {α : Type _} {s t : Set α} :
  Set.Prod s t ⊆ «expr ᶜ» { p:α × α | p.1 = p.2 } ↔ s ∩ t = ∅ :=
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
        have  : v ⊆ «expr ᶜ» s := subset_compl_comm.mp (subset.trans su (subset_compl_iff_disjoint.mpr uv))
        ⟨v, this, vo,
          by 
            simpa using xv⟩

@[simp]
theorem Filter.coclosed_compact_eq_cocompact [T2Space α] : coclosed_compact α = cocompact α :=
  by 
    simp [coclosed_compact, cocompact, infi_and', and_iff_right_of_imp IsCompact.is_closed]

/-- If `V : ι → set α` is a decreasing family of compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. This is a version of `exists_subset_nhd_of_compact'` where we
don't need to assume each `V i` closed because it follows from compactness since `α` is
assumed to be Hausdorff. -/
theorem exists_subset_nhd_of_compact [T2Space α] {ι : Type _} [Nonempty ι] {V : ι → Set α} (hV : Directed (· ⊇ ·) V)
  (hV_cpct : ∀ i, IsCompact (V i)) {U : Set α} (hU : ∀ x _ : x ∈ ⋂i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
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

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
theorem is_compact.finite_compact_cover
[t2_space α]
{s : set α}
(hs : is_compact s)
{ι}
(t : finset ι)
(U : ι → set α)
(hU : ∀ i «expr ∈ » t, is_open (U i))
(hsC : «expr ⊆ »(s, «expr⋃ , »((i «expr ∈ » t), U i))) : «expr∃ , »((K : ι → set α), «expr ∧ »(∀
  i, is_compact (K i), «expr ∧ »(∀ i, «expr ⊆ »(K i, U i), «expr = »(s, «expr⋃ , »((i «expr ∈ » t), K i))))) :=
begin
  classical,
  induction [expr t] ["using", ident finset.induction] ["with", ident x, ident t, ident hx, ident ih] ["generalizing", ident U, ident hU, ident s, ident hs, ident hsC],
  { refine [expr ⟨λ _, «expr∅»(), λ i, is_compact_empty, λ i, empty_subset _, _⟩],
    simpa [] [] ["only"] ["[", expr subset_empty_iff, ",", expr Union_false, ",", expr Union_empty, "]"] [] ["using", expr hsC] },
  simp [] [] ["only"] ["[", expr finset.set_bUnion_insert, "]"] [] ["at", ident hsC],
  simp [] [] ["only"] ["[", expr finset.mem_insert, "]"] [] ["at", ident hU],
  have [ident hU'] [":", expr ∀ i «expr ∈ » t, is_open (U i)] [":=", expr λ i hi, hU i (or.inr hi)],
  rcases [expr hs.binary_compact_cover (hU x (or.inl rfl)) (is_open_bUnion hU') hsC, "with", "⟨", ident K₁, ",", ident K₂, ",", ident h1K₁, ",", ident h1K₂, ",", ident h2K₁, ",", ident h2K₂, ",", ident hK, "⟩"],
  rcases [expr ih U hU' h1K₂ h2K₂, "with", "⟨", ident K, ",", ident h1K, ",", ident h2K, ",", ident h3K, "⟩"],
  refine [expr ⟨update K x K₁, _, _, _⟩],
  { intros [ident i],
    by_cases [expr hi, ":", expr «expr = »(i, x)],
    { simp [] [] ["only"] ["[", expr update_same, ",", expr hi, ",", expr h1K₁, "]"] [] [] },
    { rw ["[", "<-", expr ne.def, "]"] ["at", ident hi],
      simp [] [] ["only"] ["[", expr update_noteq hi, ",", expr h1K, "]"] [] [] } },
  { intros [ident i],
    by_cases [expr hi, ":", expr «expr = »(i, x)],
    { simp [] [] ["only"] ["[", expr update_same, ",", expr hi, ",", expr h2K₁, "]"] [] [] },
    { rw ["[", "<-", expr ne.def, "]"] ["at", ident hi],
      simp [] [] ["only"] ["[", expr update_noteq hi, ",", expr h2K, "]"] [] [] } },
  { simp [] [] ["only"] ["[", expr set_bUnion_insert_update _ hx, ",", expr hK, ",", expr h3K, "]"] [] [] }
end

end 

theorem locally_compact_of_compact_nhds [T2Space α] (h : ∀ x : α, ∃ s, s ∈ 𝓝 x ∧ IsCompact s) : LocallyCompactSpace α :=
  ⟨fun x n hn =>
      let ⟨u, un, uo, xu⟩ := mem_nhds_iff.mp hn 
      let ⟨k, kx, kc⟩ := h x 
      let ⟨v, w, vo, wo, xv, kuw, vw⟩ :=
        compact_compact_separated is_compact_singleton (IsCompact.diff kc uo)
          (by 
            rw [singleton_inter_eq_empty] <;> exact fun h => h.2 xu)
      have wn : «expr ᶜ» w ∈ 𝓝 x :=
        mem_nhds_iff.mpr ⟨v, subset_compl_iff_disjoint.mpr vw, vo, singleton_subset_iff.mp xv⟩
      ⟨k \ w, Filter.inter_mem kx wn, subset.trans (diff_subset_comm.mp kuw) un, kc.diff wo⟩⟩

instance (priority := 100)locally_compact_of_compact [T2Space α] [CompactSpace α] : LocallyCompactSpace α :=
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
class RegularSpace(α : Type u)[TopologicalSpace α] extends T0Space α : Prop where 
  regular : ∀ {s : Set α} {a}, IsClosed s → a ∉ s → ∃ t, IsOpen t ∧ s ⊆ t ∧ 𝓝[t] a = ⊥

instance (priority := 100)RegularSpace.t1_space [RegularSpace α] : T1Space α :=
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

theorem nhds_is_closed [RegularSpace α] {a : α} {s : Set α} (h : s ∈ 𝓝 a) :
  ∃ (t : _)(_ : t ∈ 𝓝 a), t ⊆ s ∧ IsClosed t :=
  let ⟨s', h₁, h₂, h₃⟩ := mem_nhds_iff.mp h 
  have  : ∃ t, IsOpen t ∧ «expr ᶜ» s' ⊆ t ∧ 𝓝[t] a = ⊥ :=
    RegularSpace.regular (is_closed_compl_iff.mpr h₂) (not_not_intro h₃)
  let ⟨t, ht₁, ht₂, ht₃⟩ := this
  ⟨«expr ᶜ» t,
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

instance Subtype.regular_space [RegularSpace α] {p : α → Prop} : RegularSpace (Subtype p) :=
  ⟨by 
      intro s a hs ha 
      rcases is_closed_induced_iff.1 hs with ⟨s, hs', rfl⟩
      rcases RegularSpace.regular hs' ha with ⟨t, ht, hst, hat⟩
      refine' ⟨coeₓ ⁻¹' t, is_open_induced ht, preimage_mono hst, _⟩
      rw [nhdsWithin, nhds_induced, ←comap_principal, ←comap_inf, ←nhdsWithin, hat, comap_bot]⟩

variable(α)

instance (priority := 100)RegularSpace.t2_space [RegularSpace α] : T2Space α :=
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

instance (priority := 100)RegularSpace.t2_5_space [RegularSpace α] : T25Space α :=
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

variable{α}

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
class NormalSpace(α : Type u)[TopologicalSpace α] extends T1Space α : Prop where 
  normal :
  ∀ s t : Set α, IsClosed s → IsClosed t → Disjoint s t → ∃ u v, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v

theorem normal_separation [NormalSpace α] {s t : Set α} (H1 : IsClosed s) (H2 : IsClosed t) (H3 : Disjoint s t) :
  ∃ u v, IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v :=
  NormalSpace.normal s t H1 H2 H3

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem normal_exists_closure_subset
[normal_space α]
{s t : set α}
(hs : is_closed s)
(ht : is_open t)
(hst : «expr ⊆ »(s, t)) : «expr∃ , »((u), «expr ∧ »(is_open u, «expr ∧ »(«expr ⊆ »(s, u), «expr ⊆ »(closure u, t)))) :=
begin
  have [] [":", expr disjoint s «expr ᶜ»(t)] [],
  from [expr λ (x) ⟨hxs, hxt⟩, hxt (hst hxs)],
  rcases [expr normal_separation hs (is_closed_compl_iff.2 ht) this, "with", "⟨", ident s', ",", ident t', ",", ident hs', ",", ident ht', ",", ident hss', ",", ident htt', ",", ident hs't', "⟩"],
  refine [expr ⟨s', hs', hss', subset.trans (closure_minimal _ (is_closed_compl_iff.2 ht')) (compl_subset_comm.1 htt')⟩],
  exact [expr λ x hxs hxt, hs't' ⟨hxs, hxt⟩]
end

instance (priority := 100)NormalSpace.regular_space [NormalSpace α] : RegularSpace α :=
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

end Normality

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a compact t2 space, the connected component of a point equals the intersection of all
its clopen neighbourhoods. -/
theorem connected_component_eq_Inter_clopen
[t2_space α]
[compact_space α]
{x : α} : «expr = »(connected_component x, «expr⋂ , »((Z : {Z : set α // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}), Z)) :=
begin
  apply [expr eq_of_subset_of_subset connected_component_subset_Inter_clopen],
  refine [expr is_preconnected.subset_connected_component _ (mem_Inter.2 (λ Z, Z.2.2))],
  have [ident hs] [":", expr @is_closed _ _inst_1 «expr⋂ , »((Z : {Z : set α // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}), Z)] [":=", expr is_closed_Inter (λ
    Z, Z.2.1.2)],
  rw [expr is_preconnected_iff_subset_of_fully_disjoint_closed hs] [],
  intros [ident a, ident b, ident ha, ident hb, ident hab, ident ab_empty],
  haveI [] [] [":=", expr @normal_of_compact_t2 α _ _ _],
  rcases [expr normal_separation ha hb (disjoint_iff.2 ab_empty), "with", "⟨", ident u, ",", ident v, ",", ident hu, ",", ident hv, ",", ident hau, ",", ident hbv, ",", ident huv, "⟩"],
  suffices [] [":", expr «expr∃ , »((Z : set α), «expr ∧ »(is_clopen Z, «expr ∧ »(«expr ∈ »(x, Z), «expr ⊆ »(Z, «expr ∪ »(u, v)))))],
  { cases [expr this] ["with", ident Z, ident H],
    rw ["[", expr disjoint_iff_inter_eq_empty, "]"] ["at", ident huv],
    have [ident H1] [] [":=", expr is_clopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hu hv huv],
    rw ["[", expr union_comm, "]"] ["at", ident H],
    have [ident H2] [] [":=", expr is_clopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hv hu «expr ▸ »(inter_comm u v, huv)],
    by_cases [expr «expr ∈ »(x, u)],
    { left,
      suffices [] [":", expr «expr ⊆ »(«expr⋂ , »((Z : {Z : set α // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}), «expr↑ »(Z)), u)],
      { rw ["<-", expr set.disjoint_iff_inter_eq_empty] ["at", ident huv],
        replace [ident hab] [":", expr «expr ≤ »(«expr⋂ , »((Z : {Z // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}), «expr↑ »(Z)), «expr ∪ »(a, b))] [":=", expr hab],
        replace [ident this] [":", expr «expr ≤ »(«expr⋂ , »((Z : {Z // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}), «expr↑ »(Z)), u)] [":=", expr this],
        exact [expr disjoint.left_le_of_le_sup_right hab (huv.mono this hbv)] },
      { apply [expr subset.trans _ (inter_subset_right Z u)],
        apply [expr Inter_subset (λ
          Z : {Z : set α // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}, «expr↑ »(Z)) ⟨«expr ∩ »(Z, u), H1, mem_inter H.2.1 h⟩] } },
    have [ident h1] [":", expr «expr ∈ »(x, v)] [],
    { cases [expr (mem_union x u v).1 (mem_of_subset_of_mem (subset.trans hab (union_subset_union hau hbv)) (mem_Inter.2 (λ
          i, i.2.2)))] ["with", ident h1, ident h1],
      { exfalso,
        exact [expr h h1] },
      { exact [expr h1] } },
    right,
    suffices [] [":", expr «expr ⊆ »(«expr⋂ , »((Z : {Z : set α // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}), «expr↑ »(Z)), v)],
    { rw ["[", expr inter_comm, ",", "<-", expr set.disjoint_iff_inter_eq_empty, "]"] ["at", ident huv],
      replace [ident hab] [":", expr «expr ≤ »(«expr⋂ , »((Z : {Z // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}), «expr↑ »(Z)), «expr ∪ »(a, b))] [":=", expr hab],
      replace [ident this] [":", expr «expr ≤ »(«expr⋂ , »((Z : {Z // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}), «expr↑ »(Z)), v)] [":=", expr this],
      exact [expr disjoint.left_le_of_le_sup_left hab (huv.mono this hau)] },
    { apply [expr subset.trans _ (inter_subset_right Z v)],
      apply [expr Inter_subset (λ
        Z : {Z : set α // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}, «expr↑ »(Z)) ⟨«expr ∩ »(Z, v), H2, mem_inter H.2.1 h1⟩] } },
  have [ident H1] [] [":=", expr (is_closed_compl_iff.2 (hu.union hv)).is_compact.inter_Inter_nonempty (λ
    Z : {Z : set α // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}, Z) (λ Z, Z.2.1.2)],
  rw ["[", "<-", expr not_imp_not, ",", expr not_forall, ",", expr not_nonempty_iff_eq_empty, ",", expr inter_comm, "]"] ["at", ident H1],
  have [ident huv_union] [] [":=", expr subset.trans hab (union_subset_union hau hbv)],
  rw ["[", "<-", expr compl_compl «expr ∪ »(u, v), ",", expr subset_compl_iff_disjoint, "]"] ["at", ident huv_union],
  cases [expr H1 huv_union] ["with", ident Zi, ident H2],
  refine [expr ⟨«expr⋂ , »((U «expr ∈ » Zi), subtype.val U), _, _, _⟩],
  { exact [expr is_clopen_bInter (λ Z hZ, Z.2.1)] },
  { exact [expr mem_bInter_iff.2 (λ Z hZ, Z.2.2)] },
  { rwa ["[", expr not_nonempty_iff_eq_empty, ",", expr inter_comm, ",", "<-", expr subset_compl_iff_disjoint, ",", expr compl_compl, "]"] ["at", ident H2] }
end

section Profinite

open TopologicalSpace

variable[T2Space α]

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A Hausdorff space with a clopen basis is totally separated. -/
theorem tot_sep_of_zero_dim (h : is_topological_basis {s : set α | is_clopen s}) : totally_separated_space α :=
begin
  constructor,
  rintros [ident x, "-", ident y, "-", ident hxy],
  obtain ["⟨", ident u, ",", ident v, ",", ident hu, ",", ident hv, ",", ident xu, ",", ident yv, ",", ident disj, "⟩", ":=", expr t2_separation hxy],
  obtain ["⟨", ident w, ",", ident hw, ":", expr is_clopen w, ",", ident xw, ",", ident wu, "⟩", ":=", expr (is_topological_basis.mem_nhds_iff h).1 (is_open.mem_nhds hu xu)],
  refine [expr ⟨w, «expr ᶜ»(w), hw.1, (is_clopen_compl_iff.2 hw).1, xw, _, _, set.inter_compl_self w⟩],
  { intro [ident h],
    have [] [":", expr «expr ∈ »(y, «expr ∩ »(u, v))] [":=", expr ⟨wu h, yv⟩],
    rwa [expr disj] ["at", ident this] },
  rw [expr set.union_compl_self] []
end

variable[CompactSpace α]

/-- A compact Hausdorff space is totally disconnected if and only if it is totally separated, this
  is also true for locally compact spaces. -/
theorem compact_t2_tot_disc_iff_tot_sep : TotallyDisconnectedSpace α ↔ TotallySeparatedSpace α :=
  by 
    split 
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
      simpa using hyp («expr ᶜ» w) w (is_open_compl_iff.mpr hw.2) hw.1 hx hy 
    apply TotallySeparatedSpace.totally_disconnected_space

variable[TotallyDisconnectedSpace α]

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nhds_basis_clopen (x : α) : (expr𝓝() x).has_basis (λ s : set α, «expr ∧ »(«expr ∈ »(x, s), is_clopen s)) id :=
⟨λ U, begin
   split,
   { have [] [":", expr «expr = »(connected_component x, {x})] [],
     from [expr totally_disconnected_space_iff_connected_component_singleton.mp «expr‹ ›»(_) x],
     rw [expr connected_component_eq_Inter_clopen] ["at", ident this],
     intros [ident hU],
     let [ident N] [] [":=", expr {Z // «expr ∧ »(is_clopen Z, «expr ∈ »(x, Z))}],
     suffices [] [":", expr «expr∃ , »((Z : N), «expr ⊆ »(Z.val, U))],
     { rcases [expr this, "with", "⟨", "⟨", ident s, ",", ident hs, ",", ident hs', "⟩", ",", ident hs'', "⟩"],
       exact [expr ⟨s, ⟨hs', hs⟩, hs''⟩] },
     haveI [] [":", expr nonempty N] [":=", expr ⟨⟨univ, is_clopen_univ, mem_univ x⟩⟩],
     have [ident hNcl] [":", expr ∀ Z : N, is_closed Z.val] [":=", expr λ Z, Z.property.1.2],
     have [ident hdir] [":", expr directed superset (λ Z : N, Z.val)] [],
     { rintros ["⟨", ident s, ",", ident hs, ",", ident hxs, "⟩", "⟨", ident t, ",", ident ht, ",", ident hxt, "⟩"],
       exact [expr ⟨⟨«expr ∩ »(s, t), hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left s t, inter_subset_right s t⟩] },
     have [ident h_nhd] [":", expr ∀ y «expr ∈ » «expr⋂ , »((Z : N), Z.val), «expr ∈ »(U, expr𝓝() y)] [],
     { intros [ident y, ident y_in],
       erw ["[", expr this, ",", expr mem_singleton_iff, "]"] ["at", ident y_in],
       rwa [expr y_in] [] },
     exact [expr exists_subset_nhd_of_compact_space hdir hNcl h_nhd] },
   { rintro ["⟨", ident V, ",", "⟨", ident hxV, ",", ident V_op, ",", "-", "⟩", ",", ident hUV, ":", expr «expr ⊆ »(V, U), "⟩"],
     rw [expr mem_nhds_iff] [],
     exact [expr ⟨V, hUV, V_op, hxV⟩] }
 end⟩

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_topological_basis_clopen : is_topological_basis {s : set α | is_clopen s} :=
begin
  apply [expr is_topological_basis_of_open_of_nhds (λ (U) (hU : is_clopen U), hU.1)],
  intros [ident x, ident U, ident hxU, ident U_op],
  have [] [":", expr «expr ∈ »(U, expr𝓝() x)] [],
  from [expr is_open.mem_nhds U_op hxU],
  rcases [expr (nhds_basis_clopen x).mem_iff.mp this, "with", "⟨", ident V, ",", "⟨", ident hxV, ",", ident hV, "⟩", ",", ident hVU, ":", expr «expr ⊆ »(V, U), "⟩"],
  use [expr V],
  tauto []
end

/-- Every member of an open set in a compact Hausdorff totally disconnected space
  is contained in a clopen set contained in the open set.  -/
theorem compact_exists_clopen_in_open {x : α} {U : Set α} (is_open : IsOpen U) (memU : x ∈ U) :
  ∃ (V : Set α)(hV : IsClopen V), x ∈ V ∧ V ⊆ U :=
  (is_topological_basis.mem_nhds_iff is_topological_basis_clopen).1 (IsOpen.mem_nhds memU)

end Profinite

section LocallyCompact

open TopologicalSpace

variable{H : Type _}[TopologicalSpace H][LocallyCompactSpace H][T2Space H]

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A locally compact Hausdorff totally disconnected space has a basis with clopen elements. -/
theorem loc_compact_Haus_tot_disc_of_zero_dim
[totally_disconnected_space H] : is_topological_basis {s : set H | is_clopen s} :=
begin
  refine [expr is_topological_basis_of_open_of_nhds (λ u hu, hu.1) _],
  rintros [ident x, ident U, ident memU, ident hU],
  obtain ["⟨", ident s, ",", ident comp, ",", ident xs, ",", ident sU, "⟩", ":=", expr exists_compact_subset hU memU],
  obtain ["⟨", ident t, ",", ident h, ",", ident ht, ",", ident xt, "⟩", ":=", expr mem_interior.1 xs],
  let [ident u] [":", expr set s] [":=", expr «expr ⁻¹' »((coe : s → H), interior s)],
  have [ident u_open_in_s] [":", expr is_open u] [":=", expr is_open_interior.preimage continuous_subtype_coe],
  let [ident X] [":", expr s] [":=", expr ⟨x, h xt⟩],
  have [ident Xu] [":", expr «expr ∈ »(X, u)] [":=", expr xs],
  haveI [] [":", expr compact_space s] [":=", expr is_compact_iff_compact_space.1 comp],
  obtain ["⟨", ident V, ":", expr set s, ",", ident clopen_in_s, ",", ident Vx, ",", ident V_sub, "⟩", ":=", expr compact_exists_clopen_in_open u_open_in_s Xu],
  have [ident V_clopen] [":", expr is_clopen «expr '' »((coe : s → H), V)] [],
  { refine [expr ⟨_, comp.is_closed.closed_embedding_subtype_coe.closed_iff_image_closed.1 clopen_in_s.2⟩],
    let [ident v] [":", expr set u] [":=", expr «expr ⁻¹' »((coe : u → s), V)],
    have [] [":", expr «expr = »((coe : u → H), «expr ∘ »((coe : s → H), (coe : u → s)))] [":=", expr rfl],
    have [ident f0] [":", expr embedding (coe : u → H)] [":=", expr embedding_subtype_coe.comp embedding_subtype_coe],
    have [ident f1] [":", expr open_embedding (coe : u → H)] [],
    { refine [expr ⟨f0, _⟩],
      { have [] [":", expr «expr = »(set.range (coe : u → H), interior s)] [],
        { rw ["[", expr this, ",", expr set.range_comp, ",", expr subtype.range_coe, ",", expr subtype.image_preimage_coe, "]"] [],
          apply [expr set.inter_eq_self_of_subset_left interior_subset] },
        rw [expr this] [],
        apply [expr is_open_interior] } },
    have [ident f2] [":", expr is_open v] [":=", expr clopen_in_s.1.preimage continuous_subtype_coe],
    have [ident f3] [":", expr «expr = »(«expr '' »((coe : s → H), V), «expr '' »((coe : u → H), v))] [],
    { rw ["[", expr this, ",", expr image_comp coe coe, ",", expr subtype.image_preimage_coe, ",", expr inter_eq_self_of_subset_left V_sub, "]"] [] },
    rw [expr f3] [],
    apply [expr f1.is_open_map v f2] },
  refine [expr ⟨«expr '' »(coe, V), V_clopen, by simp [] [] [] ["[", expr Vx, ",", expr h xt, "]"] [] [], _⟩],
  transitivity [expr s],
  { simp [] [] [] [] [] [] },
  assumption
end

/-- A locally compact Hausdorff space is totally disconnected
  if and only if it is totally separated. -/
theorem loc_compact_t2_tot_disc_iff_tot_sep : TotallyDisconnectedSpace H ↔ TotallySeparatedSpace H :=
  by 
    split 
    ·
      intro h 
      exact tot_sep_of_zero_dim loc_compact_Haus_tot_disc_of_zero_dim 
    apply TotallySeparatedSpace.totally_disconnected_space

end LocallyCompact

section connectedComponentSetoid

attribute [local instance] connectedComponentSetoid

-- error in Topology.Separation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `connected_components α` is Hausdorff when `α` is Hausdorff and compact -/
instance connected_components.t2 [t2_space α] [compact_space α] : t2_space (connected_components α) :=
begin
  refine [expr ⟨λ x y, quotient.induction_on x (quotient.induction_on y (λ a b ne, _))⟩],
  rw [expr connected_component_nrel_iff] ["at", ident ne],
  have [ident h] [] [":=", expr connected_component_disjoint ne],
  rw ["[", expr connected_component_eq_Inter_clopen, ",", expr disjoint_iff_inter_eq_empty, ",", expr inter_comm, "]"] ["at", ident h],
  cases [expr is_closed_connected_component.is_compact.elim_finite_subfamily_closed _ _ h] ["with", ident fin_a, ident ha],
  swap,
  { exact [expr λ Z, Z.2.1.2] },
  set [] [ident U] [":", expr set α] [":="] [expr «expr⋂ , »((i : {Z // «expr ∧ »(is_clopen Z, «expr ∈ »(b, Z))})
    (H : «expr ∈ »(i, fin_a)), i)] ["with", ident hU],
  rw ["<-", expr hU] ["at", ident ha],
  have [ident hu_clopen] [":", expr is_clopen U] [":=", expr is_clopen_bInter (λ i j, i.2.1)],
  use ["[", expr «expr '' »(quotient.mk, U), ",", expr «expr '' »(quotient.mk, «expr ᶜ»(U)), "]"],
  have [ident hu] [":", expr «expr = »(«expr ⁻¹' »(quotient.mk, «expr '' »(quotient.mk, U)), U)] [":=", expr «expr ▸ »(connected_components_preimage_image U, eq.symm) hu_clopen.eq_union_connected_components],
  have [ident huc] [":", expr «expr = »(«expr ⁻¹' »(quotient.mk, «expr '' »(quotient.mk, «expr ᶜ»(U))), «expr ᶜ»(U))] [":=", expr «expr ▸ »(connected_components_preimage_image «expr ᶜ»(U), eq.symm) (is_clopen.compl hu_clopen).eq_union_connected_components],
  refine [expr ⟨_, _, _, _, _⟩],
  { rw ["[", expr (quotient_map_iff.1 quotient_map_quotient_mk).2 _, ",", expr hu, "]"] [],
    exact [expr hu_clopen.1] },
  { rw ["[", expr (quotient_map_iff.1 quotient_map_quotient_mk).2 _, ",", expr huc, "]"] [],
    exact [expr is_open_compl_iff.2 hu_clopen.2] },
  { exact [expr mem_image_of_mem _ (mem_Inter.2 (λ Z, mem_Inter.2 (λ Zmem, Z.2.2)))] },
  { apply [expr mem_image_of_mem],
    exact [expr mem_of_subset_of_mem (subset_compl_iff_disjoint.2 ha) (@mem_connected_component _ _ a)] },
  apply [expr preimage_injective.2 (@surjective_quotient_mk _ _)],
  rw ["[", expr preimage_inter, ",", expr preimage_empty, ",", expr hu, ",", expr huc, ",", expr inter_compl_self _, "]"] []
end

end connectedComponentSetoid

