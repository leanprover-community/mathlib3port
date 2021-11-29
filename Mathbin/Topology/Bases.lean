import Mathbin.Topology.ContinuousOn 
import Mathbin.Topology.Constructions

/-!
# Bases of topologies. Countability axioms.

A topological basis on a topological space `t` is a collection of sets,
such that all open sets can be generated as unions of these sets, without the need to take
finite intersections of them. This file introduces a framework for dealing with these collections,
and also what more we can say under certain countability conditions on bases,
which are referred to as first- and second-countable.
We also briefly cover the theory of separable spaces, which are those with a countable, dense
subset. If a space is second-countable, and also has a countably generated uniformity filter
(for example, if `t` is a metric space), it will automatically be separable (and indeed, these
conditions are equivalent in this case).

## Main definitions

* `is_topological_basis s`: The topological space `t` has basis `s`.
* `separable_space α`: The topological space `t` has a countable, dense subset.
* `first_countable_topology α`: A topology in which `𝓝 x` is countably generated for every `x`.
* `second_countable_topology α`: A topology which has a topological basis which is countable.

## Main results

* `first_countable_topology.tendsto_subseq`: In a first-countable space,
  cluster points are limits of subsequences.
* `second_countable_topology.is_open_Union_countable`: In a second-countable space, the union of
  arbitrarily-many open sets is equal to a sub-union of only countably many of these sets.
* `second_countable_topology.countable_cover_nhds`: Consider `f : α → set α` with the property that
  `f x ∈ 𝓝 x` for all `x`. Then there is some countable set `s` whose image covers the space.

## Implementation Notes
For our applications we are interested that there exists a countable basis, but we do not need the
concrete basis itself. This allows us to declare these type classes as `Prop` to use them as mixins.

### TODO:
More fine grained instances for `first_countable_topology`, `separable_space`, `t2_space`, and more
(see the comment below `subtype.second_countable_topology`.)
-/


open Set Filter Classical

open_locale TopologicalSpace Filter

noncomputable theory

namespace TopologicalSpace

universe u

variable {α : Type u} [t : TopologicalSpace α]

include t

/-- A topological basis is one that satisfies the necessary conditions so that
  it suffices to take unions of the basis sets to get a topology (without taking
  finite intersections as well). -/
structure is_topological_basis (s : Set (Set α)) : Prop where 
  exists_subset_inter :
  ∀ t₁ _ : t₁ ∈ s, ∀ t₂ _ : t₂ ∈ s, ∀ x _ : x ∈ t₁ ∩ t₂, ∃ (t₃ : _)(_ : t₃ ∈ s), x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂ 
  sUnion_eq : ⋃₀s = univ 
  eq_generate_from : t = generate_from s

-- error in Topology.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a family of sets `s` generates the topology, then nonempty intersections of finite
subcollections of `s` form a topological basis. -/
theorem is_topological_basis_of_subbasis
{s : set (set α)}
(hs : «expr = »(t, generate_from s)) : is_topological_basis «expr '' »(λ
 f, «expr⋂₀ »(f), {f : set (set α) | «expr ∧ »(finite f, «expr ∧ »(«expr ⊆ »(f, s), «expr⋂₀ »(f).nonempty))}) :=
begin
  refine [expr ⟨_, _, _⟩],
  { rintro ["_", "⟨", ident t₁, ",", "⟨", ident hft₁, ",", ident ht₁b, ",", ident ht₁, "⟩", ",", ident rfl, "⟩", "_", "⟨", ident t₂, ",", "⟨", ident hft₂, ",", ident ht₂b, ",", ident ht₂, "⟩", ",", ident rfl, "⟩", ident x, ident h],
    have [] [":", expr «expr = »(«expr⋂₀ »(«expr ∪ »(t₁, t₂)), «expr ∩ »(«expr⋂₀ »(t₁), «expr⋂₀ »(t₂)))] [":=", expr sInter_union t₁ t₂],
    exact [expr ⟨_, ⟨«expr ∪ »(t₁, t₂), ⟨hft₁.union hft₂, union_subset ht₁b ht₂b, «expr ▸ »(this.symm, ⟨x, h⟩)⟩, this⟩, h, subset.rfl⟩] },
  { rw ["[", expr sUnion_image, ",", expr bUnion_eq_univ_iff, "]"] [],
    intro [ident x],
    have [] [":", expr «expr ∈ »(x, «expr⋂₀ »(«expr∅»()))] [],
    { rw [expr sInter_empty] [],
      exact [expr mem_univ x] },
    exact [expr ⟨«expr∅»(), ⟨finite_empty, empty_subset _, x, this⟩, this⟩] },
  { rw [expr hs] [],
    apply [expr le_antisymm]; apply [expr le_generate_from],
    { rintro ["_", "⟨", ident t, ",", "⟨", ident hft, ",", ident htb, ",", ident ht, "⟩", ",", ident rfl, "⟩"],
      exact [expr @is_open_sInter _ (generate_from s) _ hft (λ s hs, «expr $ »(generate_open.basic _, htb hs))] },
    { intros [ident t, ident ht],
      rcases [expr t.eq_empty_or_nonempty, "with", ident rfl, "|", ident hne],
      { apply [expr @is_open_empty _ _] },
      rw ["<-", expr sInter_singleton t] ["at", ident hne, "⊢"],
      exact [expr generate_open.basic _ ⟨{t}, ⟨finite_singleton t, singleton_subset_iff.2 ht, hne⟩, rfl⟩] } }
end

/-- If a family of open sets `s` is such that every open neighbourhood contains some
member of `s`, then `s` is a topological basis. -/
theorem is_topological_basis_of_open_of_nhds {s : Set (Set α)} (h_open : ∀ u _ : u ∈ s, IsOpen u)
  (h_nhds : ∀ a : α u : Set α, a ∈ u → IsOpen u → ∃ (v : _)(_ : v ∈ s), a ∈ v ∧ v ⊆ u) : is_topological_basis s :=
  by 
    refine' ⟨fun t₁ ht₁ t₂ ht₂ x hx => h_nhds _ _ hx (IsOpen.inter (h_open _ ht₁) (h_open _ ht₂)), _, _⟩
    ·
      refine' sUnion_eq_univ_iff.2 fun a => _ 
      rcases h_nhds a univ trivialₓ is_open_univ with ⟨u, h₁, h₂, -⟩
      exact ⟨u, h₁, h₂⟩
    ·
      refine' (le_generate_from h_open).antisymm fun u hu => _ 
      refine' (@is_open_iff_nhds α (generate_from s) u).mpr fun a ha => _ 
      rcases h_nhds a u ha hu with ⟨v, hvs, hav, hvu⟩
      rw [nhds_generate_from]
      exact binfi_le_of_le v ⟨hav, hvs⟩ (le_principal_iff.2 hvu)

/-- A set `s` is in the neighbourhood of `a` iff there is some basis set `t`, which
contains `a` and is itself contained in `s`. -/
theorem is_topological_basis.mem_nhds_iff {a : α} {s : Set α} {b : Set (Set α)} (hb : is_topological_basis b) :
  s ∈ 𝓝 a ↔ ∃ (t : _)(_ : t ∈ b), a ∈ t ∧ t ⊆ s :=
  by 
    change s ∈ (𝓝 a).Sets ↔ ∃ (t : _)(_ : t ∈ b), a ∈ t ∧ t ⊆ s 
    rw [hb.eq_generate_from, nhds_generate_from, binfi_sets_eq]
    ·
      simp only [mem_bUnion_iff, exists_prop, mem_set_of_eq, and_assoc, And.left_comm]
      rfl
    ·
      exact
        fun s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩ =>
          have  : a ∈ s ∩ t := ⟨hs₁, ht₁⟩
          let ⟨u, hu₁, hu₂, hu₃⟩ := hb.1 _ hs₂ _ ht₂ _ this
          ⟨u, ⟨hu₂, hu₁⟩, le_principal_iff.2 (subset.trans hu₃ (inter_subset_left _ _)),
            le_principal_iff.2 (subset.trans hu₃ (inter_subset_right _ _))⟩
    ·
      rcases eq_univ_iff_forall.1 hb.sUnion_eq a with ⟨i, h1, h2⟩
      exact ⟨i, h2, h1⟩

theorem is_topological_basis.nhds_has_basis {b : Set (Set α)} (hb : is_topological_basis b) {a : α} :
  (𝓝 a).HasBasis (fun t : Set α => t ∈ b ∧ a ∈ t) fun t => t :=
  ⟨fun s =>
      hb.mem_nhds_iff.trans$
        by 
          simp only [exists_prop, and_assoc]⟩

protected theorem is_topological_basis.is_open {s : Set α} {b : Set (Set α)} (hb : is_topological_basis b)
  (hs : s ∈ b) : IsOpen s :=
  by 
    rw [hb.eq_generate_from]
    exact generate_open.basic s hs

protected theorem is_topological_basis.mem_nhds {a : α} {s : Set α} {b : Set (Set α)} (hb : is_topological_basis b)
  (hs : s ∈ b) (ha : a ∈ s) : s ∈ 𝓝 a :=
  (hb.is_open hs).mem_nhds ha

theorem is_topological_basis.exists_subset_of_mem_open {b : Set (Set α)} (hb : is_topological_basis b) {a : α}
  {u : Set α} (au : a ∈ u) (ou : IsOpen u) : ∃ (v : _)(_ : v ∈ b), a ∈ v ∧ v ⊆ u :=
  hb.mem_nhds_iff.1$ IsOpen.mem_nhds ou au

/-- Any open set is the union of the basis sets contained in it. -/
theorem is_topological_basis.open_eq_sUnion' {B : Set (Set α)} (hB : is_topological_basis B) {u : Set α}
  (ou : IsOpen u) : u = ⋃₀{ s∈B | s ⊆ u } :=
  ext$
    fun a =>
      ⟨fun ha =>
          let ⟨b, hb, ab, bu⟩ := hB.exists_subset_of_mem_open ha ou
          ⟨b, ⟨hb, bu⟩, ab⟩,
        fun ⟨b, ⟨hb, bu⟩, ab⟩ => bu ab⟩

theorem is_topological_basis.open_eq_sUnion {B : Set (Set α)} (hB : is_topological_basis B) {u : Set α}
  (ou : IsOpen u) : ∃ (S : _)(_ : S ⊆ B), u = ⋃₀S :=
  ⟨{ s∈B | s ⊆ u }, fun s h => h.1, hB.open_eq_sUnion' ou⟩

theorem is_topological_basis.open_eq_Union {B : Set (Set α)} (hB : is_topological_basis B) {u : Set α} (ou : IsOpen u) :
  ∃ (β : Type u)(f : β → Set α), (u = ⋃i, f i) ∧ ∀ i, f i ∈ B :=
  ⟨«expr↥ » { s∈B | s ⊆ u }, coeₓ,
    by 
      rw [←sUnion_eq_Union]
      apply hB.open_eq_sUnion' ou,
    fun s => And.left s.2⟩

/-- A point `a` is in the closure of `s` iff all basis sets containing `a` intersect `s`. -/
theorem is_topological_basis.mem_closure_iff {b : Set (Set α)} (hb : is_topological_basis b) {s : Set α} {a : α} :
  a ∈ Closure s ↔ ∀ o _ : o ∈ b, a ∈ o → (o ∩ s).Nonempty :=
  (mem_closure_iff_nhds_basis' hb.nhds_has_basis).trans$
    by 
      simp only [and_imp]

/-- A set is dense iff it has non-trivial intersection with all basis sets. -/
theorem is_topological_basis.dense_iff {b : Set (Set α)} (hb : is_topological_basis b) {s : Set α} :
  Dense s ↔ ∀ o _ : o ∈ b, Set.Nonempty o → (o ∩ s).Nonempty :=
  by 
    simp only [Dense, hb.mem_closure_iff]
    exact ⟨fun h o hb ⟨a, ha⟩ => h a o hb ha, fun h a o hb ha => h o hb ⟨a, ha⟩⟩

theorem is_topological_basis.is_open_map_iff {β} [TopologicalSpace β] {B : Set (Set α)} (hB : is_topological_basis B)
  {f : α → β} : IsOpenMap f ↔ ∀ s _ : s ∈ B, IsOpen (f '' s) :=
  by 
    refine' ⟨fun H o ho => H _ (hB.is_open ho), fun hf o ho => _⟩
    rw [hB.open_eq_sUnion' ho, sUnion_eq_Union, image_Union]
    exact is_open_Union fun s => hf s s.2.1

theorem is_topological_basis.exists_nonempty_subset {B : Set (Set α)} (hb : is_topological_basis B) {u : Set α}
  (hu : u.nonempty) (ou : IsOpen u) : ∃ (v : _)(_ : v ∈ B), Set.Nonempty v ∧ v ⊆ u :=
  by 
    cases' hu with x hx 
    rw [hb.open_eq_sUnion' ou, mem_sUnion] at hx 
    rcases hx with ⟨v, hv, hxv⟩
    exact ⟨v, hv.1, ⟨x, hxv⟩, hv.2⟩

theorem is_topological_basis_opens : is_topological_basis { U:Set α | IsOpen U } :=
  is_topological_basis_of_open_of_nhds
    (by 
      tauto)
    (by 
      tauto)

protected theorem is_topological_basis.prod {β} [TopologicalSpace β] {B₁ : Set (Set α)} {B₂ : Set (Set β)}
  (h₁ : is_topological_basis B₁) (h₂ : is_topological_basis B₂) : is_topological_basis (image2 Set.Prod B₁ B₂) :=
  by 
    refine' is_topological_basis_of_open_of_nhds _ _
    ·
      rintro _ ⟨u₁, u₂, hu₁, hu₂, rfl⟩
      exact (h₁.is_open hu₁).Prod (h₂.is_open hu₂)
    ·
      rintro ⟨a, b⟩ u hu uo 
      rcases(h₁.nhds_has_basis.prod_nhds h₂.nhds_has_basis).mem_iff.1 (IsOpen.mem_nhds uo hu) with
        ⟨⟨s, t⟩, ⟨⟨hs, ha⟩, ht, hb⟩, hu⟩
      exact ⟨s.prod t, mem_image2_of_mem hs ht, ⟨ha, hb⟩, hu⟩

protected theorem is_topological_basis.inducing {β} [TopologicalSpace β] {f : α → β} {T : Set (Set β)} (hf : Inducing f)
  (h : is_topological_basis T) : is_topological_basis (image (preimage f) T) :=
  by 
    refine' is_topological_basis_of_open_of_nhds _ _
    ·
      rintro _ ⟨V, hV, rfl⟩
      rwa [hf.is_open_iff]
      refine' ⟨V, h.is_open hV, rfl⟩
    ·
      intro a U ha hU 
      rw [hf.is_open_iff] at hU 
      obtain ⟨V, hV, rfl⟩ := hU 
      obtain ⟨S, hS, rfl⟩ := h.open_eq_sUnion hV 
      obtain ⟨W, hW, ha⟩ := ha 
      refine' ⟨f ⁻¹' W, ⟨_, hS hW, rfl⟩, ha, Set.preimage_mono$ Set.subset_sUnion_of_mem hW⟩

theorem is_topological_basis_of_cover {ι} {U : ι → Set α} (Uo : ∀ i, IsOpen (U i)) (Uc : (⋃i, U i) = univ)
  {b : ∀ i, Set (Set (U i))} (hb : ∀ i, is_topological_basis (b i)) :
  is_topological_basis (⋃i : ι, image (coeₓ : U i → α) '' b i) :=
  by 
    refine' is_topological_basis_of_open_of_nhds (fun u hu => _) _
    ·
      simp only [mem_Union, mem_image] at hu 
      rcases hu with ⟨i, s, sb, rfl⟩
      exact (Uo i).is_open_map_subtype_coe _ ((hb i).IsOpen sb)
    ·
      intro a u ha uo 
      rcases Union_eq_univ_iff.1 Uc a with ⟨i, hi⟩
      lift a to «expr↥ » (U i) using hi 
      rcases(hb i).exists_subset_of_mem_open
          (by 
            exact ha)
          (uo.preimage continuous_subtype_coe) with
        ⟨v, hvb, hav, hvu⟩
      exact ⟨coeₓ '' v, mem_Union.2 ⟨i, mem_image_of_mem _ hvb⟩, mem_image_of_mem _ hav, image_subset_iff.2 hvu⟩

protected theorem is_topological_basis.continuous {β : Type _} [TopologicalSpace β] {B : Set (Set β)}
  (hB : is_topological_basis B) (f : α → β) (hf : ∀ s _ : s ∈ B, IsOpen (f ⁻¹' s)) : Continuous f :=
  by 
    rw [hB.eq_generate_from]
    exact continuous_generated_from hf

variable (α)

/-- A separable space is one with a countable dense subset, available through
`topological_space.exists_countable_dense`. If `α` is also known to be nonempty, then
`topological_space.dense_seq` provides a sequence `ℕ → α` with dense range, see
`topological_space.dense_range_dense_seq`.

If `α` is a uniform space with countably generated uniformity filter (e.g., an `emetric_space`),
then this condition is equivalent to `topological_space.second_countable_topology α`. In this case
the latter should be used as a typeclass argument in theorems because Lean can automatically deduce
`separable_space` from `second_countable_topology` but it can't deduce `second_countable_topology`
and `emetric_space`. -/
class separable_space : Prop where 
  exists_countable_dense : ∃ s : Set α, countable s ∧ Dense s

theorem exists_countable_dense [separable_space α] : ∃ s : Set α, countable s ∧ Dense s :=
  separable_space.exists_countable_dense

/-- A nonempty separable space admits a sequence with dense range. Instead of running `cases` on the
conclusion of this lemma, you might want to use `topological_space.dense_seq` and
`topological_space.dense_range_dense_seq`.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
theorem exists_dense_seq [separable_space α] [Nonempty α] : ∃ u : ℕ → α, DenseRange u :=
  by 
    obtain ⟨s : Set α, hs, s_dense⟩ := exists_countable_dense α 
    cases' countable_iff_exists_surjective.mp hs with u hu 
    exact ⟨u, s_dense.mono hu⟩

/-- A dense sequence in a non-empty separable topological space.

If `α` might be empty, then `exists_countable_dense` is the main way to use separability of `α`. -/
def dense_seq [separable_space α] [Nonempty α] : ℕ → α :=
  Classical.some (exists_dense_seq α)

/-- The sequence `dense_seq α` has dense range. -/
@[simp]
theorem dense_range_dense_seq [separable_space α] [Nonempty α] : DenseRange (dense_seq α) :=
  Classical.some_spec (exists_dense_seq α)

variable {α}

-- error in Topology.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a separable space, a family of nonempty disjoint open sets is countable. -/
theorem _root_.set.pairwise_disjoint.countable_of_is_open
[separable_space α]
{ι : Type*}
{s : ι → set α}
{a : set ι}
(h : a.pairwise_disjoint s)
(ha : ∀ i «expr ∈ » a, is_open (s i))
(h'a : ∀ i «expr ∈ » a, (s i).nonempty) : countable a :=
begin
  rcases [expr eq_empty_or_nonempty a, "with", ident rfl, "|", ident H],
  { exact [expr countable_empty] },
  haveI [] [":", expr inhabited α] [],
  { choose [] [ident i] [ident ia] ["using", expr H],
    choose [] [ident y] [ident hy] ["using", expr h'a i ia],
    exact [expr ⟨y⟩] },
  rcases [expr exists_countable_dense α, "with", "⟨", ident u, ",", ident u_count, ",", ident u_dense, "⟩"],
  have [] [":", expr ∀
   i, «expr ∈ »(i, a) → «expr∃ , »((y), «expr ∈ »(y, «expr ∩ »(s i, u)))] [":=", expr λ
   i hi, dense_iff_inter_open.1 u_dense (s i) (ha i hi) (h'a i hi)],
  choose ["!"] [ident f] [ident hf] ["using", expr this],
  have [ident f_inj] [":", expr inj_on f a] [],
  { assume [binders (i hi j hj hij)],
    have [] [":", expr «expr¬ »(disjoint (s i) (s j))] [],
    { rw [expr not_disjoint_iff_nonempty_inter] [],
      refine [expr ⟨f i, (hf i hi).1, _⟩],
      rw [expr hij] [],
      exact [expr (hf j hj).1] },
    contrapose ["!"] [ident this],
    exact [expr h i hi j hj this] },
  apply [expr countable_of_injective_of_countable_image f_inj],
  apply [expr u_count.mono _],
  exact [expr image_subset_iff.2 (λ i hi, (hf i hi).2)]
end

/-- In a separable space, a family of disjoint sets with nonempty interiors is countable. -/
theorem _root_.set.pairwise_disjoint.countable_of_nonempty_interior [separable_space α] {ι : Type _} {s : ι → Set α}
  {a : Set ι} (h : a.pairwise_disjoint s) (ha : ∀ i _ : i ∈ a, (Interior (s i)).Nonempty) : countable a :=
  (h.mono$ fun i => interior_subset).countable_of_is_open (fun i hi => is_open_interior) ha

end TopologicalSpace

open TopologicalSpace

-- error in Topology.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_topological_basis_pi
{ι : Type*}
{X : ι → Type*}
[∀ i, topological_space (X i)]
{T : ∀ i, set (set (X i))}
(cond : ∀
 i, is_topological_basis (T i)) : is_topological_basis {S : set (∀
 i, X i) | «expr∃ , »((U : ∀ i, set (X i))
 (F : finset ι), «expr ∧ »(∀ i, «expr ∈ »(i, F) → «expr ∈ »(U i, T i), «expr = »(S, (F : set ι).pi U)))} :=
begin
  refine [expr is_topological_basis_of_open_of_nhds _ _],
  { rintro ["_", "⟨", ident U, ",", ident F, ",", ident h1, ",", ident rfl, "⟩"],
    apply [expr is_open_set_pi F.finite_to_set],
    intros [ident i, ident hi],
    exact [expr (cond i).is_open (h1 i hi)] },
  { intros [ident a, ident U, ident ha, ident hU],
    obtain ["⟨", ident I, ",", ident t, ",", ident hta, ",", ident htU, "⟩", ":", expr «expr∃ , »((I : finset ι)
      (t : ∀ i : ι, set (X i)), «expr ∧ »(∀ i, «expr ∈ »(t i, expr𝓝() (a i)), «expr ⊆ »(set.pi «expr↑ »(I) t, U)))],
    { rw ["[", "<-", expr filter.mem_pi', ",", "<-", expr nhds_pi, "]"] [],
      exact [expr hU.mem_nhds ha] },
    have [] [":", expr ∀
     i, «expr∃ , »((V «expr ∈ » T i), «expr ∧ »(«expr ∈ »(a i, V), «expr ⊆ »(V, t i)))] [":=", expr λ
     i, (cond i).mem_nhds_iff.1 (hta i)],
    choose [] [ident V] [ident hVT, ident haV, ident hVt] [],
    exact [expr ⟨_, ⟨V, I, λ i hi, hVT i, rfl⟩, λ i hi, haV i, «expr $ »(pi_mono, λ i hi, hVt i).trans htU⟩] }
end

-- error in Topology.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_topological_basis_infi
{β : Type*}
{ι : Type*}
{X : ι → Type*}
[t : ∀ i, topological_space (X i)]
{T : ∀ i, set (set (X i))}
(cond : ∀ i, is_topological_basis (T i))
(f : ∀
 i, β → X i) : @is_topological_basis β «expr⨅ , »((i), induced (f i) (t i)) {S | «expr∃ , »((U : ∀ i, set (X i))
 (F : finset ι), «expr ∧ »(∀
  i, «expr ∈ »(i, F) → «expr ∈ »(U i, T i), «expr = »(S, «expr⋂ , »((i)
    (hi : «expr ∈ »(i, F)), «expr ⁻¹' »(f i, U i)))))} :=
begin
  convert [] [expr (is_topological_basis_pi cond).inducing (inducing_infi_to_pi _)] [],
  ext [] [ident V] [],
  split,
  { rintros ["⟨", ident U, ",", ident F, ",", ident h1, ",", ident h2, "⟩"],
    have [] [":", expr «expr = »((F : set ι).pi U, «expr⋂ , »((i : ι)
       (hi : «expr ∈ »(i, F)), «expr ⁻¹' »(λ z : ∀ j, X j, z i, U i)))] [],
    by { ext [] [] [],
      simp [] [] [] [] [] [] },
    refine [expr ⟨(F : set ι).pi U, ⟨U, F, h1, rfl⟩, _⟩],
    rw ["[", expr this, ",", expr h2, ",", expr set.preimage_Inter, "]"] [],
    congr' [1] [],
    ext1 [] [],
    rw [expr set.preimage_Inter] [],
    refl },
  { rintros ["⟨", ident U, ",", "⟨", ident U, ",", ident F, ",", ident h1, ",", ident rfl, "⟩", ",", ident h, "⟩"],
    refine [expr ⟨U, F, h1, _⟩],
    have [] [":", expr «expr = »((F : set ι).pi U, «expr⋂ , »((i : ι)
       (hi : «expr ∈ »(i, F)), «expr ⁻¹' »(λ z : ∀ j, X j, z i, U i)))] [],
    by { ext [] [] [],
      simp [] [] [] [] [] [] },
    rw ["[", "<-", expr h, ",", expr this, ",", expr set.preimage_Inter, "]"] [],
    congr' [1] [],
    ext1 [] [],
    rw [expr set.preimage_Inter] [],
    refl }
end

/-- If `α` is a separable space and `f : α → β` is a continuous map with dense range, then `β` is
a separable space as well. E.g., the completion of a separable uniform space is separable. -/
protected theorem DenseRange.separable_space {α β : Type _} [TopologicalSpace α] [separable_space α]
  [TopologicalSpace β] {f : α → β} (h : DenseRange f) (h' : Continuous f) : separable_space β :=
  let ⟨s, s_cnt, s_dense⟩ := exists_countable_dense α
  ⟨⟨f '' s, countable.image s_cnt f, h.dense_image h' s_dense⟩⟩

theorem Dense.exists_countable_dense_subset {α : Type _} [TopologicalSpace α] {s : Set α} [separable_space s]
  (hs : Dense s) : ∃ (t : _)(_ : t ⊆ s), countable t ∧ Dense t :=
  let ⟨t, htc, htd⟩ := exists_countable_dense s
  ⟨coeₓ '' t, image_subset_iff.2$ fun x _ => mem_preimage.2$ Subtype.coe_prop _, htc.image coeₓ,
    hs.dense_range_coe.dense_image continuous_subtype_val htd⟩

/-- Let `s` be a dense set in a topological space `α` with partial order structure. If `s` is a
separable space (e.g., if `α` has a second countable topology), then there exists a countable
dense subset `t ⊆ s` such that `t` contains bottom/top element of `α` when they exist and belong
to `s`. For a dense subset containing neither bot nor top elements, see
`dense.exists_countable_dense_subset_no_bot_top`. -/
theorem Dense.exists_countable_dense_subset_bot_top {α : Type _} [TopologicalSpace α] [PartialOrderₓ α] {s : Set α}
  [separable_space s] (hs : Dense s) :
  ∃ (t : _)(_ : t ⊆ s), countable t ∧ Dense t ∧ (∀ x, IsBot x → x ∈ s → x ∈ t) ∧ ∀ x, IsTop x → x ∈ s → x ∈ t :=
  by 
    rcases hs.exists_countable_dense_subset with ⟨t, hts, htc, htd⟩
    refine' ⟨(t ∪ ({ x | IsBot x } ∪ { x | IsTop x })) ∩ s, _, _, _, _, _⟩
    exacts[inter_subset_right _ _,
      (htc.union ((countable_is_bot α).union (countable_is_top α))).mono (inter_subset_left _ _),
      htd.mono (subset_inter (subset_union_left _ _) hts), fun x hx hxs => ⟨Or.inr$ Or.inl hx, hxs⟩,
      fun x hx hxs => ⟨Or.inr$ Or.inr hx, hxs⟩]

instance separable_space_univ {α : Type _} [TopologicalSpace α] [separable_space α] : separable_space (univ : Set α) :=
  (Equiv.Set.univ α).symm.Surjective.DenseRange.SeparableSpace (continuous_subtype_mk _ continuous_id)

/-- If `α` is a separable topological space with a partial order, then there exists a countable
dense set `s : set α` that contains those of both bottom and top elements of `α` that actually
exist. For a dense set containing neither bot nor top elements, see
`exists_countable_dense_no_bot_top`. -/
theorem exists_countable_dense_bot_top (α : Type _) [TopologicalSpace α] [separable_space α] [PartialOrderₓ α] :
  ∃ s : Set α, countable s ∧ Dense s ∧ (∀ x, IsBot x → x ∈ s) ∧ ∀ x, IsTop x → x ∈ s :=
  by 
    simpa using dense_univ.exists_countable_dense_subset_bot_top

namespace TopologicalSpace

universe u

variable (α : Type u) [t : TopologicalSpace α]

include t

/-- A first-countable space is one in which every point has a
  countable neighborhood basis. -/
class first_countable_topology : Prop where 
  nhds_generated_countable : ∀ a : α, (𝓝 a).IsCountablyGenerated

attribute [instance] first_countable_topology.nhds_generated_countable

namespace FirstCountableTopology

variable {α}

/-- In a first-countable space, a cluster point `x` of a sequence
is the limit of some subsequence. -/
theorem tendsto_subseq [first_countable_topology α] {u : ℕ → α} {x : α} (hx : MapClusterPt x at_top u) :
  ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ tendsto (u ∘ ψ) at_top (𝓝 x) :=
  subseq_tendsto_of_ne_bot hx

end FirstCountableTopology

variable {α}

instance is_countably_generated_nhds_within (x : α) [is_countably_generated (𝓝 x)] (s : Set α) :
  is_countably_generated (𝓝[s] x) :=
  inf.is_countably_generated _ _

variable (α)

/-- A second-countable space is one with a countable basis. -/
class second_countable_topology : Prop where 
  is_open_generated_countable{} : ∃ b : Set (Set α), countable b ∧ t = TopologicalSpace.generateFrom b

variable {α}

protected theorem is_topological_basis.second_countable_topology {b : Set (Set α)} (hb : is_topological_basis b)
  (hc : countable b) : second_countable_topology α :=
  ⟨⟨b, hc, hb.eq_generate_from⟩⟩

variable (α)

theorem exists_countable_basis [second_countable_topology α] :
  ∃ b : Set (Set α), countable b ∧ ∅ ∉ b ∧ is_topological_basis b :=
  let ⟨b, hb₁, hb₂⟩ := second_countable_topology.is_open_generated_countable α 
  let b' := (fun s => ⋂₀s) '' { s:Set (Set α) | finite s ∧ s ⊆ b ∧ (⋂₀s).Nonempty }
  ⟨b',
    ((countable_set_of_finite_subset hb₁).mono
          (by 
            simp only [←and_assoc]
            apply inter_subset_left)).Image
      _,
    fun ⟨s, ⟨_, _, hn⟩, hp⟩ => absurd hn (not_nonempty_iff_eq_empty.2 hp), is_topological_basis_of_subbasis hb₂⟩

/-- A countable topological basis of `α`. -/
def countable_basis [second_countable_topology α] : Set (Set α) :=
  (exists_countable_basis α).some

theorem countable_countable_basis [second_countable_topology α] : countable (countable_basis α) :=
  (exists_countable_basis α).some_spec.1

instance encodable_countable_basis [second_countable_topology α] : Encodable (countable_basis α) :=
  (countable_countable_basis α).toEncodable

theorem empty_nmem_countable_basis [second_countable_topology α] : ∅ ∉ countable_basis α :=
  (exists_countable_basis α).some_spec.2.1

theorem is_basis_countable_basis [second_countable_topology α] : is_topological_basis (countable_basis α) :=
  (exists_countable_basis α).some_spec.2.2

theorem eq_generate_from_countable_basis [second_countable_topology α] :
  ‹TopologicalSpace α› = generate_from (countable_basis α) :=
  (is_basis_countable_basis α).eq_generate_from

variable {α}

theorem is_open_of_mem_countable_basis [second_countable_topology α] {s : Set α} (hs : s ∈ countable_basis α) :
  IsOpen s :=
  (is_basis_countable_basis α).IsOpen hs

theorem nonempty_of_mem_countable_basis [second_countable_topology α] {s : Set α} (hs : s ∈ countable_basis α) :
  s.nonempty :=
  ne_empty_iff_nonempty.1$ ne_of_mem_of_not_mem hs$ empty_nmem_countable_basis α

variable (α)

instance (priority := 100) second_countable_topology.to_first_countable_topology [second_countable_topology α] :
  first_countable_topology α :=
  ⟨fun x =>
      has_countable_basis.is_countably_generated$
        ⟨(is_basis_countable_basis α).nhds_has_basis, (countable_countable_basis α).mono$ inter_subset_left _ _⟩⟩

/-- If `β` is a second-countable space, then its induced topology
via `f` on `α` is also second-countable. -/
theorem second_countable_topology_induced β [t : TopologicalSpace β] [second_countable_topology β] (f : α → β) :
  @second_countable_topology α (t.induced f) :=
  by 
    rcases second_countable_topology.is_open_generated_countable β with ⟨b, hb, eq⟩
    refine' { is_open_generated_countable := ⟨preimage f '' b, hb.image _, _⟩ }
    rw [Eq, induced_generate_from_eq]

instance subtype.second_countable_topology (s : Set α) [second_countable_topology α] : second_countable_topology s :=
  second_countable_topology_induced s α coeₓ

instance {β : Type _} [TopologicalSpace β] [second_countable_topology α] [second_countable_topology β] :
  second_countable_topology (α × β) :=
  ((is_basis_countable_basis α).Prod (is_basis_countable_basis β)).SecondCountableTopology$
    (countable_countable_basis α).Image2 (countable_countable_basis β) _

-- error in Topology.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance second_countable_topology_encodable
{ι : Type*}
{π : ι → Type*}
[encodable ι]
[t : ∀ a, topological_space (π a)]
[∀ a, second_countable_topology (π a)] : second_countable_topology (∀ a, π a) :=
begin
  have [] [":", expr «expr = »(t, λ a, generate_from (countable_basis (π a)))] [],
  from [expr funext (assume a, (is_basis_countable_basis (π a)).eq_generate_from)],
  rw ["[", expr this, ",", expr pi_generate_from_eq, "]"] [],
  constructor,
  refine [expr ⟨_, _, rfl⟩],
  have [] [":", expr countable {T : set (∀
    i, π i) | «expr∃ , »((I : finset ι)
    (s : ∀
     i : I, set (π i)), «expr ∧ »(∀
     i, «expr ∈ »(s i, countable_basis (π i)), «expr = »(T, {f | ∀ i : I, «expr ∈ »(f i, s i)})))}] [],
  { simp [] [] ["only"] ["[", expr set_of_exists, ",", "<-", expr exists_prop, "]"] [] [],
    refine [expr countable_Union (λ I, countable.bUnion _ (λ _ _, countable_singleton _))],
    change [expr countable {s : ∀ i : I, set (π i) | ∀ i, «expr ∈ »(s i, countable_basis (π i))}] [] [],
    exact [expr countable_pi (λ i, countable_countable_basis _)] },
  convert [] [expr this] ["using", 1],
  ext1 [] [ident T],
  split,
  { rintro ["⟨", ident s, ",", ident I, ",", ident hs, ",", ident rfl, "⟩"],
    refine [expr ⟨I, λ i, s i, λ i, hs i i.2, _⟩],
    simp [] [] ["only"] ["[", expr set.pi, ",", expr set_coe.forall', "]"] [] [],
    refl },
  { rintro ["⟨", ident I, ",", ident s, ",", ident hs, ",", ident rfl, "⟩"],
    rcases [expr @subtype.surjective_restrict ι (λ
      i, set (π i)) _ (λ i, «expr ∈ »(i, I)) s, "with", "⟨", ident s, ",", ident rfl, "⟩"],
    exact [expr ⟨s, I, λ i hi, hs ⟨i, hi⟩, «expr $ »(set.ext, λ f, subtype.forall)⟩] }
end

-- error in Topology.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance second_countable_topology_fintype
{ι : Type*}
{π : ι → Type*}
[fintype ι]
[t : ∀ a, topological_space (π a)]
[∀ a, second_countable_topology (π a)] : second_countable_topology (∀ a, π a) :=
by { letI [] [] [":=", expr fintype.encodable ι],
  exact [expr topological_space.second_countable_topology_encodable] }

instance (priority := 100) second_countable_topology.to_separable_space [second_countable_topology α] :
  separable_space α :=
  by 
    choose p hp using fun s : countable_basis α => nonempty_of_mem_countable_basis s.2 
    exact
      ⟨⟨range p, countable_range _,
          (is_basis_countable_basis α).dense_iff.2$ fun o ho _ => ⟨p ⟨o, ho⟩, hp _, mem_range_self _⟩⟩⟩

variable {α}

-- error in Topology.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A countable open cover induces a second-countable topology if all open covers
are themselves second countable. -/
theorem second_countable_topology_of_countable_cover
{ι}
[encodable ι]
{U : ι → set α}
[∀ i, second_countable_topology (U i)]
(Uo : ∀ i, is_open (U i))
(hc : «expr = »(«expr⋃ , »((i), U i), univ)) : second_countable_topology α :=
begin
  have [] [":", expr is_topological_basis «expr⋃ , »((i), «expr '' »(image (coe : U i → α), countable_basis (U i)))] [],
  from [expr is_topological_basis_of_cover Uo hc (λ i, is_basis_countable_basis (U i))],
  exact [expr this.second_countable_topology «expr $ »(countable_Union, λ i, (countable_countable_basis _).image _)]
end

-- error in Topology.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a second-countable space, an open set, given as a union of open sets,
is equal to the union of countably many of those sets. -/
theorem is_open_Union_countable
[second_countable_topology α]
{ι}
(s : ι → set α)
(H : ∀
 i, is_open (s i)) : «expr∃ , »((T : set ι), «expr ∧ »(countable T, «expr = »(«expr⋃ , »((i «expr ∈ » T), s i), «expr⋃ , »((i), s i)))) :=
begin
  let [ident B] [] [":=", expr {b ∈ countable_basis α | «expr∃ , »((i), «expr ⊆ »(b, s i))}],
  choose [] [ident f] [ident hf] ["using", expr λ b : B, b.2.2],
  haveI [] [":", expr encodable B] [":=", expr ((countable_countable_basis α).mono (sep_subset _ _)).to_encodable],
  refine [expr ⟨_, countable_range f, subset.antisymm (bUnion_subset_Union _ _) (sUnion_subset _)⟩],
  rintro ["_", "⟨", ident i, ",", ident rfl, "⟩", ident x, ident xs],
  rcases [expr (is_basis_countable_basis α).exists_subset_of_mem_open xs (H _), "with", "⟨", ident b, ",", ident hb, ",", ident xb, ",", ident bs, "⟩"],
  exact [expr ⟨_, ⟨_, rfl⟩, _, ⟨⟨⟨_, hb, _, bs⟩, rfl⟩, rfl⟩, hf _ (by exact [expr xb])⟩]
end

theorem is_open_sUnion_countable [second_countable_topology α] (S : Set (Set α)) (H : ∀ s _ : s ∈ S, IsOpen s) :
  ∃ T : Set (Set α), countable T ∧ T ⊆ S ∧ ⋃₀T = ⋃₀S :=
  let ⟨T, cT, hT⟩ := is_open_Union_countable (fun s : S => s.1) fun s => H s.1 s.2
  ⟨Subtype.val '' T, cT.image _, image_subset_iff.2$ fun ⟨x, xs⟩ xt => xs,
    by 
      rwa [sUnion_image, sUnion_eq_Union]⟩

/-- In a topological space with second countable topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
theorem countable_cover_nhds [second_countable_topology α] {f : α → Set α} (hf : ∀ x, f x ∈ 𝓝 x) :
  ∃ s : Set α, countable s ∧ (⋃(x : _)(_ : x ∈ s), f x) = univ :=
  by 
    rcases is_open_Union_countable (fun x => Interior (f x)) fun x => is_open_interior with ⟨s, hsc, hsU⟩
    suffices  : (⋃(x : _)(_ : x ∈ s), Interior (f x)) = univ 
    exact ⟨s, hsc, flip eq_univ_of_subset this (bUnion_mono$ fun _ _ => interior_subset)⟩
    simp only [hsU, eq_univ_iff_forall, mem_Union]
    exact fun x => ⟨x, mem_interior_iff_mem_nhds.2 (hf x)⟩

-- error in Topology.Bases: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem countable_cover_nhds_within
[second_countable_topology α]
{f : α → set α}
{s : set α}
(hf : ∀
 x «expr ∈ » s, «expr ∈ »(f x, «expr𝓝[ ] »(s, x))) : «expr∃ , »((t «expr ⊆ » s), «expr ∧ »(countable t, «expr ⊆ »(s, «expr⋃ , »((x «expr ∈ » t), f x)))) :=
begin
  have [] [":", expr ∀ x : s, «expr ∈ »(«expr ⁻¹' »(coe, f x), expr𝓝() x)] [],
  from [expr λ x, preimage_coe_mem_nhds_subtype.2 (hf x x.2)],
  rcases [expr countable_cover_nhds this, "with", "⟨", ident t, ",", ident htc, ",", ident htU, "⟩"],
  refine [expr ⟨«expr '' »(coe, t), subtype.coe_image_subset _ _, htc.image _, λ x hx, _⟩],
  simp [] [] ["only"] ["[", expr bUnion_image, ",", expr eq_univ_iff_forall, ",", "<-", expr preimage_Union, ",", expr mem_preimage, "]"] [] ["at", ident htU, "⊢"],
  exact [expr htU ⟨x, hx⟩]
end

end TopologicalSpace

open TopologicalSpace

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

protected theorem Inducing.second_countable_topology [second_countable_topology β] (hf : Inducing f) :
  second_countable_topology α :=
  by 
    rw [hf.1]
    exact second_countable_topology_induced α β f

protected theorem Embedding.second_countable_topology [second_countable_topology β] (hf : Embedding f) :
  second_countable_topology α :=
  hf.1.SecondCountableTopology

