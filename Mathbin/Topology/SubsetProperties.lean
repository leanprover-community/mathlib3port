import Mathbin.Order.Filter.Pi
import Mathbin.Topology.Bases
import Mathbin.Data.Finset.Order
import Mathbin.Data.Set.Accumulate
import Mathbin.Tactic.Tfae

/-!
# Properties of subsets of topological spaces

In this file we define various properties of subsets of a topological space, and some classes on
topological spaces.

## Main definitions

We define the following properties for sets in a topological space:

* `is_compact`: each open cover has a finite subcover. This is defined in mathlib using filters.
  The main property of a compact set is `is_compact.elim_finite_subcover`.
* `is_clopen`: a set that is both open and closed.
* `is_irreducible`: a nonempty set that has contains no non-trivial pair of disjoint opens.
  See also the section below in the module doc.

For each of these definitions (except for `is_clopen`), we also have a class stating that the whole
space satisfies that property:
`compact_space`, `irreducible_space`

Furthermore, we have three more classes:
* `locally_compact_space`: for every point `x`, every open neighborhood of `x` contains a compact
  neighborhood of `x`. The definition is formulated in terms of the neighborhood filter.
* `sigma_compact_space`: a space that is the union of a countably many compact subspaces;
* `noncompact_space`: a space that is not a compact space.

## On the definition of irreducible and connected sets/spaces

In informal mathematics, irreducible spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `is_preirreducible`.
In other words, the only difference is whether the empty space counts as irreducible.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/


open Set Filter Classical TopologicalSpace

open_locale Classical TopologicalSpace Filter

universe u v

variable {α : Type u} {β : Type v} {ι : Type _} {π : ι → Type _}

variable [TopologicalSpace α] [TopologicalSpace β] {s t : Set α}

section Compact

/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
    there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def IsCompact (s : Set α) :=
  ∀ ⦃f⦄ [ne_bot f], f ≤ 𝓟 s → ∃ a ∈ s, ClusterPt a f

/-- The complement to a compact set belongs to a filter `f` if it belongs to each filter
`𝓝 a ⊓ f`, `a ∈ s`. -/
theorem IsCompact.compl_mem_sets (hs : IsCompact s) {f : Filter α} (hf : ∀, ∀ a ∈ s, ∀, sᶜ ∈ 𝓝 a⊓f) : sᶜ ∈ f := by
  contrapose! hf
  simp only [not_mem_iff_inf_principal_compl, compl_compl, inf_assoc, ← exists_prop] at hf⊢
  exact @hs _ hf inf_le_right

/-- The complement to a compact set belongs to a filter `f` if each `a ∈ s` has a neighborhood `t`
within `s` such that `tᶜ` belongs to `f`. -/
theorem IsCompact.compl_mem_sets_of_nhds_within (hs : IsCompact s) {f : Filter α}
    (hf : ∀, ∀ a ∈ s, ∀, ∃ t ∈ 𝓝[s] a, tᶜ ∈ f) : sᶜ ∈ f := by
  refine' hs.compl_mem_sets fun a ha => _
  rcases hf a ha with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  rintro x ⟨h₁, h₂⟩ hs
  exact h₂ (h₁ hs)

/-- If `p : set α → Prop` is stable under restriction and union, and each point `x`
  of a compact set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_eliminator]
theorem IsCompact.induction_on {s : Set α} (hs : IsCompact s) {p : Set α → Prop} (he : p ∅)
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s) (hunion : ∀ ⦃s t⦄, p s → p t → p (s ∪ t))
    (hnhds : ∀, ∀ x ∈ s, ∀, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter α :=
    { Sets := { t | p (tᶜ) },
      univ_sets := by
        simpa,
      sets_of_superset := fun t₁ t₂ ht₁ ht => hmono (compl_subset_compl.2 ht) ht₁,
      inter_sets := fun t₁ t₂ ht₁ ht₂ => by
        simp [compl_inter, hunion ht₁ ht₂] }
  have : sᶜ ∈ f :=
    hs.compl_mem_sets_of_nhds_within
      (by
        simpa using hnhds)
  simpa

/-- The intersection of a compact set and a closed set is a compact set. -/
theorem IsCompact.inter_right (hs : IsCompact s) (ht : IsClosed t) : IsCompact (s ∩ t) := by
  intros f hnf hstf
  obtain ⟨a, hsa, ha⟩ : ∃ a ∈ s, ClusterPt a f := hs (le_transₓ hstf (le_principal_iff.2 (inter_subset_left _ _)))
  have : a ∈ t := ht.mem_of_nhds_within_ne_bot $ ha.mono $ le_transₓ hstf (le_principal_iff.2 (inter_subset_right _ _))
  exact ⟨a, ⟨hsa, this⟩, ha⟩

/-- The intersection of a closed set and a compact set is a compact set. -/
theorem IsCompact.inter_left (ht : IsCompact t) (hs : IsClosed s) : IsCompact (s ∩ t) :=
  inter_comm t s ▸ ht.inter_right hs

/-- The set difference of a compact set and an open set is a compact set. -/
theorem IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCompact (s \ t) :=
  hs.inter_right (is_closed_compl_iff.mpr ht)

/-- A closed subset of a compact set is a compact set. -/
theorem compact_of_is_closed_subset (hs : IsCompact s) (ht : IsClosed t) (h : t ⊆ s) : IsCompact t :=
  inter_eq_self_of_subset_right h ▸ hs.inter_right ht

theorem IsCompact.adherence_nhdset {f : Filter α} (hs : IsCompact s) (hf₂ : f ≤ 𝓟 s) (ht₁ : IsOpen t)
    (ht₂ : ∀, ∀ a ∈ s, ∀, ClusterPt a f → a ∈ t) : t ∈ f :=
  Classical.by_cases mem_of_eq_bot $ fun this : f⊓𝓟 (tᶜ) ≠ ⊥ =>
    let ⟨a, ha, (hfa : ClusterPt a $ f⊓𝓟 (tᶜ))⟩ := @hs ⟨this⟩ $ inf_le_of_left_le hf₂
    have : a ∈ t := ht₂ a ha hfa.of_inf_left
    have : tᶜ ∩ t ∈ 𝓝[tᶜ] a := inter_mem_nhds_within _ (IsOpen.mem_nhds ht₁ this)
    have A : 𝓝[tᶜ] a = ⊥ := empty_mem_iff_bot.1 $ compl_inter_self t ▸ this
    have : 𝓝[tᶜ] a ≠ ⊥ := hfa.of_inf_right.ne
    absurd A this

theorem is_compact_iff_ultrafilter_le_nhds : IsCompact s ↔ ∀ f : Ultrafilter α, ↑f ≤ 𝓟 s → ∃ a ∈ s, ↑f ≤ 𝓝 a := by
  refine' (forall_ne_bot_le_iff _).trans _
  · rintro f g hle ⟨a, has, haf⟩
    exact ⟨a, has, haf.mono hle⟩
    
  · simp only [Ultrafilter.cluster_pt_iff]
    

alias is_compact_iff_ultrafilter_le_nhds ↔ IsCompact.ultrafilter_le_nhds _

/-- For every open directed cover of a compact set, there exists a single element of the
cover which itself includes the set. -/
theorem IsCompact.elim_directed_cover {ι : Type v} [hι : Nonempty ι] (hs : IsCompact s) (U : ι → Set α)
    (hUo : ∀ i, IsOpen (U i)) (hsU : s ⊆ ⋃ i, U i) (hdU : Directed (· ⊆ ·) U) : ∃ i, s ⊆ U i :=
  hι.elim $ fun i₀ =>
    IsCompact.induction_on hs ⟨i₀, empty_subset _⟩ (fun s₁ s₂ hs ⟨i, hi⟩ => ⟨i, subset.trans hs hi⟩)
      (fun s₁ s₂ ⟨i, hi⟩ ⟨j, hj⟩ =>
        let ⟨k, hki, hkj⟩ := hdU i j
        ⟨k, union_subset (subset.trans hi hki) (subset.trans hj hkj)⟩)
      fun x hx =>
      let ⟨i, hi⟩ := mem_Union.1 (hsU hx)
      ⟨U i, mem_nhds_within_of_mem_nhds (IsOpen.mem_nhds (hUo i) hi), i, subset.refl _⟩

/-- For every open cover of a compact set, there exists a finite subcover. -/
theorem IsCompact.elim_finite_subcover {ι : Type v} (hs : IsCompact s) (U : ι → Set α) (hUo : ∀ i, IsOpen (U i))
    (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_directed_cover _ (fun t => is_open_bUnion $ fun i _ => hUo i) (Union_eq_Union_finset U ▸ hsU)
    (directed_of_sup $ fun t₁ t₂ h => bUnion_subset_bUnion_left h)

theorem IsCompact.elim_nhds_subcover' (hs : IsCompact s) (U : ∀, ∀ x ∈ s, ∀, Set α)
    (hU : ∀, ∀ x ∈ s, ∀, U x ‹x ∈ s› ∈ 𝓝 x) : ∃ t : Finset s, s ⊆ ⋃ x ∈ t, U (x : s) x.2 :=
  (hs.elim_finite_subcover (fun x : s => Interior (U x x.2)) (fun x => is_open_interior) fun x hx =>
        mem_Union.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 $ hU _ _⟩).imp $
    fun t ht => subset.trans ht $ bUnion_mono $ fun _ _ => interior_subset

theorem IsCompact.elim_nhds_subcover (hs : IsCompact s) (U : α → Set α) (hU : ∀, ∀ x ∈ s, ∀, U x ∈ 𝓝 x) :
    ∃ t : Finset α, (∀, ∀ x ∈ t, ∀, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x :=
  let ⟨t, ht⟩ := hs.elim_nhds_subcover' (fun x _ => U x) hU
  ⟨t.image coeₓ, fun x hx =>
    let ⟨y, hyt, hyx⟩ := Finset.mem_image.1 hx
    hyx ▸ y.2,
    by
    rwa [Finset.set_bUnion_finset_image]⟩

/-- For every family of closed sets whose intersection avoids a compact set,
there exists a finite subfamily whose intersection avoids this compact set. -/
theorem IsCompact.elim_finite_subfamily_closed {s : Set α} {ι : Type v} (hs : IsCompact s) (Z : ι → Set α)
    (hZc : ∀ i, IsClosed (Z i)) (hsZ : (s ∩ ⋂ i, Z i) = ∅) : ∃ t : Finset ι, (s ∩ ⋂ i ∈ t, Z i) = ∅ :=
  let ⟨t, ht⟩ :=
    hs.elim_finite_subcover (fun i => Z iᶜ) (fun i => (hZc i).is_open_compl)
      (by
        simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union, exists_prop, mem_inter_eq, not_and,
          iff_selfₓ, mem_Inter, mem_compl_eq] using hsZ)
  ⟨t, by
    simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union, exists_prop, mem_inter_eq, not_and,
      iff_selfₓ, mem_Inter, mem_compl_eq] using ht⟩

/-- If `s` is a compact set in a topological space `α` and `f : ι → set α` is a locally finite
family of sets, then `f i ∩ s` is nonempty only for a finitely many `i`. -/
theorem LocallyFinite.finite_nonempty_inter_compact {ι : Type _} {f : ι → Set α} (hf : LocallyFinite f) {s : Set α}
    (hs : IsCompact s) : finite { i | (f i ∩ s).Nonempty } := by
  choose U hxU hUf using hf
  rcases hs.elim_nhds_subcover U fun x _ => hxU x with ⟨t, -, hsU⟩
  refine' (t.finite_to_set.bUnion fun x _ => hUf x).Subset _
  rintro i ⟨x, hx⟩
  rcases mem_Union₂.1 (hsU hx.2) with ⟨c, hct, hcx⟩
  exact mem_bUnion hct ⟨x, hx.1, hcx⟩

/-- To show that a compact set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every finite subfamily. -/
theorem IsCompact.inter_Inter_nonempty {s : Set α} {ι : Type v} (hs : IsCompact s) (Z : ι → Set α)
    (hZc : ∀ i, IsClosed (Z i)) (hsZ : ∀ t : Finset ι, (s ∩ ⋂ i ∈ t, Z i).Nonempty) : (s ∩ ⋂ i, Z i).Nonempty := by
  simp only [← ne_empty_iff_nonempty] at hsZ⊢
  apply mt (hs.elim_finite_subfamily_closed Z hZc)
  push_neg
  exact hsZ

/-- Cantor's intersection theorem:
the intersection of a directed family of nonempty compact closed sets is nonempty. -/
theorem IsCompact.nonempty_Inter_of_directed_nonempty_compact_closed {ι : Type v} [hι : Nonempty ι] (Z : ι → Set α)
    (hZd : Directed (· ⊇ ·) Z) (hZn : ∀ i, (Z i).Nonempty) (hZc : ∀ i, IsCompact (Z i)) (hZcl : ∀ i, IsClosed (Z i)) :
    (⋂ i, Z i).Nonempty := by
  apply hι.elim
  intro i₀
  let Z' := fun i => Z i ∩ Z i₀
  suffices (⋂ i, Z' i).Nonempty by
    exact nonempty.mono (Inter_subset_Inter $ fun i => inter_subset_left (Z i) (Z i₀)) this
  rw [← ne_empty_iff_nonempty]
  intro H
  obtain ⟨t, ht⟩ : ∃ t : Finset ι, (Z i₀ ∩ ⋂ i ∈ t, Z' i) = ∅
  exact
    (hZc i₀).elim_finite_subfamily_closed Z' (fun i => IsClosed.inter (hZcl i) (hZcl i₀))
      (by
        rw [H, inter_empty])
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : ι, Z i₁ ⊆ Z i₀ ∧ ∀, ∀ i ∈ t, ∀, Z i₁ ⊆ Z' i := by
    rcases Directed.finset_le hZd t with ⟨i, hi⟩
    rcases hZd i i₀ with ⟨i₁, hi₁, hi₁₀⟩
    use i₁, hi₁₀
    intro j hj
    exact subset_inter (subset.trans hi₁ (hi j hj)) hi₁₀
  suffices (Z i₀ ∩ ⋂ i ∈ t, Z' i).Nonempty by
    rw [← ne_empty_iff_nonempty] at this
    contradiction
  refine' nonempty.mono _ (hZn i₁)
  exact subset_inter hi₁.left (subset_bInter hi₁.right)

/-- Cantor's intersection theorem for sequences indexed by `ℕ`:
the intersection of a decreasing sequence of nonempty compact closed sets is nonempty. -/
theorem IsCompact.nonempty_Inter_of_sequence_nonempty_compact_closed (Z : ℕ → Set α) (hZd : ∀ i, Z (i + 1) ⊆ Z i)
    (hZn : ∀ i, (Z i).Nonempty) (hZ0 : IsCompact (Z 0)) (hZcl : ∀ i, IsClosed (Z i)) : (⋂ i, Z i).Nonempty :=
  have Zmono : Antitone Z := antitone_nat_of_succ_le hZd
  have hZd : Directed (· ⊇ ·) Z := directed_of_sup Zmono
  have : ∀ i, Z i ⊆ Z 0 := fun i => Zmono $ zero_le i
  have hZc : ∀ i, IsCompact (Z i) := fun i => compact_of_is_closed_subset hZ0 (hZcl i) (this i)
  IsCompact.nonempty_Inter_of_directed_nonempty_compact_closed Z hZd hZn hZc hZcl

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (b' «expr ⊆ » b)
/-- For every open cover of a compact set, there exists a finite subcover. -/
theorem IsCompact.elim_finite_subcover_image {b : Set ι} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀, ∀ i ∈ b, ∀, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i ∈ b, c i) :
    ∃ (b' : _)(_ : b' ⊆ b), finite b' ∧ s ⊆ ⋃ i ∈ b', c i := by
  rcases hs.elim_finite_subcover (fun i => c i : b → Set α) _ _ with ⟨d, hd⟩ <;> [skip, simpa using hc₁,
    simpa using hc₂]
  refine' ⟨↑d.image coeₓ, _, Finset.finite_to_set _, _⟩
  · simp
    
  · rwa [Finset.coe_image, bUnion_image]
    

/-- A set `s` is compact if for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem is_compact_of_finite_subfamily_closed
    (h :
      ∀ {ι : Type u} Z : ι → Set α,
        (∀ i, IsClosed (Z i)) → (s ∩ ⋂ i, Z i) = ∅ → ∃ t : Finset ι, (s ∩ ⋂ i ∈ t, Z i) = ∅) :
    IsCompact s := fun f hfn hfs =>
  Classical.by_contradiction $ fun this : ¬∃ x ∈ s, ClusterPt x f =>
    have hf : ∀, ∀ x ∈ s, ∀, 𝓝 x⊓f = ⊥ := by
      simpa only [ClusterPt, not_exists, not_not, ne_bot_iff]
    have : ¬∃ x ∈ s, ∀, ∀ t ∈ f.sets, ∀, x ∈ Closure t := fun ⟨x, hxs, hx⟩ => by
      have : ∅ ∈ 𝓝 x⊓f := by
        rw [empty_mem_iff_bot, hf x hxs]
      let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := by
        rw [mem_inf_iff] at this <;> exact this
      have : ∅ ∈ 𝓝[t₂] x := by
        rw [ht, inter_comm]
        exact inter_mem_nhds_within _ ht₁
      have : 𝓝[t₂] x = ⊥ := by
        rwa [empty_mem_iff_bot] at this
      simp only [closure_eq_cluster_pts] at hx <;> exact (hx t₂ ht₂).Ne this
    let ⟨t, ht⟩ :=
      h (fun i : f.sets => Closure i.1) (fun i => is_closed_closure)
        (by
          simpa [eq_empty_iff_forall_not_mem, not_exists])
    have : (⋂ i ∈ t, Subtype.val i) ∈ f := t.Inter_mem_sets.2 $ fun i hi => i.2
    have : (s ∩ ⋂ i ∈ t, Subtype.val i) ∈ f := inter_mem (le_principal_iff.1 hfs) this
    have : ∅ ∈ f :=
      mem_of_superset this $ fun x ⟨hxs, hx⟩ =>
        let ⟨i, hit, hxi⟩ :=
          show ∃ i ∈ t, x ∉ Closure (Subtype.val i) by
            rw [eq_empty_iff_forall_not_mem] at ht
            simpa [hxs, not_forall] using ht x
        have : x ∈ Closure i.val :=
          subset_closure
            (by
              rw [mem_Inter₂] at hx
              exact hx i hit)
        show False from hxi this
    hfn.ne $ by
      rwa [empty_mem_iff_bot] at this

/-- A set `s` is compact if for every open cover of `s`, there exists a finite subcover. -/
theorem is_compact_of_finite_subcover
    (h : ∀ {ι : Type u} U : ι → Set α, (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i) :
    IsCompact s :=
  is_compact_of_finite_subfamily_closed $ fun ι Z hZc hsZ =>
    let ⟨t, ht⟩ :=
      h (fun i => Z iᶜ) (fun i => is_open_compl_iff.mpr $ hZc i)
        (by
          simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union, exists_prop, mem_inter_eq,
            not_and, iff_selfₓ, mem_Inter, mem_compl_eq] using hsZ)
    ⟨t, by
      simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union, exists_prop, mem_inter_eq, not_and,
        iff_selfₓ, mem_Inter, mem_compl_eq] using ht⟩

/-- A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover. -/
theorem is_compact_iff_finite_subcover :
    IsCompact s ↔
      ∀ {ι : Type u} U : ι → Set α, (∀ i, IsOpen (U i)) → (s ⊆ ⋃ i, U i) → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  ⟨fun hs ι => hs.elim_finite_subcover, is_compact_of_finite_subcover⟩

/-- A set `s` is compact if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem is_compact_iff_finite_subfamily_closed :
    IsCompact s ↔
      ∀ {ι : Type u} Z : ι → Set α,
        (∀ i, IsClosed (Z i)) → (s ∩ ⋂ i, Z i) = ∅ → ∃ t : Finset ι, (s ∩ ⋂ i ∈ t, Z i) = ∅ :=
  ⟨fun hs ι => hs.elim_finite_subfamily_closed, is_compact_of_finite_subfamily_closed⟩

/-- To show that `∀ y ∈ K, P x y` holds for `x` close enough to `x₀` when `K` is compact,
it is sufficient to show that for all `y₀ ∈ K` there `P x y` holds for `(x, y)` close enough
to `(x₀, y₀)`.
-/
theorem IsCompact.eventually_forall_of_forall_eventually {x₀ : α} {K : Set β} (hK : IsCompact K) {P : α → β → Prop}
    (hP : ∀, ∀ y ∈ K, ∀, ∀ᶠ z : α × β in 𝓝 (x₀, y), P z.1 z.2) : ∀ᶠ x in 𝓝 x₀, ∀, ∀ y ∈ K, ∀, P x y := by
  refine' hK.induction_on _ _ _ _
  · exact eventually_of_forall fun x y => False.elim
    
  · intro s t hst ht
    refine' ht.mono fun x h y hys => h y $ hst hys
    
  · intro s t hs ht
    filter_upwards [hs, ht]
    rintro x h1 h2 y (hys | hyt)
    exacts[h1 y hys, h2 y hyt]
    
  · intro y hyK
    specialize hP y hyK
    rw [nhds_prod_eq, eventually_prod_iff] at hP
    rcases hP with ⟨p, hp, q, hq, hpq⟩
    exact ⟨{ y | q y }, mem_nhds_within_of_mem_nhds hq, eventually_of_mem hp @hpq⟩
    

@[simp]
theorem is_compact_empty : IsCompact (∅ : Set α) := fun f hnf hsf =>
  Not.elim hnf.ne $ empty_mem_iff_bot.1 $ le_principal_iff.1 hsf

@[simp]
theorem is_compact_singleton {a : α} : IsCompact ({a} : Set α) := fun f hf hfa =>
  ⟨a, rfl,
    ClusterPt.of_le_nhds'
      (hfa.trans $ by
        simpa only [principal_singleton] using pure_le_nhds a)
      hf⟩

theorem Set.Subsingleton.is_compact {s : Set α} (hs : s.subsingleton) : IsCompact s :=
  subsingleton.induction_on hs is_compact_empty $ fun x => is_compact_singleton

theorem Set.Finite.compact_bUnion {s : Set ι} {f : ι → Set α} (hs : finite s) (hf : ∀, ∀ i ∈ s, ∀, IsCompact (f i)) :
    IsCompact (⋃ i ∈ s, f i) :=
  is_compact_of_finite_subcover $ fun ι U hUo hsU =>
    have : ∀ i : Subtype s, ∃ t : Finset ι, f i ⊆ ⋃ j ∈ t, U j := fun ⟨i, hi⟩ =>
      (hf i hi).elim_finite_subcover _ hUo
        (calc
          f i ⊆ ⋃ i ∈ s, f i := subset_bUnion_of_mem hi
          _ ⊆ ⋃ j, U j := hsU
          )
    let ⟨finite_subcovers, h⟩ := axiom_of_choice this
    have : Fintype (Subtype s) := hs.fintype
    let t := Finset.bUnion Finset.univ finite_subcovers
    have : (⋃ i ∈ s, f i) ⊆ ⋃ i ∈ t, U i :=
      bUnion_subset $ fun i hi =>
        calc
          f i ⊆ ⋃ j ∈ finite_subcovers ⟨i, hi⟩, U j := h ⟨i, hi⟩
          _ ⊆ ⋃ j ∈ t, U j := bUnion_subset_bUnion_left $ fun j hj => finset.mem_bUnion.mpr ⟨_, Finset.mem_univ _, hj⟩
          
    ⟨t, this⟩

theorem Finset.compact_bUnion (s : Finset ι) {f : ι → Set α} (hf : ∀, ∀ i ∈ s, ∀, IsCompact (f i)) :
    IsCompact (⋃ i ∈ s, f i) :=
  s.finite_to_set.compact_bUnion hf

theorem compact_accumulate {K : ℕ → Set α} (hK : ∀ n, IsCompact (K n)) (n : ℕ) : IsCompact (accumulate K n) :=
  (finite_le_nat n).compact_bUnion $ fun k _ => hK k

theorem compact_Union {f : ι → Set α} [Fintype ι] (h : ∀ i, IsCompact (f i)) : IsCompact (⋃ i, f i) := by
  rw [← bUnion_univ] <;> exact finite_univ.compact_bUnion fun i _ => h i

theorem Set.Finite.is_compact (hs : finite s) : IsCompact s :=
  bUnion_of_singleton s ▸ hs.compact_bUnion fun _ _ => is_compact_singleton

theorem finite_of_is_compact_of_discrete [DiscreteTopology α] (s : Set α) (hs : IsCompact s) : s.finite := by
  have := hs.elim_finite_subcover (fun x : α => ({x} : Set α)) fun x => is_open_discrete _
  simp only [Set.subset_univ, forall_prop_of_true, Set.Union_of_singleton] at this
  rcases this with ⟨t, ht⟩
  suffices (⋃ (i : α) (H : i ∈ t), {i} : Set α) = (t : Set α) by
    rw [this] at ht
    exact t.finite_to_set.subset ht
  ext x
  simp only [exists_prop, Set.mem_Union, Set.mem_singleton_iff, exists_eq_right', Finset.mem_coe]

theorem IsCompact.union (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ∪ t) := by
  rw [union_eq_Union] <;>
    exact
      compact_Union fun b => by
        cases b <;> assumption

theorem IsCompact.insert (hs : IsCompact s) a : IsCompact (insert a s) :=
  is_compact_singleton.union hs

/-- If `V : ι → set α` is a decreasing family of closed compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. We assume each `V i` is compact *and* closed because `α` is
not assumed to be Hausdorff. See `exists_subset_nhd_of_compact` for version assuming this. -/
theorem exists_subset_nhd_of_compact' {ι : Type _} [Nonempty ι] {V : ι → Set α} (hV : Directed (· ⊇ ·) V)
    (hV_cpct : ∀ i, IsCompact (V i)) (hV_closed : ∀ i, IsClosed (V i)) {U : Set α}
    (hU : ∀, ∀ x ∈ ⋂ i, V i, ∀, U ∈ 𝓝 x) : ∃ i, V i ⊆ U := by
  set Y := ⋂ i, V i
  obtain ⟨W, hsubW, W_op, hWU⟩ : ∃ W, Y ⊆ W ∧ IsOpen W ∧ W ⊆ U
  exact exists_open_set_nhds hU
  suffices ∃ i, V i ⊆ W by
    rcases this with ⟨i, hi⟩
    refine' ⟨i, Set.Subset.trans hi hWU⟩
  by_contra H
  push_neg  at H
  replace H : ∀ i, (V i ∩ Wᶜ).Nonempty := fun i => set.inter_compl_nonempty_iff.mpr (H i)
  have : (⋂ i, V i ∩ Wᶜ).Nonempty := by
    apply IsCompact.nonempty_Inter_of_directed_nonempty_compact_closed _ _ H
    · intro i
      exact (hV_cpct i).inter_right W_op.is_closed_compl
      
    · intro i
      apply (hV_closed i).inter W_op.is_closed_compl
      
    · intro i j
      rcases hV i j with ⟨k, hki, hkj⟩
      use k
      constructor <;> intro x <;> simp only [and_imp, mem_inter_eq, mem_compl_eq] <;> tauto
      
  have : ¬(⋂ i : ι, V i) ⊆ W := by
    simpa [← Inter_inter, inter_compl_nonempty_iff]
  contradiction

namespace Filter

/-- `filter.cocompact` is the filter generated by complements to compact sets. -/
def cocompact (α : Type _) [TopologicalSpace α] : Filter α :=
  ⨅ (s : Set α) (hs : IsCompact s), 𝓟 (sᶜ)

theorem has_basis_cocompact : (cocompact α).HasBasis IsCompact compl :=
  has_basis_binfi_principal'
    (fun s hs t ht =>
      ⟨s ∪ t, hs.union ht, compl_subset_compl.2 (subset_union_left s t), compl_subset_compl.2 (subset_union_right s t)⟩)
    ⟨∅, is_compact_empty⟩

theorem mem_cocompact : s ∈ cocompact α ↔ ∃ t, IsCompact t ∧ tᶜ ⊆ s :=
  has_basis_cocompact.mem_iff.trans $ exists_congr $ fun t => exists_prop

theorem mem_cocompact' : s ∈ cocompact α ↔ ∃ t, IsCompact t ∧ sᶜ ⊆ t :=
  mem_cocompact.trans $ exists_congr $ fun t => and_congr_right $ fun ht => compl_subset_comm

theorem _root_.is_compact.compl_mem_cocompact (hs : IsCompact s) : sᶜ ∈ Filter.cocompact α :=
  has_basis_cocompact.mem_of_mem hs

/-- `filter.coclosed_compact` is the filter generated by complements to closed compact sets.
In a Hausdorff space, this is the same as `filter.cocompact`. -/
def coclosed_compact (α : Type _) [TopologicalSpace α] : Filter α :=
  ⨅ (s : Set α) (h₁ : IsClosed s) (h₂ : IsCompact s), 𝓟 (sᶜ)

theorem has_basis_coclosed_compact : (Filter.coclosedCompact α).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl := by
  simp only [Filter.coclosedCompact, infi_and']
  refine' has_basis_binfi_principal' _ ⟨∅, is_closed_empty, is_compact_empty⟩
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
  exact
    ⟨s ∪ t,
      ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 (subset_union_left _ _),
        compl_subset_compl.2 (subset_union_right _ _)⟩⟩

theorem mem_coclosed_compact : s ∈ coclosed_compact α ↔ ∃ t, IsClosed t ∧ IsCompact t ∧ tᶜ ⊆ s := by
  simp [has_basis_coclosed_compact.mem_iff, and_assoc]

theorem mem_coclosed_compact' : s ∈ coclosed_compact α ↔ ∃ t, IsClosed t ∧ IsCompact t ∧ sᶜ ⊆ t := by
  simp only [mem_coclosed_compact, compl_subset_comm]

theorem cocompact_le_coclosed_compact : cocompact α ≤ coclosed_compact α :=
  infi_le_infi $ fun s => le_infi $ fun _ => le_rfl

end Filter

section TubeLemma

/-- `nhds_contain_boxes s t` means that any open neighborhood of `s × t` in `α × β` includes
a product of an open neighborhood of `s` by an open neighborhood of `t`. -/
def NhdsContainBoxes (s : Set α) (t : Set β) : Prop :=
  ∀ n : Set (α × β) hn : IsOpen n hp : s ×ˢ t ⊆ n,
    ∃ (u : Set α)(v : Set β), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n

theorem NhdsContainBoxes.symm {s : Set α} {t : Set β} : NhdsContainBoxes s t → NhdsContainBoxes t s := fun H n hn hp =>
  let ⟨u, v, uo, vo, su, tv, p⟩ :=
    H (Prod.swap ⁻¹' n) (hn.preimage continuous_swap)
      (by
        rwa [← image_subset_iff, image_swap_prod])
  ⟨v, u, vo, uo, tv, su, by
    rwa [← image_subset_iff, image_swap_prod] at p⟩

theorem NhdsContainBoxes.comm {s : Set α} {t : Set β} : NhdsContainBoxes s t ↔ NhdsContainBoxes t s :=
  Iff.intro NhdsContainBoxes.symm NhdsContainBoxes.symm

theorem nhds_contain_boxes_of_singleton {x : α} {y : β} : NhdsContainBoxes ({x} : Set α) ({y} : Set β) := fun n hn hp =>
  let ⟨u, v, uo, vo, xu, yv, hp'⟩ :=
    is_open_prod_iff.mp hn x y
      (hp $ by
        simp )
  ⟨u, v, uo, vo, by
    simpa, by
    simpa, hp'⟩

theorem nhds_contain_boxes_of_compact {s : Set α} (hs : IsCompact s) (t : Set β)
    (H : ∀, ∀ x ∈ s, ∀, NhdsContainBoxes ({x} : Set α) t) : NhdsContainBoxes s t := fun n hn hp =>
  have : ∀ x : s, ∃ uv : Set α × Set β, IsOpen uv.1 ∧ IsOpen uv.2 ∧ {↑x} ⊆ uv.1 ∧ t ⊆ uv.2 ∧ uv.1 ×ˢ uv.2 ⊆ n :=
    fun ⟨x, hx⟩ =>
    have : ({x} : Set α) ×ˢ t ⊆ n :=
      subset.trans
        (prod_mono
          (by
            simpa)
          subset.rfl)
        hp
    let ⟨ux, vx, H1⟩ := H x hx n hn this
    ⟨⟨ux, vx⟩, H1⟩
  let ⟨uvs, h⟩ := Classical.axiom_of_choice this
  have us_cover : s ⊆ ⋃ i, (uvs i).1 := fun x hx =>
    subset_Union _ ⟨x, hx⟩
      (by
        simpa using (h ⟨x, hx⟩).2.2.1)
  let ⟨s0, s0_cover⟩ := hs.elim_finite_subcover _ (fun i => (h i).1) us_cover
  let u := ⋃ i ∈ s0, (uvs i).1
  let v := ⋂ i ∈ s0, (uvs i).2
  have : IsOpen u := is_open_bUnion fun i _ => (h i).1
  have : IsOpen v := is_open_bInter s0.finite_to_set fun i _ => (h i).2.1
  have : t ⊆ v := subset_bInter fun i _ => (h i).2.2.2.1
  have : u ×ˢ v ⊆ n := fun ⟨x', y'⟩ ⟨hx', hy'⟩ =>
    have : ∃ i ∈ s0, x' ∈ (uvs i).1 := by
      simpa using hx'
    let ⟨i, is0, hi⟩ := this
    (h i).2.2.2.2 ⟨hi, (bInter_subset_of_mem is0 : v ⊆ (uvs i).2) hy'⟩
  ⟨u, v, ‹IsOpen u›, ‹IsOpen v›, s0_cover, ‹t ⊆ v›, ‹u ×ˢ v ⊆ n›⟩

/-- If `s` and `t` are compact sets and `n` is an open neighborhood of `s × t`, then there exist
open neighborhoods `u ⊇ s` and `v ⊇ t` such that `u × v ⊆ n`. -/
theorem generalized_tube_lemma {s : Set α} (hs : IsCompact s) {t : Set β} (ht : IsCompact t) {n : Set (α × β)}
    (hn : IsOpen n) (hp : s ×ˢ t ⊆ n) : ∃ (u : Set α)(v : Set β), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n :=
  have :=
    nhds_contain_boxes_of_compact hs t $ fun x _ =>
      NhdsContainBoxes.symm $ nhds_contain_boxes_of_compact ht {x} $ fun y _ => nhds_contain_boxes_of_singleton
  this n hn hp

end TubeLemma

/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
class CompactSpace (α : Type _) [TopologicalSpace α] : Prop where
  compact_univ : IsCompact (univ : Set α)

instance (priority := 10) Subsingleton.compact_space [Subsingleton α] : CompactSpace α :=
  ⟨subsingleton_univ.IsCompact⟩

theorem is_compact_univ_iff : IsCompact (univ : Set α) ↔ CompactSpace α :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

theorem compact_univ [h : CompactSpace α] : IsCompact (univ : Set α) :=
  h.compact_univ

theorem cluster_point_of_compact [CompactSpace α] (f : Filter α) [ne_bot f] : ∃ x, ClusterPt x f := by
  simpa using
    compact_univ
      (show f ≤ 𝓟 univ by
        simp )

theorem CompactSpace.elim_nhds_subcover [CompactSpace α] (U : α → Set α) (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset α, (⋃ x ∈ t, U x) = ⊤ := by
  obtain ⟨t, -, s⟩ := IsCompact.elim_nhds_subcover compact_univ U fun x m => hU x
  exact
    ⟨t, by
      rw [eq_top_iff]
      exact s⟩

theorem compact_space_of_finite_subfamily_closed
    (h : ∀ {ι : Type u} Z : ι → Set α, (∀ i, IsClosed (Z i)) → (⋂ i, Z i) = ∅ → ∃ t : Finset ι, (⋂ i ∈ t, Z i) = ∅) :
    CompactSpace α :=
  { compact_univ := by
      apply is_compact_of_finite_subfamily_closed
      intro ι Z
      specialize h Z
      simpa using h }

theorem IsClosed.is_compact [CompactSpace α] {s : Set α} (h : IsClosed s) : IsCompact s :=
  compact_of_is_closed_subset compact_univ h (subset_univ _)

/-- `α` is a noncompact topological space if it not a compact space. -/
class NoncompactSpace (α : Type _) [TopologicalSpace α] : Prop where
  noncompact_univ {} : ¬IsCompact (univ : Set α)

export NoncompactSpace (noncompact_univ)

theorem IsCompact.ne_univ [NoncompactSpace α] {s : Set α} (hs : IsCompact s) : s ≠ univ := fun h =>
  noncompact_univ α (h ▸ hs)

instance [NoncompactSpace α] : ne_bot (Filter.cocompact α) := by
  refine' filter.has_basis_cocompact.ne_bot_iff.2 fun s hs => _
  contrapose hs
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs
  rw [hs]
  exact noncompact_univ α

instance [NoncompactSpace α] : ne_bot (Filter.coclosedCompact α) :=
  ne_bot_of_le Filter.cocompact_le_coclosed_compact

theorem noncompact_space_of_ne_bot (h : ne_bot (Filter.cocompact α)) : NoncompactSpace α :=
  ⟨fun h' => (Filter.nonempty_of_mem h'.compl_mem_cocompact).ne_empty compl_univ⟩

theorem Filter.cocompact_ne_bot_iff : ne_bot (Filter.cocompact α) ↔ NoncompactSpace α :=
  ⟨noncompact_space_of_ne_bot, @Filter.cocompact.Filter.ne_bot _ _⟩

theorem not_compact_space_iff : ¬CompactSpace α ↔ NoncompactSpace α :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩, fun ⟨h₁⟩ ⟨h₂⟩ => h₁ h₂⟩

/-- A compact discrete space is finite. -/
noncomputable def fintypeOfCompactOfDiscrete [CompactSpace α] [DiscreteTopology α] : Fintype α :=
  fintype_of_univ_finite $ finite_of_is_compact_of_discrete _ compact_univ

theorem finite_cover_nhds_interior [CompactSpace α] {U : α → Set α} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset α, (⋃ x ∈ t, Interior (U x)) = univ :=
  let ⟨t, ht⟩ :=
    compact_univ.elim_finite_subcover (fun x => Interior (U x)) (fun x => is_open_interior) fun x _ =>
      mem_Union.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  ⟨t, univ_subset_iff.1 ht⟩

theorem finite_cover_nhds [CompactSpace α] {U : α → Set α} (hU : ∀ x, U x ∈ 𝓝 x) :
    ∃ t : Finset α, (⋃ x ∈ t, U x) = univ :=
  let ⟨t, ht⟩ := finite_cover_nhds_interior hU
  ⟨t, univ_subset_iff.1 $ ht ▸ bUnion_mono fun x hx => interior_subset⟩

/-- If `α` is a compact space, then a locally finite family of sets of `α` can have only finitely
many nonempty elements. -/
theorem LocallyFinite.finite_nonempty_of_compact {ι : Type _} [CompactSpace α] {f : ι → Set α} (hf : LocallyFinite f) :
    finite { i | (f i).Nonempty } := by
  simpa only [inter_univ] using hf.finite_nonempty_inter_compact compact_univ

/-- If `α` is a compact space, then a locally finite family of nonempty sets of `α` can have only
finitely many elements, `set.finite` version. -/
theorem LocallyFinite.finite_of_compact {ι : Type _} [CompactSpace α] {f : ι → Set α} (hf : LocallyFinite f)
    (hne : ∀ i, (f i).Nonempty) : finite (univ : Set ι) := by
  simpa only [hne] using hf.finite_nonempty_of_compact

/-- If `α` is a compact space, then a locally finite family of nonempty sets of `α` can have only
finitely many elements, `fintype` version. -/
noncomputable def LocallyFinite.fintypeOfCompact {ι : Type _} [CompactSpace α] {f : ι → Set α} (hf : LocallyFinite f)
    (hne : ∀ i, (f i).Nonempty) : Fintype ι :=
  fintype_of_univ_finite (hf.finite_of_compact hne)

theorem IsCompact.image_of_continuous_on {f : α → β} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s) :=
  by
  intro l lne ls
  have : ne_bot (l.comap f⊓𝓟 s) := comap_inf_principal_ne_bot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ClusterPt a (l.comap f⊓𝓟 s) := @hs this inf_le_right
  use f a, mem_image_of_mem f has
  have : tendsto f (𝓝 a⊓(comap f l⊓𝓟 s)) (𝓝 (f a)⊓l) := by
    convert (hf a has).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact @tendsto.ne_bot _ this ha

theorem IsCompact.image {f : α → β} (hs : IsCompact s) (hf : Continuous f) : IsCompact (f '' s) :=
  hs.image_of_continuous_on hf.continuous_on

/-- The comap of the cocompact filter on `β` by a continuous function `f : α → β` is less than or
equal to the cocompact filter on `α`.
This is a reformulation of the fact that images of compact sets are compact. -/
theorem Filter.comap_cocompact {f : α → β} (hf : Continuous f) : (Filter.cocompact β).comap f ≤ Filter.cocompact α := by
  rw [(filter.has_basis_cocompact.comap f).le_basis_iff Filter.has_basis_cocompact]
  intro t ht
  refine' ⟨f '' t, ht.image hf, _⟩
  simpa using t.subset_preimage_image f

theorem is_compact_range [CompactSpace α] {f : α → β} (hf : Continuous f) : IsCompact (range f) := by
  rw [← image_univ] <;> exact compact_univ.image hf

/-- If X is is_compact then pr₂ : X × Y → Y is a closed map -/
theorem is_closed_proj_of_is_compact {X : Type _} [TopologicalSpace X] [CompactSpace X] {Y : Type _}
    [TopologicalSpace Y] : IsClosedMap (Prod.snd : X × Y → Y) := by
  set πX := (Prod.fst : X × Y → X)
  set πY := (Prod.snd : X × Y → Y)
  intro C(hC : IsClosed C)
  rw [is_closed_iff_cluster_pt] at hC⊢
  intro y(y_closure : ClusterPt y $ 𝓟 (πY '' C))
  have : ne_bot (map πX (comap πY (𝓝 y)⊓𝓟 C)) := by
    suffices ne_bot (map πY (comap πY (𝓝 y)⊓𝓟 C)) by
      simpa only [map_ne_bot_iff]
    convert y_closure
    calc map πY (comap πY (𝓝 y)⊓𝓟 C) = 𝓝 y⊓map πY (𝓟 C) := Filter.push_pull' _ _ _ _ = 𝓝 y⊓𝓟 (πY '' C) := by
        rw [map_principal]
  skip
  obtain ⟨x, hx⟩ : ∃ x, ClusterPt x (map πX (comap πY (𝓝 y)⊓𝓟 C))
  exact cluster_point_of_compact _
  refine'
    ⟨⟨x, y⟩, _, by
      simp [πY]⟩
  apply hC
  rw [ClusterPt, ← Filter.map_ne_bot_iff πX]
  convert hx
  calc map πX (𝓝 (x, y)⊓𝓟 C) = map πX (comap πX (𝓝 x)⊓comap πY (𝓝 y)⊓𝓟 C) := by
      rw [nhds_prod_eq, Filter.prod]_ = map πX (comap πY (𝓝 y)⊓𝓟 C⊓comap πX (𝓝 x)) := by
      ac_rfl _ = map πX (comap πY (𝓝 y)⊓𝓟 C)⊓𝓝 x := by
      rw [Filter.push_pull]_ = 𝓝 x⊓map πX (comap πY (𝓝 y)⊓𝓟 C) := by
      rw [inf_comm]

theorem exists_subset_nhd_of_compact_space [CompactSpace α] {ι : Type _} [Nonempty ι] {V : ι → Set α}
    (hV : Directed (· ⊇ ·) V) (hV_closed : ∀ i, IsClosed (V i)) {U : Set α} (hU : ∀, ∀ x ∈ ⋂ i, V i, ∀, U ∈ 𝓝 x) :
    ∃ i, V i ⊆ U :=
  exists_subset_nhd_of_compact' hV (fun i => (hV_closed i).IsCompact) hV_closed hU

/-- If `f : α → β` is an `inducing` map, then the image `f '' s` of a set `s` is compact if and only
if the set `s` is closed. -/
theorem Inducing.is_compact_iff {f : α → β} (hf : Inducing f) {s : Set α} : IsCompact (f '' s) ↔ IsCompact s := by
  refine' ⟨_, fun hs => hs.image hf.continuous⟩
  intros hs F F_ne_bot F_le
  obtain ⟨_, ⟨x, x_in : x ∈ s, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs
      (calc
        map f F ≤ map f (𝓟 s) := map_mono F_le
        _ = 𝓟 (f '' s) := map_principal
        )
  use x, x_in
  suffices (map f (𝓝 x⊓F)).ne_bot by
    simpa [Filter.map_ne_bot_iff]
  rwa
    [calc
      map f (𝓝 x⊓F) = map f ((comap f $ 𝓝 $ f x)⊓F) := by
        rw [hf.nhds_eq_comap]
      _ = 𝓝 (f x)⊓map f F := Filter.push_pull' _ _ _
      ]

/-- If `f : α → β` is an `embedding` (or more generally, an `inducing` map, see
`inducing.is_compact_iff`), then the image `f '' s` of a set `s` is compact if and only if the set
`s` is closed. -/
theorem Embedding.is_compact_iff_is_compact_image {f : α → β} (hf : Embedding f) : IsCompact s ↔ IsCompact (f '' s) :=
  hf.to_inducing.is_compact_iff.symm

/-- The preimage of a compact set under a closed embedding is a compact set. -/
theorem ClosedEmbedding.is_compact_preimage {f : α → β} (hf : ClosedEmbedding f) {K : Set β} (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) := by
  replace hK := hK.inter_right hf.closed_range
  rwa [← hf.to_inducing.is_compact_iff, image_preimage_eq_inter_range]

/-- A closed embedding is proper, ie, inverse images of compact sets are contained in compacts.
Moreover, the preimage of a compact set is compact, see `closed_embedding.is_compact_preimage`. -/
theorem ClosedEmbedding.tendsto_cocompact {f : α → β} (hf : ClosedEmbedding f) :
    tendsto f (Filter.cocompact α) (Filter.cocompact β) :=
  Filter.has_basis_cocompact.tendsto_right_iff.mpr $ fun K hK => (hf.is_compact_preimage hK).compl_mem_cocompact

theorem compact_iff_compact_in_subtype {p : α → Prop} {s : Set { a // p a }} :
    IsCompact s ↔ IsCompact ((coeₓ : _ → α) '' s) :=
  embedding_subtype_coe.is_compact_iff_is_compact_image

theorem is_compact_iff_is_compact_univ {s : Set α} : IsCompact s ↔ IsCompact (univ : Set s) := by
  rw [compact_iff_compact_in_subtype, image_univ, Subtype.range_coe] <;> rfl

theorem is_compact_iff_compact_space {s : Set α} : IsCompact s ↔ CompactSpace s :=
  is_compact_iff_is_compact_univ.trans ⟨fun h => ⟨h⟩, @CompactSpace.compact_univ _ _⟩

protected theorem ClosedEmbedding.noncompact_space [NoncompactSpace α] {f : α → β} (hf : ClosedEmbedding f) :
    NoncompactSpace β :=
  noncompact_space_of_ne_bot hf.tendsto_cocompact.ne_bot

protected theorem ClosedEmbedding.compact_space [h : CompactSpace β] {f : α → β} (hf : ClosedEmbedding f) :
    CompactSpace α := by
  contrapose! h
  rw [not_compact_space_iff] at h⊢
  exact hf.noncompact_space

theorem IsCompact.prod {s : Set α} {t : Set β} (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s ×ˢ t) := by
  rw [is_compact_iff_ultrafilter_le_nhds] at hs ht⊢
  intro f hfs
  rw [le_principal_iff] at hfs
  obtain ⟨a : α, sa : a ∈ s, ha : map Prod.fst (↑f) ≤ 𝓝 a⟩ :=
    hs (f.map Prod.fst) (le_principal_iff.2 $ mem_map.2 $ mem_of_superset hfs fun x => And.left)
  obtain ⟨b : β, tb : b ∈ t, hb : map Prod.snd (↑f) ≤ 𝓝 b⟩ :=
    ht (f.map Prod.snd) (le_principal_iff.2 $ mem_map.2 $ mem_of_superset hfs fun x => And.right)
  rw [map_le_iff_le_comap] at ha hb
  refine' ⟨⟨a, b⟩, ⟨sa, tb⟩, _⟩
  rw [nhds_prod_eq]
  exact le_inf ha hb

/-- Finite topological spaces are compact. -/
instance (priority := 100) Fintype.compact_space [Fintype α] : CompactSpace α where
  compact_univ := finite_univ.IsCompact

/-- The product of two compact spaces is compact. -/
instance [CompactSpace α] [CompactSpace β] : CompactSpace (α × β) :=
  ⟨by
    rw [← univ_prod_univ]
    exact compact_univ.prod compact_univ⟩

/-- The disjoint union of two compact spaces is compact. -/
instance [CompactSpace α] [CompactSpace β] : CompactSpace (Sum α β) :=
  ⟨by
    rw [← range_inl_union_range_inr]
    exact (is_compact_range continuous_inl).union (is_compact_range continuous_inr)⟩

instance [Fintype ι] [∀ i, TopologicalSpace (π i)] [∀ i, CompactSpace (π i)] : CompactSpace (Σ i, π i) := by
  refine' ⟨_⟩
  rw [sigma.univ]
  exact compact_Union fun i => is_compact_range continuous_sigma_mk

/-- The coproduct of the cocompact filters on two topological spaces is the cocompact filter on
their product. -/
theorem Filter.coprod_cocompact : (Filter.cocompact α).coprod (Filter.cocompact β) = Filter.cocompact (α × β) := by
  ext S
  simp only [mem_coprod_iff, exists_prop, mem_comap, Filter.mem_cocompact]
  constructor
  · rintro ⟨⟨A, ⟨t, ht, hAt⟩, hAS⟩, B, ⟨t', ht', hBt'⟩, hBS⟩
    refine' ⟨t ×ˢ t', ht.prod ht', _⟩
    refine' subset.trans _ (union_subset hAS hBS)
    rw [compl_subset_comm] at hAt hBt'⊢
    refine' subset.trans _ (Set.prod_mono hAt hBt')
    intro x
    simp only [compl_union, mem_inter_eq, mem_prod, mem_preimage, mem_compl_eq]
    tauto
    
  · rintro ⟨t, ht, htS⟩
    refine' ⟨⟨(Prod.fst '' t)ᶜ, _, _⟩, ⟨(Prod.snd '' t)ᶜ, _, _⟩⟩
    · exact ⟨Prod.fst '' t, ht.image continuous_fst, subset.rfl⟩
      
    · rw [preimage_compl]
      rw [compl_subset_comm] at htS⊢
      exact subset.trans htS (subset_preimage_image Prod.fst _)
      
    · exact ⟨Prod.snd '' t, ht.image continuous_snd, subset.rfl⟩
      
    · rw [preimage_compl]
      rw [compl_subset_comm] at htS⊢
      exact subset.trans htS (subset_preimage_image Prod.snd _)
      
    

theorem Prod.noncompact_space_iff :
    NoncompactSpace (α × β) ↔ NoncompactSpace α ∧ Nonempty β ∨ Nonempty α ∧ NoncompactSpace β := by
  simp [← Filter.cocompact_ne_bot_iff, ← Filter.coprod_cocompact, Filter.coprod_ne_bot_iff]

instance (priority := 100) Prod.noncompact_space_left [NoncompactSpace α] [Nonempty β] : NoncompactSpace (α × β) :=
  Prod.noncompact_space_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

instance (priority := 100) Prod.noncompact_space_right [Nonempty α] [NoncompactSpace β] : NoncompactSpace (α × β) :=
  Prod.noncompact_space_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

section Tychonoff

variable [∀ i, TopologicalSpace (π i)]

/-- **Tychonoff's theorem** -/
theorem is_compact_pi_infinite {s : ∀ i, Set (π i)} :
    (∀ i, IsCompact (s i)) → IsCompact { x : ∀ i, π i | ∀ i, x i ∈ s i } := by
  simp only [is_compact_iff_ultrafilter_le_nhds, nhds_pi, Filter.pi, exists_prop, mem_set_of_eq, le_infi_iff,
    le_principal_iff]
  intro h f hfs
  have : ∀ i : ι, ∃ a, a ∈ s i ∧ tendsto (fun x : ∀ i : ι, π i => x i) f (𝓝 a) := by
    refine' fun i => h i (f.map _) (mem_map.2 _)
    exact mem_of_superset hfs fun x hx => hx i
  choose a ha
  exact ⟨a, fun i => (ha i).left, fun i => (ha i).right.le_comap⟩

/-- A version of Tychonoff's theorem that uses `set.pi`. -/
theorem is_compact_univ_pi {s : ∀ i, Set (π i)} (h : ∀ i, IsCompact (s i)) : IsCompact (pi univ s) := by
  convert is_compact_pi_infinite h
  simp only [← mem_univ_pi, set_of_mem_eq]

instance Pi.compact_space [∀ i, CompactSpace (π i)] : CompactSpace (∀ i, π i) :=
  ⟨by
    rw [← pi_univ univ]
    exact is_compact_univ_pi fun i => compact_univ⟩

/-- Product of compact sets is compact -/
theorem Filter.Coprod_cocompact {δ : Type _} {κ : δ → Type _} [∀ d, TopologicalSpace (κ d)] :
    (Filter.coprodₓ fun d => Filter.cocompact (κ d)) = Filter.cocompact (∀ d, κ d) := by
  ext S
  rcases compl_surjective S with ⟨S, rfl⟩
  simp_rw [compl_mem_Coprod_iff, Filter.mem_cocompact, compl_subset_compl]
  constructor
  · rintro ⟨t, H, hSt⟩
    choose K hKc htK using H
    exact ⟨Set.Pi univ K, is_compact_univ_pi hKc, hSt.trans $ pi_mono $ fun i _ => htK i⟩
    
  · rintro ⟨K, hKc, hSK⟩
    exact
      ⟨fun i => Function.eval i '' K, fun i => ⟨_, hKc.image (continuous_apply i), subset.rfl⟩,
        hSK.trans $ subset_pi_eval_image _ _⟩
    

end Tychonoff

instance Quot.compact_space {r : α → α → Prop} [CompactSpace α] : CompactSpace (Quot r) :=
  ⟨by
    rw [← range_quot_mk]
    exact is_compact_range continuous_quot_mk⟩

instance Quotientₓ.compact_space {s : Setoidₓ α} [CompactSpace α] : CompactSpace (Quotientₓ s) :=
  Quot.compact_space

/-- There are various definitions of "locally compact space" in the literature, which agree for
Hausdorff spaces but not in general. This one is the precise condition on X needed for the
evaluation `map C(X, Y) × X → Y` to be continuous for all `Y` when `C(X, Y)` is given the
compact-open topology. -/
class LocallyCompactSpace (α : Type _) [TopologicalSpace α] : Prop where
  local_compact_nhds : ∀ x : α, ∀ n ∈ 𝓝 x, ∀, ∃ s ∈ 𝓝 x, s ⊆ n ∧ IsCompact s

theorem compact_basis_nhds [LocallyCompactSpace α] (x : α) :
    (𝓝 x).HasBasis (fun s => s ∈ 𝓝 x ∧ IsCompact s) fun s => s :=
  has_basis_self.2 $ by
    simpa only [and_comm] using LocallyCompactSpace.local_compact_nhds x

theorem locally_compact_space_of_has_basis {ι : α → Type _} {p : ∀ x, ι x → Prop} {s : ∀ x, ι x → Set α}
    (h : ∀ x, (𝓝 x).HasBasis (p x) (s x)) (hc : ∀ x i, p x i → IsCompact (s x i)) : LocallyCompactSpace α :=
  ⟨fun x t ht =>
    let ⟨i, hp, ht⟩ := (h x).mem_iff.1 ht
    ⟨s x i, (h x).mem_of_mem hp, ht, hc x i hp⟩⟩

instance LocallyCompactSpace.prod (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β]
    [LocallyCompactSpace α] [LocallyCompactSpace β] : LocallyCompactSpace (α × β) :=
  have := fun x : α × β => (compact_basis_nhds x.1).prod_nhds' (compact_basis_nhds x.2)
  locally_compact_space_of_has_basis this $ fun x s ⟨⟨_, h₁⟩, _, h₂⟩ => h₁.prod h₂

/-- A reformulation of the definition of locally compact space: In a locally compact space,
  every open set containing `x` has a compact subset containing `x` in its interior. -/
theorem exists_compact_subset [LocallyCompactSpace α] {x : α} {U : Set α} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ K : Set α, IsCompact K ∧ x ∈ Interior K ∧ K ⊆ U := by
  rcases LocallyCompactSpace.local_compact_nhds x U (hU.mem_nhds hx) with ⟨K, h1K, h2K, h3K⟩
  exact ⟨K, h3K, mem_interior_iff_mem_nhds.2 h1K, h2K⟩

/-- In a locally compact space every point has a compact neighborhood. -/
theorem exists_compact_mem_nhds [LocallyCompactSpace α] (x : α) : ∃ K, IsCompact K ∧ K ∈ 𝓝 x :=
  let ⟨K, hKc, hx, H⟩ := exists_compact_subset is_open_univ (mem_univ x)
  ⟨K, hKc, mem_interior_iff_mem_nhds.1 hx⟩

/-- In a locally compact space, every compact set is contained in the interior of a compact set. -/
theorem exists_compact_superset [LocallyCompactSpace α] {K : Set α} (hK : IsCompact K) :
    ∃ K', IsCompact K' ∧ K ⊆ Interior K' := by
  choose U hUc hxU using fun x : K => exists_compact_mem_nhds (x : α)
  have : K ⊆ ⋃ x, Interior (U x) := fun x hx => mem_Union.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hxU _)⟩
  rcases hK.elim_finite_subcover _ _ this with ⟨t, ht⟩
  · refine' ⟨_, t.compact_bUnion fun x _ => hUc x, fun x hx => _⟩
    rcases mem_Union₂.1 (ht hx) with ⟨y, hyt, hy⟩
    exact interior_mono (subset_bUnion_of_mem hyt) hy
    
  · exact fun _ => is_open_interior
    

protected theorem ClosedEmbedding.locally_compact_space [LocallyCompactSpace β] {f : α → β} (hf : ClosedEmbedding f) :
    LocallyCompactSpace α :=
  have : ∀ x : α, (𝓝 x).HasBasis (fun s => s ∈ 𝓝 (f x) ∧ IsCompact s) fun s => f ⁻¹' s := by
    intro x
    rw [hf.to_embedding.to_inducing.nhds_eq_comap]
    exact (compact_basis_nhds _).comap _
  locally_compact_space_of_has_basis this fun x s hs => hf.is_compact_preimage hs.2

protected theorem IsClosed.locally_compact_space [LocallyCompactSpace α] {s : Set α} (hs : IsClosed s) :
    LocallyCompactSpace s :=
  (closed_embedding_subtype_coe hs).LocallyCompactSpace

protected theorem OpenEmbedding.locally_compact_space [LocallyCompactSpace β] {f : α → β} (hf : OpenEmbedding f) :
    LocallyCompactSpace α := by
  have : ∀ x : α, (𝓝 x).HasBasis (fun s => (s ∈ 𝓝 (f x) ∧ IsCompact s) ∧ s ⊆ range f) fun s => f ⁻¹' s := by
    intro x
    rw [hf.to_embedding.to_inducing.nhds_eq_comap]
    exact ((compact_basis_nhds _).restrict_subset $ hf.open_range.mem_nhds $ mem_range_self _).comap _
  refine' locally_compact_space_of_has_basis this fun x s hs => _
  rw [← hf.to_inducing.is_compact_iff, image_preimage_eq_of_subset hs.2]
  exact hs.1.2

protected theorem IsOpen.locally_compact_space [LocallyCompactSpace α] {s : Set α} (hs : IsOpen s) :
    LocallyCompactSpace s :=
  hs.open_embedding_subtype_coe.locally_compact_space

theorem Ultrafilter.le_nhds_Lim [CompactSpace α] (F : Ultrafilter α) :
    ↑F ≤ 𝓝 (@lim _ _ (F : Filter α).nonempty_of_ne_bot F) := by
  rcases compact_univ.ultrafilter_le_nhds F
      (by
        simp ) with
    ⟨x, -, h⟩
  exact le_nhds_Lim ⟨x, h⟩

theorem IsClosed.exists_minimal_nonempty_closed_subset [CompactSpace α] {S : Set α} (hS : IsClosed S)
    (hne : S.nonempty) :
    ∃ V : Set α, V ⊆ S ∧ V.nonempty ∧ IsClosed V ∧ ∀ V' : Set α, V' ⊆ V → V'.nonempty → IsClosed V' → V' = V := by
  let opens := { U : Set α | Sᶜ ⊆ U ∧ IsOpen U ∧ Uᶜ.Nonempty }
  obtain ⟨U, ⟨Uc, Uo, Ucne⟩, h⟩ :=
    Zorn.zorn_subset opens fun c hc hz => by
      by_cases' hcne : c.nonempty
      · obtain ⟨U₀, hU₀⟩ := hcne
        have : Nonempty { U // U ∈ c } := ⟨⟨U₀, hU₀⟩⟩
        obtain ⟨U₀compl, U₀opn, U₀ne⟩ := hc hU₀
        use ⋃₀c
        refine' ⟨⟨_, _, _⟩, fun U hU a ha => ⟨U, hU, ha⟩⟩
        · exact fun a ha => ⟨U₀, hU₀, U₀compl ha⟩
          
        · exact is_open_sUnion fun _ h => (hc h).2.1
          
        · convert_to (⋂ U : { U // U ∈ c }, U.1ᶜ).Nonempty
          · ext
            simp only [not_exists, exists_prop, not_and, Set.mem_Inter, Subtype.forall, Set.mem_set_of_eq,
              Set.mem_compl_eq, Subtype.val_eq_coe]
            rfl
            
          apply IsCompact.nonempty_Inter_of_directed_nonempty_compact_closed
          · rintro ⟨U, hU⟩ ⟨U', hU'⟩
            obtain ⟨V, hVc, hVU, hVU'⟩ := Zorn.Chain.directed_on hz U hU U' hU'
            exact ⟨⟨V, hVc⟩, set.compl_subset_compl.mpr hVU, set.compl_subset_compl.mpr hVU'⟩
            
          · exact fun U => (hc U.2).2.2
            
          · exact fun U => (is_closed_compl_iff.mpr (hc U.2).2.1).IsCompact
            
          · exact fun U => is_closed_compl_iff.mpr (hc U.2).2.1
            
          
        
      · use Sᶜ
        refine' ⟨⟨Set.Subset.refl _, is_open_compl_iff.mpr hS, _⟩, fun U Uc => (hcne ⟨U, Uc⟩).elim⟩
        rw [compl_compl]
        exact hne
        
  refine' ⟨Uᶜ, set.compl_subset_comm.mp Uc, Ucne, is_closed_compl_iff.mpr Uo, _⟩
  intro V' V'sub V'ne V'cls
  have : V'ᶜ = U := by
    refine' h (V'ᶜ) ⟨_, is_open_compl_iff.mpr V'cls, _⟩ (set.subset_compl_comm.mp V'sub)
    exact Set.Subset.trans Uc (set.subset_compl_comm.mp V'sub)
    simp only [compl_compl, V'ne]
  rw [← this, compl_compl]

/-- A σ-compact space is a space that is the union of a countable collection of compact subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `topological_space.compact_covering`. -/
class SigmaCompactSpace (α : Type _) [TopologicalSpace α] : Prop where
  exists_compact_covering : ∃ K : ℕ → Set α, (∀ n, IsCompact (K n)) ∧ (⋃ n, K n) = univ

instance (priority := 200) CompactSpace.sigma_compact [CompactSpace α] : SigmaCompactSpace α :=
  ⟨⟨fun _ => univ, fun _ => compact_univ, Union_const _⟩⟩

theorem SigmaCompactSpace.of_countable (S : Set (Set α)) (Hc : countable S) (Hcomp : ∀, ∀ s ∈ S, ∀, IsCompact s)
    (HU : ⋃₀S = univ) : SigmaCompactSpace α :=
  ⟨(exists_seq_cover_iff_countable ⟨_, is_compact_empty⟩).2 ⟨S, Hc, Hcomp, HU⟩⟩

instance (priority := 100) sigma_compact_space_of_locally_compact_second_countable [LocallyCompactSpace α]
    [second_countable_topology α] : SigmaCompactSpace α := by
  choose K hKc hxK using fun x : α => exists_compact_mem_nhds x
  rcases countable_cover_nhds hxK with ⟨s, hsc, hsU⟩
  refine' SigmaCompactSpace.of_countable _ (hsc.image K) (ball_image_iff.2 $ fun x _ => hKc x) _
  rwa [sUnion_image]

variable (α) [SigmaCompactSpace α]

open SigmaCompactSpace

/-- A choice of compact covering for a `σ`-compact space, chosen to be monotone. -/
def CompactCovering : ℕ → Set α :=
  accumulate exists_compact_covering.some

theorem is_compact_compact_covering (n : ℕ) : IsCompact (CompactCovering α n) :=
  compact_accumulate (Classical.some_spec SigmaCompactSpace.exists_compact_covering).1 n

theorem Union_compact_covering : (⋃ n, CompactCovering α n) = univ := by
  rw [CompactCovering, Union_accumulate]
  exact (Classical.some_spec SigmaCompactSpace.exists_compact_covering).2

@[mono]
theorem compact_covering_subset ⦃m n : ℕ⦄ (h : m ≤ n) : CompactCovering α m ⊆ CompactCovering α n :=
  monotone_accumulate h

variable {α}

theorem exists_mem_compact_covering (x : α) : ∃ n, x ∈ CompactCovering α n :=
  Union_eq_univ_iff.mp (Union_compact_covering α) x

/-- If `α` is a `σ`-compact space, then a locally finite family of nonempty sets of `α` can have
only countably many elements, `set.countable` version. -/
protected theorem LocallyFinite.countable_univ {ι : Type _} {f : ι → Set α} (hf : LocallyFinite f)
    (hne : ∀ i, (f i).Nonempty) : countable (univ : Set ι) := by
  have := fun n => hf.finite_nonempty_inter_compact (is_compact_compact_covering α n)
  refine' (countable_Union fun n => (this n).Countable).mono fun i hi => _
  rcases hne i with ⟨x, hx⟩
  rcases Union_eq_univ_iff.1 (Union_compact_covering α) x with ⟨n, hn⟩
  exact mem_Union.2 ⟨n, x, hx, hn⟩

/-- If `f : ι → set α` is a locally finite covering of a σ-compact topological space by nonempty
sets, then the index type `ι` is encodable. -/
protected noncomputable def LocallyFinite.encodable {ι : Type _} {f : ι → Set α} (hf : LocallyFinite f)
    (hne : ∀ i, (f i).Nonempty) : Encodable ι :=
  @Encodable.ofEquiv _ _ (hf.countable_univ hne).toEncodable (Equivₓ.Set.univ _).symm

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (t «expr ⊆ » s)
/-- In a topological space with sigma compact topology, if `f` is a function that sends each point
`x` of a closed set `s` to a neighborhood of `x` within `s`, then for some countable set `t ⊆ s`,
the neighborhoods `f x`, `x ∈ t`, cover the whole set `s`. -/
theorem countable_cover_nhds_within_of_sigma_compact {f : α → Set α} {s : Set α} (hs : IsClosed s)
    (hf : ∀, ∀ x ∈ s, ∀, f x ∈ 𝓝[s] x) : ∃ (t : _)(_ : t ⊆ s), countable t ∧ s ⊆ ⋃ x ∈ t, f x := by
  simp only [nhdsWithin, mem_inf_principal] at hf
  choose t ht hsub using fun n =>
    ((is_compact_compact_covering α n).inter_right hs).elim_nhds_subcover _ fun x hx => hf x hx.right
  refine'
    ⟨⋃ n, (t n : Set α), Union_subset $ fun n x hx => (ht n x hx).2, countable_Union $ fun n => (t n).countable_to_set,
      fun x hx => mem_Union₂.2 _⟩
  rcases exists_mem_compact_covering x with ⟨n, hn⟩
  rcases mem_Union₂.1 (hsub n ⟨hn, hx⟩) with ⟨y, hyt : y ∈ t n, hyf : x ∈ s → x ∈ f y⟩
  exact ⟨y, mem_Union.2 ⟨n, hyt⟩, hyf hx⟩

/-- In a topological space with sigma compact topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
theorem countable_cover_nhds_of_sigma_compact {f : α → Set α} (hf : ∀ x, f x ∈ 𝓝 x) :
    ∃ s : Set α, countable s ∧ (⋃ x ∈ s, f x) = univ := by
  simp only [← nhds_within_univ] at hf
  rcases countable_cover_nhds_within_of_sigma_compact is_closed_univ fun x _ => hf x with ⟨s, -, hsc, hsU⟩
  exact ⟨s, hsc, univ_subset_iff.1 hsU⟩

end Compact

/-- An [exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets) of a
topological space is a sequence of compact sets `K n` such that `K n ⊆ interior (K (n + 1))` and
`(⋃ n, K n) = univ`.

If `X` is a locally compact sigma compact space, then `compact_exhaustion.choice X` provides
a choice of an exhaustion by compact sets. This choice is also available as
`(default : compact_exhaustion X)`. -/
structure CompactExhaustion (X : Type _) [TopologicalSpace X] where
  toFun : ℕ → Set X
  is_compact' : ∀ n, IsCompact (to_fun n)
  subset_interior_succ' : ∀ n, to_fun n ⊆ Interior (to_fun (n + 1))
  Union_eq' : (⋃ n, to_fun n) = univ

namespace CompactExhaustion

instance : CoeFun (CompactExhaustion α) fun _ => ℕ → Set α :=
  ⟨to_fun⟩

variable {α} (K : CompactExhaustion α)

protected theorem IsCompact (n : ℕ) : IsCompact (K n) :=
  K.is_compact' n

theorem subset_interior_succ (n : ℕ) : K n ⊆ Interior (K (n + 1)) :=
  K.subset_interior_succ' n

theorem subset_succ (n : ℕ) : K n ⊆ K (n + 1) :=
  subset.trans (K.subset_interior_succ n) interior_subset

@[mono]
protected theorem subset ⦃m n : ℕ⦄ (h : m ≤ n) : K m ⊆ K n :=
  show K m ≤ K n from monotone_nat_of_le_succ K.subset_succ h

theorem subset_interior ⦃m n : ℕ⦄ (h : m < n) : K m ⊆ Interior (K n) :=
  subset.trans (K.subset_interior_succ m) $ interior_mono $ K.subset h

theorem Union_eq : (⋃ n, K n) = univ :=
  K.Union_eq'

theorem exists_mem (x : α) : ∃ n, x ∈ K n :=
  Union_eq_univ_iff.1 K.Union_eq x

/-- The minimal `n` such that `x ∈ K n`. -/
protected noncomputable def find (x : α) : ℕ :=
  Nat.findₓ (K.exists_mem x)

theorem mem_find (x : α) : x ∈ K (K.find x) :=
  Nat.find_specₓ (K.exists_mem x)

theorem mem_iff_find_le {x : α} {n : ℕ} : x ∈ K n ↔ K.find x ≤ n :=
  ⟨fun h => Nat.find_min'ₓ (K.exists_mem x) h, fun h => K.subset h $ K.mem_find x⟩

/-- Prepend the empty set to a compact exhaustion `K n`. -/
def shiftr : CompactExhaustion α where
  toFun := fun n => Nat.casesOn n ∅ K
  is_compact' := fun n => Nat.casesOn n is_compact_empty K.is_compact
  subset_interior_succ' := fun n => Nat.casesOn n (empty_subset _) K.subset_interior_succ
  Union_eq' := Union_eq_univ_iff.2 $ fun x => ⟨K.find x + 1, K.mem_find x⟩

@[simp]
theorem find_shiftr (x : α) : K.shiftr.find x = K.find x + 1 :=
  Nat.find_comp_succ _ _ (not_mem_empty _)

theorem mem_diff_shiftr_find (x : α) : x ∈ K.shiftr (K.find x + 1) \ K.shiftr (K.find x) :=
  ⟨K.mem_find _,
    mt K.shiftr.mem_iff_find_le.1 $ by
      simp only [find_shiftr, not_leₓ, Nat.lt_succ_selfₓ]⟩

/-- A choice of an
[exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets)
of a locally compact sigma compact space. -/
noncomputable def choice (X : Type _) [TopologicalSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X] :
    CompactExhaustion X := by
  apply Classical.choice
  let K : ℕ → { s : Set X // IsCompact s } := fun n =>
    Nat.recOn n ⟨∅, is_compact_empty⟩ fun n s =>
      ⟨(exists_compact_superset s.2).some ∪ CompactCovering X n,
        (exists_compact_superset s.2).some_spec.1.union (is_compact_compact_covering _ _)⟩
  refine' ⟨⟨fun n => K n, fun n => (K n).2, fun n => _, _⟩⟩
  · exact subset.trans (exists_compact_superset (K n).2).some_spec.2 (interior_mono $ subset_union_left _ _)
    
  · refine' univ_subset_iff.1 (Union_compact_covering X ▸ _)
    exact Union_subset_Union2 fun n => ⟨n + 1, subset_union_right _ _⟩
    

noncomputable instance [LocallyCompactSpace α] [SigmaCompactSpace α] : Inhabited (CompactExhaustion α) :=
  ⟨CompactExhaustion.choice α⟩

end CompactExhaustion

section Clopen

/-- A set is clopen if it is both open and closed. -/
def IsClopen (s : Set α) : Prop :=
  IsOpen s ∧ IsClosed s

protected theorem IsClopen.is_open (hs : IsClopen s) : IsOpen s :=
  hs.1

protected theorem IsClopen.is_closed (hs : IsClopen s) : IsClosed s :=
  hs.2

theorem IsClopen.union {s t : Set α} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∪ t) :=
  ⟨hs.1.union ht.1, hs.2.union ht.2⟩

theorem IsClopen.inter {s t : Set α} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

@[simp]
theorem is_clopen_empty : IsClopen (∅ : Set α) :=
  ⟨is_open_empty, is_closed_empty⟩

@[simp]
theorem is_clopen_univ : IsClopen (univ : Set α) :=
  ⟨is_open_univ, is_closed_univ⟩

theorem IsClopen.compl {s : Set α} (hs : IsClopen s) : IsClopen (sᶜ) :=
  ⟨hs.2.is_open_compl, hs.1.is_closed_compl⟩

@[simp]
theorem is_clopen_compl_iff {s : Set α} : IsClopen (sᶜ) ↔ IsClopen s :=
  ⟨fun h => compl_compl s ▸ IsClopen.compl h, IsClopen.compl⟩

theorem IsClopen.diff {s t : Set α} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s \ t) :=
  hs.inter ht.compl

theorem is_clopen_Union {β : Type _} [Fintype β] {s : β → Set α} (h : ∀ i, IsClopen (s i)) : IsClopen (⋃ i, s i) :=
  ⟨is_open_Union (forall_and_distrib.1 h).1, is_closed_Union (forall_and_distrib.1 h).2⟩

theorem is_clopen_bUnion {β : Type _} {s : Finset β} {f : β → Set α} (h : ∀, ∀ i ∈ s, ∀, IsClopen $ f i) :
    IsClopen (⋃ i ∈ s, f i) := by
  refine' ⟨is_open_bUnion fun i hi => (h i hi).1, _⟩
  show IsClosed (⋃ (i : β) (H : i ∈ (s : Set β)), f i)
  rw [bUnion_eq_Union]
  exact is_closed_Union fun ⟨i, hi⟩ => (h i hi).2

theorem is_clopen_Inter {β : Type _} [Fintype β] {s : β → Set α} (h : ∀ i, IsClopen (s i)) : IsClopen (⋂ i, s i) :=
  ⟨is_open_Inter (forall_and_distrib.1 h).1, is_closed_Inter (forall_and_distrib.1 h).2⟩

theorem is_clopen_bInter {β : Type _} {s : Finset β} {f : β → Set α} (h : ∀, ∀ i ∈ s, ∀, IsClopen (f i)) :
    IsClopen (⋂ i ∈ s, f i) :=
  ⟨is_open_bInter ⟨FinsetCoe.fintype s⟩ fun i hi => (h i hi).1, by
    show IsClosed (⋂ (i : β) (H : i ∈ (↑s : Set β)), f i)
    rw [bInter_eq_Inter]
    apply is_closed_Inter
    rintro ⟨i, hi⟩
    exact (h i hi).2⟩

theorem ContinuousOn.preimage_clopen_of_clopen {f : α → β} {s : Set α} {t : Set β} (hf : ContinuousOn f s)
    (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ f ⁻¹' t) :=
  ⟨ContinuousOn.preimage_open_of_open hf hs.1 ht.1, ContinuousOn.preimage_closed_of_closed hf hs.2 ht.2⟩

/-- The intersection of a disjoint covering by two open sets of a clopen set will be clopen. -/
theorem is_clopen_inter_of_disjoint_cover_clopen {Z a b : Set α} (h : IsClopen Z) (cover : Z ⊆ a ∪ b) (ha : IsOpen a)
    (hb : IsOpen b) (hab : a ∩ b = ∅) : IsClopen (Z ∩ a) := by
  refine' ⟨IsOpen.inter h.1 ha, _⟩
  have : IsClosed (Z ∩ bᶜ) := IsClosed.inter h.2 (is_closed_compl_iff.2 hb)
  convert this using 1
  apply subset.antisymm
  · exact inter_subset_inter_right Z (subset_compl_iff_disjoint.2 hab)
    
  · rintro x ⟨hx₁, hx₂⟩
    exact
      ⟨hx₁, by
        simpa [not_mem_of_mem_compl hx₂] using cover hx₁⟩
    

@[simp]
theorem is_clopen_discrete [DiscreteTopology α] (x : Set α) : IsClopen x :=
  ⟨is_open_discrete _, is_closed_discrete _⟩

theorem clopen_range_sigma_mk {ι : Type _} {σ : ι → Type _} [∀ i, TopologicalSpace (σ i)] {i : ι} :
    IsClopen (Set.Range (@Sigma.mk ι σ i)) :=
  ⟨open_embedding_sigma_mk.open_range, closed_embedding_sigma_mk.closed_range⟩

protected theorem QuotientMap.is_clopen_preimage {f : α → β} (hf : QuotientMap f) {s : Set β} :
    IsClopen (f ⁻¹' s) ↔ IsClopen s :=
  and_congr hf.is_open_preimage hf.is_closed_preimage

end Clopen

section Preirreducible

/-- A preirreducible set `s` is one where there is no non-trivial pair of disjoint opens on `s`. -/
def IsPreirreducible (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → (s ∩ u).Nonempty → (s ∩ v).Nonempty → (s ∩ (u ∩ v)).Nonempty

/-- An irreducible set `s` is one that is nonempty and
where there is no non-trivial pair of disjoint opens on `s`. -/
def IsIrreducible (s : Set α) : Prop :=
  s.nonempty ∧ IsPreirreducible s

theorem IsIrreducible.nonempty {s : Set α} (h : IsIrreducible s) : s.nonempty :=
  h.1

theorem IsIrreducible.is_preirreducible {s : Set α} (h : IsIrreducible s) : IsPreirreducible s :=
  h.2

theorem is_preirreducible_empty : IsPreirreducible (∅ : Set α) := fun _ _ _ _ _ ⟨x, h1, h2⟩ => h1.elim

theorem is_irreducible_singleton {x} : IsIrreducible ({x} : Set α) :=
  ⟨singleton_nonempty x, fun u v _ _ ⟨y, h1, h2⟩ ⟨z, h3, h4⟩ => by
    rw [mem_singleton_iff] at h1 h3 <;> substs y z <;> exact ⟨x, rfl, h2, h4⟩⟩

theorem IsPreirreducible.closure {s : Set α} (H : IsPreirreducible s) : IsPreirreducible (Closure s) :=
  fun u v hu hv ⟨y, hycs, hyu⟩ ⟨z, hzcs, hzv⟩ =>
  let ⟨p, hpu, hps⟩ := mem_closure_iff.1 hycs u hu hyu
  let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 hzcs v hv hzv
  let ⟨r, hrs, hruv⟩ := H u v hu hv ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩
  ⟨r, subset_closure hrs, hruv⟩

theorem IsIrreducible.closure {s : Set α} (h : IsIrreducible s) : IsIrreducible (Closure s) :=
  ⟨h.nonempty.closure, h.is_preirreducible.closure⟩

theorem is_preirreducible_of_subsingleton (s : Set α) [hs : Subsingleton s] : IsPreirreducible s := by
  cases s.eq_empty_or_nonempty
  · exact h.symm ▸ is_preirreducible_empty
    
  · obtain ⟨x, e⟩ :=
      exists_eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨h, fun _ ha _ hb => by
          injection @Subsingleton.elimₓ hs ⟨_, ha⟩ ⟨_, hb⟩⟩
    exact e.symm ▸ is_irreducible_singleton.2
    

theorem exists_preirreducible (s : Set α) (H : IsPreirreducible s) :
    ∃ t : Set α, IsPreirreducible t ∧ s ⊆ t ∧ ∀ u, IsPreirreducible u → t ⊆ u → u = t :=
  let ⟨m, hm, hsm, hmm⟩ :=
    Zorn.zorn_subset_nonempty { t : Set α | IsPreirreducible t }
      (fun c hc hcc hcn =>
        let ⟨t, htc⟩ := hcn
        ⟨⋃₀c, fun u v hu hv ⟨y, hy, hyu⟩ ⟨z, hz, hzv⟩ =>
          let ⟨p, hpc, hyp⟩ := mem_sUnion.1 hy
          let ⟨q, hqc, hzq⟩ := mem_sUnion.1 hz
          Or.cases_on (Zorn.Chain.total hcc hpc hqc)
            (fun hpq : p ⊆ q =>
              let ⟨x, hxp, hxuv⟩ := hc hqc u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨z, hzq, hzv⟩
              ⟨x, mem_sUnion_of_mem hxp hqc, hxuv⟩)
            fun hqp : q ⊆ p =>
            let ⟨x, hxp, hxuv⟩ := hc hpc u v hu hv ⟨y, hyp, hyu⟩ ⟨z, hqp hzq, hzv⟩
            ⟨x, mem_sUnion_of_mem hxp hpc, hxuv⟩,
          fun x hxc => subset_sUnion_of_mem hxc⟩)
      s H
  ⟨m, hm, hsm, fun u hu hmu => hmm _ hu hmu⟩

/-- A maximal irreducible set that contains a given point. -/
def IrreducibleComponent (x : α) : Set α :=
  Classical.some (exists_preirreducible {x} is_irreducible_singleton.IsPreirreducible)

theorem irreducible_component_property (x : α) :
    IsPreirreducible (IrreducibleComponent x) ∧
      {x} ⊆ IrreducibleComponent x ∧
        ∀ u, IsPreirreducible u → IrreducibleComponent x ⊆ u → u = IrreducibleComponent x :=
  Classical.some_spec (exists_preirreducible {x} is_irreducible_singleton.IsPreirreducible)

theorem mem_irreducible_component {x : α} : x ∈ IrreducibleComponent x :=
  singleton_subset_iff.1 (irreducible_component_property x).2.1

theorem is_irreducible_irreducible_component {x : α} : IsIrreducible (IrreducibleComponent x) :=
  ⟨⟨x, mem_irreducible_component⟩, (irreducible_component_property x).1⟩

theorem eq_irreducible_component {x : α} :
    ∀ {s : Set α}, IsPreirreducible s → IrreducibleComponent x ⊆ s → s = IrreducibleComponent x :=
  (irreducible_component_property x).2.2

theorem is_closed_irreducible_component {x : α} : IsClosed (IrreducibleComponent x) :=
  closure_eq_iff_is_closed.1 $
    eq_irreducible_component is_irreducible_irreducible_component.IsPreirreducible.closure subset_closure

/-- A preirreducible space is one where there is no non-trivial pair of disjoint opens. -/
class PreirreducibleSpace (α : Type u) [TopologicalSpace α] : Prop where
  is_preirreducible_univ {} : IsPreirreducible (univ : Set α)

/-- An irreducible space is one that is nonempty
and where there is no non-trivial pair of disjoint opens. -/
class IrreducibleSpace (α : Type u) [TopologicalSpace α] extends PreirreducibleSpace α : Prop where
  to_nonempty {} : Nonempty α

attribute [instance] IrreducibleSpace.to_nonempty

theorem IrreducibleSpace.is_irreducible_univ (α : Type u) [TopologicalSpace α] [IrreducibleSpace α] :
    IsIrreducible (⊤ : Set α) :=
  ⟨by
    simp , PreirreducibleSpace.is_preirreducible_univ α⟩

theorem irreducible_space_def (α : Type u) [TopologicalSpace α] : IrreducibleSpace α ↔ IsIrreducible (⊤ : Set α) :=
  ⟨@IrreducibleSpace.is_irreducible_univ α _, fun h =>
    have : PreirreducibleSpace α := ⟨h.2⟩
    ⟨⟨h.1.some⟩⟩⟩

theorem nonempty_preirreducible_inter [PreirreducibleSpace α] {s t : Set α} :
    IsOpen s → IsOpen t → s.nonempty → t.nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using @PreirreducibleSpace.is_preirreducible_univ α _ _ s t

theorem IsPreirreducible.image {s : Set α} (H : IsPreirreducible s) (f : α → β) (hf : ContinuousOn f s) :
    IsPreirreducible (f '' s) := by
  rintro u v hu hv ⟨_, ⟨⟨x, hx, rfl⟩, hxu⟩⟩ ⟨_, ⟨⟨y, hy, rfl⟩, hyv⟩⟩
  rw [← mem_preimage] at hxu hyv
  rcases continuous_on_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuous_on_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  have := H u' v' hu' hv'
  rw [inter_comm s u', ← u'_eq] at this
  rw [inter_comm s v', ← v'_eq] at this
  rcases this ⟨x, hxu, hx⟩ ⟨y, hyv, hy⟩ with ⟨z, hzs, hzu', hzv'⟩
  refine' ⟨f z, mem_image_of_mem f hzs, _, _⟩
  all_goals
    rw [← mem_preimage]
    apply mem_of_mem_inter_left
    show z ∈ _ ∩ s
    simp [*]

theorem IsIrreducible.image {s : Set α} (H : IsIrreducible s) (f : α → β) (hf : ContinuousOn f s) :
    IsIrreducible (f '' s) :=
  ⟨nonempty_image_iff.mpr H.nonempty, H.is_preirreducible.image f hf⟩

theorem Subtype.preirreducible_space {s : Set α} (h : IsPreirreducible s) : PreirreducibleSpace s :=
  { is_preirreducible_univ := by
      intro u v hu hv hsu hsv
      rw [is_open_induced_iff] at hu hv
      rcases hu with ⟨u, hu, rfl⟩
      rcases hv with ⟨v, hv, rfl⟩
      rcases hsu with ⟨⟨x, hxs⟩, hxs', hxu⟩
      rcases hsv with ⟨⟨y, hys⟩, hys', hyv⟩
      rcases h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨z, hzs, ⟨hzu, hzv⟩⟩
      exact ⟨⟨z, hzs⟩, ⟨Set.mem_univ _, ⟨hzu, hzv⟩⟩⟩ }

theorem Subtype.irreducible_space {s : Set α} (h : IsIrreducible s) : IrreducibleSpace s :=
  { is_preirreducible_univ := (Subtype.preirreducible_space h.is_preirreducible).is_preirreducible_univ,
    to_nonempty := h.nonempty.to_subtype }

/-- A set `s` is irreducible if and only if
for every finite collection of open sets all of whose members intersect `s`,
`s` also intersects the intersection of the entire collection
(i.e., there is an element of `s` contained in every member of the collection). -/
theorem is_irreducible_iff_sInter {s : Set α} :
    IsIrreducible s ↔
      ∀ U : Finset (Set α) hU : ∀, ∀ u ∈ U, ∀, IsOpen u H : ∀, ∀ u ∈ U, ∀, (s ∩ u).Nonempty, (s ∩ ⋂₀↑U).Nonempty :=
  by
  constructor <;> intro h
  · intro U
    apply Finset.induction_on U
    · intros
      simpa using h.nonempty
      
    · intro u U hu IH hU H
      rw [Finset.coe_insert, sInter_insert]
      apply h.2
      · solve_by_elim [Finset.mem_insert_self]
        
      · apply is_open_sInter (Finset.finite_to_set U)
        intros
        solve_by_elim [Finset.mem_insert_of_mem]
        
      · solve_by_elim [Finset.mem_insert_self]
        
      · apply IH
        all_goals
          intros
          solve_by_elim [Finset.mem_insert_of_mem]
        
      
    
  · constructor
    · simpa using h ∅ _ _ <;> intro u <;> simp
      
    intro u v hu hv hu' hv'
    simpa using h {u, v} _ _
    all_goals
      intro t
      rw [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl) <;> assumption
    

/-- A set is preirreducible if and only if
for every cover by two closed sets, it is contained in one of the two covering sets. -/
theorem is_preirreducible_iff_closed_union_closed {s : Set α} :
    IsPreirreducible s ↔ ∀ z₁ z₂ : Set α, IsClosed z₁ → IsClosed z₂ → s ⊆ z₁ ∪ z₂ → s ⊆ z₁ ∨ s ⊆ z₂ := by
  constructor
  all_goals
    intro h t₁ t₂ ht₁ ht₂
    specialize h (t₁ᶜ) (t₂ᶜ)
    simp only [is_open_compl_iff, is_closed_compl_iff] at h
    specialize h ht₁ ht₂
  · contrapose!
    simp only [not_subset]
    rintro ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩
    rcases h ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩ with ⟨z, hz, hz'⟩
    rw [← compl_union] at hz'
    exact ⟨z, hz, hz'⟩
    
  · rintro ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
    rw [← compl_inter] at h
    delta' Set.Nonempty
    rw [imp_iff_not_or] at h
    contrapose! h
    constructor
    · intro z hz hz'
      exact h z ⟨hz, hz'⟩
      
    · constructor <;> intro H <;> refine' H _ ‹_› <;> assumption
      
    

/-- A set is irreducible if and only if
for every cover by a finite collection of closed sets,
it is contained in one of the members of the collection. -/
theorem is_irreducible_iff_sUnion_closed {s : Set α} :
    IsIrreducible s ↔ ∀ Z : Finset (Set α) hZ : ∀, ∀ z ∈ Z, ∀, IsClosed z H : s ⊆ ⋃₀↑Z, ∃ z ∈ Z, s ⊆ z := by
  rw [IsIrreducible, is_preirreducible_iff_closed_union_closed]
  constructor <;> intro h
  · intro Z
    apply Finset.induction_on Z
    · intros
      rw [Finset.coe_empty, sUnion_empty] at H
      rcases h.1 with ⟨x, hx⟩
      exfalso
      tauto
      
    · intro z Z hz IH hZ H
      cases' h.2 z (⋃₀↑Z) _ _ _ with h' h'
      · exact ⟨z, Finset.mem_insert_self _ _, h'⟩
        
      · rcases IH _ h' with ⟨z', hz', hsz'⟩
        · exact ⟨z', Finset.mem_insert_of_mem hz', hsz'⟩
          
        · intros
          solve_by_elim [Finset.mem_insert_of_mem]
          
        
      · solve_by_elim [Finset.mem_insert_self]
        
      · rw [sUnion_eq_bUnion]
        apply is_closed_bUnion (Finset.finite_to_set Z)
        · intros
          solve_by_elim [Finset.mem_insert_of_mem]
          
        
      · simpa using H
        
      
    
  · constructor
    · by_contra hs
      simpa using h ∅ _ _
      · intro z
        simp
        
      · simpa [Set.Nonempty] using hs
        
      
    intro z₁ z₂ hz₁ hz₂ H
    have := h {z₁, z₂} _ _
    simp only [exists_prop, Finset.mem_insert, Finset.mem_singleton] at this
    · rcases this with ⟨z, rfl | rfl, hz⟩ <;> tauto
      
    · intro t
      rw [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl) <;> assumption
      
    · simpa using H
      
    

/-- A nonemtpy open subset of a preirreducible subspace is dense in the subspace. -/
theorem subset_closure_inter_of_is_preirreducible_of_is_open {S U : Set α} (hS : IsPreirreducible S) (hU : IsOpen U)
    (h : (S ∩ U).Nonempty) : S ⊆ Closure (S ∩ U) := by
  by_contra h'
  obtain ⟨x, h₁, h₂, h₃⟩ :=
    hS _ (Closure (S ∩ U)ᶜ) hU (is_open_compl_iff.mpr is_closed_closure) h (set.inter_compl_nonempty_iff.mpr h')
  exact h₃ (subset_closure ⟨h₁, h₂⟩)

/-- If `∅ ≠ U ⊆ S ⊆ Z` such that `U` is open and `Z` is preirreducible, then `S` is irreducible. -/
theorem IsPreirreducible.subset_irreducible {S U Z : Set α} (hZ : IsPreirreducible Z) (hU : U.nonempty) (hU' : IsOpen U)
    (h₁ : U ⊆ S) (h₂ : S ⊆ Z) : IsIrreducible S := by
  classical
  obtain ⟨z, hz⟩ := hU
  replace hZ : IsIrreducible Z := ⟨⟨z, h₂ (h₁ hz)⟩, hZ⟩
  refine' ⟨⟨z, h₁ hz⟩, _⟩
  rintro u v hu hv ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨a, -, ha'⟩ :=
    is_irreducible_iff_sInter.mp hZ {U, u, v}
      (by
        tidy)
      _
  replace ha' : a ∈ U ∧ a ∈ u ∧ a ∈ v := by
    simpa using ha'
  exact ⟨a, h₁ ha'.1, ha'.2⟩
  · intro U H
    simp only [Finset.mem_insert, Finset.mem_singleton] at H
    rcases H with (rfl | rfl | rfl)
    exacts[⟨z, h₂ (h₁ hz), hz⟩, ⟨x, h₂ hx, hx'⟩, ⟨y, h₂ hy, hy'⟩]
    

theorem IsPreirreducible.open_subset {Z U : Set α} (hZ : IsPreirreducible Z) (hU : IsOpen U) (hU' : U ⊆ Z) :
    IsPreirreducible U :=
  U.eq_empty_or_nonempty.elim (fun h => h.symm ▸ is_preirreducible_empty) fun h =>
    (hZ.subset_irreducible h hU (fun _ => id) hU').2

theorem IsPreirreducible.interior {Z : Set α} (hZ : IsPreirreducible Z) : IsPreirreducible (Interior Z) :=
  hZ.open_subset is_open_interior interior_subset

theorem IsPreirreducible.preimage {Z : Set α} (hZ : IsPreirreducible Z) {f : β → α} (hf : OpenEmbedding f) :
    IsPreirreducible (f ⁻¹' Z) := by
  rintro U V hU hV ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨_, h₁, ⟨z, h₂, rfl⟩, ⟨z', h₃, h₄⟩⟩ :=
    hZ _ _ (hf.is_open_map _ hU) (hf.is_open_map _ hV) ⟨f x, hx, Set.mem_image_of_mem f hx'⟩
      ⟨f y, hy, Set.mem_image_of_mem f hy'⟩
  cases hf.inj h₄
  exact ⟨z, h₁, h₂, h₃⟩

end Preirreducible

