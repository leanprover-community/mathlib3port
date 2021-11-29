import Mathbin.MeasureTheory.Measure.Content 
import Mathbin.MeasureTheory.Group.Prod

/-!
# Haar measure

In this file we prove the existence of Haar measure for a locally compact Hausdorff topological
group.

For the construction, we follow the write-up by Jonathan Gleason,
*Existence and Uniqueness of Haar Measure*.
This is essentially the same argument as in
https://en.wikipedia.org/wiki/Haar_measure#A_construction_using_compact_subsets.

We construct the Haar measure first on compact sets. For this we define `(K : U)` as the (smallest)
number of left-translates of `U` that are needed to cover `K` (`index` in the formalization).
Then we define a function `h` on compact sets as `lim_U (K : U) / (K₀ : U)`,
where `U` becomes a smaller and smaller open neighborhood of `1`, and `K₀` is a fixed compact set
with nonempty interior. This function is `chaar` in the formalization, and we define the limit
formally using Tychonoff's theorem.

This function `h` forms a content, which we can extend to an outer measure and then a measure
(`haar_measure`).
We normalize the Haar measure so that the measure of `K₀` is `1`.
We show that for second countable spaces any left invariant Borel measure is a scalar multiple of
the Haar measure.

Note that `μ` need not coincide with `h` on compact sets, according to
[halmos1950measure, ch. X, §53 p.233]. However, we know that `h(K)` lies between `μ(Kᵒ)` and `μ(K)`,
where `ᵒ` denotes the interior.

## Main Declarations

* `haar_measure`: the Haar measure on a locally compact Hausdorff group. This is a left invariant
  regular measure. It takes as argument a compact set of the group (with non-empty interior),
  and is normalized so that the measure of the given set is 1.
* `haar_measure_self`: the Haar measure is normalized.
* `is_left_invariant_haar_measure`: the Haar measure is left invariant.
* `regular_haar_measure`: the Haar measure is a regular measure.
* `is_haar_measure_haar_measure`: the Haar measure satisfies the `is_haar_measure` typeclass, i.e.,
  it is invariant and gives finite mass to compact sets and positive mass to nonempty open sets.
* `haar` : some choice of a Haar measure, on a locally compact Hausdorff group, constructed as
  `haar_measure K` where `K` is some arbitrary choice of a compact set with nonempty interior.

## References
* Paul Halmos (1950), Measure Theory, §53
* Jonathan Gleason, Existence and Uniqueness of Haar Measure
  - Note: step 9, page 8 contains a mistake: the last defined `μ` does not extend the `μ` on compact
    sets, see Halmos (1950) p. 233, bottom of the page. This makes some other steps (like step 11)
    invalid.
* https://en.wikipedia.org/wiki/Haar_measure
-/


noncomputable theory

open Set HasInv Function TopologicalSpace MeasurableSpace

open_locale Nnreal Classical Ennreal Pointwise TopologicalSpace

variable{G : Type _}[Groupₓ G]

namespace MeasureTheory

namespace Measureₓ

/-! We put the internal functions in the construction of the Haar measure in a namespace,
  so that the chosen names don't clash with other declarations.
  We first define a couple of the functions before proving the properties (that require that `G`
  is a topological group). -/


namespace Haar

/-- The index or Haar covering number or ratio of `K` w.r.t. `V`, denoted `(K : V)`:
  it is the smallest number of (left) translates of `V` that is necessary to cover `K`.
  It is defined to be 0 if no finite number of translates cover `K`. -/
@[toAdditive add_index "additive version of `measure_theory.measure.haar.index`"]
def index (K V : Set G) : ℕ :=
  Inf$ Finset.card '' { t:Finset G | K ⊆ ⋃(g : _)(_ : g ∈ t), (fun h => g*h) ⁻¹' V }

@[toAdditive add_index_empty]
theorem index_empty {V : Set G} : index ∅ V = 0 :=
  by 
    simp only [index, Nat.Inf_eq_zero]
    left 
    use ∅
    simp only [Finset.card_empty, empty_subset, mem_set_of_eq, eq_self_iff_true, and_selfₓ]

variable[TopologicalSpace G]

/-- `prehaar K₀ U K` is a weighted version of the index, defined as `(K : U)/(K₀ : U)`.
  In the applications `K₀` is compact with non-empty interior, `U` is open containing `1`,
  and `K` is any compact set.
  The argument `K` is a (bundled) compact set, so that we can consider `prehaar K₀ U` as an
  element of `haar_product` (below). -/
@[toAdditive "additive version of `measure_theory.measure.haar.prehaar`"]
def prehaar (K₀ U : Set G) (K : compacts G) : ℝ :=
  (index K.1 U : ℝ) / index K₀ U

@[toAdditive]
theorem prehaar_empty (K₀ : positive_compacts G) {U : Set G} : prehaar K₀.1 U ⊥ = 0 :=
  by 
    simp only [prehaar, compacts.bot_val, index_empty, Nat.cast_zero, zero_div]

@[toAdditive]
theorem prehaar_nonneg (K₀ : positive_compacts G) {U : Set G} (K : compacts G) : 0 ≤ prehaar K₀.1 U K :=
  by 
    apply div_nonneg <;> normCast <;> apply zero_le

/-- `haar_product K₀` is the product of intervals `[0, (K : K₀)]`, for all compact sets `K`.
  For all `U`, we can show that `prehaar K₀ U ∈ haar_product K₀`. -/
@[toAdditive "additive version of `measure_theory.measure.haar.haar_product`"]
def haar_product (K₀ : Set G) : Set (compacts G → ℝ) :=
  pi univ fun K => Icc 0$ index K.1 K₀

@[simp, toAdditive]
theorem mem_prehaar_empty {K₀ : Set G} {f : compacts G → ℝ} :
  f ∈ haar_product K₀ ↔ ∀ (K : compacts G), f K ∈ Icc (0 : ℝ) (index K.1 K₀) :=
  by 
    simp only [haar_product, pi, forall_prop_of_true, mem_univ, mem_set_of_eq]

/-- The closure of the collection of elements of the form `prehaar K₀ U`,
  for `U` open neighbourhoods of `1`, contained in `V`. The closure is taken in the space
  `compacts G → ℝ`, with the topology of pointwise convergence.
  We show that the intersection of all these sets is nonempty, and the Haar measure
  on compact sets is defined to be an element in the closure of this intersection. -/
@[toAdditive "additive version of `measure_theory.measure.haar.cl_prehaar`"]
def cl_prehaar (K₀ : Set G) (V : open_nhds_of (1 : G)) : Set (compacts G → ℝ) :=
  Closure$ prehaar K₀ '' { U:Set G | U ⊆ V.1 ∧ IsOpen U ∧ (1 : G) ∈ U }

variable[TopologicalGroup G]

/-!
### Lemmas about `index`
-/


/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/
@[toAdditive add_index_defined]
theorem index_defined {K V : Set G} (hK : IsCompact K) (hV : (Interior V).Nonempty) :
  ∃ n : ℕ, n ∈ Finset.card '' { t:Finset G | K ⊆ ⋃(g : _)(_ : g ∈ t), (fun h => g*h) ⁻¹' V } :=
  by 
    rcases compact_covered_by_mul_left_translates hK hV with ⟨t, ht⟩
    exact ⟨t.card, t, ht, rfl⟩

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident add_index_elim]]
theorem index_elim
{K V : set G}
(hK : is_compact K)
(hV : (interior V).nonempty) : «expr∃ , »((t : finset G), «expr ∧ »(«expr ⊆ »(K, «expr⋃ , »((g «expr ∈ » t), «expr ⁻¹' »(λ
     h, «expr * »(g, h), V))), «expr = »(finset.card t, index K V))) :=
by { have [] [] [":=", expr nat.Inf_mem (index_defined hK hV)],
  rwa ["[", expr mem_image, "]"] ["at", ident this] }

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident le_add_index_mul]]
theorem le_index_mul
(K₀ : positive_compacts G)
(K : compacts G)
{V : set G}
(hV : (interior V).nonempty) : «expr ≤ »(index K.1 V, «expr * »(index K.1 K₀.1, index K₀.1 V)) :=
begin
  rcases [expr index_elim K.2 K₀.2.2, "with", "⟨", ident s, ",", ident h1s, ",", ident h2s, "⟩"],
  rcases [expr index_elim K₀.2.1 hV, "with", "⟨", ident t, ",", ident h1t, ",", ident h2t, "⟩"],
  rw ["[", "<-", expr h2s, ",", "<-", expr h2t, ",", expr mul_comm, "]"] [],
  refine [expr le_trans _ finset.mul_card_le],
  apply [expr nat.Inf_le],
  refine [expr ⟨_, _, rfl⟩],
  rw ["[", expr mem_set_of_eq, "]"] [],
  refine [expr subset.trans h1s _],
  apply [expr bUnion_subset],
  intros [ident g₁, ident hg₁],
  rw [expr preimage_subset_iff] [],
  intros [ident g₂, ident hg₂],
  have [] [] [":=", expr h1t hg₂],
  rcases [expr this, "with", "⟨", "_", ",", "⟨", ident g₃, ",", ident rfl, "⟩", ",", ident A, ",", "⟨", ident hg₃, ",", ident rfl, "⟩", ",", ident h2V, "⟩"],
  rw ["[", expr mem_preimage, ",", "<-", expr mul_assoc, "]"] ["at", ident h2V],
  exact [expr mem_bUnion (finset.mul_mem_mul hg₃ hg₁) h2V]
end

@[toAdditive add_index_pos]
theorem index_pos (K : positive_compacts G) {V : Set G} (hV : (Interior V).Nonempty) : 0 < index K.1 V :=
  by 
    unfold index 
    rw [Nat.Inf_def, Nat.find_pos, mem_image]
    ·
      rintro ⟨t, h1t, h2t⟩
      rw [Finset.card_eq_zero] at h2t 
      subst h2t 
      cases' K.2.2 with g hg 
      show g ∈ (∅ : Set G)
      convert h1t (interior_subset hg)
      symm 
      apply bUnion_empty
    ·
      exact index_defined K.2.1 hV

@[toAdditive add_index_mono]
theorem index_mono {K K' V : Set G} (hK' : IsCompact K') (h : K ⊆ K') (hV : (Interior V).Nonempty) :
  index K V ≤ index K' V :=
  by 
    rcases index_elim hK' hV with ⟨s, h1s, h2s⟩
    apply Nat.Inf_le 
    rw [mem_image]
    refine' ⟨s, subset.trans h h1s, h2s⟩

@[toAdditive add_index_union_le]
theorem index_union_le (K₁ K₂ : compacts G) {V : Set G} (hV : (Interior V).Nonempty) :
  index (K₁.1 ∪ K₂.1) V ≤ index K₁.1 V+index K₂.1 V :=
  by 
    rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩
    rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩
    rw [←h2s, ←h2t]
    refine' le_transₓ _ (Finset.card_union_le _ _)
    apply Nat.Inf_le 
    refine' ⟨_, _, rfl⟩
    rw [mem_set_of_eq]
    apply union_subset <;>
      refine'
          subset.trans
            (by 
              assumption)
            _ <;>
        apply bUnion_subset_bUnion_left <;>
          intro g hg <;>
            simp only [mem_def] at hg <;>
              simp only [mem_def, Multiset.mem_union, Finset.union_val, hg, or_trueₓ, true_orₓ]

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident add_index_union_eq]]
theorem index_union_eq
(K₁ K₂ : compacts G)
{V : set G}
(hV : (interior V).nonempty)
(h : disjoint «expr * »(K₁.1, «expr ⁻¹»(V)) «expr * »(K₂.1, «expr ⁻¹»(V))) : «expr = »(index «expr ∪ »(K₁.1, K₂.1) V, «expr + »(index K₁.1 V, index K₂.1 V)) :=
begin
  apply [expr le_antisymm (index_union_le K₁ K₂ hV)],
  rcases [expr index_elim (K₁.2.union K₂.2) hV, "with", "⟨", ident s, ",", ident h1s, ",", ident h2s, "⟩"],
  rw ["[", "<-", expr h2s, "]"] [],
  have [] [":", expr ∀
   K : set G, «expr ⊆ »(K, «expr⋃ , »((g «expr ∈ » s), «expr ⁻¹' »(λ
      h, «expr * »(g, h), V))) → «expr ≤ »(index K V, (s.filter (λ
      g, «expr ∩ »(«expr ⁻¹' »(λ h : G, «expr * »(g, h), V), K).nonempty)).card)] [],
  { intros [ident K, ident hK],
    apply [expr nat.Inf_le],
    refine [expr ⟨_, _, rfl⟩],
    rw ["[", expr mem_set_of_eq, "]"] [],
    intros [ident g, ident hg],
    rcases [expr hK hg, "with", "⟨", "_", ",", "⟨", ident g₀, ",", ident rfl, "⟩", ",", "_", ",", "⟨", ident h1g₀, ",", ident rfl, "⟩", ",", ident h2g₀, "⟩"],
    simp [] [] ["only"] ["[", expr mem_preimage, "]"] [] ["at", ident h2g₀],
    simp [] [] ["only"] ["[", expr mem_Union, "]"] [] [],
    use [expr g₀],
    split,
    { simp [] [] ["only"] ["[", expr finset.mem_filter, ",", expr h1g₀, ",", expr true_and, "]"] [] [],
      use [expr g],
      simp [] [] ["only"] ["[", expr hg, ",", expr h2g₀, ",", expr mem_inter_eq, ",", expr mem_preimage, ",", expr and_self, "]"] [] [] },
    exact [expr h2g₀] },
  refine [expr le_trans (add_le_add «expr $ »(this K₁.1, subset.trans (subset_union_left _ _) h1s) «expr $ »(this K₂.1, subset.trans (subset_union_right _ _) h1s)) _],
  rw ["[", "<-", expr finset.card_union_eq, ",", expr finset.filter_union_right, "]"] [],
  exact [expr s.card_filter_le _],
  apply [expr finset.disjoint_filter.mpr],
  rintro [ident g₁, ident h1g₁, "⟨", ident g₂, ",", ident h1g₂, ",", ident h2g₂, "⟩", "⟨", ident g₃, ",", ident h1g₃, ",", ident h2g₃, "⟩"],
  simp [] [] ["only"] ["[", expr mem_preimage, "]"] [] ["at", ident h1g₃, ident h1g₂],
  apply [expr @h «expr ⁻¹»(g₁)],
  split; simp [] [] ["only"] ["[", expr set.mem_inv, ",", expr set.mem_mul, ",", expr exists_exists_and_eq_and, ",", expr exists_and_distrib_left, "]"] [] [],
  { refine [expr ⟨_, h2g₂, «expr ⁻¹»(«expr * »(g₁, g₂)), _, _⟩],
    simp [] [] ["only"] ["[", expr inv_inv, ",", expr h1g₂, "]"] [] [],
    simp [] [] ["only"] ["[", expr mul_inv_rev, ",", expr mul_inv_cancel_left, "]"] [] [] },
  { refine [expr ⟨_, h2g₃, «expr ⁻¹»(«expr * »(g₁, g₃)), _, _⟩],
    simp [] [] ["only"] ["[", expr inv_inv, ",", expr h1g₃, "]"] [] [],
    simp [] [] ["only"] ["[", expr mul_inv_rev, ",", expr mul_inv_cancel_left, "]"] [] [] }
end

@[toAdditive add_left_add_index_le]
theorem mul_left_index_le {K : Set G} (hK : IsCompact K) {V : Set G} (hV : (Interior V).Nonempty) (g : G) :
  index ((fun h => g*h) '' K) V ≤ index K V :=
  by 
    rcases index_elim hK hV with ⟨s, h1s, h2s⟩
    rw [←h2s]
    apply Nat.Inf_le 
    rw [mem_image]
    refine' ⟨s.map (Equiv.mulRight (g⁻¹)).toEmbedding, _, Finset.card_map _⟩
    ·
      simp only [mem_set_of_eq]
      refine' subset.trans (image_subset _ h1s) _ 
      rintro _ ⟨g₁, ⟨_, ⟨g₂, rfl⟩, ⟨_, ⟨hg₂, rfl⟩, hg₁⟩⟩, rfl⟩
      simp only [mem_preimage] at hg₁ 
      simp only [exists_prop, mem_Union, Finset.mem_map, Equiv.coe_mul_right, exists_exists_and_eq_and, mem_preimage,
        Equiv.to_embedding_apply]
      refine' ⟨_, hg₂, _⟩
      simp only [mul_assocₓ, hg₁, inv_mul_cancel_leftₓ]

@[toAdditive is_left_invariant_add_index]
theorem is_left_invariant_index {K : Set G} (hK : IsCompact K) (g : G) {V : Set G} (hV : (Interior V).Nonempty) :
  index ((fun h => g*h) '' K) V = index K V :=
  by 
    refine' le_antisymmₓ (mul_left_index_le hK hV g) _ 
    convert mul_left_index_le (hK.image$ continuous_mul_left g) hV (g⁻¹)
    rw [image_image]
    symm 
    convert image_id' _ 
    ext h 
    apply inv_mul_cancel_leftₓ

/-!
### Lemmas about `prehaar`
-/


@[toAdditive add_prehaar_le_add_index]
theorem prehaar_le_index (K₀ : positive_compacts G) {U : Set G} (K : compacts G) (hU : (Interior U).Nonempty) :
  prehaar K₀.1 U K ≤ index K.1 K₀.1 :=
  by 
    unfold prehaar 
    rw [div_le_iff] <;> normCast
    ·
      apply le_index_mul K₀ K hU
    ·
      exact index_pos K₀ hU

@[toAdditive]
theorem prehaar_pos (K₀ : positive_compacts G) {U : Set G} (hU : (Interior U).Nonempty) {K : Set G} (h1K : IsCompact K)
  (h2K : (Interior K).Nonempty) : 0 < prehaar K₀.1 U ⟨K, h1K⟩ :=
  by 
    apply div_pos <;> normCast 
    apply index_pos ⟨K, h1K, h2K⟩ hU 
    exact index_pos K₀ hU

@[toAdditive]
theorem prehaar_mono {K₀ : positive_compacts G} {U : Set G} (hU : (Interior U).Nonempty) {K₁ K₂ : compacts G}
  (h : K₁.1 ⊆ K₂.1) : prehaar K₀.1 U K₁ ≤ prehaar K₀.1 U K₂ :=
  by 
    simp only [prehaar]
    rw [div_le_div_right]
    exactModCast index_mono K₂.2 h hU 
    exactModCast index_pos K₀ hU

@[toAdditive]
theorem prehaar_self {K₀ : positive_compacts G} {U : Set G} (hU : (Interior U).Nonempty) :
  prehaar K₀.1 U ⟨K₀.1, K₀.2.1⟩ = 1 :=
  by 
    simp only [prehaar]
    rw [div_self]
    apply ne_of_gtₓ 
    exactModCast index_pos K₀ hU

@[toAdditive]
theorem prehaar_sup_le {K₀ : positive_compacts G} {U : Set G} (K₁ K₂ : compacts G) (hU : (Interior U).Nonempty) :
  prehaar K₀.1 U (K₁⊔K₂) ≤ prehaar K₀.1 U K₁+prehaar K₀.1 U K₂ :=
  by 
    simp only [prehaar]
    rw [div_add_div_same, div_le_div_right]
    exactModCast index_union_le K₁ K₂ hU 
    exactModCast index_pos K₀ hU

@[toAdditive]
theorem prehaar_sup_eq {K₀ : positive_compacts G} {U : Set G} {K₁ K₂ : compacts G} (hU : (Interior U).Nonempty)
  (h : Disjoint (K₁.1*U⁻¹) (K₂.1*U⁻¹)) : prehaar K₀.1 U (K₁⊔K₂) = prehaar K₀.1 U K₁+prehaar K₀.1 U K₂ :=
  by 
    simp only [prehaar]
    rw [div_add_div_same]
    congr 
    exactModCast index_union_eq K₁ K₂ hU h

@[toAdditive]
theorem is_left_invariant_prehaar {K₀ : positive_compacts G} {U : Set G} (hU : (Interior U).Nonempty) (g : G)
  (K : compacts G) : prehaar K₀.1 U (K.map _$ continuous_mul_left g) = prehaar K₀.1 U K :=
  by 
    simp only [prehaar, compacts.map_val, is_left_invariant_index K.2 _ hU]

/-!
### Lemmas about `haar_product`
-/


@[toAdditive]
theorem prehaar_mem_haar_product (K₀ : positive_compacts G) {U : Set G} (hU : (Interior U).Nonempty) :
  prehaar K₀.1 U ∈ haar_product K₀.1 :=
  by 
    rintro ⟨K, hK⟩ h2K 
    rw [mem_Icc]
    exact ⟨prehaar_nonneg K₀ _, prehaar_le_index K₀ _ hU⟩

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem nonempty_Inter_cl_prehaar
(K₀ : positive_compacts G) : «expr ∩ »(haar_product K₀.1, «expr⋂ , »((V : open_nhds_of (1 : G)), cl_prehaar K₀.1 V)).nonempty :=
begin
  have [] [":", expr is_compact (haar_product K₀.1)] [],
  { apply [expr is_compact_univ_pi],
    intro [ident K],
    apply [expr is_compact_Icc] },
  refine [expr this.inter_Inter_nonempty (cl_prehaar K₀.1) (λ s, is_closed_closure) (λ t, _)],
  let [ident V₀] [] [":=", expr «expr⋂ , »((V «expr ∈ » t), (V : open_nhds_of 1).1)],
  have [ident h1V₀] [":", expr is_open V₀] [],
  { apply [expr is_open_bInter],
    apply [expr finite_mem_finset],
    rintro ["⟨", ident V, ",", ident hV, "⟩", ident h2V],
    exact [expr hV.1] },
  have [ident h2V₀] [":", expr «expr ∈ »((1 : G), V₀)] [],
  { simp [] [] ["only"] ["[", expr mem_Inter, "]"] [] [],
    rintro ["⟨", ident V, ",", ident hV, "⟩", ident h2V],
    exact [expr hV.2] },
  refine [expr ⟨prehaar K₀.1 V₀, _⟩],
  split,
  { apply [expr prehaar_mem_haar_product K₀],
    use [expr 1],
    rwa [expr h1V₀.interior_eq] [] },
  { simp [] [] ["only"] ["[", expr mem_Inter, "]"] [] [],
    rintro ["⟨", ident V, ",", ident hV, "⟩", ident h2V],
    apply [expr subset_closure],
    apply [expr mem_image_of_mem],
    rw ["[", expr mem_set_of_eq, "]"] [],
    exact [expr ⟨subset.trans (Inter_subset _ ⟨V, hV⟩) (Inter_subset _ h2V), h1V₀, h2V₀⟩] }
end

/-!
### Lemmas about `chaar`
-/


/-- This is the "limit" of `prehaar K₀.1 U K` as `U` becomes a smaller and smaller open
  neighborhood of `(1 : G)`. More precisely, it is defined to be an arbitrary element
  in the intersection of all the sets `cl_prehaar K₀ V` in `haar_product K₀`.
  This is roughly equal to the Haar measure on compact sets,
  but it can differ slightly. We do know that
  `haar_measure K₀ (interior K.1) ≤ chaar K₀ K ≤ haar_measure K₀ K.1`. -/
@[toAdditive add_chaar "additive version of `measure_theory.measure.haar.chaar`"]
def chaar (K₀ : positive_compacts G) (K : compacts G) : ℝ :=
  Classical.some (nonempty_Inter_cl_prehaar K₀) K

@[toAdditive add_chaar_mem_add_haar_product]
theorem chaar_mem_haar_product (K₀ : positive_compacts G) : chaar K₀ ∈ haar_product K₀.1 :=
  (Classical.some_spec (nonempty_Inter_cl_prehaar K₀)).1

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident add_chaar_mem_cl_add_prehaar]]
theorem chaar_mem_cl_prehaar
(K₀ : positive_compacts G)
(V : open_nhds_of (1 : G)) : «expr ∈ »(chaar K₀, cl_prehaar K₀.1 V) :=
by { have [] [] [":=", expr (classical.some_spec (nonempty_Inter_cl_prehaar K₀)).2],
  rw ["[", expr mem_Inter, "]"] ["at", ident this],
  exact [expr this V] }

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident add_chaar_nonneg]]
theorem chaar_nonneg (K₀ : positive_compacts G) (K : compacts G) : «expr ≤ »(0, chaar K₀ K) :=
by { have [] [] [":=", expr chaar_mem_haar_product K₀ K (mem_univ _)],
  rw [expr mem_Icc] ["at", ident this],
  exact [expr this.1] }

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident add_chaar_empty]]
theorem chaar_empty (K₀ : positive_compacts G) : «expr = »(chaar K₀ «expr⊥»(), 0) :=
begin
  let [ident eval] [":", expr (compacts G → exprℝ()) → exprℝ()] [":=", expr λ f, f «expr⊥»()],
  have [] [":", expr continuous eval] [":=", expr continuous_apply «expr⊥»()],
  show [expr «expr ∈ »(chaar K₀, «expr ⁻¹' »(eval, {(0 : exprℝ())}))],
  apply [expr mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩)],
  unfold [ident cl_prehaar] [],
  rw [expr is_closed.closure_subset_iff] [],
  { rintro ["_", "⟨", ident U, ",", "⟨", ident h1U, ",", ident h2U, ",", ident h3U, "⟩", ",", ident rfl, "⟩"],
    apply [expr prehaar_empty] },
  { apply [expr continuous_iff_is_closed.mp this],
    exact [expr is_closed_singleton] }
end

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident add_chaar_self]]
theorem chaar_self (K₀ : positive_compacts G) : «expr = »(chaar K₀ ⟨K₀.1, K₀.2.1⟩, 1) :=
begin
  let [ident eval] [":", expr (compacts G → exprℝ()) → exprℝ()] [":=", expr λ f, f ⟨K₀.1, K₀.2.1⟩],
  have [] [":", expr continuous eval] [":=", expr continuous_apply _],
  show [expr «expr ∈ »(chaar K₀, «expr ⁻¹' »(eval, {(1 : exprℝ())}))],
  apply [expr mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩)],
  unfold [ident cl_prehaar] [],
  rw [expr is_closed.closure_subset_iff] [],
  { rintro ["_", "⟨", ident U, ",", "⟨", ident h1U, ",", ident h2U, ",", ident h3U, "⟩", ",", ident rfl, "⟩"],
    apply [expr prehaar_self],
    rw [expr h2U.interior_eq] [],
    exact [expr ⟨1, h3U⟩] },
  { apply [expr continuous_iff_is_closed.mp this],
    exact [expr is_closed_singleton] }
end

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident add_chaar_mono]]
theorem chaar_mono
{K₀ : positive_compacts G}
{K₁ K₂ : compacts G}
(h : «expr ⊆ »(K₁.1, K₂.1)) : «expr ≤ »(chaar K₀ K₁, chaar K₀ K₂) :=
begin
  let [ident eval] [":", expr (compacts G → exprℝ()) → exprℝ()] [":=", expr λ f, «expr - »(f K₂, f K₁)],
  have [] [":", expr continuous eval] [":=", expr (continuous_apply K₂).sub (continuous_apply K₁)],
  rw ["[", "<-", expr sub_nonneg, "]"] [],
  show [expr «expr ∈ »(chaar K₀, «expr ⁻¹' »(eval, Ici (0 : exprℝ())))],
  apply [expr mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩)],
  unfold [ident cl_prehaar] [],
  rw [expr is_closed.closure_subset_iff] [],
  { rintro ["_", "⟨", ident U, ",", "⟨", ident h1U, ",", ident h2U, ",", ident h3U, "⟩", ",", ident rfl, "⟩"],
    simp [] [] ["only"] ["[", expr mem_preimage, ",", expr mem_Ici, ",", expr eval, ",", expr sub_nonneg, "]"] [] [],
    apply [expr prehaar_mono _ h],
    rw [expr h2U.interior_eq] [],
    exact [expr ⟨1, h3U⟩] },
  { apply [expr continuous_iff_is_closed.mp this],
    exact [expr is_closed_Ici] }
end

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident add_chaar_sup_le]]
theorem chaar_sup_le
{K₀ : positive_compacts G}
(K₁ K₂ : compacts G) : «expr ≤ »(chaar K₀ «expr ⊔ »(K₁, K₂), «expr + »(chaar K₀ K₁, chaar K₀ K₂)) :=
begin
  let [ident eval] [":", expr (compacts G → exprℝ()) → exprℝ()] [":=", expr λ
   f, «expr - »(«expr + »(f K₁, f K₂), f «expr ⊔ »(K₁, K₂))],
  have [] [":", expr continuous eval] [":=", expr ((@continuous_add exprℝ() _ _ _).comp ((continuous_apply K₁).prod_mk (continuous_apply K₂))).sub (continuous_apply «expr ⊔ »(K₁, K₂))],
  rw ["[", "<-", expr sub_nonneg, "]"] [],
  show [expr «expr ∈ »(chaar K₀, «expr ⁻¹' »(eval, Ici (0 : exprℝ())))],
  apply [expr mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩)],
  unfold [ident cl_prehaar] [],
  rw [expr is_closed.closure_subset_iff] [],
  { rintro ["_", "⟨", ident U, ",", "⟨", ident h1U, ",", ident h2U, ",", ident h3U, "⟩", ",", ident rfl, "⟩"],
    simp [] [] ["only"] ["[", expr mem_preimage, ",", expr mem_Ici, ",", expr eval, ",", expr sub_nonneg, "]"] [] [],
    apply [expr prehaar_sup_le],
    rw [expr h2U.interior_eq] [],
    exact [expr ⟨1, h3U⟩] },
  { apply [expr continuous_iff_is_closed.mp this],
    exact [expr is_closed_Ici] }
end

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident add_chaar_sup_eq]]
theorem chaar_sup_eq
[t2_space G]
{K₀ : positive_compacts G}
{K₁ K₂ : compacts G}
(h : disjoint K₁.1 K₂.1) : «expr = »(chaar K₀ «expr ⊔ »(K₁, K₂), «expr + »(chaar K₀ K₁, chaar K₀ K₂)) :=
begin
  rcases [expr compact_compact_separated K₁.2 K₂.2 (disjoint_iff.mp h), "with", "⟨", ident U₁, ",", ident U₂, ",", ident h1U₁, ",", ident h1U₂, ",", ident h2U₁, ",", ident h2U₂, ",", ident hU, "⟩"],
  rw ["[", "<-", expr disjoint_iff_inter_eq_empty, "]"] ["at", ident hU],
  rcases [expr compact_open_separated_mul K₁.2 h1U₁ h2U₁, "with", "⟨", ident V₁, ",", ident h1V₁, ",", ident h2V₁, ",", ident h3V₁, "⟩"],
  rcases [expr compact_open_separated_mul K₂.2 h1U₂ h2U₂, "with", "⟨", ident V₂, ",", ident h1V₂, ",", ident h2V₂, ",", ident h3V₂, "⟩"],
  let [ident eval] [":", expr (compacts G → exprℝ()) → exprℝ()] [":=", expr λ
   f, «expr - »(«expr + »(f K₁, f K₂), f «expr ⊔ »(K₁, K₂))],
  have [] [":", expr continuous eval] [":=", expr ((@continuous_add exprℝ() _ _ _).comp ((continuous_apply K₁).prod_mk (continuous_apply K₂))).sub (continuous_apply «expr ⊔ »(K₁, K₂))],
  rw ["[", expr eq_comm, ",", "<-", expr sub_eq_zero, "]"] [],
  show [expr «expr ∈ »(chaar K₀, «expr ⁻¹' »(eval, {(0 : exprℝ())}))],
  let [ident V] [] [":=", expr «expr ∩ »(V₁, V₂)],
  apply [expr mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨«expr ⁻¹»(V), (is_open.inter h1V₁ h1V₂).preimage continuous_inv, by simp [] [] ["only"] ["[", expr mem_inv, ",", expr one_inv, ",", expr h2V₁, ",", expr h2V₂, ",", expr V, ",", expr mem_inter_eq, ",", expr true_and, "]"] [] []⟩)],
  unfold [ident cl_prehaar] [],
  rw [expr is_closed.closure_subset_iff] [],
  { rintro ["_", "⟨", ident U, ",", "⟨", ident h1U, ",", ident h2U, ",", ident h3U, "⟩", ",", ident rfl, "⟩"],
    simp [] [] ["only"] ["[", expr mem_preimage, ",", expr eval, ",", expr sub_eq_zero, ",", expr mem_singleton_iff, "]"] [] [],
    rw ["[", expr eq_comm, "]"] [],
    apply [expr prehaar_sup_eq],
    { rw [expr h2U.interior_eq] [],
      exact [expr ⟨1, h3U⟩] },
    { refine [expr disjoint_of_subset _ _ hU],
      { refine [expr subset.trans (mul_subset_mul subset.rfl _) h3V₁],
        exact [expr subset.trans (inv_subset.mpr h1U) (inter_subset_left _ _)] },
      { refine [expr subset.trans (mul_subset_mul subset.rfl _) h3V₂],
        exact [expr subset.trans (inv_subset.mpr h1U) (inter_subset_right _ _)] } } },
  { apply [expr continuous_iff_is_closed.mp this],
    exact [expr is_closed_singleton] }
end

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident is_left_invariant_add_chaar]]
theorem is_left_invariant_chaar
{K₀ : positive_compacts G}
(g : G)
(K : compacts G) : «expr = »(chaar K₀ «expr $ »(K.map _, continuous_mul_left g), chaar K₀ K) :=
begin
  let [ident eval] [":", expr (compacts G → exprℝ()) → exprℝ()] [":=", expr λ
   f, «expr - »(f «expr $ »(K.map _, continuous_mul_left g), f K)],
  have [] [":", expr continuous eval] [":=", expr (continuous_apply (K.map _ _)).sub (continuous_apply K)],
  rw ["[", "<-", expr sub_eq_zero, "]"] [],
  show [expr «expr ∈ »(chaar K₀, «expr ⁻¹' »(eval, {(0 : exprℝ())}))],
  apply [expr mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩)],
  unfold [ident cl_prehaar] [],
  rw [expr is_closed.closure_subset_iff] [],
  { rintro ["_", "⟨", ident U, ",", "⟨", ident h1U, ",", ident h2U, ",", ident h3U, "⟩", ",", ident rfl, "⟩"],
    simp [] [] ["only"] ["[", expr mem_singleton_iff, ",", expr mem_preimage, ",", expr eval, ",", expr sub_eq_zero, "]"] [] [],
    apply [expr is_left_invariant_prehaar],
    rw [expr h2U.interior_eq] [],
    exact [expr ⟨1, h3U⟩] },
  { apply [expr continuous_iff_is_closed.mp this],
    exact [expr is_closed_singleton] }
end

variable[T2Space G]

/-- The function `chaar` interpreted in `ℝ≥0`, as a content -/
@[toAdditive "additive version of `measure_theory.measure.haar.haar_content`"]
def haar_content (K₀ : positive_compacts G) : content G :=
  { toFun := fun K => ⟨chaar K₀ K, chaar_nonneg _ _⟩,
    mono' :=
      fun K₁ K₂ h =>
        by 
          simp only [←Nnreal.coe_le_coe, Subtype.coe_mk, chaar_mono, h],
    sup_disjoint' :=
      fun K₁ K₂ h =>
        by 
          simp only [chaar_sup_eq h]
          rfl,
    sup_le' :=
      fun K₁ K₂ =>
        by 
          simp only [←Nnreal.coe_le_coe, Nnreal.coe_add, Subtype.coe_mk, chaar_sup_le] }

/-! We only prove the properties for `haar_content` that we use at least twice below. -/


@[toAdditive]
theorem haar_content_apply (K₀ : positive_compacts G) (K : compacts G) :
  haar_content K₀ K = show Nnreal from ⟨chaar K₀ K, chaar_nonneg _ _⟩ :=
  rfl

/-- The variant of `chaar_self` for `haar_content` -/
@[toAdditive]
theorem haar_content_self {K₀ : positive_compacts G} : haar_content K₀ ⟨K₀.1, K₀.2.1⟩ = 1 :=
  by 
    simpRw [←Ennreal.coe_one, haar_content_apply, Ennreal.coe_eq_coe, chaar_self]
    rfl

/-- The variant of `is_left_invariant_chaar` for `haar_content` -/
@[toAdditive]
theorem is_left_invariant_haar_content {K₀ : positive_compacts G} (g : G) (K : compacts G) :
  haar_content K₀ (K.map _$ continuous_mul_left g) = haar_content K₀ K :=
  by 
    simpa only [Ennreal.coe_eq_coe, ←Nnreal.coe_eq, haar_content_apply] using is_left_invariant_chaar g K

@[toAdditive]
theorem haar_content_outer_measure_self_pos {K₀ : positive_compacts G} : 0 < (haar_content K₀).OuterMeasure K₀.1 :=
  by 
    apply ennreal.zero_lt_one.trans_le 
    rw [content.outer_measure_eq_infi]
    refine' le_binfi _ 
    intro U hU 
    refine' le_infi _ 
    intro h2U 
    refine' le_transₓ (le_of_eqₓ _) (le_bsupr ⟨K₀.1, K₀.2.1⟩ h2U)
    exact haar_content_self.symm

end Haar

open Haar

/-!
### The Haar measure
-/


variable[TopologicalSpace G][T2Space G][TopologicalGroup G][MeasurableSpace G][BorelSpace G]

/-- The Haar measure on the locally compact group `G`, scaled so that `haar_measure K₀ K₀ = 1`. -/
@[toAdditive
      "The Haar measure on the locally compact additive group `G`,\nscaled so that `add_haar_measure K₀ K₀ = 1`."]
def haar_measure (K₀ : positive_compacts G) : Measureₓ G :=
  (haar_content K₀).OuterMeasure K₀.1⁻¹ • (haar_content K₀).Measure

@[toAdditive]
theorem haar_measure_apply {K₀ : positive_compacts G} {s : Set G} (hs : MeasurableSet s) :
  haar_measure K₀ s = (haar_content K₀).OuterMeasure s / (haar_content K₀).OuterMeasure K₀.1 :=
  by 
    change ((haar_content K₀).OuterMeasure K₀.val⁻¹*(haar_content K₀).Measure s) = _ 
    simp only [hs, div_eq_mul_inv, mul_commₓ, content.measure_apply]

@[toAdditive]
theorem is_mul_left_invariant_haar_measure (K₀ : positive_compacts G) : is_mul_left_invariant (haar_measure K₀) :=
  by 
    intro g A hA 
    rw [haar_measure_apply hA, haar_measure_apply (measurable_const_mul g hA)]
    congr 1
    apply content.is_mul_left_invariant_outer_measure 
    apply is_left_invariant_haar_content

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]] theorem haar_measure_self {K₀ : positive_compacts G} : «expr = »(haar_measure K₀ K₀.1, 1) :=
begin
  haveI [] [":", expr locally_compact_space G] [":=", expr K₀.locally_compact_space_of_group],
  rw ["[", expr haar_measure_apply K₀.2.1.measurable_set, ",", expr ennreal.div_self, "]"] [],
  { rw ["[", "<-", expr pos_iff_ne_zero, "]"] [],
    exact [expr haar_content_outer_measure_self_pos] },
  { exact [expr ne_of_lt (content.outer_measure_lt_top_of_is_compact _ K₀.2.1)] }
end

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Haar measure is regular. -/
@[to_additive #[]]
instance regular_haar_measure {K₀ : positive_compacts G} : (haar_measure K₀).regular :=
begin
  haveI [] [":", expr locally_compact_space G] [":=", expr K₀.locally_compact_space_of_group],
  apply [expr regular.smul],
  rw [expr ennreal.inv_ne_top] [],
  exact [expr haar_content_outer_measure_self_pos.ne']
end

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Haar measure is sigma-finite in a second countable group. -/
@[to_additive #[]]
instance sigma_finite_haar_measure
[second_countable_topology G]
{K₀ : positive_compacts G} : sigma_finite (haar_measure K₀) :=
by { haveI [] [":", expr locally_compact_space G] [":=", expr K₀.locally_compact_space_of_group],
  apply_instance }

/-- The Haar measure is a Haar measure, i.e., it is invariant and gives finite mass to compact
sets and positive mass to nonempty open sets. -/
@[toAdditive]
instance is_haar_measure_haar_measure (K₀ : positive_compacts G) : is_haar_measure (haar_measure K₀) :=
  by 
    apply is_haar_measure_of_is_compact_nonempty_interior _ (is_mul_left_invariant_haar_measure K₀) K₀.1 K₀.2.1 K₀.2.2
    ·
      simp only [haar_measure_self]
      exact one_ne_zero
    ·
      simp only [haar_measure_self]
      exact Ennreal.coe_ne_top

/-- `haar` is some choice of a Haar measure, on a locally compact group. -/
@[reducible, toAdditive "`add_haar` is some choice of a Haar measure, on a locally compact\nadditive group."]
def haar [LocallyCompactSpace G] : Measureₓ G :=
  haar_measure$ Classical.choice (TopologicalSpace.nonempty_positive_compacts G)

section Unique

variable[second_countable_topology G]{μ : Measureₓ G}[sigma_finite μ]

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Haar measure is unique up to scaling. More precisely: every σ-finite left invariant measure
  is a scalar multiple of the Haar measure. -/
@[to_additive #[]]
theorem haar_measure_unique
(hμ : is_mul_left_invariant μ)
(K₀ : positive_compacts G) : «expr = »(μ, «expr • »(μ K₀.1, haar_measure K₀)) :=
begin
  ext1 [] [ident s, ident hs],
  have [] [] [":=", expr measure_mul_measure_eq hμ (is_mul_left_invariant_haar_measure K₀) K₀.2.1 hs],
  rw ["[", expr haar_measure_self, ",", expr one_mul, "]"] ["at", ident this],
  rw ["[", "<-", expr this (by norm_num [] []), ",", expr smul_apply, "]"] []
end

@[toAdditive]
theorem regular_of_is_mul_left_invariant (hμ : is_mul_left_invariant μ) {K} (hK : IsCompact K)
  (h2K : (Interior K).Nonempty) (hμK : μ K ≠ ∞) : regular μ :=
  by 
    rw [haar_measure_unique hμ ⟨K, hK, h2K⟩]
    exact regular.smul hμK

end Unique

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident is_add_haar_measure_eq_smul_is_add_haar_measure]]
theorem is_haar_measure_eq_smul_is_haar_measure
[locally_compact_space G]
[second_countable_topology G]
(μ ν : measure G)
[is_haar_measure μ]
[is_haar_measure ν] : «expr∃ , »((c : «exprℝ≥0∞»()), «expr ∧ »(«expr ≠ »(c, 0), «expr ∧ »(«expr ≠ »(c, «expr∞»()), «expr = »(μ, «expr • »(c, ν))))) :=
begin
  have [ident K] [":", expr positive_compacts G] [":=", expr classical.choice (topological_space.nonempty_positive_compacts G)],
  have [ident νpos] [":", expr «expr < »(0, ν K.1)] [":=", expr haar_pos_of_nonempty_interior _ K.2.2],
  have [ident νlt] [":", expr «expr < »(ν K.1, «expr∞»())] [":=", expr is_compact.haar_lt_top _ K.2.1],
  refine [expr ⟨«expr / »(μ K.1, ν K.1), _, _, _⟩],
  { simp [] [] ["only"] ["[", expr νlt.ne, ",", expr (μ.haar_pos_of_nonempty_interior K.property.right).ne', ",", expr ne.def, ",", expr ennreal.div_zero_iff, ",", expr not_false_iff, ",", expr or_self, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr div_eq_mul_inv, ",", expr νpos.ne', ",", expr (is_compact.haar_lt_top μ K.property.left).ne, ",", expr or_self, ",", expr ennreal.inv_eq_top, ",", expr with_top.mul_eq_top_iff, ",", expr ne.def, ",", expr not_false_iff, ",", expr and_false, ",", expr false_and, "]"] [] [] },
  { calc
      «expr = »(μ, «expr • »(μ K.1, haar_measure K)) : haar_measure_unique (is_mul_left_invariant_haar μ) K
      «expr = »(..., «expr • »(«expr / »(μ K.1, ν K.1), «expr • »(ν K.1, haar_measure K))) : by rw ["[", expr smul_smul, ",", expr div_eq_mul_inv, ",", expr mul_assoc, ",", expr ennreal.inv_mul_cancel νpos.ne' νlt.ne, ",", expr mul_one, "]"] []
      «expr = »(..., «expr • »(«expr / »(μ K.1, ν K.1), ν)) : by rw ["<-", expr haar_measure_unique (is_mul_left_invariant_haar ν) K] [] }
end

-- error in MeasureTheory.Measure.Haar: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any Haar measure is invariant under inversion in a commutative group. -/
@[to_additive #[]]
theorem map_haar_inv
{G : Type*}
[comm_group G]
[topological_space G]
[topological_group G]
[t2_space G]
[measurable_space G]
[borel_space G]
[locally_compact_space G]
[second_countable_topology G]
(μ : measure G)
[is_haar_measure μ] : «expr = »(measure.map has_inv.inv μ, μ) :=
begin
  haveI [] [":", expr is_haar_measure (measure.map has_inv.inv μ)] [":=", expr is_haar_measure_map μ (mul_equiv.inv G) continuous_inv continuous_inv],
  obtain ["⟨", ident c, ",", ident cpos, ",", ident clt, ",", ident hc, "⟩", ":", expr «expr∃ , »((c : «exprℝ≥0∞»()), «expr ∧ »(«expr ≠ »(c, 0), «expr ∧ »(«expr ≠ »(c, «expr∞»()), «expr = »(measure.map has_inv.inv μ, «expr • »(c, μ))))), ":=", expr is_haar_measure_eq_smul_is_haar_measure _ _],
  have [] [":", expr «expr = »(map has_inv.inv (map has_inv.inv μ), «expr • »(«expr ^ »(c, 2), μ))] [],
  by simp [] [] ["only"] ["[", expr hc, ",", expr smul_smul, ",", expr pow_two, ",", expr linear_map.map_smul, "]"] [] [],
  have [ident μeq] [":", expr «expr = »(μ, «expr • »(«expr ^ »(c, 2), μ))] [],
  { rw ["[", expr map_map continuous_inv.measurable continuous_inv.measurable, "]"] ["at", ident this],
    { simpa [] [] ["only"] ["[", expr inv_involutive, ",", expr involutive.comp_self, ",", expr map_id, "]"] [] [] },
    all_goals { apply_instance } },
  have [ident K] [":", expr positive_compacts G] [":=", expr classical.choice (topological_space.nonempty_positive_compacts G)],
  have [] [":", expr «expr = »(«expr * »(«expr ^ »(c, 2), μ K.1), «expr * »(«expr ^ »(1, 2), μ K.1))] [],
  by { conv_rhs [] [] { rw [expr μeq] },
    change [expr «expr = »(«expr * »(«expr ^ »(c, 2), μ K.1), «expr * »(«expr ^ »(1, 2), «expr * »(«expr ^ »(c, 2), μ K.1)))] [] [],
    rw ["[", expr one_pow, ",", expr one_mul, "]"] [] },
  have [] [":", expr «expr = »(«expr ^ »(c, 2), «expr ^ »(1, 2))] [":=", expr (ennreal.mul_eq_mul_right (haar_pos_of_nonempty_interior _ K.2.2).ne' (is_compact.haar_lt_top _ K.2.1).ne).1 this],
  have [] [":", expr «expr = »(c, 1)] [":=", expr (ennreal.pow_strict_mono two_ne_zero).injective this],
  rw ["[", expr hc, ",", expr this, ",", expr one_smul, "]"] []
end

@[simp, toAdditive]
theorem haar_preimage_inv {G : Type _} [CommGroupₓ G] [TopologicalSpace G] [TopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [second_countable_topology G] (μ : Measureₓ G)
  [is_haar_measure μ] (s : Set G) : μ (s⁻¹) = μ s :=
  calc μ (s⁻¹) = measure.map HasInv.inv μ s := ((Homeomorph.inv G).toMeasurableEquiv.map_apply s).symm 
    _ = μ s :=
    by 
      rw [map_haar_inv]
    

end Measureₓ

end MeasureTheory

