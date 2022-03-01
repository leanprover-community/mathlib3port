/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
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


noncomputable section

open Set Inv Function TopologicalSpace MeasurableSpace

open_locale Nnreal Classical Ennreal Pointwise TopologicalSpace

variable {G : Type _} [Groupₓ G]

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
@[to_additive add_index "additive version of `measure_theory.measure.haar.index`"]
def index (K V : Set G) : ℕ :=
  Inf <| Finset.card '' { t : Finset G | K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V }

@[to_additive add_index_empty]
theorem index_empty {V : Set G} : index ∅ V = 0 := by
  simp only [index, Nat.Inf_eq_zero]
  left
  use ∅
  simp only [Finset.card_empty, empty_subset, mem_set_of_eq, eq_self_iff_true, and_selfₓ]

variable [TopologicalSpace G]

/-- `prehaar K₀ U K` is a weighted version of the index, defined as `(K : U)/(K₀ : U)`.
  In the applications `K₀` is compact with non-empty interior, `U` is open containing `1`,
  and `K` is any compact set.
  The argument `K` is a (bundled) compact set, so that we can consider `prehaar K₀ U` as an
  element of `haar_product` (below). -/
@[to_additive "additive version of `measure_theory.measure.haar.prehaar`"]
def prehaar (K₀ U : Set G) (K : Compacts G) : ℝ :=
  (index (K : Set G) U : ℝ) / index K₀ U

@[to_additive]
theorem prehaar_empty (K₀ : PositiveCompacts G) {U : Set G} : prehaar (K₀ : Set G) U ⊥ = 0 := by
  rw [prehaar, compacts.coe_bot, index_empty, Nat.cast_zeroₓ, zero_div]

@[to_additive]
theorem prehaar_nonneg (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G) : 0 ≤ prehaar (K₀ : Set G) U K := by
  apply div_nonneg <;> norm_cast <;> apply zero_le

/-- `haar_product K₀` is the product of intervals `[0, (K : K₀)]`, for all compact sets `K`.
  For all `U`, we can show that `prehaar K₀ U ∈ haar_product K₀`. -/
@[to_additive "additive version of `measure_theory.measure.haar.haar_product`"]
def HaarProduct (K₀ : Set G) : Set (Compacts G → ℝ) :=
  Pi Univ fun K => Icc 0 <| index (K : Set G) K₀

@[simp, to_additive]
theorem mem_prehaar_empty {K₀ : Set G} {f : Compacts G → ℝ} :
    f ∈ HaarProduct K₀ ↔ ∀ K : Compacts G, f K ∈ Icc (0 : ℝ) (index (K : Set G) K₀) := by
  simp only [haar_product, pi, forall_prop_of_true, mem_univ, mem_set_of_eq]

/-- The closure of the collection of elements of the form `prehaar K₀ U`,
  for `U` open neighbourhoods of `1`, contained in `V`. The closure is taken in the space
  `compacts G → ℝ`, with the topology of pointwise convergence.
  We show that the intersection of all these sets is nonempty, and the Haar measure
  on compact sets is defined to be an element in the closure of this intersection. -/
@[to_additive "additive version of `measure_theory.measure.haar.cl_prehaar`"]
def ClPrehaar (K₀ : Set G) (V : OpenNhdsOf (1 : G)) : Set (Compacts G → ℝ) :=
  Closure <| prehaar K₀ '' { U : Set G | U ⊆ V.1 ∧ IsOpen U ∧ (1 : G) ∈ U }

variable [TopologicalGroup G]

/-!
### Lemmas about `index`
-/


/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/
@[to_additive add_index_defined]
theorem index_defined {K V : Set G} (hK : IsCompact K) (hV : (Interior V).Nonempty) :
    ∃ n : ℕ, n ∈ Finset.card '' { t : Finset G | K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V } := by
  rcases compact_covered_by_mul_left_translates hK hV with ⟨t, ht⟩
  exact ⟨t.card, t, ht, rfl⟩

@[to_additive add_index_elim]
theorem index_elim {K V : Set G} (hK : IsCompact K) (hV : (Interior V).Nonempty) :
    ∃ t : Finset G, (K ⊆ ⋃ g ∈ t, (fun h => g * h) ⁻¹' V) ∧ Finset.card t = index K V := by
  have := Nat.Inf_mem (index_defined hK hV)
  rwa [mem_image] at this

@[to_additive le_add_index_mul]
theorem le_index_mul (K₀ : PositiveCompacts G) (K : Compacts G) {V : Set G} (hV : (Interior V).Nonempty) :
    index (K : Set G) V ≤ index (K : Set G) K₀ * index (K₀ : Set G) V := by
  obtain ⟨s, h1s, h2s⟩ := index_elim K.compact K₀.interior_nonempty
  obtain ⟨t, h1t, h2t⟩ := index_elim K₀.compact hV
  rw [← h2s, ← h2t, mul_comm]
  refine' le_transₓ _ Finset.mul_card_le
  apply Nat.Inf_le
  refine' ⟨_, _, rfl⟩
  rw [mem_set_of_eq]
  refine' subset.trans h1s _
  apply Union₂_subset
  intro g₁ hg₁
  rw [preimage_subset_iff]
  intro g₂ hg₂
  have := h1t hg₂
  rcases this with ⟨_, ⟨g₃, rfl⟩, A, ⟨hg₃, rfl⟩, h2V⟩
  rw [mem_preimage, ← mul_assoc] at h2V
  exact mem_bUnion (Finset.mul_mem_mul hg₃ hg₁) h2V

@[to_additive add_index_pos]
theorem index_pos (K : PositiveCompacts G) {V : Set G} (hV : (Interior V).Nonempty) : 0 < index (K : Set G) V := by
  unfold index
  rw [Nat.Inf_def, Nat.find_pos, mem_image]
  · rintro ⟨t, h1t, h2t⟩
    rw [Finset.card_eq_zero] at h2t
    subst h2t
    obtain ⟨g, hg⟩ := K.interior_nonempty
    show g ∈ (∅ : Set G)
    convert h1t (interior_subset hg)
    symm
    apply bUnion_empty
    
  · exact index_defined K.compact hV
    

@[to_additive add_index_mono]
theorem index_mono {K K' V : Set G} (hK' : IsCompact K') (h : K ⊆ K') (hV : (Interior V).Nonempty) :
    index K V ≤ index K' V := by
  rcases index_elim hK' hV with ⟨s, h1s, h2s⟩
  apply Nat.Inf_le
  rw [mem_image]
  refine' ⟨s, subset.trans h h1s, h2s⟩

@[to_additive add_index_union_le]
theorem index_union_le (K₁ K₂ : Compacts G) {V : Set G} (hV : (Interior V).Nonempty) :
    index (K₁.1 ∪ K₂.1) V ≤ index K₁.1 V + index K₂.1 V := by
  rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩
  rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩
  rw [← h2s, ← h2t]
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

@[to_additive add_index_union_eq]
theorem index_union_eq (K₁ K₂ : Compacts G) {V : Set G} (hV : (Interior V).Nonempty)
    (h : Disjoint (K₁.1 * V⁻¹) (K₂.1 * V⁻¹)) : index (K₁.1 ∪ K₂.1) V = index K₁.1 V + index K₂.1 V := by
  apply le_antisymmₓ (index_union_le K₁ K₂ hV)
  rcases index_elim (K₁.2.union K₂.2) hV with ⟨s, h1s, h2s⟩
  rw [← h2s]
  have :
    ∀ K : Set G,
      (K ⊆ ⋃ g ∈ s, (fun h => g * h) ⁻¹' V) →
        index K V ≤ (s.filter fun g => ((fun h : G => g * h) ⁻¹' V ∩ K).Nonempty).card :=
    by
    intro K hK
    apply Nat.Inf_le
    refine' ⟨_, _, rfl⟩
    rw [mem_set_of_eq]
    intro g hg
    rcases hK hg with ⟨_, ⟨g₀, rfl⟩, _, ⟨h1g₀, rfl⟩, h2g₀⟩
    simp only [mem_preimage] at h2g₀
    simp only [mem_Union]
    use g₀
    constructor
    · simp only [Finset.mem_filter, h1g₀, true_andₓ]
      use g
      simp only [hg, h2g₀, mem_inter_eq, mem_preimage, and_selfₓ]
      
    exact h2g₀
  refine'
    le_transₓ
      (add_le_add (this K₁.1 <| subset.trans (subset_union_left _ _) h1s)
        (this K₂.1 <| subset.trans (subset_union_right _ _) h1s))
      _
  rw [← Finset.card_union_eq, Finset.filter_union_right]
  exact s.card_filter_le _
  apply finset.disjoint_filter.mpr
  rintro g₁ h1g₁ ⟨g₂, h1g₂, h2g₂⟩ ⟨g₃, h1g₃, h2g₃⟩
  simp only [mem_preimage] at h1g₃ h1g₂
  apply @h g₁⁻¹
  constructor <;> simp only [Set.mem_inv, Set.mem_mul, exists_exists_and_eq_and, exists_and_distrib_left]
  · refine' ⟨_, h2g₂, (g₁ * g₂)⁻¹, _, _⟩
    simp only [inv_invₓ, h1g₂]
    simp only [mul_inv_rev, mul_inv_cancel_left]
    
  · refine' ⟨_, h2g₃, (g₁ * g₃)⁻¹, _, _⟩
    simp only [inv_invₓ, h1g₃]
    simp only [mul_inv_rev, mul_inv_cancel_left]
    

@[to_additive add_left_add_index_le]
theorem mul_left_index_le {K : Set G} (hK : IsCompact K) {V : Set G} (hV : (Interior V).Nonempty) (g : G) :
    index ((fun h => g * h) '' K) V ≤ index K V := by
  rcases index_elim hK hV with ⟨s, h1s, h2s⟩
  rw [← h2s]
  apply Nat.Inf_le
  rw [mem_image]
  refine' ⟨s.map (Equivₓ.mulRight g⁻¹).toEmbedding, _, Finset.card_map _⟩
  · simp only [mem_set_of_eq]
    refine' subset.trans (image_subset _ h1s) _
    rintro _ ⟨g₁, ⟨_, ⟨g₂, rfl⟩, ⟨_, ⟨hg₂, rfl⟩, hg₁⟩⟩, rfl⟩
    simp only [mem_preimage] at hg₁
    simp only [exists_prop, mem_Union, Finset.mem_map, Equivₓ.coe_mul_right, exists_exists_and_eq_and, mem_preimage,
      Equivₓ.to_embedding_apply]
    refine' ⟨_, hg₂, _⟩
    simp only [mul_assoc, hg₁, inv_mul_cancel_leftₓ]
    

@[to_additive is_left_invariant_add_index]
theorem is_left_invariant_index {K : Set G} (hK : IsCompact K) (g : G) {V : Set G} (hV : (Interior V).Nonempty) :
    index ((fun h => g * h) '' K) V = index K V := by
  refine' le_antisymmₓ (mul_left_index_le hK hV g) _
  convert mul_left_index_le (hK.image <| continuous_mul_left g) hV g⁻¹
  rw [image_image]
  symm
  convert image_id' _
  ext h
  apply inv_mul_cancel_leftₓ

/-!
### Lemmas about `prehaar`
-/


@[to_additive add_prehaar_le_add_index]
theorem prehaar_le_index (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G) (hU : (Interior U).Nonempty) :
    prehaar (K₀ : Set G) U K ≤ index (K : Set G) K₀ := by
  unfold prehaar
  rw [div_le_iff] <;> norm_cast
  · apply le_index_mul K₀ K hU
    
  · exact index_pos K₀ hU
    

@[to_additive]
theorem prehaar_pos (K₀ : PositiveCompacts G) {U : Set G} (hU : (Interior U).Nonempty) {K : Set G} (h1K : IsCompact K)
    (h2K : (Interior K).Nonempty) : 0 < prehaar (K₀ : Set G) U ⟨K, h1K⟩ := by
  apply div_pos <;> norm_cast
  apply index_pos ⟨⟨K, h1K⟩, h2K⟩ hU
  exact index_pos K₀ hU

@[to_additive]
theorem prehaar_mono {K₀ : PositiveCompacts G} {U : Set G} (hU : (Interior U).Nonempty) {K₁ K₂ : Compacts G}
    (h : (K₁ : Set G) ⊆ K₂.1) : prehaar (K₀ : Set G) U K₁ ≤ prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]
  rw [div_le_div_right]
  exact_mod_cast index_mono K₂.2 h hU
  exact_mod_cast index_pos K₀ hU

@[to_additive]
theorem prehaar_self {K₀ : PositiveCompacts G} {U : Set G} (hU : (Interior U).Nonempty) :
    prehaar (K₀ : Set G) U K₀.toCompacts = 1 :=
  div_self <|
    ne_of_gtₓ <| by
      exact_mod_cast index_pos K₀ hU

@[to_additive]
theorem prehaar_sup_le {K₀ : PositiveCompacts G} {U : Set G} (K₁ K₂ : Compacts G) (hU : (Interior U).Nonempty) :
    prehaar (K₀ : Set G) U (K₁⊔K₂) ≤ prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]
  rw [div_add_div_same, div_le_div_right]
  exact_mod_cast index_union_le K₁ K₂ hU
  exact_mod_cast index_pos K₀ hU

@[to_additive]
theorem prehaar_sup_eq {K₀ : PositiveCompacts G} {U : Set G} {K₁ K₂ : Compacts G} (hU : (Interior U).Nonempty)
    (h : Disjoint (K₁.1 * U⁻¹) (K₂.1 * U⁻¹)) :
    prehaar (K₀ : Set G) U (K₁⊔K₂) = prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]
  rw [div_add_div_same]
  congr
  exact_mod_cast index_union_eq K₁ K₂ hU h

@[to_additive]
theorem is_left_invariant_prehaar {K₀ : PositiveCompacts G} {U : Set G} (hU : (Interior U).Nonempty) (g : G)
    (K : Compacts G) : prehaar (K₀ : Set G) U (K.map _ <| continuous_mul_left g) = prehaar (K₀ : Set G) U K := by
  simp only [prehaar, compacts.coe_map, is_left_invariant_index K.compact _ hU]

/-!
### Lemmas about `haar_product`
-/


@[to_additive]
theorem prehaar_mem_haar_product (K₀ : PositiveCompacts G) {U : Set G} (hU : (Interior U).Nonempty) :
    prehaar (K₀ : Set G) U ∈ HaarProduct (K₀ : Set G) := by
  rintro ⟨K, hK⟩ h2K
  rw [mem_Icc]
  exact ⟨prehaar_nonneg K₀ _, prehaar_le_index K₀ _ hU⟩

@[to_additive]
theorem nonempty_Inter_cl_prehaar (K₀ : PositiveCompacts G) :
    (HaarProduct (K₀ : Set G) ∩ ⋂ V : OpenNhdsOf (1 : G), ClPrehaar K₀ V).Nonempty := by
  have : IsCompact (haar_product (K₀ : Set G)) := by
    apply is_compact_univ_pi
    intro K
    apply is_compact_Icc
  refine' this.inter_Inter_nonempty (cl_prehaar K₀) (fun s => is_closed_closure) fun t => _
  let V₀ := ⋂ V ∈ t, (V : open_nhds_of 1).1
  have h1V₀ : IsOpen V₀ := by
    apply is_open_bInter
    apply finite_mem_finset
    rintro ⟨V, hV⟩ h2V
    exact hV.1
  have h2V₀ : (1 : G) ∈ V₀ := by
    simp only [mem_Inter]
    rintro ⟨V, hV⟩ h2V
    exact hV.2
  refine' ⟨prehaar K₀ V₀, _⟩
  constructor
  · apply prehaar_mem_haar_product K₀
    use 1
    rwa [h1V₀.interior_eq]
    
  · simp only [mem_Inter]
    rintro ⟨V, hV⟩ h2V
    apply subset_closure
    apply mem_image_of_mem
    rw [mem_set_of_eq]
    exact ⟨subset.trans (Inter_subset _ ⟨V, hV⟩) (Inter_subset _ h2V), h1V₀, h2V₀⟩
    

/-!
### Lemmas about `chaar`
-/


/-- This is the "limit" of `prehaar K₀ U K` as `U` becomes a smaller and smaller open
  neighborhood of `(1 : G)`. More precisely, it is defined to be an arbitrary element
  in the intersection of all the sets `cl_prehaar K₀ V` in `haar_product K₀`.
  This is roughly equal to the Haar measure on compact sets,
  but it can differ slightly. We do know that
  `haar_measure K₀ (interior K) ≤ chaar K₀ K ≤ haar_measure K₀ K`. -/
@[to_additive add_chaar "additive version of `measure_theory.measure.haar.chaar`"]
def chaar (K₀ : PositiveCompacts G) (K : Compacts G) : ℝ :=
  Classical.some (nonempty_Inter_cl_prehaar K₀) K

@[to_additive add_chaar_mem_add_haar_product]
theorem chaar_mem_haar_product (K₀ : PositiveCompacts G) : chaar K₀ ∈ HaarProduct (K₀ : Set G) :=
  (Classical.some_spec (nonempty_Inter_cl_prehaar K₀)).1

@[to_additive add_chaar_mem_cl_add_prehaar]
theorem chaar_mem_cl_prehaar (K₀ : PositiveCompacts G) (V : OpenNhdsOf (1 : G)) : chaar K₀ ∈ ClPrehaar (K₀ : Set G) V :=
  by
  have := (Classical.some_spec (nonempty_Inter_cl_prehaar K₀)).2
  rw [mem_Inter] at this
  exact this V

@[to_additive add_chaar_nonneg]
theorem chaar_nonneg (K₀ : PositiveCompacts G) (K : Compacts G) : 0 ≤ chaar K₀ K := by
  have := chaar_mem_haar_product K₀ K (mem_univ _)
  rw [mem_Icc] at this
  exact this.1

@[to_additive add_chaar_empty]
theorem chaar_empty (K₀ : PositiveCompacts G) : chaar K₀ ⊥ = 0 := by
  let eval : (compacts G → ℝ) → ℝ := fun f => f ⊥
  have : Continuous eval := continuous_apply ⊥
  show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨Set.Univ, is_open_univ, mem_univ _⟩)
  unfold cl_prehaar
  rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    apply prehaar_empty
    
  · apply continuous_iff_is_closed.mp this
    exact is_closed_singleton
    

@[to_additive add_chaar_self]
theorem chaar_self (K₀ : PositiveCompacts G) : chaar K₀ K₀.toCompacts = 1 := by
  let eval : (compacts G → ℝ) → ℝ := fun f => f K₀.to_compacts
  have : Continuous eval := continuous_apply _
  show chaar K₀ ∈ eval ⁻¹' {(1 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨Set.Univ, is_open_univ, mem_univ _⟩)
  unfold cl_prehaar
  rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    apply prehaar_self
    rw [h2U.interior_eq]
    exact ⟨1, h3U⟩
    
  · apply continuous_iff_is_closed.mp this
    exact is_closed_singleton
    

@[to_additive add_chaar_mono]
theorem chaar_mono {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G} (h : (K₁ : Set G) ⊆ K₂) : chaar K₀ K₁ ≤ chaar K₀ K₂ :=
  by
  let eval : (compacts G → ℝ) → ℝ := fun f => f K₂ - f K₁
  have : Continuous eval := (continuous_apply K₂).sub (continuous_apply K₁)
  rw [← sub_nonneg]
  show chaar K₀ ∈ eval ⁻¹' Ici (0 : ℝ)
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨Set.Univ, is_open_univ, mem_univ _⟩)
  unfold cl_prehaar
  rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    simp only [mem_preimage, mem_Ici, eval, sub_nonneg]
    apply prehaar_mono _ h
    rw [h2U.interior_eq]
    exact ⟨1, h3U⟩
    
  · apply continuous_iff_is_closed.mp this
    exact is_closed_Ici
    

@[to_additive add_chaar_sup_le]
theorem chaar_sup_le {K₀ : PositiveCompacts G} (K₁ K₂ : Compacts G) : chaar K₀ (K₁⊔K₂) ≤ chaar K₀ K₁ + chaar K₀ K₂ := by
  let eval : (compacts G → ℝ) → ℝ := fun f => f K₁ + f K₂ - f (K₁⊔K₂)
  have : Continuous eval :=
    ((@continuous_add ℝ _ _ _).comp ((continuous_apply K₁).prod_mk (continuous_apply K₂))).sub
      (continuous_apply (K₁⊔K₂))
  rw [← sub_nonneg]
  show chaar K₀ ∈ eval ⁻¹' Ici (0 : ℝ)
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨Set.Univ, is_open_univ, mem_univ _⟩)
  unfold cl_prehaar
  rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    simp only [mem_preimage, mem_Ici, eval, sub_nonneg]
    apply prehaar_sup_le
    rw [h2U.interior_eq]
    exact ⟨1, h3U⟩
    
  · apply continuous_iff_is_closed.mp this
    exact is_closed_Ici
    

@[to_additive add_chaar_sup_eq]
theorem chaar_sup_eq [T2Space G] {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G} (h : Disjoint K₁.1 K₂.1) :
    chaar K₀ (K₁⊔K₂) = chaar K₀ K₁ + chaar K₀ K₂ := by
  rcases compact_compact_separated K₁.2 K₂.2 (disjoint_iff.mp h) with ⟨U₁, U₂, h1U₁, h1U₂, h2U₁, h2U₂, hU⟩
  rw [← disjoint_iff_inter_eq_empty] at hU
  rcases compact_open_separated_mul K₁.2 h1U₁ h2U₁ with ⟨V₁, h1V₁, h2V₁, h3V₁⟩
  rcases compact_open_separated_mul K₂.2 h1U₂ h2U₂ with ⟨V₂, h1V₂, h2V₂, h3V₂⟩
  let eval : (compacts G → ℝ) → ℝ := fun f => f K₁ + f K₂ - f (K₁⊔K₂)
  have : Continuous eval :=
    ((@continuous_add ℝ _ _ _).comp ((continuous_apply K₁).prod_mk (continuous_apply K₂))).sub
      (continuous_apply (K₁⊔K₂))
  rw [eq_comm, ← sub_eq_zero]
  show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  let V := V₁ ∩ V₂
  apply
    mem_of_subset_of_mem _
      (chaar_mem_cl_prehaar K₀
        ⟨V⁻¹, (IsOpen.inter h1V₁ h1V₂).Preimage continuous_inv, by
          simp only [mem_inv, one_inv, h2V₁, h2V₂, V, mem_inter_eq, true_andₓ]⟩)
  unfold cl_prehaar
  rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    simp only [mem_preimage, eval, sub_eq_zero, mem_singleton_iff]
    rw [eq_comm]
    apply prehaar_sup_eq
    · rw [h2U.interior_eq]
      exact ⟨1, h3U⟩
      
    · refine' disjoint_of_subset _ _ hU
      · refine' subset.trans (mul_subset_mul subset.rfl _) h3V₁
        exact subset.trans (inv_subset.mpr h1U) (inter_subset_left _ _)
        
      · refine' subset.trans (mul_subset_mul subset.rfl _) h3V₂
        exact subset.trans (inv_subset.mpr h1U) (inter_subset_right _ _)
        
      
    
  · apply continuous_iff_is_closed.mp this
    exact is_closed_singleton
    

@[to_additive is_left_invariant_add_chaar]
theorem is_left_invariant_chaar {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) :
    chaar K₀ (K.map _ <| continuous_mul_left g) = chaar K₀ K := by
  let eval : (compacts G → ℝ) → ℝ := fun f => f (K.map _ <| continuous_mul_left g) - f K
  have : Continuous eval := (continuous_apply (K.map _ _)).sub (continuous_apply K)
  rw [← sub_eq_zero]
  show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)}
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨Set.Univ, is_open_univ, mem_univ _⟩)
  unfold cl_prehaar
  rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    simp only [mem_singleton_iff, mem_preimage, eval, sub_eq_zero]
    apply is_left_invariant_prehaar
    rw [h2U.interior_eq]
    exact ⟨1, h3U⟩
    
  · apply continuous_iff_is_closed.mp this
    exact is_closed_singleton
    

variable [T2Space G]

/-- The function `chaar` interpreted in `ℝ≥0`, as a content -/
@[to_additive "additive version of `measure_theory.measure.haar.haar_content`"]
def haarContent (K₀ : PositiveCompacts G) : Content G where
  toFun := fun K => ⟨chaar K₀ K, chaar_nonneg _ _⟩
  mono' := fun K₁ K₂ h => by
    simp only [← Nnreal.coe_le_coe, Subtype.coe_mk, chaar_mono, h]
  sup_disjoint' := fun K₁ K₂ h => by
    simp only [chaar_sup_eq h]
    rfl
  sup_le' := fun K₁ K₂ => by
    simp only [← Nnreal.coe_le_coe, Nnreal.coe_add, Subtype.coe_mk, chaar_sup_le]

/-! We only prove the properties for `haar_content` that we use at least twice below. -/


@[to_additive]
theorem haar_content_apply (K₀ : PositiveCompacts G) (K : Compacts G) :
    haarContent K₀ K = show Nnreal from ⟨chaar K₀ K, chaar_nonneg _ _⟩ :=
  rfl

/-- The variant of `chaar_self` for `haar_content` -/
@[to_additive]
theorem haar_content_self {K₀ : PositiveCompacts G} : haarContent K₀ K₀.toCompacts = 1 := by
  simp_rw [← Ennreal.coe_one, haar_content_apply, Ennreal.coe_eq_coe, chaar_self]
  rfl

/-- The variant of `is_left_invariant_chaar` for `haar_content` -/
@[to_additive]
theorem is_left_invariant_haar_content {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) :
    haarContent K₀ (K.map _ <| continuous_mul_left g) = haarContent K₀ K := by
  simpa only [Ennreal.coe_eq_coe, ← Nnreal.coe_eq, haar_content_apply] using is_left_invariant_chaar g K

@[to_additive]
theorem haar_content_outer_measure_self_pos {K₀ : PositiveCompacts G} : 0 < (haarContent K₀).OuterMeasure K₀ := by
  apply ennreal.zero_lt_one.trans_le
  rw [content.outer_measure_eq_infi]
  refine' le_binfi _
  intro U hU
  refine' le_infi _
  intro h2U
  refine' le_transₓ (le_of_eqₓ _) (le_bsupr K₀.to_compacts h2U)
  exact haar_content_self.symm

end Haar

open Haar

/-!
### The Haar measure
-/


variable [TopologicalSpace G] [T2Space G] [TopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The Haar measure on the locally compact group `G`, scaled so that `haar_measure K₀ K₀ = 1`. -/
@[to_additive
      "The Haar measure on the locally compact additive group `G`,\nscaled so that `add_haar_measure K₀ K₀ = 1`."]
def haarMeasure (K₀ : PositiveCompacts G) : Measure G :=
  ((haarContent K₀).OuterMeasure K₀)⁻¹ • (haarContent K₀).Measure

@[to_additive]
theorem haar_measure_apply {K₀ : PositiveCompacts G} {s : Set G} (hs : MeasurableSet s) :
    haarMeasure K₀ s = (haarContent K₀).OuterMeasure s / (haarContent K₀).OuterMeasure K₀ := by
  change ((haar_content K₀).OuterMeasure K₀)⁻¹ * (haar_content K₀).Measure s = _
  simp only [hs, div_eq_mul_inv, mul_comm, content.measure_apply]

@[to_additive]
instance is_mul_left_invariant_haar_measure (K₀ : PositiveCompacts G) : IsMulLeftInvariant (haarMeasure K₀) := by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  rw [haar_measure_apply hA, haar_measure_apply (measurable_const_mul g hA)]
  congr 1
  apply content.is_mul_left_invariant_outer_measure
  apply is_left_invariant_haar_content

@[to_additive]
theorem haar_measure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ K₀ = 1 := by
  have : LocallyCompactSpace G := K₀.locally_compact_space_of_group
  rw [haar_measure_apply K₀.compact.measurable_set, Ennreal.div_self]
  · rw [← pos_iff_ne_zero]
    exact haar_content_outer_measure_self_pos
    
  · exact (content.outer_measure_lt_top_of_is_compact _ K₀.compact).Ne
    

/-- The Haar measure is regular. -/
@[to_additive]
instance regular_haar_measure {K₀ : PositiveCompacts G} : (haarMeasure K₀).regular := by
  have : LocallyCompactSpace G := K₀.locally_compact_space_of_group
  apply regular.smul
  rw [Ennreal.inv_ne_top]
  exact haar_content_outer_measure_self_pos.ne'

/-- The Haar measure is sigma-finite in a second countable group. -/
@[to_additive]
instance sigma_finite_haar_measure [SecondCountableTopology G] {K₀ : PositiveCompacts G} :
    SigmaFinite (haarMeasure K₀) := by
  have : LocallyCompactSpace G := K₀.locally_compact_space_of_group
  infer_instance

/-- The Haar measure is a Haar measure, i.e., it is invariant and gives finite mass to compact
sets and positive mass to nonempty open sets. -/
@[to_additive]
instance is_haar_measure_haar_measure (K₀ : PositiveCompacts G) : IsHaarMeasure (haarMeasure K₀) := by
  apply is_haar_measure_of_is_compact_nonempty_interior (haar_measure K₀) K₀ K₀.compact K₀.interior_nonempty
  · simp only [haar_measure_self]
    exact one_ne_zero
    
  · simp only [haar_measure_self]
    exact Ennreal.coe_ne_top
    

/-- `haar` is some choice of a Haar measure, on a locally compact group. -/
@[reducible, to_additive "`add_haar` is some choice of a Haar measure, on a locally compact\nadditive group."]
def haar [LocallyCompactSpace G] : Measure G :=
  haar_measure <| Classical.arbitrary _

section SecondCountable

variable [SecondCountableTopology G]

/-- The Haar measure is unique up to scaling. More precisely: every σ-finite left invariant measure
  is a scalar multiple of the Haar measure.
  This is slightly weaker than assuming that `μ` is a Haar measure (in particular we don't require
  `μ ≠ 0`). -/
@[to_additive]
theorem haar_measure_unique (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ] (K₀ : PositiveCompacts G) :
    μ = μ K₀ • haarMeasure K₀ := by
  refine'
    (measure_eq_div_smul μ (haar_measure K₀) K₀.compact.measurable_set
          (measure_pos_of_nonempty_interior _ K₀.interior_nonempty).ne' K₀.compact.measure_lt_top.ne).trans
      _
  rw [haar_measure_self, Ennreal.div_one]

example [LocallyCompactSpace G] (μ : Measure G) [IsHaarMeasure μ] (K₀ : PositiveCompacts G) :
    μ = μ K₀.1 • haarMeasure K₀ :=
  haar_measure_unique μ K₀

/-- To show that an invariant σ-finite measure is regular it is sufficient to show that it is finite
  on some compact set with non-empty interior. -/
@[to_additive]
theorem regular_of_is_mul_left_invariant {μ : Measure G} [SigmaFinite μ] [IsMulLeftInvariant μ] {K : Set G}
    (hK : IsCompact K) (h2K : (Interior K).Nonempty) (hμK : μ K ≠ ∞) : Regular μ := by
  rw [haar_measure_unique μ ⟨⟨K, hK⟩, h2K⟩]
  exact regular.smul hμK

@[to_additive is_add_haar_measure_eq_smul_is_add_haar_measure]
theorem is_haar_measure_eq_smul_is_haar_measure [LocallyCompactSpace G] (μ ν : Measure G) [IsHaarMeasure μ]
    [IsHaarMeasure ν] : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • ν := by
  have K : positive_compacts G := Classical.arbitrary _
  have νpos : 0 < ν K := measure_pos_of_nonempty_interior _ K.interior_nonempty
  have νne : ν K ≠ ∞ := K.compact.measure_lt_top.ne
  refine' ⟨μ K / ν K, _, _, _⟩
  · simp only [νne, (μ.measure_pos_of_nonempty_interior K.interior_nonempty).ne', Ne.def, Ennreal.div_zero_iff,
      not_false_iff, or_selfₓ]
    
  · simp only [div_eq_mul_inv, νpos.ne', K.compact.measure_lt_top.Ne, or_selfₓ, Ennreal.inv_eq_top,
      WithTop.mul_eq_top_iff, Ne.def, not_false_iff, and_falseₓ, false_andₓ]
    
  · calc μ = μ K • haar_measure K := haar_measure_unique μ K _ = (μ K / ν K) • ν K • haar_measure K := by
        rw [smul_smul, div_eq_mul_inv, mul_assoc, Ennreal.inv_mul_cancel νpos.ne' νne, mul_oneₓ]_ = (μ K / ν K) • ν :=
        by
        rw [← haar_measure_unique ν K]
    

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 90) regular_of_is_haar_measure [LocallyCompactSpace G] (μ : Measure G) [IsHaarMeasure μ] :
    Regular μ := by
  have K : positive_compacts G := Classical.arbitrary _
  obtain ⟨c, c0, ctop, hμ⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • haar_measure K :=
    is_haar_measure_eq_smul_is_haar_measure μ _
  rw [hμ]
  exact regular.smul ctop

end SecondCountable

/-- Any Haar measure is invariant under inversion in a commutative group. -/
@[to_additive]
theorem map_haar_inv {G : Type _} [CommGroupₓ G] [TopologicalSpace G] [TopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (μ : Measure G)
    [IsHaarMeasure μ] : Measure.map Inv.inv μ = μ := by
  -- the image measure is a Haar measure. By uniqueness up to multiplication, it is of the form
  -- `c μ`. Applying again inversion, one gets the measure `c^2 μ`. But since inversion is an
  -- involution, this is also `μ`. Hence, `c^2 = 1`, which implies `c = 1`.
  have : is_haar_measure (measure.map Inv.inv μ) := is_haar_measure_map μ (MulEquiv.inv G) continuous_inv continuous_inv
  obtain ⟨c, cpos, clt, hc⟩ : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ measure.map Inv.inv μ = c • μ :=
    is_haar_measure_eq_smul_is_haar_measure _ _
  have : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    simp only [hc, smul_smul, pow_two, LinearMap.map_smul]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at this
    · simpa only [inv_involutive, involutive.comp_self, map_id]
      
    all_goals
      infer_instance
  have K : positive_compacts G := Classical.arbitrary _
  have : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have : c ^ 2 = 1 ^ 2 :=
    (Ennreal.mul_eq_mul_right (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.compact.measure_lt_top.ne).1
      this
  have : c = 1 := (Ennreal.pow_strict_mono two_ne_zero).Injective this
  rw [hc, this, one_smul]

@[simp, to_additive]
theorem haar_preimage_inv {G : Type _} [CommGroupₓ G] [TopologicalSpace G] [TopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (μ : Measure G)
    [IsHaarMeasure μ] (s : Set G) : μ s⁻¹ = μ s :=
  calc
    μ s⁻¹ = Measure.map Inv.inv μ s := ((Homeomorph.inv G).toMeasurableEquiv.map_apply s).symm
    _ = μ s := by
      rw [map_haar_inv]
    

end Measureₓ

end MeasureTheory

