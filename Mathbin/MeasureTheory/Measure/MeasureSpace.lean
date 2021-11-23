import Mathbin.MeasureTheory.Measure.NullMeasurable 
import Mathbin.MeasureTheory.MeasurableSpace

/-!
# Measure spaces

The definition of a measure and a measure space are in `measure_theory.measure_space_def`, with
only a few basic properties. This file provides many more properties of these objects.
This separation allows the measurability tactic to import only the file `measure_space_def`, and to
be available in `measure_space` (through `measurable_space`).

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

We introduce the following typeclasses for measures:

* `is_probability_measure μ`: `μ univ = 1`;
* `is_finite_measure μ`: `μ univ < ∞`;
* `sigma_finite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite;
* `is_locally_finite_measure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`;
* `has_no_atoms μ` : `∀ x, μ {x} = 0`; possibly should be redefined as
  `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `measure.of_measurable` and `outer_measure.to_measure` are two important ways to define a measure.

## Implementation notes

Given `μ : measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `measure.of_measurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `outer_measure.to_measure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generate_from_of_Union`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generate_from_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generate_from_of_Union` using
  `C ∪ {univ}`, but is easier to work with.

A `measure_space` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/


noncomputable theory

open Classical Set

open Filter hiding map

open Function MeasurableSpace

open_locale Classical TopologicalSpace BigOperators Filter Ennreal Nnreal

variable{α β γ δ ι : Type _}

namespace MeasureTheory

section 

variable{m : MeasurableSpace α}{μ μ₁ μ₂ : Measureₓ α}{s s₁ s₂ t : Set α}

instance ae_is_measurably_generated : is_measurably_generated μ.ae :=
  ⟨fun s hs =>
      let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs
      ⟨«expr ᶜ» t, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩

theorem measure_union (hd : Disjoint s₁ s₂) (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : μ (s₁ ∪ s₂) = μ s₁+μ s₂ :=
  measure_union₀ h₁.null_measurable_set h₂.null_measurable_set hd

theorem measure_add_measure_compl (h : MeasurableSet s) : (μ s+μ («expr ᶜ» s)) = μ univ :=
  by 
    rw [←union_compl_self s, measure_union _ h h.compl]
    exact disjoint_compl_right

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measure_bUnion
{s : set β}
{f : β → set α}
(hs : countable s)
(hd : s.pairwise «expr on »(disjoint, f))
(h : ∀
 b «expr ∈ » s, measurable_set (f b)) : «expr = »(μ «expr⋃ , »((b «expr ∈ » s), f b), «expr∑' , »((p : s), μ (f p))) :=
begin
  haveI [] [] [":=", expr hs.to_encodable],
  rw [expr bUnion_eq_Union] [],
  exact [expr measure_Union «expr $ »(hd.on_injective subtype.coe_injective, λ x, x.2) (λ x, h x x.2)]
end

theorem measure_sUnion {S : Set (Set α)} (hs : countable S) (hd : S.pairwise Disjoint)
  (h : ∀ s _ : s ∈ S, MeasurableSet s) : μ (⋃₀S) = ∑'s : S, μ s :=
  by 
    rw [sUnion_eq_bUnion, measure_bUnion hs hd h]

theorem measure_bUnion_finset {s : Finset ι} {f : ι → Set α} (hd : Set.Pairwise («expr↑ » s) (Disjoint on f))
  (hm : ∀ b _ : b ∈ s, MeasurableSet (f b)) : μ (⋃(b : _)(_ : b ∈ s), f b) = ∑p in s, μ (f p) :=
  by 
    rw [←Finset.sum_attach, Finset.attach_eq_univ, ←tsum_fintype]
    exact measure_bUnion s.countable_to_set hd hm

/-- If `s` is a countable set, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem tsum_measure_preimage_singleton {s : Set β} (hs : countable s) {f : α → β}
  (hf : ∀ y _ : y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑'b : s, μ (f ⁻¹' {«expr↑ » b})) = μ (f ⁻¹' s) :=
  by 
    rw [←Set.bUnion_preimage_singleton, measure_bUnion hs (pairwise_disjoint_fiber _ _) hf]

/-- If `s` is a `finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem sum_measure_preimage_singleton (s : Finset β) {f : α → β} (hf : ∀ y _ : y ∈ s, MeasurableSet (f ⁻¹' {y})) :
  (∑b in s, μ (f ⁻¹' {b})) = μ (f ⁻¹' «expr↑ » s) :=
  by 
    simp only [←measure_bUnion_finset (pairwise_disjoint_fiber _ _) hf, Finset.set_bUnion_preimage_singleton]

theorem measure_diff_null' (h : μ (s₁ ∩ s₂) = 0) : μ (s₁ \ s₂) = μ s₁ :=
  measure_congr$ diff_ae_eq_self.2 h

theorem measure_diff_null (h : μ s₂ = 0) : μ (s₁ \ s₂) = μ s₁ :=
  measure_diff_null'$ measure_mono_null (inter_subset_right _ _) h

theorem measure_diff (h : s₂ ⊆ s₁) (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) (h_fin : μ s₂ ≠ ∞) :
  μ (s₁ \ s₂) = μ s₁ - μ s₂ :=
  by 
    refine' (Ennreal.add_sub_self' h_fin).symm.trans _ 
    rw [←measure_union disjoint_diff h₂ (h₁.diff h₂), union_diff_cancel h]

theorem le_measure_diff : μ s₁ - μ s₂ ≤ μ (s₁ \ s₂) :=
  tsub_le_iff_left.2$
    calc μ s₁ ≤ μ (s₂ ∪ s₁) := measure_mono (subset_union_right _ _)
      _ = μ (s₂ ∪ s₁ \ s₂) := congr_argₓ μ union_diff_self.symm 
      _ ≤ μ s₂+μ (s₁ \ s₂) := measure_union_le _ _
      

theorem measure_diff_lt_of_lt_add (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) (hs' : μ s ≠ ∞) {ε : ℝ≥0∞}
  (h : μ t < μ s+ε) : μ (t \ s) < ε :=
  by 
    rw [measure_diff hst ht hs hs']
    rw [add_commₓ] at h 
    exact Ennreal.sub_lt_of_lt_add (measure_mono hst) h

theorem measure_diff_le_iff_le_add (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) (hs' : μ s ≠ ∞)
  {ε : ℝ≥0∞} : μ (t \ s) ≤ ε ↔ μ t ≤ μ s+ε :=
  by 
    rwa [measure_diff hst ht hs hs', tsub_le_iff_left]

theorem measure_eq_measure_of_null_diff {s t : Set α} (hst : s ⊆ t) (h_nulldiff : μ (t.diff s) = 0) : μ s = μ t :=
  by 
    rw [←diff_diff_cancel_left hst, ←@measure_diff_null _ _ _ t _ h_nulldiff]
    rfl

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measure_eq_measure_of_between_null_diff
{s₁ s₂ s₃ : set α}
(h12 : «expr ⊆ »(s₁, s₂))
(h23 : «expr ⊆ »(s₂, s₃))
(h_nulldiff : «expr = »(μ «expr \ »(s₃, s₁), 0)) : «expr ∧ »(«expr = »(μ s₁, μ s₂), «expr = »(μ s₂, μ s₃)) :=
begin
  have [ident le12] [":", expr «expr ≤ »(μ s₁, μ s₂)] [":=", expr measure_mono h12],
  have [ident le23] [":", expr «expr ≤ »(μ s₂, μ s₃)] [":=", expr measure_mono h23],
  have [ident key] [":", expr «expr ≤ »(μ s₃, μ s₁)] [":=", expr calc
     «expr = »(μ s₃, μ «expr ∪ »(«expr \ »(s₃, s₁), s₁)) : by rw [expr diff_union_of_subset (h12.trans h23)] []
     «expr ≤ »(..., «expr + »(μ «expr \ »(s₃, s₁), μ s₁)) : measure_union_le _ _
     «expr = »(..., μ s₁) : by simp [] [] ["only"] ["[", expr h_nulldiff, ",", expr zero_add, "]"] [] []],
  exact [expr ⟨le12.antisymm (le23.trans key), le23.antisymm (key.trans le12)⟩]
end

theorem measure_eq_measure_smaller_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃)
  (h_nulldiff : μ (s₃.diff s₁) = 0) : μ s₁ = μ s₂ :=
  (measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).1

theorem measure_eq_measure_larger_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃)
  (h_nulldiff : μ (s₃.diff s₁) = 0) : μ s₂ = μ s₃ :=
  (measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).2

theorem measure_compl (h₁ : MeasurableSet s) (h_fin : μ s ≠ ∞) : μ («expr ᶜ» s) = μ univ - μ s :=
  by 
    rw [compl_eq_univ_diff]
    exact measure_diff (subset_univ s) MeasurableSet.univ h₁ h_fin

theorem sum_measure_le_measure_univ {s : Finset ι} {t : ι → Set α} (h : ∀ i _ : i ∈ s, MeasurableSet (t i))
  (H : Set.Pairwise («expr↑ » s) (Disjoint on t)) : (∑i in s, μ (t i)) ≤ μ (univ : Set α) :=
  by 
    rw [←measure_bUnion_finset H h]
    exact measure_mono (subset_univ _)

theorem tsum_measure_le_measure_univ {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i)) (H : Pairwise (Disjoint on s)) :
  (∑'i, μ (s i)) ≤ μ (univ : Set α) :=
  by 
    rw [Ennreal.tsum_eq_supr_sum]
    exact supr_le fun s => sum_measure_le_measure_univ (fun i hi => hs i) fun i hi j hj hij => H i j hij

/-- If `sᵢ` is a countable family of measurable sets such that all pairwise intersections have
measure `0`, then there exists a subordinate family `tᵢ ⊆ sᵢ` of measurable pairwise disjoint sets
such that `tᵢ =ᵐ[μ] sᵢ`. -/
theorem exists_subordinate_pairwise_disjoint [Encodable ι] {s : ι → Set α} (h : ∀ i, MeasurableSet (s i))
  (hd : Pairwise fun i j => μ (s i ∩ s j) = 0) :
  ∃ t : ι → Set α, (∀ i, t i ⊆ s i) ∧ (∀ i, s i =ᵐ[μ] t i) ∧ (∀ i, MeasurableSet (t i)) ∧ Pairwise (Disjoint on t) :=
  by 
    set t : ι → Set α := fun i => s i \ ⋃(j : _)(_ : j ∈ («expr ᶜ» {i} : Set ι)), s j 
    refine'
      ⟨t, fun i => diff_subset _ _, fun i => _,
        fun i => (h i).diff$ MeasurableSet.bUnion (countable_encodable _)$ fun j hj => h j, _⟩
    ·
      refine' eventually_le.antisymm _ (diff_subset _ _).EventuallyLe 
      rw [ae_le_set, sdiff_sdiff_right_self, inf_eq_inter]
      simp only [inter_Union, measure_bUnion_null_iff (countable_encodable _)]
      exact fun j hj => hd _ _ (Ne.symm hj)
    ·
      rintro i j hne x ⟨⟨hsi, -⟩, -, Hj⟩
      exact Hj (mem_bUnion hne hsi)

theorem measure_Union_of_null_inter [Encodable ι] {f : ι → Set α} (h : ∀ i, MeasurableSet (f i))
  (hn : Pairwise ((fun S T => μ (S ∩ T) = 0) on f)) : μ (⋃i, f i) = ∑'i, μ (f i) :=
  by 
    rcases exists_subordinate_pairwise_disjoint h hn with ⟨t, ht_sub, ht_eq, htm, htd⟩
    calc μ (⋃i, f i) = μ (⋃i, t i) := measure_congr (EventuallyEq.countable_Union ht_eq)_ = ∑'i, μ (t i) :=
      measure_Union htd htm _ = ∑'i, μ (f i) := tsum_congr fun i => measure_congr (ht_eq i).symm

/-- Pigeonhole principle for measure spaces: if `∑' i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_tsum_measure {m : MeasurableSpace α} (μ : Measureₓ α) {s : ι → Set α}
  (hs : ∀ i, MeasurableSet (s i)) (H : μ (univ : Set α) < ∑'i, μ (s i)) :
  ∃ (i j : _)(h : i ≠ j), (s i ∩ s j).Nonempty :=
  by 
    contrapose! H 
    apply tsum_measure_le_measure_univ hs 
    exact fun i j hij x hx => H i j hij ⟨x, hx⟩

/-- Pigeonhole principle for measure spaces: if `s` is a `finset` and
`∑ i in s, μ (t i) > μ univ`, then one of the intersections `t i ∩ t j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_sum_measure {m : MeasurableSpace α} (μ : Measureₓ α) {s : Finset ι}
  {t : ι → Set α} (h : ∀ i _ : i ∈ s, MeasurableSet (t i)) (H : μ (univ : Set α) < ∑i in s, μ (t i)) :
  ∃ (i : _)(_ : i ∈ s)(j : _)(_ : j ∈ s)(h : i ≠ j), (t i ∩ t j).Nonempty :=
  by 
    contrapose! H 
    apply sum_measure_le_measure_univ h 
    exact fun i hi j hj hij x hx => H i hi j hj hij ⟨x, hx⟩

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Continuity from below: the measure of the union of a directed sequence of measurable sets
is the supremum of the measures. -/
theorem measure_Union_eq_supr
[encodable ι]
{s : ι → set α}
(h : ∀ i, measurable_set (s i))
(hd : directed ((«expr ⊆ »)) s) : «expr = »(μ «expr⋃ , »((i), s i), «expr⨆ , »((i), μ (s i))) :=
begin
  casesI [expr is_empty_or_nonempty ι] [],
  { simp [] [] ["only"] ["[", expr supr_of_empty, ",", expr Union, "]"] [] [],
    exact [expr measure_empty] },
  refine [expr le_antisymm _ «expr $ »(supr_le, λ i, «expr $ »(measure_mono, subset_Union _ _))],
  have [] [":", expr ∀
   n, measurable_set (disjointed (λ
     n, «expr⋃ , »((b «expr ∈ » encodable.decode₂ ι n), s b)) n)] [":=", expr measurable_set.disjointed (measurable_set.bUnion_decode₂ h)],
  rw ["[", "<-", expr encodable.Union_decode₂, ",", "<-", expr Union_disjointed, ",", expr measure_Union (disjoint_disjointed _) this, ",", expr ennreal.tsum_eq_supr_nat, "]"] [],
  simp [] [] ["only"] ["[", "<-", expr measure_bUnion_finset ((disjoint_disjointed _).set_pairwise _) (λ
    n _, this n), "]"] [] [],
  refine [expr supr_le (λ n, _)],
  refine [expr le_trans (_ : «expr ≤ »(_, μ «expr⋃ , »((k «expr ∈ » finset.range n)
     (i «expr ∈ » encodable.decode₂ ι k), s i))) _],
  exact [expr measure_mono (bUnion_mono (λ k hk, disjointed_subset _ _))],
  simp [] [] ["only"] ["[", "<-", expr finset.set_bUnion_option_to_finset, ",", "<-", expr finset.set_bUnion_bUnion, "]"] [] [],
  generalize [] [":"] [expr «expr = »((finset.range n).bUnion (λ k, (encodable.decode₂ ι k).to_finset), t)],
  rcases [expr hd.finset_le t, "with", "⟨", ident i, ",", ident hi, "⟩"],
  exact [expr le_supr_of_le i «expr $ »(measure_mono, bUnion_subset hi)]
end

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measure_bUnion_eq_supr
{s : ι → set α}
{t : set ι}
(ht : countable t)
(h : ∀ i «expr ∈ » t, measurable_set (s i))
(hd : directed_on «expr on »((«expr ⊆ »), s) t) : «expr = »(μ «expr⋃ , »((i «expr ∈ » t), s i), «expr⨆ , »((i «expr ∈ » t), μ (s i))) :=
begin
  haveI [] [] [":=", expr ht.to_encodable],
  rw ["[", expr bUnion_eq_Union, ",", expr measure_Union_eq_supr (set_coe.forall'.1 h) hd.directed_coe, ",", expr supr_subtype', "]"] [],
  refl
end

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the infimum of the measures. -/
theorem measure_Inter_eq_infi
[encodable ι]
{s : ι → set α}
(h : ∀ i, measurable_set (s i))
(hd : directed ((«expr ⊇ »)) s)
(hfin : «expr∃ , »((i), «expr ≠ »(μ (s i), «expr∞»()))) : «expr = »(μ «expr⋂ , »((i), s i), «expr⨅ , »((i), μ (s i))) :=
begin
  rcases [expr hfin, "with", "⟨", ident k, ",", ident hk, "⟩"],
  have [] [":", expr ∀ t «expr ⊆ » s k, «expr ≠ »(μ t, «expr∞»())] [],
  from [expr λ t ht, ne_top_of_le_ne_top hk (measure_mono ht)],
  rw ["[", "<-", expr ennreal.sub_sub_cancel (by exact [expr hk]) (infi_le _ k), ",", expr ennreal.sub_infi, ",", "<-", expr ennreal.sub_sub_cancel (by exact [expr hk]) (measure_mono (Inter_subset _ k)), ",", "<-", expr measure_diff (Inter_subset _ k) (h k) (measurable_set.Inter h) (this _ (Inter_subset _ k)), ",", expr diff_Inter, ",", expr measure_Union_eq_supr, "]"] [],
  { congr' [1] [],
    refine [expr le_antisymm «expr $ »(supr_le_supr2, λ i, _) «expr $ »(supr_le_supr, λ i, _)],
    { rcases [expr hd i k, "with", "⟨", ident j, ",", ident hji, ",", ident hjk, "⟩"],
      use [expr j],
      rw ["[", "<-", expr measure_diff hjk (h _) (h _) (this _ hjk), "]"] [],
      exact [expr measure_mono (diff_subset_diff_right hji)] },
    { rw ["[", expr tsub_le_iff_right, ",", "<-", expr measure_union disjoint_diff.symm ((h k).diff (h i)) (h i), ",", expr set.union_comm, "]"] [],
      exact [expr measure_mono «expr $ »(diff_subset_iff.1, subset.refl _)] } },
  { exact [expr λ i, (h k).diff (h i)] },
  { exact [expr hd.mono_comp _ (λ _ _, diff_subset_diff_right)] }
end

/-- Continuity from below: the measure of the union of an increasing sequence of measurable sets
is the limit of the measures. -/
theorem tendsto_measure_Union [SemilatticeSup ι] [Encodable ι] {s : ι → Set α} (hs : ∀ n, MeasurableSet (s n))
  (hm : Monotone s) : tendsto (μ ∘ s) at_top (𝓝 (μ (⋃n, s n))) :=
  by 
    rw [measure_Union_eq_supr hs (directed_of_sup hm)]
    exact tendsto_at_top_supr fun n m hnm => measure_mono$ hm hnm

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the limit of the measures. -/
theorem tendsto_measure_Inter [Encodable ι] [SemilatticeSup ι] {s : ι → Set α} (hs : ∀ n, MeasurableSet (s n))
  (hm : Antitone s) (hf : ∃ i, μ (s i) ≠ ∞) : tendsto (μ ∘ s) at_top (𝓝 (μ (⋂n, s n))) :=
  by 
    rw [measure_Inter_eq_infi hs (directed_of_sup hm) hf]
    exact tendsto_at_top_infi fun n m hnm => measure_mono$ hm hnm

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- One direction of the **Borel-Cantelli lemma**: if (sᵢ) is a sequence of sets such
that `∑ μ sᵢ` is finite, then the limit superior of the `sᵢ` is a null set. -/
theorem measure_limsup_eq_zero
{s : exprℕ() → set α}
(hs : «expr ≠ »(«expr∑' , »((i), μ (s i)), «expr∞»())) : «expr = »(μ (limsup at_top s), 0) :=
begin
  set [] [ident t] [":", expr exprℕ() → set α] [":="] [expr λ n, to_measurable μ (s n)] [],
  have [ident ht] [":", expr «expr ≠ »(«expr∑' , »((i), μ (t i)), «expr∞»())] [],
  by simpa [] [] ["only"] ["[", expr t, ",", expr measure_to_measurable, "]"] [] ["using", expr hs],
  suffices [] [":", expr «expr = »(μ (limsup at_top t), 0)],
  { have [ident A] [":", expr «expr ≤ »(s, t)] [":=", expr λ n, subset_to_measurable μ (s n)],
    exact [expr measure_mono_null (limsup_le_limsup (eventually_of_forall A) is_cobounded_le_of_bot is_bounded_le_of_top) this] },
  simp [] [] ["only"] ["[", expr limsup_eq_infi_supr_of_nat', ",", expr set.infi_eq_Inter, ",", expr set.supr_eq_Union, ",", "<-", expr nonpos_iff_eq_zero, "]"] [] [],
  refine [expr le_of_tendsto_of_tendsto' (tendsto_measure_Inter (λ
     i, measurable_set.Union (λ
      b, measurable_set_to_measurable _ _)) _ ⟨0, ne_top_of_le_ne_top ht (measure_Union_le t)⟩) (ennreal.tendsto_sum_nat_add «expr ∘ »(μ, t) ht) (λ
    n, measure_Union_le _)],
  intros [ident n, ident m, ident hnm, ident x],
  simp [] [] ["only"] ["[", expr set.mem_Union, "]"] [] [],
  exact [expr λ
   ⟨i, hi⟩, ⟨«expr + »(i, «expr - »(m, n)), by simpa [] [] ["only"] ["[", expr add_assoc, ",", expr tsub_add_cancel_of_le hnm, "]"] [] ["using", expr hi]⟩]
end

theorem measure_if {x : β} {t : Set β} {s : Set α} : μ (if x ∈ t then s else ∅) = indicator t (fun _ => μ s) x :=
  by 
    splitIfs <;> simp [h]

end 

section OuterMeasure

variable[ms : MeasurableSpace α]{s t : Set α}

include ms

/-- Obtain a measure by giving an outer measure where all sets in the σ-algebra are
  Carathéodory measurable. -/
def outer_measure.to_measure (m : outer_measure α) (h : ms ≤ m.caratheodory) : Measureₓ α :=
  measure.of_measurable (fun s _ => m s) m.empty fun f hf hd => m.Union_eq_of_caratheodory (fun i => h _ (hf i)) hd

theorem le_to_outer_measure_caratheodory (μ : Measureₓ α) : ms ≤ μ.to_outer_measure.caratheodory :=
  by 
    intro s hs 
    rw [to_outer_measure_eq_induced_outer_measure]
    refine' outer_measure.of_function_caratheodory fun t => le_infi$ fun ht => _ 
    rw [←measure_eq_extend (ht.inter hs), ←measure_eq_extend (ht.diff hs), ←measure_union _ (ht.inter hs) (ht.diff hs),
      inter_union_diff]
    exact le_reflₓ _ 
    exact fun x ⟨⟨_, h₁⟩, _, h₂⟩ => h₂ h₁

@[simp]
theorem to_measure_to_outer_measure (m : outer_measure α) (h : ms ≤ m.caratheodory) :
  (m.to_measure h).toOuterMeasure = m.trim :=
  rfl

@[simp]
theorem to_measure_apply (m : outer_measure α) (h : ms ≤ m.caratheodory) {s : Set α} (hs : MeasurableSet s) :
  m.to_measure h s = m s :=
  m.trim_eq hs

theorem le_to_measure_apply (m : outer_measure α) (h : ms ≤ m.caratheodory) (s : Set α) : m s ≤ m.to_measure h s :=
  m.le_trim s

theorem to_measure_apply₀ (m : outer_measure α) (h : ms ≤ m.caratheodory) {s : Set α}
  (hs : null_measurable_set s (m.to_measure h)) : m.to_measure h s = m s :=
  by 
    refine' le_antisymmₓ _ (le_to_measure_apply _ _ _)
    rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, heq⟩
    calc m.to_measure h s = m.to_measure h t := measure_congr HEq.symm _ = m t := to_measure_apply m h htm _ ≤ m s :=
      m.mono hts

@[simp]
theorem to_outer_measure_to_measure {μ : Measureₓ α} :
  μ.to_outer_measure.to_measure (le_to_outer_measure_caratheodory _) = μ :=
  measure.ext$ fun s => μ.to_outer_measure.trim_eq

@[simp]
theorem bounded_by_measure (μ : Measureₓ α) : outer_measure.bounded_by μ = μ.to_outer_measure :=
  μ.to_outer_measure.bounded_by_eq_self

end OuterMeasure

variable{m0 : MeasurableSpace α}[MeasurableSpace β][MeasurableSpace γ]

variable{μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measureₓ α}{s s' t : Set α}

theorem measure_inter_add_diff (s : Set α) (ht : MeasurableSet t) : (μ (s ∩ t)+μ (s \ t)) = μ s :=
  (le_to_outer_measure_caratheodory μ _ ht _).symm

theorem measure_union_add_inter (s : Set α) (ht : MeasurableSet t) : (μ (s ∪ t)+μ (s ∩ t)) = μ s+μ t :=
  by 
    rw [←measure_inter_add_diff (s ∪ t) ht, Set.union_inter_cancel_right, union_diff_right,
      ←measure_inter_add_diff s ht]
    acRfl

theorem measure_union_add_inter' (hs : MeasurableSet s) (t : Set α) : (μ (s ∪ t)+μ (s ∩ t)) = μ s+μ t :=
  by 
    rw [union_comm, inter_comm, measure_union_add_inter t hs, add_commₓ]

namespace Measureₓ

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `u` is a superset of `t` with the same measure (both sets possibly non-measurable), then
for any measurable set `s` one also has `μ (t ∩ s) = μ (u ∩ s)`. -/
theorem measure_inter_eq_of_measure_eq
{s t u : set α}
(hs : measurable_set s)
(h : «expr = »(μ t, μ u))
(htu : «expr ⊆ »(t, u))
(ht_ne_top : «expr ≠ »(μ t, «expr∞»())) : «expr = »(μ «expr ∩ »(t, s), μ «expr ∩ »(u, s)) :=
begin
  rw [expr h] ["at", ident ht_ne_top],
  refine [expr le_antisymm (measure_mono (inter_subset_inter_left _ htu)) _],
  have [ident A] [":", expr «expr ≤ »(«expr + »(μ «expr ∩ »(u, s), μ «expr \ »(u, s)), «expr + »(μ «expr ∩ »(t, s), μ «expr \ »(u, s)))] [":=", expr calc
     «expr = »(«expr + »(μ «expr ∩ »(u, s), μ «expr \ »(u, s)), μ u) : measure_inter_add_diff _ hs
     «expr = »(..., μ t) : h.symm
     «expr = »(..., «expr + »(μ «expr ∩ »(t, s), μ «expr \ »(t, s))) : (measure_inter_add_diff _ hs).symm
     «expr ≤ »(..., «expr + »(μ «expr ∩ »(t, s), μ «expr \ »(u, s))) : add_le_add le_rfl (measure_mono (diff_subset_diff htu subset.rfl))],
  have [ident B] [":", expr «expr ≠ »(μ «expr \ »(u, s), «expr∞»())] [":=", expr (lt_of_le_of_lt (measure_mono (diff_subset _ _)) ht_ne_top.lt_top).ne],
  exact [expr ennreal.le_of_add_le_add_right B A]
end

theorem measure_to_measurable_inter {s t : Set α} (hs : MeasurableSet s) (ht : μ t ≠ ∞) :
  μ (to_measurable μ t ∩ s) = μ (t ∩ s) :=
  (measure_inter_eq_of_measure_eq hs (measure_to_measurable t).symm (subset_to_measurable μ t) ht).symm

/-! ### The `ℝ≥0∞`-module of measures -/


instance  [MeasurableSpace α] : HasZero (Measureₓ α) :=
  ⟨{ toOuterMeasure := 0, m_Union := fun f hf hd => tsum_zero.symm, trimmed := outer_measure.trim_zero }⟩

@[simp]
theorem zero_to_outer_measure {m : MeasurableSpace α} : (0 : Measureₓ α).toOuterMeasure = 0 :=
  rfl

@[simp, normCast]
theorem coe_zero {m : MeasurableSpace α} : «expr⇑ » (0 : Measureₓ α) = 0 :=
  rfl

theorem eq_zero_of_is_empty [IsEmpty α] {m : MeasurableSpace α} (μ : Measureₓ α) : μ = 0 :=
  ext$
    fun s hs =>
      by 
        simp only [eq_empty_of_is_empty s, measure_empty]

instance  [MeasurableSpace α] : Inhabited (Measureₓ α) :=
  ⟨0⟩

instance  [MeasurableSpace α] : Add (Measureₓ α) :=
  ⟨fun μ₁ μ₂ =>
      { toOuterMeasure := μ₁.to_outer_measure+μ₂.to_outer_measure,
        m_Union :=
          fun s hs hd =>
            show (μ₁ (⋃i, s i)+μ₂ (⋃i, s i)) = ∑'i, μ₁ (s i)+μ₂ (s i)by 
              rw [Ennreal.tsum_add, measure_Union hd hs, measure_Union hd hs],
        trimmed :=
          by 
            rw [outer_measure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp]
theorem add_to_outer_measure {m : MeasurableSpace α} (μ₁ μ₂ : Measureₓ α) :
  (μ₁+μ₂).toOuterMeasure = μ₁.to_outer_measure+μ₂.to_outer_measure :=
  rfl

@[simp, normCast]
theorem coe_add {m : MeasurableSpace α} (μ₁ μ₂ : Measureₓ α) : «expr⇑ » (μ₁+μ₂) = μ₁+μ₂ :=
  rfl

theorem add_apply {m : MeasurableSpace α} (μ₁ μ₂ : Measureₓ α) (s : Set α) : (μ₁+μ₂) s = μ₁ s+μ₂ s :=
  rfl

instance AddCommMonoidₓ [MeasurableSpace α] : AddCommMonoidₓ (Measureₓ α) :=
  to_outer_measure_injective.AddCommMonoid to_outer_measure zero_to_outer_measure add_to_outer_measure

instance  [MeasurableSpace α] : HasScalar ℝ≥0∞ (Measureₓ α) :=
  ⟨fun c μ =>
      { toOuterMeasure := c • μ.to_outer_measure,
        m_Union :=
          fun s hs hd =>
            by 
              simp [measure_Union, Ennreal.tsum_mul_left],
        trimmed :=
          by 
            rw [outer_measure.trim_smul, μ.trimmed] }⟩

@[simp]
theorem smul_to_outer_measure {m : MeasurableSpace α} (c : ℝ≥0∞) (μ : Measureₓ α) :
  (c • μ).toOuterMeasure = c • μ.to_outer_measure :=
  rfl

@[simp, normCast]
theorem coe_smul {m : MeasurableSpace α} (c : ℝ≥0∞) (μ : Measureₓ α) : «expr⇑ » (c • μ) = c • μ :=
  rfl

@[simp]
theorem smul_apply {m : MeasurableSpace α} (c : ℝ≥0∞) (μ : Measureₓ α) (s : Set α) : (c • μ) s = c*μ s :=
  rfl

instance  [MeasurableSpace α] : Module ℝ≥0∞ (Measureₓ α) :=
  injective.module ℝ≥0∞ ⟨to_outer_measure, zero_to_outer_measure, add_to_outer_measure⟩ to_outer_measure_injective
    smul_to_outer_measure

@[simp, normCast]
theorem coe_nnreal_smul {m : MeasurableSpace α} (c :  ℝ≥0 ) (μ : Measureₓ α) : «expr⇑ » (c • μ) = c • μ :=
  rfl

@[simp]
theorem coe_nnreal_smul_apply {m : MeasurableSpace α} (c :  ℝ≥0 ) (μ : Measureₓ α) (s : Set α) : (c • μ) s = c*μ s :=
  rfl

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measure_eq_left_of_subset_of_measure_add_eq
{s t : set α}
(h : «expr ≠ »(«expr + »(μ, ν) t, «expr∞»()))
(h' : «expr ⊆ »(s, t))
(h'' : «expr = »(«expr + »(μ, ν) s, «expr + »(μ, ν) t)) : «expr = »(μ s, μ t) :=
begin
  refine [expr le_antisymm (measure_mono h') _],
  have [] [":", expr «expr ≤ »(«expr + »(μ t, ν t), «expr + »(μ s, ν t))] [":=", expr calc
     «expr = »(«expr + »(μ t, ν t), «expr + »(μ s, ν s)) : h''.symm
     «expr ≤ »(..., «expr + »(μ s, ν t)) : add_le_add le_rfl (measure_mono h')],
  apply [expr ennreal.le_of_add_le_add_right _ this],
  simp [] [] ["only"] ["[", expr not_or_distrib, ",", expr ennreal.add_eq_top, ",", expr pi.add_apply, ",", expr ne.def, ",", expr coe_add, "]"] [] ["at", ident h],
  exact [expr h.2]
end

theorem measure_eq_right_of_subset_of_measure_add_eq {s t : Set α} (h : (μ+ν) t ≠ ∞) (h' : s ⊆ t)
  (h'' : (μ+ν) s = (μ+ν) t) : ν s = ν t :=
  by 
    rw [add_commₓ] at h'' h 
    exact measure_eq_left_of_subset_of_measure_add_eq h h' h''

theorem measure_to_measurable_add_inter_left {s t : Set α} (hs : MeasurableSet s) (ht : (μ+ν) t ≠ ∞) :
  μ (to_measurable (μ+ν) t ∩ s) = μ (t ∩ s) :=
  by 
    refine' (measure_inter_eq_of_measure_eq hs _ (subset_to_measurable _ _) _).symm
    ·
      refine' measure_eq_left_of_subset_of_measure_add_eq _ (subset_to_measurable _ _) (measure_to_measurable t).symm 
      rwa [measure_to_measurable t]
    ·
      simp only [not_or_distrib, Ennreal.add_eq_top, Pi.add_apply, Ne.def, coe_add] at ht 
      exact ht.1

theorem measure_to_measurable_add_inter_right {s t : Set α} (hs : MeasurableSet s) (ht : (μ+ν) t ≠ ∞) :
  ν (to_measurable (μ+ν) t ∩ s) = ν (t ∩ s) :=
  by 
    rw [add_commₓ] at ht⊢
    exact measure_to_measurable_add_inter_left hs ht

/-! ### The complete lattice of measures -/


/-- Measures are partially ordered.

The definition of less equal here is equivalent to the definition without the
measurable set condition, and this is shown by `measure.le_iff'`. It is defined
this way since, to prove `μ ≤ ν`, we may simply `intros s hs` instead of rewriting followed
by `intros s hs`. -/
instance  [MeasurableSpace α] : PartialOrderₓ (Measureₓ α) :=
  { le := fun m₁ m₂ => ∀ s, MeasurableSet s → m₁ s ≤ m₂ s, le_refl := fun m s hs => le_reflₓ _,
    le_trans := fun m₁ m₂ m₃ h₁ h₂ s hs => le_transₓ (h₁ s hs) (h₂ s hs),
    le_antisymm := fun m₁ m₂ h₁ h₂ => ext$ fun s hs => le_antisymmₓ (h₁ s hs) (h₂ s hs) }

theorem le_iff : μ₁ ≤ μ₂ ↔ ∀ s, MeasurableSet s → μ₁ s ≤ μ₂ s :=
  Iff.rfl

theorem to_outer_measure_le : μ₁.to_outer_measure ≤ μ₂.to_outer_measure ↔ μ₁ ≤ μ₂ :=
  by 
    rw [←μ₂.trimmed, outer_measure.le_trim_iff] <;> rfl

theorem le_iff' : μ₁ ≤ μ₂ ↔ ∀ s, μ₁ s ≤ μ₂ s :=
  to_outer_measure_le.symm

theorem lt_iff : μ < ν ↔ μ ≤ ν ∧ ∃ s, MeasurableSet s ∧ μ s < ν s :=
  lt_iff_le_not_leₓ.trans$
    and_congr Iff.rfl$
      by 
        simp only [le_iff, not_forall, not_leₓ, exists_prop]

theorem lt_iff' : μ < ν ↔ μ ≤ ν ∧ ∃ s, μ s < ν s :=
  lt_iff_le_not_leₓ.trans$
    and_congr Iff.rfl$
      by 
        simp only [le_iff', not_forall, not_leₓ]

instance covariant_add_le [MeasurableSpace α] : CovariantClass (Measureₓ α) (Measureₓ α) (·+·) (· ≤ ·) :=
  ⟨fun ν μ₁ μ₂ hμ s hs => add_le_add_left (hμ s hs) _⟩

protected theorem le_add_left (h : μ ≤ ν) : μ ≤ ν'+ν :=
  fun s hs => le_add_left (h s hs)

protected theorem le_add_right (h : μ ≤ ν) : μ ≤ ν+ν' :=
  fun s hs => le_add_right (h s hs)

section Inf

variable{m : Set (Measureₓ α)}

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem Inf_caratheodory
(s : set α)
(hs : measurable_set s) : (Inf «expr '' »(to_outer_measure, m)).caratheodory.measurable_set' s :=
begin
  rw ["[", expr outer_measure.Inf_eq_bounded_by_Inf_gen, "]"] [],
  refine [expr outer_measure.bounded_by_caratheodory (λ t, _)],
  simp [] [] ["only"] ["[", expr outer_measure.Inf_gen, ",", expr le_infi_iff, ",", expr ball_image_iff, ",", expr coe_to_outer_measure, ",", expr measure_eq_infi t, "]"] [] [],
  intros [ident μ, ident hμ, ident u, ident htu, ident hu],
  have [ident hm] [":", expr ∀
   {s t}, «expr ⊆ »(s, t) → «expr ≤ »(outer_measure.Inf_gen «expr '' »(to_outer_measure, m) s, μ t)] [],
  { intros [ident s, ident t, ident hst],
    rw ["[", expr outer_measure.Inf_gen_def, "]"] [],
    refine [expr infi_le_of_le μ.to_outer_measure (infi_le_of_le (mem_image_of_mem _ hμ) _)],
    rw ["[", expr to_outer_measure_apply, "]"] [],
    refine [expr measure_mono hst] },
  rw ["[", "<-", expr measure_inter_add_diff u hs, "]"] [],
  refine [expr add_le_add «expr $ »(hm, inter_subset_inter_left _ htu) «expr $ »(hm, diff_subset_diff_left htu)]
end

instance  [MeasurableSpace α] : HasInfₓ (Measureₓ α) :=
  ⟨fun m => (Inf (to_outer_measure '' m)).toMeasure$ Inf_caratheodory⟩

theorem Inf_apply (hs : MeasurableSet s) : Inf m s = Inf (to_outer_measure '' m) s :=
  to_measure_apply _ _ hs

private theorem measure_Inf_le (h : μ ∈ m) : Inf m ≤ μ :=
  have  : Inf (to_outer_measure '' m) ≤ μ.to_outer_measure := Inf_le (mem_image_of_mem _ h)
  fun s hs =>
    by 
      rw [Inf_apply hs, ←to_outer_measure_apply] <;> exact this s

private theorem measure_le_Inf (h : ∀ μ' _ : μ' ∈ m, μ ≤ μ') : μ ≤ Inf m :=
  have  : μ.to_outer_measure ≤ Inf (to_outer_measure '' m) :=
    le_Inf$ ball_image_of_ball$ fun μ hμ => to_outer_measure_le.2$ h _ hμ 
  fun s hs =>
    by 
      rw [Inf_apply hs, ←to_outer_measure_apply] <;> exact this s

instance  [MeasurableSpace α] : CompleteSemilatticeInf (Measureₓ α) :=
  { (by 
      infer_instance :
    PartialOrderₓ (Measureₓ α)),
    (by 
      infer_instance :
    HasInfₓ (Measureₓ α)) with
    Inf_le := fun s a => measure_Inf_le, le_Inf := fun s a => measure_le_Inf }

instance  [MeasurableSpace α] : CompleteLattice (Measureₓ α) :=
  { completeLatticeOfCompleteSemilatticeInf (Measureₓ α) with bot := 0,
    bot_le :=
      fun a s hs =>
        by 
          exact bot_le }

end Inf

protected theorem zero_le {m0 : MeasurableSpace α} (μ : Measureₓ α) : 0 ≤ μ :=
  bot_le

theorem nonpos_iff_eq_zero' : μ ≤ 0 ↔ μ = 0 :=
  μ.zero_le.le_iff_eq

@[simp]
theorem measure_univ_eq_zero : μ univ = 0 ↔ μ = 0 :=
  ⟨fun h => bot_unique$ fun s hs => trans_rel_left (· ≤ ·) (measure_mono (subset_univ s)) h, fun h => h.symm ▸ rfl⟩

/-! ### Pushforward and pullback -/


/-- Lift a linear map between `outer_measure` spaces such that for each measure `μ` every measurable
set is caratheodory-measurable w.r.t. `f μ` to a linear map between `measure` spaces. -/
def lift_linear {m0 : MeasurableSpace α} (f : outer_measure α →ₗ[ℝ≥0∞] outer_measure β)
  (hf : ∀ μ : Measureₓ α, ‹_› ≤ (f μ.to_outer_measure).caratheodory) : Measureₓ α →ₗ[ℝ≥0∞] Measureₓ β :=
  { toFun := fun μ => (f μ.to_outer_measure).toMeasure (hf μ),
    map_add' :=
      fun μ₁ μ₂ =>
        ext$
          fun s hs =>
            by 
              simp [hs],
    map_smul' :=
      fun c μ =>
        ext$
          fun s hs =>
            by 
              simp [hs] }

@[simp]
theorem lift_linear_apply {f : outer_measure α →ₗ[ℝ≥0∞] outer_measure β} hf {s : Set β} (hs : MeasurableSet s) :
  lift_linear f hf μ s = f μ.to_outer_measure s :=
  to_measure_apply _ _ hs

theorem le_lift_linear_apply {f : outer_measure α →ₗ[ℝ≥0∞] outer_measure β} hf (s : Set β) :
  f μ.to_outer_measure s ≤ lift_linear f hf μ s :=
  le_to_measure_apply _ _ s

/-- The pushforward of a measure. It is defined to be `0` if `f` is not a measurable function. -/
def map [MeasurableSpace α] (f : α → β) : Measureₓ α →ₗ[ℝ≥0∞] Measureₓ β :=
  if hf : Measurable f then
    lift_linear (outer_measure.map f)$ fun μ s hs t => le_to_outer_measure_caratheodory μ _ (hf hs) (f ⁻¹' t) else 0

/-- We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `measure_theory.measure.le_map_apply` and `measurable_equiv.map_apply`. -/
@[simp]
theorem map_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) : map f μ s = μ (f ⁻¹' s) :=
  by 
    simp [map, dif_pos hf, hs]

theorem map_to_outer_measure {f : α → β} (hf : Measurable f) :
  (map f μ).toOuterMeasure = (outer_measure.map f μ.to_outer_measure).trim :=
  by 
    rw [←trimmed, outer_measure.trim_eq_trim_iff]
    intro s hs 
    rw [coe_to_outer_measure, map_apply hf hs, outer_measure.map_apply, coe_to_outer_measure]

theorem map_of_not_measurable {f : α → β} (hf : ¬Measurable f) : map f μ = 0 :=
  by 
    rw [map, dif_neg hf, LinearMap.zero_apply]

@[simp]
theorem map_id : map id μ = μ :=
  ext$ fun s => map_apply measurable_id

theorem map_map {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) : map g (map f μ) = map (g ∘ f) μ :=
  ext$
    fun s hs =>
      by 
        simp [hf, hg, hs, hg hs, hg.comp hf, ←preimage_comp]

@[mono]
theorem map_mono (f : α → β) (h : μ ≤ ν) : map f μ ≤ map f ν :=
  if hf : Measurable f then
    fun s hs =>
      by 
        simp only [map_apply hf hs, h _ (hf hs)]
  else
    by 
      simp only [map_of_not_measurable hf, le_rfl]

/-- Even if `s` is not measurable, we can bound `map f μ s` from below.
  See also `measurable_equiv.map_apply`. -/
theorem le_map_apply {f : α → β} (hf : Measurable f) (s : Set β) : μ (f ⁻¹' s) ≤ map f μ s :=
  calc μ (f ⁻¹' s) ≤ μ (f ⁻¹' to_measurable (map f μ) s) := measure_mono$ preimage_mono$ subset_to_measurable _ _ 
    _ = map f μ (to_measurable (map f μ) s) := (map_apply hf$ measurable_set_to_measurable _ _).symm 
    _ = map f μ s := measure_to_measurable _
    

/-- Even if `s` is not measurable, `map f μ s = 0` implies that `μ (f ⁻¹' s) = 0`. -/
theorem preimage_null_of_map_null {f : α → β} (hf : Measurable f) {s : Set β} (hs : map f μ s = 0) : μ (f ⁻¹' s) = 0 :=
  nonpos_iff_eq_zero.mp$ (le_map_apply hf s).trans_eq hs

theorem tendsto_ae_map {f : α → β} (hf : Measurable f) : tendsto f μ.ae (map f μ).ae :=
  fun s hs => preimage_null_of_map_null hf hs

/-- Pullback of a `measure`. If `f` sends each `measurable` set to a `measurable` set, then for each
measurable set `s` we have `comap f μ s = μ (f '' s)`. -/
def comap [MeasurableSpace α] (f : α → β) : Measureₓ β →ₗ[ℝ≥0∞] Measureₓ α :=
  if hf : injective f ∧ ∀ s, MeasurableSet s → MeasurableSet (f '' s) then
    lift_linear (outer_measure.comap f)$
      fun μ s hs t =>
        by 
          simp only [coe_to_outer_measure, outer_measure.comap_apply, ←image_inter hf.1, image_diff hf.1]
          apply le_to_outer_measure_caratheodory 
          exact hf.2 s hs
  else 0

theorem comap_apply {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β) (hfi : injective f)
  (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measureₓ β) (hs : MeasurableSet s) :
  comap f μ s = μ (f '' s) :=
  by 
    rw [comap, dif_pos, lift_linear_apply _ hs, outer_measure.comap_apply, coe_to_outer_measure]
    exact ⟨hfi, hf⟩

/-! ### Restricting a measure -/


/-- Restrict a measure `μ` to a set `s` as an `ℝ≥0∞`-linear map. -/
def restrictₗ {m0 : MeasurableSpace α} (s : Set α) : Measureₓ α →ₗ[ℝ≥0∞] Measureₓ α :=
  lift_linear (outer_measure.restrict s)$
    fun μ s' hs' t =>
      by 
        suffices  : μ (s ∩ t) = μ (s ∩ t ∩ s')+μ (s ∩ t \ s')
        ·
          simpa [←Set.inter_assoc, Set.inter_comm _ s, ←inter_diff_assoc]
        exact le_to_outer_measure_caratheodory _ _ hs' _

/-- Restrict a measure `μ` to a set `s`. -/
def restrict {m0 : MeasurableSpace α} (μ : Measureₓ α) (s : Set α) : Measureₓ α :=
  restrictₗ s μ

@[simp]
theorem restrictₗ_apply {m0 : MeasurableSpace α} (s : Set α) (μ : Measureₓ α) : restrictₗ s μ = μ.restrict s :=
  rfl

/-- This lemma shows that `restrict` and `to_outer_measure` commute. Note that the LHS has a
restrict on measures and the RHS has a restrict on outer measures. -/
theorem restrict_to_outer_measure_eq_to_outer_measure_restrict (h : MeasurableSet s) :
  (μ.restrict s).toOuterMeasure = outer_measure.restrict s μ.to_outer_measure :=
  by 
    simpRw [restrict, restrictₗ, lift_linear, LinearMap.coe_mk, to_measure_to_outer_measure,
      outer_measure.restrict_trim h, μ.trimmed]

theorem restrict_apply₀ (ht : null_measurable_set t (μ.restrict s)) : μ.restrict s t = μ (t ∩ s) :=
  (to_measure_apply₀ _ _ ht).trans$
    by 
      simp only [coe_to_outer_measure, outer_measure.restrict_apply]

/-- If `t` is a measurable set, then the measure of `t` with respect to the restriction of
  the measure to `s` equals the outer measure of `t ∩ s`. An alternate version requiring that `s`
  be measurable instead of `t` exists as `measure.restrict_apply'`. -/
@[simp]
theorem restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t ∩ s) :=
  restrict_apply₀ ht.null_measurable_set

/-- If `s` is a measurable set, then the outer measure of `t` with respect to the restriction of
the measure to `s` equals the outer measure of `t ∩ s`. This is an alternate version of
`measure.restrict_apply`, requiring that `s` is measurable instead of `t`. -/
@[simp]
theorem restrict_apply' (hs : MeasurableSet s) : μ.restrict s t = μ (t ∩ s) :=
  by 
    rw [←coe_to_outer_measure, measure.restrict_to_outer_measure_eq_to_outer_measure_restrict hs,
      outer_measure.restrict_apply s t _, coe_to_outer_measure]

theorem restrict_eq_self' (hs : MeasurableSet s) (t_subset : t ⊆ s) : μ.restrict s t = μ t :=
  by 
    rw [restrict_apply' hs, Set.inter_eq_self_of_subset_left t_subset]

theorem restrict_eq_self (h_meas_t : MeasurableSet t) (h : t ⊆ s) : μ.restrict s t = μ t :=
  by 
    rw [restrict_apply h_meas_t, inter_eq_left_iff_subset.mpr h]

theorem restrict_apply_self {m0 : MeasurableSpace α} (μ : Measureₓ α) (h_meas_s : MeasurableSet s) :
  (μ.restrict s) s = μ s :=
  restrict_eq_self h_meas_s (Set.Subset.refl _)

theorem restrict_apply_univ (s : Set α) : μ.restrict s univ = μ s :=
  by 
    rw [restrict_apply MeasurableSet.univ, Set.univ_inter]

theorem le_restrict_apply (s t : Set α) : μ (t ∩ s) ≤ μ.restrict s t :=
  by 
    rw [restrict, restrictₗ]
    convert le_lift_linear_apply _ t 
    simp 

@[simp]
theorem restrict_add {m0 : MeasurableSpace α} (μ ν : Measureₓ α) (s : Set α) :
  (μ+ν).restrict s = μ.restrict s+ν.restrict s :=
  (restrictₗ s).map_add μ ν

@[simp]
theorem restrict_zero {m0 : MeasurableSpace α} (s : Set α) : (0 : Measureₓ α).restrict s = 0 :=
  (restrictₗ s).map_zero

@[simp]
theorem restrict_smul {m0 : MeasurableSpace α} (c : ℝ≥0∞) (μ : Measureₓ α) (s : Set α) :
  (c • μ).restrict s = c • μ.restrict s :=
  (restrictₗ s).map_smul c μ

@[simp]
theorem restrict_restrict (hs : MeasurableSet s) : (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  ext$
    fun u hu =>
      by 
        simp [Set.inter_assoc]

theorem restrict_comm (hs : MeasurableSet s) (ht : MeasurableSet t) :
  (μ.restrict t).restrict s = (μ.restrict s).restrict t :=
  by 
    rw [restrict_restrict hs, restrict_restrict ht, inter_comm]

theorem restrict_apply_eq_zero (ht : MeasurableSet t) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 :=
  by 
    rw [restrict_apply ht]

theorem measure_inter_eq_zero_of_restrict (h : μ.restrict s t = 0) : μ (t ∩ s) = 0 :=
  nonpos_iff_eq_zero.1 (h ▸ le_restrict_apply _ _)

theorem restrict_apply_eq_zero' (hs : MeasurableSet s) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 :=
  by 
    rw [restrict_apply' hs]

@[simp]
theorem restrict_eq_zero : μ.restrict s = 0 ↔ μ s = 0 :=
  by 
    rw [←measure_univ_eq_zero, restrict_apply_univ]

theorem restrict_zero_set {s : Set α} (h : μ s = 0) : μ.restrict s = 0 :=
  by 
    simp only [measure.restrict_eq_zero, h]

@[simp]
theorem restrict_empty : μ.restrict ∅ = 0 :=
  restrict_zero_set measure_empty

@[simp]
theorem restrict_univ : μ.restrict univ = μ :=
  ext$
    fun s hs =>
      by 
        simp [hs]

theorem restrict_union_apply (h : Disjoint (t ∩ s) (t ∩ s')) (hs : MeasurableSet s) (hs' : MeasurableSet s')
  (ht : MeasurableSet t) : μ.restrict (s ∪ s') t = μ.restrict s t+μ.restrict s' t :=
  by 
    simp only [restrict_apply, ht, Set.inter_union_distrib_left]
    exact measure_union h (ht.inter hs) (ht.inter hs')

theorem restrict_union (h : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t) :
  μ.restrict (s ∪ t) = μ.restrict s+μ.restrict t :=
  ext$ fun t' ht' => restrict_union_apply (h.mono inf_le_right inf_le_right) hs ht ht'

theorem restrict_union_add_inter (s : Set α) (ht : MeasurableSet t) :
  (μ.restrict (s ∪ t)+μ.restrict (s ∩ t)) = μ.restrict s+μ.restrict t :=
  by 
    ext1 u hu 
    simp only [add_apply, restrict_apply hu, inter_union_distrib_left]
    convert measure_union_add_inter (u ∩ s) (hu.inter ht) using 3
    rw [Set.inter_left_comm (u ∩ s), Set.inter_assoc, ←Set.inter_assoc u u, Set.inter_self]

@[simp]
theorem restrict_add_restrict_compl (hs : MeasurableSet s) : (μ.restrict s+μ.restrict («expr ᶜ» s)) = μ :=
  by 
    rw [←restrict_union (@disjoint_compl_right (Set α) _ _) hs hs.compl, union_compl_self, restrict_univ]

@[simp]
theorem restrict_compl_add_restrict (hs : MeasurableSet s) : (μ.restrict («expr ᶜ» s)+μ.restrict s) = μ :=
  by 
    rw [add_commₓ, restrict_add_restrict_compl hs]

theorem restrict_union_le (s s' : Set α) : μ.restrict (s ∪ s') ≤ μ.restrict s+μ.restrict s' :=
  by 
    intro t ht 
    suffices  : μ (t ∩ s ∪ t ∩ s') ≤ μ (t ∩ s)+μ (t ∩ s')
    ·
      simpa [ht, inter_union_distrib_left]
    apply measure_union_le

theorem restrict_Union_apply_ae [Encodable ι] {s : ι → Set α} (hd : Pairwise fun i j => μ (s i ∩ s j) = 0)
  (hm : ∀ i, MeasurableSet (s i)) {t : Set α} (ht : MeasurableSet t) :
  μ.restrict (⋃i, s i) t = ∑'i, μ.restrict (s i) t :=
  by 
    simp only [restrict_apply, ht, inter_Union]
    exact
      measure_Union_of_null_inter (fun i => ht.inter (hm _))
        fun i j hne =>
          measure_mono_null (inter_subset_inter (inter_subset_right _ _) (inter_subset_right _ _)) (hd i j hne)

theorem restrict_Union_apply [Encodable ι] {s : ι → Set α} (hd : Pairwise (Disjoint on s))
  (hm : ∀ i, MeasurableSet (s i)) {t : Set α} (ht : MeasurableSet t) :
  μ.restrict (⋃i, s i) t = ∑'i, μ.restrict (s i) t :=
  restrict_Union_apply_ae
    (fun i j hij =>
      by 
        simp [Set.disjoint_iff_inter_eq_empty.1 (hd i j hij)])
    hm ht

theorem restrict_Union_apply_eq_supr [Encodable ι] {s : ι → Set α} (hm : ∀ i, MeasurableSet (s i))
  (hd : Directed (· ⊆ ·) s) {t : Set α} (ht : MeasurableSet t) : μ.restrict (⋃i, s i) t = ⨆i, μ.restrict (s i) t :=
  by 
    simp only [restrict_apply ht, inter_Union]
    rw [measure_Union_eq_supr]
    exacts[fun i => ht.inter (hm i), hd.mono_comp _ fun s₁ s₂ => inter_subset_inter_right _]

theorem restrict_map {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
  (map f μ).restrict s = map f (μ.restrict$ f ⁻¹' s) :=
  ext$
    fun t ht =>
      by 
        simp [hf ht]

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
theorem restrict_mono' {m0 : MeasurableSpace α} ⦃s s' : Set α⦄ ⦃μ ν : Measureₓ α⦄ (hs : s ≤ᵐ[μ] s') (hμν : μ ≤ ν) :
  μ.restrict s ≤ ν.restrict s' :=
  fun t ht =>
    calc μ.restrict s t = μ (t ∩ s) := restrict_apply ht 
      _ ≤ μ (t ∩ s') := measure_mono_ae$ hs.mono$ fun x hx ⟨hxt, hxs⟩ => ⟨hxt, hx hxs⟩
      _ ≤ ν (t ∩ s') := le_iff'.1 hμν (t ∩ s')
      _ = ν.restrict s' t := (restrict_apply ht).symm
      

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
@[mono]
theorem restrict_mono {m0 : MeasurableSpace α} ⦃s s' : Set α⦄ (hs : s ⊆ s') ⦃μ ν : Measureₓ α⦄ (hμν : μ ≤ ν) :
  μ.restrict s ≤ ν.restrict s' :=
  restrict_mono' (ae_of_all _ hs) hμν

theorem restrict_le_self : μ.restrict s ≤ μ :=
  fun t ht =>
    calc μ.restrict s t = μ (t ∩ s) := restrict_apply ht 
      _ ≤ μ t := measure_mono$ inter_subset_left t s
      

theorem restrict_congr_meas (hs : MeasurableSet s) :
  μ.restrict s = ν.restrict s ↔ ∀ t _ : t ⊆ s, MeasurableSet t → μ t = ν t :=
  ⟨fun H t hts ht =>
      by 
        rw [←inter_eq_self_of_subset_left hts, ←restrict_apply ht, H, restrict_apply ht],
    fun H =>
      ext$
        fun t ht =>
          by 
            rw [restrict_apply ht, restrict_apply ht, H _ (inter_subset_right _ _) (ht.inter hs)]⟩

theorem restrict_congr_mono (hs : s ⊆ t) (hm : MeasurableSet s) (h : μ.restrict t = ν.restrict t) :
  μ.restrict s = ν.restrict s :=
  by 
    rw [←inter_eq_self_of_subset_left hs, ←restrict_restrict hm, h, restrict_restrict hm]

/-- If two measures agree on all measurable subsets of `s` and `t`, then they agree on all
measurable subsets of `s ∪ t`. -/
theorem restrict_union_congr (hsm : MeasurableSet s) (htm : MeasurableSet t) :
  μ.restrict (s ∪ t) = ν.restrict (s ∪ t) ↔ μ.restrict s = ν.restrict s ∧ μ.restrict t = ν.restrict t :=
  by 
    refine'
      ⟨fun h => ⟨restrict_congr_mono (subset_union_left _ _) hsm h, restrict_congr_mono (subset_union_right _ _) htm h⟩,
        _⟩
    simp only [restrict_congr_meas, hsm, htm, hsm.union htm]
    rintro ⟨hs, ht⟩ u hu hum 
    rw [←measure_inter_add_diff u hsm, ←measure_inter_add_diff u hsm, hs _ (inter_subset_right _ _) (hum.inter hsm),
      ht _ (diff_subset_iff.2 hu) (hum.diff hsm)]

theorem restrict_finset_bUnion_congr {s : Finset ι} {t : ι → Set α} (htm : ∀ i _ : i ∈ s, MeasurableSet (t i)) :
  μ.restrict (⋃(i : _)(_ : i ∈ s), t i) = ν.restrict (⋃(i : _)(_ : i ∈ s), t i) ↔
    ∀ i _ : i ∈ s, μ.restrict (t i) = ν.restrict (t i) :=
  by 
    induction' s using Finset.induction_on with i s hi hs
    ·
      simp 
    simp only [Finset.mem_insert, or_imp_distrib, forall_and_distrib, forall_eq] at htm⊢
    simp only [Finset.set_bUnion_insert, ←hs htm.2]
    exact restrict_union_congr htm.1 (s.measurable_set_bUnion htm.2)

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem restrict_Union_congr
[encodable ι]
{s : ι → set α}
(hm : ∀
 i, measurable_set (s i)) : «expr ↔ »(«expr = »(μ.restrict «expr⋃ , »((i), s i), ν.restrict «expr⋃ , »((i), s i)), ∀
 i, «expr = »(μ.restrict (s i), ν.restrict (s i))) :=
begin
  refine [expr ⟨λ h i, restrict_congr_mono (subset_Union _ _) (hm i) h, λ h, _⟩],
  ext1 [] [ident t, ident ht],
  have [ident M] [":", expr ∀
   t : finset ι, measurable_set «expr⋃ , »((i «expr ∈ » t), s i)] [":=", expr λ
   t, t.measurable_set_bUnion (λ i _, hm i)],
  have [ident D] [":", expr directed ((«expr ⊆ »)) (λ
    t : finset ι, «expr⋃ , »((i «expr ∈ » t), s i))] [":=", expr directed_of_sup (λ
    t₁ t₂ ht, bUnion_subset_bUnion_left ht)],
  rw ["[", expr Union_eq_Union_finset, "]"] [],
  simp [] [] ["only"] ["[", expr restrict_Union_apply_eq_supr M D ht, ",", expr (restrict_finset_bUnion_congr (λ
     i hi, hm i)).2 (λ i hi, h i), "]"] [] []
end

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem restrict_bUnion_congr
{s : set ι}
{t : ι → set α}
(hc : countable s)
(htm : ∀
 i «expr ∈ » s, measurable_set (t i)) : «expr ↔ »(«expr = »(μ.restrict «expr⋃ , »((i «expr ∈ » s), t i), ν.restrict «expr⋃ , »((i «expr ∈ » s), t i)), ∀
 i «expr ∈ » s, «expr = »(μ.restrict (t i), ν.restrict (t i))) :=
begin
  simp [] [] ["only"] ["[", expr bUnion_eq_Union, ",", expr set_coe.forall', "]"] [] ["at", ident htm, "⊢"],
  haveI [] [] [":=", expr hc.to_encodable],
  exact [expr restrict_Union_congr htm]
end

theorem restrict_sUnion_congr {S : Set (Set α)} (hc : countable S) (hm : ∀ s _ : s ∈ S, MeasurableSet s) :
  μ.restrict (⋃₀S) = ν.restrict (⋃₀S) ↔ ∀ s _ : s ∈ S, μ.restrict s = ν.restrict s :=
  by 
    rw [sUnion_eq_bUnion, restrict_bUnion_congr hc hm]

/-- This lemma shows that `Inf` and `restrict` commute for measures. -/
theorem restrict_Inf_eq_Inf_restrict {m0 : MeasurableSpace α} {m : Set (Measureₓ α)} (hm : m.nonempty)
  (ht : MeasurableSet t) : (Inf m).restrict t = Inf ((fun μ : Measureₓ α => μ.restrict t) '' m) :=
  by 
    ext1 s hs 
    simpRw [Inf_apply hs, restrict_apply hs, Inf_apply (MeasurableSet.inter hs ht), Set.image_image,
      restrict_to_outer_measure_eq_to_outer_measure_restrict ht, ←Set.image_image _ to_outer_measure,
      ←outer_measure.restrict_Inf_eq_Inf_restrict _ (hm.image _), outer_measure.restrict_apply]

/-! ### Extensionality results -/


/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `Union`). -/
theorem ext_iff_of_Union_eq_univ [Encodable ι] {s : ι → Set α} (hm : ∀ i, MeasurableSet (s i)) (hs : (⋃i, s i) = univ) :
  μ = ν ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) :=
  by 
    rw [←restrict_Union_congr hm, hs, restrict_univ, restrict_univ]

alias ext_iff_of_Union_eq_univ ↔ _ MeasureTheory.Measure.ext_of_Union_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `bUnion`). -/
theorem ext_iff_of_bUnion_eq_univ {S : Set ι} {s : ι → Set α} (hc : countable S)
  (hm : ∀ i _ : i ∈ S, MeasurableSet (s i)) (hs : (⋃(i : _)(_ : i ∈ S), s i) = univ) :
  μ = ν ↔ ∀ i _ : i ∈ S, μ.restrict (s i) = ν.restrict (s i) :=
  by 
    rw [←restrict_bUnion_congr hc hm, hs, restrict_univ, restrict_univ]

alias ext_iff_of_bUnion_eq_univ ↔ _ MeasureTheory.Measure.ext_of_bUnion_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `sUnion`). -/
theorem ext_iff_of_sUnion_eq_univ {S : Set (Set α)} (hc : countable S) (hm : ∀ s _ : s ∈ S, MeasurableSet s)
  (hs : ⋃₀S = univ) : μ = ν ↔ ∀ s _ : s ∈ S, μ.restrict s = ν.restrict s :=
  ext_iff_of_bUnion_eq_univ hc hm$
    by 
      rwa [←sUnion_eq_bUnion]

alias ext_iff_of_sUnion_eq_univ ↔ _ MeasureTheory.Measure.ext_of_sUnion_eq_univ

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ext_of_generate_from_of_cover
{S T : set (set α)}
(h_gen : «expr = »(«expr‹ ›»(_), generate_from S))
(hc : countable T)
(h_inter : is_pi_system S)
(hm : ∀ t «expr ∈ » T, measurable_set t)
(hU : «expr = »(«expr⋃₀ »(T), univ))
(htop : ∀ t «expr ∈ » T, «expr ≠ »(μ t, «expr∞»()))
(ST_eq : ∀ (t «expr ∈ » T) (s «expr ∈ » S), «expr = »(μ «expr ∩ »(s, t), ν «expr ∩ »(s, t)))
(T_eq : ∀ t «expr ∈ » T, «expr = »(μ t, ν t)) : «expr = »(μ, ν) :=
begin
  refine [expr ext_of_sUnion_eq_univ hc hm hU (λ t ht, _)],
  ext1 [] [ident u, ident hu],
  simp [] [] ["only"] ["[", expr restrict_apply hu, "]"] [] [],
  refine [expr induction_on_inter h_gen h_inter _ (ST_eq t ht) _ _ hu],
  { simp [] [] ["only"] ["[", expr set.empty_inter, ",", expr measure_empty, "]"] [] [] },
  { intros [ident v, ident hv, ident hvt],
    have [] [] [":=", expr T_eq t ht],
    rw ["[", expr set.inter_comm, "]"] ["at", ident hvt, "⊢"],
    rwa ["[", "<-", expr measure_inter_add_diff t hv, ",", "<-", expr measure_inter_add_diff t hv, ",", "<-", expr hvt, ",", expr ennreal.add_right_inj, "]"] ["at", ident this],
    exact [expr ne_top_of_le_ne_top (htop t ht) «expr $ »(measure_mono, set.inter_subset_left _ _)] },
  { intros [ident f, ident hfd, ident hfm, ident h_eq],
    have [] [":", expr pairwise «expr on »(disjoint, λ
      n, «expr ∩ »(f n, t))] [":=", expr λ m n hmn, (hfd m n hmn).mono (inter_subset_left _ _) (inter_subset_left _ _)],
    simp [] [] ["only"] ["[", expr Union_inter, ",", expr measure_Union this (λ
      n, (hfm n).inter (hm t ht)), ",", expr h_eq, "]"] [] [] }
end

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on a increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `sUnion`. -/
theorem ext_of_generate_from_of_cover_subset {S T : Set (Set α)} (h_gen : ‹_› = generate_from S)
  (h_inter : IsPiSystem S) (h_sub : T ⊆ S) (hc : countable T) (hU : ⋃₀T = univ) (htop : ∀ s _ : s ∈ T, μ s ≠ ∞)
  (h_eq : ∀ s _ : s ∈ S, μ s = ν s) : μ = ν :=
  by 
    refine' ext_of_generate_from_of_cover h_gen hc h_inter _ hU htop _ fun t ht => h_eq t (h_sub ht)
    ·
      intro t ht 
      rw [h_gen]
      exact generate_measurable.basic _ (h_sub ht)
    ·
      intro t ht s hs 
      cases' (s ∩ t).eq_empty_or_nonempty with H H
      ·
        simp only [H, measure_empty]
      ·
        exact h_eq _ (h_inter _ _ hs (h_sub ht) H)

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on a increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `Union`.
  `finite_spanning_sets_in.ext` is a reformulation of this lemma. -/
theorem ext_of_generate_from_of_Union (C : Set (Set α)) (B : ℕ → Set α) (hA : ‹_› = generate_from C) (hC : IsPiSystem C)
  (h1B : (⋃i, B i) = univ) (h2B : ∀ i, B i ∈ C) (hμB : ∀ i, μ (B i) ≠ ∞) (h_eq : ∀ s _ : s ∈ C, μ s = ν s) : μ = ν :=
  by 
    refine' ext_of_generate_from_of_cover_subset hA hC _ (countable_range B) h1B _ h_eq
    ·
      rintro _ ⟨i, rfl⟩
      apply h2B
    ·
      rintro _ ⟨i, rfl⟩
      apply hμB

section Dirac

variable[MeasurableSpace α]

/-- The dirac measure. -/
def dirac (a : α) : Measureₓ α :=
  (outer_measure.dirac a).toMeasure
    (by 
      simp )

instance  : measure_space PUnit :=
  ⟨dirac PUnit.unit⟩

theorem le_dirac_apply {a} : s.indicator 1 a ≤ dirac a s :=
  outer_measure.dirac_apply a s ▸ le_to_measure_apply _ _ _

@[simp]
theorem dirac_apply' (a : α) (hs : MeasurableSet s) : dirac a s = s.indicator 1 a :=
  to_measure_apply _ _ hs

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem dirac_apply_of_mem {a : α} (h : «expr ∈ »(a, s)) : «expr = »(dirac a s, 1) :=
begin
  have [] [":", expr ∀ t : set α, «expr ∈ »(a, t) → «expr = »(t.indicator (1 : α → «exprℝ≥0∞»()) a, 1)] [],
  from [expr λ t ht, indicator_of_mem ht 1],
  refine [expr le_antisymm «expr ▸ »(this univ trivial, _) «expr ▸ »(this s h, le_dirac_apply)],
  rw ["[", "<-", expr dirac_apply' a measurable_set.univ, "]"] [],
  exact [expr measure_mono (subset_univ s)]
end

@[simp]
theorem dirac_apply [MeasurableSingletonClass α] (a : α) (s : Set α) : dirac a s = s.indicator 1 a :=
  by 
    byCases' h : a ∈ s
    ·
      rw [dirac_apply_of_mem h, indicator_of_mem h, Pi.one_apply]
    rw [indicator_of_not_mem h, ←nonpos_iff_eq_zero]
    calc dirac a s ≤ dirac a («expr ᶜ» {a}) := measure_mono (subset_compl_comm.1$ singleton_subset_iff.2 h)_ = 0 :=
      by 
        simp [dirac_apply' _ (measurable_set_singleton _).Compl]

theorem map_dirac {f : α → β} (hf : Measurable f) (a : α) : map f (dirac a) = dirac (f a) :=
  ext$
    fun s hs =>
      by 
        simp [hs, map_apply hf hs, hf hs, indicator_apply]

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem restrict_singleton (μ : measure α) (a : α) : «expr = »(μ.restrict {a}, «expr • »(μ {a}, dirac a)) :=
begin
  ext1 [] [ident s, ident hs],
  by_cases [expr ha, ":", expr «expr ∈ »(a, s)],
  { have [] [":", expr «expr = »(«expr ∩ »(s, {a}), {a})] [],
    by simpa [] [] [] [] [] [],
    simp [] [] [] ["*"] [] [] },
  { have [] [":", expr «expr = »(«expr ∩ »(s, {a}), «expr∅»())] [],
    from [expr inter_singleton_eq_empty.2 ha],
    simp [] [] [] ["*"] [] [] }
end

end Dirac

section Sum

include m0

/-- Sum of an indexed family of measures. -/
def Sum (f : ι → Measureₓ α) : Measureₓ α :=
  (outer_measure.sum fun i => (f i).toOuterMeasure).toMeasure$
    le_transₓ
      (by 
        exact le_infi fun i => le_to_outer_measure_caratheodory _)
      (outer_measure.le_sum_caratheodory _)

theorem le_sum_apply (f : ι → Measureₓ α) (s : Set α) : (∑'i, f i s) ≤ Sum f s :=
  le_to_measure_apply _ _ _

@[simp]
theorem sum_apply (f : ι → Measureₓ α) {s : Set α} (hs : MeasurableSet s) : Sum f s = ∑'i, f i s :=
  to_measure_apply _ _ hs

theorem le_sum (μ : ι → Measureₓ α) (i : ι) : μ i ≤ Sum μ :=
  fun s hs =>
    by 
      simp only [sum_apply μ hs, Ennreal.le_tsum i]

@[simp]
theorem sum_apply_eq_zero [Encodable ι] {μ : ι → Measureₓ α} {s : Set α} : Sum μ s = 0 ↔ ∀ i, μ i s = 0 :=
  by 
    refine' ⟨fun h i => nonpos_iff_eq_zero.1$ h ▸ le_iff'.1 (le_sum μ i) _, fun h => nonpos_iff_eq_zero.1 _⟩
    rcases exists_measurable_superset_forall_eq μ s with ⟨t, hst, htm, ht⟩
    calc Sum μ s ≤ Sum μ t := measure_mono hst _ = 0 :=
      by 
        simp 

theorem sum_apply_eq_zero' {μ : ι → Measureₓ α} {s : Set α} (hs : MeasurableSet s) : Sum μ s = 0 ↔ ∀ i, μ i s = 0 :=
  by 
    simp [hs]

theorem ae_sum_iff [Encodable ι] {μ : ι → Measureₓ α} {p : α → Prop} : (∀ᵐx ∂Sum μ, p x) ↔ ∀ i, ∀ᵐx ∂μ i, p x :=
  sum_apply_eq_zero

theorem ae_sum_iff' {μ : ι → Measureₓ α} {p : α → Prop} (h : MeasurableSet { x | p x }) :
  (∀ᵐx ∂Sum μ, p x) ↔ ∀ i, ∀ᵐx ∂μ i, p x :=
  sum_apply_eq_zero' h.compl

@[simp]
theorem ae_sum_eq [Encodable ι] (μ : ι → Measureₓ α) : (Sum μ).ae = ⨆i, (μ i).ae :=
  Filter.ext$ fun s => ae_sum_iff.trans mem_supr.symm

@[simp]
theorem sum_bool (f : Bool → Measureₓ α) : Sum f = f tt+f ff :=
  ext$
    fun s hs =>
      by 
        simp [hs, tsum_fintype]

@[simp]
theorem sum_cond (μ ν : Measureₓ α) : (Sum fun b => cond b μ ν) = μ+ν :=
  sum_bool _

@[simp]
theorem restrict_sum (μ : ι → Measureₓ α) {s : Set α} (hs : MeasurableSet s) :
  (Sum μ).restrict s = Sum fun i => (μ i).restrict s :=
  ext$
    fun t ht =>
      by 
        simp only [sum_apply, restrict_apply, ht, ht.inter hs]

@[simp]
theorem sum_of_empty [IsEmpty ι] (μ : ι → Measureₓ α) : Sum μ = 0 :=
  by 
    rw [←measure_univ_eq_zero, sum_apply _ MeasurableSet.univ, tsum_empty]

theorem sum_congr {μ ν : ℕ → Measureₓ α} (h : ∀ n, μ n = ν n) : Sum μ = Sum ν :=
  by 
    congr 
    ext1 n 
    exact h n

theorem sum_add_sum (μ ν : ℕ → Measureₓ α) : (Sum μ+Sum ν) = Sum fun n => μ n+ν n :=
  by 
    ext1 s hs 
    simp only [add_apply, sum_apply _ hs, Pi.add_apply, coe_add, tsum_add Ennreal.summable Ennreal.summable]

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` is a map with encodable codomain, then `map f μ` is the sum of Dirac measures -/
theorem map_eq_sum
[encodable β]
[measurable_singleton_class β]
(μ : measure α)
(f : α → β)
(hf : measurable f) : «expr = »(map f μ, sum (λ b : β, «expr • »(μ «expr ⁻¹' »(f, {b}), dirac b))) :=
begin
  ext1 [] [ident s, ident hs],
  have [] [":", expr ∀ y «expr ∈ » s, measurable_set «expr ⁻¹' »(f, {y})] [],
  from [expr λ y _, hf (measurable_set_singleton _)],
  simp [] [] [] ["[", "<-", expr tsum_measure_preimage_singleton (countable_encodable s) this, ",", "*", ",", expr tsum_subtype s (λ
    b, μ «expr ⁻¹' »(f, {b})), ",", "<-", expr indicator_mul_right s (λ b, μ «expr ⁻¹' »(f, {b})), "]"] [] []
end

/-- A measure on an encodable type is a sum of dirac measures. -/
@[simp]
theorem sum_smul_dirac [Encodable α] [MeasurableSingletonClass α] (μ : Measureₓ α) :
  (Sum fun a => μ {a} • dirac a) = μ :=
  by 
    simpa using (map_eq_sum μ id measurable_id).symm

omit m0

end Sum

theorem restrict_Union_ae [Encodable ι] {s : ι → Set α} (hd : Pairwise fun i j => μ (s i ∩ s j) = 0)
  (hm : ∀ i, MeasurableSet (s i)) : μ.restrict (⋃i, s i) = Sum fun i => μ.restrict (s i) :=
  ext$
    fun t ht =>
      by 
        simp only [sum_apply _ ht, restrict_Union_apply_ae hd hm ht]

theorem restrict_Union [Encodable ι] {s : ι → Set α} (hd : Pairwise (Disjoint on s)) (hm : ∀ i, MeasurableSet (s i)) :
  μ.restrict (⋃i, s i) = Sum fun i => μ.restrict (s i) :=
  ext$
    fun t ht =>
      by 
        simp only [sum_apply _ ht, restrict_Union_apply hd hm ht]

theorem restrict_Union_le [Encodable ι] {s : ι → Set α} : μ.restrict (⋃i, s i) ≤ Sum fun i => μ.restrict (s i) :=
  by 
    intro t ht 
    suffices  : μ (⋃i, t ∩ s i) ≤ ∑'i, μ (t ∩ s i)
    ·
      simpa [ht, inter_Union]
    apply measure_Union_le

section Count

variable[MeasurableSpace α]

/-- Counting measure on any measurable space. -/
def count : Measureₓ α :=
  Sum dirac

theorem le_count_apply : (∑'i : s, 1 : ℝ≥0∞) ≤ count s :=
  calc (∑'i : s, 1 : ℝ≥0∞) = ∑'i, indicator s 1 i := tsum_subtype s 1
    _ ≤ ∑'i, dirac i s := Ennreal.tsum_le_tsum$ fun x => le_dirac_apply 
    _ ≤ count s := le_sum_apply _ _
    

theorem count_apply (hs : MeasurableSet s) : count s = ∑'i : s, 1 :=
  by 
    simp only [count, sum_apply, hs, dirac_apply', ←tsum_subtype s 1, Pi.one_apply]

@[simp]
theorem count_apply_finset [MeasurableSingletonClass α] (s : Finset α) : count («expr↑ » s : Set α) = s.card :=
  calc count («expr↑ » s : Set α) = ∑'i : («expr↑ » s : Set α), 1 := count_apply s.measurable_set 
    _ = ∑i in s, 1 := s.tsum_subtype 1
    _ = s.card :=
    by 
      simp 
    

theorem count_apply_finite [MeasurableSingletonClass α] (s : Set α) (hs : finite s) : count s = hs.to_finset.card :=
  by 
    rw [←count_apply_finset, finite.coe_to_finset]

/-- `count` measure evaluates to infinity at infinite sets. -/
theorem count_apply_infinite (hs : s.infinite) : count s = ∞ :=
  by 
    refine' top_unique (le_of_tendsto' Ennreal.tendsto_nat_nhds_top$ fun n => _)
    rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
    calc (t.card : ℝ≥0∞) = ∑i in t, 1 :=
      by 
        simp _ = ∑'i : (t : Set α), 1 :=
      (t.tsum_subtype 1).symm _ ≤ count (t : Set α) := le_count_apply _ ≤ count s := measure_mono ht

@[simp]
theorem count_apply_eq_top [MeasurableSingletonClass α] : count s = ∞ ↔ s.infinite :=
  by 
    byCases' hs : s.finite
    ·
      simp [Set.Infinite, hs, count_apply_finite]
    ·
      change s.infinite at hs 
      simp [hs, count_apply_infinite]

@[simp]
theorem count_apply_lt_top [MeasurableSingletonClass α] : count s < ∞ ↔ s.finite :=
  calc count s < ∞ ↔ count s ≠ ∞ := lt_top_iff_ne_top 
    _ ↔ ¬s.infinite := not_congr count_apply_eq_top 
    _ ↔ s.finite := not_not
    

end Count

/-! ### Absolute continuity -/


/-- We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
  if `ν(A) = 0` implies that `μ(A) = 0`. -/
def absolutely_continuous {m0 : MeasurableSpace α} (μ ν : Measureₓ α) : Prop :=
  ∀ ⦃s : Set α⦄, ν s = 0 → μ s = 0

localized [MeasureTheory] infixl:50 " ≪ " => MeasureTheory.Measure.AbsolutelyContinuous

theorem absolutely_continuous_of_le (h : μ ≤ ν) : μ ≪ ν :=
  fun s hs => nonpos_iff_eq_zero.1$ hs ▸ le_iff'.1 h s

alias absolutely_continuous_of_le ← LE.le.absolutely_continuous

theorem absolutely_continuous_of_eq (h : μ = ν) : μ ≪ ν :=
  h.le.absolutely_continuous

alias absolutely_continuous_of_eq ← Eq.absolutely_continuous

namespace AbsolutelyContinuous

theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → ν s = 0 → μ s = 0) : μ ≪ ν :=
  by 
    intro s hs 
    rcases exists_measurable_superset_of_null hs with ⟨t, h1t, h2t, h3t⟩
    exact measure_mono_null h1t (h h2t h3t)

@[refl]
protected theorem refl {m0 : MeasurableSpace α} (μ : Measureₓ α) : μ ≪ μ :=
  rfl.AbsolutelyContinuous

protected theorem rfl : μ ≪ μ :=
  fun s hs => hs

instance  [MeasurableSpace α] : IsRefl (Measureₓ α) (· ≪ ·) :=
  ⟨fun μ => absolutely_continuous.rfl⟩

@[trans]
protected theorem trans (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃) : μ₁ ≪ μ₃ :=
  fun s hs => h1$ h2 hs

@[mono]
protected theorem map (h : μ ≪ ν) (f : α → β) : map f μ ≪ map f ν :=
  if hf : Measurable f then
    absolutely_continuous.mk$
      fun s hs =>
        by 
          simpa [hf, hs] using @h _
  else
    by 
      simp only [map_of_not_measurable hf]

protected theorem smul (h : μ ≪ ν) (c : ℝ≥0∞) : c • μ ≪ ν :=
  mk
    fun s hs hνs =>
      by 
        simp only [h hνs, Algebra.id.smul_eq_mul, coe_smul, Pi.smul_apply, mul_zero]

protected theorem coe_nnreal_smul (h : μ ≪ ν) (c :  ℝ≥0 ) : c • μ ≪ ν :=
  h.smul c

end AbsolutelyContinuous

theorem ae_le_iff_absolutely_continuous : μ.ae ≤ ν.ae ↔ μ ≪ ν :=
  ⟨fun h s =>
      by 
        rw [measure_zero_iff_ae_nmem, measure_zero_iff_ae_nmem]
        exact fun hs => h hs,
    fun h s hs => h hs⟩

alias ae_le_iff_absolutely_continuous ↔ LE.le.absolutely_continuous_of_ae
  MeasureTheory.Measure.AbsolutelyContinuous.ae_le

alias absolutely_continuous.ae_le ← ae_mono'

theorem absolutely_continuous.ae_eq (h : μ ≪ ν) {f g : α → δ} (h' : f =ᵐ[ν] g) : f =ᵐ[μ] g :=
  h.ae_le h'

/-! ### Quasi measure preserving maps (a.k.a. non-singular maps) -/


/-- A map `f : α → β` is said to be *quasi measure preserving* (a.k.a. non-singular) w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`. -/
@[protectProj]
structure
  quasi_measure_preserving{m0 : MeasurableSpace α}(f : α → β)(μa : Measureₓ α :=  by 
    runTac 
      volume_tac)(μb : Measureₓ β :=  by 
    runTac 
      volume_tac) :
  Prop where 
  Measurable : Measurable f 
  AbsolutelyContinuous : map f μa ≪ μb

namespace QuasiMeasurePreserving

protected theorem id {m0 : MeasurableSpace α} (μ : Measureₓ α) : quasi_measure_preserving id μ μ :=
  ⟨measurable_id, map_id.AbsolutelyContinuous⟩

variable{μa μa' : Measureₓ α}{μb μb' : Measureₓ β}{μc : Measureₓ γ}{f : α → β}

theorem mono_left (h : quasi_measure_preserving f μa μb) (ha : μa' ≪ μa) : quasi_measure_preserving f μa' μb :=
  ⟨h.1, (ha.map f).trans h.2⟩

theorem mono_right (h : quasi_measure_preserving f μa μb) (ha : μb ≪ μb') : quasi_measure_preserving f μa μb' :=
  ⟨h.1, h.2.trans ha⟩

@[mono]
theorem mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : quasi_measure_preserving f μa μb) :
  quasi_measure_preserving f μa' μb' :=
  (h.mono_left ha).mono_right hb

protected theorem comp {g : β → γ} {f : α → β} (hg : quasi_measure_preserving g μb μc)
  (hf : quasi_measure_preserving f μa μb) : quasi_measure_preserving (g ∘ f) μa μc :=
  ⟨hg.measurable.comp hf.measurable,
    by 
      rw [←map_map hg.1 hf.1]
      exact (hf.2.map g).trans hg.2⟩

protected theorem iterate {f : α → α} (hf : quasi_measure_preserving f μa μa) :
  ∀ n, quasi_measure_preserving (f^[n]) μa μa
| 0 => quasi_measure_preserving.id μa
| n+1 => (iterate n).comp hf

theorem ae_map_le (h : quasi_measure_preserving f μa μb) : (map f μa).ae ≤ μb.ae :=
  h.2.ae_le

theorem tendsto_ae (h : quasi_measure_preserving f μa μb) : tendsto f μa.ae μb.ae :=
  (tendsto_ae_map h.1).mono_right h.ae_map_le

theorem ae (h : quasi_measure_preserving f μa μb) {p : β → Prop} (hg : ∀ᵐx ∂μb, p x) : ∀ᵐx ∂μa, p (f x) :=
  h.tendsto_ae hg

theorem ae_eq (h : quasi_measure_preserving f μa μb) {g₁ g₂ : β → δ} (hg : g₁ =ᵐ[μb] g₂) : (g₁ ∘ f) =ᵐ[μa] (g₂ ∘ f) :=
  h.ae hg

theorem preimage_null (h : quasi_measure_preserving f μa μb) {s : Set β} (hs : μb s = 0) : μa (f ⁻¹' s) = 0 :=
  preimage_null_of_map_null h.1 (h.2 hs)

end QuasiMeasurePreserving

/-! ### The `cofinite` filter -/


/-- The filter of sets `s` such that `sᶜ` has finite measure. -/
def cofinite {m0 : MeasurableSpace α} (μ : Measureₓ α) : Filter α :=
  { Sets := { s | μ («expr ᶜ» s) < ∞ },
    univ_sets :=
      by 
        simp ,
    inter_sets :=
      fun s t hs ht =>
        by 
          simp only [compl_inter, mem_set_of_eq]
          calc μ («expr ᶜ» s ∪ «expr ᶜ» t) ≤ μ («expr ᶜ» s)+μ («expr ᶜ» t) := measure_union_le _ _ _ < ∞ :=
            Ennreal.add_lt_top.2 ⟨hs, ht⟩,
    sets_of_superset := fun s t hs hst => lt_of_le_of_ltₓ (measure_mono$ compl_subset_compl.2 hst) hs }

theorem mem_cofinite : s ∈ μ.cofinite ↔ μ («expr ᶜ» s) < ∞ :=
  Iff.rfl

theorem compl_mem_cofinite : «expr ᶜ» s ∈ μ.cofinite ↔ μ s < ∞ :=
  by 
    rw [mem_cofinite, compl_compl]

theorem eventually_cofinite {p : α → Prop} : (∀ᶠx in μ.cofinite, p x) ↔ μ { x | ¬p x } < ∞ :=
  Iff.rfl

end Measureₓ

open Measureₓ

open_locale MeasureTheory

theorem null_measurable_set.mono_ac (h : null_measurable_set s μ) (hle : ν ≪ μ) : null_measurable_set s ν :=
  ⟨to_measurable μ s, measurable_set_to_measurable _ _, hle.ae_eq h.to_measurable_ae_eq.symm⟩

theorem null_measurable_set.mono (h : null_measurable_set s μ) (hle : ν ≤ μ) : null_measurable_set s ν :=
  h.mono_ac hle.absolutely_continuous

@[simp]
theorem ae_eq_bot : μ.ae = ⊥ ↔ μ = 0 :=
  by 
    rw [←empty_mem_iff_bot, mem_ae_iff, compl_empty, measure_univ_eq_zero]

@[simp]
theorem ae_ne_bot : μ.ae.ne_bot ↔ μ ≠ 0 :=
  ne_bot_iff.trans (not_congr ae_eq_bot)

@[simp]
theorem ae_zero {m0 : MeasurableSpace α} : (0 : Measureₓ α).ae = ⊥ :=
  ae_eq_bot.2 rfl

@[mono]
theorem ae_mono (h : μ ≤ ν) : μ.ae ≤ ν.ae :=
  h.absolutely_continuous.ae_le

theorem mem_ae_map_iff {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
  s ∈ (map f μ).ae ↔ f ⁻¹' s ∈ μ.ae :=
  by 
    simp only [mem_ae_iff, map_apply hf hs.compl, preimage_compl]

theorem mem_ae_of_mem_ae_map {f : α → β} (hf : Measurable f) {s : Set β} (hs : s ∈ (map f μ).ae) : f ⁻¹' s ∈ μ.ae :=
  (tendsto_ae_map hf).Eventually hs

theorem ae_map_iff {f : α → β} (hf : Measurable f) {p : β → Prop} (hp : MeasurableSet { x | p x }) :
  (∀ᵐy ∂map f μ, p y) ↔ ∀ᵐx ∂μ, p (f x) :=
  mem_ae_map_iff hf hp

theorem ae_of_ae_map {f : α → β} (hf : Measurable f) {p : β → Prop} (h : ∀ᵐy ∂map f μ, p y) : ∀ᵐx ∂μ, p (f x) :=
  mem_ae_of_mem_ae_map hf h

theorem ae_map_mem_range {m0 : MeasurableSpace α} (f : α → β) (hf : MeasurableSet (range f)) (μ : Measureₓ α) :
  ∀ᵐx ∂map f μ, x ∈ range f :=
  by 
    byCases' h : Measurable f
    ·
      change range f ∈ (map f μ).ae 
      rw [mem_ae_map_iff h hf]
      apply eventually_of_forall 
      exact mem_range_self
    ·
      simp [map_of_not_measurable h]

theorem ae_restrict_iff {p : α → Prop} (hp : MeasurableSet { x | p x }) :
  (∀ᵐx ∂μ.restrict s, p x) ↔ ∀ᵐx ∂μ, x ∈ s → p x :=
  by 
    simp only [ae_iff, ←compl_set_of, restrict_apply hp.compl]
    congr with x 
    simp [and_comm]

theorem ae_imp_of_ae_restrict {s : Set α} {p : α → Prop} (h : ∀ᵐx ∂μ.restrict s, p x) : ∀ᵐx ∂μ, x ∈ s → p x :=
  by 
    simp only [ae_iff] at h⊢
    simpa [set_of_and, inter_comm] using measure_inter_eq_zero_of_restrict h

theorem ae_restrict_iff' {s : Set α} {p : α → Prop} (hs : MeasurableSet s) :
  (∀ᵐx ∂μ.restrict s, p x) ↔ ∀ᵐx ∂μ, x ∈ s → p x :=
  by 
    simp only [ae_iff, ←compl_set_of, restrict_apply_eq_zero' hs]
    congr with x 
    simp [and_comm]

theorem ae_restrict_mem {s : Set α} (hs : MeasurableSet s) : ∀ᵐx ∂μ.restrict s, x ∈ s :=
  (ae_restrict_iff' hs).2 (Filter.eventually_of_forall fun x => id)

theorem ae_restrict_of_ae {s : Set α} {p : α → Prop} (h : ∀ᵐx ∂μ, p x) : ∀ᵐx ∂μ.restrict s, p x :=
  eventually.filter_mono (ae_mono measure.restrict_le_self) h

theorem ae_restrict_of_ae_restrict_of_subset {s t : Set α} {p : α → Prop} (hst : s ⊆ t) (h : ∀ᵐx ∂μ.restrict t, p x) :
  ∀ᵐx ∂μ.restrict s, p x :=
  h.filter_mono (ae_mono$ measure.restrict_mono hst (le_reflₓ μ))

theorem ae_of_ae_restrict_of_ae_restrict_compl {t : Set α} {p : α → Prop} (ht : ∀ᵐx ∂μ.restrict t, p x)
  (htc : ∀ᵐx ∂μ.restrict («expr ᶜ» t), p x) : ∀ᵐx ∂μ, p x :=
  nonpos_iff_eq_zero.1$
    calc μ { x | ¬p x } = μ ({ x | ¬p x } ∩ t ∪ { x | ¬p x } ∩ «expr ᶜ» t) :=
      by 
        rw [←inter_union_distrib_left, union_compl_self, inter_univ]
      _ ≤ μ ({ x | ¬p x } ∩ t)+μ ({ x | ¬p x } ∩ «expr ᶜ» t) := measure_union_le _ _ 
      _ ≤ μ.restrict t { x | ¬p x }+μ.restrict («expr ᶜ» t) { x | ¬p x } :=
      add_le_add (le_restrict_apply _ _) (le_restrict_apply _ _)
      _ = 0 :=
      by 
        rw [ae_iff.1 ht, ae_iff.1 htc, zero_addₓ]
      

theorem mem_map_restrict_ae_iff {β} {s : Set α} {t : Set β} {f : α → β} (hs : MeasurableSet s) :
  t ∈ Filter.map f (μ.restrict s).ae ↔ μ («expr ᶜ» (f ⁻¹' t) ∩ s) = 0 :=
  by 
    rw [mem_map, mem_ae_iff, measure.restrict_apply' hs]

theorem ae_smul_measure {p : α → Prop} (h : ∀ᵐx ∂μ, p x) (c : ℝ≥0∞) : ∀ᵐx ∂c • μ, p x :=
  ae_iff.2$
    by 
      rw [smul_apply, ae_iff.1 h, mul_zero]

theorem ae_smul_measure_iff {p : α → Prop} {c : ℝ≥0∞} (hc : c ≠ 0) : (∀ᵐx ∂c • μ, p x) ↔ ∀ᵐx ∂μ, p x :=
  by 
    simp [ae_iff, hc]

theorem ae_add_measure_iff {p : α → Prop} {ν} : (∀ᵐx ∂μ+ν, p x) ↔ (∀ᵐx ∂μ, p x) ∧ ∀ᵐx ∂ν, p x :=
  add_eq_zero_iff

theorem ae_eq_comp' {ν : Measureₓ β} {f : α → β} {g g' : β → δ} (hf : Measurable f) (h : g =ᵐ[ν] g')
  (h2 : map f μ ≪ ν) : (g ∘ f) =ᵐ[μ] (g' ∘ f) :=
  (quasi_measure_preserving.mk hf h2).ae_eq h

theorem ae_eq_comp {f : α → β} {g g' : β → δ} (hf : Measurable f) (h : g =ᵐ[measure.map f μ] g') :
  (g ∘ f) =ᵐ[μ] (g' ∘ f) :=
  ae_eq_comp' hf h absolutely_continuous.rfl

theorem sub_ae_eq_zero {β} [AddGroupₓ β] (f g : α → β) : f - g =ᵐ[μ] 0 ↔ f =ᵐ[μ] g :=
  by 
    refine' ⟨fun h => h.mono fun x hx => _, fun h => h.mono fun x hx => _⟩
    ·
      rwa [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hx
    ·
      rwa [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]

theorem le_ae_restrict : μ.ae⊓𝓟 s ≤ (μ.restrict s).ae :=
  fun s hs => eventually_inf_principal.2 (ae_imp_of_ae_restrict hs)

@[simp]
theorem ae_restrict_eq (hs : MeasurableSet s) : (μ.restrict s).ae = μ.ae⊓𝓟 s :=
  by 
    ext t 
    simp only [mem_inf_principal, mem_ae_iff, restrict_apply_eq_zero' hs, compl_set_of, not_imp, and_comm (_ ∈ s)]
    rfl

@[simp]
theorem ae_restrict_eq_bot {s} : (μ.restrict s).ae = ⊥ ↔ μ s = 0 :=
  ae_eq_bot.trans restrict_eq_zero

@[simp]
theorem ae_restrict_ne_bot {s} : (μ.restrict s).ae.ne_bot ↔ 0 < μ s :=
  ne_bot_iff.trans$ (not_congr ae_restrict_eq_bot).trans pos_iff_ne_zero.symm

theorem self_mem_ae_restrict {s} (hs : MeasurableSet s) : s ∈ (μ.restrict s).ae :=
  by 
    simp only [ae_restrict_eq hs, exists_prop, mem_principal, mem_inf_iff] <;>
      exact ⟨_, univ_mem, s, subset.rfl, (univ_inter s).symm⟩

/-- A version of the **Borel-Cantelli lemma**: if `pᵢ` is a sequence of predicates such that
`∑ μ {x | pᵢ x}` is finite, then the measure of `x` such that `pᵢ x` holds frequently as `i → ∞` (or
equivalently, `pᵢ x` holds for infinitely many `i`) is equal to zero. -/
theorem measure_set_of_frequently_eq_zero {p : ℕ → α → Prop} (hp : (∑'i, μ { x | p i x }) ≠ ∞) :
  μ { x | ∃ᶠn in at_top, p n x } = 0 :=
  by 
    simpa only [limsup_eq_infi_supr_of_nat, frequently_at_top, set_of_forall, set_of_exists] using
      measure_limsup_eq_zero hp

/-- A version of the **Borel-Cantelli lemma**: if `sᵢ` is a sequence of sets such that
`∑ μ sᵢ` exists, then for almost all `x`, `x` does not belong to almost all `sᵢ`. -/
theorem ae_eventually_not_mem {s : ℕ → Set α} (hs : (∑'i, μ (s i)) ≠ ∞) : ∀ᵐx ∂μ, ∀ᶠn in at_top, x ∉ s n :=
  measure_set_of_frequently_eq_zero hs

section Dirac

variable[MeasurableSpace α]

theorem mem_ae_dirac_iff {a : α} (hs : MeasurableSet s) : s ∈ (dirac a).ae ↔ a ∈ s :=
  by 
    byCases' a ∈ s <;> simp [mem_ae_iff, dirac_apply', hs.compl, indicator_apply]

theorem ae_dirac_iff {a : α} {p : α → Prop} (hp : MeasurableSet { x | p x }) : (∀ᵐx ∂dirac a, p x) ↔ p a :=
  mem_ae_dirac_iff hp

@[simp]
theorem ae_dirac_eq [MeasurableSingletonClass α] (a : α) : (dirac a).ae = pure a :=
  by 
    ext s 
    simp [mem_ae_iff, imp_false]

theorem ae_eq_dirac' [MeasurableSingletonClass β] {a : α} {f : α → β} (hf : Measurable f) :
  f =ᵐ[dirac a] const α (f a) :=
  (ae_dirac_iff$ show MeasurableSet (f ⁻¹' {f a}) from hf$ measurable_set_singleton _).2 rfl

theorem ae_eq_dirac [MeasurableSingletonClass α] {a : α} (f : α → δ) : f =ᵐ[dirac a] const α (f a) :=
  by 
    simp [Filter.EventuallyEq]

end Dirac

theorem restrict_mono_ae (h : s ≤ᵐ[μ] t) : μ.restrict s ≤ μ.restrict t :=
  by 
    intro u hu 
    simp only [restrict_apply hu]
    exact measure_mono_ae (h.mono$ fun x hx => And.imp id hx)

theorem restrict_congr_set (H : s =ᵐ[μ] t) : μ.restrict s = μ.restrict t :=
  le_antisymmₓ (restrict_mono_ae H.le) (restrict_mono_ae H.symm.le)

section IsFiniteMeasure

include m0

/-- A measure `μ` is called finite if `μ univ < ∞`. -/
class is_finite_measure(μ : Measureₓ α) : Prop where 
  measure_univ_lt_top : μ univ < ∞

instance restrict.is_finite_measure (μ : Measureₓ α) [hs : Fact (μ s < ∞)] : is_finite_measure (μ.restrict s) :=
  ⟨by 
      simp [hs.elim]⟩

theorem measure_lt_top (μ : Measureₓ α) [is_finite_measure μ] (s : Set α) : μ s < ∞ :=
  (measure_mono (subset_univ s)).trans_lt is_finite_measure.measure_univ_lt_top

theorem measure_ne_top (μ : Measureₓ α) [is_finite_measure μ] (s : Set α) : μ s ≠ ∞ :=
  ne_of_ltₓ (measure_lt_top μ s)

theorem measure_compl_le_add_of_le_add [is_finite_measure μ] (hs : MeasurableSet s) (ht : MeasurableSet t) {ε : ℝ≥0∞}
  (h : μ s ≤ μ t+ε) : μ («expr ᶜ» t) ≤ μ («expr ᶜ» s)+ε :=
  by 
    rw [measure_compl ht (measure_ne_top μ _), measure_compl hs (measure_ne_top μ _), tsub_le_iff_right]
    calc μ univ = (μ univ - μ s)+μ s :=
      (tsub_add_cancel_of_le$ measure_mono s.subset_univ).symm _ ≤ (μ univ - μ s)+μ t+ε := add_le_add_left h _ _ = _ :=
      by 
        rw [add_right_commₓ, add_assocₓ]

theorem measure_compl_le_add_iff [is_finite_measure μ] (hs : MeasurableSet s) (ht : MeasurableSet t) {ε : ℝ≥0∞} :
  (μ («expr ᶜ» s) ≤ μ («expr ᶜ» t)+ε) ↔ μ t ≤ μ s+ε :=
  ⟨fun h => compl_compl s ▸ compl_compl t ▸ measure_compl_le_add_of_le_add hs.compl ht.compl h,
    measure_compl_le_add_of_le_add ht hs⟩

/-- The measure of the whole space with respect to a finite measure, considered as `ℝ≥0`. -/
def measure_univ_nnreal (μ : Measureₓ α) :  ℝ≥0  :=
  (μ univ).toNnreal

@[simp]
theorem coe_measure_univ_nnreal (μ : Measureₓ α) [is_finite_measure μ] : «expr↑ » (measure_univ_nnreal μ) = μ univ :=
  Ennreal.coe_to_nnreal (measure_ne_top μ univ)

instance is_finite_measure_zero : is_finite_measure (0 : Measureₓ α) :=
  ⟨by 
      simp ⟩

instance (priority := 100)is_finite_measure_of_is_empty [IsEmpty α] : is_finite_measure μ :=
  by 
    rw [eq_zero_of_is_empty μ]
    infer_instance

@[simp]
theorem measure_univ_nnreal_zero : measure_univ_nnreal (0 : Measureₓ α) = 0 :=
  rfl

omit m0

instance is_finite_measure_add [is_finite_measure μ] [is_finite_measure ν] : is_finite_measure (μ+ν) :=
  { measure_univ_lt_top :=
      by 
        rw [measure.coe_add, Pi.add_apply, Ennreal.add_lt_top]
        exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩ }

instance is_finite_measure_smul_nnreal [is_finite_measure μ] {r :  ℝ≥0 } : is_finite_measure (r • μ) :=
  { measure_univ_lt_top := Ennreal.mul_lt_top Ennreal.coe_ne_top (measure_ne_top _ _) }

theorem is_finite_measure_of_le (μ : Measureₓ α) [is_finite_measure μ] (h : ν ≤ μ) : is_finite_measure ν :=
  { measure_univ_lt_top := lt_of_le_of_ltₓ (h Set.Univ MeasurableSet.univ) (measure_lt_top _ _) }

@[instance]
theorem measure.is_finite_measure_map {m : MeasurableSpace α} (μ : Measureₓ α) [is_finite_measure μ] (f : α → β) :
  is_finite_measure (map f μ) :=
  by 
    byCases' hf : Measurable f
    ·
      constructor 
      rw [map_apply hf MeasurableSet.univ]
      exact measure_lt_top μ _
    ·
      rw [map_of_not_measurable hf]
      exact MeasureTheory.is_finite_measure_zero

@[simp]
theorem measure_univ_nnreal_eq_zero [is_finite_measure μ] : measure_univ_nnreal μ = 0 ↔ μ = 0 :=
  by 
    rw [←MeasureTheory.Measure.measure_univ_eq_zero, ←coe_measure_univ_nnreal]
    normCast

theorem measure_univ_nnreal_pos [is_finite_measure μ] (hμ : μ ≠ 0) : 0 < measure_univ_nnreal μ :=
  by 
    contrapose! hμ 
    simpa [measure_univ_nnreal_eq_zero, le_zero_iff] using hμ

/-- `le_of_add_le_add_left` is normally applicable to `ordered_cancel_add_comm_monoid`,
but it holds for measures with the additional assumption that μ is finite. -/
theorem measure.le_of_add_le_add_left [is_finite_measure μ] (A2 : (μ+ν₁) ≤ μ+ν₂) : ν₁ ≤ ν₂ :=
  fun S B1 => Ennreal.le_of_add_le_add_left (MeasureTheory.measure_ne_top μ S) (A2 S B1)

theorem summable_measure_to_real [hμ : is_finite_measure μ] {f : ℕ → Set α} (hf₁ : ∀ i : ℕ, MeasurableSet (f i))
  (hf₂ : Pairwise (Disjoint on f)) : Summable fun x => (μ (f x)).toReal :=
  by 
    apply Ennreal.summable_to_real 
    rw [←MeasureTheory.measure_Union hf₂ hf₁]
    exact ne_of_ltₓ (measure_lt_top _ _)

end IsFiniteMeasure

section IsProbabilityMeasure

include m0

/-- A measure `μ` is called a probability measure if `μ univ = 1`. -/
class is_probability_measure(μ : Measureₓ α) : Prop where 
  measure_univ : μ univ = 1

export IsProbabilityMeasure(measure_univ)

instance (priority := 100)is_probability_measure.to_is_finite_measure (μ : Measureₓ α) [is_probability_measure μ] :
  is_finite_measure μ :=
  ⟨by 
      simp only [measure_univ, Ennreal.one_lt_top]⟩

theorem is_probability_measure.ne_zero (μ : Measureₓ α) [is_probability_measure μ] : μ ≠ 0 :=
  mt measure_univ_eq_zero.2$
    by 
      simp [measure_univ]

omit m0

instance measure.dirac.is_probability_measure [MeasurableSpace α] {x : α} : is_probability_measure (dirac x) :=
  ⟨dirac_apply_of_mem$ mem_univ x⟩

theorem prob_add_prob_compl [is_probability_measure μ] (h : MeasurableSet s) : (μ s+μ («expr ᶜ» s)) = 1 :=
  (measure_add_measure_compl h).trans measure_univ

theorem prob_le_one [is_probability_measure μ] : μ s ≤ 1 :=
  (measure_mono$ Set.subset_univ _).trans_eq measure_univ

end IsProbabilityMeasure

section NoAtoms

/-- Measure `μ` *has no atoms* if the measure of each singleton is zero.

NB: Wikipedia assumes that for any measurable set `s` with positive `μ`-measure,
there exists a measurable `t ⊆ s` such that `0 < μ t < μ s`. While this implies `μ {x} = 0`,
the converse is not true. -/
class has_no_atoms{m0 : MeasurableSpace α}(μ : Measureₓ α) : Prop where 
  measure_singleton : ∀ x, μ {x} = 0

export HasNoAtoms(measure_singleton)

attribute [simp] measure_singleton

variable[has_no_atoms μ]

theorem _root_.set.subsingleton.measure_zero {α : Type _} {m : MeasurableSpace α} {s : Set α} (hs : s.subsingleton)
  (μ : Measureₓ α) [has_no_atoms μ] : μ s = 0 :=
  hs.induction_on measure_empty measure_singleton

theorem measure.restrict_singleton' {a : α} : μ.restrict {a} = 0 :=
  by 
    simp only [measure_singleton, measure.restrict_eq_zero]

instance  (s : Set α) : has_no_atoms (μ.restrict s) :=
  by 
    refine' ⟨fun x => _⟩
    obtain ⟨t, hxt, ht1, ht2⟩ := exists_measurable_superset_of_null (measure_singleton x : μ {x} = 0)
    apply measure_mono_null hxt 
    rw [measure.restrict_apply ht1]
    apply measure_mono_null (inter_subset_left t s) ht2

theorem _root_.set.countable.measure_zero {α : Type _} {m : MeasurableSpace α} {s : Set α} (h : countable s)
  (μ : Measureₓ α) [has_no_atoms μ] : μ s = 0 :=
  by 
    rw [←bUnion_of_singleton s, ←nonpos_iff_eq_zero]
    refine' le_transₓ (measure_bUnion_le h _) _ 
    simp 

theorem _root_.set.finite.measure_zero {α : Type _} {m : MeasurableSpace α} {s : Set α} (h : s.finite) (μ : Measureₓ α)
  [has_no_atoms μ] : μ s = 0 :=
  h.countable.measure_zero μ

theorem _root_.finset.measure_zero {α : Type _} {m : MeasurableSpace α} (s : Finset α) (μ : Measureₓ α)
  [has_no_atoms μ] : μ s = 0 :=
  s.finite_to_set.measure_zero μ

theorem insert_ae_eq_self (a : α) (s : Set α) : (insert a s : Set α) =ᵐ[μ] s :=
  union_ae_eq_right.2$ measure_mono_null (diff_subset _ _) (measure_singleton _)

variable[PartialOrderₓ α]{a b : α}

theorem Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a :=
  by 
    simp only [←Iic_diff_right, diff_ae_eq_self, measure_mono_null (Set.inter_subset_right _ _) (measure_singleton a)]

theorem Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a :=
  @Iio_ae_eq_Iic (OrderDual α) ‹_› ‹_› _ _ _

theorem Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b :=
  (ae_eq_refl _).inter Iio_ae_eq_Iic

theorem Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b :=
  Ioi_ae_eq_Ici.inter (ae_eq_refl _)

theorem Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b :=
  Ioi_ae_eq_Ici.inter (ae_eq_refl _)

theorem Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b :=
  Ioi_ae_eq_Ici.inter Iio_ae_eq_Iic

theorem Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b :=
  (ae_eq_refl _).inter Iio_ae_eq_Iic

theorem Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b :=
  Ioo_ae_eq_Ico.symm.trans Ioo_ae_eq_Ioc

end NoAtoms

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ite_ae_eq_of_measure_zero
{γ}
(f : α → γ)
(g : α → γ)
(s : set α)
(hs_zero : «expr = »(μ s, 0)) : «expr =ᵐ[ ] »(λ x, ite «expr ∈ »(x, s) (f x) (g x), μ, g) :=
begin
  have [ident h_ss] [":", expr «expr ⊆ »(«expr ᶜ»(s), {a : α | «expr = »(ite «expr ∈ »(a, s) (f a) (g a), g a)})] [],
  from [expr λ x hx, by simp [] [] [] ["[", expr (set.mem_compl_iff _ _).mp hx, "]"] [] []],
  refine [expr measure_mono_null _ hs_zero],
  nth_rewrite [0] ["<-", expr compl_compl s] [],
  rwa [expr set.compl_subset_compl] []
end

theorem ite_ae_eq_of_measure_compl_zero {γ} (f : α → γ) (g : α → γ) (s : Set α) (hs_zero : μ («expr ᶜ» s) = 0) :
  (fun x => ite (x ∈ s) (f x) (g x)) =ᵐ[μ] f :=
  by 
    filterUpwards [hs_zero]
    intros 
    splitIfs 
    rfl

namespace Measureₓ

/-- A measure is called finite at filter `f` if it is finite at some set `s ∈ f`.
Equivalently, it is eventually finite at `s` in `f.lift' powerset`. -/
def finite_at_filter {m0 : MeasurableSpace α} (μ : Measureₓ α) (f : Filter α) : Prop :=
  ∃ (s : _)(_ : s ∈ f), μ s < ∞

theorem finite_at_filter_of_finite {m0 : MeasurableSpace α} (μ : Measureₓ α) [is_finite_measure μ] (f : Filter α) :
  μ.finite_at_filter f :=
  ⟨univ, univ_mem, measure_lt_top μ univ⟩

theorem finite_at_filter.exists_mem_basis {f : Filter α} (hμ : finite_at_filter μ f) {p : ι → Prop} {s : ι → Set α}
  (hf : f.has_basis p s) : ∃ (i : _)(hi : p i), μ (s i) < ∞ :=
  (hf.exists_iff fun s t hst ht => (measure_mono hst).trans_lt ht).1 hμ

theorem finite_at_bot {m0 : MeasurableSpace α} (μ : Measureₓ α) : μ.finite_at_filter ⊥ :=
  ⟨∅, mem_bot,
    by 
      simp only [measure_empty, WithTop.zero_lt_top]⟩

/-- `μ` has finite spanning sets in `C` if there is a countable sequence of sets in `C` that have
  finite measures. This structure is a type, which is useful if we want to record extra properties
  about the sets, such as that they are monotone.
  `sigma_finite` is defined in terms of this: `μ` is σ-finite if there exists a sequence of
  finite spanning sets in the collection of all measurable sets. -/
@[protectProj, nolint has_inhabited_instance]
structure finite_spanning_sets_in{m0 : MeasurableSpace α}(μ : Measureₓ α)(C : Set (Set α)) where 
  Set : ℕ → Set α 
  set_mem : ∀ i, Set i ∈ C 
  Finite : ∀ i, μ (Set i) < ∞
  spanning : (⋃i, Set i) = univ

end Measureₓ

open Measureₓ

/-- A measure `μ` is called σ-finite if there is a countable collection of sets
 `{ A i | i ∈ ℕ }` such that `μ (A i) < ∞` and `⋃ i, A i = s`. -/
class sigma_finite{m0 : MeasurableSpace α}(μ : Measureₓ α) : Prop where 
  out' : Nonempty (μ.finite_spanning_sets_in univ)

theorem sigma_finite_iff : sigma_finite μ ↔ Nonempty (μ.finite_spanning_sets_in univ) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem sigma_finite.out (h : sigma_finite μ) : Nonempty (μ.finite_spanning_sets_in univ) :=
  h.1

include m0

/-- If `μ` is σ-finite it has finite spanning sets in the collection of all measurable sets. -/
def measure.to_finite_spanning_sets_in (μ : Measureₓ α) [h : sigma_finite μ] :
  μ.finite_spanning_sets_in { s | MeasurableSet s } :=
  { Set := fun n => to_measurable μ (h.out.some.set n), set_mem := fun n => measurable_set_to_measurable _ _,
    Finite :=
      fun n =>
        by 
          rw [measure_to_measurable]
          exact h.out.some.finite n,
    spanning := eq_univ_of_subset (Union_subset_Union$ fun n => subset_to_measurable _ _) h.out.some.spanning }

/-- A noncomputable way to get a monotone collection of sets that span `univ` and have finite
  measure using `classical.some`. This definition satisfies monotonicity in addition to all other
  properties in `sigma_finite`. -/
def spanning_sets (μ : Measureₓ α) [sigma_finite μ] (i : ℕ) : Set α :=
  accumulate μ.to_finite_spanning_sets_in.set i

theorem monotone_spanning_sets (μ : Measureₓ α) [sigma_finite μ] : Monotone (spanning_sets μ) :=
  monotone_accumulate

theorem measurable_spanning_sets (μ : Measureₓ α) [sigma_finite μ] (i : ℕ) : MeasurableSet (spanning_sets μ i) :=
  MeasurableSet.Union$ fun j => MeasurableSet.Union_Prop$ fun hij => μ.to_finite_spanning_sets_in.set_mem j

theorem measure_spanning_sets_lt_top (μ : Measureₓ α) [sigma_finite μ] (i : ℕ) : μ (spanning_sets μ i) < ∞ :=
  measure_bUnion_lt_top (finite_le_nat i)$ fun j _ => (μ.to_finite_spanning_sets_in.finite j).Ne

theorem Union_spanning_sets (μ : Measureₓ α) [sigma_finite μ] : (⋃i : ℕ, spanning_sets μ i) = univ :=
  by 
    simpRw [spanning_sets, Union_accumulate, μ.to_finite_spanning_sets_in.spanning]

theorem is_countably_spanning_spanning_sets (μ : Measureₓ α) [sigma_finite μ] :
  IsCountablySpanning (range (spanning_sets μ)) :=
  ⟨spanning_sets μ, mem_range_self, Union_spanning_sets μ⟩

/-- `spanning_sets_index μ x` is the least `n : ℕ` such that `x ∈ spanning_sets μ n`. -/
def spanning_sets_index (μ : Measureₓ α) [sigma_finite μ] (x : α) : ℕ :=
  Nat.findₓ$ Union_eq_univ_iff.1 (Union_spanning_sets μ) x

theorem measurable_spanning_sets_index (μ : Measureₓ α) [sigma_finite μ] : Measurable (spanning_sets_index μ) :=
  measurable_find _$ measurable_spanning_sets μ

theorem preimage_spanning_sets_index_singleton (μ : Measureₓ α) [sigma_finite μ] (n : ℕ) :
  spanning_sets_index μ ⁻¹' {n} = disjointed (spanning_sets μ) n :=
  preimage_find_eq_disjointed _ _ _

theorem spanning_sets_index_eq_iff (μ : Measureₓ α) [sigma_finite μ] {x : α} {n : ℕ} :
  spanning_sets_index μ x = n ↔ x ∈ disjointed (spanning_sets μ) n :=
  by 
    convert Set.ext_iff.1 (preimage_spanning_sets_index_singleton μ n) x

theorem mem_disjointed_spanning_sets_index (μ : Measureₓ α) [sigma_finite μ] (x : α) :
  x ∈ disjointed (spanning_sets μ) (spanning_sets_index μ x) :=
  (spanning_sets_index_eq_iff μ).1 rfl

theorem mem_spanning_sets_index (μ : Measureₓ α) [sigma_finite μ] (x : α) :
  x ∈ spanning_sets μ (spanning_sets_index μ x) :=
  disjointed_subset _ _ (mem_disjointed_spanning_sets_index μ x)

theorem mem_spanning_sets_of_index_le (μ : Measureₓ α) [sigma_finite μ] (x : α) {n : ℕ}
  (hn : spanning_sets_index μ x ≤ n) : x ∈ spanning_sets μ n :=
  monotone_spanning_sets μ hn (mem_spanning_sets_index μ x)

theorem eventually_mem_spanning_sets (μ : Measureₓ α) [sigma_finite μ] (x : α) : ∀ᶠn in at_top, x ∈ spanning_sets μ n :=
  eventually_at_top.2 ⟨spanning_sets_index μ x, fun b => mem_spanning_sets_of_index_le μ x⟩

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_of_forall_measure_lt_top_ae_restrict
{μ : measure α}
[sigma_finite μ]
(P : α → exprProp())
(h : ∀
 s, measurable_set s → «expr < »(μ s, «expr∞»()) → «expr∀ᵐ ∂ , »((x), μ.restrict s, P x)) : «expr∀ᵐ ∂ , »((x), μ, P x) :=
begin
  have [] [":", expr ∀ n, «expr∀ᵐ ∂ , »((x), μ, «expr ∈ »(x, spanning_sets μ n) → P x)] [],
  { assume [binders (n)],
    have [] [] [":=", expr h (spanning_sets μ n) (measurable_spanning_sets _ _) (measure_spanning_sets_lt_top _ _)],
    rwa [expr ae_restrict_iff' (measurable_spanning_sets _ _)] ["at", ident this] },
  filter_upwards ["[", expr ae_all_iff.2 this, "]"] [],
  assume [binders (x hx)],
  exact [expr hx _ (mem_spanning_sets_index _ _)]
end

omit m0

namespace Measureₓ

theorem supr_restrict_spanning_sets [sigma_finite μ] (hs : MeasurableSet s) :
  (⨆i, μ.restrict (spanning_sets μ i) s) = μ s :=
  by 
    convert (restrict_Union_apply_eq_supr (measurable_spanning_sets μ) _ hs).symm
    ·
      simp [Union_spanning_sets]
    ·
      exact directed_of_sup (monotone_spanning_sets μ)

namespace FiniteSpanningSetsIn

variable{C D : Set (Set α)}

/-- If `μ` has finite spanning sets in `C` and `C ∩ {s | μ s < ∞} ⊆ D` then `μ` has finite spanning
sets in `D`. -/
protected def mono' (h : μ.finite_spanning_sets_in C) (hC : C ∩ { s | μ s < ∞ } ⊆ D) : μ.finite_spanning_sets_in D :=
  ⟨h.set, fun i => hC ⟨h.set_mem i, h.finite i⟩, h.finite, h.spanning⟩

/-- If `μ` has finite spanning sets in `C` and `C ⊆ D` then `μ` has finite spanning sets in `D`. -/
protected def mono (h : μ.finite_spanning_sets_in C) (hC : C ⊆ D) : μ.finite_spanning_sets_in D :=
  h.mono' fun s hs => hC hs.1

/-- If `μ` has finite spanning sets in the collection of measurable sets `C`, then `μ` is σ-finite.
-/
protected theorem sigma_finite (h : μ.finite_spanning_sets_in C) : sigma_finite μ :=
  ⟨⟨h.mono$ subset_univ C⟩⟩

/-- An extensionality for measures. It is `ext_of_generate_from_of_Union` formulated in terms of
`finite_spanning_sets_in`. -/
protected theorem ext {ν : Measureₓ α} {C : Set (Set α)} (hA : ‹_› = generate_from C) (hC : IsPiSystem C)
  (h : μ.finite_spanning_sets_in C) (h_eq : ∀ s _ : s ∈ C, μ s = ν s) : μ = ν :=
  ext_of_generate_from_of_Union C _ hA hC h.spanning h.set_mem (fun i => (h.finite i).Ne) h_eq

protected theorem IsCountablySpanning (h : μ.finite_spanning_sets_in C) : IsCountablySpanning C :=
  ⟨h.set, h.set_mem, h.spanning⟩

end FiniteSpanningSetsIn

theorem sigma_finite_of_countable {S : Set (Set α)} (hc : countable S) (hμ : ∀ s _ : s ∈ S, μ s < ∞) (hU : ⋃₀S = univ) :
  sigma_finite μ :=
  by 
    obtain ⟨s, hμ, hs⟩ : ∃ s : ℕ → Set α, (∀ n, μ (s n) < ∞) ∧ (⋃n, s n) = univ 
    exact
      (@exists_seq_cover_iff_countable _ (fun x => μ x < ⊤)
            ⟨∅,
              by 
                simp ⟩).2
        ⟨S, hc, hμ, hU⟩
    exact ⟨⟨⟨fun n => s n, fun n => trivialₓ, hμ, hs⟩⟩⟩

/-- Given measures `μ`, `ν` where `ν ≤ μ`, `finite_spanning_sets_in.of_le` provides the induced
`finite_spanning_set` with respect to `ν` from a `finite_spanning_set` with respect to `μ`. -/
def finite_spanning_sets_in.of_le (h : ν ≤ μ) {C : Set (Set α)} (S : μ.finite_spanning_sets_in C) :
  ν.finite_spanning_sets_in C :=
  { Set := S.set, set_mem := S.set_mem, Finite := fun n => lt_of_le_of_ltₓ (le_iff'.1 h _) (S.finite n),
    spanning := S.spanning }

theorem sigma_finite_of_le (μ : Measureₓ α) [hs : sigma_finite μ] (h : ν ≤ μ) : sigma_finite ν :=
  ⟨hs.out.map$ finite_spanning_sets_in.of_le h⟩

end Measureₓ

include m0

/-- Every finite measure is σ-finite. -/
instance (priority := 100)is_finite_measure.to_sigma_finite (μ : Measureₓ α) [is_finite_measure μ] : sigma_finite μ :=
  ⟨⟨⟨fun _ => univ, fun _ => trivialₓ, fun _ => measure_lt_top μ _, Union_const _⟩⟩⟩

instance restrict.sigma_finite (μ : Measureₓ α) [sigma_finite μ] (s : Set α) : sigma_finite (μ.restrict s) :=
  by 
    refine' ⟨⟨⟨spanning_sets μ, fun _ => trivialₓ, fun i => _, Union_spanning_sets μ⟩⟩⟩
    rw [restrict_apply (measurable_spanning_sets μ i)]
    exact (measure_mono$ inter_subset_left _ _).trans_lt (measure_spanning_sets_lt_top μ i)

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance sum.sigma_finite {ι} [fintype ι] (μ : ι → measure α) [∀ i, sigma_finite (μ i)] : sigma_finite (sum μ) :=
begin
  haveI [] [":", expr encodable ι] [":=", expr fintype.encodable ι],
  have [] [":", expr ∀
   n, measurable_set «expr⋂ , »((i : ι), spanning_sets (μ i) n)] [":=", expr λ
   n, measurable_set.Inter (λ i, measurable_spanning_sets (μ i) n)],
  refine [expr ⟨⟨⟨λ n, «expr⋂ , »((i), spanning_sets (μ i) n), λ _, trivial, λ n, _, _⟩⟩⟩],
  { rw ["[", expr sum_apply _ (this n), ",", expr tsum_fintype, ",", expr ennreal.sum_lt_top_iff, "]"] [],
    rintro [ident i, "-"],
    exact [expr «expr $ »(measure_mono, Inter_subset _ i).trans_lt (measure_spanning_sets_lt_top (μ i) n)] },
  { rw ["[", expr Union_Inter_of_monotone, "]"] [],
    simp_rw ["[", expr Union_spanning_sets, ",", expr Inter_univ, "]"] [],
    exact [expr λ i, monotone_spanning_sets (μ i)] }
end

instance add.sigma_finite (μ ν : Measureₓ α) [sigma_finite μ] [sigma_finite ν] : sigma_finite (μ+ν) :=
  by 
    rw [←sum_cond]
    refine' @sum.sigma_finite _ _ _ _ _ (Bool.rec _ _) <;> simpa

theorem sigma_finite.of_map (μ : Measureₓ α) {f : α → β} (hf : Measurable f) (h : sigma_finite (map f μ)) :
  sigma_finite μ :=
  ⟨⟨⟨fun n => f ⁻¹' spanning_sets (map f μ) n, fun n => trivialₓ,
        fun n =>
          by 
            simp only [←map_apply hf, measurable_spanning_sets, measure_spanning_sets_lt_top],
        by 
          rw [←preimage_Union, Union_spanning_sets, preimage_univ]⟩⟩⟩

/-- A measure is called locally finite if it is finite in some neighborhood of each point. -/
class is_locally_finite_measure[TopologicalSpace α](μ : Measureₓ α) : Prop where 
  finite_at_nhds : ∀ x, μ.finite_at_filter (𝓝 x)

instance (priority := 100)is_finite_measure.to_is_locally_finite_measure [TopologicalSpace α] (μ : Measureₓ α)
  [is_finite_measure μ] : is_locally_finite_measure μ :=
  ⟨fun x => finite_at_filter_of_finite _ _⟩

theorem measure.finite_at_nhds [TopologicalSpace α] (μ : Measureₓ α) [is_locally_finite_measure μ] (x : α) :
  μ.finite_at_filter (𝓝 x) :=
  is_locally_finite_measure.finite_at_nhds x

theorem measure.smul_finite (μ : Measureₓ α) [is_finite_measure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) :
  is_finite_measure (c • μ) :=
  by 
    lift c to  ℝ≥0  using hc 
    exact MeasureTheory.is_finite_measure_smul_nnreal

theorem measure.exists_is_open_measure_lt_top [TopologicalSpace α] (μ : Measureₓ α) [is_locally_finite_measure μ]
  (x : α) : ∃ s : Set α, x ∈ s ∧ IsOpen s ∧ μ s < ∞ :=
  by 
    simpa only [exists_prop, And.assoc] using (μ.finite_at_nhds x).exists_mem_basis (nhds_basis_opens x)

instance is_locally_finite_measure_smul_nnreal [TopologicalSpace α] (μ : Measureₓ α) [is_locally_finite_measure μ]
  (c :  ℝ≥0 ) : is_locally_finite_measure (c • μ) :=
  by 
    refine' ⟨fun x => _⟩
    rcases μ.exists_is_open_measure_lt_top x with ⟨o, xo, o_open, μo⟩
    refine' ⟨o, o_open.mem_nhds xo, _⟩
    apply Ennreal.mul_lt_top _ μo.ne 
    simp only [Ennreal.coe_ne_top, Ennreal.coe_of_nnreal_hom, Ne.def, not_false_iff]

omit m0

instance (priority := 100)sigma_finite_of_locally_finite [TopologicalSpace α]
  [TopologicalSpace.SecondCountableTopology α] [is_locally_finite_measure μ] : sigma_finite μ :=
  by 
    choose s hsx hsμ using μ.finite_at_nhds 
    rcases TopologicalSpace.countable_cover_nhds hsx with ⟨t, htc, htU⟩
    refine' measure.sigma_finite_of_countable (htc.image s) (ball_image_iff.2$ fun x hx => hsμ x) _ 
    rwa [sUnion_image]

/-- If a set has zero measure in a neighborhood of each of its points, then it has zero measure
in a second-countable space. -/
theorem null_of_locally_null [TopologicalSpace α] [TopologicalSpace.SecondCountableTopology α] (s : Set α)
  (hs : ∀ x _ : x ∈ s, ∃ (u : _)(_ : u ∈ 𝓝[s] x), μ (s ∩ u) = 0) : μ s = 0 :=
  by 
    choose! u hu using hs 
    obtain ⟨t, ts, t_count, ht⟩ : ∃ (t : _)(_ : t ⊆ s), t.countable ∧ s ⊆ ⋃(x : _)(_ : x ∈ t), u x :=
      TopologicalSpace.countable_cover_nhds_within fun x hx => (hu x hx).1
    replace ht : s ⊆ ⋃(x : _)(_ : x ∈ t), s ∩ u x
    ·
      ·
        rw [←inter_bUnion]
        exact subset_inter (subset.refl _) ht 
    apply measure_mono_null ht 
    exact (measure_bUnion_null_iff t_count).2 fun x hx => (hu x (ts hx)).2

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If two finite measures give the same mass to the whole space and coincide on a π-system made
of measurable sets, then they coincide on all sets in the σ-algebra generated by the π-system. -/
theorem ext_on_measurable_space_of_generate_finite
{α}
(m₀ : measurable_space α)
{μ ν : measure α}
[is_finite_measure μ]
(C : set (set α))
(hμν : ∀ s «expr ∈ » C, «expr = »(μ s, ν s))
{m : measurable_space α}
(h : «expr ≤ »(m, m₀))
(hA : «expr = »(m, measurable_space.generate_from C))
(hC : is_pi_system C)
(h_univ : «expr = »(μ set.univ, ν set.univ))
{s : set α}
(hs : m.measurable_set' s) : «expr = »(μ s, ν s) :=
begin
  haveI [] [":", expr is_finite_measure ν] [":=", expr begin
     constructor,
     rw ["<-", expr h_univ] [],
     apply [expr is_finite_measure.measure_univ_lt_top]
   end],
  refine [expr induction_on_inter hA hC (by simp [] [] [] [] [] []) hμν _ _ hs],
  { intros [ident t, ident h1t, ident h2t],
    have [ident h1t_] [":", expr @measurable_set α m₀ t] [],
    from [expr h _ h1t],
    rw ["[", expr @measure_compl α m₀ μ t h1t_ (@measure_ne_top α m₀ μ _ t), ",", expr @measure_compl α m₀ ν t h1t_ (@measure_ne_top α m₀ ν _ t), ",", expr h_univ, ",", expr h2t, "]"] [] },
  { intros [ident f, ident h1f, ident h2f, ident h3f],
    have [ident h2f_] [":", expr ∀ i : exprℕ(), @measurable_set α m₀ (f i)] [],
    from [expr λ i, h _ (h2f i)],
    have [ident h_Union] [":", expr @measurable_set α m₀ «expr⋃ , »((i : exprℕ()), f i)] [],
    from [expr @measurable_set.Union α exprℕ() m₀ _ f h2f_],
    simp [] [] [] ["[", expr measure_Union, ",", expr h_Union, ",", expr h1f, ",", expr h3f, ",", expr h2f_, "]"] [] [] }
end

/-- Two finite measures are equal if they are equal on the π-system generating the σ-algebra
  (and `univ`). -/
theorem ext_of_generate_finite (C : Set (Set α)) (hA : m0 = generate_from C) (hC : IsPiSystem C) [is_finite_measure μ]
  (hμν : ∀ s _ : s ∈ C, μ s = ν s) (h_univ : μ univ = ν univ) : μ = ν :=
  measure.ext fun s hs => ext_on_measurable_space_of_generate_finite m0 C hμν le_rfl hA hC h_univ hs

namespace Measureₓ

section disjointed

include m0

/-- Given `S : μ.finite_spanning_sets_in {s | measurable_set s}`,
`finite_spanning_sets_in.disjointed` provides a `finite_spanning_sets_in {s | measurable_set s}`
such that its underlying sets are pairwise disjoint. -/
protected def finite_spanning_sets_in.disjointed {μ : Measureₓ α}
  (S : μ.finite_spanning_sets_in { s | MeasurableSet s }) : μ.finite_spanning_sets_in { s | MeasurableSet s } :=
  ⟨disjointed S.set, MeasurableSet.disjointed S.set_mem,
    fun n => lt_of_le_of_ltₓ (measure_mono (disjointed_subset S.set n)) (S.finite _), S.spanning ▸ Union_disjointed⟩

theorem finite_spanning_sets_in.disjointed_set_eq {μ : Measureₓ α}
  (S : μ.finite_spanning_sets_in { s | MeasurableSet s }) : S.disjointed.set = disjointed S.set :=
  rfl

theorem exists_eq_disjoint_finite_spanning_sets_in (μ ν : Measureₓ α) [sigma_finite μ] [sigma_finite ν] :
  ∃ (S : μ.finite_spanning_sets_in { s | MeasurableSet s })(T : ν.finite_spanning_sets_in { s | MeasurableSet s }),
    S.set = T.set ∧ Pairwise (Disjoint on S.set) :=
  let S := (μ+ν).toFiniteSpanningSetsIn.disjointed
  ⟨S.of_le (measure.le_add_right le_rfl), S.of_le (measure.le_add_left le_rfl), rfl, disjoint_disjointed _⟩

end disjointed

namespace FiniteAtFilter

variable{f g : Filter α}

theorem filter_mono (h : f ≤ g) : μ.finite_at_filter g → μ.finite_at_filter f :=
  fun ⟨s, hs, hμ⟩ => ⟨s, h hs, hμ⟩

theorem inf_of_left (h : μ.finite_at_filter f) : μ.finite_at_filter (f⊓g) :=
  h.filter_mono inf_le_left

theorem inf_of_right (h : μ.finite_at_filter g) : μ.finite_at_filter (f⊓g) :=
  h.filter_mono inf_le_right

@[simp]
theorem inf_ae_iff : μ.finite_at_filter (f⊓μ.ae) ↔ μ.finite_at_filter f :=
  by 
    refine' ⟨_, fun h => h.filter_mono inf_le_left⟩
    rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hμ⟩
    suffices  : μ t ≤ μ (t ∩ u)
    exact ⟨t, ht, this.trans_lt hμ⟩
    exact measure_mono_ae (mem_of_superset hu fun x hu ht => ⟨ht, hu⟩)

alias inf_ae_iff ↔ MeasureTheory.Measure.FiniteAtFilter.of_inf_ae _

theorem filter_mono_ae (h : f⊓μ.ae ≤ g) (hg : μ.finite_at_filter g) : μ.finite_at_filter f :=
  inf_ae_iff.1 (hg.filter_mono h)

protected theorem measure_mono (h : μ ≤ ν) : ν.finite_at_filter f → μ.finite_at_filter f :=
  fun ⟨s, hs, hν⟩ => ⟨s, hs, (measure.le_iff'.1 h s).trans_lt hν⟩

@[mono]
protected theorem mono (hf : f ≤ g) (hμ : μ ≤ ν) : ν.finite_at_filter g → μ.finite_at_filter f :=
  fun h => (h.filter_mono hf).measure_mono hμ

protected theorem eventually (h : μ.finite_at_filter f) : ∀ᶠs in f.lift' powerset, μ s < ∞ :=
  (eventually_lift'_powerset'$ fun s t hst ht => (measure_mono hst).trans_lt ht).2 h

theorem filter_sup : μ.finite_at_filter f → μ.finite_at_filter g → μ.finite_at_filter (f⊔g) :=
  fun ⟨s, hsf, hsμ⟩ ⟨t, htg, htμ⟩ =>
    ⟨s ∪ t, union_mem_sup hsf htg, (measure_union_le s t).trans_lt (Ennreal.add_lt_top.2 ⟨hsμ, htμ⟩)⟩

end FiniteAtFilter

theorem finite_at_nhds_within [TopologicalSpace α] {m0 : MeasurableSpace α} (μ : Measureₓ α)
  [is_locally_finite_measure μ] (x : α) (s : Set α) : μ.finite_at_filter (𝓝[s] x) :=
  (finite_at_nhds μ x).inf_of_left

@[simp]
theorem finite_at_principal : μ.finite_at_filter (𝓟 s) ↔ μ s < ∞ :=
  ⟨fun ⟨t, ht, hμ⟩ => (measure_mono ht).trans_lt hμ, fun h => ⟨s, mem_principal_self s, h⟩⟩

theorem is_locally_finite_measure_of_le [TopologicalSpace α] {m : MeasurableSpace α} {μ ν : Measureₓ α}
  [H : is_locally_finite_measure μ] (h : ν ≤ μ) : is_locally_finite_measure ν :=
  let F := H.finite_at_nhds
  ⟨fun x => (F x).measure_mono h⟩

/-! ### Subtraction of measures -/


/-- The measure `μ - ν` is defined to be the least measure `τ` such that `μ ≤ τ + ν`.
It is the equivalent of `(μ - ν) ⊔ 0` if `μ` and `ν` were signed measures.
Compare with `ennreal.has_sub`.
Specifically, note that if you have `α = {1,2}`, and  `μ {1} = 2`, `μ {2} = 0`, and
`ν {2} = 2`, `ν {1} = 0`, then `(μ - ν) {1, 2} = 2`. However, if `μ ≤ ν`, and
`ν univ ≠ ∞`, then `(μ - ν) + ν = μ`. -/
noncomputable instance Sub {α : Type _} [MeasurableSpace α] : Sub (Measureₓ α) :=
  ⟨fun μ ν => Inf { τ | μ ≤ τ+ν }⟩

section MeasureSub

theorem sub_def : μ - ν = Inf { d | μ ≤ d+ν } :=
  rfl

theorem sub_eq_zero_of_le (h : μ ≤ ν) : μ - ν = 0 :=
  by 
    rw [←nonpos_iff_eq_zero', measure.sub_def]
    apply @Inf_le (Measureₓ α) _ _ 
    simp [h]

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This application lemma only works in special circumstances. Given knowledge of
when `μ ≤ ν` and `ν ≤ μ`, a more general application lemma can be written. -/
theorem sub_apply
[is_finite_measure ν]
(h₁ : measurable_set s)
(h₂ : «expr ≤ »(ν, μ)) : «expr = »(«expr - »(μ, ν) s, «expr - »(μ s, ν s)) :=
begin
  let [ident measure_sub] [":", expr measure α] [":=", expr @measure_theory.measure.of_measurable α _ (λ
    (t : set α)
    (h_t_measurable_set : measurable_set t), «expr - »(μ t, ν t)) (begin
      simp [] [] [] [] [] []
    end) (begin
      intros [ident g, ident h_meas, ident h_disj],
      simp [] [] ["only"] [] [] [],
      rw [expr ennreal.tsum_sub] [],
      repeat { rw ["<-", expr measure_theory.measure_Union h_disj h_meas] [] },
      exacts ["[", expr measure_theory.measure_ne_top _ _, ",", expr λ i, h₂ _ (h_meas _), "]"]
    end)],
  begin
    have [ident h_measure_sub_add] [":", expr «expr = »(«expr + »(ν, measure_sub), μ)] [],
    { ext [] [ident t, ident h_t_measurable_set] [],
      simp [] [] ["only"] ["[", expr pi.add_apply, ",", expr coe_add, "]"] [] [],
      rw ["[", expr measure_theory.measure.of_measurable_apply _ h_t_measurable_set, ",", expr add_comm, ",", expr tsub_add_cancel_of_le (h₂ t h_t_measurable_set), "]"] [] },
    have [ident h_measure_sub_eq] [":", expr «expr = »(«expr - »(μ, ν), measure_sub)] [],
    { rw [expr measure_theory.measure.sub_def] [],
      apply [expr le_antisymm],
      { apply [expr @Inf_le (measure α) measure.complete_semilattice_Inf],
        simp [] [] [] ["[", expr le_refl, ",", expr add_comm, ",", expr h_measure_sub_add, "]"] [] [] },
      apply [expr @le_Inf (measure α) measure.complete_semilattice_Inf],
      intros [ident d, ident h_d],
      rw ["[", "<-", expr h_measure_sub_add, ",", expr mem_set_of_eq, ",", expr add_comm d, "]"] ["at", ident h_d],
      apply [expr measure.le_of_add_le_add_left h_d] },
    rw [expr h_measure_sub_eq] [],
    apply [expr measure.of_measurable_apply _ h₁]
  end
end

theorem sub_add_cancel_of_le [is_finite_measure ν] (h₁ : ν ≤ μ) : ((μ - ν)+ν) = μ :=
  by 
    ext s h_s_meas 
    rw [add_apply, sub_apply h_s_meas h₁, tsub_add_cancel_of_le (h₁ s h_s_meas)]

theorem sub_le : μ - ν ≤ μ :=
  Inf_le (measure.le_add_right (le_reflₓ _))

end MeasureSub

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem restrict_sub_eq_restrict_sub_restrict
(h_meas_s : measurable_set s) : «expr = »(«expr - »(μ, ν).restrict s, «expr - »(μ.restrict s, ν.restrict s)) :=
begin
  repeat { rw [expr sub_def] [] },
  have [ident h_nonempty] [":", expr {d | «expr ≤ »(μ, «expr + »(d, ν))}.nonempty] [],
  { apply [expr @set.nonempty_of_mem _ _ μ],
    rw [expr mem_set_of_eq] [],
    intros [ident t, ident h_meas],
    exact [expr le_self_add] },
  rw [expr restrict_Inf_eq_Inf_restrict h_nonempty h_meas_s] [],
  apply [expr le_antisymm],
  { apply [expr @Inf_le_Inf_of_forall_exists_le (measure α) _],
    intros [ident ν', ident h_ν'_in],
    rw [expr mem_set_of_eq] ["at", ident h_ν'_in],
    apply [expr exists.intro (ν'.restrict s)],
    split,
    { rw [expr mem_image] [],
      apply [expr exists.intro «expr + »(ν', («expr⊤»() : measure_theory.measure α).restrict «expr ᶜ»(s))],
      rw [expr mem_set_of_eq] [],
      split,
      { rw ["[", expr add_assoc, ",", expr add_comm _ ν, ",", "<-", expr add_assoc, ",", expr measure_theory.measure.le_iff, "]"] [],
        intros [ident t, ident h_meas_t],
        have [ident h_inter_inter_eq_inter] [":", expr ∀
         t' : set α, «expr = »(«expr ∩ »(«expr ∩ »(t, t'), t'), «expr ∩ »(t, t'))] [],
        { intro [ident t'],
          rw [expr set.inter_eq_self_of_subset_left] [],
          apply [expr set.inter_subset_right t t'] },
        have [ident h_meas_t_inter_s] [":", expr measurable_set «expr ∩ »(t, s)] [":=", expr h_meas_t.inter h_meas_s],
        repeat { rw ["<-", expr measure_inter_add_diff t h_meas_s] [],
          rw [expr set.diff_eq] [] },
        refine [expr add_le_add _ _],
        { rw [expr add_apply] [],
          apply [expr le_add_right _],
          rw [expr add_apply] [],
          rw ["<-", expr @restrict_eq_self _ _ μ s _ h_meas_t_inter_s (set.inter_subset_right _ _)] [],
          rw ["<-", expr @restrict_eq_self _ _ ν s _ h_meas_t_inter_s (set.inter_subset_right _ _)] [],
          apply [expr h_ν'_in _ h_meas_t_inter_s] },
        cases [expr @set.eq_empty_or_nonempty _ «expr ∩ »(t, «expr ᶜ»(s))] ["with", ident h_inter_empty, ident h_inter_nonempty],
        { simp [] [] [] ["[", expr h_inter_empty, "]"] [] [] },
        { rw [expr add_apply] [],
          have [ident h_meas_inter_compl] [] [":=", expr h_meas_t.inter (measurable_set.compl h_meas_s)],
          rw ["[", expr restrict_apply h_meas_inter_compl, ",", expr h_inter_inter_eq_inter «expr ᶜ»(s), "]"] [],
          have [ident h_mu_le_add_top] [":", expr «expr ≤ »(μ, «expr + »(«expr + »(ν', ν), «expr⊤»()))] [],
          { rw [expr add_comm] [],
            have [ident h_le_top] [":", expr «expr ≤ »(μ, «expr⊤»())] [":=", expr le_top],
            apply [expr λ t₂ h_meas, le_add_right (h_le_top t₂ h_meas)] },
          apply [expr h_mu_le_add_top _ h_meas_inter_compl] } },
      { ext1 [] [ident t, ident h_meas_t],
        simp [] [] [] ["[", expr restrict_apply h_meas_t, ",", expr restrict_apply (h_meas_t.inter h_meas_s), ",", expr set.inter_assoc, "]"] [] [] } },
    { apply [expr restrict_le_self] } },
  { apply [expr @Inf_le_Inf_of_forall_exists_le (measure α) _],
    intros [ident s, ident h_s_in],
    cases [expr h_s_in] ["with", ident t, ident h_t],
    cases [expr h_t] ["with", ident h_t_in, ident h_t_eq],
    subst [expr s],
    apply [expr exists.intro (t.restrict s)],
    split,
    { rw ["[", expr set.mem_set_of_eq, ",", "<-", expr restrict_add, "]"] [],
      apply [expr restrict_mono (set.subset.refl _) h_t_in] },
    { apply [expr le_refl _] } }
end

theorem sub_apply_eq_zero_of_restrict_le_restrict (h_le : μ.restrict s ≤ ν.restrict s) (h_meas_s : MeasurableSet s) :
  (μ - ν) s = 0 :=
  by 
    rw [←restrict_apply_self _ h_meas_s, restrict_sub_eq_restrict_sub_restrict, sub_eq_zero_of_le]
    repeat' 
      simp 

instance is_finite_measure_sub [is_finite_measure μ] : is_finite_measure (μ - ν) :=
  { measure_univ_lt_top := lt_of_le_of_ltₓ (measure.sub_le Set.Univ MeasurableSet.univ) (measure_lt_top _ _) }

end Measureₓ

end MeasureTheory

open MeasureTheory MeasureTheory.Measure

namespace MeasurableEmbedding

variable{m0 : MeasurableSpace α}{m1 : MeasurableSpace β}{f : α → β}(hf : MeasurableEmbedding f)

include hf

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_apply (μ : measure α) (s : set β) : «expr = »(map f μ s, μ «expr ⁻¹' »(f, s)) :=
begin
  refine [expr le_antisymm _ (le_map_apply hf.measurable s)],
  set [] [ident t] [] [":="] [expr «expr ∪ »(«expr '' »(f, to_measurable μ «expr ⁻¹' »(f, s)), «expr ᶜ»(range f))] [],
  have [ident htm] [":", expr measurable_set t] [],
  from [expr «expr $ »(hf.measurable_set_image.2, measurable_set_to_measurable _ _).union hf.measurable_set_range.compl],
  have [ident hst] [":", expr «expr ⊆ »(s, t)] [],
  { rw ["[", expr subset_union_compl_iff_inter_subset, ",", "<-", expr image_preimage_eq_inter_range, "]"] [],
    exact [expr image_subset _ (subset_to_measurable _ _)] },
  have [ident hft] [":", expr «expr = »(«expr ⁻¹' »(f, t), to_measurable μ «expr ⁻¹' »(f, s))] [],
  by rw ["[", expr preimage_union, ",", expr preimage_compl, ",", expr preimage_range, ",", expr compl_univ, ",", expr union_empty, ",", expr hf.injective.preimage_image, "]"] [],
  calc
    «expr ≤ »(map f μ s, map f μ t) : measure_mono hst
    «expr = »(..., μ «expr ⁻¹' »(f, s)) : by rw ["[", expr map_apply hf.measurable htm, ",", expr hft, ",", expr measure_to_measurable, "]"] []
end

theorem map_comap (μ : Measureₓ β) : map f (comap f μ) = μ.restrict (range f) :=
  by 
    ext1 t ht 
    rw [hf.map_apply, comap_apply f hf.injective hf.measurable_set_image' _ (hf.measurable ht),
      image_preimage_eq_inter_range, restrict_apply ht]

theorem comap_apply (μ : Measureₓ β) (s : Set α) : comap f μ s = μ (f '' s) :=
  calc comap f μ s = comap f μ (f ⁻¹' (f '' s)) :=
    by 
      rw [hf.injective.preimage_image]
    _ = map f (comap f μ) (f '' s) := (hf.map_apply _ _).symm 
    _ = μ (f '' s) :=
    by 
      rw [hf.map_comap, restrict_apply' hf.measurable_set_range, inter_eq_self_of_subset_left (image_subset_range _ _)]
    

theorem ae_map_iff {p : β → Prop} {μ : Measureₓ α} : (∀ᵐx ∂map f μ, p x) ↔ ∀ᵐx ∂μ, p (f x) :=
  by 
    simp only [ae_iff, hf.map_apply, preimage_set_of_eq]

theorem restrict_map (μ : Measureₓ α) (s : Set β) : (map f μ).restrict s = map f (μ.restrict$ f ⁻¹' s) :=
  measure.ext$
    fun t ht =>
      by 
        simp [hf.map_apply, ht, hf.measurable ht]

end MeasurableEmbedding

section Subtype

theorem comap_subtype_coe_apply {m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) (μ : Measureₓ α)
  (t : Set s) : comap coeₓ μ t = μ (coeₓ '' t) :=
  (MeasurableEmbedding.subtype_coe hs).comap_apply _ _

theorem map_comap_subtype_coe {m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s) (μ : Measureₓ α) :
  map (coeₓ : s → α) (comap coeₓ μ) = μ.restrict s :=
  by 
    rw [(MeasurableEmbedding.subtype_coe hs).map_comap, Subtype.range_coe]

theorem ae_restrict_iff_subtype {m0 : MeasurableSpace α} {μ : Measureₓ α} {s : Set α} (hs : MeasurableSet s)
  {p : α → Prop} : (∀ᵐx ∂μ.restrict s, p x) ↔ ∀ᵐx ∂comap (coeₓ : s → α) μ, p («expr↑ » x) :=
  by 
    rw [←map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).ae_map_iff]

variable[measure_space α]

/-!
### Volume on `s : set α`
-/


instance _root_.set_coe.measure_space (s : Set α) : measure_space s :=
  ⟨comap (coeₓ : s → α) volume⟩

theorem volume_set_coe_def (s : Set α) : (volume : Measureₓ s) = comap (coeₓ : s → α) volume :=
  rfl

theorem MeasurableSet.map_coe_volume {s : Set α} (hs : MeasurableSet s) :
  map (coeₓ : s → α) volume = restrict volume s :=
  by 
    rw [volume_set_coe_def, (MeasurableEmbedding.subtype_coe hs).map_comap volume, Subtype.range_coe]

theorem volume_image_subtype_coe {s : Set α} (hs : MeasurableSet s) (t : Set s) :
  volume (coeₓ '' t : Set α) = volume t :=
  (comap_subtype_coe_apply hs volume t).symm

end Subtype

namespace MeasurableEquiv

/-! Interactions of measurable equivalences and measures -/


open Equiv MeasureTheory.Measure

variable[MeasurableSpace α][MeasurableSpace β]{μ : Measureₓ α}{ν : Measureₓ β}

/-- If we map a measure along a measurable equivalence, we can compute the measure on all sets
  (not just the measurable ones). -/
protected theorem map_apply (f : α ≃ᵐ β) (s : Set β) : map f μ s = μ (f ⁻¹' s) :=
  f.measurable_embedding.map_apply _ _

@[simp]
theorem map_symm_map (e : α ≃ᵐ β) : map e.symm (map e μ) = μ :=
  by 
    simp [map_map e.symm.measurable e.measurable]

@[simp]
theorem map_map_symm (e : α ≃ᵐ β) : map e (map e.symm ν) = ν :=
  by 
    simp [map_map e.measurable e.symm.measurable]

theorem map_measurable_equiv_injective (e : α ≃ᵐ β) : injective (map e) :=
  by 
    intro μ₁ μ₂ hμ 
    applyFun map e.symm  at hμ 
    simpa [map_symm_map e] using hμ

theorem map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : map e μ = ν ↔ map e.symm ν = μ :=
  by 
    rw [←(map_measurable_equiv_injective e).eq_iff, map_map_symm, eq_comm]

theorem restrict_map (e : α ≃ᵐ β) (s : Set β) : (map e μ).restrict s = map e (μ.restrict$ e ⁻¹' s) :=
  e.measurable_embedding.restrict_map _ _

end MeasurableEquiv

namespace MeasureTheory

theorem outer_measure.to_measure_zero [MeasurableSpace α] :
  (0 : outer_measure α).toMeasure (le_top.trans outer_measure.zero_caratheodory.symm.le) = 0 :=
  by 
    rw [←measure.measure_univ_eq_zero, to_measure_apply _ _ MeasurableSet.univ, outer_measure.coe_zero, Pi.zero_apply]

section Trim

/-- Restriction of a measure to a sub-sigma algebra.
It is common to see a measure `μ` on a measurable space structure `m0` as being also a measure on
any `m ≤ m0`. Since measures in mathlib have to be trimmed to the measurable space, `μ` itself
cannot be a measure on `m`, hence the definition of `μ.trim hm`.

This notion is related to `outer_measure.trim`, see the lemma
`to_outer_measure_trim_eq_trim_to_outer_measure`. -/
def measure.trim {m m0 : MeasurableSpace α} (μ : @Measureₓ α m0) (hm : m ≤ m0) : @Measureₓ α m :=
  @outer_measure.to_measure α m μ.to_outer_measure (hm.trans (le_to_outer_measure_caratheodory μ))

@[simp]
theorem trim_eq_self [MeasurableSpace α] {μ : Measureₓ α} : μ.trim le_rfl = μ :=
  by 
    simp [measure.trim]

variable{m m0 : MeasurableSpace α}{μ : Measureₓ α}{s : Set α}

theorem to_outer_measure_trim_eq_trim_to_outer_measure (μ : Measureₓ α) (hm : m ≤ m0) :
  @measure.to_outer_measure _ m (μ.trim hm) = @outer_measure.trim _ m μ.to_outer_measure :=
  by 
    rw [measure.trim, to_measure_to_outer_measure]

@[simp]
theorem zero_trim (hm : m ≤ m0) : (0 : Measureₓ α).trim hm = (0 : @Measureₓ α m) :=
  by 
    simp [measure.trim, outer_measure.to_measure_zero]

theorem trim_measurable_set_eq (hm : m ≤ m0) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s :=
  by 
    simp [measure.trim, hs]

theorem le_trim (hm : m ≤ m0) : μ s ≤ μ.trim hm s :=
  by 
    simpRw [measure.trim]
    exact @le_to_measure_apply _ m _ _ _

theorem measure_eq_zero_of_trim_eq_zero (hm : m ≤ m0) (h : μ.trim hm s = 0) : μ s = 0 :=
  le_antisymmₓ ((le_trim hm).trans (le_of_eqₓ h)) (zero_le _)

theorem measure_trim_to_measurable_eq_zero {hm : m ≤ m0} (hs : μ.trim hm s = 0) :
  μ (@to_measurable α m (μ.trim hm) s) = 0 :=
  measure_eq_zero_of_trim_eq_zero hm
    (by 
      rwa [measure_to_measurable])

theorem ae_eq_of_ae_eq_trim {E} {hm : m ≤ m0} {f₁ f₂ : α → E} (h12 : f₁ =ᶠ[@measure.ae α m (μ.trim hm)] f₂) :
  f₁ =ᵐ[μ] f₂ :=
  measure_eq_zero_of_trim_eq_zero hm h12

theorem restrict_trim (hm : m ≤ m0) (μ : Measureₓ α) (hs : @MeasurableSet α m s) :
  @measure.restrict α m (μ.trim hm) s = (μ.restrict s).trim hm :=
  by 
    ext1 t ht 
    rw [@measure.restrict_apply α m _ _ _ ht, trim_measurable_set_eq hm ht, measure.restrict_apply (hm t ht),
      trim_measurable_set_eq hm (@MeasurableSet.inter α m t s ht hs)]

instance is_finite_measure_trim (hm : m ≤ m0) [is_finite_measure μ] : is_finite_measure (μ.trim hm) :=
  { measure_univ_lt_top :=
      by 
        rw [trim_measurable_set_eq hm (@MeasurableSet.univ _ m)]
        exact measure_lt_top _ _ }

end Trim

end MeasureTheory

open_locale MeasureTheory

/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. This property, called `ae_measurable f μ`, is defined in the file `measure_space_def`.
We discuss several of its properties that are analogous to properties of measurable functions.
-/


section 

open MeasureTheory

variable[MeasurableSpace α][MeasurableSpace β]{f g : α → β}{μ ν : Measureₓ α}

@[nontriviality, measurability]
theorem Subsingleton.ae_measurable [Subsingleton α] : AeMeasurable f μ :=
  Subsingleton.measurable.AeMeasurable

@[nontriviality, measurability]
theorem ae_measurable_of_subsingleton_codomain [Subsingleton β] : AeMeasurable f μ :=
  (measurable_of_subsingleton_codomain f).AeMeasurable

@[simp, measurability]
theorem ae_measurable_zero_measure : AeMeasurable f (0 : Measureₓ α) :=
  by 
    nontriviality α 
    inhabit α 
    exact ⟨fun x => f (default α), measurable_const, rfl⟩

namespace AeMeasurable

theorem mono_measure (h : AeMeasurable f μ) (h' : ν ≤ μ) : AeMeasurable f ν :=
  ⟨h.mk f, h.measurable_mk, eventually.filter_mono (ae_mono h') h.ae_eq_mk⟩

theorem mono_set {s t} (h : s ⊆ t) (ht : AeMeasurable f (μ.restrict t)) : AeMeasurable f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)

protected theorem mono' (h : AeMeasurable f μ) (h' : ν ≪ μ) : AeMeasurable f ν :=
  ⟨h.mk f, h.measurable_mk, h' h.ae_eq_mk⟩

theorem ae_mem_imp_eq_mk {s} (h : AeMeasurable f (μ.restrict s)) : ∀ᵐx ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk

theorem ae_inf_principal_eq_mk {s} (h : AeMeasurable f (μ.restrict s)) : f =ᶠ[μ.ae⊓𝓟 s] h.mk f :=
  le_ae_restrict h.ae_eq_mk

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[measurability #[]]
theorem sum_measure [encodable ι] {μ : ι → measure α} (h : ∀ i, ae_measurable f (μ i)) : ae_measurable f (sum μ) :=
begin
  nontriviality [expr β] [],
  inhabit [expr β] [],
  set [] [ident s] [":", expr ι → set α] [":="] [expr λ i, to_measurable (μ i) {x | «expr ≠ »(f x, (h i).mk f x)}] [],
  have [ident hsμ] [":", expr ∀ i, «expr = »(μ i (s i), 0)] [],
  { intro [ident i],
    rw [expr measure_to_measurable] [],
    exact [expr (h i).ae_eq_mk] },
  have [ident hsm] [":", expr measurable_set «expr⋂ , »((i), s i)] [],
  from [expr measurable_set.Inter (λ i, measurable_set_to_measurable _ _)],
  have [ident hs] [":", expr ∀ i x, «expr ∉ »(x, s i) → «expr = »(f x, (h i).mk f x)] [],
  { intros [ident i, ident x, ident hx],
    contrapose ["!"] [ident hx],
    exact [expr subset_to_measurable _ _ hx] },
  set [] [ident g] [":", expr α → β] [":="] [expr «expr⋂ , »((i), s i).piecewise (const α (default β)) f] [],
  refine [expr ⟨g, measurable_of_restrict_of_restrict_compl hsm _ _, «expr $ »(ae_sum_iff.mpr, λ i, _)⟩],
  { rw ["[", expr restrict_piecewise, "]"] [],
    simp [] [] ["only"] ["[", expr set.restrict, ",", expr const, "]"] [] [],
    exact [expr measurable_const] },
  { rw ["[", expr restrict_piecewise_compl, ",", expr compl_Inter, "]"] [],
    intros [ident t, ident ht],
    refine [expr ⟨«expr⋃ , »((i), «expr ∩ »(«expr ⁻¹' »((h i).mk f, t), «expr ᶜ»(s i))), «expr $ »(measurable_set.Union, λ
       i, (measurable_mk _ ht).inter (measurable_set_to_measurable _ _).compl), _⟩],
    ext [] ["⟨", ident x, ",", ident hx, "⟩"] [],
    simp [] [] ["only"] ["[", expr mem_preimage, ",", expr mem_Union, ",", expr subtype.coe_mk, ",", expr set.restrict, ",", expr mem_inter_eq, ",", expr mem_compl_iff, "]"] [] ["at", ident hx, "⊢"],
    split,
    { rintro ["⟨", ident i, ",", ident hxt, ",", ident hxs, "⟩"],
      rwa [expr hs _ _ hxs] [] },
    { rcases [expr hx, "with", "⟨", ident i, ",", ident hi, "⟩"],
      rw [expr hs _ _ hi] [],
      exact [expr λ h, ⟨i, h, hi⟩] } },
  { refine [expr measure_mono_null (λ (x) (hx : «expr ≠ »(f x, g x)), _) (hsμ i)],
    contrapose ["!"] [ident hx],
    refine [expr (piecewise_eq_of_not_mem _ _ _ _).symm],
    exact [expr λ h, hx (mem_Inter.1 h i)] }
end

@[simp]
theorem _root_.ae_measurable_sum_measure_iff [Encodable ι] {μ : ι → Measureₓ α} :
  AeMeasurable f (Sum μ) ↔ ∀ i, AeMeasurable f (μ i) :=
  ⟨fun h i => h.mono_measure (le_sum _ _), sum_measure⟩

@[simp]
theorem _root_.ae_measurable_add_measure_iff : AeMeasurable f (μ+ν) ↔ AeMeasurable f μ ∧ AeMeasurable f ν :=
  by 
    rw [←sum_cond, ae_measurable_sum_measure_iff, Bool.forall_bool, And.comm]
    rfl

@[measurability]
theorem add_measure {f : α → β} (hμ : AeMeasurable f μ) (hν : AeMeasurable f ν) : AeMeasurable f (μ+ν) :=
  ae_measurable_add_measure_iff.2 ⟨hμ, hν⟩

@[measurability]
protected theorem Union [Encodable ι] {s : ι → Set α} (h : ∀ i, AeMeasurable f (μ.restrict (s i))) :
  AeMeasurable f (μ.restrict (⋃i, s i)) :=
  (sum_measure h).mono_measure$ restrict_Union_le

@[simp]
theorem _root_.ae_measurable_Union_iff [Encodable ι] {s : ι → Set α} :
  AeMeasurable f (μ.restrict (⋃i, s i)) ↔ ∀ i, AeMeasurable f (μ.restrict (s i)) :=
  ⟨fun h i => h.mono_measure$ restrict_mono (subset_Union _ _) le_rfl, AeMeasurable.Union⟩

@[measurability]
theorem smul_measure (h : AeMeasurable f μ) (c : ℝ≥0∞) : AeMeasurable f (c • μ) :=
  ⟨h.mk f, h.measurable_mk, ae_smul_measure h.ae_eq_mk c⟩

theorem comp_measurable [MeasurableSpace δ] {f : α → δ} {g : δ → β} (hg : AeMeasurable g (map f μ))
  (hf : Measurable f) : AeMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ f, hg.measurable_mk.comp hf, ae_eq_comp hf hg.ae_eq_mk⟩

theorem comp_measurable' {δ} [MeasurableSpace δ] {ν : Measureₓ δ} {f : α → δ} {g : δ → β} (hg : AeMeasurable g ν)
  (hf : Measurable f) (h : map f μ ≪ ν) : AeMeasurable (g ∘ f) μ :=
  (hg.mono' h).comp_measurable hf

@[measurability]
theorem prod_mk {γ : Type _} [MeasurableSpace γ] {f : α → β} {g : α → γ} (hf : AeMeasurable f μ)
  (hg : AeMeasurable g μ) : AeMeasurable (fun x => (f x, g x)) μ :=
  ⟨fun a => (hf.mk f a, hg.mk g a), hf.measurable_mk.prod_mk hg.measurable_mk,
    eventually_eq.prod_mk hf.ae_eq_mk hg.ae_eq_mk⟩

theorem subtype_mk (h : AeMeasurable f μ) {s : Set β} {hfs : ∀ x, f x ∈ s} (hs : MeasurableSet s) :
  AeMeasurable (cod_restrict f s hfs) μ :=
  by 
    nontriviality α 
    inhabit α 
    rcases h with ⟨g, hgm, hg⟩
    rcases hs.exists_measurable_proj ⟨f (default α), hfs _⟩ with ⟨π, hπm, hπ⟩
    refine' ⟨π ∘ g, hπm.comp hgm, hg.mono$ fun x hx => _⟩
    rw [comp_apply, ←hx, ←coe_cod_restrict_apply f s hfs, hπ]

protected theorem null_measurable (h : AeMeasurable f μ) : null_measurable f μ :=
  let ⟨g, hgm, hg⟩ := h 
  hgm.null_measurable.congr hg.symm

end AeMeasurable

theorem ae_measurable_iff_measurable [μ.is_complete] : AeMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.null_measurable.measurable_of_complete, fun h => h.ae_measurable⟩

theorem MeasurableEmbedding.ae_measurable_map_iff [MeasurableSpace γ] {f : α → β} (hf : MeasurableEmbedding f)
  {μ : Measureₓ α} {g : β → γ} : AeMeasurable g (map f μ) ↔ AeMeasurable (g ∘ f) μ :=
  by 
    refine' ⟨fun H => H.comp_measurable hf.measurable, _⟩
    rintro ⟨g₁, hgm₁, heq⟩
    rcases hf.exists_measurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
    exact ⟨g₂, hgm₂, hf.ae_map_iff.2 HEq⟩

theorem MeasurableEmbedding.ae_measurable_comp_iff [MeasurableSpace γ] {g : β → γ} (hg : MeasurableEmbedding g)
  {μ : Measureₓ α} {f : α → β} : AeMeasurable (g ∘ f) μ ↔ AeMeasurable f μ :=
  by 
    refine' ⟨fun H => _, hg.measurable.comp_ae_measurable⟩
    suffices  : AeMeasurable ((range_splitting g ∘ range_factorization g) ∘ f) μ
    ·
      rwa [(right_inverse_range_splitting hg.injective).comp_eq_id] at this 
    exact hg.measurable_range_splitting.comp_ae_measurable (H.subtype_mk hg.measurable_set_range)

theorem ae_measurable_restrict_iff_comap_subtype {s : Set α} (hs : MeasurableSet s) {μ : Measureₓ α} {f : α → β} :
  AeMeasurable f (μ.restrict s) ↔ AeMeasurable (f ∘ coeₓ : s → β) (comap coeₓ μ) :=
  by 
    rw [←map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).ae_measurable_map_iff]

@[simp, toAdditive]
theorem ae_measurable_one [HasOne β] : AeMeasurable (fun a : α => (1 : β)) μ :=
  measurable_one.AeMeasurable

@[simp]
theorem ae_measurable_smul_measure_iff {c : ℝ≥0∞} (hc : c ≠ 0) : AeMeasurable f (c • μ) ↔ AeMeasurable f μ :=
  ⟨fun h => ⟨h.mk f, h.measurable_mk, (ae_smul_measure_iff hc).1 h.ae_eq_mk⟩,
    fun h => ⟨h.mk f, h.measurable_mk, (ae_smul_measure_iff hc).2 h.ae_eq_mk⟩⟩

theorem ae_measurable_of_ae_measurable_trim {α} {m m0 : MeasurableSpace α} {μ : Measureₓ α} (hm : m ≤ m0) {f : α → β}
  (hf : AeMeasurable f (μ.trim hm)) : AeMeasurable f μ :=
  ⟨hf.mk f, Measurable.mono hf.measurable_mk hm le_rfl, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩

theorem ae_measurable_restrict_of_measurable_subtype {s : Set α} (hs : MeasurableSet s)
  (hf : Measurable fun x : s => f x) : AeMeasurable f (μ.restrict s) :=
  (ae_measurable_restrict_iff_comap_subtype hs).2 hf.ae_measurable

theorem ae_measurable_map_equiv_iff [MeasurableSpace γ] (e : α ≃ᵐ β) {f : β → γ} :
  AeMeasurable f (map e μ) ↔ AeMeasurable (f ∘ e) μ :=
  e.measurable_embedding.ae_measurable_map_iff

end 

namespace IsCompact

variable[TopologicalSpace α][MeasurableSpace α]{μ : Measureₓ α}{s : Set α}

/-- If `s` is a compact set and `μ` is finite at `𝓝 x` for every `x ∈ s`, then `s` admits an open
superset of finite measure. -/
theorem exists_open_superset_measure_lt_top' (h : IsCompact s) (hμ : ∀ x _ : x ∈ s, μ.finite_at_filter (𝓝 x)) :
  ∃ (U : _)(_ : U ⊇ s), IsOpen U ∧ μ U < ∞ :=
  by 
    refine' IsCompact.induction_on h _ _ _ _
    ·
      use ∅
      simp [Superset]
    ·
      rintro s t hst ⟨U, htU, hUo, hU⟩
      exact ⟨U, hst.trans htU, hUo, hU⟩
    ·
      rintro s t ⟨U, hsU, hUo, hU⟩ ⟨V, htV, hVo, hV⟩
      refine'
        ⟨U ∪ V, union_subset_union hsU htV, hUo.union hVo,
          (measure_union_le _ _).trans_lt$ Ennreal.add_lt_top.2 ⟨hU, hV⟩⟩
    ·
      intro x hx 
      rcases(hμ x hx).exists_mem_basis (nhds_basis_opens _) with ⟨U, ⟨hx, hUo⟩, hU⟩
      exact ⟨U, nhds_within_le_nhds (hUo.mem_nhds hx), U, subset.rfl, hUo, hU⟩

/-- If `s` is a compact set and `μ` is a locally finite measure, then `s` admits an open superset of
finite measure. -/
theorem exists_open_superset_measure_lt_top (h : IsCompact s) (μ : Measureₓ α) [is_locally_finite_measure μ] :
  ∃ (U : _)(_ : U ⊇ s), IsOpen U ∧ μ U < ∞ :=
  h.exists_open_superset_measure_lt_top'$ fun x hx => μ.finite_at_nhds x

theorem measure_lt_top_of_nhds_within (h : IsCompact s) (hμ : ∀ x _ : x ∈ s, μ.finite_at_filter (𝓝[s] x)) : μ s < ∞ :=
  IsCompact.induction_on h
    (by 
      simp )
    (fun s t hst ht => (measure_mono hst).trans_lt ht)
    (fun s t hs ht => (measure_union_le s t).trans_lt (Ennreal.add_lt_top.2 ⟨hs, ht⟩)) hμ

theorem measure_lt_top (h : IsCompact s) {μ : Measureₓ α} [is_locally_finite_measure μ] : μ s < ∞ :=
  h.measure_lt_top_of_nhds_within$ fun x hx => μ.finite_at_nhds_within _ _

theorem measure_zero_of_nhds_within (hs : IsCompact s) :
  (∀ a _ : a ∈ s, ∃ (t : _)(_ : t ∈ 𝓝[s] a), μ t = 0) → μ s = 0 :=
  by 
    simpa only [←compl_mem_ae_iff] using hs.compl_mem_sets_of_nhds_within

end IsCompact

/-- Compact covering of a `σ`-compact topological space as
`measure_theory.measure.finite_spanning_sets_in`. -/
def MeasureTheory.Measure.finiteSpanningSetsInCompact [TopologicalSpace α] [SigmaCompactSpace α] {m : MeasurableSpace α}
  (μ : Measureₓ α) [is_locally_finite_measure μ] : μ.finite_spanning_sets_in { K | IsCompact K } :=
  { Set := CompactCovering α, set_mem := is_compact_compact_covering α,
    Finite := fun n => (is_compact_compact_covering α n).measure_lt_top, spanning := Union_compact_covering α }

/-- A locally finite measure on a `σ`-compact topological space admits a finite spanning sequence
of open sets. -/
def MeasureTheory.Measure.finiteSpanningSetsInOpen [TopologicalSpace α] [SigmaCompactSpace α] {m : MeasurableSpace α}
  (μ : Measureₓ α) [is_locally_finite_measure μ] : μ.finite_spanning_sets_in { K | IsOpen K } :=
  { Set := fun n => ((is_compact_compact_covering α n).exists_open_superset_measure_lt_top μ).some,
    set_mem := fun n => ((is_compact_compact_covering α n).exists_open_superset_measure_lt_top μ).some_spec.snd.1,
    Finite := fun n => ((is_compact_compact_covering α n).exists_open_superset_measure_lt_top μ).some_spec.snd.2,
    spanning :=
      eq_univ_of_subset
        (Union_subset_Union$
          fun n => ((is_compact_compact_covering α n).exists_open_superset_measure_lt_top μ).some_spec.fst)
        (Union_compact_covering α) }

section MeasureIxx

variable[ConditionallyCompleteLinearOrder
      α][TopologicalSpace
      α][OrderTopology α]{m : MeasurableSpace α}{μ : Measureₓ α}[is_locally_finite_measure μ]{a b : α}

theorem measure_Icc_lt_top : μ (Icc a b) < ∞ :=
  is_compact_Icc.measure_lt_top

theorem measure_Ico_lt_top : μ (Ico a b) < ∞ :=
  (measure_mono Ico_subset_Icc_self).trans_lt measure_Icc_lt_top

theorem measure_Ioc_lt_top : μ (Ioc a b) < ∞ :=
  (measure_mono Ioc_subset_Icc_self).trans_lt measure_Icc_lt_top

theorem measure_Ioo_lt_top : μ (Ioo a b) < ∞ :=
  (measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top

end MeasureIxx

theorem Metric.Bounded.measure_lt_top [MetricSpace α] [ProperSpace α] [MeasurableSpace α] {μ : Measureₓ α}
  [is_locally_finite_measure μ] {s : Set α} (hs : Metric.Bounded s) : μ s < ∞ :=
  (measure_mono subset_closure).trans_lt
    (Metric.compact_iff_closed_bounded.2 ⟨is_closed_closure, Metric.bounded_closure_of_bounded hs⟩).measure_lt_top

section Piecewise

variable[MeasurableSpace α]{μ : Measureₓ α}{s t : Set α}{f g : α → β}

theorem piecewise_ae_eq_restrict (hs : MeasurableSet s) : piecewise s f g =ᵐ[μ.restrict s] f :=
  by 
    rw [ae_restrict_eq hs]
    exact (piecewise_eq_on s f g).EventuallyEq.filter_mono inf_le_right

theorem piecewise_ae_eq_restrict_compl (hs : MeasurableSet s) : piecewise s f g =ᵐ[μ.restrict («expr ᶜ» s)] g :=
  by 
    rw [ae_restrict_eq hs.compl]
    exact (piecewise_eq_on_compl s f g).EventuallyEq.filter_mono inf_le_right

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem piecewise_ae_eq_of_ae_eq_set
(hst : «expr =ᵐ[ ] »(s, μ, t)) : «expr =ᵐ[ ] »(s.piecewise f g, μ, t.piecewise f g) :=
begin
  filter_upwards ["[", expr hst, "]"] [],
  intros [ident x, ident hx],
  replace [ident hx] [":", expr «expr ↔ »(«expr ∈ »(x, s), «expr ∈ »(x, t))] [":=", expr iff_of_eq hx],
  by_cases [expr h, ":", expr «expr ∈ »(x, s)]; have [ident h'] [] [":=", expr h]; rw [expr hx] ["at", ident h']; simp [] [] [] ["[", expr h, ",", expr h', "]"] [] []
end

end Piecewise

section IndicatorFunction

variable[MeasurableSpace α]{μ : Measureₓ α}{s t : Set α}{f : α → β}

theorem mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem [HasZero β] {t : Set β} (ht : (0 : β) ∈ t)
  (hs : MeasurableSet s) : t ∈ Filter.map (s.indicator f) μ.ae ↔ t ∈ Filter.map f (μ.restrict s).ae :=
  by 
    simpRw [mem_map, mem_ae_iff]
    rw [measure.restrict_apply' hs, Set.indicator_preimage, Set.Ite]
    simpRw [Set.compl_union, Set.compl_inter]
    change
      μ ((«expr ᶜ» (f ⁻¹' t) ∪ «expr ᶜ» s) ∩ «expr ᶜ» ((fun x => (0 : β)) ⁻¹' t \ s)) = 0 ↔
        μ («expr ᶜ» (f ⁻¹' t) ∩ s) = 0
    simp only [ht, ←Set.compl_eq_univ_diff, compl_compl, Set.compl_union, if_true, Set.preimage_const]
    simpRw [Set.union_inter_distrib_right, Set.compl_inter_self s, Set.union_empty]

theorem mem_map_indicator_ae_iff_of_zero_nmem [HasZero β] {t : Set β} (ht : (0 : β) ∉ t) :
  t ∈ Filter.map (s.indicator f) μ.ae ↔ μ («expr ᶜ» (f ⁻¹' t) ∪ «expr ᶜ» s) = 0 :=
  by 
    rw [mem_map, mem_ae_iff, Set.indicator_preimage, Set.Ite, Set.compl_union, Set.compl_inter]
    change
      μ ((«expr ᶜ» (f ⁻¹' t) ∪ «expr ᶜ» s) ∩ «expr ᶜ» ((fun x => (0 : β)) ⁻¹' t \ s)) = 0 ↔
        μ («expr ᶜ» (f ⁻¹' t) ∪ «expr ᶜ» s) = 0
    simp only [ht, if_false, Set.compl_empty, Set.empty_diff, Set.inter_univ, Set.preimage_const]

theorem map_restrict_ae_le_map_indicator_ae [HasZero β] (hs : MeasurableSet s) :
  Filter.map f (μ.restrict s).ae ≤ Filter.map (s.indicator f) μ.ae :=
  by 
    intro t 
    byCases' ht : (0 : β) ∈ t
    ·
      rw [mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem ht hs]
      exact id 
    rw [mem_map_indicator_ae_iff_of_zero_nmem ht, mem_map_restrict_ae_iff hs]
    exact fun h => measure_mono_null ((Set.inter_subset_left _ _).trans (Set.subset_union_left _ _)) h

theorem AeMeasurable.restrict [MeasurableSpace β] (hfm : AeMeasurable f μ) {s} : AeMeasurable f (μ.restrict s) :=
  ⟨AeMeasurable.mk f hfm, hfm.measurable_mk, ae_restrict_of_ae hfm.ae_eq_mk⟩

variable[HasZero β]

theorem indicator_ae_eq_restrict (hs : MeasurableSet s) : indicator s f =ᵐ[μ.restrict s] f :=
  piecewise_ae_eq_restrict hs

theorem indicator_ae_eq_restrict_compl (hs : MeasurableSet s) : indicator s f =ᵐ[μ.restrict («expr ᶜ» s)] 0 :=
  piecewise_ae_eq_restrict_compl hs

theorem indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.indicator f =ᵐ[μ] t.indicator f :=
  piecewise_ae_eq_of_ae_eq_set hst

variable[MeasurableSpace β]

-- error in MeasureTheory.Measure.MeasureSpace: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_measurable_indicator_iff
{s}
(hs : measurable_set s) : «expr ↔ »(ae_measurable (indicator s f) μ, ae_measurable f (μ.restrict s)) :=
begin
  split,
  { assume [binders (h)],
    exact [expr (h.mono_measure measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)] },
  { assume [binders (h)],
    refine [expr ⟨indicator s (h.mk f), h.measurable_mk.indicator hs, _⟩],
    have [ident A] [":", expr «expr =ᵐ[ ] »(s.indicator f, μ.restrict s, s.indicator (ae_measurable.mk f h))] [":=", expr (indicator_ae_eq_restrict hs).trans «expr $ »(h.ae_eq_mk.trans, (indicator_ae_eq_restrict hs).symm)],
    have [ident B] [":", expr «expr =ᵐ[ ] »(s.indicator f, μ.restrict «expr ᶜ»(s), s.indicator (ae_measurable.mk f h))] [":=", expr (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm],
    exact [expr ae_of_ae_restrict_of_ae_restrict_compl A B] }
end

@[measurability]
theorem AeMeasurable.indicator (hfm : AeMeasurable f μ) {s} (hs : MeasurableSet s) : AeMeasurable (s.indicator f) μ :=
  (ae_measurable_indicator_iff hs).mpr hfm.restrict

end IndicatorFunction

