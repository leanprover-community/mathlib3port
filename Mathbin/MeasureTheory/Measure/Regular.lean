import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Regular measures

A measure is `outer_regular` if the measure of any measurable set `A` is the infimum of `μ U` over
all open sets `U` containing `A`.

A measure is `regular` if it satisfies the following properties:
* it is finite on compact sets;
* it is outer regular;
* it is inner regular for open sets with respect to compacts sets: the measure of any open set `U`
  is the supremum of `μ K` over all compact sets `K` contained in `U`.

A measure is `weakly_regular` if it satisfies the following properties:
* it is outer regular;
* it is inner regular for open sets with respect to closed sets: the measure of any open set `U`
  is the supremum of `μ F` over all compact sets `F` contained in `U`.

In a Hausdorff topological space, regularity implies weak regularity. These three conditions are
registered as typeclasses for a measure `μ`, and this implication is recorded as an instance.

In order to avoid code duplication, we also define a measure `μ` to be `inner_regular` for sets
satisfying a predicate `q` with respect to sets satisfying a predicate `p` if for any set
`U ∈ {U | q U}` and a number `r < μ U` there exists `F ⊆ U` such that `p F` and `r < μ F`.

We prove that inner regularity for open sets with respect to compact sets or closed sets implies
inner regularity for all measurable sets of finite measure (with respect to
compact sets or closed sets respectively), and register some corollaries for (weakly) regular
measures.

Note that a similar statement for measurable sets of infinite mass can fail. For a counterexample,
consider the group `ℝ × ℝ` where the first factor has the discrete topology and the second one the
usual topology. It is a locally compact Hausdorff topological group, with Haar measure equal to
Lebesgue measure on each vertical fiber. The set `ℝ × {0}` has infinite measure (by outer
regularity), but any compact set it contains has zero measure (as it is finite).

Several authors require as a definition of regularity that all measurable sets are inner regular.
We have opted for the slightly weaker definition above as it holds for all Haar measures, it is
enough for essentially all applications, and it is equivalent to the other definition when the
measure is finite.

The interest of the notion of weak regularity is that it is enough for many applications, and it
is automatically satisfied by any finite measure on a metric space.

## Main definitions

* `measure_theory.measure.outer_regular μ`: a typeclass registering that a measure `μ` on a
  topological space is outer regular.
* `measure_theory.measure.regular μ`: a typeclass registering that a measure `μ` on a topological
  space is regular.
* `measure_theory.measure.weakly_regular μ`: a typeclass registering that a measure `μ` on a
  topological space is weakly regular.
* `measure_theory.measure.inner_regular μ p q`: a non-typeclass predicate saying that a measure `μ`
  is inner regular for sets satisfying `q` with respect to sets satisfying `p`.

## Main results

### Outer regular measures

* `set.measure_eq_infi_is_open` asserts that, when `μ` is outer regular, the measure of a
  set is the infimum of the measure of open sets containing it.
* `set.exists_is_open_lt_of_lt'` asserts that, when `μ` is outer regular, for every set `s`
  and `r > μ s` there exists an open superset `U ⊇ s` of measure less than `r`.
* push forward of an outer regular measure is outer regular, and scalar multiplication of a regular
  measure by a finite number is outer regular.
* `measure_theory.measure.outer_regular.of_sigma_compact_space_of_is_locally_finite_measure`:
  a locally finite measure on a `σ`-compact metric (or even pseudo emetric) space is outer regular.

### Weakly regular measures

* `is_open.measure_eq_supr_is_closed` asserts that the measure of an open set is the supremum of
  the measure of closed sets it contains.
* `is_open.exists_lt_is_closed`: for an open set `U` and `r < μ U`, there exists a closed `F ⊆ U`
  of measure greater than `r`;
* `measurable_set.measure_eq_supr_is_closed_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of closed sets it contains.
*  `measurable_set.exists_lt_is_closed_of_ne_top` and `measurable_set.exists_is_closed_lt_add`:
  a measurable set of finite measure can be approximated by a closed subset (stated as
  `r < μ F` and `μ s < μ F + ε`, respectively).
* `measure_theory.measure.weakly_regular.of_pseudo_emetric_space_of_is_finite_measure` is an
  instance registering that a finite measure on a metric space is weakly regular (in fact, a pseudo
  emetric space is enough);
* `measure_theory.measure.weakly_regular.of_pseudo_emetric_sigma_compact_space_of_locally_finite`
  is an instance registering that a locally finite measure on a `σ`-compact metric space (or even
  a pseudo emetric space) is weakly regular.

### Regular measures

* `is_open.measure_eq_supr_is_compact` asserts that the measure of an open set is the supremum of
  the measure of compact sets it contains.
* `is_open.exists_lt_is_compact`: for an open set `U` and `r < μ U`, there exists a compact `K ⊆ U`
  of measure greater than `r`;
* `measurable_set.measure_eq_supr_is_compact_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of compact sets it contains.
*  `measurable_set.exists_lt_is_compact_of_ne_top` and `measurable_set.exists_is_compact_lt_add`:
  a measurable set of finite measure can be approximated by a compact subset (stated as
  `r < μ K` and `μ s < μ K + ε`, respectively).
* `measure_theory.measure.regular.of_sigma_compact_space_of_is_locally_finite_measure` is an
  instance registering that a locally finite measure on a `σ`-compact metric space is regular (in
  fact, an emetric space is enough).

## Implementation notes

The main nontrivial statement is `measure_theory.measure.inner_regular.weakly_regular_of_finite`,
expressing that in a finite measure space, if every open set can be approximated from inside by
closed sets, then the measure is in fact weakly regular. To prove that we show that any measurable
set can be approximated from inside by closed sets and from outside by open sets. This statement is
proved by measurable induction, starting from open sets and checking that it is stable by taking
complements (this is the point of this condition, being symmetrical between inside and outside) and
countable disjoint unions.

Once this statement is proved, one deduces results for `σ`-finite measures from this statement, by
restricting them to finite measure sets (and proving that this restriction is weakly regular, using
again the same statement).

## References

[Halmos, Measure Theory, §52][halmos1950measure]. Note that Halmos uses an unusual definition of
Borel sets (for him, they are elements of the `σ`-algebra generated by compact sets!), so his
proofs or statements do not apply directly.

[Billingsley, Convergence of Probability Measures][billingsley1999]
-/


open Set Filter

open_locale Ennreal TopologicalSpace Nnreal BigOperators

namespace MeasureTheory

namespace Measureₓ

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » U)
/-- We say that a measure `μ` is *inner regular* with respect to predicates `p q : set α → Prop`,
if for every `U` such that `q U` and `r < μ U`, there exists a subset `K ⊆ U` satisfying `p K`
of measure greater than `r`.

This definition is used to prove some facts about regular and weakly regular measures without
repeating the proofs. -/
def inner_regular {α} {m : MeasurableSpace α} (μ : Measureₓ α) (p q : Set α → Prop) :=
  ∀ ⦃U⦄, q U → ∀, ∀ r < μ U, ∀, ∃ (K : _)(_ : K ⊆ U), p K ∧ r < μ K

namespace InnerRegular

variable {α : Type _} {m : MeasurableSpace α} {μ : Measureₓ α} {p q : Set α → Prop} {U : Set α} {ε : ℝ≥0∞}

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » U)
theorem measure_eq_supr (H : inner_regular μ p q) (hU : q U) : μ U = ⨆ (K) (_ : K ⊆ U) (hK : p K), μ K := by
  refine' le_antisymmₓ (le_of_forall_lt fun r hr => _) (bsupr_le $ fun K hK => supr_le $ fun _ => μ.mono hK)
  simpa only [lt_supr_iff, exists_prop] using H hU r hr

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » U)
theorem exists_subset_lt_add (H : inner_regular μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U ≠ ∞) (hε : ε ≠ 0) :
    ∃ (K : _)(_ : K ⊆ U), p K ∧ μ U < μ K + ε := by
  cases' eq_or_ne (μ U) 0 with h₀ h₀
  · refine' ⟨∅, empty_subset _, h0, _⟩
    rwa [measure_empty, h₀, zero_addₓ, pos_iff_ne_zero]
    
  · rcases H hU _ (Ennreal.sub_lt_self hμU h₀ hε) with ⟨K, hKU, hKc, hrK⟩
    exact ⟨K, hKU, hKc, Ennreal.lt_add_of_sub_lt (Or.inl hμU) hrK⟩
    

theorem map {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measureₓ α} {pa qa : Set α → Prop}
    (H : inner_regular μ pa qa) (f : α ≃ β) (hf : Measurable f) {pb qb : Set β → Prop} (hAB : ∀ U, qb U → qa (f ⁻¹' U))
    (hAB' : ∀ K, pa K → pb (f '' K)) (hB₁ : ∀ K, pb K → MeasurableSet K) (hB₂ : ∀ U, qb U → MeasurableSet U) :
    inner_regular (map f μ) pb qb := by
  intro U hU r hr
  rw [map_apply hf (hB₂ _ hU)] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine' ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, _⟩
  rwa [map_apply hf (hB₁ _ $ hAB' _ hKc), f.preimage_image]

theorem smul (H : inner_regular μ p q) (c : ℝ≥0∞) : inner_regular (c • μ) p q := by
  intro U hU r hr
  rw [smul_apply, H.measure_eq_supr hU] at hr
  simpa only [Ennreal.mul_supr, lt_supr_iff, exists_prop] using hr

theorem trans {q' : Set α → Prop} (H : inner_regular μ p q) (H' : inner_regular μ q q') : inner_regular μ p q' := by
  intro U hU r hr
  rcases H' hU r hr with ⟨F, hFU, hqF, hF⟩
  rcases H hqF _ hF with ⟨K, hKF, hpK, hrK⟩
  exact ⟨K, hKF.trans hFU, hpK, hrK⟩

end InnerRegular

variable {α β : Type _} [MeasurableSpace α] [TopologicalSpace α] {μ : Measureₓ α}

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (U «expr ⊇ » A)
/-- A measure `μ` is outer regular if `μ(A) = inf {μ(U) | A ⊆ U open}` for a measurable set `A`.

This definition implies the same equality for any (not necessarily measurable) set, see
`set.measure_eq_infi_is_open`. -/
@[protect_proj]
class outer_regular (μ : Measureₓ α) : Prop where
  OuterRegular : ∀ ⦃A : Set α⦄, MeasurableSet A → ∀, ∀ r > μ A, ∀, ∃ (U : _)(_ : U ⊇ A), IsOpen U ∧ μ U < r

/-- A measure `μ` is regular if
  - it is finite on all compact sets;
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using compact sets:
    `μ(U) = sup {μ(K) | K ⊆ U compact}` for `U` open. -/
@[protect_proj]
class regular (μ : Measureₓ α) extends is_finite_measure_on_compacts μ, outer_regular μ : Prop where
  InnerRegular : inner_regular μ IsCompact IsOpen

/-- A measure `μ` is weakly regular if
  - it is outer regular: `μ(A) = inf {μ(U) | A ⊆ U open}` for `A` measurable;
  - it is inner regular for open sets, using closed sets:
    `μ(U) = sup {μ(F) | F ⊆ U compact}` for `U` open. -/
@[protect_proj]
class weakly_regular (μ : Measureₓ α) extends outer_regular μ : Prop where
  InnerRegular : inner_regular μ IsClosed IsOpen

/-- A regular measure is weakly regular. -/
instance (priority := 100) regular.weakly_regular [T2Space α] [regular μ] : weakly_regular μ where
  InnerRegular := fun U hU r hr =>
    let ⟨K, hKU, hcK, hK⟩ := regular.inner_regular hU r hr
    ⟨K, hKU, hcK.is_closed, hK⟩

namespace OuterRegular

instance zero : outer_regular (0 : Measureₓ α) :=
  ⟨fun A hA r hr => ⟨univ, subset_univ A, is_open_univ, hr⟩⟩

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (U «expr ⊇ » A)
/-- Given `r` larger than the measure of a set `A`, there exists an open superset of `A` with
measure less than `r`. -/
theorem _root_.set.exists_is_open_lt_of_lt [outer_regular μ] (A : Set α) (r : ℝ≥0∞) (hr : μ A < r) :
    ∃ (U : _)(_ : U ⊇ A), IsOpen U ∧ μ U < r := by
  rcases outer_regular.outer_regular (measurable_set_to_measurable μ A) r
      (by
        rwa [measure_to_measurable]) with
    ⟨U, hAU, hUo, hU⟩
  exact ⟨U, (subset_to_measurable _ _).trans hAU, hUo, hU⟩

/-- For an outer regular measure, the measure of a set is the infimum of the measures of open sets
containing it. -/
theorem _root_.set.measure_eq_infi_is_open (A : Set α) (μ : Measureₓ α) [outer_regular μ] :
    μ A = ⨅ (U : Set α) (h : A ⊆ U) (h2 : IsOpen U), μ U := by
  refine' le_antisymmₓ (le_binfi $ fun s hs => le_infi $ fun h2s => μ.mono hs) _
  refine' le_of_forall_lt' fun r hr => _
  simpa only [infi_lt_iff, exists_prop] using A.exists_is_open_lt_of_lt r hr

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (U «expr ⊇ » A)
theorem _root_.set.exists_is_open_lt_add [outer_regular μ] (A : Set α) (hA : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (U : _)(_ : U ⊇ A), IsOpen U ∧ μ U < μ A + ε :=
  A.exists_is_open_lt_of_lt _ (Ennreal.lt_add_right hA hε)

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (U «expr ⊇ » A)
theorem _root_.set.exists_is_open_le_add (A : Set α) (μ : Measureₓ α) [outer_regular μ] {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (U : _)(_ : U ⊇ A), IsOpen U ∧ μ U ≤ μ A + ε := by
  rcases le_or_ltₓ ∞ (μ A) with (H | H)
  · exact
      ⟨univ, subset_univ _, is_open_univ, by
        simp only [top_le_iff.mp H, Ennreal.top_add, le_top]⟩
    
  · rcases A.exists_is_open_lt_add H.ne hε with ⟨U, AU, U_open, hU⟩
    exact ⟨U, AU, U_open, hU.le⟩
    

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (U «expr ⊇ » A)
theorem _root_.measurable_set.exists_is_open_diff_lt [outer_regular μ] {A : Set α} (hA : MeasurableSet A)
    (hA' : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ (U : _)(_ : U ⊇ A), IsOpen U ∧ μ U < ∞ ∧ μ (U \ A) < ε := by
  rcases A.exists_is_open_lt_add hA' hε with ⟨U, hAU, hUo, hU⟩
  use U, hAU, hUo, hU.trans_le le_top
  exact measure_diff_lt_of_lt_add hA hAU hA' hU

protected theorem map [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β] [BorelSpace β] (f : α ≃ₜ β)
    (μ : Measureₓ α) [outer_regular μ] : (measure.map f μ).OuterRegular := by
  refine' ⟨fun A hA r hr => _⟩
  rw [map_apply f.measurable hA, ← f.image_symm] at hr
  rcases Set.exists_is_open_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩
  have : IsOpen (f.symm ⁻¹' U) := hUo.preimage f.symm.continuous
  refine' ⟨f.symm ⁻¹' U, image_subset_iff.1 hAU, this, _⟩
  rwa [map_apply f.measurable this.measurable_set, f.preimage_symm, f.preimage_image]

protected theorem smul (μ : Measureₓ α) [outer_regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) : (x • μ).OuterRegular := by
  rcases eq_or_ne x 0 with (rfl | h0)
  · rw [zero_smul]
    exact outer_regular.zero
    
  · refine' ⟨fun A hA r hr => _⟩
    rw [smul_apply, A.measure_eq_infi_is_open] at hr
    simpa only [Ennreal.mul_infi_of_ne h0 hx, gt_iff_lt, infi_lt_iff, exists_prop] using hr
    

end OuterRegular

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (U «expr ⊇ » A n)
/-- If a measure `μ` admits finite spanning open sets such that the restriction of `μ` to each set
is outer regular, then the original measure is outer regular as well. -/
protected theorem finite_spanning_sets_in.outer_regular [OpensMeasurableSpace α] {μ : Measureₓ α}
    (s : μ.finite_spanning_sets_in { U | IsOpen U ∧ outer_regular (μ.restrict U) }) : outer_regular μ := by
  refine' ⟨fun A hA r hr => _⟩
  have hm : ∀ n, MeasurableSet (s.set n) := fun n => (s.set_mem n).1.MeasurableSet
  have : ∀ n, outer_regular (μ.restrict (s.set n)) := fun n => (s.set_mem n).2
  obtain ⟨A, hAm, hAs, hAd, rfl⟩ :
    ∃ A' : ℕ → Set α, (∀ n, MeasurableSet (A' n)) ∧ (∀ n, A' n ⊆ s.set n) ∧ Pairwise (Disjoint on A') ∧ A = ⋃ n, A' n :=
    by
    refine'
      ⟨fun n => A ∩ disjointed s.set n, fun n => hA.inter (MeasurableSet.disjointed hm _), fun n =>
        (inter_subset_right _ _).trans (disjointed_subset _ _),
        (disjoint_disjointed s.set).mono fun k l hkl => hkl.mono inf_le_right inf_le_right, _⟩
    rw [← inter_Union, Union_disjointed, s.spanning, inter_univ]
  rcases Ennreal.exists_pos_sum_of_encodable' (tsub_pos_iff_lt.2 hr).ne' ℕ with ⟨δ, δ0, hδε⟩
  rw [lt_tsub_iff_right, add_commₓ] at hδε
  have : ∀ n, ∃ (U : _)(_ : U ⊇ A n), IsOpen U ∧ μ U < μ (A n) + δ n := by
    intro n
    have H₁ : ∀ t, μ.restrict (s.set n) t = μ (t ∩ s.set n) := fun t => restrict_apply' (hm n)
    have Ht : μ.restrict (s.set n) (A n) ≠ ⊤ := by
      rw [H₁]
      exact ((measure_mono $ inter_subset_right _ _).trans_lt (s.finite n)).Ne
    rcases(A n).exists_is_open_lt_add Ht (δ0 n).ne' with ⟨U, hAU, hUo, hU⟩
    rw [H₁, H₁, inter_eq_self_of_subset_left (hAs _)] at hU
    exact ⟨U ∩ s.set n, subset_inter hAU (hAs _), hUo.inter (s.set_mem n).1, hU⟩
  choose U hAU hUo hU
  refine' ⟨⋃ n, U n, Union_subset_Union hAU, is_open_Union hUo, _⟩
  calc μ (⋃ n, U n) ≤ ∑' n, μ (U n) := measure_Union_le _ _ ≤ ∑' n, μ (A n) + δ n :=
      Ennreal.tsum_le_tsum fun n => (hU n).le _ = (∑' n, μ (A n)) + ∑' n, δ n :=
      Ennreal.tsum_add _ = μ (⋃ n, A n) + ∑' n, δ n := congr_arg2ₓ (· + ·) (measure_Union hAd hAm).symm rfl _ < r := hδε

namespace InnerRegular

variable {p q : Set α → Prop} {U s : Set α} {ε r : ℝ≥0∞}

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (ε «expr ≠ » 0)
/-- If a measure is inner regular (using closed or compact sets), then every measurable set of
finite measure can by approximated by a (closed or compact) subset. -/
theorem measurable_set_of_open [outer_regular μ] (H : inner_regular μ p IsOpen) (h0 : p ∅)
    (hd : ∀ ⦃s U⦄, p s → IsOpen U → p (s \ U)) : inner_regular μ p fun s => MeasurableSet s ∧ μ s ≠ ∞ := by
  rintro s ⟨hs, hμs⟩ r hr
  obtain ⟨ε, hε, hεs, rfl⟩ : ∃ (ε : _)(_ : ε ≠ 0), ε + ε ≤ μ s ∧ r = μ s - (ε + ε) := by
    use (μ s - r) / 2
    simp [*, hr.le, Ennreal.add_halves, Ennreal.sub_sub_cancel, le_add_right]
  rcases hs.exists_is_open_diff_lt hμs hε with ⟨U, hsU, hUo, hUt, hμU⟩
  rcases(U \ s).exists_is_open_lt_of_lt _ hμU with ⟨U', hsU', hU'o, hμU'⟩
  replace hsU' := diff_subset_comm.1 hsU'
  rcases H.exists_subset_lt_add h0 hUo hUt.ne hε with ⟨K, hKU, hKc, hKr⟩
  refine' ⟨K \ U', fun x hx => hsU' ⟨hKU hx.1, hx.2⟩, hd hKc hU'o, Ennreal.sub_lt_of_lt_add hεs _⟩
  calc μ s ≤ μ U := μ.mono hsU _ < μ K + ε := hKr _ ≤ μ (K \ U') + μ U' + ε :=
      add_le_add_right (tsub_le_iff_right.1 le_measure_diff) _ _ ≤ μ (K \ U') + ε + ε := by
      mono*
      exacts[hμU'.le, le_rfl]_ = μ (K \ U') + (ε + ε) := add_assocₓ _ _ _

open Finset

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (ε «expr ≠ » 0)
-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (F «expr ⊆ » s)
-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (U «expr ⊇ » s)
/-- In a finite measure space, assume that any open set can be approximated from inside by closed
sets. Then the measure is weakly regular. -/
theorem weakly_regular_of_finite [BorelSpace α] (μ : Measureₓ α) [is_finite_measure μ]
    (H : inner_regular μ IsClosed IsOpen) : weakly_regular μ := by
  have hfin : ∀ {s}, μ s ≠ ⊤ := measure_ne_top μ
  suffices
    ∀ s,
      MeasurableSet s →
        ∀ ε _ : ε ≠ 0, ∃ (F : _)(_ : F ⊆ s)(U : _)(_ : U ⊇ s), IsClosed F ∧ IsOpen U ∧ μ s ≤ μ F + ε ∧ μ U ≤ μ s + ε
    by
    refine' { OuterRegular := fun s hs r hr => _, InnerRegular := H }
    rcases exists_between hr with ⟨r', hsr', hr'r⟩
    rcases this s hs _ (tsub_pos_iff_lt.2 hsr').ne' with ⟨-, -, U, hsU, -, hUo, -, H⟩
    refine' ⟨U, hsU, hUo, _⟩
    rw [add_tsub_cancel_of_le hsr'.le] at H
    exact H.trans_lt hr'r
  refine' MeasurableSet.induction_on_open _ _ _
  · intro U hU ε hε
    rcases H.exists_subset_lt_add is_closed_empty hU hfin hε with ⟨F, hsF, hFc, hF⟩
    exact ⟨F, hsF, U, subset.rfl, hFc, hU, hF.le, le_self_add⟩
    
  · rintro s hs H ε hε
    rcases H ε hε with ⟨F, hFs, U, hsU, hFc, hUo, hF, hU⟩
    refine' ⟨Uᶜ, compl_subset_compl.2 hsU, Fᶜ, compl_subset_compl.2 hFs, hUo.is_closed_compl, hFc.is_open_compl, _⟩
    simp only [measure_compl_le_add_iff, *, hUo.measurable_set, hFc.measurable_set, true_andₓ]
    
  · intro s hsd hsm H ε ε0
    have ε0' : ε / 2 ≠ 0 := (Ennreal.half_pos ε0).ne'
    rcases Ennreal.exists_pos_sum_of_encodable' ε0' ℕ with ⟨δ, δ0, hδε⟩
    choose F hFs U hsU hFc hUo hF hU using fun n => H n (δ n) (δ0 n).ne'
    have : tendsto (fun t => (∑ k in t, μ (s k)) + ε / 2) at_top (𝓝 $ μ (⋃ n, s n) + ε / 2) := by
      rw [measure_Union hsd hsm]
      exact tendsto.add ennreal.summable.has_sum tendsto_const_nhds
    rcases(this.eventually $ lt_mem_nhds $ Ennreal.lt_add_right hfin ε0').exists with ⟨t, ht⟩
    refine'
      ⟨⋃ k ∈ t, F k, Union_subset_Union $ fun k => Union_subset $ fun _ => hFs _, ⋃ n, U n, Union_subset_Union hsU,
        is_closed_bUnion t.finite_to_set $ fun k _ => hFc k, is_open_Union hUo, ht.le.trans _, _⟩
    · calc (∑ k in t, μ (s k)) + ε / 2 ≤ ((∑ k in t, μ (F k)) + ∑ k in t, δ k) + ε / 2 := by
          rw [← sum_add_distrib]
          exact add_le_add_right (sum_le_sum $ fun k hk => hF k) _ _ ≤ (∑ k in t, μ (F k)) + ε / 2 + ε / 2 :=
          add_le_add_right (add_le_add_left ((Ennreal.sum_le_tsum _).trans hδε.le) _) _ _ = μ (⋃ k ∈ t, F k) + ε := _
      rw [measure_bUnion_finset, add_assocₓ, Ennreal.add_halves]
      exacts[fun k _ n _ hkn => (hsd k n hkn).mono (hFs k) (hFs n), fun k hk => (hFc k).MeasurableSet]
      
    · calc μ (⋃ n, U n) ≤ ∑' n, μ (U n) := measure_Union_le _ _ ≤ ∑' n, μ (s n) + δ n :=
          Ennreal.tsum_le_tsum hU _ = μ (⋃ n, s n) + ∑' n, δ n := by
          rw [measure_Union hsd hsm, Ennreal.tsum_add]_ ≤ μ (⋃ n, s n) + ε :=
          add_le_add_left (hδε.le.trans Ennreal.half_le_self) _
      
    

/-- In a metric space (or even a pseudo emetric space), an open set can be approximated from inside
by closed sets. -/
theorem of_pseudo_emetric_space {X : Type _} [PseudoEmetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measureₓ X) : inner_regular μ IsClosed IsOpen := by
  intro U hU r hr
  rcases hU.exists_Union_is_closed with ⟨F, F_closed, -, rfl, F_mono⟩
  rw [measure_Union_eq_supr (fun n => (F_closed n).MeasurableSet) F_mono.directed_le] at hr
  rcases lt_supr_iff.1 hr with ⟨n, hn⟩
  exact ⟨F n, subset_Union _ _, F_closed n, hn⟩

/-- In a `σ`-compact space, any closed set can be approximated by a compact subset. -/
theorem is_compact_is_closed {X : Type _} [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measureₓ X) : inner_regular μ IsCompact IsClosed := by
  intro F hF r hr
  set B : ℕ → Set X := CompactCovering X
  have hBc : ∀ n, IsCompact (F ∩ B n) := fun n => (is_compact_compact_covering X n).inter_left hF
  have hBU : (⋃ n, F ∩ B n) = F := by
    rw [← inter_Union, Union_compact_covering, Set.inter_univ]
  have : μ F = ⨆ n, μ (F ∩ B n) := by
    rw [← measure_Union_eq_supr, hBU]
    exacts[fun n => (hBc n).MeasurableSet,
      Monotone.directed_le $ fun m n h => inter_subset_inter_right _ (compact_covering_subset _ h)]
  rw [this] at hr
  rcases lt_supr_iff.1 hr with ⟨n, hn⟩
  exact ⟨_, inter_subset_left _ _, hBc n, hn⟩

end InnerRegular

namespace Regular

instance zero : regular (0 : Measureₓ α) :=
  ⟨fun U hU r hr => ⟨∅, empty_subset _, is_compact_empty, hr⟩⟩

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » U)
/-- If `μ` is a regular measure, then any open set can be approximated by a compact subset. -/
theorem _root_.is_open.exists_lt_is_compact [regular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : ℝ≥0∞} (hr : r < μ U) :
    ∃ (K : _)(_ : K ⊆ U), IsCompact K ∧ r < μ K :=
  regular.inner_regular hU r hr

/-- The measure of an open set is the supremum of the measures of compact sets it contains. -/
theorem _root_.is_open.measure_eq_supr_is_compact ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measureₓ α) [regular μ] :
    μ U = ⨆ (K : Set α) (h : K ⊆ U) (h2 : IsCompact K), μ K :=
  regular.inner_regular.measure_eq_supr hU

theorem exists_compact_not_null [regular μ] : (∃ K, IsCompact K ∧ μ K ≠ 0) ↔ μ ≠ 0 := by
  simp_rw [Ne.def, ← measure_univ_eq_zero, is_open_univ.measure_eq_supr_is_compact, Ennreal.supr_eq_zero, not_forall,
    exists_prop, subset_univ, true_andₓ]

/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `measurable_set.exists_is_compact_lt_add` and
`measurable_set.exists_lt_is_compact_of_ne_top`. -/
theorem inner_regular_measurable [regular μ] : inner_regular μ IsCompact fun s => MeasurableSet s ∧ μ s ≠ ∞ :=
  regular.inner_regular.measurable_set_of_open is_compact_empty fun _ _ => IsCompact.diff

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » A)
/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `measurable_set.exists_lt_is_compact_of_ne_top`. -/
theorem _root_.measurable_set.exists_is_compact_lt_add [regular μ] ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ (K : _)(_ : K ⊆ A), IsCompact K ∧ μ A < μ K + ε :=
  regular.inner_regular_measurable.exists_subset_lt_add is_compact_empty ⟨hA, h'A⟩ h'A hε

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » A)
/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `measurable_set.exists_is_compact_lt_add` and
`measurable_set.exists_lt_is_compact_of_ne_top`. -/
theorem _root_.measurable_set.exists_is_compact_diff_lt [OpensMeasurableSpace α] [T2Space α] [regular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (K : _)(_ : K ⊆ A), IsCompact K ∧ μ (A \ K) < ε := by
  rcases hA.exists_is_compact_lt_add h'A hε with ⟨K, hKA, hKc, hK⟩
  exact ⟨K, hKA, hKc, measure_diff_lt_of_lt_add hKc.measurable_set hKA (ne_top_of_le_ne_top h'A $ measure_mono hKA) hK⟩

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » A)
/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `measurable_set.exists_is_compact_lt_add`. -/
theorem _root_.measurable_set.exists_lt_is_compact_of_ne_top [regular μ] ⦃A : Set α⦄ (hA : MeasurableSet A)
    (h'A : μ A ≠ ∞) {r : ℝ≥0∞} (hr : r < μ A) : ∃ (K : _)(_ : K ⊆ A), IsCompact K ∧ r < μ K :=
  regular.inner_regular_measurable ⟨hA, h'A⟩ _ hr

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » A)
/-- Given a regular measure, any measurable set of finite mass can be approximated from
inside by compact sets. -/
theorem _root_.measurable_set.measure_eq_supr_is_compact_of_ne_top [regular μ] ⦃A : Set α⦄ (hA : MeasurableSet A)
    (h'A : μ A ≠ ∞) : μ A = ⨆ (K) (_ : K ⊆ A) (h : IsCompact K), μ K :=
  regular.inner_regular_measurable.measure_eq_supr ⟨hA, h'A⟩

protected theorem map [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β] [T2Space β] [BorelSpace β]
    [regular μ] (f : α ≃ₜ β) : (measure.map f μ).regular := by
  have := outer_regular.map f μ
  have := IsFiniteMeasureOnCompacts.map μ f
  exact
    ⟨regular.inner_regular.map f.to_equiv f.measurable (fun U hU => hU.preimage f.continuous)
        (fun K hK => hK.image f.continuous) (fun K hK => hK.measurable_set) fun U hU => hU.measurable_set⟩

protected theorem smul [regular μ] {x : ℝ≥0∞} (hx : x ≠ ∞) : (x • μ).regular := by
  have := outer_regular.smul μ hx
  have := is_finite_measure_on_compacts.smul μ hx
  exact ⟨regular.inner_regular.smul x⟩

/-- A regular measure in a σ-compact space is σ-finite. -/
instance (priority := 100) sigma_finite [SigmaCompactSpace α] [regular μ] : sigma_finite μ :=
  ⟨⟨{ Set := CompactCovering α, set_mem := fun n => trivialₓ,
        Finite := fun n => (is_compact_compact_covering α n).measure_lt_top, spanning := Union_compact_covering α }⟩⟩

end Regular

namespace WeaklyRegular

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (F «expr ⊆ » U)
/-- If `μ` is a weakly regular measure, then any open set can be approximated by a closed subset. -/
theorem _root_.is_open.exists_lt_is_closed [weakly_regular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : ℝ≥0∞} (hr : r < μ U) :
    ∃ (F : _)(_ : F ⊆ U), IsClosed F ∧ r < μ F :=
  weakly_regular.inner_regular hU r hr

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (F «expr ⊆ » U)
/-- If `μ` is a weakly regular measure, then any open set can be approximated by a closed subset. -/
theorem _root_.is_open.measure_eq_supr_is_closed ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measureₓ α) [weakly_regular μ] :
    μ U = ⨆ (F) (_ : F ⊆ U) (h : IsClosed F), μ F :=
  weakly_regular.inner_regular.measure_eq_supr hU

theorem inner_regular_measurable [weakly_regular μ] : inner_regular μ IsClosed fun s => MeasurableSet s ∧ μ s ≠ ∞ :=
  weakly_regular.inner_regular.measurable_set_of_open is_closed_empty fun _ _ h₁ h₂ => h₁.inter h₂.is_closed_compl

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » s)
/-- If `s` is a measurable set, a weakly regular measure `μ` is finite on `s`, and `ε` is a positive
number, then there exist a closed set `K ⊆ s` such that `μ s < μ K + ε`. -/
theorem _root_.measurable_set.exists_is_closed_lt_add [weakly_regular μ] {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ (K : _)(_ : K ⊆ s), IsClosed K ∧ μ s < μ K + ε :=
  inner_regular_measurable.exists_subset_lt_add is_closed_empty ⟨hs, hμs⟩ hμs hε

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (F «expr ⊆ » A)
theorem _root_.measurable_set.exists_is_closed_diff_lt [OpensMeasurableSpace α] [weakly_regular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ (F : _)(_ : F ⊆ A), IsClosed F ∧ μ (A \ F) < ε :=
  by
  rcases hA.exists_is_closed_lt_add h'A hε with ⟨F, hFA, hFc, hF⟩
  exact ⟨F, hFA, hFc, measure_diff_lt_of_lt_add hFc.measurable_set hFA (ne_top_of_le_ne_top h'A $ measure_mono hFA) hF⟩

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » A)
/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
theorem _root_.measurable_set.exists_lt_is_closed_of_ne_top [weakly_regular μ] ⦃A : Set α⦄ (hA : MeasurableSet A)
    (h'A : μ A ≠ ∞) {r : ℝ≥0∞} (hr : r < μ A) : ∃ (K : _)(_ : K ⊆ A), IsClosed K ∧ r < μ K :=
  inner_regular_measurable ⟨hA, h'A⟩ _ hr

-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (K «expr ⊆ » A)
/-- Given a weakly regular measure, any measurable set of finite mass can be approximated from
inside by closed sets. -/
theorem _root_.measurable_set.measure_eq_supr_is_closed_of_ne_top [weakly_regular μ] ⦃A : Set α⦄ (hA : MeasurableSet A)
    (h'A : μ A ≠ ∞) : μ A = ⨆ (K) (_ : K ⊆ A) (h : IsClosed K), μ K :=
  inner_regular_measurable.measure_eq_supr ⟨hA, h'A⟩

/-- The restriction of a weakly regular measure to a measurable set of finite measure is
weakly regular. -/
theorem restrict_of_measurable_set [BorelSpace α] [weakly_regular μ] (A : Set α) (hA : MeasurableSet A)
    (h'A : μ A ≠ ∞) : weakly_regular (μ.restrict A) := by
  have : Fact (μ A < ∞) := ⟨h'A.lt_top⟩
  refine' inner_regular.weakly_regular_of_finite _ fun V V_open => _
  simp only [restrict_apply' hA]
  intro r hr
  have : μ (V ∩ A) ≠ ∞ := ne_top_of_le_ne_top h'A (measure_mono $ inter_subset_right _ _)
  rcases(V_open.measurable_set.inter hA).exists_lt_is_closed_of_ne_top this hr with ⟨F, hFVA, hFc, hF⟩
  refine' ⟨F, hFVA.trans (inter_subset_left _ _), hFc, _⟩
  rwa [inter_eq_self_of_subset_left (hFVA.trans $ inter_subset_right _ _)]

/-- Any finite measure on a metric space (or even a pseudo emetric space) is weakly regular. -/
instance (priority := 100) of_pseudo_emetric_space_of_is_finite_measure {X : Type _} [PseudoEmetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measureₓ X) [is_finite_measure μ] : weakly_regular μ :=
  (inner_regular.of_pseudo_emetric_space μ).weakly_regular_of_finite μ

/-- Any locally finite measure on a `σ`-compact metric space (or even a pseudo emetric space) is
weakly regular. -/
instance (priority := 100) of_pseudo_emetric_sigma_compact_space_of_locally_finite {X : Type _} [PseudoEmetricSpace X]
    [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measureₓ X) [is_locally_finite_measure μ] :
    weakly_regular μ :=
  have : outer_regular μ := by
    refine' (μ.finite_spanning_sets_in_open.mono' $ fun U hU => _).OuterRegular
    have : Fact (μ U < ∞) := ⟨hU.2⟩
    exact ⟨hU.1, inferInstance⟩
  ⟨inner_regular.of_pseudo_emetric_space μ⟩

end WeaklyRegular

/-- Any locally finite measure on a `σ`-compact (e)metric space is regular. -/
instance (priority := 100) regular.of_sigma_compact_space_of_is_locally_finite_measure {X : Type _} [EmetricSpace X]
    [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measureₓ X) [is_locally_finite_measure μ] :
    regular μ where
  lt_top_of_is_compact := fun K hK => hK.measure_lt_top
  InnerRegular := (inner_regular.is_compact_is_closed μ).trans (inner_regular.of_pseudo_emetric_space μ)

end Measureₓ

end MeasureTheory

