import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Vitali families

On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets with
nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.

This file gives the basic definition of Vitali families. More interesting developments of this
notion are deferred to other files:
* constructions of specific Vitali families are provided by the Besicovitch covering theorem, in
`besicovitch.vitali_family`, and by the Vitali covering theorem, in `vitali.vitali_family`.
* The main theorem on differentiation of measures along a Vitali family is proved in
`vitali_family.ae_tendsto_rn_deriv`.

## Main definitions

* `vitali_family μ` is a structure made, for each `x : X`, of a family of sets around `x`, such that
one can extract an almost everywhere disjoint covering from any subfamily containing sets of
arbitrarily small diameters.

Let `v` be such a Vitali family.
* `v.fine_subfamily_on` describes the subfamilies of `v` from which one can extract almost
everywhere disjoint coverings. This property, called
`v.fine_subfamily_on.exists_disjoint_covering_ae`, is essentially a restatement of the definition
of a Vitali family. We also provide an API to use efficiently such a disjoint covering.
* `v.filter_at x` is a filter on sets of `X`, such that convergence with respect to this filter
means convergence when sets in the Vitali family shrink towards `x`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.8][Federer1996] (Vitali families are called
Vitali relations there)
-/


open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure

open_locale Filter MeasureTheory TopologicalSpace

variable{α : Type _}[MetricSpace α]

/-- On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets
with nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the
following property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
@[nolint has_inhabited_instance]
structure VitaliFamily{m : MeasurableSpace α}(μ : Measureₓ α) where 
  SetsAt : ∀ (x : α), Set (Set α)
  MeasurableSet' : ∀ (x : α), ∀ (a : Set α), a ∈ sets_at x → MeasurableSet a 
  nonempty_interior : ∀ (x : α), ∀ (y : Set α), y ∈ sets_at x → (Interior y).Nonempty 
  Nontrivial : ∀ (x : α) ε (_ : ε > (0 : ℝ)), ∃ (y : _)(_ : y ∈ sets_at x), y ⊆ closed_ball x ε 
  covering :
  ∀ (s : Set α) (f : ∀ (x : α), Set (Set α)),
    (∀ x (_ : x ∈ s), f x ⊆ sets_at x) →
      (∀ x (_ : x ∈ s) ε (_ : ε > (0 : ℝ)), ∃ (a : _)(_ : a ∈ f x), a ⊆ closed_ball x ε) →
        ∃ (t : Set α)(u : α → Set α),
          t ⊆ s ∧ t.pairwise_disjoint u ∧ (∀ x (_ : x ∈ t), u x ∈ f x) ∧ μ (s \ ⋃(x : _)(_ : x ∈ t), u x) = 0

namespace VitaliFamily

variable{m0 : MeasurableSpace α}{μ : Measureₓ α}

include μ

/-- A Vitali family for a measure `μ` is also a Vitali family for any measure absolutely continuous
with respect to `μ`. -/
def mono (v : VitaliFamily μ) (ν : Measureₓ α) (hν : ν ≪ μ) : VitaliFamily ν :=
  { SetsAt := v.sets_at, MeasurableSet' := v.measurable_set', nonempty_interior := v.nonempty_interior,
    Nontrivial := v.nontrivial,
    covering :=
      fun s f h h' =>
        by 
          rcases v.covering s f h h' with ⟨t, u, ts, u_disj, uf, μu⟩
          exact ⟨t, u, ts, u_disj, uf, hν μu⟩ }

/-- Given a Vitali family `v` for a measure `μ`, a family `f` is a fine subfamily on a set `s` if
every point `x` in `s` belongs to arbitrarily small sets in `v.sets_at x ∩ f x`. This is precisely
the subfamilies for which the Vitali family definition ensures that one can extract a disjoint
covering of almost all `s`. -/
def fine_subfamily_on (v : VitaliFamily μ) (f : α → Set (Set α)) (s : Set α) : Prop :=
  ∀ x (_ : x ∈ s), ∀ ε (_ : ε > 0), ∃ (a : _)(_ : a ∈ v.sets_at x ∩ f x), a ⊆ closed_ball x ε

namespace FineSubfamilyOn

variable{v : VitaliFamily μ}{f : α → Set (Set α)}{s : Set α}(h : v.fine_subfamily_on f s)

include h

theorem exists_disjoint_covering_ae :
  ∃ (t : Set α)(u : α → Set α),
    t ⊆ s ∧ t.pairwise_disjoint u ∧ (∀ x (_ : x ∈ t), u x ∈ v.sets_at x ∩ f x) ∧ μ (s \ ⋃(x : _)(_ : x ∈ t), u x) = 0 :=
  v.covering s (fun x => v.sets_at x ∩ f x) (fun x hx => inter_subset_left _ _) h

/-- Given `h : v.fine_subfamily_on f s`, then `h.index` is a subset of `s` parametrizing a disjoint
covering of almost every `s`. -/
protected def index : Set α :=
  h.exists_disjoint_covering_ae.some

/-- Given `h : v.fine_subfamily_on f s`, then `h.covering x` is a set in the family,
for `x ∈ h.index`, such that these sets form a disjoint covering of almost every `s`. -/
protected def covering : α → Set α :=
  h.exists_disjoint_covering_ae.some_spec.some

theorem index_subset : h.index ⊆ s :=
  h.exists_disjoint_covering_ae.some_spec.some_spec.1

theorem covering_disjoint : h.index.pairwise_disjoint h.covering :=
  h.exists_disjoint_covering_ae.some_spec.some_spec.2.1

-- error in MeasureTheory.Covering.VitaliFamily: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem covering_disjoint_subtype : pairwise «expr on »(disjoint, λ x : h.index, h.covering x) :=
(pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint

theorem covering_mem {x : α} (hx : x ∈ h.index) : h.covering x ∈ f x :=
  (h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.1 x hx).2

theorem covering_mem_family {x : α} (hx : x ∈ h.index) : h.covering x ∈ v.sets_at x :=
  (h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.1 x hx).1

theorem measure_diff_bUnion : μ (s \ ⋃(x : _)(_ : x ∈ h.index), h.covering x) = 0 :=
  h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.2

theorem index_countable [second_countable_topology α] : countable h.index :=
  h.covering_disjoint.countable_of_nonempty_interior fun x hx => v.nonempty_interior _ _ (h.covering_mem_family hx)

protected theorem measurable_set_u {x : α} (hx : x ∈ h.index) : MeasurableSet (h.covering x) :=
  v.measurable_set' x _ (h.covering_mem_family hx)

theorem measure_le_tsum_of_absolutely_continuous [second_countable_topology α] {ρ : Measureₓ α} (hρ : ρ ≪ μ) :
  ρ s ≤ ∑'x : h.index, ρ (h.covering x) :=
  calc ρ s ≤ ρ ((s \ ⋃(x : _)(_ : x ∈ h.index), h.covering x) ∪ ⋃(x : _)(_ : x ∈ h.index), h.covering x) :=
    measure_mono
      (by 
        simp only [subset_union_left, diff_union_self])
    _ ≤ ρ (s \ ⋃(x : _)(_ : x ∈ h.index), h.covering x)+ρ (⋃(x : _)(_ : x ∈ h.index), h.covering x) :=
    measure_union_le _ _ 
    _ = ∑'x : h.index, ρ (h.covering x) :=
    by 
      rw [hρ h.measure_diff_bUnion,
        measure_bUnion h.index_countable h.covering_disjoint fun x hx => h.measurable_set_u hx, zero_addₓ]
    

theorem measure_le_tsum [second_countable_topology α] : μ s ≤ ∑'x : h.index, μ (h.covering x) :=
  h.measure_le_tsum_of_absolutely_continuous measure.absolutely_continuous.rfl

end FineSubfamilyOn

variable(v : VitaliFamily μ)

include v

/-- Given a vitali family `v`, then `v.filter_at x` is the filter on `set α` made of those families
that contain all sets of `v.sets_at x` of a sufficiently small diameter. This filter makes it
possible to express limiting behavior when sets in `v.sets_at x` shrink to `x`. -/
def filter_at (x : α) : Filter (Set α) :=
  ⨅(ε : _)(_ : ε ∈ Ioi (0 : ℝ)), 𝓟 { a∈v.sets_at x | a ⊆ closed_ball x ε }

theorem mem_filter_at_iff {x : α} {s : Set (Set α)} :
  s ∈ v.filter_at x ↔ ∃ (ε : _)(_ : ε > (0 : ℝ)), ∀ a (_ : a ∈ v.sets_at x), a ⊆ closed_ball x ε → a ∈ s :=
  by 
    simp only [filter_at, exists_prop, gt_iff_lt]
    rw [mem_binfi_of_directed]
    ·
      simp only [subset_def, and_imp, exists_prop, mem_sep_eq, mem_Ioi, mem_principal]
    ·
      simp only [DirectedOn, exists_prop, ge_iff_le, le_principal_iff, mem_Ioi, Order.Preimage, mem_principal]
      intro x hx y hy 
      refine'
        ⟨min x y, lt_minₓ hx hy, fun a ha => ⟨ha.1, ha.2.trans (closed_ball_subset_closed_ball (min_le_leftₓ _ _))⟩,
          fun a ha => ⟨ha.1, ha.2.trans (closed_ball_subset_closed_ball (min_le_rightₓ _ _))⟩⟩
    ·
      exact ⟨(1 : ℝ), mem_Ioi.2 zero_lt_one⟩

instance filter_at_ne_bot (x : α) : (v.filter_at x).ne_bot :=
  by 
    simp only [ne_bot_iff, ←empty_mem_iff_bot, mem_filter_at_iff, not_exists, exists_prop, mem_empty_eq, and_trueₓ,
      gt_iff_lt, not_and, Ne.def, not_false_iff, not_forall]
    intro ε εpos 
    obtain ⟨w, w_sets, hw⟩ : ∃ (w : _)(_ : w ∈ v.sets_at x), w ⊆ closed_ball x ε := v.nontrivial x ε εpos 
    exact ⟨w, w_sets, hw⟩

theorem eventually_filter_at_iff {x : α} {P : Set α → Prop} :
  (∀ᶠa in v.filter_at x, P a) ↔ ∃ (ε : _)(_ : ε > (0 : ℝ)), ∀ a (_ : a ∈ v.sets_at x), a ⊆ closed_ball x ε → P a :=
  v.mem_filter_at_iff

-- error in MeasureTheory.Covering.VitaliFamily: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eventually_filter_at_mem_sets (x : α) : «expr∀ᶠ in , »((a), v.filter_at x, «expr ∈ »(a, v.sets_at x)) :=
begin
  simp [] [] ["only"] ["[", expr eventually_filter_at_iff, ",", expr exists_prop, ",", expr and_true, ",", expr gt_iff_lt, ",", expr implies_true_iff, "]"] [] [] { contextual := tt },
  exact [expr ⟨1, zero_lt_one⟩]
end

theorem frequently_filter_at_iff {x : α} {P : Set α → Prop} :
  (∃ᶠa in v.filter_at x, P a) ↔ ∀ ε (_ : ε > (0 : ℝ)), ∃ (a : _)(_ : a ∈ v.sets_at x), a ⊆ closed_ball x ε ∧ P a :=
  by 
    simp only [Filter.Frequently, eventually_filter_at_iff, not_exists, exists_prop, not_and, not_not, not_forall]

theorem eventually_filter_at_subset_of_nhds {x : α} {o : Set α} (hx : o ∈ 𝓝 x) : ∀ᶠa in v.filter_at x, a ⊆ o :=
  by 
    rw [eventually_filter_at_iff]
    rcases Metric.mem_nhds_iff.1 hx with ⟨ε, εpos, hε⟩
    exact ⟨ε / 2, half_pos εpos, fun a av ha => ha.trans ((closed_ball_subset_ball (half_lt_self εpos)).trans hε)⟩

theorem fine_subfamily_on_of_frequently (v : VitaliFamily μ) (f : α → Set (Set α)) (s : Set α)
  (h : ∀ x (_ : x ∈ s), ∃ᶠa in v.filter_at x, a ∈ f x) : v.fine_subfamily_on f s :=
  by 
    intro x hx ε εpos 
    obtain ⟨a, av, ha, af⟩ : ∃ (a : Set α)(H : a ∈ v.sets_at x), a ⊆ closed_ball x ε ∧ a ∈ f x :=
      v.frequently_filter_at_iff.1 (h x hx) ε εpos 
    exact ⟨a, ⟨av, af⟩, ha⟩

end VitaliFamily

