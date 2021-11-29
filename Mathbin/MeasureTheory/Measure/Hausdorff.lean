import Mathbin.Topology.MetricSpace.MetricSeparated 
import Mathbin.MeasureTheory.Constructions.BorelSpace 
import Mathbin.MeasureTheory.Measure.Lebesgue 
import Mathbin.Analysis.SpecialFunctions.Pow 
import Mathbin.Topology.MetricSpace.Holder 
import Mathbin.Data.Equiv.List

/-!
# Hausdorff measure and metric (outer) measures

In this file we define the `d`-dimensional Hausdorff measure on an (extended) metric space `X` and
the Hausdorff dimension of a set in an (extended) metric space. Let `μ d δ` be the maximal outer
measure such that `μ d δ s ≤ (emetric.diam s) ^ d` for every set of diameter less than `δ`. Then
the Hausdorff measure `μH[d] s` of `s` is defined as `⨆ δ > 0, μ d δ s`. By Caratheodory theorem
`measure_theory.outer_measure.is_metric.borel_le_caratheodory`, this is a Borel measure on `X`.

The value of `μH[d]`, `d > 0`, on a set `s` (measurable or not) is given by
```
μH[d] s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, emetric.diam (t n) ≤ r), ∑' n, emetric.diam (t n) ^ d
```

For every set `s` for any `d < d'` we have either `μH[d] s = ∞` or `μH[d'] s = 0`, see
`measure_theory.measure.hausdorff_measure_zero_or_top`. In
`topology.metric_space.hausdorff_dimension` we use this fact to define the Hausdorff dimension
`dimH` of a set in an (extended) metric space.

We also define two generalizations of the Hausdorff measure. In one generalization (see
`measure_theory.measure.mk_metric`) we take any function `m (diam s)` instead of `(diam s) ^ d`. In
an even more general definition (see `measure_theory.measure.mk_metric'`) we use any function
of `m : set X → ℝ≥0∞`. Some authors start with a partial function `m` defined only on some sets
`s : set X` (e.g., only on balls or only on measurable sets). This is equivalent to our definition
applied to `measure_theory.extend m`.

We also define a predicate `measure_theory.outer_measure.is_metric` which says that an outer measure
is additive on metric separated pairs of sets: `μ (s ∪ t) = μ s + μ t` provided that
`⨅ (x ∈ s) (y ∈ t), edist x y ≠ 0`. This is the property required for the Caratheodory theorem
`measure_theory.outer_measure.is_metric.borel_le_caratheodory`, so we prove this theorem for any
metric outer measure, then prove that outer measures constructed using `mk_metric'` are metric outer
measures.

## Main definitions

* `measure_theory.outer_measure.is_metric`: an outer measure `μ` is called *metric* if
  `μ (s ∪ t) = μ s + μ t` for any two metric separated sets `s` and `t`. A metric outer measure in a
  Borel extended metric space is guaranteed to satisfy the Caratheodory condition, see
  `measure_theory.outer_measure.is_metric.borel_le_caratheodory`.
* `measure_theory.outer_measure.mk_metric'` and its particular case
  `measure_theory.outer_measure.mk_metric`: a construction of an outer measure that is guaranteed to
  be metric. Both constructions are generalizations of the Hausdorff measure. The same measures
  interpreted as Borel measures are called `measure_theory.measure.mk_metric'` and
  `measure_theory.measure.mk_metric`.
* `measure_theory.measure.hausdorff_measure` a.k.a. `μH[d]`: the `d`-dimensional Hausdorff measure.
  There are many definitions of the Hausdorff measure that differ from each other by a
  multiplicative constant. We put
  `μH[d] s = ⨆ r > 0, ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n) (ht : ∀ n, emetric.diam (t n) ≤ r),
    ∑' n, ⨆ (ht : ¬set.subsingleton (t n)), (emetric.diam (t n)) ^ d`,
  see `measure_theory.measure.hausdorff_measure_apply'`. In the most interesting case `0 < d` one
  can omit the `⨆ (ht : ¬set.subsingleton (t n))` part.

## Main statements

### Basic properties

* `measure_theory.outer_measure.is_metric.borel_le_caratheodory`: if `μ` is a metric outer measure
  on an extended metric space `X` (that is, it is additive on pairs of metric separated sets), then
  every Borel set is Caratheodory measurable (hence, `μ` defines an actual
  `measure_theory.measure`). See also `measure_theory.measure.mk_metric`.
* `measure_theory.measure.hausdorff_measure_mono`: `μH[d] s` is an antitone function
  of `d`.
* `measure_theory.measure.hausdorff_measure_zero_or_top`: if `d₁ < d₂`, then for any `s`, either
  `μH[d₂] s = 0` or `μH[d₁] s = ∞`. Together with the previous lemma, this means that `μH[d] s` is
  equal to infinity on some ray `(-∞, D)` and is equal to zero on `(D, +∞)`, where `D` is a possibly
  infinite number called the *Hausdorff dimension* of `s`; `μH[D] s` can be zero, infinity, or
  anything in between.
* `measure_theory.measure.no_atoms_hausdorff`: Hausdorff measure has no atoms.

### Hausdorff measure in `ℝⁿ`

* `measure_theory.hausdorff_measure_pi_real`: for a nonempty `ι`, `μH[card ι]` on `ι → ℝ` equals
  Lebesgue measure.

## Notations

We use the following notation localized in `measure_theory`.

- `μH[d]` : `measure_theory.measure.hausdorff_measure d`

## Implementation notes

There are a few similar constructions called the `d`-dimensional Hausdorff measure. E.g., some
sources only allow coverings by balls and use `r ^ d` instead of `(diam s) ^ d`. While these
construction lead to different Hausdorff measures, they lead to the same notion of the Hausdorff
dimension.

Some sources define the `0`-dimensional Hausdorff measure to be the counting measure. We define it
to be zero on subsingletons because this way we can have a
`measure.has_no_atoms (measure.hausdorff_measure d)` instance.

## TODO

* prove that `1`-dimensional Hausdorff measure on `ℝ` equals `volume`;
* prove a similar statement for `ℝ × ℝ`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.10][Federer1996]

## Tags

Hausdorff measure, measure, metric measure
-/


open_locale Nnreal Ennreal TopologicalSpace BigOperators

open Emetric Set Function Filter Encodable FiniteDimensional TopologicalSpace

noncomputable theory

variable{ι X Y : Type _}[EmetricSpace X][EmetricSpace Y]

namespace MeasureTheory

namespace OuterMeasure

/-!
### Metric outer measures

In this section we define metric outer measures and prove Caratheodory theorem: a metric outer
measure has the Caratheodory property.
-/


/-- We say that an outer measure `μ` in an (e)metric space is *metric* if `μ (s ∪ t) = μ s + μ t`
for any two metric separated sets `s`, `t`. -/
def is_metric (μ : outer_measure X) : Prop :=
  ∀ (s t : Set X), IsMetricSeparated s t → μ (s ∪ t) = μ s+μ t

namespace IsMetric

variable{μ : outer_measure X}

/-- A metric outer measure is additive on a finite set of pairwise metric separated sets. -/
theorem finset_Union_of_pairwise_separated (hm : is_metric μ) {I : Finset ι} {s : ι → Set X}
  (hI : ∀ i (_ : i ∈ I) j (_ : j ∈ I), i ≠ j → IsMetricSeparated (s i) (s j)) :
  μ (⋃(i : _)(_ : i ∈ I), s i) = ∑i in I, μ (s i) :=
  by 
    classical 
    induction' I using Finset.induction_on with i I hiI ihI hI
    ·
      simp 
    simp only [Finset.mem_insert] at hI 
    rw [Finset.set_bUnion_insert, hm, ihI, Finset.sum_insert hiI]
    exacts[fun i hi j hj hij => hI i (Or.inr hi) j (Or.inr hj) hij,
      IsMetricSeparated.finset_Union_right
        fun j hj => hI i (Or.inl rfl) j (Or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm]

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Caratheodory theorem. If `m` is a metric outer measure, then every Borel measurable set `t` is
Caratheodory measurable: for any (not necessarily measurable) set `s` we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
theorem borel_le_caratheodory (hm : is_metric μ) : «expr ≤ »(borel X, μ.caratheodory) :=
begin
  rw ["[", expr borel_eq_generate_from_is_closed, "]"] [],
  refine [expr measurable_space.generate_from_le (λ t ht, «expr $ »(μ.is_caratheodory_iff_le.2, λ s, _))],
  set [] [ident S] [":", expr exprℕ() → set X] [":="] [expr λ
   n, {x ∈ s | «expr ≤ »(«expr ⁻¹»(«expr↑ »(n)), inf_edist x t)}] [],
  have [ident n0] [":", expr ∀ {n : exprℕ()}, «expr ≠ »((«expr ⁻¹»(n) : «exprℝ≥0∞»()), 0)] [],
  from [expr λ n, ennreal.inv_ne_zero.2 ennreal.coe_nat_ne_top],
  have [ident Ssep] [":", expr ∀ n, is_metric_separated (S n) t] [],
  from [expr λ n, ⟨«expr ⁻¹»(n), n0, λ x hx y hy, «expr $ »(hx.2.trans, inf_edist_le_edist_of_mem hy)⟩],
  have [ident Ssep'] [":", expr ∀ n, is_metric_separated (S n) «expr ∩ »(s, t)] [],
  from [expr λ n, (Ssep n).mono subset.rfl (inter_subset_right _ _)],
  have [ident S_sub] [":", expr ∀ n, «expr ⊆ »(S n, «expr \ »(s, t))] [],
  from [expr λ n, subset_inter (inter_subset_left _ _) (Ssep n).subset_compl_right],
  have [ident hSs] [":", expr ∀ n, «expr ≤ »(«expr + »(μ «expr ∩ »(s, t), μ (S n)), μ s)] [],
  from [expr λ n, calc
     «expr = »(«expr + »(μ «expr ∩ »(s, t), μ (S n)), μ «expr ∪ »(«expr ∩ »(s, t), S n)) : «expr $ »(eq.symm, «expr $ »(hm _ _, (Ssep' n).symm))
     «expr ≤ »(..., μ «expr ∪ »(«expr ∩ »(s, t), «expr \ »(s, t))) : by { mono ["*"] [] [] [],
       exact [expr le_rfl] }
     «expr = »(..., μ s) : by rw ["[", expr inter_union_diff, "]"] []],
  have [ident Union_S] [":", expr «expr = »(«expr⋃ , »((n), S n), «expr \ »(s, t))] [],
  { refine [expr subset.antisymm (Union_subset S_sub) _],
    rintro [ident x, "⟨", ident hxs, ",", ident hxt, "⟩"],
    rw [expr mem_iff_inf_edist_zero_of_closed ht] ["at", ident hxt],
    rcases [expr ennreal.exists_inv_nat_lt hxt, "with", "⟨", ident n, ",", ident hn, "⟩"],
    exact [expr mem_Union.2 ⟨n, hxs, hn.le⟩] },
  by_cases [expr htop, ":", expr «expr = »(μ «expr \ »(s, t), «expr∞»())],
  { rw ["[", expr htop, ",", expr ennreal.add_top, ",", "<-", expr htop, "]"] [],
    exact [expr μ.mono (diff_subset _ _)] },
  suffices [] [":", expr «expr ≤ »(μ «expr⋃ , »((n), S n), «expr⨆ , »((n), μ (S n)))],
  calc
    «expr = »(«expr + »(μ «expr ∩ »(s, t), μ «expr \ »(s, t)), «expr + »(μ «expr ∩ »(s, t), μ «expr⋃ , »((n), S n))) : by rw [expr Union_S] []
    «expr ≤ »(..., «expr + »(μ «expr ∩ »(s, t), «expr⨆ , »((n), μ (S n)))) : add_le_add le_rfl this
    «expr = »(..., «expr⨆ , »((n), «expr + »(μ «expr ∩ »(s, t), μ (S n)))) : ennreal.add_supr
    «expr ≤ »(..., μ s) : supr_le hSs,
  have [] [":", expr ∀ n, «expr ⊆ »(S n, S «expr + »(n, 1))] [],
  from [expr λ n x hx, ⟨hx.1, le_trans «expr $ »(ennreal.inv_le_inv.2, ennreal.coe_nat_le_coe_nat.2 n.le_succ) hx.2⟩],
  refine [expr (μ.Union_nat_of_monotone_of_tsum_ne_top this _).le],
  clear [ident this],
  rw ["[", "<-", expr tsum_even_add_odd ennreal.summable ennreal.summable, ",", expr ennreal.add_ne_top, "]"] [],
  suffices [] [":", expr ∀
   a, «expr ≠ »(«expr∑' , »((k : exprℕ()), μ «expr \ »(S «expr + »(«expr + »(«expr * »(2, k), 1), a), S «expr + »(«expr * »(2, k), a))), «expr∞»())],
  from [expr ⟨by simpa [] [] [] [] [] ["using", expr this 0], by simpa [] [] [] [] [] ["using", expr this 1]⟩],
  refine [expr λ r, ne_top_of_le_ne_top htop _],
  rw ["[", "<-", expr Union_S, ",", expr ennreal.tsum_eq_supr_nat, ",", expr supr_le_iff, "]"] [],
  intro [ident n],
  rw ["[", "<-", expr hm.finset_Union_of_pairwise_separated, "]"] [],
  { exact [expr μ.mono «expr $ »(Union_subset, λ i, «expr $ »(Union_subset, λ hi x hx, mem_Union.2 ⟨_, hx.1⟩))] },
  suffices [] [":", expr ∀
   i
   j, «expr < »(i, j) → is_metric_separated (S «expr + »(«expr + »(«expr * »(2, i), 1), r)) «expr \ »(s, S «expr + »(«expr * »(2, j), r))],
  from [expr λ
   i
   _
   j
   _
   hij, hij.lt_or_lt.elim (λ
    h, (this i j h).mono (inter_subset_left _ _) (λ
     x hx, ⟨hx.1.1, hx.2⟩)) (λ h, (this j i h).symm.mono (λ x hx, ⟨hx.1.1, hx.2⟩) (inter_subset_left _ _))],
  intros [ident i, ident j, ident hj],
  have [ident A] [":", expr «expr < »((«expr ⁻¹»(«expr↑ »(«expr + »(«expr * »(2, j), r))) : «exprℝ≥0∞»()), «expr ⁻¹»(«expr↑ »(«expr + »(«expr + »(«expr * »(2, i), 1), r))))] [],
  by { rw ["[", expr ennreal.inv_lt_inv, ",", expr ennreal.coe_nat_lt_coe_nat, "]"] [],
    linarith [] [] [] },
  refine [expr ⟨«expr - »(«expr ⁻¹»(«expr↑ »(«expr + »(«expr + »(«expr * »(2, i), 1), r))), «expr ⁻¹»(«expr↑ »(«expr + »(«expr * »(2, j), r)))), by simpa [] [] [] [] [] ["using", expr A], λ
    x hx y hy, _⟩],
  have [] [":", expr «expr < »(inf_edist y t, «expr ⁻¹»(«expr↑ »(«expr + »(«expr * »(2, j), r))))] [],
  from [expr not_le.1 (λ hle, hy.2 ⟨hy.1, hle⟩)],
  rcases [expr exists_edist_lt_of_inf_edist_lt this, "with", "⟨", ident z, ",", ident hzt, ",", ident hyz, "⟩"],
  have [ident hxz] [":", expr «expr ≤ »(«expr ⁻¹»(«expr↑ »(«expr + »(«expr + »(«expr * »(2, i), 1), r))), edist x z)] [],
  from [expr le_inf_edist.1 hx.2 _ hzt],
  apply [expr ennreal.le_of_add_le_add_right hyz.ne_top],
  refine [expr le_trans _ (edist_triangle _ _ _)],
  refine [expr (add_le_add le_rfl hyz.le).trans (eq.trans_le _ hxz)],
  rw ["[", expr tsub_add_cancel_of_le A.le, "]"] []
end

theorem le_caratheodory [MeasurableSpace X] [BorelSpace X] (hm : is_metric μ) : ‹MeasurableSpace X› ≤ μ.caratheodory :=
  by 
    rw [@BorelSpace.measurable_eq X _ _]
    exact hm.borel_le_caratheodory

end IsMetric

/-!
### Constructors of metric outer measures

In this section we provide constructors `measure_theory.outer_measure.mk_metric'` and
`measure_theory.outer_measure.mk_metric` and prove that these outer measures are metric outer
measures. We also prove basic lemmas about `map`/`comap` of these measures.
-/


-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Auxiliary definition for `outer_measure.mk_metric'`: given a function on sets
`m : set X → ℝ≥0∞`, returns the maximal outer measure `μ` such that `μ s ≤ m s`
for any set `s` of diameter at most `r`.-/
def mk_metric'.pre (m : set X → «exprℝ≥0∞»()) (r : «exprℝ≥0∞»()) : outer_measure X :=
«expr $ »(bounded_by, extend (λ (s) (hs : «expr ≤ »(diam s, r)), m s))

/-- Given a function `m : set X → ℝ≥0∞`, `mk_metric' m` is the supremum of `mk_metric'.pre m r`
over `r > 0`. Equivalently, it is the limit of `mk_metric'.pre m r` as `r` tends to zero from
the right. -/
def mk_metric' (m : Set X → ℝ≥0∞) : outer_measure X :=
  ⨆(r : _)(_ : r > 0), mk_metric'.pre m r

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞` and `r > 0`, let `μ r` be the maximal outer measure such that
`μ s = 0` on subsingletons and `μ s ≤ m (emetric.diam s)` whenever `emetric.diam s < r`. Then
`mk_metric m = ⨆ r > 0, μ r`. We add `⨆ (hs : ¬s.subsingleton)` to ensure that in the case
`m x = x ^ d` the definition gives the expected result for `d = 0`. -/
def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) : outer_measure X :=
  mk_metric' fun s => ⨆hs : ¬s.subsingleton, m (diam s)

namespace MkMetric'

variable{m : Set X → ℝ≥0∞}{r : ℝ≥0∞}{μ : outer_measure X}{s : Set X}

theorem le_pre : μ ≤ pre m r ↔ ∀ (s : Set X), diam s ≤ r → μ s ≤ m s :=
  by 
    simp only [pre, le_bounded_by, extend, le_infi_iff]

theorem pre_le (hs : diam s ≤ r) : pre m r s ≤ m s :=
  (bounded_by_le _).trans$ infi_le _ hs

theorem mono_pre (m : Set X → ℝ≥0∞) {r r' : ℝ≥0∞} (h : r ≤ r') : pre m r' ≤ pre m r :=
  le_pre.2$ fun s hs => pre_le (hs.trans h)

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem mono_pre_nat (m : set X → «exprℝ≥0∞»()) : monotone (λ k : exprℕ(), pre m «expr ⁻¹»(k)) :=
λ k l h, «expr $ »(le_pre.2, λ s hs, pre_le «expr $ »(hs.trans, by simpa [] [] [] [] [] []))

theorem tendsto_pre (m : Set X → ℝ≥0∞) (s : Set X) : tendsto (fun r => pre m r s) (𝓝[Ioi 0] 0) (𝓝$ mk_metric' m s) :=
  by 
    rw [←map_coe_Ioi_at_bot, tendsto_map'_iff]
    simp only [mk_metric', outer_measure.supr_apply, supr_subtype']
    exact tendsto_at_bot_supr fun r r' hr => mono_pre _ hr _

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_pre_nat
(m : set X → «exprℝ≥0∞»())
(s : set X) : tendsto (λ n : exprℕ(), pre m «expr ⁻¹»(n) s) at_top «expr $ »(expr𝓝(), mk_metric' m s) :=
begin
  refine [expr (tendsto_pre m s).comp (tendsto_inf.2 ⟨ennreal.tendsto_inv_nat_nhds_zero, _⟩)],
  refine [expr tendsto_principal.2 «expr $ »(eventually_of_forall, λ n, _)],
  simp [] [] [] [] [] []
end

theorem eq_supr_nat (m : Set X → ℝ≥0∞) : mk_metric' m = ⨆n : ℕ, mk_metric'.pre m (n⁻¹) :=
  by 
    ext1 s 
    rw [supr_apply]
    refine'
      tendsto_nhds_unique (mk_metric'.tendsto_pre_nat m s)
        (tendsto_at_top_supr$ fun k l hkl => mk_metric'.mono_pre_nat m hkl s)

/-- `measure_theory.outer_measure.mk_metric'.pre m r` is a trimmed measure provided that
`m (closure s) = m s` for any set `s`. -/
theorem trim_pre [MeasurableSpace X] [OpensMeasurableSpace X] (m : Set X → ℝ≥0∞) (hcl : ∀ s, m (Closure s) = m s)
  (r : ℝ≥0∞) : (pre m r).trim = pre m r :=
  by 
    refine' le_antisymmₓ (le_pre.2$ fun s hs => _) (le_trim _)
    rw [trim_eq_infi]
    refine'
      infi_le_of_le (Closure s)$
        infi_le_of_le subset_closure$ infi_le_of_le measurable_set_closure ((pre_le _).trans_eq (hcl _))
    rwa [diam_closure]

end MkMetric'

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An outer measure constructed using `outer_measure.mk_metric'` is a metric outer measure. -/
theorem mk_metric'_is_metric (m : set X → «exprℝ≥0∞»()) : (mk_metric' m).is_metric :=
begin
  rintros [ident s, ident t, "⟨", ident r, ",", ident r0, ",", ident hr, "⟩"],
  refine [expr tendsto_nhds_unique_of_eventually_eq (mk_metric'.tendsto_pre _ _) ((mk_metric'.tendsto_pre _ _).add (mk_metric'.tendsto_pre _ _)) _],
  rw ["[", "<-", expr pos_iff_ne_zero, "]"] ["at", ident r0],
  filter_upwards ["[", expr Ioo_mem_nhds_within_Ioi ⟨le_rfl, r0⟩, "]"] [],
  rintro [ident ε, "⟨", ident ε0, ",", ident εr, "⟩"],
  refine [expr bounded_by_union_of_top_of_nonempty_inter _],
  rintro [ident u, "⟨", ident x, ",", ident hxs, ",", ident hxu, "⟩", "⟨", ident y, ",", ident hyt, ",", ident hyu, "⟩"],
  have [] [":", expr «expr < »(ε, diam u)] [],
  from [expr εr.trans_le «expr $ »((hr x hxs y hyt).trans, edist_le_diam_of_mem hxu hyu)],
  exact [expr infi_eq_top.2 (λ h, (this.not_le h).elim)]
end

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `0 < d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then `mk_metric m₁ hm₁ ≤ c • mk_metric m₂ hm₂`. -/
theorem mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0)
  (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] c • m₂) : (mk_metric m₁ : outer_measure X) ≤ c • mk_metric m₂ :=
  by 
    classical 
    rcases(mem_nhds_within_Ioi_iff_exists_Ioo_subset' Ennreal.zero_lt_one).1 hle with ⟨r, hr0, hr⟩
    refine'
      fun s =>
        le_of_tendsto_of_tendsto (mk_metric'.tendsto_pre _ s)
          (Ennreal.Tendsto.const_mul (mk_metric'.tendsto_pre _ s) (Or.inr hc))
          (mem_of_superset (Ioo_mem_nhds_within_Ioi ⟨le_rfl, hr0⟩) fun r' hr' => _)
    simp only [mem_set_of_eq, mk_metric'.pre]
    rw [←smul_apply, smul_bounded_by hc]
    refine' le_bounded_by.2 (fun t => (bounded_by_le _).trans _) _ 
    simp only [smul_eq_mul, Pi.smul_apply, extend, infi_eq_if]
    splitIfs with ht ht
    ·
      refine' supr_le fun ht₁ => _ 
      rw [supr_eq_if, if_pos ht₁]
      refine' hr ⟨_, ht.trans_lt hr'.2⟩
      exact pos_iff_ne_zero.2 (mt diam_eq_zero_iff.1 ht₁)
    ·
      simp [h0]

/-- If `m₁ d ≤ m₂ d` for `0 < d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then
`mk_metric m₁ hm₁ ≤ mk_metric m₂ hm₂`-/
theorem mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] m₂) :
  (mk_metric m₁ : outer_measure X) ≤ mk_metric m₂ :=
  by 
    convert mk_metric_mono_smul Ennreal.one_ne_top ennreal.zero_lt_one.ne' _ <;> simp 

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem isometry_comap_mk_metric
(m : «exprℝ≥0∞»() → «exprℝ≥0∞»())
{f : X → Y}
(hf : isometry f)
(H : «expr ∨ »(monotone (λ
   d : {d : «exprℝ≥0∞»() | «expr ≠ »(d, 0)}, m d), surjective f)) : «expr = »(comap f (mk_metric m), mk_metric m) :=
begin
  simp [] [] ["only"] ["[", expr mk_metric, ",", expr mk_metric', ",", expr mk_metric'.pre, ",", expr induced_outer_measure, ",", expr comap_supr, "]"] [] [],
  refine [expr supr_congr id surjective_id (λ ε, «expr $ »(supr_congr id surjective_id, λ hε, _))],
  rw [expr comap_bounded_by _ (H.imp (λ h_mono, _) id)] [],
  { congr' [] ["with", ident s, ":", 1],
    apply [expr extend_congr],
    { simp [] [] [] ["[", expr hf.ediam_image, "]"] [] [] },
    { intros [],
      simp [] [] [] ["[", expr hf.injective.subsingleton_image_iff, ",", expr hf.ediam_image, "]"] [] [] } },
  { refine [expr λ s t hst, infi_le_infi2 (λ ht, ⟨(diam_mono hst).trans ht, «expr $ »(supr_le, λ hs, _)⟩)],
    have [ident ht] [":", expr «expr¬ »((t : set Y).subsingleton)] [],
    from [expr λ ht, hs (ht.mono hst)],
    refine [expr (@h_mono ⟨_, mt diam_eq_zero_iff.1 hs⟩ ⟨_, mt diam_eq_zero_iff.1 ht⟩ (diam_mono hst)).trans _],
    exact [expr le_supr (λ h : «expr¬ »((t : set Y).subsingleton), m (diam (t : set Y))) ht] }
end

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem isometry_map_mk_metric
(m : «exprℝ≥0∞»() → «exprℝ≥0∞»())
{f : X → Y}
(hf : isometry f)
(H : «expr ∨ »(monotone (λ
   d : {d : «exprℝ≥0∞»() | «expr ≠ »(d, 0)}, m d), surjective f)) : «expr = »(map f (mk_metric m), restrict (range f) (mk_metric m)) :=
by rw ["[", "<-", expr isometry_comap_mk_metric _ hf H, ",", expr map_comap, "]"] []

theorem isometric_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) : comap f (mk_metric m) = mk_metric m :=
  isometry_comap_mk_metric _ f.isometry (Or.inr f.surjective)

theorem isometric_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) : map f (mk_metric m) = mk_metric m :=
  by 
    rw [←isometric_comap_mk_metric _ f, map_comap_of_surjective f.surjective]

theorem trim_mk_metric [MeasurableSpace X] [BorelSpace X] (m : ℝ≥0∞ → ℝ≥0∞) :
  (mk_metric m : outer_measure X).trim = mk_metric m :=
  by 
    simp only [mk_metric, mk_metric'.eq_supr_nat, trim_supr]
    congr 1 with n : 1
    refine' mk_metric'.trim_pre _ (fun s => _) _ 
    simp 

theorem le_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (μ : outer_measure X) (hμ : ∀ x, μ {x} = 0) (r : ℝ≥0∞) (h0 : 0 < r)
  (hr : ∀ s, diam s ≤ r → ¬s.subsingleton → μ s ≤ m (diam s)) : μ ≤ mk_metric m :=
  le_bsupr_of_le r h0$
    mk_metric'.le_pre.2$
      fun s hs =>
        by 
          byCases' h : s.subsingleton 
          exacts[h.induction_on (μ.empty'.trans_le (zero_le _)) fun x => (hμ x).trans_le (zero_le _),
            le_supr_of_le h (hr _ hs h)]

end OuterMeasure

/-!
### Metric measures

In this section we use `measure_theory.outer_measure.to_measure` and theorems about
`measure_theory.outer_measure.mk_metric'`/`measure_theory.outer_measure.mk_metric` to define
`measure_theory.measure.mk_metric'`/`measure_theory.measure.mk_metric`. We also restate some lemmas
about metric outer measures for metric measures.
-/


namespace Measureₓ

variable[MeasurableSpace X][BorelSpace X]

/-- Given a function `m : set X → ℝ≥0∞`, `mk_metric' m` is the supremum of `μ r`
over `r > 0`, where `μ r` is the maximal outer measure `μ` such that `μ s ≤ m s`
for all `s`. While each `μ r` is an *outer* measure, the supremum is a measure. -/
def mk_metric' (m : Set X → ℝ≥0∞) : Measureₓ X :=
  (outer_measure.mk_metric' m).toMeasure (outer_measure.mk_metric'_is_metric _).le_caratheodory

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞`, `mk_metric m` is the supremum of `μ r` over `r > 0`, where
`μ r` is the maximal outer measure `μ` such that `μ s ≤ m s` for all sets `s` that contain at least
two points. While each `mk_metric'.pre` is an *outer* measure, the supremum is a measure. -/
def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) : Measureₓ X :=
  (outer_measure.mk_metric m).toMeasure (outer_measure.mk_metric'_is_metric _).le_caratheodory

@[simp]
theorem mk_metric'_to_outer_measure (m : Set X → ℝ≥0∞) :
  (mk_metric' m).toOuterMeasure = (outer_measure.mk_metric' m).trim :=
  rfl

@[simp]
theorem mk_metric_to_outer_measure (m : ℝ≥0∞ → ℝ≥0∞) :
  (mk_metric m : Measureₓ X).toOuterMeasure = outer_measure.mk_metric m :=
  outer_measure.trim_mk_metric m

end Measureₓ

theorem outer_measure.coe_mk_metric [MeasurableSpace X] [BorelSpace X] (m : ℝ≥0∞ → ℝ≥0∞) :
  «expr⇑ » (outer_measure.mk_metric m : outer_measure X) = measure.mk_metric m :=
  by 
    rw [←measure.mk_metric_to_outer_measure, coe_to_outer_measure]

namespace Measureₓ

variable[MeasurableSpace X][BorelSpace X]

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `0 < d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then `mk_metric m₁ hm₁ ≤ c • mk_metric m₂ hm₂`. -/
theorem mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0)
  (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] c • m₂) : (mk_metric m₁ : Measureₓ X) ≤ c • mk_metric m₂ :=
  by 
    intro s hs 
    rw [←outer_measure.coe_mk_metric, coe_smul, ←outer_measure.coe_mk_metric]
    exact outer_measure.mk_metric_mono_smul hc h0 hle s

/-- If `m₁ d ≤ m₂ d` for `0 < d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝[Ioi 0]]` to state this), then
`mk_metric m₁ hm₁ ≤ mk_metric m₂ hm₂`-/
theorem mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝[Ioi 0] 0] m₂) :
  (mk_metric m₁ : Measureₓ X) ≤ mk_metric m₂ :=
  by 
    convert mk_metric_mono_smul Ennreal.one_ne_top ennreal.zero_lt_one.ne' _ <;> simp 

/-- A formula for `measure_theory.measure.mk_metric`. -/
theorem mk_metric_apply (m : ℝ≥0∞ → ℝ≥0∞) (s : Set X) :
  mk_metric m s =
    ⨆(r : ℝ≥0∞)(hr : 0 < r),
      ⨅(t : ℕ → Set X)(hts : s ⊆ ⋃n, t n)(ht : ∀ n, diam (t n) ≤ r), ∑'n, ⨆ht : ¬(t n).Subsingleton, m (diam (t n)) :=
  by 
    classical 
    simp only [←outer_measure.coe_mk_metric, outer_measure.mk_metric, outer_measure.mk_metric',
      outer_measure.supr_apply, outer_measure.mk_metric'.pre, outer_measure.bounded_by_apply, extend]
    refine'
      supr_congr (fun r => r) surjective_id
        fun r =>
          supr_congr_Prop Iff.rfl$ fun hr => infi_congr _ surjective_id$ fun t => infi_congr_Prop Iff.rfl$ fun ht => _ 
    byCases' htr : ∀ n, diam (t n) ≤ r
    ·
      rw [infi_eq_if, if_pos htr]
      congr 1 with n : 1
      simp only [infi_eq_if, htr n, id, if_true, supr_and']
      refine' supr_congr_Prop (and_iff_right_of_imp$ fun h => _) fun _ => rfl 
      contrapose! h 
      rw [not_nonempty_iff_eq_empty.1 h]
      exact subsingleton_empty
    ·
      rw [infi_eq_if, if_neg htr]
      pushNeg  at htr 
      rcases htr with ⟨n, hn⟩
      refine' Ennreal.tsum_eq_top_of_eq_top ⟨n, _⟩
      rw [supr_eq_if, if_pos, infi_eq_if, if_neg]
      exact hn.not_le 
      rcases diam_pos_iff.1 ((zero_le r).trans_lt hn) with ⟨x, hx, -⟩
      exact ⟨x, hx⟩

theorem le_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (μ : Measureₓ X) [has_no_atoms μ] (ε : ℝ≥0∞) (h₀ : 0 < ε)
  (h : ∀ (s : Set X), diam s ≤ ε → ¬s.subsingleton → μ s ≤ m (diam s)) : μ ≤ mk_metric m :=
  by 
    rw [←to_outer_measure_le, mk_metric_to_outer_measure]
    exact outer_measure.le_mk_metric m μ.to_outer_measure measure_singleton ε h₀ h

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- To bound the Hausdorff measure (or, more generally, for a measure defined using
`measure_theory.measure.mk_metric`) of a set, one may use coverings with maximum diameter tending to
`0`, indexed by any sequence of encodable types. -/
theorem mk_metric_le_liminf_tsum
{β : Type*}
{ι : β → Type*}
[∀ n, encodable (ι n)]
(s : set X)
{l : filter β}
(r : β → «exprℝ≥0∞»())
(hr : tendsto r l (expr𝓝() 0))
(t : ∀ n : β, ι n → set X)
(ht : «expr∀ᶠ in , »((n), l, ∀ i, «expr ≤ »(diam (t n i), r n)))
(hst : «expr∀ᶠ in , »((n), l, «expr ⊆ »(s, «expr⋃ , »((i), t n i))))
(m : «exprℝ≥0∞»() → «exprℝ≥0∞»()) : «expr ≤ »(mk_metric m s, liminf l (λ n, «expr∑' , »((i), m (diam (t n i))))) :=
begin
  simp [] [] ["only"] ["[", expr mk_metric_apply, "]"] [] [],
  refine [expr bsupr_le (λ ε hε, _)],
  refine [expr le_of_forall_le_of_dense (λ c hc, _)],
  rcases [expr ((frequently_lt_of_liminf_lt (by apply_auto_param) hc).and_eventually ((hr.eventually (gt_mem_nhds hε)).and (ht.and hst))).exists, "with", "⟨", ident n, ",", ident hn, ",", ident hrn, ",", ident htn, ",", ident hstn, "⟩"],
  set [] [ident u] [":", expr exprℕ() → set X] [":="] [expr λ j, «expr⋃ , »((b «expr ∈ » decode₂ (ι n) j), t n b)] [],
  refine [expr binfi_le_of_le u (by rwa [expr Union_decode₂] []) _],
  refine [expr infi_le_of_le (λ j, _) _],
  { rw [expr emetric.diam_Union_mem_option] [],
    exact [expr bsupr_le (λ _ _, (htn _).trans hrn.le)] },
  { calc
      «expr = »(«expr∑' , »((j : exprℕ()), «expr⨆ , »((ht : «expr¬ »((u j).subsingleton)), m (diam (u j)))), _) : tsum_Union_decode₂ (λ
       t : set X, «expr⨆ , »((h : «expr¬ »(t.subsingleton)), m (diam t))) (by simp [] [] [] [] [] []) _
      «expr ≤ »(..., _) : ennreal.tsum_le_tsum (λ b, «expr $ »(supr_le, λ htb, le_rfl))
      «expr ≤ »(..., c) : hn.le }
end

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- To bound the Hausdorff measure (or, more generally, for a measure defined using
`measure_theory.measure.mk_metric`) of a set, one may use coverings with maximum diameter tending to
`0`, indexed by any sequence of finite types. -/
theorem mk_metric_le_liminf_sum
{β : Type*}
{ι : β → Type*}
[hι : ∀ n, fintype (ι n)]
(s : set X)
{l : filter β}
(r : β → «exprℝ≥0∞»())
(hr : tendsto r l (expr𝓝() 0))
(t : ∀ n : β, ι n → set X)
(ht : «expr∀ᶠ in , »((n), l, ∀ i, «expr ≤ »(diam (t n i), r n)))
(hst : «expr∀ᶠ in , »((n), l, «expr ⊆ »(s, «expr⋃ , »((i), t n i))))
(m : «exprℝ≥0∞»() → «exprℝ≥0∞»()) : «expr ≤ »(mk_metric m s, liminf l (λ n, «expr∑ , »((i), m (diam (t n i))))) :=
begin
  haveI [] [":", expr ∀ n, encodable (ι n)] [],
  from [expr λ n, fintype.encodable _],
  simpa [] [] ["only"] ["[", expr tsum_fintype, "]"] [] ["using", expr mk_metric_le_liminf_tsum s r hr t ht hst m]
end

/-!
### Hausdorff measure and Hausdorff dimension
-/


/-- Hausdorff measure on an (e)metric space. -/
def hausdorff_measure (d : ℝ) : Measureₓ X :=
  mk_metric fun r => r^d

localized [MeasureTheory] notation "μH[" d "]" => MeasureTheory.Measure.hausdorffMeasure d

theorem le_hausdorff_measure (d : ℝ) (μ : Measureₓ X) [has_no_atoms μ] (ε : ℝ≥0∞) (h₀ : 0 < ε)
  (h : ∀ (s : Set X), diam s ≤ ε → ¬s.subsingleton → μ s ≤ (diam s^d)) : μ ≤ μH[d] :=
  le_mk_metric _ μ ε h₀ h

/-- A formula for `μH[d] s` that works for all `d`. In case of a positive `d` a simpler formula
is available as `measure_theory.measure.hausdorff_measure_apply`. -/
theorem hausdorff_measure_apply' (d : ℝ) (s : Set X) :
  μH[d] s =
    ⨆(r : ℝ≥0∞)(hr : 0 < r),
      ⨅(t : ℕ → Set X)(hts : s ⊆ ⋃n, t n)(ht : ∀ n, diam (t n) ≤ r), ∑'n, ⨆ht : ¬(t n).Subsingleton, diam (t n)^d :=
  mk_metric_apply _ _

/-- A formula for `μH[d] s` that works for all positive `d`. -/
theorem hausdorff_measure_apply {d : ℝ} (hd : 0 < d) (s : Set X) :
  μH[d] s = ⨆(r : ℝ≥0∞)(hr : 0 < r), ⨅(t : ℕ → Set X)(hts : s ⊆ ⋃n, t n)(ht : ∀ n, diam (t n) ≤ r), ∑'n, diam (t n)^d :=
  by 
    classical 
    rw [hausdorff_measure_apply']
    refine'
      supr_congr id surjective_id
        fun r =>
          supr_congr_Prop Iff.rfl$
            fun hr =>
              infi_congr id surjective_id$
                fun t => infi_congr_Prop Iff.rfl$ fun hts => infi_congr_Prop Iff.rfl$ fun ht => tsum_congr$ fun n => _ 
    rw [supr_eq_if]
    splitIfs with ht'
    ·
      erw [diam_eq_zero_iff.2 ht', Ennreal.zero_rpow_of_pos hd, Ennreal.bot_eq_zero]
    ·
      rfl

/-- To bound the Hausdorff measure of a set, one may use coverings with maximum diameter tending
to `0`, indexed by any sequence of encodable types. -/
theorem hausdorff_measure_le_liminf_tsum {β : Type _} {ι : β → Type _} [hι : ∀ n, Encodable (ι n)] (d : ℝ) (s : Set X)
  {l : Filter β} (r : β → ℝ≥0∞) (hr : tendsto r l (𝓝 0)) (t : ∀ (n : β), ι n → Set X)
  (ht : ∀ᶠn in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠn in l, s ⊆ ⋃i, t n i) :
  μH[d] s ≤ liminf l fun n => ∑'i, diam (t n i)^d :=
  mk_metric_le_liminf_tsum s r hr t ht hst _

/-- To bound the Hausdorff measure of a set, one may use coverings with maximum diameter tending
to `0`, indexed by any sequence of finite types. -/
theorem hausdorff_measure_le_liminf_sum {β : Type _} {ι : β → Type _} [hι : ∀ n, Fintype (ι n)] (d : ℝ) (s : Set X)
  {l : Filter β} (r : β → ℝ≥0∞) (hr : tendsto r l (𝓝 0)) (t : ∀ (n : β), ι n → Set X)
  (ht : ∀ᶠn in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠn in l, s ⊆ ⋃i, t n i) :
  μH[d] s ≤ liminf l fun n => ∑i, diam (t n i)^d :=
  mk_metric_le_liminf_sum s r hr t ht hst _

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `d₁ < d₂`, then for any set `s` we have either `μH[d₂] s = 0`, or `μH[d₁] s = ∞`. -/
theorem hausdorff_measure_zero_or_top
{d₁ d₂ : exprℝ()}
(h : «expr < »(d₁, d₂))
(s : set X) : «expr ∨ »(«expr = »(«exprμH[ ]»(d₂) s, 0), «expr = »(«exprμH[ ]»(d₁) s, «expr∞»())) :=
begin
  by_contra [ident H],
  push_neg ["at", ident H],
  suffices [] [":", expr ∀
   c : «exprℝ≥0»(), «expr ≠ »(c, 0) → «expr ≤ »(«exprμH[ ]»(d₂) s, «expr * »(c, «exprμH[ ]»(d₁) s))],
  { rcases [expr ennreal.exists_nnreal_pos_mul_lt H.2 H.1, "with", "⟨", ident c, ",", ident hc0, ",", ident hc, "⟩"],
    exact [expr hc.not_le (this c (pos_iff_ne_zero.1 hc0))] },
  intros [ident c, ident hc],
  refine [expr le_iff'.1 (mk_metric_mono_smul ennreal.coe_ne_top (by exact_mod_cast [expr hc]) _) s],
  have [] [":", expr «expr < »(0, («expr ^ »(c, «expr ⁻¹»(«expr - »(d₂, d₁))) : «exprℝ≥0∞»()))] [],
  { rw ["[", expr ennreal.coe_rpow_of_ne_zero hc, ",", expr pos_iff_ne_zero, ",", expr ne.def, ",", expr ennreal.coe_eq_zero, ",", expr nnreal.rpow_eq_zero_iff, "]"] [],
    exact [expr mt and.left hc] },
  filter_upwards ["[", expr Ioo_mem_nhds_within_Ioi ⟨le_rfl, this⟩, "]"] [],
  rintro [ident r, "⟨", ident hr₀, ",", ident hrc, "⟩"],
  lift [expr r] ["to", expr «exprℝ≥0»()] ["using", expr ne_top_of_lt hrc] [],
  rw ["[", expr pi.smul_apply, ",", expr smul_eq_mul, ",", "<-", expr ennreal.div_le_iff_le_mul (or.inr ennreal.coe_ne_top) «expr $ »(or.inr, mt ennreal.coe_eq_zero.1 hc), ",", "<-", expr ennreal.rpow_sub _ _ hr₀.ne' ennreal.coe_ne_top, "]"] [],
  refine [expr (ennreal.rpow_lt_rpow hrc (sub_pos.2 h)).le.trans _],
  rw ["[", "<-", expr ennreal.rpow_mul, ",", expr inv_mul_cancel (sub_pos.2 h).ne', ",", expr ennreal.rpow_one, "]"] [],
  exact [expr le_rfl]
end

/-- Hausdorff measure `μH[d] s` is monotone in `d`. -/
theorem hausdorff_measure_mono {d₁ d₂ : ℝ} (h : d₁ ≤ d₂) (s : Set X) : μH[d₂] s ≤ μH[d₁] s :=
  by 
    rcases h.eq_or_lt with (rfl | h)
    ·
      exact le_rfl 
    cases' hausdorff_measure_zero_or_top h s with hs hs
    ·
      rw [hs]
      exact zero_le _
    ·
      rw [hs]
      exact le_top

instance no_atoms_hausdorff (d : ℝ) : has_no_atoms (hausdorff_measure d : Measureₓ X) :=
  by 
    refine' ⟨fun x => _⟩
    rw [←nonpos_iff_eq_zero, hausdorff_measure_apply']
    refine' bsupr_le fun ε ε0 => binfi_le_of_le (fun n => {x}) _ (infi_le_of_le (fun n => _) _)
    ·
      exact subset_Union (fun n => {x} : ℕ → Set X) 0
    ·
      simp only [Emetric.diam_singleton, zero_le]
    ·
      simp 

end Measureₓ

open_locale MeasureTheory

open Measureₓ

/-!
### Hausdorff measure and Lebesgue measure
-/


-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- In the space `ι → ℝ`, Hausdorff measure coincides exactly with Lebesgue measure. -/
@[simp]
theorem hausdorff_measure_pi_real
{ι : Type*}
[fintype ι]
[nonempty ι] : «expr = »((«exprμH[ ]»(fintype.card ι) : measure (ι → exprℝ())), volume) :=
begin
  classical,
  refine [expr (pi_eq_generate_from (λ
     i, real.borel_eq_generate_from_Ioo_rat.symm) (λ
     i, real.is_pi_system_Ioo_rat) (λ i, real.finite_spanning_sets_in_Ioo_rat _) _).symm],
  simp [] [] ["only"] ["[", expr mem_Union, ",", expr mem_singleton_iff, "]"] [] [],
  intros [ident s, ident hs],
  choose [] [ident a] [ident b, ident H] ["using", expr hs],
  obtain [ident rfl, ":", expr «expr = »(s, λ i, Ioo (a i) (b i))],
  from [expr funext (λ i, (H i).2)],
  replace [ident H] [] [":=", expr λ i, (H i).1],
  apply [expr le_antisymm _],
  { have [ident Hle] [":", expr «expr ≤ »(volume, («exprμH[ ]»(fintype.card ι) : measure (ι → exprℝ())))] [],
    { refine [expr le_hausdorff_measure _ _ «expr∞»() ennreal.coe_lt_top (λ s h₁ h₂, _)],
      rw ["[", expr ennreal.rpow_nat_cast, "]"] [],
      exact [expr real.volume_pi_le_diam_pow s] },
    rw ["[", "<-", expr volume_pi_pi (λ i, Ioo (a i : exprℝ()) (b i)), "]"] [],
    exact [expr measure.le_iff'.1 Hle _] },
  have [ident I] [":", expr ∀
   i, «expr ≤ »(0, «expr - »((b i : exprℝ()), a i))] [":=", expr λ
   i, by simpa [] [] ["only"] ["[", expr sub_nonneg, ",", expr rat.cast_le, "]"] [] ["using", expr (H i).le]],
  let [ident γ] [] [":=", expr λ n : exprℕ(), ∀ i : ι, fin «expr⌈ ⌉₊»(«expr * »(«expr - »((b i : exprℝ()), a i), n))],
  let [ident t] [":", expr ∀
   n : exprℕ(), γ n → set (ι → exprℝ())] [":=", expr λ
   n f, set.pi univ (λ i, Icc «expr + »(a i, «expr / »(f i, n)) «expr + »(a i, «expr / »(«expr + »(f i, 1), n)))],
  have [ident A] [":", expr tendsto (λ n : exprℕ(), «expr / »(1, (n : «exprℝ≥0∞»()))) at_top (expr𝓝() 0)] [],
  by simp [] [] ["only"] ["[", expr one_div, ",", expr ennreal.tendsto_inv_nat_nhds_zero, "]"] [] [],
  have [ident B] [":", expr «expr∀ᶠ in , »((n), at_top, ∀ i : γ n, «expr ≤ »(diam (t n i), «expr / »(1, n)))] [],
  { apply [expr eventually_at_top.2 ⟨1, λ n hn, _⟩],
    assume [binders (f)],
    apply [expr diam_pi_le_of_le (λ b, _)],
    simp [] [] ["only"] ["[", expr real.ediam_Icc, ",", expr add_div, ",", expr ennreal.of_real_div_of_pos (nat.cast_pos.mpr hn), ",", expr le_refl, ",", expr add_sub_add_left_eq_sub, ",", expr add_sub_cancel', ",", expr ennreal.of_real_one, ",", expr ennreal.of_real_coe_nat, "]"] [] [] },
  have [ident C] [":", expr «expr∀ᶠ in , »((n), at_top, «expr ⊆ »(set.pi univ (λ
      i : ι, Ioo (a i : exprℝ()) (b i)), «expr⋃ , »((i : γ n), t n i)))] [],
  { apply [expr eventually_at_top.2 ⟨1, λ n hn, _⟩],
    have [ident npos] [":", expr «expr < »((0 : exprℝ()), n)] [":=", expr nat.cast_pos.2 hn],
    assume [binders (x hx)],
    simp [] [] ["only"] ["[", expr mem_Ioo, ",", expr mem_univ_pi, "]"] [] ["at", ident hx],
    simp [] [] ["only"] ["[", expr mem_Union, ",", expr mem_Ioo, ",", expr mem_univ_pi, ",", expr coe_coe, "]"] [] [],
    let [ident f] [":", expr γ n] [":=", expr λ
     i, ⟨«expr⌊ ⌋₊»(«expr * »(«expr - »(x i, a i), n)), begin
        apply [expr nat.floor_lt_ceil_of_lt_of_pos],
        { refine [expr (mul_lt_mul_right npos).2 _],
          simp [] [] ["only"] ["[", expr (hx i).right, ",", expr sub_lt_sub_iff_right, "]"] [] [] },
        { refine [expr mul_pos _ npos],
          simpa [] [] ["only"] ["[", expr rat.cast_lt, ",", expr sub_pos, "]"] [] ["using", expr H i] }
      end⟩],
    refine [expr ⟨f, λ i, ⟨_, _⟩⟩],
    { calc
        «expr ≤ »(«expr + »((a i : exprℝ()), «expr / »(«expr⌊ ⌋₊»(«expr * »(«expr - »(x i, a i), n)), n)), «expr + »((a i : exprℝ()), «expr / »(«expr * »(«expr - »(x i, a i), n), n))) : begin
          refine [expr add_le_add le_rfl ((div_le_div_right npos).2 _)],
          exact [expr nat.floor_le (mul_nonneg (sub_nonneg.2 (hx i).1.le) npos.le)]
        end
        «expr = »(..., x i) : by field_simp [] ["[", expr npos.ne', "]"] [] [] },
    { calc
        «expr = »(x i, «expr + »((a i : exprℝ()), «expr / »(«expr * »(«expr - »(x i, a i), n), n))) : by field_simp [] ["[", expr npos.ne', "]"] [] []
        «expr ≤ »(..., «expr + »((a i : exprℝ()), «expr / »(«expr + »(«expr⌊ ⌋₊»(«expr * »(«expr - »(x i, a i), n)), 1), n))) : add_le_add le_rfl ((div_le_div_right npos).2 (nat.lt_floor_add_one _).le) } },
  calc
    «expr ≤ »(«exprμH[ ]»(fintype.card ι) (set.pi univ (λ
       i : ι, Ioo (a i : exprℝ()) (b i))), liminf at_top (λ
      n : exprℕ(), «expr∑ , »((i : γ n), «expr ^ »(diam (t n i), «expr↑ »(fintype.card ι))))) : hausdorff_measure_le_liminf_sum _ (set.pi univ (λ
      i, Ioo (a i : exprℝ()) (b i))) (λ n : exprℕ(), «expr / »(1, (n : «exprℝ≥0∞»()))) A t B C
    «expr ≤ »(..., liminf at_top (λ
      n : exprℕ(), «expr∑ , »((i : γ n), «expr ^ »(«expr / »(1, n), fintype.card ι)))) : begin
      refine [expr liminf_le_liminf _ (by is_bounded_default)],
      filter_upwards ["[", expr B, "]"] [],
      assume [binders (n hn)],
      apply [expr finset.sum_le_sum (λ i _, _)],
      rw [expr ennreal.rpow_nat_cast] [],
      exact [expr pow_le_pow_of_le_left' (hn i) _]
    end
    «expr = »(..., liminf at_top (λ
      n : exprℕ(), «expr∏ , »((i : ι), «expr / »((«expr⌈ ⌉₊»(«expr * »(«expr - »((b i : exprℝ()), a i), n)) : «exprℝ≥0∞»()), n)))) : begin
      simp [] [] ["only"] ["[", expr finset.card_univ, ",", expr nat.cast_prod, ",", expr one_mul, ",", expr fintype.card_fin, ",", expr finset.sum_const, ",", expr nsmul_eq_mul, ",", expr fintype.card_pi, ",", expr div_eq_mul_inv, ",", expr finset.prod_mul_distrib, ",", expr finset.prod_const, "]"] [] []
    end
    «expr = »(..., «expr∏ , »((i : ι), volume (Ioo (a i : exprℝ()) (b i)))) : begin
      simp [] [] ["only"] ["[", expr real.volume_Ioo, "]"] [] [],
      apply [expr tendsto.liminf_eq],
      refine [expr ennreal.tendsto_finset_prod_of_ne_top _ (λ i hi, _) (λ i hi, _)],
      { apply [expr tendsto.congr' _ ((ennreal.continuous_of_real.tendsto _).comp ((tendsto_nat_ceil_mul_div_at_top (I i)).comp tendsto_coe_nat_at_top_at_top))],
        apply [expr eventually_at_top.2 ⟨1, λ n hn, _⟩],
        simp [] [] ["only"] ["[", expr ennreal.of_real_div_of_pos (nat.cast_pos.mpr hn), ",", expr comp_app, ",", expr ennreal.of_real_coe_nat, "]"] [] [] },
      { simp [] [] ["only"] ["[", expr ennreal.of_real_ne_top, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [] }
    end
end

end MeasureTheory

/-!
### Hausdorff measure, Hausdorff dimension, and Hölder or Lipschitz continuous maps
-/


open_locale MeasureTheory

open MeasureTheory MeasureTheory.Measure

variable[MeasurableSpace X][BorelSpace X][MeasurableSpace Y][BorelSpace Y]

namespace HolderOnWith

variable{C r :  ℝ≥0 }{f : X → Y}{s t : Set X}

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f : X → Y` is Hölder continuous on `s` with a positive exponent `r`, then
`μH[d] (f '' s) ≤ C ^ d * μH[r * d] s`. -/
theorem hausdorff_measure_image_le
(h : holder_on_with C r f s)
(hr : «expr < »(0, r))
{d : exprℝ()}
(hd : «expr ≤ »(0, d)) : «expr ≤ »(«exprμH[ ]»(d) «expr '' »(f, s), «expr * »(«expr ^ »(C, d), «exprμH[ ]»(«expr * »(r, d)) s)) :=
begin
  rcases [expr (zero_le C).eq_or_lt, "with", ident rfl, "|", ident hC0],
  { have [] [":", expr «expr '' »(f, s).subsingleton] [],
    by simpa [] [] [] ["[", expr diam_eq_zero_iff, "]"] [] ["using", expr h.ediam_image_le],
    rw [expr this.measure_zero] [],
    exact [expr zero_le _] },
  { have [ident hCd0] [":", expr «expr ≠ »(«expr ^ »((C : «exprℝ≥0∞»()), d), 0)] [],
    by simp [] [] [] ["[", expr hC0.ne', "]"] [] [],
    have [ident hCd] [":", expr «expr ≠ »(«expr ^ »((C : «exprℝ≥0∞»()), d), «expr∞»())] [],
    by simp [] [] [] ["[", expr hd, "]"] [] [],
    simp [] [] ["only"] ["[", expr hausdorff_measure_apply', ",", expr ennreal.mul_supr, ",", expr ennreal.mul_infi_of_ne hCd0 hCd, ",", "<-", expr ennreal.tsum_mul_left, "]"] [] [],
    refine [expr supr_le (λ R, «expr $ »(supr_le, λ hR, _))],
    have [] [":", expr tendsto (λ
      d : «exprℝ≥0∞»(), «expr * »((C : «exprℝ≥0∞»()), «expr ^ »(d, (r : exprℝ())))) (expr𝓝() 0) (expr𝓝() 0)] [],
    from [expr ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos ennreal.coe_ne_top hr],
    rcases [expr ennreal.nhds_zero_basis_Iic.eventually_iff.1 (this.eventually (gt_mem_nhds hR)), "with", "⟨", ident δ, ",", ident δ0, ",", ident H, "⟩"],
    refine [expr le_supr_of_le δ «expr $ »(le_supr_of_le δ0, «expr $ »(le_binfi, λ
       t hst, «expr $ »(le_infi, λ htδ, _)))],
    refine [expr binfi_le_of_le (λ n, «expr '' »(f, «expr ∩ »(t n, s))) _ (infi_le_of_le (λ n, _) _)],
    { rw ["[", "<-", expr image_Union, ",", "<-", expr Union_inter, "]"] [],
      exact [expr image_subset _ (subset_inter hst subset.rfl)] },
    { exact [expr (h.ediam_image_inter_le (t n)).trans (H (htδ n)).le] },
    { refine [expr ennreal.tsum_le_tsum (λ
        n, «expr $ »(supr_le, λ
         hft, le_supr_of_le (λ ht, «expr $ »(hft, (ht.mono (inter_subset_left _ _)).image f)) _))],
      rw ["[", expr ennreal.rpow_mul, ",", "<-", expr ennreal.mul_rpow_of_nonneg _ _ hd, "]"] [],
      exact [expr ennreal.rpow_le_rpow (h.ediam_image_inter_le _) hd] } }
end

end HolderOnWith

namespace LipschitzOnWith

variable{K :  ℝ≥0 }{f : X → Y}{s t : Set X}

/-- If `f : X → Y` is `K`-Lipschitz on `s`, then `μH[d] (f '' s) ≤ K ^ d * μH[d] s`. -/
theorem hausdorff_measure_image_le (h : LipschitzOnWith K f s) {d : ℝ} (hd : 0 ≤ d) : μH[d] (f '' s) ≤ (K^d)*μH[d] s :=
  by 
    simpa only [Nnreal.coe_one, one_mulₓ] using h.holder_on_with.hausdorff_measure_image_le zero_lt_one hd

end LipschitzOnWith

namespace LipschitzWith

variable{K :  ℝ≥0 }{f : X → Y}

/-- If `f` is a `K`-Lipschitz map, then it increases the Hausdorff `d`-measures of sets at most
by the factor of `K ^ d`.-/
theorem hausdorff_measure_image_le (h : LipschitzWith K f) {d : ℝ} (hd : 0 ≤ d) (s : Set X) :
  μH[d] (f '' s) ≤ (K^d)*μH[d] s :=
  (h.lipschitz_on_with s).hausdorff_measure_image_le hd

end LipschitzWith

/-!
### Antilipschitz maps do not decrease Hausdorff measures and dimension
-/


namespace AntilipschitzWith

variable{f : X → Y}{K :  ℝ≥0 }{d : ℝ}

-- error in MeasureTheory.Measure.Hausdorff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem hausdorff_measure_preimage_le
(hf : antilipschitz_with K f)
(hd : «expr ≤ »(0, d))
(s : set Y) : «expr ≤ »(«exprμH[ ]»(d) «expr ⁻¹' »(f, s), «expr * »(«expr ^ »(K, d), «exprμH[ ]»(d) s)) :=
begin
  rcases [expr eq_or_ne K 0, "with", ident rfl, "|", ident h0],
  { haveI [] [":", expr subsingleton X] [":=", expr hf.subsingleton],
    have [] [":", expr «expr ⁻¹' »(f, s).subsingleton] [],
    from [expr subsingleton_univ.mono (subset_univ _)],
    rw [expr this.measure_zero] [],
    exact [expr zero_le _] },
  have [ident hKd0] [":", expr «expr ≠ »(«expr ^ »((K : «exprℝ≥0∞»()), d), 0)] [],
  by simp [] [] [] ["[", expr h0, "]"] [] [],
  have [ident hKd] [":", expr «expr ≠ »(«expr ^ »((K : «exprℝ≥0∞»()), d), «expr∞»())] [],
  by simp [] [] [] ["[", expr hd, "]"] [] [],
  simp [] [] ["only"] ["[", expr hausdorff_measure_apply', ",", expr ennreal.mul_supr, ",", expr ennreal.mul_infi_of_ne hKd0 hKd, ",", "<-", expr ennreal.tsum_mul_left, "]"] [] [],
  refine [expr bsupr_le (λ ε ε0, _)],
  refine [expr le_bsupr_of_le «expr / »(ε, K) (by simp [] [] [] ["[", expr ε0.ne', "]"] [] []) _],
  refine [expr le_binfi (λ t hst, «expr $ »(le_infi, λ htε, _))],
  replace [ident hst] [":", expr «expr ⊆ »(«expr ⁻¹' »(f, s), _)] [":=", expr preimage_mono hst],
  rw [expr preimage_Union] ["at", ident hst],
  refine [expr binfi_le_of_le _ hst (infi_le_of_le (λ n, _) _)],
  { exact [expr (hf.ediam_preimage_le _).trans «expr $ »(ennreal.mul_le_of_le_div', htε n)] },
  { refine [expr ennreal.tsum_le_tsum (λ
      n, «expr $ »(supr_le, λ H, le_supr_of_le (λ h, «expr $ »(H, h.preimage hf.injective)) _))],
    rw ["[", "<-", expr ennreal.mul_rpow_of_nonneg _ _ hd, "]"] [],
    exact [expr ennreal.rpow_le_rpow (hf.ediam_preimage_le _) hd] }
end

theorem le_hausdorff_measure_image (hf : AntilipschitzWith K f) (hd : 0 ≤ d) (s : Set X) :
  μH[d] s ≤ (K^d)*μH[d] (f '' s) :=
  calc μH[d] s ≤ μH[d] (f ⁻¹' (f '' s)) := measure_mono (subset_preimage_image _ _)
    _ ≤ (K^d)*μH[d] (f '' s) := hf.hausdorff_measure_preimage_le hd (f '' s)
    

end AntilipschitzWith

/-!
### Isometries preserve the Hausdorff measure and Hausdorff dimension
-/


namespace Isometry

variable{f : X → Y}{d : ℝ}

theorem hausdorff_measure_image (hf : Isometry f) (hd : 0 ≤ d ∨ surjective f) (s : Set X) : μH[d] (f '' s) = μH[d] s :=
  by 
    simp only [hausdorff_measure, ←outer_measure.coe_mk_metric, ←outer_measure.comap_apply]
    rw [outer_measure.isometry_comap_mk_metric _ hf (hd.imp_left _)]
    exact fun hd x y hxy => Ennreal.rpow_le_rpow hxy hd

theorem hausdorff_measure_preimage (hf : Isometry f) (hd : 0 ≤ d ∨ surjective f) (s : Set Y) :
  μH[d] (f ⁻¹' s) = μH[d] (s ∩ range f) :=
  by 
    rw [←hf.hausdorff_measure_image hd, image_preimage_eq_inter_range]

theorem map_hausdorff_measure (hf : Isometry f) (hd : 0 ≤ d ∨ surjective f) :
  measure.map f μH[d] = μH[d].restrict (range f) :=
  by 
    ext1 s hs 
    rw [map_apply hf.continuous.measurable hs, restrict_apply hs, hf.hausdorff_measure_preimage hd]

end Isometry

namespace Isometric

@[simp]
theorem hausdorff_measure_image (e : X ≃ᵢ Y) (d : ℝ) (s : Set X) : μH[d] (e '' s) = μH[d] s :=
  e.isometry.hausdorff_measure_image (Or.inr e.surjective) s

@[simp]
theorem hausdorff_measure_preimage (e : X ≃ᵢ Y) (d : ℝ) (s : Set Y) : μH[d] (e ⁻¹' s) = μH[d] s :=
  by 
    rw [←e.image_symm, e.symm.hausdorff_measure_image]

end Isometric

