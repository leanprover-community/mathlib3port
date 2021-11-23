import Mathbin.MeasureTheory.Function.SimpleFuncDense

/-!
# Extension of a linear function from indicators to L1

Let `T : set α → E →L[ℝ] F` be additive for measurable sets with finite measure, in the sense that
for `s, t` two such sets, `s ∩ t = ∅ → T (s ∪ t) = T s + T t`. `T` is akin to a bilinear map on
`set α × E`, or a linear map on indicator functions.

This file constructs an extension of `T` to integrable simple functions, which are finite sums of
indicators of measurable sets with finite measure, then to integrable functions, which are limits of
integrable simple functions.

The main result is a continuous linear map `(α →₁[μ] E) →L[ℝ] F`. This extension process is used to
define the Bochner integral in the `measure_theory.integral.bochner` file and the conditional
expectation of an integrable function in `measure_theory.function.conditional_expectation`.

## Main Definitions

- `fin_meas_additive μ T`: the property that `T` is additive on measurable sets with finite measure.
  For two such sets, `s ∩ t = ∅ → T (s ∪ t) = T s + T t`.
- `dominated_fin_meas_additive μ T C`: `fin_meas_additive μ T ∧ ∀ s, ∥T s∥ ≤ C * (μ s).to_real`.
  This is the property needed to perform the extension from indicators to L1.
- `set_to_L1 (hT : dominated_fin_meas_additive μ T C) : (α →₁[μ] E) →L[ℝ] F`: the extension of `T`
  from indicators to L1.
- `set_to_fun (hT : dominated_fin_meas_additive μ T C) (f : α → E) : F`: a version of the extension
  which applies to functions (with value 0 if the function is not integrable).

## Implementation notes

The starting object `T : set α → E →L[ℝ] F` matters only through its restriction on measurable sets
with finite measure. Its value on other sets is ignored.

The extension step from integrable simple functions to L1 relies on a `second_countable_topology`
assumption. Without it, we could only extend to `ae_fin_strongly_measurable` functions. (TODO: this
might be worth doing?)

-/


noncomputable theory

open_locale Classical TopologicalSpace BigOperators Nnreal Ennreal MeasureTheory Pointwise

open Set Filter TopologicalSpace Ennreal Emetric

attribute [local instance] fact_one_le_one_ennreal

namespace MeasureTheory

variable{α E F F' G 𝕜 :
    Type
      _}{p :
    ℝ≥0∞}[NormedGroup
      E][MeasurableSpace
      E][NormedSpace ℝ
      E][NormedGroup
      F][NormedSpace ℝ
      F][NormedGroup F'][NormedSpace ℝ F'][NormedGroup G][MeasurableSpace G]{m : MeasurableSpace α}{μ : Measureₓ α}

local infixr:25 " →ₛ " => simple_func

open Finset

section FinMeasAdditive

/-- A set function is `fin_meas_additive` if its value on the union of two disjoint measurable
sets with finite measure is the sum of its values on each set. -/
def fin_meas_additive {β} [AddMonoidₓ β] {m : MeasurableSpace α} (μ : Measureₓ α) (T : Set α → β) : Prop :=
  ∀ s t, MeasurableSet s → MeasurableSet t → μ s ≠ ∞ → μ t ≠ ∞ → s ∩ t = ∅ → T (s ∪ t) = T s+T t

-- error in MeasureTheory.Integral.SetToL1: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_empty_eq_zero_of_map_union
{β}
[add_cancel_monoid β]
(T : set α → β)
(h_add : fin_meas_additive μ T) : «expr = »(T «expr∅»(), 0) :=
begin
  have [ident h_empty] [":", expr «expr ≠ »(μ «expr∅»(), «expr∞»())] [],
  from [expr (measure_empty.le.trans_lt ennreal.coe_lt_top).ne],
  specialize [expr h_add «expr∅»() «expr∅»() measurable_set.empty measurable_set.empty h_empty h_empty (set.inter_empty «expr∅»())],
  rw [expr set.union_empty] ["at", ident h_add],
  nth_rewrite [0] ["<-", expr add_zero (T «expr∅»())] ["at", ident h_add],
  exact [expr (add_left_cancel h_add).symm]
end

theorem map_Union_fin_meas_set_eq_sum {β} [AddCommMonoidₓ β] (T : Set α → β) (T_empty : T ∅ = 0)
  (h_add : fin_meas_additive μ T) {ι} (S : ι → Set α) (sι : Finset ι) (hS_meas : ∀ i, MeasurableSet (S i))
  (hSp : ∀ i _ : i ∈ sι, μ (S i) ≠ ∞) (h_disj : ∀ i j _ : i ∈ sι _ : j ∈ sι, i ≠ j → Disjoint (S i) (S j)) :
  T (⋃(i : _)(_ : i ∈ sι), S i) = ∑i in sι, T (S i) :=
  by 
    revert hSp h_disj 
    refine' Finset.induction_on sι _ _
    ·
      simp only [Finset.not_mem_empty, forall_false_left, Union_false, Union_empty, sum_empty, forall_2_true_iff,
        implies_true_iff, forall_true_left, not_false_iff, T_empty]
    intro a s has h hps h_disj 
    rw [Finset.sum_insert has, ←h]
    swap
    ·
      exact fun i hi => hps i (Finset.mem_insert_of_mem hi)
    swap
    ·
      exact fun i j hi hj hij => h_disj i j (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij 
    rw
      [←h_add (S a) (⋃(i : _)(_ : i ∈ s), S i) (hS_meas a) (measurable_set_bUnion _ fun i _ => hS_meas i)
        (hps a (Finset.mem_insert_self a s))]
    ·
      congr 
      convert Finset.supr_insert a s S
    ·
      exact
        ((measure_bUnion_finset_le _ _).trans_lt$ Ennreal.sum_lt_top$ fun i hi => hps i$ Finset.mem_insert_of_mem hi).Ne
    ·
      simpRw [Set.inter_Union]
      refine' Union_eq_empty.mpr fun i => Union_eq_empty.mpr fun hi => _ 
      rw [←Set.disjoint_iff_inter_eq_empty]
      refine' h_disj a i (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) fun hai => _ 
      rw [←hai] at hi 
      exact has hi

/-- A `fin_meas_additive` set function whose norm on every set is less than the measure of the
set (up to a multiplicative constant). -/
def dominated_fin_meas_additive {β} [NormedGroup β] {m : MeasurableSpace α} (μ : Measureₓ α) (T : Set α → β) (C : ℝ) :
  Prop :=
  fin_meas_additive μ T ∧ ∀ s, ∥T s∥ ≤ C*(μ s).toReal

end FinMeasAdditive

namespace SimpleFunc

/-- Extend `set α → (F →L[ℝ] F')` to `(α →ₛ F) → F'`. -/
def set_to_simple_func {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) : F' :=
  ∑x in f.range, T (f ⁻¹' {x}) x

@[simp]
theorem set_to_simple_func_zero {m : MeasurableSpace α} (f : α →ₛ F) :
  set_to_simple_func (0 : Set α → F →L[ℝ] F') f = 0 :=
  by 
    simp [set_to_simple_func]

@[simp]
theorem set_to_simple_func_zero_apply {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') :
  set_to_simple_func T (0 : α →ₛ F) = 0 :=
  by 
    cases' is_empty_or_nonempty α <;> simp [set_to_simple_func]

theorem set_to_simple_func_eq_sum_filter {m : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) :
  set_to_simple_func T f = ∑x in f.range.filter fun x => x ≠ 0, (T (f ⁻¹' {x})) x :=
  by 
    symm 
    refine' sum_filter_of_ne fun x hx => mt fun hx0 => _ 
    rw [hx0]
    exact ContinuousLinearMap.map_zero _

theorem set_to_simple_func_mono {G} [NormedLinearOrderedGroup G] [NormedSpace ℝ G] {m : MeasurableSpace α}
  (T : Set α → F →L[ℝ] G) (T' : Set α → F →L[ℝ] G) (hTT' : ∀ s x, T s x ≤ T' s x) (f : α →ₛ F) :
  set_to_simple_func T f ≤ set_to_simple_func T' f :=
  by 
    simpRw [set_to_simple_func]
    exact sum_le_sum fun i hi => hTT' _ i

-- error in MeasureTheory.Integral.SetToL1: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_set_to_simple_func
(T : set α → «expr →L[ ] »(F, exprℝ(), F'))
(h_add : fin_meas_additive μ T)
{f : «expr →ₛ »(α, G)}
(hf : integrable f μ)
{g : G → F}
(hg : «expr = »(g 0, 0)) : «expr = »((f.map g).set_to_simple_func T, «expr∑ in , »((x), f.range, T «expr ⁻¹' »(f, {x}) (g x))) :=
begin
  have [ident T_empty] [":", expr «expr = »(T «expr∅»(), 0)] [],
  from [expr map_empty_eq_zero_of_map_union T h_add],
  have [ident hfp] [":", expr ∀ x «expr ∈ » f.range, «expr ≠ »(x, 0) → «expr ≠ »(μ «expr ⁻¹' »(f, {x}), «expr∞»())] [],
  from [expr λ x hx hx0, (measure_preimage_lt_top_of_integrable f hf hx0).ne],
  simp [] [] ["only"] ["[", expr set_to_simple_func, ",", expr range_map, "]"] [] [],
  refine [expr finset.sum_image' _ (assume b hb, _)],
  rcases [expr mem_range.1 hb, "with", "⟨", ident a, ",", ident rfl, "⟩"],
  by_cases [expr h0, ":", expr «expr = »(g (f a), 0)],
  { simp_rw [expr h0] [],
    rw ["[", expr continuous_linear_map.map_zero, ",", expr finset.sum_eq_zero (λ x hx, _), "]"] [],
    rw [expr mem_filter] ["at", ident hx],
    rw ["[", expr hx.2, ",", expr continuous_linear_map.map_zero, "]"] [] },
  have [ident h_left_eq] [":", expr «expr = »(T «expr ⁻¹' »(map g f, {g (f a)}) (g (f a)), T «expr ⁻¹' »(f, «expr↑ »(f.range.filter (λ
       b, «expr = »(g b, g (f a))))) (g (f a)))] [],
  { congr,
    rw [expr map_preimage_singleton] [] },
  rw [expr h_left_eq] [],
  have [ident h_left_eq'] [":", expr «expr = »(T «expr ⁻¹' »(f, «expr↑ »(filter (λ
       b : G, «expr = »(g b, g (f a))) f.range)) (g (f a)), T «expr⋃ , »((y «expr ∈ » filter (λ
       b : G, «expr = »(g b, g (f a))) f.range), «expr ⁻¹' »(f, {y})) (g (f a)))] [],
  { congr,
    rw ["<-", expr finset.set_bUnion_preimage_singleton] [] },
  rw [expr h_left_eq'] [],
  rw [expr map_Union_fin_meas_set_eq_sum T T_empty h_add] [],
  { simp [] [] ["only"] ["[", expr filter_congr_decidable, ",", expr sum_apply, ",", expr continuous_linear_map.coe_sum', "]"] [] [],
    refine [expr finset.sum_congr rfl (λ x hx, _)],
    rw [expr mem_filter] ["at", ident hx],
    rw [expr hx.2] [] },
  { exact [expr λ i, measurable_set_fiber _ _] },
  { intros [ident i, ident hi],
    rw [expr mem_filter] ["at", ident hi],
    refine [expr hfp i hi.1 (λ hi0, _)],
    rw ["[", expr hi0, ",", expr hg, "]"] ["at", ident hi],
    exact [expr h0 hi.2.symm] },
  { intros [ident i, ident j, ident hi, ident hj, ident hij],
    rw [expr set.disjoint_iff] [],
    intros [ident x, ident hx],
    rw ["[", expr set.mem_inter_iff, ",", expr set.mem_preimage, ",", expr set.mem_preimage, ",", expr set.mem_singleton_iff, ",", expr set.mem_singleton_iff, "]"] ["at", ident hx],
    rw ["[", "<-", expr hx.1, ",", "<-", expr hx.2, "]"] ["at", ident hij],
    exact [expr absurd rfl hij] }
end

-- error in MeasureTheory.Integral.SetToL1: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem set_to_simple_func_congr'
(T : set α → «expr →L[ ] »(E, exprℝ(), F))
(h_add : fin_meas_additive μ T)
{f g : «expr →ₛ »(α, E)}
(hf : integrable f μ)
(hg : integrable g μ)
(h : ∀
 x
 y, «expr ≠ »(x, y) → «expr = »(T «expr ∩ »(«expr ⁻¹' »(f, {x}), «expr ⁻¹' »(g, {y})), 0)) : «expr = »(f.set_to_simple_func T, g.set_to_simple_func T) :=
show «expr = »(((pair f g).map prod.fst).set_to_simple_func T, ((pair f g).map prod.snd).set_to_simple_func T), from begin
  have [ident h_pair] [":", expr integrable (f.pair g) μ] [],
  from [expr integrable_pair hf hg],
  rw [expr map_set_to_simple_func T h_add h_pair prod.fst_zero] [],
  rw [expr map_set_to_simple_func T h_add h_pair prod.snd_zero] [],
  refine [expr finset.sum_congr rfl (λ p hp, _)],
  rcases [expr mem_range.1 hp, "with", "⟨", ident a, ",", ident rfl, "⟩"],
  by_cases [expr eq, ":", expr «expr = »(f a, g a)],
  { dsimp ["only"] ["[", expr pair_apply, "]"] [] [],
    rw [expr eq] [] },
  { have [] [":", expr «expr = »(T «expr ⁻¹' »(pair f g, {(f a, g a)}), 0)] [],
    { have [ident h_eq] [":", expr «expr = »(T «expr ⁻¹' »(«expr⇑ »(f.pair g), {(f a, g a)}), T «expr ∩ »(«expr ⁻¹' »(f, {f a}), «expr ⁻¹' »(g, {g a})))] [],
      { congr,
        rw [expr pair_preimage_singleton f g] [] },
      rw [expr h_eq] [],
      exact [expr h (f a) (g a) eq] },
    simp [] [] ["only"] ["[", expr this, ",", expr continuous_linear_map.zero_apply, ",", expr pair_apply, "]"] [] [] }
end

theorem set_to_simple_func_congr (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
  (h_add : fin_meas_additive μ T) {f g : α →ₛ E} (hf : integrable f μ) (h : f =ᵐ[μ] g) :
  f.set_to_simple_func T = g.set_to_simple_func T :=
  by 
    refine' set_to_simple_func_congr' T h_add hf ((integrable_congr h).mp hf) _ 
    refine' fun x y hxy => h_zero _ ((measurable_set_fiber f x).inter (measurable_set_fiber g y)) _ 
    rw [eventually_eq, ae_iff] at h 
    refine' measure_mono_null (fun z => _) h 
    simpRw [Set.mem_inter_iff, Set.mem_set_of_eq, Set.mem_preimage, Set.mem_singleton_iff]
    intro h 
    rwa [h.1, h.2]

theorem set_to_simple_func_add_left {m : MeasurableSpace α} (T T' : Set α → F →L[ℝ] F') {f : α →ₛ F} :
  set_to_simple_func (T+T') f = set_to_simple_func T f+set_to_simple_func T' f :=
  by 
    simpRw [set_to_simple_func, Pi.add_apply]
    pushCast 
    simpRw [Pi.add_apply, sum_add_distrib]

theorem set_to_simple_func_add_left' (T T' T'' : Set α → E →L[ℝ] F)
  (h_add : ∀ s, MeasurableSet s → μ s ≠ ∞ → T'' s = T s+T' s) {f : α →ₛ E} (hf : integrable f μ) :
  set_to_simple_func T'' f = set_to_simple_func T f+set_to_simple_func T' f :=
  by 
    simpRw [set_to_simple_func_eq_sum_filter]
    suffices  : ∀ x _ : x ∈ Filter (fun x : E => x ≠ 0) f.range, T'' (f ⁻¹' {x}) = T (f ⁻¹' {x})+T' (f ⁻¹' {x})
    ·
      rw [←sum_add_distrib]
      refine' Finset.sum_congr rfl fun x hx => _ 
      rw [this x hx]
      pushCast 
      rw [Pi.add_apply]
    intro x hx 
    refine' h_add (f ⁻¹' {x}) (measurable_set_preimage _ _) (measure_preimage_lt_top_of_integrable _ hf _).Ne 
    rw [mem_filter] at hx 
    exact hx.2

theorem set_to_simple_func_add (T : Set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T) {f g : α →ₛ E}
  (hf : integrable f μ) (hg : integrable g μ) :
  set_to_simple_func T (f+g) = set_to_simple_func T f+set_to_simple_func T g :=
  have hp_pair : integrable (f.pair g) μ := integrable_pair hf hg 
  calc set_to_simple_func T (f+g) = ∑x in (pair f g).range, T (pair f g ⁻¹' {x}) (x.fst+x.snd) :=
    by 
      rw [add_eq_map₂, map_set_to_simple_func T h_add hp_pair]
      simp 
    _ = ∑x in (pair f g).range, T (pair f g ⁻¹' {x}) x.fst+T (pair f g ⁻¹' {x}) x.snd :=
    Finset.sum_congr rfl$ fun a ha => ContinuousLinearMap.map_add _ _ _ 
    _ = (∑x in (pair f g).range, T (pair f g ⁻¹' {x}) x.fst)+∑x in (pair f g).range, T (pair f g ⁻¹' {x}) x.snd :=
    by 
      rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).setToSimpleFunc T+((pair f g).map Prod.snd).setToSimpleFunc T :=
    by 
      rw [map_set_to_simple_func T h_add hp_pair Prod.snd_zero, map_set_to_simple_func T h_add hp_pair Prod.fst_zero]
    

theorem set_to_simple_func_neg (T : Set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T) {f : α →ₛ E}
  (hf : integrable f μ) : set_to_simple_func T (-f) = -set_to_simple_func T f :=
  calc set_to_simple_func T (-f) = set_to_simple_func T (f.map Neg.neg) := rfl 
    _ = -set_to_simple_func T f :=
    by 
      rw [map_set_to_simple_func T h_add hf neg_zero, set_to_simple_func, ←sum_neg_distrib]
      exact Finset.sum_congr rfl fun x h => ContinuousLinearMap.map_neg _ _
    

theorem set_to_simple_func_sub (T : Set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T) {f g : α →ₛ E}
  (hf : integrable f μ) (hg : integrable g μ) :
  set_to_simple_func T (f - g) = set_to_simple_func T f - set_to_simple_func T g :=
  by 
    rw [sub_eq_add_neg, set_to_simple_func_add T h_add hf, set_to_simple_func_neg T h_add hg, sub_eq_add_neg]
    rw [integrable_iff] at hg⊢
    intro x hx_ne 
    change μ ((Neg.neg ∘ g) ⁻¹' {x}) < ∞
    rw [preimage_comp, neg_preimage, neg_singleton]
    refine' hg (-x) _ 
    simp [hx_ne]

theorem set_to_simple_func_smul_real (T : Set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T) (c : ℝ) {f : α →ₛ E}
  (hf : integrable f μ) : set_to_simple_func T (c • f) = c • set_to_simple_func T f :=
  calc set_to_simple_func T (c • f) = ∑x in f.range, T (f ⁻¹' {x}) (c • x) :=
    by 
      rw [smul_eq_map c f, map_set_to_simple_func T h_add hf]
      rw [smul_zero]
    _ = ∑x in f.range, c • T (f ⁻¹' {x}) x :=
    Finset.sum_congr rfl$
      fun b hb =>
        by 
          rw [ContinuousLinearMap.map_smul (T (f ⁻¹' {b})) c b]
    _ = c • set_to_simple_func T f :=
    by 
      simp only [set_to_simple_func, smul_sum, smul_smul, mul_commₓ]
    

theorem set_to_simple_func_smul {E} [MeasurableSpace E] [NormedGroup E] [NormedField 𝕜] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [NormedSpace 𝕜 F] (T : Set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) {f : α →ₛ E} (hf : integrable f μ) :
  set_to_simple_func T (c • f) = c • set_to_simple_func T f :=
  calc set_to_simple_func T (c • f) = ∑x in f.range, T (f ⁻¹' {x}) (c • x) :=
    by 
      rw [smul_eq_map c f, map_set_to_simple_func T h_add hf]
      rw [smul_zero]
    _ = ∑x in f.range, c • T (f ⁻¹' {x}) x :=
    Finset.sum_congr rfl$
      fun b hb =>
        by 
          rw [h_smul]
    _ = c • set_to_simple_func T f :=
    by 
      simp only [set_to_simple_func, smul_sum, smul_smul, mul_commₓ]
    

theorem norm_set_to_simple_func_le_sum_op_norm {m : MeasurableSpace α} (T : Set α → F' →L[ℝ] F) (f : α →ₛ F') :
  ∥f.set_to_simple_func T∥ ≤ ∑x in f.range, ∥T (f ⁻¹' {x})∥*∥x∥ :=
  calc ∥∑x in f.range, T (f ⁻¹' {x}) x∥ ≤ ∑x in f.range, ∥T (f ⁻¹' {x}) x∥ := norm_sum_le _ _ 
    _ ≤ ∑x in f.range, ∥T (f ⁻¹' {x})∥*∥x∥ :=
    by 
      refine' Finset.sum_le_sum fun b hb => _ 
      simpRw [ContinuousLinearMap.le_op_norm]
    

theorem norm_set_to_simple_func_le_sum_mul_norm (T : Set α → F →L[ℝ] F') {C : ℝ} (hT_norm : ∀ s, ∥T s∥ ≤ C*(μ s).toReal)
  (f : α →ₛ F) : ∥f.set_to_simple_func T∥ ≤ C*∑x in f.range, (μ (f ⁻¹' {x})).toReal*∥x∥ :=
  calc ∥f.set_to_simple_func T∥ ≤ ∑x in f.range, ∥T (f ⁻¹' {x})∥*∥x∥ := norm_set_to_simple_func_le_sum_op_norm T f 
    _ ≤ ∑x in f.range, (C*(μ (f ⁻¹' {x})).toReal)*∥x∥ :=
    by 
      refine' Finset.sum_le_sum fun b hb => _ 
      byCases' hb : ∥b∥ = 0
      ·
        rw [hb]
        simp 
      rw [_root_.mul_le_mul_right _]
      ·
        exact hT_norm _
      ·
        exact lt_of_le_of_neₓ (norm_nonneg _) (Ne.symm hb)
    _ ≤ C*∑x in f.range, (μ (f ⁻¹' {x})).toReal*∥x∥ :=
    by 
      simpRw [mul_sum, ←mul_assocₓ]
    

-- error in MeasureTheory.Integral.SetToL1: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem set_to_simple_func_indicator
(T : set α → «expr →L[ ] »(F, exprℝ(), F'))
(hT_empty : «expr = »(T «expr∅»(), 0))
{m : measurable_space α}
{s : set α}
(hs : measurable_set s)
(x : F) : «expr = »(simple_func.set_to_simple_func T (simple_func.piecewise s hs (simple_func.const α x) (simple_func.const α 0)), T s x) :=
begin
  by_cases [expr hs_empty, ":", expr «expr = »(s, «expr∅»())],
  { simp [] [] ["only"] ["[", expr hs_empty, ",", expr hT_empty, ",", expr continuous_linear_map.zero_apply, ",", expr piecewise_empty, ",", expr const_zero, ",", expr set_to_simple_func_zero_apply, "]"] [] [] },
  by_cases [expr hs_univ, ":", expr «expr = »(s, univ)],
  { casesI [expr hα, ":", expr is_empty_or_nonempty α] [],
    { refine [expr absurd _ hs_empty],
      haveI [] [":", expr subsingleton (set α)] [],
      by { unfold [ident set] [],
        apply_instance },
      exact [expr subsingleton.elim s «expr∅»()] },
    simp [] [] [] ["[", expr hs_univ, ",", expr set_to_simple_func, "]"] [] [] },
  simp_rw [expr set_to_simple_func] [],
  rw ["[", "<-", expr ne.def, ",", expr set.ne_empty_iff_nonempty, "]"] ["at", ident hs_empty],
  rw [expr range_indicator hs hs_empty hs_univ] [],
  by_cases [expr hx0, ":", expr «expr = »(x, 0)],
  { simp_rw [expr hx0] [],
    simp [] [] [] [] [] [] },
  rw [expr sum_insert] [],
  swap,
  { rw [expr finset.mem_singleton] [],
    exact [expr hx0] },
  rw ["[", expr sum_singleton, ",", expr (T _).map_zero, ",", expr add_zero, "]"] [],
  congr,
  simp [] [] ["only"] ["[", expr coe_piecewise, ",", expr piecewise_eq_indicator, ",", expr coe_const, ",", expr pi.const_zero, ",", expr piecewise_eq_indicator, "]"] [] [],
  rw ["[", expr indicator_preimage, ",", expr preimage_const_of_mem, "]"] [],
  swap,
  { exact [expr set.mem_singleton x] },
  rw ["[", "<-", expr pi.const_zero, ",", expr preimage_const_of_not_mem, "]"] [],
  swap,
  { rw [expr set.mem_singleton_iff] [],
    exact [expr ne.symm hx0] },
  simp [] [] [] [] [] []
end

end SimpleFunc

namespace L1

open AeEqFun Lp.SimpleFunc Lp

variable{α E μ}

namespace SimpleFunc

-- error in MeasureTheory.Integral.SetToL1: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_eq_sum_mul
[second_countable_topology G]
[borel_space G]
(f : «expr →₁ₛ[ ] »(α, μ, G)) : «expr = »(«expr∥ ∥»(f), «expr∑ in , »((x), (to_simple_func f).range, «expr * »((μ «expr ⁻¹' »(to_simple_func f, {x})).to_real, «expr∥ ∥»(x)))) :=
begin
  rw ["[", expr norm_to_simple_func, ",", expr snorm_one_eq_lintegral_nnnorm, "]"] [],
  have [ident h_eq] [] [":=", expr simple_func.map_apply (λ x, (nnnorm x : «exprℝ≥0∞»())) (to_simple_func f)],
  dsimp ["only"] [] [] ["at", ident h_eq],
  simp_rw ["<-", expr h_eq] [],
  rw ["[", expr simple_func.lintegral_eq_lintegral, ",", expr simple_func.map_lintegral, ",", expr ennreal.to_real_sum, "]"] [],
  { congr,
    ext1 [] [ident x],
    rw ["[", expr ennreal.to_real_mul, ",", expr mul_comm, ",", "<-", expr of_real_norm_eq_coe_nnnorm, ",", expr ennreal.to_real_of_real (norm_nonneg _), "]"] [] },
  { intros [ident x, ident hx],
    by_cases [expr hx0, ":", expr «expr = »(x, 0)],
    { rw [expr hx0] [],
      simp [] [] [] [] [] [] },
    { exact [expr ennreal.mul_ne_top ennreal.coe_ne_top (simple_func.measure_preimage_lt_top_of_integrable _ (simple_func.integrable f) hx0).ne] } }
end

section SetToL1s

variable[second_countable_topology E][BorelSpace E][NormedField 𝕜][NormedSpace 𝕜 E]

attribute [local instance] Lp.simple_func.module

attribute [local instance] Lp.simple_func.normed_space

/-- Extend `set α → (E →L[ℝ] F')` to `(α →₁ₛ[μ] E) → F'`. -/
def set_to_L1s (T : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) : F :=
  (to_simple_func f).setToSimpleFunc T

theorem set_to_L1s_eq_set_to_simple_func (T : Set α → E →L[ℝ] F) (f : α →₁ₛ[μ] E) :
  set_to_L1s T f = (to_simple_func f).setToSimpleFunc T :=
  rfl

theorem set_to_L1s_congr (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
  (h_add : fin_meas_additive μ T) {f g : α →₁ₛ[μ] E} (h : to_simple_func f =ᵐ[μ] to_simple_func g) :
  set_to_L1s T f = set_to_L1s T g :=
  simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable f) h

theorem set_to_L1s_add (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
  (h_add : fin_meas_additive μ T) (f g : α →₁ₛ[μ] E) : set_to_L1s T (f+g) = set_to_L1s T f+set_to_L1s T g :=
  by 
    simpRw [set_to_L1s]
    rw [←simple_func.set_to_simple_func_add T h_add (simple_func.integrable f) (simple_func.integrable g)]
    exact simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _) (add_to_simple_func f g)

theorem set_to_L1s_smul_real (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0)
  (h_add : fin_meas_additive μ T) (c : ℝ) (f : α →₁ₛ[μ] E) : set_to_L1s T (c • f) = c • set_to_L1s T f :=
  by 
    simpRw [set_to_L1s]
    rw [←simple_func.set_to_simple_func_smul_real T h_add c (simple_func.integrable f)]
    refine' simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _) _ 
    exact smul_to_simple_func c f

theorem set_to_L1s_smul {E} [NormedGroup E] [MeasurableSpace E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [second_countable_topology E] [BorelSpace E] [NormedSpace 𝕜 F] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜]
  (T : Set α → E →L[ℝ] F) (h_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0) (h_add : fin_meas_additive μ T)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) (f : α →₁ₛ[μ] E) :
  set_to_L1s T (c • f) = c • set_to_L1s T f :=
  by 
    simpRw [set_to_L1s]
    rw [←simple_func.set_to_simple_func_smul T h_add h_smul c (simple_func.integrable f)]
    refine' simple_func.set_to_simple_func_congr T h_zero h_add (simple_func.integrable _) _ 
    exact smul_to_simple_func c f

theorem norm_set_to_L1s_le (T : Set α → E →L[ℝ] F) {C : ℝ} (hT_norm : ∀ s, ∥T s∥ ≤ C*(μ s).toReal) (f : α →₁ₛ[μ] E) :
  ∥set_to_L1s T f∥ ≤ C*∥f∥ :=
  by 
    rw [set_to_L1s, norm_eq_sum_mul f]
    exact simple_func.norm_set_to_simple_func_le_sum_mul_norm T hT_norm _

-- error in MeasureTheory.Integral.SetToL1: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem set_to_L1s_indicator_const
{T : set α → «expr →L[ ] »(E, exprℝ(), F)}
{C : exprℝ()}
{s : set α}
(hT : dominated_fin_meas_additive μ T C)
(hs : measurable_set s)
(hμs : «expr ≠ »(μ s, «expr∞»()))
(x : E) : «expr = »(set_to_L1s T (simple_func.indicator_const 1 hs hμs x), T s x) :=
begin
  have [ident h_zero] [":", expr ∀ (s) (hs : measurable_set s) (hs_zero : «expr = »(μ s, 0)), «expr = »(T s, 0)] [],
  { refine [expr λ s hs hs0, norm_eq_zero.mp _],
    refine [expr le_antisymm ((hT.2 s).trans (le_of_eq _)) (norm_nonneg _)],
    rw ["[", expr hs0, ",", expr ennreal.zero_to_real, ",", expr mul_zero, "]"] [] },
  have [ident h_empty] [":", expr «expr = »(T «expr∅»(), 0)] [],
  from [expr h_zero «expr∅»() measurable_set.empty measure_empty],
  rw [expr set_to_L1s_eq_set_to_simple_func] [],
  refine [expr eq.trans _ (simple_func.set_to_simple_func_indicator T h_empty hs x)],
  refine [expr simple_func.set_to_simple_func_congr T h_zero hT.1 (simple_func.integrable _) _],
  exact [expr Lp.simple_func.to_simple_func_indicator_const hs hμs x]
end

variable[NormedSpace 𝕜 F][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

variable(α E μ 𝕜)

/-- Extend `set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[𝕜] F`. -/
def set_to_L1s_clm' {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : dominated_fin_meas_additive μ T C)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : (α →₁ₛ[μ] E) →L[𝕜] F :=
  have h_zero : ∀ s hs : MeasurableSet s hs_zero : μ s = 0, T s = 0 :=
    by 
      refine' fun s hs hs0 => norm_eq_zero.mp _ 
      refine' le_antisymmₓ ((hT.2 s).trans (le_of_eqₓ _)) (norm_nonneg _)
      rw [hs0, Ennreal.zero_to_real, mul_zero]
  LinearMap.mkContinuous ⟨set_to_L1s T, set_to_L1s_add T h_zero hT.1, set_to_L1s_smul T h_zero hT.1 h_smul⟩ C
    fun f => norm_set_to_L1s_le T hT.2 f

/-- Extend `set α → E →L[ℝ] F` to `(α →₁ₛ[μ] E) →L[ℝ] F`. -/
def set_to_L1s_clm {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : dominated_fin_meas_additive μ T C) : (α →₁ₛ[μ] E) →L[ℝ] F :=
  have h_zero : ∀ s hs : MeasurableSet s hs_zero : μ s = 0, T s = 0 :=
    by 
      refine' fun s hs hs0 => norm_eq_zero.mp _ 
      refine' le_antisymmₓ ((hT.2 s).trans (le_of_eqₓ _)) (norm_nonneg _)
      rw [hs0, Ennreal.zero_to_real, mul_zero]
  LinearMap.mkContinuous ⟨set_to_L1s T, set_to_L1s_add T h_zero hT.1, set_to_L1s_smul_real T h_zero hT.1⟩ C
    fun f => norm_set_to_L1s_le T hT.2 f

variable{α E μ 𝕜}

theorem norm_set_to_L1s_clm_le {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : dominated_fin_meas_additive μ T C) (hC : 0 ≤ C) :
  ∥set_to_L1s_clm α E μ hT∥ ≤ C :=
  LinearMap.mk_continuous_norm_le _ hC _

theorem norm_set_to_L1s_clm_le' {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : dominated_fin_meas_additive μ T C) :
  ∥set_to_L1s_clm α E μ hT∥ ≤ max C 0 :=
  LinearMap.mk_continuous_norm_le' _ _

end SetToL1s

end SimpleFunc

open SimpleFunc

section SetToL1

attribute [local instance] Lp.simple_func.module

attribute [local instance] Lp.simple_func.normed_space

variable(𝕜)[NondiscreteNormedField
      𝕜][MeasurableSpace
      𝕜][OpensMeasurableSpace
      𝕜][second_countable_topology
      E][BorelSpace E][NormedSpace 𝕜 E][NormedSpace 𝕜 F][CompleteSpace F]{T : Set α → E →L[ℝ] F}{C : ℝ}

/-- Extend `set α → (E →L[ℝ] F)` to `(α →₁[μ] E) →L[𝕜] F`. -/
def set_to_L1' (hT : dominated_fin_meas_additive μ T C) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) :
  (α →₁[μ] E) →L[𝕜] F :=
  (set_to_L1s_clm' α E 𝕜 μ hT h_smul).extend (coe_to_Lp α E 𝕜) (simple_func.dense_range one_ne_top)
    simple_func.uniform_inducing

variable{𝕜}

/-- Extend `set α → E →L[ℝ] F` to `(α →₁[μ] E) →L[ℝ] F`. -/
def set_to_L1 (hT : dominated_fin_meas_additive μ T C) : (α →₁[μ] E) →L[ℝ] F :=
  (set_to_L1s_clm α E μ hT).extend (coe_to_Lp α E ℝ) (simple_func.dense_range one_ne_top) simple_func.uniform_inducing

theorem set_to_L1_eq_set_to_L1s_clm (hT : dominated_fin_meas_additive μ T C) (f : α →₁ₛ[μ] E) :
  set_to_L1 hT f = set_to_L1s_clm α E μ hT f :=
  uniformly_extend_of_ind simple_func.uniform_inducing (simple_func.dense_range one_ne_top)
    (set_to_L1s_clm α E μ hT).UniformContinuous _

theorem set_to_L1_eq_set_to_L1' (hT : dominated_fin_meas_additive μ T C)
  (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : α →₁[μ] E) : set_to_L1 hT f = set_to_L1' 𝕜 hT h_smul f :=
  rfl

theorem set_to_L1_smul (hT : dominated_fin_meas_additive μ T C) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x)
  (c : 𝕜) (f : α →₁[μ] E) : set_to_L1 hT (c • f) = c • set_to_L1 hT f :=
  by 
    rw [set_to_L1_eq_set_to_L1' hT h_smul, set_to_L1_eq_set_to_L1' hT h_smul]
    exact ContinuousLinearMap.map_smul _ _ _

theorem set_to_L1_indicator_const_Lp (hT : dominated_fin_meas_additive μ T C) {s : Set α} (hs : MeasurableSet s)
  (hμs : μ s ≠ ∞) (x : E) : set_to_L1 hT (indicator_const_Lp 1 hs hμs x) = T s x :=
  by 
    rw [←Lp.simple_func.coe_indicator_const hs hμs x, set_to_L1_eq_set_to_L1s_clm]
    exact set_to_L1s_indicator_const hT hs hμs x

theorem norm_set_to_L1_le_norm_set_to_L1s_clm (hT : dominated_fin_meas_additive μ T C) :
  ∥set_to_L1 hT∥ ≤ ∥set_to_L1s_clm α E μ hT∥ :=
  calc ∥set_to_L1 hT∥ ≤ (1 :  ℝ≥0 )*∥set_to_L1s_clm α E μ hT∥ :=
    by 
      refine'
        ContinuousLinearMap.op_norm_extend_le (set_to_L1s_clm α E μ hT) (coe_to_Lp α E ℝ)
          (simple_func.dense_range one_ne_top) fun x => le_of_eqₓ _ 
      rw [Nnreal.coe_one, one_mulₓ]
      rfl 
    _ = ∥set_to_L1s_clm α E μ hT∥ :=
    by 
      rw [Nnreal.coe_one, one_mulₓ]
    

theorem norm_set_to_L1_le_mul_norm (hT : dominated_fin_meas_additive μ T C) (hC : 0 ≤ C) (f : α →₁[μ] E) :
  ∥set_to_L1 hT f∥ ≤ C*∥f∥ :=
  calc ∥set_to_L1 hT f∥ ≤ ∥set_to_L1s_clm α E μ hT∥*∥f∥ :=
    ContinuousLinearMap.le_of_op_norm_le _ (norm_set_to_L1_le_norm_set_to_L1s_clm hT) _ 
    _ ≤ C*∥f∥ := mul_le_mul (norm_set_to_L1s_clm_le hT hC) le_rfl (norm_nonneg _) hC
    

theorem norm_set_to_L1_le_mul_norm' (hT : dominated_fin_meas_additive μ T C) (f : α →₁[μ] E) :
  ∥set_to_L1 hT f∥ ≤ max C 0*∥f∥ :=
  calc ∥set_to_L1 hT f∥ ≤ ∥set_to_L1s_clm α E μ hT∥*∥f∥ :=
    ContinuousLinearMap.le_of_op_norm_le _ (norm_set_to_L1_le_norm_set_to_L1s_clm hT) _ 
    _ ≤ max C 0*∥f∥ := mul_le_mul (norm_set_to_L1s_clm_le' hT) le_rfl (norm_nonneg _) (le_max_rightₓ _ _)
    

theorem norm_set_to_L1_le (hT : dominated_fin_meas_additive μ T C) (hC : 0 ≤ C) : ∥set_to_L1 hT∥ ≤ C :=
  ContinuousLinearMap.op_norm_le_bound _ hC (norm_set_to_L1_le_mul_norm hT hC)

theorem norm_set_to_L1_le' (hT : dominated_fin_meas_additive μ T C) : ∥set_to_L1 hT∥ ≤ max C 0 :=
  ContinuousLinearMap.op_norm_le_bound _ (le_max_rightₓ _ _) (norm_set_to_L1_le_mul_norm' hT)

theorem set_to_L1_lipschitz (hT : dominated_fin_meas_additive μ T C) : LipschitzWith (Real.toNnreal C) (set_to_L1 hT) :=
  (set_to_L1 hT).lipschitz.weaken (norm_set_to_L1_le' hT)

/-- If `fs i → f` in `L1`, then `set_to_L1 hT (fs i) → set_to_L1 hT f`. -/
theorem tendsto_set_to_L1 (hT : dominated_fin_meas_additive μ T C) (f : α →₁[μ] E) {ι} (fs : ι → α →₁[μ] E)
  {l : Filter ι} (hfs : tendsto fs l (𝓝 f)) : tendsto (fun i => set_to_L1 hT (fs i)) l (𝓝$ set_to_L1 hT f) :=
  ((set_to_L1 hT).Continuous.Tendsto _).comp hfs

end SetToL1

end L1

section Function

variable[second_countable_topology E][BorelSpace E][CompleteSpace F]{T : Set α → E →L[ℝ] F}{C : ℝ}{f g : α → E}

/-- Extend `T : set α → E →L[ℝ] F` to `(α → E) → F` (for integrable functions `α → E`). We set it to
0 if the function is not integrable. -/
def set_to_fun (hT : dominated_fin_meas_additive μ T C) (f : α → E) : F :=
  if hf : integrable f μ then L1.set_to_L1 hT (hf.to_L1 f) else 0

theorem set_to_fun_eq (hT : dominated_fin_meas_additive μ T C) (hf : integrable f μ) :
  set_to_fun hT f = L1.set_to_L1 hT (hf.to_L1 f) :=
  dif_pos hf

theorem L1.set_to_fun_eq_set_to_L1 (hT : dominated_fin_meas_additive μ T C) (f : α →₁[μ] E) :
  set_to_fun hT f = L1.set_to_L1 hT f :=
  by 
    rw [set_to_fun_eq hT (L1.integrable_coe_fn f), integrable.to_L1_coe_fn]

theorem set_to_fun_undef (hT : dominated_fin_meas_additive μ T C) (hf : ¬integrable f μ) : set_to_fun hT f = 0 :=
  dif_neg hf

theorem set_to_fun_non_ae_measurable (hT : dominated_fin_meas_additive μ T C) (hf : ¬AeMeasurable f μ) :
  set_to_fun hT f = 0 :=
  set_to_fun_undef hT (not_and_of_not_left _ hf)

@[simp]
theorem set_to_fun_zero (hT : dominated_fin_meas_additive μ T C) : set_to_fun hT (0 : α → E) = 0 :=
  by 
    rw [set_to_fun_eq hT]
    ·
      simp only [integrable.to_L1_zero, ContinuousLinearMap.map_zero]
    ·
      exact integrable_zero _ _ _

theorem set_to_fun_add (hT : dominated_fin_meas_additive μ T C) (hf : integrable f μ) (hg : integrable g μ) :
  set_to_fun hT (f+g) = set_to_fun hT f+set_to_fun hT g :=
  by 
    rw [set_to_fun_eq hT (hf.add hg), set_to_fun_eq hT hf, set_to_fun_eq hT hg, integrable.to_L1_add,
      (L1.set_to_L1 hT).map_add]

theorem set_to_fun_neg (hT : dominated_fin_meas_additive μ T C) (f : α → E) : set_to_fun hT (-f) = -set_to_fun hT f :=
  by 
    byCases' hf : integrable f μ
    ·
      rw [set_to_fun_eq hT hf, set_to_fun_eq hT hf.neg, integrable.to_L1_neg, (L1.set_to_L1 hT).map_neg]
    ·
      rw [set_to_fun_undef hT hf, set_to_fun_undef hT, neg_zero]
      rwa [←integrable_neg_iff] at hf

theorem set_to_fun_sub (hT : dominated_fin_meas_additive μ T C) (hf : integrable f μ) (hg : integrable g μ) :
  set_to_fun hT (f - g) = set_to_fun hT f - set_to_fun hT g :=
  by 
    rw [sub_eq_add_neg, sub_eq_add_neg, set_to_fun_add hT hf hg.neg, set_to_fun_neg hT g]

-- error in MeasureTheory.Integral.SetToL1: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem set_to_fun_smul
[nondiscrete_normed_field 𝕜]
[measurable_space 𝕜]
[opens_measurable_space 𝕜]
[normed_space 𝕜 E]
[normed_space 𝕜 F]
(hT : dominated_fin_meas_additive μ T C)
(h_smul : ∀ c : 𝕜, ∀ s x, «expr = »(T s «expr • »(c, x), «expr • »(c, T s x)))
(c : 𝕜)
(f : α → E) : «expr = »(set_to_fun hT «expr • »(c, f), «expr • »(c, set_to_fun hT f)) :=
begin
  by_cases [expr hf, ":", expr integrable f μ],
  { rw ["[", expr set_to_fun_eq hT hf, ",", expr set_to_fun_eq hT, ",", expr integrable.to_L1_smul', ",", expr L1.set_to_L1_smul hT h_smul c _, "]"] [] },
  { by_cases [expr hr, ":", expr «expr = »(c, 0)],
    { rw [expr hr] [],
      simp [] [] [] [] [] [] },
    { have [ident hf'] [":", expr «expr¬ »(integrable «expr • »(c, f) μ)] [],
      by rwa ["[", expr integrable_smul_iff hr f, "]"] [],
      rw ["[", expr set_to_fun_undef hT hf, ",", expr set_to_fun_undef hT hf', ",", expr smul_zero, "]"] [] } }
end

-- error in MeasureTheory.Integral.SetToL1: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem set_to_fun_congr_ae
(hT : dominated_fin_meas_additive μ T C)
(h : «expr =ᵐ[ ] »(f, μ, g)) : «expr = »(set_to_fun hT f, set_to_fun hT g) :=
begin
  by_cases [expr hfi, ":", expr integrable f μ],
  { have [ident hgi] [":", expr integrable g μ] [":=", expr hfi.congr h],
    rw ["[", expr set_to_fun_eq hT hfi, ",", expr set_to_fun_eq hT hgi, ",", expr (integrable.to_L1_eq_to_L1_iff f g hfi hgi).2 h, "]"] [] },
  { have [ident hgi] [":", expr «expr¬ »(integrable g μ)] [],
    { rw [expr integrable_congr h] ["at", ident hfi],
      exact [expr hfi] },
    rw ["[", expr set_to_fun_undef hT hfi, ",", expr set_to_fun_undef hT hgi, "]"] [] }
end

theorem set_to_fun_to_L1 (hT : dominated_fin_meas_additive μ T C) (hf : integrable f μ) :
  set_to_fun hT (hf.to_L1 f) = set_to_fun hT f :=
  set_to_fun_congr_ae hT hf.coe_fn_to_L1

theorem set_to_fun_indicator_const (hT : dominated_fin_meas_additive μ T C) {s : Set α} (hs : MeasurableSet s)
  (hμs : μ s ≠ ∞) (x : E) : set_to_fun hT (s.indicator fun _ => x) = T s x :=
  by 
    rw [set_to_fun_congr_ae hT (@indicator_const_Lp_coe_fn _ _ _ 1 _ _ _ _ hs hμs x _ _).symm]
    rw [L1.set_to_fun_eq_set_to_L1 hT]
    exact L1.set_to_L1_indicator_const_Lp hT hs hμs x

@[continuity]
theorem continuous_set_to_fun (hT : dominated_fin_meas_additive μ T C) :
  Continuous fun f : α →₁[μ] E => set_to_fun hT f :=
  by 
    simpRw [L1.set_to_fun_eq_set_to_L1 hT]
    exact ContinuousLinearMap.continuous _

theorem norm_set_to_fun_le_mul_norm (hT : dominated_fin_meas_additive μ T C) (f : α →₁[μ] E) (hC : 0 ≤ C) :
  ∥set_to_fun hT f∥ ≤ C*∥f∥ :=
  by 
    rw [L1.set_to_fun_eq_set_to_L1]
    exact L1.norm_set_to_L1_le_mul_norm hT hC f

theorem norm_set_to_fun_le_mul_norm' (hT : dominated_fin_meas_additive μ T C) (f : α →₁[μ] E) :
  ∥set_to_fun hT f∥ ≤ max C 0*∥f∥ :=
  by 
    rw [L1.set_to_fun_eq_set_to_L1]
    exact L1.norm_set_to_L1_le_mul_norm' hT f

theorem norm_set_to_fun_le (hT : dominated_fin_meas_additive μ T C) (hf : integrable f μ) (hC : 0 ≤ C) :
  ∥set_to_fun hT f∥ ≤ C*∥hf.to_L1 f∥ :=
  by 
    rw [set_to_fun_eq hT hf]
    exact L1.norm_set_to_L1_le_mul_norm hT hC _

theorem norm_set_to_fun_le' (hT : dominated_fin_meas_additive μ T C) (hf : integrable f μ) :
  ∥set_to_fun hT f∥ ≤ max C 0*∥hf.to_L1 f∥ :=
  by 
    rw [set_to_fun_eq hT hf]
    exact L1.norm_set_to_L1_le_mul_norm' hT _

-- error in MeasureTheory.Integral.SetToL1: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Lebesgue dominated convergence theorem provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their image by
  `set_to_fun`.
  We could weaken the condition `bound_integrable` to require `has_finite_integral bound μ` instead
  (i.e. not requiring that `bound` is measurable), but in all applications proving integrability
  is easier. -/
theorem tendsto_set_to_fun_of_dominated_convergence
(hT : dominated_fin_meas_additive μ T C)
{fs : exprℕ() → α → E}
{f : α → E}
(bound : α → exprℝ())
(fs_measurable : ∀ n, ae_measurable (fs n) μ)
(bound_integrable : integrable bound μ)
(h_bound : ∀ n, «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(«expr∥ ∥»(fs n a), bound a)))
(h_lim : «expr∀ᵐ ∂ , »((a), μ, tendsto (λ
   n, fs n a) at_top (expr𝓝() (f a)))) : tendsto (λ
 n, set_to_fun hT (fs n)) at_top «expr $ »(expr𝓝(), set_to_fun hT f) :=
begin
  have [ident f_measurable] [":", expr ae_measurable f μ] [":=", expr ae_measurable_of_tendsto_metric_ae fs_measurable h_lim],
  have [ident fs_int] [":", expr ∀
   n, integrable (fs n) μ] [":=", expr λ n, bound_integrable.mono' (fs_measurable n) (h_bound _)],
  have [ident f_int] [":", expr integrable f μ] [":=", expr ⟨f_measurable, has_finite_integral_of_dominated_convergence bound_integrable.has_finite_integral h_bound h_lim⟩],
  suffices [] [":", expr tendsto (λ
    n, L1.set_to_L1 hT ((fs_int n).to_L1 (fs n))) at_top (expr𝓝() (L1.set_to_L1 hT (f_int.to_L1 f)))],
  { convert [] [expr this] [],
    { ext1 [] [ident n],
      exact [expr set_to_fun_eq hT (fs_int n)] },
    { exact [expr set_to_fun_eq hT f_int] } },
  refine [expr L1.tendsto_set_to_L1 hT _ _ _],
  rw [expr tendsto_iff_norm_tendsto_zero] [],
  have [ident lintegral_norm_tendsto_zero] [":", expr tendsto (λ
    n, «expr $ »(ennreal.to_real, «expr∫⁻ , ∂ »((a), ennreal.of_real «expr∥ ∥»(«expr - »(fs n a, f a)), μ))) at_top (expr𝓝() 0)] [":=", expr (tendsto_to_real zero_ne_top).comp (tendsto_lintegral_norm_of_dominated_convergence fs_measurable bound_integrable.has_finite_integral h_bound h_lim)],
  convert [] [expr lintegral_norm_tendsto_zero] [],
  ext1 [] [ident n],
  rw [expr L1.norm_def] [],
  congr' [1] [],
  refine [expr lintegral_congr_ae _],
  rw ["<-", expr integrable.to_L1_sub] [],
  refine [expr ((fs_int n).sub f_int).coe_fn_to_L1.mono (λ x hx, _)],
  dsimp ["only"] [] [] [],
  rw ["[", expr hx, ",", expr of_real_norm_eq_coe_nnnorm, ",", expr pi.sub_apply, "]"] []
end

-- error in MeasureTheory.Integral.SetToL1: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
theorem tendsto_set_to_fun_filter_of_dominated_convergence
(hT : dominated_fin_meas_additive μ T C)
{ι}
{l : _root_.filter ι}
[l.is_countably_generated]
{fs : ι → α → E}
{f : α → E}
(bound : α → exprℝ())
(hfs_meas : «expr∀ᶠ in , »((n), l, ae_measurable (fs n) μ))
(h_bound : «expr∀ᶠ in , »((n), l, «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(«expr∥ ∥»(fs n a), bound a))))
(bound_integrable : integrable bound μ)
(h_lim : «expr∀ᵐ ∂ , »((a), μ, tendsto (λ
   n, fs n a) l (expr𝓝() (f a)))) : tendsto (λ n, set_to_fun hT (fs n)) l «expr $ »(expr𝓝(), set_to_fun hT f) :=
begin
  rw [expr tendsto_iff_seq_tendsto] [],
  intros [ident x, ident xl],
  have [ident hxl] [":", expr ∀ s «expr ∈ » l, «expr∃ , »((a), ∀ b «expr ≥ » a, «expr ∈ »(x b, s))] [],
  by { rwa [expr tendsto_at_top'] ["at", ident xl] },
  have [ident h] [":", expr «expr ∈ »(«expr ∩ »({x : ι | λ
     n, ae_measurable (fs n) μ x}, {x : ι | λ
     n, «expr∀ᵐ ∂ , »((a), μ, «expr ≤ »(«expr∥ ∥»(fs n a), bound a)) x}), l)] [],
  from [expr inter_mem hfs_meas h_bound],
  obtain ["⟨", ident k, ",", ident h, "⟩", ":=", expr hxl _ h],
  rw ["<-", expr tendsto_add_at_top_iff_nat k] [],
  refine [expr tendsto_set_to_fun_of_dominated_convergence hT bound _ bound_integrable _ _],
  { exact [expr λ n, (h _ (self_le_add_left _ _)).1] },
  { exact [expr λ n, (h _ (self_le_add_left _ _)).2] },
  { filter_upwards ["[", expr h_lim, "]"] [],
    refine [expr λ a h_lin, @tendsto.comp _ _ _ (λ n, x «expr + »(n, k)) (λ n, fs n a) _ _ _ h_lin _],
    rw [expr tendsto_add_at_top_iff_nat] [],
    assumption }
end

variable{X : Type _}[TopologicalSpace X][first_countable_topology X]

theorem continuous_at_set_to_fun_of_dominated (hT : dominated_fin_meas_additive μ T C) {fs : X → α → E} {x₀ : X}
  {bound : α → ℝ} (hfs_meas : ∀ᶠx in 𝓝 x₀, AeMeasurable (fs x) μ) (h_bound : ∀ᶠx in 𝓝 x₀, ∀ᵐa ∂μ, ∥fs x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐa ∂μ, ContinuousAt (fun x => fs x a) x₀) :
  ContinuousAt (fun x => set_to_fun hT (fs x)) x₀ :=
  tendsto_set_to_fun_filter_of_dominated_convergence hT bound ‹_› ‹_› ‹_› ‹_›

theorem continuous_set_to_fun_of_dominated (hT : dominated_fin_meas_additive μ T C) {fs : X → α → E} {bound : α → ℝ}
  (hfs_meas : ∀ x, AeMeasurable (fs x) μ) (h_bound : ∀ x, ∀ᵐa ∂μ, ∥fs x a∥ ≤ bound a)
  (bound_integrable : integrable bound μ) (h_cont : ∀ᵐa ∂μ, Continuous fun x => fs x a) :
  Continuous fun x => set_to_fun hT (fs x) :=
  continuous_iff_continuous_at.mpr
    fun x₀ =>
      continuous_at_set_to_fun_of_dominated hT (eventually_of_forall hfs_meas) (eventually_of_forall h_bound) ‹_›$
        h_cont.mono$ fun _ => Continuous.continuous_at

end Function

end MeasureTheory

