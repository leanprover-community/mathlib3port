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
define the Bochner integral in the `bochner` file. It will also be used to define the conditional
expectation of an integrable function (TODO).

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

theorem map_empty_eq_zero_of_map_union {β} [AddCancelMonoid β] (T : Set α → β) (h_add : fin_meas_additive μ T) :
  T ∅ = 0 :=
  by 
    have h_empty : μ ∅ ≠ ∞
    exact (measure_empty.le.trans_lt Ennreal.coe_lt_top).Ne 
    specialize h_add ∅ ∅ MeasurableSet.empty MeasurableSet.empty h_empty h_empty (Set.inter_empty ∅)
    rw [Set.union_empty] at h_add 
    nthRw 0[←add_zeroₓ (T ∅)]  at h_add 
    exact (add_left_cancelₓ h_add).symm

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
    casesI is_empty_or_nonempty α <;> simp [set_to_simple_func]

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

theorem map_set_to_simple_func (T : Set α → F →L[ℝ] F') (h_add : fin_meas_additive μ T) {f : α →ₛ G}
  (hf : integrable f μ) {g : G → F} (hg : g 0 = 0) : (f.map g).setToSimpleFunc T = ∑x in f.range, T (f ⁻¹' {x}) (g x) :=
  by 
    have T_empty : T ∅ = 0 
    exact map_empty_eq_zero_of_map_union T h_add 
    have hfp : ∀ x _ : x ∈ f.range, x ≠ 0 → μ (f ⁻¹' {x}) ≠ ∞
    exact fun x hx hx0 => (measure_preimage_lt_top_of_integrable f hf hx0).Ne 
    simp only [set_to_simple_func, range_map]
    refine' Finset.sum_image' _ fun b hb => _ 
    rcases mem_range.1 hb with ⟨a, rfl⟩
    byCases' h0 : g (f a) = 0
    ·
      simpRw [h0]
      rw [ContinuousLinearMap.map_zero, Finset.sum_eq_zero fun x hx => _]
      rw [mem_filter] at hx 
      rw [hx.2, ContinuousLinearMap.map_zero]
    have h_left_eq :
      T (map g f ⁻¹' {g (f a)}) (g (f a)) = T (f ⁻¹' «expr↑ » (f.range.filter fun b => g b = g (f a))) (g (f a))
    ·
      congr 
      rw [map_preimage_singleton]
    rw [h_left_eq]
    have h_left_eq' :
      T (f ⁻¹' «expr↑ » (Filter (fun b : G => g b = g (f a)) f.range)) (g (f a)) =
        T (⋃(y : _)(_ : y ∈ Filter (fun b : G => g b = g (f a)) f.range), f ⁻¹' {y}) (g (f a))
    ·
      congr 
      rw [←Finset.set_bUnion_preimage_singleton]
    rw [h_left_eq']
    rw [map_Union_fin_meas_set_eq_sum T T_empty h_add]
    ·
      simp only [filter_congr_decidable, sum_apply, ContinuousLinearMap.coe_sum']
      refine' Finset.sum_congr rfl fun x hx => _ 
      rw [mem_filter] at hx 
      rw [hx.2]
    ·
      exact fun i => measurable_set_fiber _ _
    ·
      intro i hi 
      rw [mem_filter] at hi 
      refine' hfp i hi.1 fun hi0 => _ 
      rw [hi0, hg] at hi 
      exact h0 hi.2.symm
    ·
      intro i j hi hj hij 
      rw [Set.disjoint_iff]
      intro x hx 
      rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff] at hx 
      rw [←hx.1, ←hx.2] at hij 
      exact absurd rfl hij

theorem set_to_simple_func_congr' (T : Set α → E →L[ℝ] F) (h_add : fin_meas_additive μ T) {f g : α →ₛ E}
  (hf : integrable f μ) (hg : integrable g μ) (h : ∀ x y, x ≠ y → T (f ⁻¹' {x} ∩ g ⁻¹' {y}) = 0) :
  f.set_to_simple_func T = g.set_to_simple_func T :=
  show ((pair f g).map Prod.fst).setToSimpleFunc T = ((pair f g).map Prod.snd).setToSimpleFunc T from
    by 
      have h_pair : integrable (f.pair g) μ 
      exact integrable_pair hf hg 
      rw [map_set_to_simple_func T h_add h_pair Prod.fst_zero]
      rw [map_set_to_simple_func T h_add h_pair Prod.snd_zero]
      refine' Finset.sum_congr rfl fun p hp => _ 
      rcases mem_range.1 hp with ⟨a, rfl⟩
      byCases' eq : f a = g a
      ·
        dsimp only [pair_apply]
        rw [Eq]
      ·
        have  : T (pair f g ⁻¹' {(f a, g a)}) = 0
        ·
          have h_eq : T («expr⇑ » (f.pair g) ⁻¹' {(f a, g a)}) = T (f ⁻¹' {f a} ∩ g ⁻¹' {g a})
          ·
            congr 
            rw [pair_preimage_singleton f g]
          rw [h_eq]
          exact h (f a) (g a) Eq 
        simp only [this, ContinuousLinearMap.zero_apply, pair_apply]

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
    

theorem set_to_simple_func_indicator (T : Set α → F →L[ℝ] F') (hT_empty : T ∅ = 0) {m : MeasurableSpace α} {s : Set α}
  (hs : MeasurableSet s) (x : F) :
  simple_func.set_to_simple_func T (simple_func.piecewise s hs (simple_func.const α x) (simple_func.const α 0)) =
    T s x :=
  by 
    byCases' hs_empty : s = ∅
    ·
      simp only [hs_empty, hT_empty, ContinuousLinearMap.zero_apply, piecewise_empty, const_zero,
        set_to_simple_func_zero_apply]
    byCases' hs_univ : s = univ
    ·
      casesI hα : is_empty_or_nonempty α
      ·
        refine' absurd _ hs_empty 
        haveI  : Subsingleton (Set α)
        ·
          ·
            unfold Set 
            infer_instance 
        exact Subsingleton.elimₓ s ∅
      simp [hs_univ, set_to_simple_func]
    simpRw [set_to_simple_func]
    rw [←Ne.def, Set.ne_empty_iff_nonempty] at hs_empty 
    rw [range_indicator hs hs_empty hs_univ]
    byCases' hx0 : x = 0
    ·
      simpRw [hx0]
      simp 
    rw [sum_insert]
    swap
    ·
      rw [Finset.mem_singleton]
      exact hx0 
    rw [sum_singleton, (T _).map_zero, add_zeroₓ]
    congr 
    simp only [coe_piecewise, piecewise_eq_indicator, coe_const, Pi.const_zero, piecewise_eq_indicator]
    rw [indicator_preimage, preimage_const_of_mem]
    swap
    ·
      exact Set.mem_singleton x 
    rw [←Pi.const_zero, preimage_const_of_not_mem]
    swap
    ·
      rw [Set.mem_singleton_iff]
      exact Ne.symm hx0 
    simp 

end SimpleFunc

namespace L1

open AeEqFun Lp.SimpleFunc Lp

variable{α E μ}

namespace SimpleFunc

theorem norm_eq_sum_mul [second_countable_topology G] [BorelSpace G] (f : α →₁ₛ[μ] G) :
  ∥f∥ = ∑x in (to_simple_func f).range, (μ (to_simple_func f ⁻¹' {x})).toReal*∥x∥ :=
  by 
    rw [norm_to_simple_func, snorm_one_eq_lintegral_nnnorm]
    have h_eq := simple_func.map_apply (fun x => (nnnorm x : ℝ≥0∞)) (to_simple_func f)
    dsimp only  at h_eq 
    simpRw [←h_eq]
    rw [simple_func.lintegral_eq_lintegral, simple_func.map_lintegral, Ennreal.to_real_sum]
    ·
      congr 
      ext1 x 
      rw [Ennreal.to_real_mul, mul_commₓ, ←of_real_norm_eq_coe_nnnorm, Ennreal.to_real_of_real (norm_nonneg _)]
    ·
      intro x hx 
      byCases' hx0 : x = 0
      ·
        rw [hx0]
        simp 
      ·
        exact
          Ennreal.mul_ne_top Ennreal.coe_ne_top
            (simple_func.measure_preimage_lt_top_of_integrable _ (simple_func.integrable f) hx0).Ne

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

theorem set_to_L1s_indicator_const {T : Set α → E →L[ℝ] F} {C : ℝ} {s : Set α} (hT : dominated_fin_meas_additive μ T C)
  (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) : set_to_L1s T (simple_func.indicator_const 1 hs hμs x) = T s x :=
  by 
    have h_zero : ∀ s hs : MeasurableSet s hs_zero : μ s = 0, T s = 0
    ·
      refine' fun s hs hs0 => norm_eq_zero.mp _ 
      refine' le_antisymmₓ ((hT.2 s).trans (le_of_eqₓ _)) (norm_nonneg _)
      rw [hs0, Ennreal.zero_to_real, mul_zero]
    have h_empty : T ∅ = 0 
    exact h_zero ∅ MeasurableSet.empty measure_empty 
    rw [set_to_L1s_eq_set_to_simple_func]
    refine' Eq.trans _ (simple_func.set_to_simple_func_indicator T h_empty hs x)
    refine' simple_func.set_to_simple_func_congr T h_zero hT.1 (simple_func.integrable _) _ 
    exact Lp.simple_func.to_simple_func_indicator_const hs hμs x

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

theorem set_to_L1_eq_set_to_L1s_clm {T : Set α → E →L[ℝ] F} {C : ℝ} (hT : dominated_fin_meas_additive μ T C)
  (f : α →₁ₛ[μ] E) : set_to_L1 hT f = set_to_L1s_clm α E μ hT f :=
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

theorem set_to_fun_smul [NondiscreteNormedField 𝕜] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜 F] (hT : dominated_fin_meas_additive μ T C) (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜)
  (f : α → E) : set_to_fun hT (c • f) = c • set_to_fun hT f :=
  by 
    byCases' hf : integrable f μ
    ·
      rw [set_to_fun_eq hT hf, set_to_fun_eq hT, integrable.to_L1_smul', L1.set_to_L1_smul hT h_smul c _]
    ·
      byCases' hr : c = 0
      ·
        rw [hr]
        simp 
      ·
        have hf' : ¬integrable (c • f) μ
        ·
          rwa [integrable_smul_iff hr f]
        rw [set_to_fun_undef hT hf, set_to_fun_undef hT hf', smul_zero]

theorem set_to_fun_congr_ae (hT : dominated_fin_meas_additive μ T C) (h : f =ᵐ[μ] g) :
  set_to_fun hT f = set_to_fun hT g :=
  by 
    byCases' hfi : integrable f μ
    ·
      have hgi : integrable g μ := hfi.congr h 
      rw [set_to_fun_eq hT hfi, set_to_fun_eq hT hgi, (integrable.to_L1_eq_to_L1_iff f g hfi hgi).2 h]
    ·
      have hgi : ¬integrable g μ
      ·
        rw [integrable_congr h] at hfi 
        exact hfi 
      rw [set_to_fun_undef hT hfi, set_to_fun_undef hT hgi]

theorem set_to_fun_indicator_const (hT : dominated_fin_meas_additive μ T C) {s : Set α} (hs : MeasurableSet s)
  (hμs : μ s ≠ ∞) (x : E) : set_to_fun hT (s.indicator fun _ => x) = T s x :=
  by 
    rw [set_to_fun_congr_ae hT (@indicator_const_Lp_coe_fn _ _ _ 1 _ _ _ _ hs hμs x _ _).symm]
    rw [L1.set_to_fun_eq_set_to_L1 hT]
    exact L1.set_to_L1_indicator_const_Lp hT hs hμs x

end Function

end MeasureTheory

