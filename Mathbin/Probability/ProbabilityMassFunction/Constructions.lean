/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import Probability.ProbabilityMassFunction.Monad

#align_import probability.probability_mass_function.constructions from "leanprover-community/mathlib"@"0b7c740e25651db0ba63648fbae9f9d6f941e31b"

/-!
# Specific Constructions of Probability Mass Functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gives a number of different `pmf` constructions for common probability distributions.

`map` and `seq` allow pushing a `pmf α` along a function `f : α → β` (or distribution of
functions `f : pmf (α → β)`) to get a `pmf β`

`of_finset` and `of_fintype` simplify the construction of a `pmf α` from a function `f : α → ℝ≥0∞`,
by allowing the "sum equals 1" constraint to be in terms of `finset.sum` instead of `tsum`.

`normalize` constructs a `pmf α` by normalizing a function `f : α → ℝ≥0∞` by its sum,
and `filter` uses this to filter the support of a `pmf` and re-normalize the new distribution.

`bernoulli` represents the bernoulli distribution on `bool`

-/


namespace PMF

noncomputable section

variable {α β γ : Type _}

open scoped Classical BigOperators NNReal ENNReal

section Map

#print PMF.map /-
/-- The functorial action of a function on a `pmf`. -/
def map (f : α → β) (p : PMF α) : PMF β :=
  bind p (pure ∘ f)
#align pmf.map PMF.map
-/

variable (f : α → β) (p : PMF α) (b : β)

#print PMF.monad_map_eq_map /-
theorem monad_map_eq_map {α β : Type _} (f : α → β) (p : PMF α) : f <$> p = p.map f :=
  rfl
#align pmf.monad_map_eq_map PMF.monad_map_eq_map
-/

#print PMF.map_apply /-
@[simp]
theorem map_apply : (map f p) b = ∑' a, if b = f a then p a else 0 := by simp [map]
#align pmf.map_apply PMF.map_apply
-/

#print PMF.support_map /-
@[simp]
theorem support_map : (map f p).support = f '' p.support :=
  Set.ext fun b => by simp [map, @eq_comm β b]
#align pmf.support_map PMF.support_map
-/

#print PMF.mem_support_map_iff /-
theorem mem_support_map_iff : b ∈ (map f p).support ↔ ∃ a ∈ p.support, f a = b := by simp
#align pmf.mem_support_map_iff PMF.mem_support_map_iff
-/

#print PMF.bind_pure_comp /-
theorem bind_pure_comp : bind p (pure ∘ f) = map f p :=
  rfl
#align pmf.bind_pure_comp PMF.bind_pure_comp
-/

#print PMF.map_id /-
theorem map_id : map id p = p :=
  bind_pure _
#align pmf.map_id PMF.map_id
-/

#print PMF.map_comp /-
theorem map_comp (g : β → γ) : (p.map f).map g = p.map (g ∘ f) := by simp [map]
#align pmf.map_comp PMF.map_comp
-/

#print PMF.pure_map /-
theorem pure_map (a : α) : (pure a).map f = pure (f a) :=
  pure_bind _ _
#align pmf.pure_map PMF.pure_map
-/

#print PMF.map_bind /-
theorem map_bind (q : α → PMF β) (f : β → γ) : (p.bind q).map f = p.bind fun a => (q a).map f :=
  bind_bind _ _ _
#align pmf.map_bind PMF.map_bind
-/

#print PMF.bind_map /-
@[simp]
theorem bind_map (p : PMF α) (f : α → β) (q : β → PMF γ) : (p.map f).bind q = p.bind (q ∘ f) :=
  (bind_bind _ _ _).trans (congr_arg _ (funext fun a => pure_bind _ _))
#align pmf.bind_map PMF.bind_map
-/

#print PMF.map_const /-
@[simp]
theorem map_const : p.map (Function.const α b) = pure b := by
  simp only [map, bind_const, Function.comp_const]
#align pmf.map_const PMF.map_const
-/

section Measure

variable (s : Set β)

#print PMF.toOuterMeasure_map_apply /-
@[simp]
theorem toOuterMeasure_map_apply : (p.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s) := by
  simp [map, Set.indicator, to_outer_measure_apply p (f ⁻¹' s)]
#align pmf.to_outer_measure_map_apply PMF.toOuterMeasure_map_apply
-/

#print PMF.toMeasure_map_apply /-
@[simp]
theorem toMeasure_map_apply [MeasurableSpace α] [MeasurableSpace β] (hf : Measurable f)
    (hs : MeasurableSet s) : (p.map f).toMeasure s = p.toMeasure (f ⁻¹' s) :=
  by
  rw [to_measure_apply_eq_to_outer_measure_apply _ s hs,
    to_measure_apply_eq_to_outer_measure_apply _ (f ⁻¹' s) (measurableSet_preimage hf hs)]
  exact to_outer_measure_map_apply f p s
#align pmf.to_measure_map_apply PMF.toMeasure_map_apply
-/

end Measure

end Map

section Seq

#print PMF.seq /-
/-- The monadic sequencing operation for `pmf`. -/
def seq (q : PMF (α → β)) (p : PMF α) : PMF β :=
  q.bind fun m => p.bind fun a => pure (m a)
#align pmf.seq PMF.seq
-/

variable (q : PMF (α → β)) (p : PMF α) (b : β)

#print PMF.monad_seq_eq_seq /-
theorem monad_seq_eq_seq {α β : Type _} (q : PMF (α → β)) (p : PMF α) : q <*> p = q.seq p :=
  rfl
#align pmf.monad_seq_eq_seq PMF.monad_seq_eq_seq
-/

#print PMF.seq_apply /-
@[simp]
theorem seq_apply : (seq q p) b = ∑' (f : α → β) (a : α), if b = f a then q f * p a else 0 :=
  by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine' tsum_congr fun f => ENNReal.tsum_mul_left.symm.trans (tsum_congr fun a => _)
  simpa only [MulZeroClass.mul_zero] using mul_ite (b = f a) (q f) (p a) 0
#align pmf.seq_apply PMF.seq_apply
-/

#print PMF.support_seq /-
@[simp]
theorem support_seq : (seq q p).support = ⋃ f ∈ q.support, f '' p.support :=
  Set.ext fun b => by simp [-mem_support_iff, seq, @eq_comm β b]
#align pmf.support_seq PMF.support_seq
-/

#print PMF.mem_support_seq_iff /-
theorem mem_support_seq_iff : b ∈ (seq q p).support ↔ ∃ f ∈ q.support, b ∈ f '' p.support := by simp
#align pmf.mem_support_seq_iff PMF.mem_support_seq_iff
-/

end Seq

instance : LawfulFunctor PMF where
  map_const α β := rfl
  id_map α := bind_pure
  comp_map α β γ g h x := (map_comp _ _ _).symm

instance : LawfulMonad PMF where
  bind_pure_comp α β f x := rfl
  bind_map α β f x := rfl
  pure_bind α β := pure_bind
  bind_assoc α β γ := bind_bind

section OfFinset

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (a «expr ∉ » s) -/
#print PMF.ofFinset /-
/-- Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `pmf` -/
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a in s, f a = 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : PMF α :=
  ⟨f, h ▸ hasSum_sum_of_ne_finset_zero h'⟩
#align pmf.of_finset PMF.ofFinset
-/

/- ././././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (a «expr ∉ » s) -/
variable {f : α → ℝ≥0∞} {s : Finset α} (h : ∑ a in s, f a = 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

#print PMF.ofFinset_apply /-
@[simp]
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a :=
  rfl
#align pmf.of_finset_apply PMF.ofFinset_apply
-/

#print PMF.support_ofFinset /-
@[simp]
theorem support_ofFinset : (ofFinset f s h h').support = s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)
#align pmf.support_of_finset PMF.support_ofFinset
-/

#print PMF.mem_support_ofFinset_iff /-
theorem mem_support_ofFinset_iff (a : α) : a ∈ (ofFinset f s h h').support ↔ a ∈ s ∧ f a ≠ 0 := by
  simp
#align pmf.mem_support_of_finset_iff PMF.mem_support_ofFinset_iff
-/

#print PMF.ofFinset_apply_of_not_mem /-
theorem ofFinset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha
#align pmf.of_finset_apply_of_not_mem PMF.ofFinset_apply_of_not_mem
-/

section Measure

variable (t : Set α)

#print PMF.toOuterMeasure_ofFinset_apply /-
@[simp]
theorem toOuterMeasure_ofFinset_apply :
    (ofFinset f s h h').toOuterMeasure t = ∑' x, t.indicator f x :=
  toOuterMeasure_apply (ofFinset f s h h') t
#align pmf.to_outer_measure_of_finset_apply PMF.toOuterMeasure_ofFinset_apply
-/

#print PMF.toMeasure_ofFinset_apply /-
@[simp]
theorem toMeasure_ofFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofFinset f s h h').toMeasure t = ∑' x, t.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ t ht).trans (toOuterMeasure_ofFinset_apply h h' t)
#align pmf.to_measure_of_finset_apply PMF.toMeasure_ofFinset_apply
-/

end Measure

end OfFinset

section OfFintype

#print PMF.ofFintype /-
/-- Given a finite type `α` and a function `f : α → ℝ≥0∞` with sum 1, we get a `pmf`. -/
def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) : PMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha
#align pmf.of_fintype PMF.ofFintype
-/

variable [Fintype α] {f : α → ℝ≥0∞} (h : ∑ a, f a = 1)

#print PMF.ofFintype_apply /-
@[simp]
theorem ofFintype_apply (a : α) : ofFintype f h a = f a :=
  rfl
#align pmf.of_fintype_apply PMF.ofFintype_apply
-/

#print PMF.support_ofFintype /-
@[simp]
theorem support_ofFintype : (ofFintype f h).support = Function.support f :=
  rfl
#align pmf.support_of_fintype PMF.support_ofFintype
-/

#print PMF.mem_support_ofFintype_iff /-
theorem mem_support_ofFintype_iff (a : α) : a ∈ (ofFintype f h).support ↔ f a ≠ 0 :=
  Iff.rfl
#align pmf.mem_support_of_fintype_iff PMF.mem_support_ofFintype_iff
-/

section Measure

variable (s : Set α)

#print PMF.toOuterMeasure_ofFintype_apply /-
@[simp]
theorem toOuterMeasure_ofFintype_apply : (ofFintype f h).toOuterMeasure s = ∑' x, s.indicator f x :=
  toOuterMeasure_apply (ofFintype f h) s
#align pmf.to_outer_measure_of_fintype_apply PMF.toOuterMeasure_ofFintype_apply
-/

#print PMF.toMeasure_ofFintype_apply /-
@[simp]
theorem toMeasure_ofFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (ofFintype f h).toMeasure s = ∑' x, s.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ s hs).trans (toOuterMeasure_ofFintype_apply h s)
#align pmf.to_measure_of_fintype_apply PMF.toMeasure_ofFintype_apply
-/

end Measure

end OfFintype

section normalize

#print PMF.normalize /-
/-- Given a `f` with non-zero and non-infinite sum, get a `pmf` by normalizing `f` by its `tsum` -/
def normalize (f : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞) : PMF α :=
  ⟨fun a => f a * (∑' x, f x)⁻¹,
    ENNReal.summable.hasSum_iff.2 (ENNReal.tsum_mul_right.trans (ENNReal.mul_inv_cancel hf0 hf))⟩
#align pmf.normalize PMF.normalize
-/

variable {f : α → ℝ≥0∞} (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞)

#print PMF.normalize_apply /-
@[simp]
theorem normalize_apply (a : α) : (normalize f hf0 hf) a = f a * (∑' x, f x)⁻¹ :=
  rfl
#align pmf.normalize_apply PMF.normalize_apply
-/

#print PMF.support_normalize /-
@[simp]
theorem support_normalize : (normalize f hf0 hf).support = Function.support f :=
  Set.ext fun a => by simp [hf, mem_support_iff]
#align pmf.support_normalize PMF.support_normalize
-/

#print PMF.mem_support_normalize_iff /-
theorem mem_support_normalize_iff (a : α) : a ∈ (normalize f hf0 hf).support ↔ f a ≠ 0 := by simp
#align pmf.mem_support_normalize_iff PMF.mem_support_normalize_iff
-/

end normalize

section Filter

#print PMF.filter /-
/-- Create new `pmf` by filtering on a set with non-zero measure and normalizing -/
def filter (p : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support) : PMF α :=
  PMF.normalize (s.indicator p) (by simpa using h) (p.tsum_coe_indicator_ne_top s)
#align pmf.filter PMF.filter
-/

variable {p : PMF α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support)

#print PMF.filter_apply /-
@[simp]
theorem filter_apply (a : α) :
    (p.filterₓ s h) a = s.indicator p a * (∑' a', (s.indicator p) a')⁻¹ := by
  rw [Filter, normalize_apply]
#align pmf.filter_apply PMF.filter_apply
-/

#print PMF.filter_apply_eq_zero_of_not_mem /-
theorem filter_apply_eq_zero_of_not_mem {a : α} (ha : a ∉ s) : (p.filterₓ s h) a = 0 := by
  rw [filter_apply, set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha, MulZeroClass.zero_mul]
#align pmf.filter_apply_eq_zero_of_not_mem PMF.filter_apply_eq_zero_of_not_mem
-/

#print PMF.mem_support_filter_iff /-
theorem mem_support_filter_iff {a : α} : a ∈ (p.filterₓ s h).support ↔ a ∈ s ∧ a ∈ p.support :=
  (mem_support_normalize_iff _ _ _).trans Set.indicator_apply_ne_zero
#align pmf.mem_support_filter_iff PMF.mem_support_filter_iff
-/

#print PMF.support_filter /-
@[simp]
theorem support_filter : (p.filterₓ s h).support = s ∩ p.support :=
  Set.ext fun x => mem_support_filter_iff _
#align pmf.support_filter PMF.support_filter
-/

#print PMF.filter_apply_eq_zero_iff /-
theorem filter_apply_eq_zero_iff (a : α) : (p.filterₓ s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support := by
  erw [apply_eq_zero_iff, support_filter, Set.mem_inter_iff, not_and_or]
#align pmf.filter_apply_eq_zero_iff PMF.filter_apply_eq_zero_iff
-/

#print PMF.filter_apply_ne_zero_iff /-
theorem filter_apply_ne_zero_iff (a : α) : (p.filterₓ s h) a ≠ 0 ↔ a ∈ s ∧ a ∈ p.support := by
  rw [Ne.def, filter_apply_eq_zero_iff, not_or, Classical.not_not, Classical.not_not]
#align pmf.filter_apply_ne_zero_iff PMF.filter_apply_ne_zero_iff
-/

end Filter

section bernoulli

#print PMF.bernoulli /-
/-- A `pmf` which assigns probability `p` to `tt` and `1 - p` to `ff`. -/
def bernoulli (p : ℝ≥0∞) (h : p ≤ 1) : PMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])
#align pmf.bernoulli PMF.bernoulli
-/

variable {p : ℝ≥0∞} (h : p ≤ 1) (b : Bool)

#print PMF.bernoulli_apply /-
@[simp]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) :=
  rfl
#align pmf.bernoulli_apply PMF.bernoulli_apply
-/

#print PMF.support_bernoulli /-
@[simp]
theorem support_bernoulli : (bernoulli p h).support = {b | cond b (p ≠ 0) (p ≠ 1)} :=
  by
  refine' Set.ext fun b => _
  induction b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne.def, tsub_eq_zero_iff_le, not_le]
    exact ⟨ne_of_lt, lt_of_le_of_ne h⟩
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_true, Set.mem_setOf_eq]
#align pmf.support_bernoulli PMF.support_bernoulli
-/

#print PMF.mem_support_bernoulli_iff /-
theorem mem_support_bernoulli_iff : b ∈ (bernoulli p h).support ↔ cond b (p ≠ 0) (p ≠ 1) := by simp
#align pmf.mem_support_bernoulli_iff PMF.mem_support_bernoulli_iff
-/

end bernoulli

end PMF

