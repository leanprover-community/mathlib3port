/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma

! This file was ported from Lean 3 source module probability.probability_mass_function.basic
! leanprover-community/mathlib commit e001509c11c4d0f549d91d89da95b4a0b43c714f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Instances.Ennreal
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in `probability_mass_function/monad.lean`,
other constructions of `pmf`s are found in `probability_mass_function/constructions.lean`.

Given `p : pmf α`, `pmf.to_outer_measure` constructs an `outer_measure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `measure` on `α`, see `pmf.to_measure`.
`pmf.to_measure.is_probability_measure` shows this associated measure is a probability measure.

## Tags

probability mass function, discrete probability measure
-/


noncomputable section

variable {α β γ : Type _}

open Classical BigOperators Nnreal Ennreal

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0∞` such
  that the values have (infinite) sum `1`. -/
def Pmf.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // HasSum f 1 }
#align pmf Pmf

namespace Pmf

instance : CoeFun (Pmf α) fun p => α → ℝ≥0∞ :=
  ⟨fun p a => p.1 a⟩

@[ext]
protected theorem ext : ∀ {p q : Pmf α}, (∀ a, p a = q a) → p = q
  | ⟨f, hf⟩, ⟨g, hg⟩, Eq => Subtype.eq <| funext Eq
#align pmf.ext Pmf.ext

theorem has_sum_coe_one (p : Pmf α) : HasSum p 1 :=
  p.2
#align pmf.has_sum_coe_one Pmf.has_sum_coe_one

@[simp]
theorem tsum_coe (p : Pmf α) : (∑' a, p a) = 1 :=
  p.has_sum_coe_one.tsum_eq
#align pmf.tsum_coe Pmf.tsum_coe

theorem tsum_coe_ne_top (p : Pmf α) : (∑' a, p a) ≠ ∞ :=
  p.tsum_coe.symm ▸ Ennreal.one_ne_top
#align pmf.tsum_coe_ne_top Pmf.tsum_coe_ne_top

theorem tsum_coe_indicator_ne_top (p : Pmf α) (s : Set α) : (∑' a, s.indicator p a) ≠ ∞ :=
  ne_of_lt
    (lt_of_le_of_lt
      (tsum_le_tsum (fun a => Set.indicator_apply_le fun _ => le_rfl) Ennreal.summable
        Ennreal.summable)
      (lt_of_le_of_ne le_top p.tsum_coe_ne_top))
#align pmf.tsum_coe_indicator_ne_top Pmf.tsum_coe_indicator_ne_top

/-- The support of a `pmf` is the set where it is nonzero. -/
def support (p : Pmf α) : Set α :=
  Function.support p
#align pmf.support Pmf.support

@[simp]
theorem mem_support_iff (p : Pmf α) (a : α) : a ∈ p.support ↔ p a ≠ 0 :=
  Iff.rfl
#align pmf.mem_support_iff Pmf.mem_support_iff

theorem apply_eq_zero_iff (p : Pmf α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, not_not]
#align pmf.apply_eq_zero_iff Pmf.apply_eq_zero_iff

theorem apply_pos_iff (p : Pmf α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm
#align pmf.apply_pos_iff Pmf.apply_pos_iff

theorem apply_eq_one_iff (p : Pmf α) (a : α) : p a = 1 ↔ p.support = {a} :=
  by
  refine'
    ⟨fun h =>
      Set.Subset.antisymm (fun a' ha' => by_contra fun ha => _) fun a' ha' =>
        ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one <| ha.symm.trans h,
      fun h =>
      trans (symm <| tsum_eq_single a fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha'))
        p.tsum_coe⟩
  suffices : 1 < ∑' a, p a
  exact ne_of_lt this p.tsum_coe.symm
  have : 0 < ∑' b, ite (b = a) 0 (p b) :=
    lt_of_le_of_ne' zero_le'
      ((tsum_ne_zero_iff Ennreal.summable).2
        ⟨a', ite_ne_left_iff.2 ⟨ha, Ne.symm <| (p.mem_support_iff a').2 ha'⟩⟩)
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ < p a + ∑' b, ite (b = a) 0 (p b) :=
      Ennreal.add_lt_add_of_le_of_lt Ennreal.one_ne_top (le_of_eq h.symm) this
    _ = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) := by rw [eq_self_iff_true, if_true]
    _ = (∑' b, ite (b = a) (p b) 0) + ∑' b, ite (b = a) 0 (p b) :=
      by
      congr
      exact symm ((tsum_eq_single a) fun b hb => if_neg hb)
    _ = ∑' b, ite (b = a) (p b) 0 + ite (b = a) 0 (p b) := ennreal.tsum_add.symm
    _ = ∑' b, p b := tsum_congr fun b => by split_ifs <;> simp only [zero_add, add_zero, le_rfl]
    
#align pmf.apply_eq_one_iff Pmf.apply_eq_one_iff

theorem coe_le_one (p : Pmf α) (a : α) : p a ≤ 1 :=
  has_sum_le
    (by
      intro b
      split_ifs <;> simp only [h, zero_le', le_rfl])
    (has_sum_ite_eq a (p a)) (has_sum_coe_one p)
#align pmf.coe_le_one Pmf.coe_le_one

theorem apply_ne_top (p : Pmf α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) Ennreal.one_lt_top)
#align pmf.apply_ne_top Pmf.apply_ne_top

theorem apply_lt_top (p : Pmf α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)
#align pmf.apply_lt_top Pmf.apply_lt_top

section OuterMeasure

open MeasureTheory MeasureTheory.OuterMeasure

/-- Construct an `outer_measure` from a `pmf`, by assigning measure to each set `s : set α` equal
  to the sum of `p x` for for each `x ∈ α` -/
def toOuterMeasure (p : Pmf α) : OuterMeasure α :=
  OuterMeasure.sum fun x : α => p x • dirac x
#align pmf.to_outer_measure Pmf.toOuterMeasure

variable (p : Pmf α) (s t : Set α)

theorem to_outer_measure_apply : p.toOuterMeasure s = ∑' x, s.indicator p x :=
  tsum_congr fun x => smul_dirac_apply (p x) x s
#align pmf.to_outer_measure_apply Pmf.to_outer_measure_apply

@[simp]
theorem to_outer_measure_apply_finset (s : Finset α) : p.toOuterMeasure s = ∑ x in s, p x :=
  by
  refine' (to_outer_measure_apply p s).trans ((@tsum_eq_sum _ _ _ _ _ _ s _).trans _)
  · exact fun x hx => Set.indicator_of_not_mem hx _
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem hx _
#align pmf.to_outer_measure_apply_finset Pmf.to_outer_measure_apply_finset

theorem to_outer_measure_apply_singleton (a : α) : p.toOuterMeasure {a} = p a :=
  by
  refine' (p.to_outer_measure_apply {a}).trans (((tsum_eq_single a) fun b hb => _).trans _)
  · exact ite_eq_right_iff.2 fun hb' => False.elim <| hb hb'
  · exact ite_eq_left_iff.2 fun ha' => False.elim <| ha' rfl
#align pmf.to_outer_measure_apply_singleton Pmf.to_outer_measure_apply_singleton

theorem to_outer_measure_apply_eq_zero_iff : p.toOuterMeasure s = 0 ↔ Disjoint p.support s :=
  by
  rw [to_outer_measure_apply, Ennreal.tsum_eq_zero]
  exact function.funext_iff.symm.trans Set.indicator_eq_zero'
#align pmf.to_outer_measure_apply_eq_zero_iff Pmf.to_outer_measure_apply_eq_zero_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ∉ » s) -/
theorem to_outer_measure_apply_eq_one_iff : p.toOuterMeasure s = 1 ↔ p.support ⊆ s :=
  by
  refine' (p.to_outer_measure_apply s).symm ▸ ⟨fun h a hap => _, fun h => _⟩
  · refine' by_contra fun hs => ne_of_lt _ (h.trans p.tsum_coe.symm)
    have hs' : s.indicator p a = 0 := Set.indicator_apply_eq_zero.2 fun hs' => False.elim <| hs hs'
    have hsa : s.indicator p a < p a := hs'.symm ▸ (p.apply_pos_iff a).2 hap
    exact
      Ennreal.tsum_lt_tsum (p.tsum_coe_indicator_ne_top s)
        (fun x => Set.indicator_apply_le fun _ => le_rfl) hsa
  · suffices : ∀ (x) (_ : x ∉ s), p x = 0
    exact
      trans
        (tsum_congr fun a => (Set.indicator_apply s p a).trans (ite_eq_left_iff.2 <| symm ∘ this a))
        p.tsum_coe
    exact fun a ha => (p.apply_eq_zero_iff a).2 <| Set.not_mem_subset h ha
#align pmf.to_outer_measure_apply_eq_one_iff Pmf.to_outer_measure_apply_eq_one_iff

@[simp]
theorem to_outer_measure_apply_inter_support :
    p.toOuterMeasure (s ∩ p.support) = p.toOuterMeasure s := by
  simp only [to_outer_measure_apply, Pmf.support, Set.indicator_inter_support]
#align pmf.to_outer_measure_apply_inter_support Pmf.to_outer_measure_apply_inter_support

/-- Slightly stronger than `outer_measure.mono` having an intersection with `p.support` -/
theorem to_outer_measure_mono {s t : Set α} (h : s ∩ p.support ⊆ t) :
    p.toOuterMeasure s ≤ p.toOuterMeasure t :=
  le_trans (le_of_eq (to_outer_measure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)
#align pmf.to_outer_measure_mono Pmf.to_outer_measure_mono

theorem to_outer_measure_apply_eq_of_inter_support_eq {s t : Set α}
    (h : s ∩ p.support = t ∩ p.support) : p.toOuterMeasure s = p.toOuterMeasure t :=
  le_antisymm (p.to_outer_measure_mono (h.symm ▸ Set.inter_subset_left t p.support))
    (p.to_outer_measure_mono (h ▸ Set.inter_subset_left s p.support))
#align
  pmf.to_outer_measure_apply_eq_of_inter_support_eq Pmf.to_outer_measure_apply_eq_of_inter_support_eq

@[simp]
theorem to_outer_measure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.indicator p x :=
  (p.to_outer_measure_apply s).trans (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)
#align pmf.to_outer_measure_apply_fintype Pmf.to_outer_measure_apply_fintype

@[simp]
theorem to_outer_measure_caratheodory (p : Pmf α) : (toOuterMeasure p).caratheodory = ⊤ :=
  by
  refine' eq_top_iff.2 <| le_trans (le_infₛ fun x hx => _) (le_sum_caratheodory _)
  obtain ⟨y, hy⟩ := hx
  exact
    ((le_of_eq (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eq hy)
#align pmf.to_outer_measure_caratheodory Pmf.to_outer_measure_caratheodory

end OuterMeasure

section Measure

open MeasureTheory

/-- Since every set is Carathéodory-measurable under `pmf.to_outer_measure`,
  we can further extend this `outer_measure` to a `measure` on `α` -/
def toMeasure [MeasurableSpace α] (p : Pmf α) : Measure α :=
  p.toOuterMeasure.toMeasure ((to_outer_measure_caratheodory p).symm ▸ le_top)
#align pmf.to_measure Pmf.toMeasure

variable [MeasurableSpace α] (p : Pmf α) (s t : Set α)

theorem to_outer_measure_apply_le_to_measure_apply : p.toOuterMeasure s ≤ p.toMeasure s :=
  le_to_measure_apply p.toOuterMeasure _ s
#align pmf.to_outer_measure_apply_le_to_measure_apply Pmf.to_outer_measure_apply_le_to_measure_apply

theorem to_measure_apply_eq_to_outer_measure_apply (hs : MeasurableSet s) :
    p.toMeasure s = p.toOuterMeasure s :=
  to_measure_apply p.toOuterMeasure _ hs
#align pmf.to_measure_apply_eq_to_outer_measure_apply Pmf.to_measure_apply_eq_to_outer_measure_apply

theorem to_measure_apply (hs : MeasurableSet s) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.to_measure_apply_eq_to_outer_measure_apply s hs).trans (p.to_outer_measure_apply s)
#align pmf.to_measure_apply Pmf.to_measure_apply

theorem to_measure_apply_singleton (a : α) (h : MeasurableSet ({a} : Set α)) :
    p.toMeasure {a} = p a := by
  simp [to_measure_apply_eq_to_outer_measure_apply p {a} h, to_outer_measure_apply_singleton]
#align pmf.to_measure_apply_singleton Pmf.to_measure_apply_singleton

theorem to_measure_apply_eq_zero_iff (hs : MeasurableSet s) :
    p.toMeasure s = 0 ↔ Disjoint p.support s := by
  rw [to_measure_apply_eq_to_outer_measure_apply p s hs, to_outer_measure_apply_eq_zero_iff]
#align pmf.to_measure_apply_eq_zero_iff Pmf.to_measure_apply_eq_zero_iff

theorem to_measure_apply_eq_one_iff (hs : MeasurableSet s) : p.toMeasure s = 1 ↔ p.support ⊆ s :=
  (p.to_measure_apply_eq_to_outer_measure_apply s hs : p.toMeasure s = p.toOuterMeasure s).symm ▸
    p.to_outer_measure_apply_eq_one_iff s
#align pmf.to_measure_apply_eq_one_iff Pmf.to_measure_apply_eq_one_iff

@[simp]
theorem to_measure_apply_inter_support (hs : MeasurableSet s) (hp : MeasurableSet p.support) :
    p.toMeasure (s ∩ p.support) = p.toMeasure s := by
  simp [p.to_measure_apply_eq_to_outer_measure_apply s hs,
    p.to_measure_apply_eq_to_outer_measure_apply _ (hs.inter hp)]
#align pmf.to_measure_apply_inter_support Pmf.to_measure_apply_inter_support

theorem to_measure_mono {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : s ∩ p.support ⊆ t) : p.toMeasure s ≤ p.toMeasure t := by
  simpa only [p.to_measure_apply_eq_to_outer_measure_apply, hs, ht] using to_outer_measure_mono p h
#align pmf.to_measure_mono Pmf.to_measure_mono

theorem to_measure_apply_eq_of_inter_support_eq {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : s ∩ p.support = t ∩ p.support) : p.toMeasure s = p.toMeasure t := by
  simpa only [p.to_measure_apply_eq_to_outer_measure_apply, hs, ht] using
    to_outer_measure_apply_eq_of_inter_support_eq p h
#align pmf.to_measure_apply_eq_of_inter_support_eq Pmf.to_measure_apply_eq_of_inter_support_eq

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

@[simp]
theorem to_measure_apply_finset (s : Finset α) : p.toMeasure s = ∑ x in s, p x :=
  (p.to_measure_apply_eq_to_outer_measure_apply s s.MeasurableSet).trans
    (p.to_outer_measure_apply_finset s)
#align pmf.to_measure_apply_finset Pmf.to_measure_apply_finset

theorem to_measure_apply_of_finite (hs : s.Finite) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.to_measure_apply_eq_to_outer_measure_apply s hs.MeasurableSet).trans
    (p.to_outer_measure_apply s)
#align pmf.to_measure_apply_of_finite Pmf.to_measure_apply_of_finite

@[simp]
theorem to_measure_apply_fintype [Fintype α] : p.toMeasure s = ∑ x, s.indicator p x :=
  (p.to_measure_apply_eq_to_outer_measure_apply s s.to_finite.MeasurableSet).trans
    (p.to_outer_measure_apply_fintype s)
#align pmf.to_measure_apply_fintype Pmf.to_measure_apply_fintype

end MeasurableSingletonClass

/-- The measure associated to a `pmf` by `to_measure` is a probability measure -/
instance toMeasure.isProbabilityMeasure (p : Pmf α) : IsProbabilityMeasure p.toMeasure :=
  ⟨by
    simpa only [MeasurableSet.univ, to_measure_apply_eq_to_outer_measure_apply, Set.indicator_univ,
      to_outer_measure_apply, Ennreal.coe_eq_one] using tsum_coe p⟩
#align pmf.to_measure.is_probability_measure Pmf.toMeasure.isProbabilityMeasure

end Measure

end Pmf

