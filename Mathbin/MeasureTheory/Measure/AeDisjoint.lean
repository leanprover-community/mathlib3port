/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.measure.ae_disjoint
! leanprover-community/mathlib commit b5ad141426bb005414324f89719c77c0aa3ec612
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Almost everywhere disjoint sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that sets `s` and `t` are `μ`-a.e. disjoint (see `measure_theory.ae_disjoint`) if their
intersection has measure zero. This assumption can be used instead of `disjoint` in most theorems in
measure theory.
-/


open Set Function

namespace MeasureTheory

variable {ι α : Type _} {m : MeasurableSpace α} (μ : Measure α)

#print MeasureTheory.AEDisjoint /-
/-- Two sets are said to be `μ`-a.e. disjoint if their intersection has measure zero. -/
def AEDisjoint (s t : Set α) :=
  μ (s ∩ t) = 0
#align measure_theory.ae_disjoint MeasureTheory.AEDisjoint
-/

variable {μ} {s t u v : Set α}

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (j «expr ≠ » i) -/
/-- If `s : ι → set α` is a countable family of pairwise a.e. disjoint sets, then there exists a
family of measurable null sets `t i` such that `s i \ t i` are pairwise disjoint. -/
theorem exists_null_pairwise_disjoint_diff [Countable ι] {s : ι → Set α}
    (hd : Pairwise (AEDisjoint μ on s)) :
    ∃ t : ι → Set α,
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, μ (t i) = 0) ∧ Pairwise (Disjoint on fun i => s i \ t i) :=
  by
  refine'
    ⟨fun i => to_measurable μ (s i ∩ ⋃ j ∈ ({i}ᶜ : Set ι), s j), fun i =>
      measurable_set_to_measurable _ _, fun i => _, _⟩
  · simp only [measure_to_measurable, inter_Union]
    exact (measure_bUnion_null_iff <| to_countable _).2 fun j hj => hd (Ne.symm hj)
  · simp only [Pairwise, disjoint_left, on_fun, mem_diff, not_and, and_imp, Classical.not_not]
    intro i j hne x hi hU hj
    replace hU : x ∉ s i ∩ ⋃ (j) (_ : j ≠ i), s j := fun h => hU (subset_to_measurable _ _ h)
    simp only [mem_inter_iff, mem_Union, not_and, not_exists] at hU 
    exact (hU hi j hne.symm hj).elim
#align measure_theory.exists_null_pairwise_disjoint_diff MeasureTheory.exists_null_pairwise_disjoint_diff

namespace AeDisjoint

protected theorem eq (h : AEDisjoint μ s t) : μ (s ∩ t) = 0 :=
  h
#align measure_theory.ae_disjoint.eq MeasureTheory.AEDisjoint.eq

#print MeasureTheory.AEDisjoint.symm /-
@[symm]
protected theorem symm (h : AEDisjoint μ s t) : AEDisjoint μ t s := by rwa [ae_disjoint, inter_comm]
#align measure_theory.ae_disjoint.symm MeasureTheory.AEDisjoint.symm
-/

#print MeasureTheory.AEDisjoint.symmetric /-
protected theorem symmetric : Symmetric (AEDisjoint μ) := fun s t h => h.symm
#align measure_theory.ae_disjoint.symmetric MeasureTheory.AEDisjoint.symmetric
-/

#print MeasureTheory.AEDisjoint.comm /-
protected theorem comm : AEDisjoint μ s t ↔ AEDisjoint μ t s :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align measure_theory.ae_disjoint.comm MeasureTheory.AEDisjoint.comm
-/

protected theorem Disjoint.aedisjoint (h : Disjoint s t) : AEDisjoint μ s t := by
  rw [ae_disjoint, disjoint_iff_inter_eq_empty.1 h, measure_empty]
#align disjoint.ae_disjoint Disjoint.aedisjoint

protected theorem Pairwise.aedisjoint {f : ι → Set α} (hf : Pairwise (Disjoint on f)) :
    Pairwise (AEDisjoint μ on f) :=
  hf.mono fun i j h => h.AEDisjoint
#align pairwise.ae_disjoint Pairwise.aedisjoint

protected theorem Set.PairwiseDisjoint.aedisjoint {f : ι → Set α} {s : Set ι}
    (hf : s.PairwiseDisjoint f) : s.Pairwise (AEDisjoint μ on f) :=
  hf.mono' fun i j h => h.AEDisjoint
#align set.pairwise_disjoint.ae_disjoint Set.PairwiseDisjoint.aedisjoint

#print MeasureTheory.AEDisjoint.mono_ae /-
theorem mono_ae (h : AEDisjoint μ s t) (hu : u ≤ᵐ[μ] s) (hv : v ≤ᵐ[μ] t) : AEDisjoint μ u v :=
  measure_mono_null_ae (hu.inter hv) h
#align measure_theory.ae_disjoint.mono_ae MeasureTheory.AEDisjoint.mono_ae
-/

#print MeasureTheory.AEDisjoint.mono /-
protected theorem mono (h : AEDisjoint μ s t) (hu : u ⊆ s) (hv : v ⊆ t) : AEDisjoint μ u v :=
  h.mono_ae hu.EventuallyLE hv.EventuallyLE
#align measure_theory.ae_disjoint.mono MeasureTheory.AEDisjoint.mono
-/

#print MeasureTheory.AEDisjoint.congr /-
protected theorem congr (h : AEDisjoint μ s t) (hu : u =ᵐ[μ] s) (hv : v =ᵐ[μ] t) :
    AEDisjoint μ u v :=
  h.mono_ae (Filter.EventuallyEq.le hu) (Filter.EventuallyEq.le hv)
#align measure_theory.ae_disjoint.congr MeasureTheory.AEDisjoint.congr
-/

@[simp]
theorem iUnion_left_iff [Countable ι] {s : ι → Set α} :
    AEDisjoint μ (⋃ i, s i) t ↔ ∀ i, AEDisjoint μ (s i) t := by
  simp only [ae_disjoint, Union_inter, measure_Union_null_iff]
#align measure_theory.ae_disjoint.Union_left_iff MeasureTheory.AEDisjoint.iUnion_left_iff

@[simp]
theorem iUnion_right_iff [Countable ι] {t : ι → Set α} :
    AEDisjoint μ s (⋃ i, t i) ↔ ∀ i, AEDisjoint μ s (t i) := by
  simp only [ae_disjoint, inter_Union, measure_Union_null_iff]
#align measure_theory.ae_disjoint.Union_right_iff MeasureTheory.AEDisjoint.iUnion_right_iff

@[simp]
theorem union_left_iff : AEDisjoint μ (s ∪ t) u ↔ AEDisjoint μ s u ∧ AEDisjoint μ t u := by
  simp [union_eq_Union, and_comm]
#align measure_theory.ae_disjoint.union_left_iff MeasureTheory.AEDisjoint.union_left_iff

@[simp]
theorem union_right_iff : AEDisjoint μ s (t ∪ u) ↔ AEDisjoint μ s t ∧ AEDisjoint μ s u := by
  simp [union_eq_Union, and_comm]
#align measure_theory.ae_disjoint.union_right_iff MeasureTheory.AEDisjoint.union_right_iff

theorem union_left (hs : AEDisjoint μ s u) (ht : AEDisjoint μ t u) : AEDisjoint μ (s ∪ t) u :=
  union_left_iff.mpr ⟨hs, ht⟩
#align measure_theory.ae_disjoint.union_left MeasureTheory.AEDisjoint.union_left

theorem union_right (ht : AEDisjoint μ s t) (hu : AEDisjoint μ s u) : AEDisjoint μ s (t ∪ u) :=
  union_right_iff.2 ⟨ht, hu⟩
#align measure_theory.ae_disjoint.union_right MeasureTheory.AEDisjoint.union_right

theorem diff_ae_eq_left (h : AEDisjoint μ s t) : (s \ t : Set α) =ᵐ[μ] s :=
  @diff_self_inter _ s t ▸ diff_null_ae_eq_self h
#align measure_theory.ae_disjoint.diff_ae_eq_left MeasureTheory.AEDisjoint.diff_ae_eq_left

theorem diff_ae_eq_right (h : AEDisjoint μ s t) : (t \ s : Set α) =ᵐ[μ] t :=
  h.symm.diff_ae_eq_left
#align measure_theory.ae_disjoint.diff_ae_eq_right MeasureTheory.AEDisjoint.diff_ae_eq_right

theorem measure_diff_left (h : AEDisjoint μ s t) : μ (s \ t) = μ s :=
  measure_congr h.diff_ae_eq_left
#align measure_theory.ae_disjoint.measure_diff_left MeasureTheory.AEDisjoint.measure_diff_left

theorem measure_diff_right (h : AEDisjoint μ s t) : μ (t \ s) = μ t :=
  measure_congr h.diff_ae_eq_right
#align measure_theory.ae_disjoint.measure_diff_right MeasureTheory.AEDisjoint.measure_diff_right

/-- If `s` and `t` are `μ`-a.e. disjoint, then `s \ u` and `t` are disjoint for some measurable null
set `u`. -/
theorem exists_disjoint_diff (h : AEDisjoint μ s t) :
    ∃ u, MeasurableSet u ∧ μ u = 0 ∧ Disjoint (s \ u) t :=
  ⟨toMeasurable μ (s ∩ t), measurableSet_toMeasurable _ _, (measure_toMeasurable _).trans h,
    disjoint_sdiff_self_left.mono_left fun x hx =>
      ⟨hx.1, fun hxt => hx.2 <| subset_toMeasurable _ _ ⟨hx.1, hxt⟩⟩⟩
#align measure_theory.ae_disjoint.exists_disjoint_diff MeasureTheory.AEDisjoint.exists_disjoint_diff

theorem of_null_right (h : μ t = 0) : AEDisjoint μ s t :=
  measure_mono_null (inter_subset_right _ _) h
#align measure_theory.ae_disjoint.of_null_right MeasureTheory.AEDisjoint.of_null_right

theorem of_null_left (h : μ s = 0) : AEDisjoint μ s t :=
  (of_null_right h).symm
#align measure_theory.ae_disjoint.of_null_left MeasureTheory.AEDisjoint.of_null_left

end AeDisjoint

theorem aedisjoint_compl_left : AEDisjoint μ (sᶜ) s :=
  (@disjoint_compl_left _ _ s).AEDisjoint
#align measure_theory.ae_disjoint_compl_left MeasureTheory.aedisjoint_compl_left

theorem aedisjoint_compl_right : AEDisjoint μ s (sᶜ) :=
  (@disjoint_compl_right _ _ s).AEDisjoint
#align measure_theory.ae_disjoint_compl_right MeasureTheory.aedisjoint_compl_right

end MeasureTheory

