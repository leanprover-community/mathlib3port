/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.extend_from
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Basic
import Mathbin.Topology.ExtendFrom

/-!
# Lemmas about `extend_from` in an order topology.
-/


open Filter Set TopologicalSpace

open TopologicalSpace Classical

universe u v

variable {α : Type u} {β : Type v}

theorem continuous_on_Icc_extend_from_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la lb : β}
    (hab : a ≠ b) (hf : ContinuousOn f (ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la))
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFrom (ioo a b) f) (icc a b) := by
  apply continuous_on_extend_from
  · rw [closure_Ioo hab]
  · intro x x_in
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc x_in with (rfl | rfl | h)
    · exact ⟨la, ha.mono_left <| nhds_within_mono _ Ioo_subset_Ioi_self⟩
    · exact ⟨lb, hb.mono_left <| nhds_within_mono _ Ioo_subset_Iio_self⟩
    · use f x, hf x h
#align continuous_on_Icc_extend_from_Ioo continuous_on_Icc_extend_from_Ioo

theorem eq_lim_at_left_extend_from_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {la : β} (hab : a < b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 la)) : extendFrom (ioo a b) f a = la := by
  apply extend_from_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc]
  · simpa [hab]
#align eq_lim_at_left_extend_from_Ioo eq_lim_at_left_extend_from_Ioo

theorem eq_lim_at_right_extend_from_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {lb : β} (hab : a < b)
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : extendFrom (ioo a b) f b = lb := by
  apply extend_from_eq
  · rw [closure_Ioo hab.ne]
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc]
  · simpa [hab]
#align eq_lim_at_right_extend_from_Ioo eq_lim_at_right_extend_from_Ioo

theorem continuous_on_Ico_extend_from_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la : β}
    (hab : a < b) (hf : ContinuousOn f (ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) :
    ContinuousOn (extendFrom (ioo a b) f) (ico a b) := by
  apply continuous_on_extend_from
  · rw [closure_Ioo hab.ne]
    exact Ico_subset_Icc_self
  · intro x x_in
    rcases eq_left_or_mem_Ioo_of_mem_Ico x_in with (rfl | h)
    · use la
      simpa [hab]
    · use f x, hf x h
#align continuous_on_Ico_extend_from_Ioo continuous_on_Ico_extend_from_Ioo

theorem continuous_on_Ioc_extend_from_Ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {lb : β}
    (hab : a < b) (hf : ContinuousOn f (ioo a b)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (ioo a b) f) (ioc a b) := by
  have := @continuous_on_Ico_extend_from_Ioo αᵒᵈ _ _ _ _ _ _ _ f _ _ _ hab
  erw [dual_Ico, dual_Ioi, dual_Ioo] at this
  exact this hf hb
#align continuous_on_Ioc_extend_from_Ioo continuous_on_Ioc_extend_from_Ioo

