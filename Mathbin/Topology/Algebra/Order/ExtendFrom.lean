/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.extend_from
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
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

theorem continuousOn_icc_extendFrom_ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la lb : β}
    (hab : a ≠ b) (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la))
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : ContinuousOn (extendFrom (Ioo a b) f) (Icc a b) :=
  by
  apply continuousOn_extendFrom
  · rw [closure_ioo hab]
  · intro x x_in
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc x_in with (rfl | rfl | h)
    · exact ⟨la, ha.mono_left <| nhdsWithin_mono _ Ioo_subset_Ioi_self⟩
    · exact ⟨lb, hb.mono_left <| nhdsWithin_mono _ Ioo_subset_Iio_self⟩
    · use f x, hf x h
#align continuous_on_Icc_extend_from_Ioo continuousOn_icc_extendFrom_ioo

theorem eq_lim_at_left_extendFrom_ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {la : β} (hab : a < b)
    (ha : Tendsto f (𝓝[>] a) (𝓝 la)) : extendFrom (Ioo a b) f a = la :=
  by
  apply extendFrom_eq
  · rw [closure_ioo hab.ne]
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc]
  · simpa [hab]
#align eq_lim_at_left_extend_from_Ioo eq_lim_at_left_extendFrom_ioo

theorem eq_lim_at_right_extendFrom_ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [T2Space β] {f : α → β} {a b : α} {lb : β} (hab : a < b)
    (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) : extendFrom (Ioo a b) f b = lb :=
  by
  apply extendFrom_eq
  · rw [closure_ioo hab.ne]
    simp only [le_of_lt hab, left_mem_Icc, right_mem_Icc]
  · simpa [hab]
#align eq_lim_at_right_extend_from_Ioo eq_lim_at_right_extendFrom_ioo

theorem continuousOn_ico_extendFrom_ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {la : β}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 la)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ico a b) :=
  by
  apply continuousOn_extendFrom
  · rw [closure_ioo hab.ne]
    exact Ico_subset_Icc_self
  · intro x x_in
    rcases eq_left_or_mem_Ioo_of_mem_Ico x_in with (rfl | h)
    · use la
      simpa [hab]
    · use f x, hf x h
#align continuous_on_Ico_extend_from_Ioo continuousOn_ico_extendFrom_ioo

theorem continuousOn_ioc_extendFrom_ioo [TopologicalSpace α] [LinearOrder α] [DenselyOrdered α]
    [OrderTopology α] [TopologicalSpace β] [RegularSpace β] {f : α → β} {a b : α} {lb : β}
    (hab : a < b) (hf : ContinuousOn f (Ioo a b)) (hb : Tendsto f (𝓝[<] b) (𝓝 lb)) :
    ContinuousOn (extendFrom (Ioo a b) f) (Ioc a b) :=
  by
  have := @continuousOn_ico_extendFrom_ioo αᵒᵈ _ _ _ _ _ _ _ f _ _ _ hab
  erw [dual_Ico, dual_Ioi, dual_Ioo] at this
  exact this hf hb
#align continuous_on_Ioc_extend_from_Ioo continuousOn_ioc_extendFrom_ioo

