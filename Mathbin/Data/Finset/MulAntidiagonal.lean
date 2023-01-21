/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies

! This file was ported from Lean 3 source module data.finset.mul_antidiagonal
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Data.Set.MulAntidiagonal

/-! # Multiplication antidiagonal as a `finset`.

We construct the `finset` of all pairs
of an element in `s` and an element in `t` that multiply to `a`,
given that `s` and `t` are well-ordered.-/


namespace Set

open Pointwise

variable {α : Type _} {s t : Set α}

@[to_additive]
theorem IsPwo.mul [OrderedCancelCommMonoid α] (hs : s.IsPwo) (ht : t.IsPwo) : IsPwo (s * t) :=
  by
  rw [← image_mul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.mul' monotone_snd)
#align set.is_pwo.mul Set.IsPwo.mul
#align set.is_pwo.add Set.IsPwo.add

variable [LinearOrderedCancelCommMonoid α]

@[to_additive]
theorem IsWf.mul (hs : s.IsWf) (ht : t.IsWf) : IsWf (s * t) :=
  (hs.IsPwo.mul ht.IsPwo).IsWf
#align set.is_wf.mul Set.IsWf.mul
#align set.is_wf.add Set.IsWf.add

@[to_additive]
theorem IsWf.min_mul (hs : s.IsWf) (ht : t.IsWf) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.mul ht).min (hsn.mul htn) = hs.min hsn * ht.min htn :=
  by
  refine' le_antisymm (is_wf.min_le _ _ (mem_mul.2 ⟨_, _, hs.min_mem _, ht.min_mem _, rfl⟩)) _
  rw [is_wf.le_min_iff]
  rintro _ ⟨x, y, hx, hy, rfl⟩
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy)
#align set.is_wf.min_mul Set.IsWf.min_mul
#align set.is_wf.min_add Set.IsWf.min_add

end Set

namespace Finset

open Pointwise

variable {α : Type _}

variable [OrderedCancelCommMonoid α] {s t : Set α} (hs : s.IsPwo) (ht : t.IsPwo) (a : α)

/-- `finset.mul_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in `s` and an
element in `t` that multiply to `a`, but its construction requires proofs that `s` and `t` are
well-ordered. -/
@[to_additive
      "`finset.add_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in\n`s` and an element in `t` that add to `a`, but its construction requires proofs that `s` and `t` are\nwell-ordered."]
noncomputable def mulAntidiagonal : Finset (α × α) :=
  (Set.mulAntidiagonal.finite_of_isPwo hs ht a).toFinset
#align finset.mul_antidiagonal Finset.mulAntidiagonal
#align finset.add_antidiagonal Finset.addAntidiagonal

variable {hs ht a} {u : Set α} {hu : u.IsPwo} {x : α × α}

@[simp, to_additive]
theorem mem_mulAntidiagonal : x ∈ mulAntidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a := by
  simp [mul_antidiagonal, and_rotate]
#align finset.mem_mul_antidiagonal Finset.mem_mulAntidiagonal
#align finset.mem_add_antidiagonal Finset.mem_add_antidiagonal

@[to_additive]
theorem mulAntidiagonal_mono_left (h : u ⊆ s) : mulAntidiagonal hu ht a ⊆ mulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.mulAntidiagonal_mono_left h
#align finset.mul_antidiagonal_mono_left Finset.mulAntidiagonal_mono_left
#align finset.add_antidiagonal_mono_left Finset.add_antidiagonal_mono_left

@[to_additive]
theorem mulAntidiagonal_mono_right (h : u ⊆ t) :
    mulAntidiagonal hs hu a ⊆ mulAntidiagonal hs ht a :=
  Set.Finite.toFinset_mono <| Set.mulAntidiagonal_mono_right h
#align finset.mul_antidiagonal_mono_right Finset.mulAntidiagonal_mono_right
#align finset.add_antidiagonal_mono_right Finset.add_antidiagonal_mono_right

@[simp, to_additive]
theorem swap_mem_mulAntidiagonal :
    x.swap ∈ Finset.mulAntidiagonal hs ht a ↔ x ∈ Finset.mulAntidiagonal ht hs a := by
  simp [mul_comm, and_left_comm]
#align finset.swap_mem_mul_antidiagonal Finset.swap_mem_mulAntidiagonal
#align finset.swap_mem_add_antidiagonal Finset.swap_mem_add_antidiagonal

@[to_additive]
theorem support_mulAntidiagonal_subset_mul : { a | (mulAntidiagonal hs ht a).Nonempty } ⊆ s * t :=
  fun a ⟨b, hb⟩ => by
  rw [mem_mul_antidiagonal] at hb
  exact ⟨b.1, b.2, hb⟩
#align finset.support_mul_antidiagonal_subset_mul Finset.support_mulAntidiagonal_subset_mul
#align finset.support_add_antidiagonal_subset_add Finset.support_add_antidiagonal_subset_add

@[to_additive]
theorem isPwo_support_mulAntidiagonal : { a | (mulAntidiagonal hs ht a).Nonempty }.IsPwo :=
  (hs.mul ht).mono support_mulAntidiagonal_subset_mul
#align finset.is_pwo_support_mul_antidiagonal Finset.isPwo_support_mulAntidiagonal
#align finset.is_pwo_support_add_antidiagonal Finset.isPwo_support_add_antidiagonal

@[to_additive]
theorem mulAntidiagonal_min_mul_min {α} [LinearOrderedCancelCommMonoid α] {s t : Set α}
    (hs : s.IsWf) (ht : t.IsWf) (hns : s.Nonempty) (hnt : t.Nonempty) :
    mulAntidiagonal hs.IsPwo ht.IsPwo (hs.min hns * ht.min hnt) = {(hs hns, ht hnt)} :=
  by
  ext ⟨a, b⟩
  simp only [mem_mul_antidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (mul_lt_mul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, mul_left_cancel hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩
#align finset.mul_antidiagonal_min_mul_min Finset.mulAntidiagonal_min_mul_min
#align finset.add_antidiagonal_min_add_min Finset.add_antidiagonal_min_add_min

end Finset

