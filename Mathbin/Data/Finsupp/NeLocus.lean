/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module data.finsupp.ne_locus
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Defs

/-!
# Locus of unequal values of finitely supported functions

Let `α N` be two Types, assume that `N` has a `0` and let `f g : α →₀ N` be finitely supported
functions.

## Main definition

* `finsupp.ne_locus f g : finset α`, the finite subset of `α` where `f` and `g` differ.

In the case in which `N` is an additive group, `finsupp.ne_locus f g` coincides with
`finsupp.support (f - g)`.
-/


variable {α M N P : Type _}

namespace Finsupp

variable [DecidableEq α]

section NHasZero

variable [DecidableEq N] [Zero N] (f g : α →₀ N)

/-- Given two finitely supported functions `f g : α →₀ N`, `finsupp.ne_locus f g` is the `finset`
where `f` and `g` differ. This generalizes `(f - g).support` to situations without subtraction. -/
def neLocus (f g : α →₀ N) : Finset α :=
  (f.support ∪ g.support).filter fun x => f x ≠ g x
#align finsupp.ne_locus Finsupp.neLocus

@[simp]
theorem mem_ne_locus {f g : α →₀ N} {a : α} : a ∈ f.neLocus g ↔ f a ≠ g a := by
  simpa only [ne_locus, Finset.mem_filter, Finset.mem_union, mem_support_iff,
    and_iff_right_iff_imp] using Ne.ne_or_ne _
#align finsupp.mem_ne_locus Finsupp.mem_ne_locus

theorem not_mem_ne_locus {f g : α →₀ N} {a : α} : a ∉ f.neLocus g ↔ f a = g a :=
  mem_ne_locus.Not.trans not_ne_iff
#align finsupp.not_mem_ne_locus Finsupp.not_mem_ne_locus

@[simp]
theorem coe_ne_locus : ↑(f.neLocus g) = { x | f x ≠ g x } :=
  by
  ext
  exact mem_ne_locus
#align finsupp.coe_ne_locus Finsupp.coe_ne_locus

@[simp]
theorem ne_locus_eq_empty {f g : α →₀ N} : f.neLocus g = ∅ ↔ f = g :=
  ⟨fun h =>
    ext fun a => not_not.mp (mem_ne_locus.Not.mp (Finset.eq_empty_iff_forall_not_mem.mp h a)),
    fun h => h ▸ by simp only [ne_locus, Ne.def, eq_self_iff_true, not_true, Finset.filter_false]⟩
#align finsupp.ne_locus_eq_empty Finsupp.ne_locus_eq_empty

@[simp]
theorem nonempty_ne_locus_iff {f g : α →₀ N} : (f.neLocus g).Nonempty ↔ f ≠ g :=
  Finset.nonempty_iff_ne_empty.trans ne_locus_eq_empty.Not
#align finsupp.nonempty_ne_locus_iff Finsupp.nonempty_ne_locus_iff

theorem ne_locus_comm : f.neLocus g = g.neLocus f := by
  simp_rw [ne_locus, Finset.union_comm, ne_comm]
#align finsupp.ne_locus_comm Finsupp.ne_locus_comm

@[simp]
theorem ne_locus_zero_right : f.neLocus 0 = f.support :=
  by
  ext
  rw [mem_ne_locus, mem_support_iff, coe_zero, Pi.zero_apply]
#align finsupp.ne_locus_zero_right Finsupp.ne_locus_zero_right

@[simp]
theorem ne_locus_zero_left : (0 : α →₀ N).neLocus f = f.support :=
  (ne_locus_comm _ _).trans (ne_locus_zero_right _)
#align finsupp.ne_locus_zero_left Finsupp.ne_locus_zero_left

end NHasZero

section NeLocusAndMaps

theorem subset_map_range_ne_locus [DecidableEq N] [Zero N] [DecidableEq M] [Zero M] (f g : α →₀ N)
    {F : N → M} (F0 : F 0 = 0) : (f.mapRange F F0).neLocus (g.mapRange F F0) ⊆ f.neLocus g :=
  fun x => by simpa only [mem_ne_locus, map_range_apply, not_imp_not] using congr_arg F
#align finsupp.subset_map_range_ne_locus Finsupp.subset_map_range_ne_locus

theorem zip_with_ne_locus_eq_left [DecidableEq N] [Zero M] [DecidableEq P] [Zero P] [Zero N]
    {F : M → N → P} (F0 : F 0 0 = 0) (f : α →₀ M) (g₁ g₂ : α →₀ N)
    (hF : ∀ f, Function.Injective fun g => F f g) :
    (zipWith F F0 f g₁).neLocus (zipWith F F0 f g₂) = g₁.neLocus g₂ :=
  by
  ext
  simpa only [mem_ne_locus] using (hF _).ne_iff
#align finsupp.zip_with_ne_locus_eq_left Finsupp.zip_with_ne_locus_eq_left

theorem zip_with_ne_locus_eq_right [DecidableEq M] [Zero M] [DecidableEq P] [Zero P] [Zero N]
    {F : M → N → P} (F0 : F 0 0 = 0) (f₁ f₂ : α →₀ M) (g : α →₀ N)
    (hF : ∀ g, Function.Injective fun f => F f g) :
    (zipWith F F0 f₁ g).neLocus (zipWith F F0 f₂ g) = f₁.neLocus f₂ :=
  by
  ext
  simpa only [mem_ne_locus] using (hF _).ne_iff
#align finsupp.zip_with_ne_locus_eq_right Finsupp.zip_with_ne_locus_eq_right

theorem map_range_ne_locus_eq [DecidableEq N] [DecidableEq M] [Zero M] [Zero N] (f g : α →₀ N)
    {F : N → M} (F0 : F 0 = 0) (hF : Function.Injective F) :
    (f.mapRange F F0).neLocus (g.mapRange F F0) = f.neLocus g :=
  by
  ext
  simpa only [mem_ne_locus] using hF.ne_iff
#align finsupp.map_range_ne_locus_eq Finsupp.map_range_ne_locus_eq

end NeLocusAndMaps

variable [DecidableEq N]

@[simp]
theorem ne_locus_add_left [AddLeftCancelMonoid N] (f g h : α →₀ N) :
    (f + g).neLocus (f + h) = g.neLocus h :=
  zip_with_ne_locus_eq_left _ _ _ _ add_right_injective
#align finsupp.ne_locus_add_left Finsupp.ne_locus_add_left

@[simp]
theorem ne_locus_add_right [AddRightCancelMonoid N] (f g h : α →₀ N) :
    (f + h).neLocus (g + h) = f.neLocus g :=
  zip_with_ne_locus_eq_right _ _ _ _ add_left_injective
#align finsupp.ne_locus_add_right Finsupp.ne_locus_add_right

section AddGroup

variable [AddGroup N] (f f₁ f₂ g g₁ g₂ : α →₀ N)

@[simp]
theorem ne_locus_neg_neg : neLocus (-f) (-g) = f.neLocus g :=
  map_range_ne_locus_eq _ _ neg_zero neg_injective
#align finsupp.ne_locus_neg_neg Finsupp.ne_locus_neg_neg

theorem ne_locus_neg : neLocus (-f) g = f.neLocus (-g) := by rw [← ne_locus_neg_neg, neg_neg]
#align finsupp.ne_locus_neg Finsupp.ne_locus_neg

theorem ne_locus_eq_support_sub : f.neLocus g = (f - g).support := by
  rw [← ne_locus_add_right _ _ (-g), add_right_neg, ne_locus_zero_right, sub_eq_add_neg]
#align finsupp.ne_locus_eq_support_sub Finsupp.ne_locus_eq_support_sub

@[simp]
theorem ne_locus_sub_left : neLocus (f - g₁) (f - g₂) = neLocus g₁ g₂ := by
  simp only [sub_eq_add_neg, ne_locus_add_left, ne_locus_neg_neg]
#align finsupp.ne_locus_sub_left Finsupp.ne_locus_sub_left

@[simp]
theorem ne_locus_sub_right : neLocus (f₁ - g) (f₂ - g) = neLocus f₁ f₂ := by
  simpa only [sub_eq_add_neg] using ne_locus_add_right _ _ _
#align finsupp.ne_locus_sub_right Finsupp.ne_locus_sub_right

@[simp]
theorem ne_locus_self_add_right : neLocus f (f + g) = g.support := by
  rw [← ne_locus_zero_left, ← ne_locus_add_left f 0 g, add_zero]
#align finsupp.ne_locus_self_add_right Finsupp.ne_locus_self_add_right

@[simp]
theorem ne_locus_self_add_left : neLocus (f + g) f = g.support := by
  rw [ne_locus_comm, ne_locus_self_add_right]
#align finsupp.ne_locus_self_add_left Finsupp.ne_locus_self_add_left

@[simp]
theorem ne_locus_self_sub_right : neLocus f (f - g) = g.support := by
  rw [sub_eq_add_neg, ne_locus_self_add_right, support_neg]
#align finsupp.ne_locus_self_sub_right Finsupp.ne_locus_self_sub_right

@[simp]
theorem ne_locus_self_sub_left : neLocus (f - g) f = g.support := by
  rw [ne_locus_comm, ne_locus_self_sub_right]
#align finsupp.ne_locus_self_sub_left Finsupp.ne_locus_self_sub_left

end AddGroup

end Finsupp

