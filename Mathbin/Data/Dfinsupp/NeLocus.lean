/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyan Xu

! This file was ported from Lean 3 source module data.dfinsupp.ne_locus
! leanprover-community/mathlib commit a437a2499163d85d670479f69f625f461cc5fef9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Dfinsupp.Basic

/-!
# Locus of unequal values of finitely supported dependent functions

Let `N : α → Type*` be a type family, assume that `N a` has a `0` for all `a : α` and let
`f g : Π₀ a, N a` be finitely supported dependent functions.

## Main definition

* `dfinsupp.ne_locus f g : finset α`, the finite subset of `α` where `f` and `g` differ.
In the case in which `N a` is an additive group for all `a`, `dfinsupp.ne_locus f g` coincides with
`dfinsupp.support (f - g)`.
-/


variable {α : Type _} {N : α → Type _}

namespace Dfinsupp

variable [DecidableEq α]

section NHasZero

variable [∀ a, DecidableEq (N a)] [∀ a, Zero (N a)] (f g : Π₀ a, N a)

/-- Given two finitely supported functions `f g : α →₀ N`, `finsupp.ne_locus f g` is the `finset`
where `f` and `g` differ. This generalizes `(f - g).support` to situations without subtraction. -/
def neLocus (f g : Π₀ a, N a) : Finset α :=
  (f.support ∪ g.support).filter fun x => f x ≠ g x
#align dfinsupp.ne_locus Dfinsupp.neLocus

@[simp]
theorem mem_ne_locus {f g : Π₀ a, N a} {a : α} : a ∈ f.neLocus g ↔ f a ≠ g a := by
  simpa only [ne_locus, Finset.mem_filter, Finset.mem_union, mem_support_iff,
    and_iff_right_iff_imp] using Ne.ne_or_ne _
#align dfinsupp.mem_ne_locus Dfinsupp.mem_ne_locus

theorem not_mem_ne_locus {f g : Π₀ a, N a} {a : α} : a ∉ f.neLocus g ↔ f a = g a :=
  mem_ne_locus.Not.trans not_ne_iff
#align dfinsupp.not_mem_ne_locus Dfinsupp.not_mem_ne_locus

@[simp]
theorem coe_ne_locus : ↑(f.neLocus g) = { x | f x ≠ g x } :=
  Set.ext fun x => mem_ne_locus
#align dfinsupp.coe_ne_locus Dfinsupp.coe_ne_locus

@[simp]
theorem ne_locus_eq_empty {f g : Π₀ a, N a} : f.neLocus g = ∅ ↔ f = g :=
  ⟨fun h =>
    ext fun a => not_not.mp (mem_ne_locus.Not.mp (Finset.eq_empty_iff_forall_not_mem.mp h a)),
    fun h => h ▸ by simp only [ne_locus, Ne.def, eq_self_iff_true, not_true, Finset.filter_false]⟩
#align dfinsupp.ne_locus_eq_empty Dfinsupp.ne_locus_eq_empty

@[simp]
theorem nonempty_ne_locus_iff {f g : Π₀ a, N a} : (f.neLocus g).Nonempty ↔ f ≠ g :=
  Finset.nonempty_iff_ne_empty.trans ne_locus_eq_empty.Not
#align dfinsupp.nonempty_ne_locus_iff Dfinsupp.nonempty_ne_locus_iff

theorem ne_locus_comm : f.neLocus g = g.neLocus f := by
  simp_rw [ne_locus, Finset.union_comm, ne_comm]
#align dfinsupp.ne_locus_comm Dfinsupp.ne_locus_comm

@[simp]
theorem ne_locus_zero_right : f.neLocus 0 = f.support :=
  by
  ext
  rw [mem_ne_locus, mem_support_iff, coe_zero, Pi.zero_apply]
#align dfinsupp.ne_locus_zero_right Dfinsupp.ne_locus_zero_right

@[simp]
theorem ne_locus_zero_left : (0 : Π₀ a, N a).neLocus f = f.support :=
  (ne_locus_comm _ _).trans (ne_locus_zero_right _)
#align dfinsupp.ne_locus_zero_left Dfinsupp.ne_locus_zero_left

end NHasZero

section NeLocusAndMaps

variable {M P : α → Type _} [∀ a, Zero (N a)] [∀ a, Zero (M a)] [∀ a, Zero (P a)]

theorem subset_map_range_ne_locus [∀ a, DecidableEq (N a)] [∀ a, DecidableEq (M a)]
    (f g : Π₀ a, N a) {F : ∀ a, N a → M a} (F0 : ∀ a, F a 0 = 0) :
    (f.map_range F F0).neLocus (g.map_range F F0) ⊆ f.neLocus g := fun a => by
  simpa only [mem_ne_locus, map_range_apply, not_imp_not] using congr_arg (F a)
#align dfinsupp.subset_map_range_ne_locus Dfinsupp.subset_map_range_ne_locus

theorem zip_with_ne_locus_eq_left [∀ a, DecidableEq (N a)] [∀ a, DecidableEq (P a)]
    {F : ∀ a, M a → N a → P a} (F0 : ∀ a, F a 0 0 = 0) (f : Π₀ a, M a) (g₁ g₂ : Π₀ a, N a)
    (hF : ∀ a f, Function.Injective fun g => F a f g) :
    (zipWith F F0 f g₁).neLocus (zipWith F F0 f g₂) = g₁.neLocus g₂ :=
  by
  ext
  simpa only [mem_ne_locus] using (hF a _).ne_iff
#align dfinsupp.zip_with_ne_locus_eq_left Dfinsupp.zip_with_ne_locus_eq_left

theorem zip_with_ne_locus_eq_right [∀ a, DecidableEq (M a)] [∀ a, DecidableEq (P a)]
    {F : ∀ a, M a → N a → P a} (F0 : ∀ a, F a 0 0 = 0) (f₁ f₂ : Π₀ a, M a) (g : Π₀ a, N a)
    (hF : ∀ a g, Function.Injective fun f => F a f g) :
    (zipWith F F0 f₁ g).neLocus (zipWith F F0 f₂ g) = f₁.neLocus f₂ :=
  by
  ext
  simpa only [mem_ne_locus] using (hF a _).ne_iff
#align dfinsupp.zip_with_ne_locus_eq_right Dfinsupp.zip_with_ne_locus_eq_right

theorem map_range_ne_locus_eq [∀ a, DecidableEq (N a)] [∀ a, DecidableEq (M a)] (f g : Π₀ a, N a)
    {F : ∀ a, N a → M a} (F0 : ∀ a, F a 0 = 0) (hF : ∀ a, Function.Injective (F a)) :
    (f.map_range F F0).neLocus (g.map_range F F0) = f.neLocus g :=
  by
  ext
  simpa only [mem_ne_locus] using (hF a).ne_iff
#align dfinsupp.map_range_ne_locus_eq Dfinsupp.map_range_ne_locus_eq

end NeLocusAndMaps

variable [∀ a, DecidableEq (N a)]

@[simp]
theorem ne_locus_add_left [∀ a, AddLeftCancelMonoid (N a)] (f g h : Π₀ a, N a) :
    (f + g).neLocus (f + h) = g.neLocus h :=
  (zip_with_ne_locus_eq_left _ _ _ _) fun a => add_right_injective
#align dfinsupp.ne_locus_add_left Dfinsupp.ne_locus_add_left

@[simp]
theorem ne_locus_add_right [∀ a, AddRightCancelMonoid (N a)] (f g h : Π₀ a, N a) :
    (f + h).neLocus (g + h) = f.neLocus g :=
  (zip_with_ne_locus_eq_right _ _ _ _) fun a => add_left_injective
#align dfinsupp.ne_locus_add_right Dfinsupp.ne_locus_add_right

section AddGroup

variable [∀ a, AddGroup (N a)] (f f₁ f₂ g g₁ g₂ : Π₀ a, N a)

@[simp]
theorem ne_locus_neg_neg : neLocus (-f) (-g) = f.neLocus g :=
  map_range_ne_locus_eq _ _ (fun a => neg_zero) fun a => neg_injective
#align dfinsupp.ne_locus_neg_neg Dfinsupp.ne_locus_neg_neg

theorem ne_locus_neg : neLocus (-f) g = f.neLocus (-g) := by rw [← ne_locus_neg_neg, neg_neg]
#align dfinsupp.ne_locus_neg Dfinsupp.ne_locus_neg

theorem ne_locus_eq_support_sub : f.neLocus g = (f - g).support := by
  rw [← @ne_locus_add_right α N _ _ _ _ _ (-g), add_right_neg, ne_locus_zero_right, sub_eq_add_neg]
#align dfinsupp.ne_locus_eq_support_sub Dfinsupp.ne_locus_eq_support_sub

@[simp]
theorem ne_locus_sub_left : neLocus (f - g₁) (f - g₂) = neLocus g₁ g₂ := by
  simp only [sub_eq_add_neg, @ne_locus_add_left α N _ _ _, ne_locus_neg_neg]
#align dfinsupp.ne_locus_sub_left Dfinsupp.ne_locus_sub_left

@[simp]
theorem ne_locus_sub_right : neLocus (f₁ - g) (f₂ - g) = neLocus f₁ f₂ := by
  simpa only [sub_eq_add_neg] using @ne_locus_add_right α N _ _ _ _ _ _
#align dfinsupp.ne_locus_sub_right Dfinsupp.ne_locus_sub_right

@[simp]
theorem ne_locus_self_add_right : neLocus f (f + g) = g.support := by
  rw [← ne_locus_zero_left, ← @ne_locus_add_left α N _ _ _ f 0 g, add_zero]
#align dfinsupp.ne_locus_self_add_right Dfinsupp.ne_locus_self_add_right

@[simp]
theorem ne_locus_self_add_left : neLocus (f + g) f = g.support := by
  rw [ne_locus_comm, ne_locus_self_add_right]
#align dfinsupp.ne_locus_self_add_left Dfinsupp.ne_locus_self_add_left

@[simp]
theorem ne_locus_self_sub_right : neLocus f (f - g) = g.support := by
  rw [sub_eq_add_neg, ne_locus_self_add_right, support_neg]
#align dfinsupp.ne_locus_self_sub_right Dfinsupp.ne_locus_self_sub_right

@[simp]
theorem ne_locus_self_sub_left : neLocus (f - g) f = g.support := by
  rw [ne_locus_comm, ne_locus_self_sub_right]
#align dfinsupp.ne_locus_self_sub_left Dfinsupp.ne_locus_self_sub_left

end AddGroup

end Dfinsupp

