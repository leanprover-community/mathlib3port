/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
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
  (f.Support ∪ g.Support).filter fun x => f x ≠ g x

@[simp]
theorem mem_ne_locus {f g : α →₀ N} {a : α} : a ∈ f.neLocus g ↔ f a ≠ g a := by
  simpa only [ne_locus, Finset.mem_filter, Finset.mem_union, mem_support_iff, and_iff_right_iff_imp] using Ne.ne_or_ne _

@[simp]
theorem coe_ne_locus : ↑(f.neLocus g) = { x | f x ≠ g x } := by
  ext
  exact mem_ne_locus

@[simp]
theorem ne_locus_eq_empty {f g : α →₀ N} : f.neLocus g = ∅ ↔ f = g :=
  ⟨fun h => ext fun a => not_not.mp (mem_ne_locus.Not.mp (Finset.eq_empty_iff_forall_not_mem.mp h a)), fun h =>
    h ▸ by
      simp only [ne_locus, Ne.def, eq_self_iff_true, not_true, Finset.filter_false]⟩

@[simp]
theorem nonempty_ne_locus_iff {f g : α →₀ N} : (f.neLocus g).Nonempty ↔ f ≠ g :=
  Finset.nonempty_iff_ne_empty.trans ne_locus_eq_empty.Not

theorem ne_locus_comm : f.neLocus g = g.neLocus f := by
  simp_rw [ne_locus, Finset.union_comm, ne_comm]

@[simp]
theorem ne_locus_zero_right : f.neLocus 0 = f.Support := by
  ext
  rw [mem_ne_locus, mem_support_iff, coe_zero, Pi.zero_apply]

@[simp]
theorem ne_locus_zero_left : (0 : α →₀ N).neLocus f = f.Support :=
  (ne_locus_comm _ _).trans (ne_locus_zero_right _)

end NHasZero

section NeLocusAndMaps

theorem subset_map_range_ne_locus [DecidableEq N] [Zero N] [DecidableEq M] [Zero M] (f g : α →₀ N) {F : N → M}
    (F0 : F 0 = 0) : (f.map_range F F0).neLocus (g.map_range F F0) ⊆ f.neLocus g := fun x => by
  simpa only [mem_ne_locus, map_range_apply, not_imp_not] using congr_arg F

theorem zip_with_ne_locus_eq_left [DecidableEq N] [Zero M] [DecidableEq P] [Zero P] [Zero N] {F : M → N → P}
    (F0 : F 0 0 = 0) (f : α →₀ M) (g₁ g₂ : α →₀ N) (hF : ∀ f, Function.Injective fun g => F f g) :
    (zipWith F F0 f g₁).neLocus (zipWith F F0 f g₂) = g₁.neLocus g₂ := by
  ext
  simpa only [mem_ne_locus] using (hF _).ne_iff

theorem zip_with_ne_locus_eq_right [DecidableEq M] [Zero M] [DecidableEq P] [Zero P] [Zero N] {F : M → N → P}
    (F0 : F 0 0 = 0) (f₁ f₂ : α →₀ M) (g : α →₀ N) (hF : ∀ g, Function.Injective fun f => F f g) :
    (zipWith F F0 f₁ g).neLocus (zipWith F F0 f₂ g) = f₁.neLocus f₂ := by
  ext
  simpa only [mem_ne_locus] using (hF _).ne_iff

theorem map_range_ne_locus_eq [DecidableEq N] [DecidableEq M] [Zero M] [Zero N] (f g : α →₀ N) {F : N → M}
    (F0 : F 0 = 0) (hF : Function.Injective F) : (f.map_range F F0).neLocus (g.map_range F F0) = f.neLocus g := by
  ext
  simpa only [mem_ne_locus] using hF.ne_iff

end NeLocusAndMaps

section CancelAndGroup

variable [DecidableEq N]

@[simp]
theorem add_ne_locus_add_eq_left [AddLeftCancelMonoid N] (f g h : α →₀ N) : (f + g).neLocus (f + h) = g.neLocus h :=
  zip_with_ne_locus_eq_left _ _ _ _ add_right_injective

@[simp]
theorem add_ne_locus_add_eq_right [AddRightCancelMonoid N] (f g h : α →₀ N) : (f + h).neLocus (g + h) = f.neLocus g :=
  zip_with_ne_locus_eq_right _ _ _ _ add_left_injective

@[simp]
theorem neg_ne_locus_neg [AddGroupₓ N] (f g : α →₀ N) : (-f).neLocus (-g) = f.neLocus g :=
  map_range_ne_locus_eq _ _ neg_zero neg_injective

theorem ne_locus_neg [AddGroupₓ N] (f g : α →₀ N) : (-f).neLocus g = f.neLocus (-g) := by
  rw [← neg_ne_locus_neg _ _, neg_negₓ]

theorem ne_locus_eq_support_sub [AddGroupₓ N] (f g : α →₀ N) : f.neLocus g = (f - g).Support := by
  rw [← add_ne_locus_add_eq_right _ _ (-g), add_right_negₓ, ne_locus_zero_right, sub_eq_add_neg]

@[simp]
theorem sub_ne_locus_sub_eq_left [AddGroupₓ N] (f g h : α →₀ N) : (f - g).neLocus (f - h) = g.neLocus h :=
  zip_with_ne_locus_eq_left _ _ _ _ fun fn => sub_right_injective

@[simp]
theorem sub_ne_locus_sub_eq_right [AddGroupₓ N] (f g h : α →₀ N) : (f - h).neLocus (g - h) = f.neLocus g :=
  zip_with_ne_locus_eq_right _ _ _ _ fun hn => sub_left_injective

end CancelAndGroup

end Finsupp

