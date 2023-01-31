/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finsupp.interval
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Finsupp
import Mathbin.Data.Finset.LocallyFinite
import Mathbin.Data.Finsupp.Order

/-!
# Finite intervals of finitely supported functions

This file provides the `locally_finite_order` instance for `ι →₀ α` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.

## Main declarations

* `finsupp.range_singleton`: Postcomposition with `has_singleton.singleton` on `finset` as a
  `finsupp`.
* `finsupp.range_Icc`: Postcomposition with `finset.Icc` as a `finsupp`.

Both these definitions use the fact that `0 = {0}` to ensure that the resulting function is finitely
supported.
-/


noncomputable section

open Finset Finsupp Function

open BigOperators Classical Pointwise

variable {ι α : Type _}

namespace Finsupp

section RangeSingleton

variable [Zero α] {f : ι →₀ α} {i : ι} {a : α}

/-- Pointwise `finset.singleton` bundled as a `finsupp`. -/
@[simps]
def rangeSingleton (f : ι →₀ α) : ι →₀ Finset α
    where
  toFun i := {f i}
  support := f.support
  mem_support_to_fun i :=
    by
    rw [← not_iff_not, not_mem_support_iff, not_ne_iff]
    exact singleton_injective.eq_iff.symm
#align finsupp.range_singleton Finsupp.rangeSingleton

theorem mem_rangeSingleton_apply_iff : a ∈ f.rangeSingleton i ↔ a = f i :=
  mem_singleton
#align finsupp.mem_range_singleton_apply_iff Finsupp.mem_rangeSingleton_apply_iff

end RangeSingleton

section RangeIcc

variable [Zero α] [PartialOrder α] [LocallyFiniteOrder α] {f g : ι →₀ α} {i : ι} {a : α}

/-- Pointwise `finset.Icc` bundled as a `finsupp`. -/
@[simps toFun]
def rangeIcc (f g : ι →₀ α) : ι →₀ Finset α
    where
  toFun i := Icc (f i) (g i)
  support :=
    haveI := Classical.decEq ι
    f.support ∪ g.support
  mem_support_to_fun i :=
    by
    rw [mem_union, ← not_iff_not, not_or, not_mem_support_iff, not_mem_support_iff, not_ne_iff]
    exact Icc_eq_singleton_iff.symm
#align finsupp.range_Icc Finsupp.rangeIcc

@[simp]
theorem rangeIcc_support [DecidableEq ι] (f g : ι →₀ α) :
    (rangeIcc f g).support = f.support ∪ g.support := by convert rfl
#align finsupp.range_Icc_support Finsupp.rangeIcc_support

theorem mem_rangeIcc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i :=
  mem_Icc
#align finsupp.mem_range_Icc_apply_iff Finsupp.mem_rangeIcc_apply_iff

end RangeIcc

section PartialOrder

variable [PartialOrder α] [Zero α] [LocallyFiniteOrder α] (f g : ι →₀ α)

instance : LocallyFiniteOrder (ι →₀ α) := by
  haveI := Classical.decEq ι <;> haveI := Classical.decEq α <;>
    exact
      LocallyFiniteOrder.ofIcc (ι →₀ α) (fun f g => (f.support ∪ g.support).Finsupp <| f.rangeIcc g)
        fun f g x =>
        by
        refine'
          (mem_finsupp_iff_of_support_subset <| Finset.subset_of_eq <| range_Icc_support _ _).trans
            _
        simp_rw [mem_range_Icc_apply_iff]
        exact forall_and

theorem icc_eq [DecidableEq ι] : Icc f g = (f.support ∪ g.support).Finsupp (f.rangeIcc g) := by
  convert rfl
#align finsupp.Icc_eq Finsupp.icc_eq

theorem card_icc [DecidableEq ι] :
    (Icc f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card := by
  simp_rw [Icc_eq, card_finsupp, range_Icc_to_fun]
#align finsupp.card_Icc Finsupp.card_icc

theorem card_ico [DecidableEq ι] :
    (Ico f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
#align finsupp.card_Ico Finsupp.card_ico

theorem card_ioc [DecidableEq ι] :
    (Ioc f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
#align finsupp.card_Ioc Finsupp.card_ioc

theorem card_ioo [DecidableEq ι] :
    (Ioo f g).card = (∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
#align finsupp.card_Ioo Finsupp.card_ioo

end PartialOrder

section CanonicallyOrdered

variable [CanonicallyOrderedAddMonoid α] [LocallyFiniteOrder α]

variable (f : ι →₀ α)

theorem card_iic : (Iic f).card = ∏ i in f.support, (Iic (f i)).card := by
  classical simp_rw [Iic_eq_Icc, card_Icc, Finsupp.bot_eq_zero, support_zero, empty_union,
      zero_apply, bot_eq_zero]
#align finsupp.card_Iic Finsupp.card_iic

theorem card_iio : (Iio f).card = (∏ i in f.support, (Iic (f i)).card) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]
#align finsupp.card_Iio Finsupp.card_iio

end CanonicallyOrdered

end Finsupp

