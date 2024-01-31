/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Data.Finset.Finsupp
import Data.Finset.LocallyFinite
import Data.Finsupp.Order

#align_import data.finsupp.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Finite intervals of finitely supported functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

open scoped BigOperators Classical Pointwise

variable {ι α : Type _}

namespace Finsupp

section RangeSingleton

variable [Zero α] {f : ι →₀ α} {i : ι} {a : α}

#print Finsupp.rangeSingleton /-
/-- Pointwise `finset.singleton` bundled as a `finsupp`. -/
@[simps]
def rangeSingleton (f : ι →₀ α) : ι →₀ Finset α
    where
  toFun i := {f i}
  support := f.support
  mem_support_toFun i := by
    rw [← not_iff_not, not_mem_support_iff, not_ne_iff]
    exact singleton_injective.eq_iff.symm
#align finsupp.range_singleton Finsupp.rangeSingleton
-/

#print Finsupp.mem_rangeSingleton_apply_iff /-
theorem mem_rangeSingleton_apply_iff : a ∈ f.rangeSingleton i ↔ a = f i :=
  mem_singleton
#align finsupp.mem_range_singleton_apply_iff Finsupp.mem_rangeSingleton_apply_iff
-/

end RangeSingleton

section RangeIcc

variable [Zero α] [PartialOrder α] [LocallyFiniteOrder α] {f g : ι →₀ α} {i : ι} {a : α}

#print Finsupp.rangeIcc /-
/-- Pointwise `finset.Icc` bundled as a `finsupp`. -/
@[simps toFun]
def rangeIcc (f g : ι →₀ α) : ι →₀ Finset α
    where
  toFun i := Icc (f i) (g i)
  support :=
    haveI := Classical.decEq ι
    f.support ∪ g.support
  mem_support_toFun i :=
    by
    rw [mem_union, ← not_iff_not, not_or, not_mem_support_iff, not_mem_support_iff, not_ne_iff]
    exact Icc_eq_singleton_iff.symm
#align finsupp.range_Icc Finsupp.rangeIcc
-/

#print Finsupp.rangeIcc_support /-
@[simp]
theorem rangeIcc_support [DecidableEq ι] (f g : ι →₀ α) :
    (rangeIcc f g).support = f.support ∪ g.support := by convert rfl
#align finsupp.range_Icc_support Finsupp.rangeIcc_support
-/

#print Finsupp.mem_rangeIcc_apply_iff /-
theorem mem_rangeIcc_apply_iff : a ∈ f.rangeIcc g i ↔ f i ≤ a ∧ a ≤ g i :=
  mem_Icc
#align finsupp.mem_range_Icc_apply_iff Finsupp.mem_rangeIcc_apply_iff
-/

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

#print Finsupp.Icc_eq /-
theorem Icc_eq [DecidableEq ι] : Icc f g = (f.support ∪ g.support).Finsupp (f.rangeIcc g) := by
  convert rfl
#align finsupp.Icc_eq Finsupp.Icc_eq
-/

#print Finsupp.card_Icc /-
theorem card_Icc [DecidableEq ι] :
    (Icc f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card := by
  simp_rw [Icc_eq, card_finsupp, range_Icc_to_fun]
#align finsupp.card_Icc Finsupp.card_Icc
-/

#print Finsupp.card_Ico /-
theorem card_Ico [DecidableEq ι] :
    (Ico f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
#align finsupp.card_Ico Finsupp.card_Ico
-/

#print Finsupp.card_Ioc /-
theorem card_Ioc [DecidableEq ι] :
    (Ioc f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
#align finsupp.card_Ioc Finsupp.card_Ioc
-/

#print Finsupp.card_Ioo /-
theorem card_Ioo [DecidableEq ι] :
    (Ioo f g).card = ∏ i in f.support ∪ g.support, (Icc (f i) (g i)).card - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
#align finsupp.card_Ioo Finsupp.card_Ioo
-/

end PartialOrder

section Lattice

variable [Lattice α] [Zero α] [LocallyFiniteOrder α] (f g : ι →₀ α)

#print Finsupp.card_uIcc /-
theorem card_uIcc [DecidableEq ι] :
    (uIcc f g).card = ∏ i in f.support ∪ g.support, (uIcc (f i) (g i)).card := by
  rw [← support_inf_union_support_sup]; exact card_Icc _ _
#align finsupp.card_uIcc Finsupp.card_uIcc
-/

end Lattice

section CanonicallyOrdered

variable [CanonicallyOrderedAddCommMonoid α] [LocallyFiniteOrder α]

variable (f : ι →₀ α)

#print Finsupp.card_Iic /-
theorem card_Iic : (Iic f).card = ∏ i in f.support, (Iic (f i)).card := by classical
#align finsupp.card_Iic Finsupp.card_Iic
-/

#print Finsupp.card_Iio /-
theorem card_Iio : (Iio f).card = ∏ i in f.support, (Iic (f i)).card - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]
#align finsupp.card_Iio Finsupp.card_Iio
-/

end CanonicallyOrdered

end Finsupp

