/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Data.Finset.LocallyFinite
import Data.Dfinsupp.Interval
import Data.Dfinsupp.Multiset
import Data.Nat.Interval

#align_import data.multiset.interval from "leanprover-community/mathlib"@"1d29de43a5ba4662dd33b5cfeecfc2a27a5a8a29"

/-!
# Finite intervals of multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the `locally_finite_order` instance for `multiset α` and calculates the
cardinality of its finite intervals.

## Implementation notes

We implement the intervals via the intervals on `dfinsupp`, rather than via filtering
`multiset.powerset`; this is because `(multiset.replicate n x).powerset` has `2^n` entries not `n+1`
entries as it contains duplicates. We do not go via `finsupp` as this would be noncomputable, and
multisets are typically used computationally.

-/


open Finset DFinsupp Function

open scoped BigOperators Pointwise

variable {α : Type _}

namespace Multiset

variable [DecidableEq α] (s t : Multiset α)

instance : LocallyFiniteOrder (Multiset α) :=
  LocallyFiniteOrder.ofIcc (Multiset α)
    (fun s t =>
      (Finset.Icc s.toDFinsupp t.toDFinsupp).map Multiset.equivDFinsupp.toEquiv.symm.toEmbedding)
    fun s t x => by simp

#print Multiset.Icc_eq /-
theorem Icc_eq :
    Finset.Icc s t =
      (Finset.Icc s.toDFinsupp t.toDFinsupp).map Multiset.equivDFinsupp.toEquiv.symm.toEmbedding :=
  rfl
#align multiset.Icc_eq Multiset.Icc_eq
-/

#print Multiset.uIcc_eq /-
theorem uIcc_eq :
    uIcc s t =
      (uIcc s.toDFinsupp t.toDFinsupp).map Multiset.equivDFinsupp.toEquiv.symm.toEmbedding :=
  (Icc_eq _ _).trans <| by simp [uIcc]
#align multiset.uIcc_eq Multiset.uIcc_eq
-/

#print Multiset.card_Icc /-
theorem card_Icc :
    (Finset.Icc s t).card = ∏ i in s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) := by
  simp_rw [Icc_eq, Finset.card_map, DFinsupp.card_Icc, Nat.card_Icc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]
#align multiset.card_Icc Multiset.card_Icc
-/

#print Multiset.card_Ico /-
theorem card_Ico :
    (Finset.Ico s t).card = ∏ i in s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
#align multiset.card_Ico Multiset.card_Ico
-/

#print Multiset.card_Ioc /-
theorem card_Ioc :
    (Finset.Ioc s t).card = ∏ i in s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
#align multiset.card_Ioc Multiset.card_Ioc
-/

#print Multiset.card_Ioo /-
theorem card_Ioo :
    (Finset.Ioo s t).card = ∏ i in s.toFinset ∪ t.toFinset, (t.count i + 1 - s.count i) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
#align multiset.card_Ioo Multiset.card_Ioo
-/

#print Multiset.card_uIcc /-
theorem card_uIcc :
    (uIcc s t).card = ∏ i in s.toFinset ∪ t.toFinset, ((t.count i - s.count i : ℤ).natAbs + 1) := by
  simp_rw [uIcc_eq, Finset.card_map, DFinsupp.card_uIcc, Nat.card_uIcc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]
#align multiset.card_uIcc Multiset.card_uIcc
-/

#print Multiset.card_Iic /-
theorem card_Iic : (Finset.Iic s).card = ∏ i in s.toFinset, (s.count i + 1) := by
  simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, to_finset_zero, empty_union, count_zero, tsub_zero]
#align multiset.card_Iic Multiset.card_Iic
-/

end Multiset

