/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Algebra.Order.Group.Int
import Data.Nat.SuccPred

#align_import data.int.succ_pred from "leanprover-community/mathlib"@"e04043d6bf7264a3c84bc69711dc354958ca4516"

/-!
# Successors and predecessors of integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we show that `ℤ` is both an archimedean `succ_order` and an archimedean `pred_order`.
-/


open Function Order

namespace Int

-- so that Lean reads `int.succ` through `succ_order.succ`
@[reducible]
instance : SuccOrder ℤ :=
  { SuccOrder.ofSuccLeIff succ fun a b => Iff.rfl with succ := succ }

-- so that Lean reads `int.pred` through `pred_order.pred`
@[reducible]
instance : PredOrder ℤ where
  pred := pred
  pred_le a := (sub_one_lt_of_le le_rfl).le
  min_of_le_pred a ha := ((sub_one_lt_of_le le_rfl).not_le ha).elim
  le_pred_of_lt a b := le_sub_one_of_lt
  le_of_pred_lt a b := le_of_sub_one_lt

#print Int.succ_eq_succ /-
@[simp]
theorem succ_eq_succ : Order.succ = succ :=
  rfl
#align int.succ_eq_succ Int.succ_eq_succ
-/

#print Int.pred_eq_pred /-
@[simp]
theorem pred_eq_pred : Order.pred = pred :=
  rfl
#align int.pred_eq_pred Int.pred_eq_pred
-/

#print Int.pos_iff_one_le /-
theorem pos_iff_one_le {a : ℤ} : 0 < a ↔ 1 ≤ a :=
  Order.succ_le_iff.symm
#align int.pos_iff_one_le Int.pos_iff_one_le
-/

#print Int.succ_iterate /-
theorem succ_iterate (a : ℤ) : ∀ n, (succ^[n]) a = a + n
  | 0 => (add_zero a).symm
  | n + 1 => by
    rw [Function.iterate_succ', Int.ofNat_succ, ← add_assoc]
    exact congr_arg _ (succ_iterate n)
#align int.succ_iterate Int.succ_iterate
-/

#print Int.pred_iterate /-
theorem pred_iterate (a : ℤ) : ∀ n, (pred^[n]) a = a - n
  | 0 => (sub_zero a).symm
  | n + 1 => by
    rw [Function.iterate_succ', Int.ofNat_succ, ← sub_sub]
    exact congr_arg _ (pred_iterate n)
#align int.pred_iterate Int.pred_iterate
-/

instance : IsSuccArchimedean ℤ :=
  ⟨fun a b h =>
    ⟨(b - a).toNat, by
      rw [succ_eq_succ, succ_iterate, to_nat_sub_of_le h, ← add_sub_assoc, add_sub_cancel_left]⟩⟩

instance : IsPredArchimedean ℤ :=
  ⟨fun a b h =>
    ⟨(b - a).toNat, by rw [pred_eq_pred, pred_iterate, to_nat_sub_of_le h, sub_sub_cancel]⟩⟩

/-! ### Covering relation -/


#print Int.covBy_iff_succ_eq /-
protected theorem covBy_iff_succ_eq {m n : ℤ} : m ⋖ n ↔ m + 1 = n :=
  succ_eq_iff_covBy.symm
#align int.covby_iff_succ_eq Int.covBy_iff_succ_eq
-/

#print Int.sub_one_covBy /-
@[simp]
theorem sub_one_covBy (z : ℤ) : z - 1 ⋖ z := by rw [Int.covBy_iff_succ_eq, sub_add_cancel]
#align int.sub_one_covby Int.sub_one_covBy
-/

#print Int.covBy_add_one /-
@[simp]
theorem covBy_add_one (z : ℤ) : z ⋖ z + 1 :=
  Int.covBy_iff_succ_eq.mpr rfl
#align int.covby_add_one Int.covBy_add_one
-/

end Int

#print Int.natCast_covBy /-
@[simp, norm_cast]
theorem Int.natCast_covBy {a b : ℕ} : (a : ℤ) ⋖ b ↔ a ⋖ b := by
  rw [Nat.covBy_iff_succ_eq, Int.covBy_iff_succ_eq]; exact Int.natCast_inj
#align nat.cast_int_covby_iff Int.natCast_covBy
-/

alias ⟨_, CovBy.intCast⟩ := Int.natCast_covBy
#align covby.cast_int CovBy.intCast

