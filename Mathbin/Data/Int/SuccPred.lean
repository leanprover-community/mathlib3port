import Mathbin.Data.Int.Basic 
import Mathbin.Order.SuccPred

/-!
# Successors and predecessors of integers

In this file, we show that `ℤ` is both an archimedean `succ_order` and an archimedean `pred_order`.
-/


open Function Int

@[reducible]
instance  : SuccOrder ℤ :=
  { SuccOrder.ofSuccLeIff succ fun a b => Iff.rfl with succ := succ }

@[reducible]
instance  : PredOrder ℤ :=
  { pred := pred, pred_le := fun a => (sub_one_lt_of_le le_rfl).le,
    minimal_of_le_pred := fun a ha => ((sub_one_lt_of_le le_rfl).not_le ha).elim,
    le_pred_of_lt := fun a b => le_sub_one_of_lt, le_of_pred_lt := fun a b => le_of_sub_one_lt }

theorem Int.succ_iterate (a : ℤ) : ∀ n, (succ^[n]) a = a+n
| 0 => (add_zeroₓ a).symm
| n+1 =>
  by 
    rw [Function.iterate_succ', Int.coe_nat_succ, ←add_assocₓ]
    exact congr_argₓ _ (Int.succ_iterate n)

theorem Int.pred_iterate (a : ℤ) : ∀ n, (pred^[n]) a = a - n
| 0 => (sub_zero a).symm
| n+1 =>
  by 
    rw [Function.iterate_succ', Int.coe_nat_succ, ←sub_sub]
    exact congr_argₓ _ (Int.pred_iterate n)

instance  : IsSuccArchimedean ℤ :=
  ⟨fun a b h =>
      ⟨(b - a).toNat,
        by 
          rw [Int.succ_iterate, Int.to_nat_sub_of_le h, ←add_sub_assoc, add_sub_cancel']⟩⟩

instance  : IsPredArchimedean ℤ :=
  ⟨fun a b h =>
      ⟨(b - a).toNat,
        by 
          rw [Int.pred_iterate, Int.to_nat_sub_of_le h, sub_sub_cancel]⟩⟩

