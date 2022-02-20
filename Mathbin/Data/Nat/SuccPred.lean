/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.SuccPred.Basic

/-!
# Successors and predecessors of naturals

In this file, we show that `ℕ` is both an archimedean `succ_order` and an archimedean `pred_order`.
-/


open Function Nat

-- so that Lean reads `nat.succ` through `succ_order.succ`
@[reducible]
instance : SuccOrder ℕ :=
  { SuccOrder.ofSuccLeIff succ fun a b => Iff.rfl with succ := succ }

-- so that Lean reads `nat.pred` through `pred_order.pred`
@[reducible]
instance : PredOrder ℕ where
  pred := pred
  pred_le := pred_leₓ
  minimal_of_le_pred := fun a ha b h => by
    cases a
    · exact b.not_lt_zero h
      
    · exact Nat.lt_irreflₓ a ha
      
  le_pred_of_lt := fun a b h => by
    cases b
    · exact (a.not_lt_zero h).elim
      
    · exact le_of_succ_le_succ h
      
  le_of_pred_lt := fun a b h => by
    cases a
    · exact b.zero_le
      
    · exact h
      

theorem Nat.succ_iterate (a : ℕ) : ∀ n, (succ^[n]) a = a + n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ', add_succ]
    exact congr_argₓ _ n.succ_iterate

theorem Nat.pred_iterate (a : ℕ) : ∀ n, (pred^[n]) a = a - n
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ', sub_succ]
    exact congr_argₓ _ n.pred_iterate

instance : IsSuccArchimedean ℕ :=
  ⟨fun a b h =>
    ⟨b - a, by
      rw [Nat.succ_iterate, add_tsub_cancel_of_le h]⟩⟩

instance : IsPredArchimedean ℕ :=
  ⟨fun a b h =>
    ⟨b - a, by
      rw [Nat.pred_iterate, tsub_tsub_cancel_of_le h]⟩⟩

