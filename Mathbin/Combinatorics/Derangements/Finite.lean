import Mathbin.Combinatorics.Derangements.Basic 
import Mathbin.Data.Fintype.Card 
import Mathbin.Tactic.DeltaInstance 
import Mathbin.Tactic.Ring

/-!
# Derangements on fintypes

This file contains lemmas that describe the cardinality of `derangements α` when `α` is a fintype.

# Main definitions

* `card_derangements_invariant`: A lemma stating that the number of derangements on a type `α`
    depends only on the cardinality of `α`.
* `num_derangements n`: The number of derangements on an n-element set, defined in a computation-
    friendly way.
* `card_derangements_eq_num_derangements`: Proof that `num_derangements` really does compute the
    number of derangements.
* `num_derangements_sum`: A lemma giving an expression for `num_derangements n` in terms of
    factorials.
-/


open Derangements Equiv Fintype

open_locale BigOperators

variable{α : Type _}[DecidableEq α][Fintype α]

instance  : DecidablePred (Derangements α) :=
  fun _ => Fintype.decidableForallFintype

instance  : Fintype (Derangements α) :=
  by 
    deltaInstance derangements

theorem card_derangements_invariant {α β : Type _} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  (h : card α = card β) : card (Derangements α) = card (Derangements β) :=
  Fintype.card_congr (Equiv.derangementsCongr$ equiv_of_card_eq h)

-- error in Combinatorics.Derangements.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_derangements_fin_add_two
(n : exprℕ()) : «expr = »(card (derangements (fin «expr + »(n, 2))), «expr + »(«expr * »(«expr + »(n, 1), card (derangements (fin n))), «expr * »(«expr + »(n, 1), card (derangements (fin «expr + »(n, 1)))))) :=
begin
  have [ident h1] [":", expr ∀
   a : fin «expr + »(n, 1), «expr = »(card («expr ᶜ»({a}) : set (fin «expr + »(n, 1))), card (fin n))] [],
  { intro [ident a],
    simp [] [] ["only"] ["[", expr fintype.card_fin, ",", expr finset.card_fin, ",", expr fintype.card_of_finset, ",", expr finset.filter_ne' _ a, ",", expr set.mem_compl_singleton_iff, ",", expr finset.card_erase_of_mem (finset.mem_univ a), ",", expr nat.pred_succ, "]"] [] [] },
  have [ident h2] [":", expr «expr = »(card (fin «expr + »(n, 2)), card (option (fin «expr + »(n, 1))))] [],
  { simp [] [] ["only"] ["[", expr card_fin, ",", expr card_option, "]"] [] [] },
  simp [] [] ["only"] ["[", expr card_derangements_invariant h2, ",", expr card_congr (@derangements_recursion_equiv (fin «expr + »(n, 1)) _), ",", expr card_sigma, ",", expr card_sum, ",", expr card_derangements_invariant (h1 _), ",", expr finset.sum_const, ",", expr nsmul_eq_mul, ",", expr finset.card_fin, ",", expr mul_add, ",", expr nat.cast_id, "]"] [] []
end

/-- The number of derangements of an `n`-element set. -/
def numDerangements : ℕ → ℕ
| 0 => 1
| 1 => 0
| n+2 => (n+1)*numDerangements n+numDerangements (n+1)

@[simp]
theorem num_derangements_zero : numDerangements 0 = 1 :=
  rfl

@[simp]
theorem num_derangements_one : numDerangements 1 = 0 :=
  rfl

theorem num_derangements_add_two (n : ℕ) : numDerangements (n+2) = (n+1)*numDerangements n+numDerangements (n+1) :=
  rfl

theorem num_derangements_succ (n : ℕ) : (numDerangements (n+1) : ℤ) = ((n+1)*(numDerangements n : ℤ)) - -1 ^ n :=
  by 
    induction' n with n hn
    ·
      rfl
    ·
      simp only [num_derangements_add_two, hn, pow_succₓ, Int.coe_nat_mul, Int.coe_nat_add, Int.coe_nat_succ]
      ring

theorem card_derangements_fin_eq_num_derangements {n : ℕ} : card (Derangements (Finₓ n)) = numDerangements n :=
  by 
    induction' n using Nat.strong_induction_onₓ with n hyp 
    obtain _ | _ | n := n
    ·
      rfl
    ·
      rfl 
    rw [num_derangements_add_two, card_derangements_fin_add_two, mul_addₓ, hyp _ (Nat.lt_add_of_pos_rightₓ zero_lt_two),
      hyp _ (lt_add_one _)]

theorem card_derangements_eq_num_derangements (α : Type _) [Fintype α] [DecidableEq α] :
  card (Derangements α) = numDerangements (card α) :=
  by 
    rw [←card_derangements_invariant (card_fin _)]
    exact card_derangements_fin_eq_num_derangements

-- error in Combinatorics.Derangements.Finite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem num_derangements_sum
(n : exprℕ()) : «expr = »((num_derangements n : exprℤ()), «expr∑ in , »((k), finset.range «expr + »(n, 1), «expr * »(«expr ^ »((«expr- »(1) : exprℤ()), k), nat.asc_factorial k «expr - »(n, k)))) :=
begin
  induction [expr n] [] ["with", ident n, ident hn] [],
  { refl },
  rw ["[", expr finset.sum_range_succ, ",", expr num_derangements_succ, ",", expr hn, ",", expr finset.mul_sum, ",", expr tsub_self, ",", expr nat.asc_factorial_zero, ",", expr int.coe_nat_one, ",", expr mul_one, ",", expr pow_succ, ",", expr neg_one_mul, ",", expr sub_eq_add_neg, ",", expr add_left_inj, ",", expr finset.sum_congr rfl, "]"] [],
  intros [ident x, ident hx],
  have [ident h_le] [":", expr «expr ≤ »(x, n)] [":=", expr finset.mem_range_succ_iff.mp hx],
  rw ["[", expr nat.succ_sub h_le, ",", expr nat.asc_factorial_succ, ",", expr add_tsub_cancel_of_le h_le, ",", expr int.coe_nat_mul, ",", expr int.coe_nat_succ, ",", expr mul_left_comm, "]"] []
end

