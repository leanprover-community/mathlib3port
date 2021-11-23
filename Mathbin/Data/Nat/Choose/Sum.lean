import Mathbin.Data.Nat.Choose.Basic 
import Mathbin.Tactic.Linarith.Default 
import Mathbin.Algebra.BigOperators.Ring 
import Mathbin.Algebra.BigOperators.Intervals 
import Mathbin.Algebra.BigOperators.Order 
import Mathbin.Algebra.BigOperators.NatAntidiagonal

/-!
# Sums of binomial coefficients

This file includes variants of the binomial theorem and other results on sums of binomial
coefficients. Theorems whose proofs depend on such sums may also go in this file for import
reasons.

-/


open Nat

open Finset

open_locale BigOperators

variable{R : Type _}

namespace Commute

variable[Semiringₓ R]{x y : R}(h : Commute x y)(n : ℕ)

include h

-- error in Data.Nat.Choose.Sum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A version of the **binomial theorem** for noncommutative semirings. -/
theorem add_pow : «expr = »(«expr ^ »(«expr + »(x, y), n), «expr∑ in , »((m), range «expr + »(n, 1), «expr * »(«expr * »(«expr ^ »(x, m), «expr ^ »(y, «expr - »(n, m))), choose n m))) :=
begin
  let [ident t] [":", expr exprℕ() → exprℕ() → R] [":=", expr λ
   n m, «expr * »(«expr * »(«expr ^ »(x, m), «expr ^ »(y, «expr - »(n, m))), choose n m)],
  change [expr «expr = »(«expr ^ »(«expr + »(x, y), n), «expr∑ in , »((m), range «expr + »(n, 1), t n m))] [] [],
  have [ident h_first] [":", expr ∀
   n, «expr = »(t n 0, «expr ^ »(y, n))] [":=", expr λ n, by { dsimp [] ["[", expr t, "]"] [] [],
     rw ["[", expr choose_zero_right, ",", expr pow_zero, ",", expr nat.cast_one, ",", expr mul_one, ",", expr one_mul, "]"] [] }],
  have [ident h_last] [":", expr ∀
   n, «expr = »(t n n.succ, 0)] [":=", expr λ n, by { dsimp [] ["[", expr t, "]"] [] [],
     rw ["[", expr choose_succ_self, ",", expr nat.cast_zero, ",", expr mul_zero, "]"] [] }],
  have [ident h_middle] [":", expr ∀
   n
   i : exprℕ(), «expr ∈ »(i, range n.succ) → «expr = »(«expr ∘ »(t n.succ, nat.succ) i, «expr + »(«expr * »(x, t n i), «expr * »(y, t n i.succ)))] [":=", expr begin
     intros [ident n, ident i, ident h_mem],
     have [ident h_le] [":", expr «expr ≤ »(i, n)] [":=", expr nat.le_of_lt_succ (mem_range.mp h_mem)],
     dsimp [] ["[", expr t, "]"] [] [],
     rw ["[", expr choose_succ_succ, ",", expr nat.cast_add, ",", expr mul_add, "]"] [],
     congr' [1] [],
     { rw ["[", expr pow_succ x, ",", expr succ_sub_succ, ",", expr mul_assoc, ",", expr mul_assoc, ",", expr mul_assoc, "]"] [] },
     { rw ["[", "<-", expr mul_assoc y, ",", "<-", expr mul_assoc y, ",", expr (h.symm.pow_right i.succ).eq, "]"] [],
       by_cases [expr h_eq, ":", expr «expr = »(i, n)],
       { rw ["[", expr h_eq, ",", expr choose_succ_self, ",", expr nat.cast_zero, ",", expr mul_zero, ",", expr mul_zero, "]"] [] },
       { rw ["[", expr succ_sub (lt_of_le_of_ne h_le h_eq), "]"] [],
         rw ["[", expr pow_succ y, ",", expr mul_assoc, ",", expr mul_assoc, ",", expr mul_assoc, ",", expr mul_assoc, "]"] [] } }
   end],
  induction [expr n] [] ["with", ident n, ident ih] [],
  { rw ["[", expr pow_zero, ",", expr sum_range_succ, ",", expr range_zero, ",", expr sum_empty, ",", expr zero_add, "]"] [],
    dsimp [] ["[", expr t, "]"] [] [],
    rw ["[", expr pow_zero, ",", expr pow_zero, ",", expr choose_self, ",", expr nat.cast_one, ",", expr mul_one, ",", expr mul_one, "]"] [] },
  { rw ["[", expr sum_range_succ', ",", expr h_first, "]"] [],
    rw ["[", expr sum_congr rfl (h_middle n), ",", expr sum_add_distrib, ",", expr add_assoc, "]"] [],
    rw ["[", expr pow_succ «expr + »(x, y), ",", expr ih, ",", expr add_mul, ",", expr mul_sum, ",", expr mul_sum, "]"] [],
    congr' [1] [],
    rw ["[", expr sum_range_succ', ",", expr sum_range_succ, ",", expr h_first, ",", expr h_last, ",", expr mul_zero, ",", expr add_zero, ",", expr pow_succ, "]"] [] }
end

/-- A version of `commute.add_pow` that avoids ℕ-subtraction by summing over the antidiagonal and
also with the binomial coefficient applied via scalar action of ℕ. -/
theorem add_pow' : (x+y) ^ n = ∑m in nat.antidiagonal n, choose n m.fst • (x ^ m.fst)*y ^ m.snd :=
  by 
    simpRw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun m p => choose n m • (x ^ m)*y ^ p, _root_.nsmul_eq_mul,
      cast_comm, h.add_pow]

end Commute

/-- The **binomial theorem** -/
theorem add_pow [CommSemiringₓ R] (x y : R) (n : ℕ) : (x+y) ^ n = ∑m in range (n+1), ((x ^ m)*y ^ (n - m))*choose n m :=
  (Commute.all x y).add_pow n

namespace Nat

/-- The sum of entries in a row of Pascal's triangle -/
theorem sum_range_choose (n : ℕ) : (∑m in range (n+1), choose n m) = 2 ^ n :=
  by 
    simpa using (add_pow 1 1 n).symm

-- error in Data.Nat.Choose.Sum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sum_range_choose_halfway
(m : nat) : «expr = »(«expr∑ in , »((i), range «expr + »(m, 1), choose «expr + »(«expr * »(2, m), 1) i), «expr ^ »(4, m)) :=
have «expr = »(«expr∑ in , »((i), range «expr + »(m, 1), choose «expr + »(«expr * »(2, m), 1) «expr - »(«expr + »(«expr * »(2, m), 1), i)), «expr∑ in , »((i), range «expr + »(m, 1), choose «expr + »(«expr * »(2, m), 1) i)), from «expr $ »(sum_congr rfl, λ
 i hi, «expr $ »(choose_symm, by linarith [] [] ["[", expr mem_range.1 hi, "]"])),
«expr $ »((nat.mul_right_inj zero_lt_two).1, calc
   «expr = »(«expr * »(2, «expr∑ in , »((i), range «expr + »(m, 1), choose «expr + »(«expr * »(2, m), 1) i)), «expr + »(«expr∑ in , »((i), range «expr + »(m, 1), choose «expr + »(«expr * »(2, m), 1) i), «expr∑ in , »((i), range «expr + »(m, 1), choose «expr + »(«expr * »(2, m), 1) «expr - »(«expr + »(«expr * »(2, m), 1), i)))) : by rw ["[", expr two_mul, ",", expr this, "]"] []
   «expr = »(..., «expr + »(«expr∑ in , »((i), range «expr + »(m, 1), choose «expr + »(«expr * »(2, m), 1) i), «expr∑ in , »((i), Ico «expr + »(m, 1) «expr + »(«expr * »(2, m), 2), choose «expr + »(«expr * »(2, m), 1) i))) : begin
     rw ["[", expr range_eq_Ico, ",", expr sum_Ico_reflect, "]"] [],
     { congr,
       have [ident A] [":", expr «expr ≤ »(«expr + »(m, 1), «expr + »(«expr * »(2, m), 1))] [],
       by linarith [] [] [],
       rw ["[", expr add_comm, ",", expr add_tsub_assoc_of_le A, ",", "<-", expr add_comm, "]"] [],
       congr,
       rw [expr tsub_eq_iff_eq_add_of_le A] [],
       ring [] },
     { linarith [] [] [] }
   end
   «expr = »(..., «expr∑ in , »((i), range «expr + »(«expr * »(2, m), 2), choose «expr + »(«expr * »(2, m), 1) i)) : sum_range_add_sum_Ico _ (by linarith [] [] [])
   «expr = »(..., «expr ^ »(2, «expr + »(«expr * »(2, m), 1))) : sum_range_choose «expr + »(«expr * »(2, m), 1)
   «expr = »(..., «expr * »(2, «expr ^ »(4, m))) : by { rw ["[", expr pow_succ, ",", expr pow_mul, "]"] [],
     refl })

-- error in Data.Nat.Choose.Sum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem choose_middle_le_pow (n : exprℕ()) : «expr ≤ »(choose «expr + »(«expr * »(2, n), 1) n, «expr ^ »(4, n)) :=
begin
  have [ident t] [":", expr «expr ≤ »(choose «expr + »(«expr * »(2, n), 1) n, «expr∑ in , »((i), range «expr + »(n, 1), choose «expr + »(«expr * »(2, n), 1) i))] [":=", expr single_le_sum (λ
    x _, by linarith [] [] []) (self_mem_range_succ n)],
  simpa [] [] [] ["[", expr sum_range_choose_halfway n, "]"] [] ["using", expr t]
end

theorem four_pow_le_two_mul_add_one_mul_central_binom (n : ℕ) : 4 ^ n ≤ ((2*n)+1)*choose (2*n) n :=
  calc 4 ^ n = (1+1) ^ 2*n :=
    by 
      normNum [pow_mulₓ]
    _ = ∑m in range ((2*n)+1), choose (2*n) m :=
    by 
      simp [add_pow]
    _ ≤ ∑m in range ((2*n)+1), choose (2*n) ((2*n) / 2) := sum_le_sum fun i hi => choose_le_middle i (2*n)
    _ = ((2*n)+1)*choose (2*n) n :=
    by 
      simp 
    

end Nat

-- error in Data.Nat.Choose.Sum: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem int.alternating_sum_range_choose
{n : exprℕ()} : «expr = »(«expr∑ in , »((m), range «expr + »(n, 1), («expr * »(«expr ^ »(«expr- »(1), m), «expr↑ »(choose n m)) : exprℤ())), if «expr = »(n, 0) then 1 else 0) :=
begin
  cases [expr n] [],
  { simp [] [] [] [] [] [] },
  have [ident h] [] [":=", expr add_pow («expr- »(1) : exprℤ()) 1 n.succ],
  simp [] [] ["only"] ["[", expr one_pow, ",", expr mul_one, ",", expr add_left_neg, ",", expr int.nat_cast_eq_coe_nat, "]"] [] ["at", ident h],
  rw ["[", "<-", expr h, ",", expr zero_pow (nat.succ_pos n), ",", expr if_neg (nat.succ_ne_zero n), "]"] []
end

theorem Int.alternating_sum_range_choose_of_ne {n : ℕ} (h0 : n ≠ 0) :
  (∑m in range (n+1), ((-1 ^ m)*«expr↑ » (choose n m) : ℤ)) = 0 :=
  by 
    rw [Int.alternating_sum_range_choose, if_neg h0]

namespace Finset

theorem sum_powerset_apply_card {α β : Type _} [AddCommMonoidₓ α] (f : ℕ → α) {x : Finset β} :
  (∑m in x.powerset, f m.card) = ∑m in range (x.card+1), x.card.choose m • f m :=
  by 
    trans ∑m in range (x.card+1), ∑j in x.powerset.filter fun z => z.card = m, f j.card
    ·
      refine' (sum_fiberwise_of_maps_to _ _).symm 
      intro y hy 
      rw [mem_range, Nat.lt_succ_iff]
      rw [mem_powerset] at hy 
      exact card_le_of_subset hy
    ·
      refine' sum_congr rfl fun y hy => _ 
      rw [←card_powerset_len, ←sum_const]
      refine' sum_congr powerset_len_eq_filter.symm fun z hz => _ 
      rw [(mem_powerset_len.1 hz).2]

theorem sum_powerset_neg_one_pow_card {α : Type _} [DecidableEq α] {x : Finset α} :
  (∑m in x.powerset, (-1 : ℤ) ^ m.card) = if x = ∅ then 1 else 0 :=
  by 
    rw [sum_powerset_apply_card]
    simp only [nsmul_eq_mul', ←card_eq_zero]
    convert Int.alternating_sum_range_choose 
    ext 
    simp 

theorem sum_powerset_neg_one_pow_card_of_nonempty {α : Type _} {x : Finset α} (h0 : x.nonempty) :
  (∑m in x.powerset, (-1 : ℤ) ^ m.card) = 0 :=
  by 
    classical 
    rw [sum_powerset_neg_one_pow_card, if_neg]
    rw [←Ne.def, ←nonempty_iff_ne_empty]
    apply h0

end Finset

