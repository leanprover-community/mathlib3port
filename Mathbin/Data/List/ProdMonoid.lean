import Mathbin.Data.List.BigOperators

/-!
# Products / sums of lists of terms of a monoid

This file provides basic results about `list.prod` (definition in `data.list.defs`) in a monoid.
It is in a separate file so that `data.list.big_operators` does not depend on
`algebra.group_power.basic`.
-/


open Nat

namespace List

universe u v

variable {α : Type u}

@[simp, toAdditive]
theorem prod_repeat [Monoidₓ α] (a : α) (n : ℕ) : (repeat a n).Prod = a ^ n :=
  by 
    induction' n with n ih
    ·
      rw [pow_zeroₓ]
      rfl
    ·
      rw [List.repeat_succ, List.prod_cons, ih, pow_succₓ]

-- error in Data.List.ProdMonoid: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_le_of_forall_le
[ordered_comm_monoid α]
(l : list α)
(n : α)
(h : ∀ x «expr ∈ » l, «expr ≤ »(x, n)) : «expr ≤ »(l.prod, «expr ^ »(n, l.length)) :=
begin
  induction [expr l] [] ["with", ident y, ident l, ident IH] [],
  { simp [] [] [] [] [] [] },
  { specialize [expr IH (λ x hx, h x (mem_cons_of_mem _ hx))],
    have [ident hy] [":", expr «expr ≤ »(y, n)] [":=", expr h y (mem_cons_self _ _)],
    simpa [] [] [] ["[", expr pow_succ, "]"] [] ["using", expr mul_le_mul' hy IH] }
end

end List

