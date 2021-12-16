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

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
@[toAdditive]
theorem prod_le_of_forall_le [OrderedCommMonoid α] (l : List α) (n : α) (h : ∀ x _ : x ∈ l, x ≤ n) :
  l.prod ≤ n ^ l.length :=
  by 
    induction' l with y l IH
    ·
      simp 
    ·
      specialize IH fun x hx => h x (mem_cons_of_mem _ hx)
      have hy : y ≤ n := h y (mem_cons_self _ _)
      simpa [pow_succₓ] using mul_le_mul' hy IH

end List

