/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Data.W.Basic
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of W-types

This file proves some theorems about the cardinality of W-types. The main result is
`cardinal_mk_le_max_omega_of_fintype` which says that if for any `a : α`,
`β a` is finite, then the cardinality of `W_type β` is at most the maximum of the
cardinality of `α` and `cardinal.omega`.
This can be used to prove theorems about the cardinality of algebraic constructions such as
polynomials. There is a surjection from a `W_type` to `mv_polynomial` for example, and
this surjection can be used to put an upper bound on the cardinality of `mv_polynomial`.

## Tags

W, W type, cardinal, first order
-/


universe u

variable {α : Type u} {β : α → Type u}

noncomputable section

namespace WType

open Cardinal

open Cardinal

theorem cardinal_mk_eq_sum : # (WType β) = Sum fun a : α => # (WType β) ^ # (β a) := by
  simp only [Cardinal.power_def, ← Cardinal.mk_sigma]
  exact mk_congr (equiv_sigma β)

/-- `#(W_type β)` is the least cardinal `κ` such that `sum (λ a : α, κ ^ #(β a)) ≤ κ` -/
theorem cardinal_mk_le_of_le {κ : Cardinal.{u}} (hκ : (Sum fun a : α => κ ^ # (β a)) ≤ κ) : # (WType β) ≤ κ := by
  induction' κ using Cardinal.induction_on with γ
  simp only [Cardinal.power_def, ← Cardinal.mk_sigma, Cardinal.le_def] at hκ
  cases hκ
  exact Cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)

/-- If, for any `a : α`, `β a` is finite, then the cardinality of `W_type β`
  is at most the maximum of the cardinality of `α` and `ω`  -/
theorem cardinal_mk_le_max_omega_of_fintype [∀ a, Fintype (β a)] : # (WType β) ≤ max (# α) ω :=
  ((is_empty_or_nonempty α).elim
      (by
        intro h
        rw [Cardinal.mk_eq_zero (WType β)]
        exact zero_le _))
    fun hn =>
    let m := max (# α) ω
    cardinal_mk_le_of_le <|
      calc
        (Cardinal.sum fun a : α => m ^ # (β a)) ≤ # α * Cardinal.sup.{u, u} fun a : α => m ^ Cardinal.mk (β a) :=
          Cardinal.sum_le_sup _
        _ ≤ m * Cardinal.sup.{u, u} fun a : α => m ^ # (β a) := mul_le_mul' (le_max_leftₓ _ _) le_rfl
        _ = m :=
          mul_eq_left.{u} (le_max_rightₓ _ _)
            (Cardinal.sup_le fun i => by
              cases' lt_omega.1 (lt_omega_of_fintype (β i)) with n hn
              rw [hn]
              exact power_nat_le (le_max_rightₓ _ _))
            (pos_iff_ne_zero.1
              (succ_le.1
                (by
                  rw [succ_zero]
                  obtain ⟨a⟩ : Nonempty α
                  exact hn
                  refine' le_transₓ _ (le_sup _ a)
                  rw [← @power_zero m]
                  exact
                    power_le_power_left (pos_iff_ne_zero.1 (lt_of_lt_of_leₓ omega_pos (le_max_rightₓ _ _)))
                      (zero_le _))))
        

end WType

