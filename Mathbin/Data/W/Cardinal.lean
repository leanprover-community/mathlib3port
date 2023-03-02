/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.W.cardinal
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.W.Basic
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of W-types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves some theorems about the cardinality of W-types. The main result is
`cardinal_mk_le_max_aleph_0_of_fintype` which says that if for any `a : α`,
`β a` is finite, then the cardinality of `W_type β` is at most the maximum of the
cardinality of `α` and `ℵ₀`.
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

#print WType.cardinal_mk_eq_sum /-
theorem cardinal_mk_eq_sum : (#WType β) = Sum fun a : α => (#WType β) ^ (#β a) :=
  by
  simp only [Cardinal.power_def, ← Cardinal.mk_sigma]
  exact mk_congr (equiv_sigma β)
#align W_type.cardinal_mk_eq_sum WType.cardinal_mk_eq_sum
-/

#print WType.cardinal_mk_le_of_le /-
/-- `#(W_type β)` is the least cardinal `κ` such that `sum (λ a : α, κ ^ #(β a)) ≤ κ` -/
theorem cardinal_mk_le_of_le {κ : Cardinal.{u}} (hκ : (Sum fun a : α => κ ^ (#β a)) ≤ κ) :
    (#WType β) ≤ κ := by
  induction' κ using Cardinal.inductionOn with γ
  simp only [Cardinal.power_def, ← Cardinal.mk_sigma, Cardinal.le_def] at hκ
  cases hκ
  exact Cardinal.mk_le_of_injective (elim_injective _ hκ.1 hκ.2)
#align W_type.cardinal_mk_le_of_le WType.cardinal_mk_le_of_le
-/

/- warning: W_type.cardinal_mk_le_max_aleph_0_of_finite -> WType.cardinal_mk_le_max_aleph0_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u1}} [_inst_1 : forall (a : α), Finite.{succ u1} (β a)], LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (WType.{u1, u1} α β)) (LinearOrder.max.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1})) (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1})
but is expected to have type
  forall {α : Type.{u1}} {β : α -> Type.{u1}} [_inst_1 : forall (a : α), Finite.{succ u1} (β a)], LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (WType.{u1, u1} α β)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align W_type.cardinal_mk_le_max_aleph_0_of_finite WType.cardinal_mk_le_max_aleph0_of_finiteₓ'. -/
/-- If, for any `a : α`, `β a` is finite, then the cardinality of `W_type β`
  is at most the maximum of the cardinality of `α` and `ℵ₀`  -/
theorem cardinal_mk_le_max_aleph0_of_finite [∀ a, Finite (β a)] : (#WType β) ≤ max (#α) ℵ₀ :=
  (isEmpty_or_nonempty α).elim
    (by
      intro h
      rw [Cardinal.mk_eq_zero (WType β)]
      exact zero_le _)
    fun hn =>
    let m := max (#α) ℵ₀
    cardinal_mk_le_of_le <|
      calc
        (Cardinal.sum fun a => m ^ (#β a)) ≤ (#α) * ⨆ a, m ^ (#β a) := Cardinal.sum_le_supᵢ _
        _ ≤ m * ⨆ a, m ^ (#β a) := (mul_le_mul' (le_max_left _ _) le_rfl)
        _ = m :=
          mul_eq_left.{u} (le_max_right _ _)
              (csupᵢ_le' fun i => pow_le (le_max_right _ _) (lt_aleph0_of_finite _)) <|
            pos_iff_ne_zero.1 <|
              Order.succ_le_iff.1
                (by
                  rw [succ_zero]
                  obtain ⟨a⟩ : Nonempty α; exact hn
                  refine' le_trans _ (le_csupᵢ (bddAbove_range.{u, u} _) a)
                  rw [← power_zero]
                  exact
                    power_le_power_left
                      (pos_iff_ne_zero.1 (aleph_0_pos.trans_le (le_max_right _ _))) (zero_le _))
        
#align W_type.cardinal_mk_le_max_aleph_0_of_finite WType.cardinal_mk_le_max_aleph0_of_finite

end WType

