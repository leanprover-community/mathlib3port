/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu

! This file was ported from Lean 3 source module data.polynomial.cardinal
! leanprover-community/mathlib commit 62c0a4ef1441edb463095ea02a06e87f3dfe135c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Basic
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of Polynomial Ring

The reuslt in this file is that the cardinality of `R[X]` is at most the maximum
of `#R` and `ℵ₀`.
-/


universe u

open Cardinal Polynomial

open Cardinal

namespace Polynomial

/- warning: polynomial.cardinal_mk_eq_max -> Polynomial.cardinal_mk_eq_max is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Polynomial.{u1} R _inst_1)) (LinearOrder.max.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1})) (Cardinal.mk.{u1} R) Cardinal.aleph0.{u1})
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Polynomial.{u1} R _inst_1)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} R) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align polynomial.cardinal_mk_eq_max Polynomial.cardinal_mk_eq_maxₓ'. -/
@[simp]
theorem cardinal_mk_eq_max {R : Type u} [Semiring R] [Nontrivial R] : (#R[X]) = max (#R) ℵ₀ :=
  (toFinsuppIso R).toEquiv.cardinal_eq.trans <|
    by
    rw [AddMonoidAlgebra, mk_finsupp_lift_of_infinite, lift_uzero, max_comm]
    rfl
#align polynomial.cardinal_mk_eq_max Polynomial.cardinal_mk_eq_max

/- warning: polynomial.cardinal_mk_le_max -> Polynomial.cardinal_mk_le_max is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (Polynomial.{u1} R _inst_1)) (LinearOrder.max.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toLinearOrder.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1})) (Cardinal.mk.{u1} R) Cardinal.aleph0.{u1})
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R], LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Polynomial.{u1} R _inst_1)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} R) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align polynomial.cardinal_mk_le_max Polynomial.cardinal_mk_le_maxₓ'. -/
theorem cardinal_mk_le_max {R : Type u} [Semiring R] : (#R[X]) ≤ max (#R) ℵ₀ :=
  by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph_0)
  · exact cardinal_mk_eq_max.le
#align polynomial.cardinal_mk_le_max Polynomial.cardinal_mk_le_max

end Polynomial

