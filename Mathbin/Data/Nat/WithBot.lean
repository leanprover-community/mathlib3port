/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.nat.with_bot
! leanprover-community/mathlib commit 12665d3612d46b1838ec1273d291c21a61fc1707
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Order.Basic
import Mathbin.Algebra.Order.Monoid.WithTop

/-!
# `with_bot ℕ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Lemmas about the type of natural numbers with a bottom element adjoined.
-/


namespace Nat

namespace WithBot

#print Nat.WithBot.add_eq_zero_iff /-
theorem add_eq_zero_iff {n m : WithBot ℕ} : n + m = 0 ↔ n = 0 ∧ m = 0 :=
  by
  rcases n, m with ⟨_ | _, _ | _⟩
  any_goals tauto
  repeat' erw [WithBot.coe_eq_coe]
  exact add_eq_zero_iff
#align nat.with_bot.add_eq_zero_iff Nat.WithBot.add_eq_zero_iff
-/

#print Nat.WithBot.add_eq_one_iff /-
theorem add_eq_one_iff {n m : WithBot ℕ} : n + m = 1 ↔ n = 0 ∧ m = 1 ∨ n = 1 ∧ m = 0 :=
  by
  rcases n, m with ⟨_ | _, _ | _⟩
  any_goals tauto
  repeat' erw [WithBot.coe_eq_coe]
  exact add_eq_one_iff
#align nat.with_bot.add_eq_one_iff Nat.WithBot.add_eq_one_iff
-/

#print Nat.WithBot.add_eq_two_iff /-
theorem add_eq_two_iff {n m : WithBot ℕ} :
    n + m = 2 ↔ n = 0 ∧ m = 2 ∨ n = 1 ∧ m = 1 ∨ n = 2 ∧ m = 0 :=
  by
  rcases n, m with ⟨_ | _, _ | _⟩
  any_goals tauto
  repeat' erw [WithBot.coe_eq_coe]
  exact add_eq_two_iff
#align nat.with_bot.add_eq_two_iff Nat.WithBot.add_eq_two_iff
-/

#print Nat.WithBot.add_eq_three_iff /-
theorem add_eq_three_iff {n m : WithBot ℕ} :
    n + m = 3 ↔ n = 0 ∧ m = 3 ∨ n = 1 ∧ m = 2 ∨ n = 2 ∧ m = 1 ∨ n = 3 ∧ m = 0 :=
  by
  rcases n, m with ⟨_ | _, _ | _⟩
  any_goals tauto
  repeat' erw [WithBot.coe_eq_coe]
  exact add_eq_three_iff
#align nat.with_bot.add_eq_three_iff Nat.WithBot.add_eq_three_iff
-/

/- warning: nat.with_bot.coe_nonneg -> Nat.WithBot.coe_nonneg is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, LE.le.{0} (WithBot.{0} Nat) (Preorder.toHasLe.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (OfNat.ofNat.{0} (WithBot.{0} Nat) 0 (OfNat.mk.{0} (WithBot.{0} Nat) 0 (Zero.zero.{0} (WithBot.{0} Nat) (WithBot.hasZero.{0} Nat Nat.hasZero)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) n)
but is expected to have type
  forall {n : Nat}, LE.le.{0} (WithBot.{0} Nat) (Preorder.toLE.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (OfNat.ofNat.{0} (WithBot.{0} Nat) 0 (Zero.toOfNat0.{0} (WithBot.{0} Nat) (WithBot.zero.{0} Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) (Nat.cast.{0} (WithBot.{0} Nat) (AddMonoidWithOne.toNatCast.{0} (WithBot.{0} Nat) (WithBot.addMonoidWithOne.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))))) n)
Case conversion may be inaccurate. Consider using '#align nat.with_bot.coe_nonneg Nat.WithBot.coe_nonnegₓ'. -/
theorem coe_nonneg {n : ℕ} : 0 ≤ (n : WithBot ℕ) :=
  by
  rw [← WithBot.coe_zero, WithBot.coe_le_coe]
  exact Nat.zero_le _
#align nat.with_bot.coe_nonneg Nat.WithBot.coe_nonneg

/- warning: nat.with_bot.lt_zero_iff -> Nat.WithBot.lt_zero_iff is a dubious translation:
lean 3 declaration is
  forall (n : WithBot.{0} Nat), Iff (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) n (OfNat.ofNat.{0} (WithBot.{0} Nat) 0 (OfNat.mk.{0} (WithBot.{0} Nat) 0 (Zero.zero.{0} (WithBot.{0} Nat) (WithBot.hasZero.{0} Nat Nat.hasZero))))) (Eq.{1} (WithBot.{0} Nat) n (Bot.bot.{0} (WithBot.{0} Nat) (WithBot.hasBot.{0} Nat)))
but is expected to have type
  forall (n : WithBot.{0} Nat), Iff (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) n (OfNat.ofNat.{0} (WithBot.{0} Nat) 0 (Zero.toOfNat0.{0} (WithBot.{0} Nat) (WithBot.zero.{0} Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))))) (Eq.{1} (WithBot.{0} Nat) n (Bot.bot.{0} (WithBot.{0} Nat) (WithBot.bot.{0} Nat)))
Case conversion may be inaccurate. Consider using '#align nat.with_bot.lt_zero_iff Nat.WithBot.lt_zero_iffₓ'. -/
@[simp]
theorem lt_zero_iff (n : WithBot ℕ) : n < 0 ↔ n = ⊥ :=
  Option.casesOn n (by decide) fun n =>
    iff_of_false (by simp [WithBot.some_eq_coe, coe_nonneg]) fun h => Option.noConfusion h
#align nat.with_bot.lt_zero_iff Nat.WithBot.lt_zero_iff

/- warning: nat.with_bot.one_le_iff_zero_lt -> Nat.WithBot.one_le_iff_zero_lt is a dubious translation:
lean 3 declaration is
  forall {x : WithBot.{0} Nat}, Iff (LE.le.{0} (WithBot.{0} Nat) (Preorder.toHasLe.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (OfNat.ofNat.{0} (WithBot.{0} Nat) 1 (OfNat.mk.{0} (WithBot.{0} Nat) 1 (One.one.{0} (WithBot.{0} Nat) (WithBot.hasOne.{0} Nat Nat.hasOne)))) x) (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (OfNat.ofNat.{0} (WithBot.{0} Nat) 0 (OfNat.mk.{0} (WithBot.{0} Nat) 0 (Zero.zero.{0} (WithBot.{0} Nat) (WithBot.hasZero.{0} Nat Nat.hasZero)))) x)
but is expected to have type
  forall {x : WithBot.{0} Nat}, Iff (LE.le.{0} (WithBot.{0} Nat) (Preorder.toLE.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (OfNat.ofNat.{0} (WithBot.{0} Nat) 1 (One.toOfNat1.{0} (WithBot.{0} Nat) (WithBot.one.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)))) x) (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (OfNat.ofNat.{0} (WithBot.{0} Nat) 0 (Zero.toOfNat0.{0} (WithBot.{0} Nat) (WithBot.zero.{0} Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))) x)
Case conversion may be inaccurate. Consider using '#align nat.with_bot.one_le_iff_zero_lt Nat.WithBot.one_le_iff_zero_ltₓ'. -/
theorem one_le_iff_zero_lt {x : WithBot ℕ} : 1 ≤ x ↔ 0 < x :=
  by
  refine' ⟨fun h => lt_of_lt_of_le (with_bot.coe_lt_coe.mpr zero_lt_one) h, fun h => _⟩
  induction x using WithBot.recBotCoe
  · exact (not_lt_bot h).elim
  · exact with_bot.coe_le_coe.mpr (nat.succ_le_iff.mpr (with_bot.coe_lt_coe.mp h))
#align nat.with_bot.one_le_iff_zero_lt Nat.WithBot.one_le_iff_zero_lt

/- warning: nat.with_bot.lt_one_iff_le_zero -> Nat.WithBot.lt_one_iff_le_zero is a dubious translation:
lean 3 declaration is
  forall {x : WithBot.{0} Nat}, Iff (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) x (OfNat.ofNat.{0} (WithBot.{0} Nat) 1 (OfNat.mk.{0} (WithBot.{0} Nat) 1 (One.one.{0} (WithBot.{0} Nat) (WithBot.hasOne.{0} Nat Nat.hasOne))))) (LE.le.{0} (WithBot.{0} Nat) (Preorder.toHasLe.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) x (OfNat.ofNat.{0} (WithBot.{0} Nat) 0 (OfNat.mk.{0} (WithBot.{0} Nat) 0 (Zero.zero.{0} (WithBot.{0} Nat) (WithBot.hasZero.{0} Nat Nat.hasZero)))))
but is expected to have type
  forall {x : WithBot.{0} Nat}, Iff (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) x (OfNat.ofNat.{0} (WithBot.{0} Nat) 1 (One.toOfNat1.{0} (WithBot.{0} Nat) (WithBot.one.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring))))) (LE.le.{0} (WithBot.{0} Nat) (Preorder.toLE.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) x (OfNat.ofNat.{0} (WithBot.{0} Nat) 0 (Zero.toOfNat0.{0} (WithBot.{0} Nat) (WithBot.zero.{0} Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)))))
Case conversion may be inaccurate. Consider using '#align nat.with_bot.lt_one_iff_le_zero Nat.WithBot.lt_one_iff_le_zeroₓ'. -/
theorem lt_one_iff_le_zero {x : WithBot ℕ} : x < 1 ↔ x ≤ 0 :=
  not_iff_not.mp (by simpa using one_le_iff_zero_lt)
#align nat.with_bot.lt_one_iff_le_zero Nat.WithBot.lt_one_iff_le_zero

/- warning: nat.with_bot.add_one_le_of_lt -> Nat.WithBot.add_one_le_of_lt is a dubious translation:
lean 3 declaration is
  forall {n : WithBot.{0} Nat} {m : WithBot.{0} Nat}, (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) n m) -> (LE.le.{0} (WithBot.{0} Nat) (Preorder.toHasLe.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (HAdd.hAdd.{0, 0, 0} (WithBot.{0} Nat) (WithBot.{0} Nat) (WithBot.{0} Nat) (instHAdd.{0} (WithBot.{0} Nat) (WithBot.hasAdd.{0} Nat Nat.hasAdd)) n (OfNat.ofNat.{0} (WithBot.{0} Nat) 1 (OfNat.mk.{0} (WithBot.{0} Nat) 1 (One.one.{0} (WithBot.{0} Nat) (WithBot.hasOne.{0} Nat Nat.hasOne))))) m)
but is expected to have type
  forall {n : WithBot.{0} Nat} {m : WithBot.{0} Nat}, (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) n m) -> (LE.le.{0} (WithBot.{0} Nat) (Preorder.toLE.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (HAdd.hAdd.{0, 0, 0} (WithBot.{0} Nat) (WithBot.{0} Nat) (WithBot.{0} Nat) (instHAdd.{0} (WithBot.{0} Nat) (WithBot.add.{0} Nat instAddNat)) n (OfNat.ofNat.{0} (WithBot.{0} Nat) 1 (One.toOfNat1.{0} (WithBot.{0} Nat) (WithBot.one.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring))))) m)
Case conversion may be inaccurate. Consider using '#align nat.with_bot.add_one_le_of_lt Nat.WithBot.add_one_le_of_ltₓ'. -/
theorem add_one_le_of_lt {n m : WithBot ℕ} (h : n < m) : n + 1 ≤ m :=
  by
  cases n; · exact bot_le
  cases m; exacts[(not_lt_bot h).elim, WithBot.some_le_some.2 (WithBot.some_lt_some.1 h)]
#align nat.with_bot.add_one_le_of_lt Nat.WithBot.add_one_le_of_lt

end WithBot

end Nat

