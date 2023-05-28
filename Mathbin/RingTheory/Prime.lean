/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module ring_theory.prime
! leanprover-community/mathlib commit 327c3c0d9232d80e250dc8f65e7835b82b266ea5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Associated
import Mathbin.Algebra.BigOperators.Basic

/-!
# Prime elements in rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file contains lemmas about prime elements of commutative rings.
-/


section CancelCommMonoidWithZero

variable {R : Type _} [CancelCommMonoidWithZero R]

open Finset

open BigOperators

/- warning: mul_eq_mul_prime_prod -> mul_eq_mul_prime_prod is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_eq_mul_prime_prod mul_eq_mul_prime_prodₓ'. -/
/-- If `x * y = a * ∏ i in s, p i` where `p i` is always prime, then
  `x` and `y` can both be written as a divisor of `a` multiplied by
  a product over a subset of `s`  -/
theorem mul_eq_mul_prime_prod {α : Type _} [DecidableEq α] {x y a : R} {s : Finset α} {p : α → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hx : x * y = a * ∏ i in s, p i) :
    ∃ (t u : Finset α)(b c : R),
      t ∪ u = s ∧ Disjoint t u ∧ a = b * c ∧ (x = b * ∏ i in t, p i) ∧ y = c * ∏ i in u, p i :=
  by
  induction' s using Finset.induction with i s his ih generalizing x y a
  · exact ⟨∅, ∅, x, y, by simp [hx]⟩
  · rw [prod_insert his, ← mul_assoc] at hx
    have hpi : Prime (p i) := hp i (mem_insert_self _ _)
    rcases ih (fun i hi => hp i (mem_insert_of_mem hi)) hx with
      ⟨t, u, b, c, htus, htu, hbc, rfl, rfl⟩
    have hit : i ∉ t := fun hit => his (htus ▸ mem_union_left _ hit)
    have hiu : i ∉ u := fun hiu => his (htus ▸ mem_union_right _ hiu)
    obtain ⟨d, rfl⟩ | ⟨d, rfl⟩ : p i ∣ b ∨ p i ∣ c
    exact hpi.dvd_or_dvd ⟨a, by rw [← hbc, mul_comm]⟩
    · rw [mul_assoc, mul_comm a, mul_right_inj' hpi.ne_zero] at hbc
      exact
        ⟨insert i t, u, d, c, by rw [insert_union, htus], disjoint_insert_left.2 ⟨hiu, htu⟩, by
          simp [hbc, prod_insert hit, mul_assoc, mul_comm, mul_left_comm]⟩
    · rw [← mul_assoc, mul_right_comm b, mul_left_inj' hpi.ne_zero] at hbc
      exact
        ⟨t, insert i u, b, d, by rw [union_insert, htus], disjoint_insert_right.2 ⟨hit, htu⟩, by
          simp [← hbc, prod_insert hiu, mul_assoc, mul_comm, mul_left_comm]⟩
#align mul_eq_mul_prime_prod mul_eq_mul_prime_prod

/- warning: mul_eq_mul_prime_pow -> mul_eq_mul_prime_pow is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mul_eq_mul_prime_pow mul_eq_mul_prime_powₓ'. -/
/-- If ` x * y = a * p ^ n` where `p` is prime, then `x` and `y` can both be written
  as the product of a power of `p` and a divisor of `a`. -/
theorem mul_eq_mul_prime_pow {x y a p : R} {n : ℕ} (hp : Prime p) (hx : x * y = a * p ^ n) :
    ∃ (i j : ℕ)(b c : R), i + j = n ∧ a = b * c ∧ x = b * p ^ i ∧ y = c * p ^ j :=
  by
  rcases mul_eq_mul_prime_prod (fun _ _ => hp)
      (show x * y = a * (range n).Prod fun _ => p by simpa) with
    ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩
  exact ⟨t.card, u.card, b, c, by rw [← card_disjoint_union htu, htus, card_range], by simp⟩
#align mul_eq_mul_prime_pow mul_eq_mul_prime_pow

end CancelCommMonoidWithZero

section CommRing

variable {α : Type _} [CommRing α]

/- warning: prime.neg -> Prime.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] {p : α}, (Prime.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1)) p) -> (Prime.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1)) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (CommRing.toRing.{u1} α _inst_1)))))) p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] {p : α}, (Prime.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1)) p) -> (Prime.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1)) (Neg.neg.{u1} α (Ring.toNeg.{u1} α (CommRing.toRing.{u1} α _inst_1)) p))
Case conversion may be inaccurate. Consider using '#align prime.neg Prime.negₓ'. -/
theorem Prime.neg {p : α} (hp : Prime p) : Prime (-p) :=
  by
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨neg_ne_zero.mpr h1, by rwa [IsUnit.neg_iff], by simpa [neg_dvd] using h3⟩
#align prime.neg Prime.neg

/- warning: prime.abs -> Prime.abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] [_inst_2 : LinearOrder.{u1} α] {p : α}, (Prime.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1)) p) -> (Prime.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1)) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α (CommRing.toRing.{u1} α _inst_1)))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α _inst_2)))) p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommRing.{u1} α] [_inst_2 : LinearOrder.{u1} α] {p : α}, (Prime.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1)) p) -> (Prime.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α _inst_1)) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (Ring.toNeg.{u1} α (CommRing.toRing.{u1} α _inst_1)) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2))))) p))
Case conversion may be inaccurate. Consider using '#align prime.abs Prime.absₓ'. -/
theorem Prime.abs [LinearOrder α] {p : α} (hp : Prime p) : Prime (abs p) :=
  by
  obtain h | h := abs_choice p <;> rw [h]
  · exact hp
  · exact hp.neg
#align prime.abs Prime.abs

end CommRing

