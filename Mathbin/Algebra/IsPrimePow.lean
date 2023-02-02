/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module algebra.is_prime_pow
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Associated
import Mathbin.NumberTheory.Divisors

/-!
# Prime powers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file deals with prime powers: numbers which are positive integer powers of a single prime.
-/


variable {R : Type _} [CommMonoidWithZero R] (n p : R) (k : ℕ)

#print IsPrimePow /-
/-- `n` is a prime power if there is a prime `p` and a positive natural `k` such that `n` can be
written as `p^k`. -/
def IsPrimePow : Prop :=
  ∃ (p : R)(k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n
#align is_prime_pow IsPrimePow
-/

#print isPrimePow_def /-
theorem isPrimePow_def : IsPrimePow n ↔ ∃ (p : R)(k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n :=
  Iff.rfl
#align is_prime_pow_def isPrimePow_def
-/

#print isPrimePow_iff_pow_succ /-
/-- An equivalent definition for prime powers: `n` is a prime power iff there is a prime `p` and a
natural `k` such that `n` can be written as `p^(k+1)`. -/
theorem isPrimePow_iff_pow_succ : IsPrimePow n ↔ ∃ (p : R)(k : ℕ), Prime p ∧ p ^ (k + 1) = n :=
  (isPrimePow_def _).trans
    ⟨fun ⟨p, k, hp, hk, hn⟩ => ⟨_, _, hp, by rwa [Nat.sub_add_cancel hk]⟩, fun ⟨p, k, hp, hn⟩ =>
      ⟨_, _, hp, Nat.succ_pos', hn⟩⟩
#align is_prime_pow_iff_pow_succ isPrimePow_iff_pow_succ
-/

/- warning: not_is_prime_pow_zero -> not_isPrimePow_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (MulZeroClass.toHasMul.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1))))], Not (IsPrimePow.{u1} R _inst_1 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (MulZeroClass.toMul.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1)))) (CommMonoidWithZero.toZero.{u1} R _inst_1)], Not (IsPrimePow.{u1} R _inst_1 (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align not_is_prime_pow_zero not_isPrimePow_zeroₓ'. -/
theorem not_isPrimePow_zero [NoZeroDivisors R] : ¬IsPrimePow (0 : R) :=
  by
  simp only [isPrimePow_def, not_exists, not_and', and_imp]
  intro x n hn hx
  rw [pow_eq_zero hx]
  simp
#align not_is_prime_pow_zero not_isPrimePow_zero

#print IsPrimePow.not_unit /-
theorem IsPrimePow.not_unit {n : R} (h : IsPrimePow n) : ¬IsUnit n :=
  let ⟨p, k, hp, hk, hn⟩ := h
  hn ▸ (isUnit_pow_iff hk.ne').Not.mpr hp.not_unit
#align is_prime_pow.not_unit IsPrimePow.not_unit
-/

#print IsUnit.not_isPrimePow /-
theorem IsUnit.not_isPrimePow {n : R} (h : IsUnit n) : ¬IsPrimePow n := fun h' => h'.not_unit h
#align is_unit.not_is_prime_pow IsUnit.not_isPrimePow
-/

/- warning: not_is_prime_pow_one -> not_isPrimePow_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} R], Not (IsPrimePow.{u1} R _inst_1 (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} R], Not (IsPrimePow.{u1} R _inst_1 (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R (MonoidWithZero.toMonoid.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align not_is_prime_pow_one not_isPrimePow_oneₓ'. -/
theorem not_isPrimePow_one : ¬IsPrimePow (1 : R) :=
  isUnit_one.not_isPrimePow
#align not_is_prime_pow_one not_isPrimePow_one

#print Prime.isPrimePow /-
theorem Prime.isPrimePow {p : R} (hp : Prime p) : IsPrimePow p :=
  ⟨p, 1, hp, zero_lt_one, by simp⟩
#align prime.is_prime_pow Prime.isPrimePow
-/

#print IsPrimePow.pow /-
theorem IsPrimePow.pow {n : R} (hn : IsPrimePow n) {k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) :=
  let ⟨p, k', hp, hk', hn⟩ := hn
  ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by rw [pow_mul', hn]⟩
#align is_prime_pow.pow IsPrimePow.pow
-/

/- warning: is_prime_pow.ne_zero -> IsPrimePow.ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (MulZeroClass.toHasMul.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1))))] {n : R}, (IsPrimePow.{u1} R _inst_1 n) -> (Ne.{succ u1} R n (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (MulZeroClass.toMul.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1)))) (CommMonoidWithZero.toZero.{u1} R _inst_1)] {n : R}, (IsPrimePow.{u1} R _inst_1 n) -> (Ne.{succ u1} R n (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align is_prime_pow.ne_zero IsPrimePow.ne_zeroₓ'. -/
theorem IsPrimePow.ne_zero [NoZeroDivisors R] {n : R} (h : IsPrimePow n) : n ≠ 0 := fun t =>
  Eq.ndrec not_isPrimePow_zero t.symm h
#align is_prime_pow.ne_zero IsPrimePow.ne_zero

/- warning: is_prime_pow.ne_one -> IsPrimePow.ne_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} R] {n : R}, (IsPrimePow.{u1} R _inst_1 n) -> (Ne.{succ u1} R n (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} R] {n : R}, (IsPrimePow.{u1} R _inst_1 n) -> (Ne.{succ u1} R n (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R (MonoidWithZero.toMonoid.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align is_prime_pow.ne_one IsPrimePow.ne_oneₓ'. -/
theorem IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n ≠ 1 := fun t =>
  Eq.ndrec not_isPrimePow_one t.symm h
#align is_prime_pow.ne_one IsPrimePow.ne_one

section Nat

#print isPrimePow_nat_iff /-
theorem isPrimePow_nat_iff (n : ℕ) : IsPrimePow n ↔ ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p ^ k = n := by
  simp only [isPrimePow_def, Nat.prime_iff]
#align is_prime_pow_nat_iff isPrimePow_nat_iff
-/

#print Nat.Prime.isPrimePow /-
theorem Nat.Prime.isPrimePow {p : ℕ} (hp : p.Prime) : IsPrimePow p :=
  hp.Prime.IsPrimePow
#align nat.prime.is_prime_pow Nat.Prime.isPrimePow
-/

#print isPrimePow_nat_iff_bounded /-
theorem isPrimePow_nat_iff_bounded (n : ℕ) :
    IsPrimePow n ↔ ∃ p : ℕ, p ≤ n ∧ ∃ k : ℕ, k ≤ n ∧ p.Prime ∧ 0 < k ∧ p ^ k = n :=
  by
  rw [isPrimePow_nat_iff]
  refine' Iff.symm ⟨fun ⟨p, _, k, _, hp, hk, hn⟩ => ⟨p, k, hp, hk, hn⟩, _⟩
  rintro ⟨p, k, hp, hk, rfl⟩
  refine' ⟨p, _, k, (Nat.lt_pow_self hp.one_lt _).le, hp, hk, rfl⟩
  simpa using Nat.pow_le_pow_of_le_right hp.pos hk
#align is_prime_pow_nat_iff_bounded isPrimePow_nat_iff_bounded
-/

instance {n : ℕ} : Decidable (IsPrimePow n) :=
  decidable_of_iff' _ (isPrimePow_nat_iff_bounded n)

#print IsPrimePow.dvd /-
theorem IsPrimePow.dvd {n m : ℕ} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m ≠ 1) : IsPrimePow m :=
  by
  rw [isPrimePow_nat_iff] at hn⊢
  rcases hn with ⟨p, k, hp, hk, rfl⟩
  obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow hp).1 hm
  refine' ⟨p, i, hp, _, rfl⟩
  apply Nat.pos_of_ne_zero
  rintro rfl
  simpa using hm₁
#align is_prime_pow.dvd IsPrimePow.dvd
-/

/- warning: nat.disjoint_divisors_filter_prime_pow -> Nat.disjoint_divisors_filter_isPrimePow is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {b : Nat}, (Nat.coprime a b) -> (Disjoint.{0} (Finset.{0} Nat) (Finset.partialOrder.{0} Nat) (Finset.orderBot.{0} Nat) (Finset.filter.{0} Nat (IsPrimePow.{0} Nat (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (fun (a : Nat) => IsPrimePow.decidable a) (Nat.divisors a)) (Finset.filter.{0} Nat (IsPrimePow.{0} Nat (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (fun (a : Nat) => IsPrimePow.decidable a) (Nat.divisors b)))
but is expected to have type
  forall {a : Nat} {b : Nat}, (Nat.coprime a b) -> (Disjoint.{0} (Finset.{0} Nat) (Finset.partialOrder.{0} Nat) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{0} Nat) (Finset.filter.{0} Nat (IsPrimePow.{0} Nat (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (fun (a : Nat) => instDecidableIsPrimePowNatToCommMonoidWithZeroLinearOrderedCommMonoidWithZero a) (Nat.divisors a)) (Finset.filter.{0} Nat (IsPrimePow.{0} Nat (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{0} Nat Nat.linearOrderedCommMonoidWithZero)) (fun (a : Nat) => instDecidableIsPrimePowNatToCommMonoidWithZeroLinearOrderedCommMonoidWithZero a) (Nat.divisors b)))
Case conversion may be inaccurate. Consider using '#align nat.disjoint_divisors_filter_prime_pow Nat.disjoint_divisors_filter_isPrimePowₓ'. -/
theorem Nat.disjoint_divisors_filter_isPrimePow {a b : ℕ} (hab : a.coprime b) :
    Disjoint (a.divisors.filterₓ IsPrimePow) (b.divisors.filterₓ IsPrimePow) :=
  by
  simp only [Finset.disjoint_left, Finset.mem_filter, and_imp, Nat.mem_divisors, not_and]
  rintro n han ha hn hbn hb -
  exact hn.ne_one (Nat.eq_one_of_dvd_coprimes hab han hbn)
#align nat.disjoint_divisors_filter_prime_pow Nat.disjoint_divisors_filter_isPrimePow

#print IsPrimePow.two_le /-
theorem IsPrimePow.two_le : ∀ {n : ℕ}, IsPrimePow n → 2 ≤ n
  | 0, h => (not_isPrimePow_zero h).elim
  | 1, h => (not_isPrimePow_one h).elim
  | n + 2, _ => le_add_self
#align is_prime_pow.two_le IsPrimePow.two_le
-/

#print IsPrimePow.pos /-
theorem IsPrimePow.pos {n : ℕ} (hn : IsPrimePow n) : 0 < n :=
  pos_of_gt hn.two_le
#align is_prime_pow.pos IsPrimePow.pos
-/

#print IsPrimePow.one_lt /-
theorem IsPrimePow.one_lt {n : ℕ} (h : IsPrimePow n) : 1 < n :=
  h.two_le
#align is_prime_pow.one_lt IsPrimePow.one_lt
-/

end Nat

