/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

! This file was ported from Lean 3 source module algebra.char_p.char_and_card
! leanprover-community/mathlib commit 75be6b616681ab6ca66d798ead117e75cd64f125
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.GroupTheory.Perm.Cycle.Type

/-!
# Characteristic and cardinality

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove some results relating characteristic and cardinality of finite rings

## Tags
characterstic, cardinality, ring
-/


/- warning: is_unit_iff_not_dvd_char_of_ring_char_ne_zero -> isUnit_iff_not_dvd_char_of_ringChar_ne_zero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (p : Nat) [_inst_2 : Fact (Nat.Prime p)], (Ne.{1} Nat (ringChar.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Iff (IsUnit.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) p)) (Not (Dvd.Dvd.{0} Nat Nat.hasDvd p (ringChar.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (p : Nat) [_inst_2 : Fact (Nat.Prime p)], (Ne.{1} Nat (ringChar.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Iff (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) p)) (Not (Dvd.dvd.{0} Nat Nat.instDvdNat p (ringChar.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align is_unit_iff_not_dvd_char_of_ring_char_ne_zero isUnit_iff_not_dvd_char_of_ringChar_ne_zeroₓ'. -/
/-- A prime `p` is a unit in a commutative ring `R` of nonzero characterstic iff it does not divide
the characteristic. -/
theorem isUnit_iff_not_dvd_char_of_ringChar_ne_zero (R : Type _) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : ringChar R ≠ 0) : IsUnit (p : R) ↔ ¬p ∣ ringChar R :=
  by
  have hch := CharP.cast_eq_zero R (ringChar R)
  have hp : p.prime := Fact.out p.prime
  constructor
  · rintro h₁ ⟨q, hq⟩
    rcases IsUnit.exists_left_inv h₁ with ⟨a, ha⟩
    have h₃ : ¬ringChar R ∣ q := by
      rintro ⟨r, hr⟩
      rw [hr, ← mul_assoc, mul_comm p, mul_assoc] at hq
      nth_rw 1 [← mul_one (ringChar R)] at hq
      exact Nat.Prime.not_dvd_one hp ⟨r, mul_left_cancel₀ hR hq⟩
    have h₄ := mt (CharP.int_cast_eq_zero_iff R (ringChar R) q).mp
    apply_fun (coe : ℕ → R)  at hq
    apply_fun (· * ·) a  at hq
    rw [Nat.cast_mul, hch, MulZeroClass.mul_zero, ← mul_assoc, ha, one_mul] at hq
    norm_cast  at h₄
    exact h₄ h₃ hq.symm
  · intro h
    rcases(hp.coprime_iff_not_dvd.mpr h).IsCoprime with ⟨a, b, hab⟩
    apply_fun (coe : ℤ → R)  at hab
    push_cast at hab
    rw [hch, MulZeroClass.mul_zero, add_zero, mul_comm] at hab
    exact isUnit_of_mul_eq_one (p : R) a hab
#align is_unit_iff_not_dvd_char_of_ring_char_ne_zero isUnit_iff_not_dvd_char_of_ringChar_ne_zero

/- warning: is_unit_iff_not_dvd_char -> isUnit_iff_not_dvd_char is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (p : Nat) [_inst_2 : Fact (Nat.Prime p)] [_inst_3 : Finite.{succ u1} R], Iff (IsUnit.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) p)) (Not (Dvd.Dvd.{0} Nat Nat.hasDvd p (ringChar.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : CommRing.{u1} R] (p : Nat) [_inst_2 : Fact (Nat.Prime p)] [_inst_3 : Finite.{succ u1} R], Iff (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) p)) (Not (Dvd.dvd.{0} Nat Nat.instDvdNat p (ringChar.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align is_unit_iff_not_dvd_char isUnit_iff_not_dvd_charₓ'. -/
/-- A prime `p` is a unit in a finite commutative ring `R`
iff it does not divide the characteristic. -/
theorem isUnit_iff_not_dvd_char (R : Type _) [CommRing R] (p : ℕ) [Fact p.Prime] [Finite R] :
    IsUnit (p : R) ↔ ¬p ∣ ringChar R :=
  isUnit_iff_not_dvd_char_of_ringChar_ne_zero R p <| CharP.char_ne_zero_of_finite R (ringChar R)
#align is_unit_iff_not_dvd_char isUnit_iff_not_dvd_char

#print prime_dvd_char_iff_dvd_card /-
/-- The prime divisors of the characteristic of a finite commutative ring are exactly
the prime divisors of its cardinality. -/
theorem prime_dvd_char_iff_dvd_card {R : Type _} [CommRing R] [Fintype R] (p : ℕ) [Fact p.Prime] :
    p ∣ ringChar R ↔ p ∣ Fintype.card R :=
  by
  refine'
    ⟨fun h =>
      h.trans <|
        int.coe_nat_dvd.mp <|
          (CharP.int_cast_eq_zero_iff R (ringChar R) (Fintype.card R)).mp <| by
            exact_mod_cast CharP.cast_card_eq_zero R,
      fun h => _⟩
  by_contra h₀
  rcases exists_prime_addOrderOf_dvd_card p h with ⟨r, hr⟩
  have hr₁ := addOrderOf_nsmul_eq_zero r
  rw [hr, nsmul_eq_mul] at hr₁
  rcases IsUnit.exists_left_inv ((isUnit_iff_not_dvd_char R p).mpr h₀) with ⟨u, hu⟩
  apply_fun (· * ·) u  at hr₁
  rw [MulZeroClass.mul_zero, ← mul_assoc, hu, one_mul] at hr₁
  exact
    mt add_monoid.order_of_eq_one_iff.mpr (ne_of_eq_of_ne hr (Nat.Prime.ne_one (Fact.out p.prime)))
      hr₁
#align prime_dvd_char_iff_dvd_card prime_dvd_char_iff_dvd_card
-/

/- warning: not_is_unit_prime_of_dvd_card -> not_isUnit_prime_of_dvd_card is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Fintype.{u1} R] (p : Nat) [_inst_3 : Fact (Nat.Prime p)], (Dvd.Dvd.{0} Nat Nat.hasDvd p (Fintype.card.{u1} R _inst_2)) -> (Not (IsUnit.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) p)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Fintype.{u1} R] (p : Nat) [_inst_3 : Fact (Nat.Prime p)], (Dvd.dvd.{0} Nat Nat.instDvdNat p (Fintype.card.{u1} R _inst_2)) -> (Not (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) p)))
Case conversion may be inaccurate. Consider using '#align not_is_unit_prime_of_dvd_card not_isUnit_prime_of_dvd_cardₓ'. -/
/-- A prime that does not divide the cardinality of a finite commutative ring `R`
is a unit in `R`. -/
theorem not_isUnit_prime_of_dvd_card {R : Type _} [CommRing R] [Fintype R] (p : ℕ) [Fact p.Prime]
    (hp : p ∣ Fintype.card R) : ¬IsUnit (p : R) :=
  mt (isUnit_iff_not_dvd_char R p).mp
    (Classical.not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))
#align not_is_unit_prime_of_dvd_card not_isUnit_prime_of_dvd_card

