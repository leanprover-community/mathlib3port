/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

! This file was ported from Lean 3 source module number_theory.padics.padic_norm
! leanprover-community/mathlib commit cb3ceec8485239a61ed51d944cb9a95b68c6bafc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.NumberTheory.Padics.PadicVal

/-!
# p-adic norm

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `p`-adic norm on `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`.

The valuation induces a norm on `ℚ`. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Notations

This file uses the local notation `/.` for `rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact p.prime]` as a type class argument.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/


#print padicNorm /-
/-- If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ -padic_val_rat p q`.
If `q = 0`, the `p`-adic norm of `q` is `0`. -/
def padicNorm (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else (p : ℚ) ^ (-padicValRat p q)
#align padic_norm padicNorm
-/

namespace padicNorm

open padicValRat

variable {p : ℕ}

/- warning: padic_norm.eq_zpow_of_nonzero -> padicNorm.eq_zpow_of_nonzero is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) -> (Eq.{1} Rat (padicNorm p q) (HPow.hPow.{0, 0, 0} Rat Int Rat (instHPow.{0, 0} Rat Int (DivInvMonoid.Pow.{0} Rat (DivisionRing.toDivInvMonoid.{0} Rat Rat.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) p) (Neg.neg.{0} Int Int.hasNeg (padicValRat p q))))
but is expected to have type
  forall {p : Nat} {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) -> (Eq.{1} Rat (padicNorm p q) (HPow.hPow.{0, 0, 0} Rat Int Rat (instHPow.{0, 0} Rat Int (DivInvMonoid.Pow.{0} Rat (DivisionRing.toDivInvMonoid.{0} Rat Rat.divisionRing))) (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) p) (Neg.neg.{0} Int Int.instNegInt (padicValRat p q))))
Case conversion may be inaccurate. Consider using '#align padic_norm.eq_zpow_of_nonzero padicNorm.eq_zpow_of_nonzeroₓ'. -/
/-- Unfolds the definition of the `p`-adic norm of `q` when `q ≠ 0`. -/
@[simp]
protected theorem eq_zpow_of_nonzero {q : ℚ} (hq : q ≠ 0) :
    padicNorm p q = p ^ (-padicValRat p q) := by simp [hq, padicNorm]
#align padic_norm.eq_zpow_of_nonzero padicNorm.eq_zpow_of_nonzero

/- warning: padic_norm.nonneg -> padicNorm.nonneg is a dubious translation:
lean 3 declaration is
  forall {p : Nat} (q : Rat), LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) (padicNorm p q)
but is expected to have type
  forall {p : Nat} (q : Rat), LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) (padicNorm p q)
Case conversion may be inaccurate. Consider using '#align padic_norm.nonneg padicNorm.nonnegₓ'. -/
/-- The `p`-adic norm is nonnegative. -/
protected theorem nonneg (q : ℚ) : 0 ≤ padicNorm p q :=
  if hq : q = 0 then by simp [hq, padicNorm]
  else by
    unfold padicNorm <;> split_ifs
    apply zpow_nonneg
    exact_mod_cast Nat.zero_le _
#align padic_norm.nonneg padicNorm.nonneg

#print padicNorm.zero /-
/-- The `p`-adic norm of `0` is `0`. -/
@[simp]
protected theorem zero : padicNorm p 0 = 0 := by simp [padicNorm]
#align padic_norm.zero padicNorm.zero
-/

#print padicNorm.one /-
/-- The `p`-adic norm of `1` is `1`. -/
@[simp]
protected theorem one : padicNorm p 1 = 1 := by simp [padicNorm]
#align padic_norm.one padicNorm.one
-/

/- warning: padic_norm.padic_norm_p -> padicNorm.padicNorm_p is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) p) -> (Eq.{1} Rat (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) p)) (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) p)))
but is expected to have type
  forall {p : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) p) -> (Eq.{1} Rat (padicNorm p (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) p)) (Inv.inv.{0} Rat Rat.instInvRat (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) p)))
Case conversion may be inaccurate. Consider using '#align padic_norm.padic_norm_p padicNorm.padicNorm_pₓ'. -/
/-- The `p`-adic norm of `p` is `p⁻¹` if `p > 1`.

See also `padic_norm.padic_norm_p_of_prime` for a version assuming `p` is prime. -/
theorem padicNorm_p (hp : 1 < p) : padicNorm p p = p⁻¹ := by
  simp [padicNorm, (pos_of_gt hp).ne', padicValNat.self hp]
#align padic_norm.padic_norm_p padicNorm.padicNorm_p

/- warning: padic_norm.padic_norm_p_of_prime -> padicNorm.padicNorm_p_of_prime is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], Eq.{1} Rat (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) p)) (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) p))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], Eq.{1} Rat (padicNorm p (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) p)) (Inv.inv.{0} Rat Rat.instInvRat (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) p))
Case conversion may be inaccurate. Consider using '#align padic_norm.padic_norm_p_of_prime padicNorm.padicNorm_p_of_primeₓ'. -/
/-- The `p`-adic norm of `p` is `p⁻¹` if `p` is prime.

See also `padic_norm.padic_norm_p` for a version assuming `1 < p`. -/
@[simp]
theorem padicNorm_p_of_prime [Fact p.Prime] : padicNorm p p = p⁻¹ :=
  padicNorm_p <| Nat.Prime.one_lt (Fact.out _)
#align padic_norm.padic_norm_p_of_prime padicNorm.padicNorm_p_of_prime

/- warning: padic_norm.padic_norm_of_prime_of_ne -> padicNorm.padicNorm_of_prime_of_ne is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {q : Nat} [p_prime : Fact (Nat.Prime p)] [q_prime : Fact (Nat.Prime q)], (Ne.{1} Nat p q) -> (Eq.{1} Rat (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) q)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))))
but is expected to have type
  forall {p : Nat} {q : Nat} [p_prime : Fact (Nat.Prime p)] [q_prime : Fact (Nat.Prime q)], (Ne.{1} Nat p q) -> (Eq.{1} Rat (padicNorm p (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) q)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)))
Case conversion may be inaccurate. Consider using '#align padic_norm.padic_norm_of_prime_of_ne padicNorm.padicNorm_of_prime_of_neₓ'. -/
/-- The `p`-adic norm of `q` is `1` if `q` is prime and not equal to `p`. -/
theorem padicNorm_of_prime_of_ne {q : ℕ} [p_prime : Fact p.Prime] [q_prime : Fact q.Prime]
    (neq : p ≠ q) : padicNorm p q = 1 :=
  by
  have p : padicValRat p q = 0 := by exact_mod_cast @padicValNat_primes p q p_prime q_prime neq
  simp [padicNorm, p, q_prime.1.1, q_prime.1.NeZero]
#align padic_norm.padic_norm_of_prime_of_ne padicNorm.padicNorm_of_prime_of_ne

/- warning: padic_norm.padic_norm_p_lt_one -> padicNorm.padicNorm_p_lt_one is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) p) -> (LT.lt.{0} Rat Rat.hasLt (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) p)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))))
but is expected to have type
  forall {p : Nat}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) p) -> (LT.lt.{0} Rat Rat.instLTRat_1 (padicNorm p (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) p)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)))
Case conversion may be inaccurate. Consider using '#align padic_norm.padic_norm_p_lt_one padicNorm.padicNorm_p_lt_oneₓ'. -/
/-- The `p`-adic norm of `p` is less than `1` if `1 < p`.

See also `padic_norm.padic_norm_p_lt_one_of_prime` for a version assuming `p` is prime. -/
theorem padicNorm_p_lt_one (hp : 1 < p) : padicNorm p p < 1 :=
  by
  rw [padic_norm_p hp, inv_lt_one_iff]
  exact_mod_cast Or.inr hp
#align padic_norm.padic_norm_p_lt_one padicNorm.padicNorm_p_lt_one

/- warning: padic_norm.padic_norm_p_lt_one_of_prime -> padicNorm.padicNorm_p_lt_one_of_prime is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], LT.lt.{0} Rat Rat.hasLt (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) p)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))
but is expected to have type
  forall {p : Nat} [_inst_1 : Fact (Nat.Prime p)], LT.lt.{0} Rat Rat.instLTRat_1 (padicNorm p (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) p)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))
Case conversion may be inaccurate. Consider using '#align padic_norm.padic_norm_p_lt_one_of_prime padicNorm.padicNorm_p_lt_one_of_primeₓ'. -/
/-- The `p`-adic norm of `p` is less than `1` if `p` is prime.

See also `padic_norm.padic_norm_p_lt_one` for a version assuming `1 < p`. -/
theorem padicNorm_p_lt_one_of_prime [Fact p.Prime] : padicNorm p p < 1 :=
  padicNorm_p_lt_one <| Nat.Prime.one_lt (Fact.out _)
#align padic_norm.padic_norm_p_lt_one_of_prime padicNorm.padicNorm_p_lt_one_of_prime

/- warning: padic_norm.values_discrete -> padicNorm.values_discrete is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))) -> (Exists.{1} Int (fun (z : Int) => Eq.{1} Rat (padicNorm p q) (HPow.hPow.{0, 0, 0} Rat Int Rat (instHPow.{0, 0} Rat Int (DivInvMonoid.Pow.{0} Rat (DivisionRing.toDivInvMonoid.{0} Rat Rat.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) p) (Neg.neg.{0} Int Int.hasNeg z))))
but is expected to have type
  forall {p : Nat} {q : Rat}, (Ne.{1} Rat q (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))) -> (Exists.{1} Int (fun (z : Int) => Eq.{1} Rat (padicNorm p q) (HPow.hPow.{0, 0, 0} Rat Int Rat (instHPow.{0, 0} Rat Int (DivInvMonoid.Pow.{0} Rat (DivisionRing.toDivInvMonoid.{0} Rat Rat.divisionRing))) (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) p) (Neg.neg.{0} Int Int.instNegInt z))))
Case conversion may be inaccurate. Consider using '#align padic_norm.values_discrete padicNorm.values_discreteₓ'. -/
/-- `padic_norm p q` takes discrete values `p ^ -z` for `z : ℤ`. -/
protected theorem values_discrete {q : ℚ} (hq : q ≠ 0) : ∃ z : ℤ, padicNorm p q = p ^ (-z) :=
  ⟨padicValRat p q, by simp [padicNorm, hq]⟩
#align padic_norm.values_discrete padicNorm.values_discrete

#print padicNorm.neg /-
/-- `padic_norm p` is symmetric. -/
@[simp]
protected theorem neg (q : ℚ) : padicNorm p (-q) = padicNorm p q :=
  if hq : q = 0 then by simp [hq] else by simp [padicNorm, hq]
#align padic_norm.neg padicNorm.neg
-/

variable [hp : Fact p.Prime]

include hp

#print padicNorm.nonzero /-
/-- If `q ≠ 0`, then `padic_norm p q ≠ 0`. -/
protected theorem nonzero {q : ℚ} (hq : q ≠ 0) : padicNorm p q ≠ 0 :=
  by
  rw [padicNorm.eq_zpow_of_nonzero hq]
  apply zpow_ne_zero_of_ne_zero
  exact_mod_cast ne_of_gt hp.1.Pos
#align padic_norm.nonzero padicNorm.nonzero
-/

#print padicNorm.zero_of_padicNorm_eq_zero /-
/-- If the `p`-adic norm of `q` is 0, then `q` is `0`. -/
theorem zero_of_padicNorm_eq_zero {q : ℚ} (h : padicNorm p q = 0) : q = 0 :=
  by
  apply by_contradiction; intro hq
  unfold padicNorm at h; rw [if_neg hq] at h
  apply absurd h
  apply zpow_ne_zero_of_ne_zero
  exact_mod_cast hp.1.NeZero
#align padic_norm.zero_of_padic_norm_eq_zero padicNorm.zero_of_padicNorm_eq_zero
-/

#print padicNorm.mul /-
/-- The `p`-adic norm is multiplicative. -/
@[simp]
protected theorem mul (q r : ℚ) : padicNorm p (q * r) = padicNorm p q * padicNorm p r :=
  if hq : q = 0 then by simp [hq]
  else
    if hr : r = 0 then by simp [hr]
    else by
      have : q * r ≠ 0 := mul_ne_zero hq hr
      have : (p : ℚ) ≠ 0 := by simp [hp.1.NeZero]
      simp [padicNorm, *, padicValRat.mul, zpow_add₀ this, mul_comm]
#align padic_norm.mul padicNorm.mul
-/

#print padicNorm.div /-
/-- The `p`-adic norm respects division. -/
@[simp]
protected theorem div (q r : ℚ) : padicNorm p (q / r) = padicNorm p q / padicNorm p r :=
  if hr : r = 0 then by simp [hr]
  else eq_div_of_mul_eq (padicNorm.nonzero hr) (by rw [← padicNorm.mul, div_mul_cancel _ hr])
#align padic_norm.div padicNorm.div
-/

/- warning: padic_norm.of_int -> padicNorm.of_int is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (z : Int), LE.le.{0} Rat Rat.hasLe (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) z)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (z : Int), LE.le.{0} Rat Rat.instLERat (padicNorm p (Int.cast.{0} Rat Rat.instIntCastRat z)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))
Case conversion may be inaccurate. Consider using '#align padic_norm.of_int padicNorm.of_intₓ'. -/
/-- The `p`-adic norm of an integer is at most `1`. -/
protected theorem of_int (z : ℤ) : padicNorm p z ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by
    unfold padicNorm
    rw [if_neg _]
    · refine' zpow_le_one_of_nonpos _ _
      · exact_mod_cast le_of_lt hp.1.one_lt
      · rw [padicValRat.of_int, neg_nonpos]
        norm_cast; simp
    exact_mod_cast hz
#align padic_norm.of_int padicNorm.of_int

private theorem nonarchimedean_aux {q r : ℚ} (h : padicValRat p q ≤ padicValRat p r) :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
  have hnqp : padicNorm p q ≥ 0 := padicNorm.nonneg _
  have hnrp : padicNorm p r ≥ 0 := padicNorm.nonneg _
  if hq : q = 0 then by simp [hq, max_eq_right hnrp, le_max_right]
  else
    if hr : r = 0 then by simp [hr, max_eq_left hnqp, le_max_left]
    else
      if hqr : q + r = 0 then le_trans (by simpa [hqr] using hnqp) (le_max_left _ _)
      else by
        unfold padicNorm; split_ifs
        apply le_max_iff.2
        left
        apply zpow_le_of_le
        · exact_mod_cast le_of_lt hp.1.one_lt
        · apply neg_le_neg
          have : padicValRat p q = min (padicValRat p q) (padicValRat p r) := (min_eq_left h).symm
          rw [this]
          apply min_le_padic_val_rat_add <;> assumption

/- warning: padic_norm.nonarchimedean -> padicNorm.nonarchimedean is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {q : Rat} {r : Rat}, LE.le.{0} Rat Rat.hasLe (padicNorm p (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) q r)) (LinearOrder.max.{0} Rat Rat.linearOrder (padicNorm p q) (padicNorm p r))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {q : Rat} {r : Rat}, LE.le.{0} Rat Rat.instLERat (padicNorm p (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) q r)) (Max.max.{0} Rat (LinearOrderedRing.toMax.{0} Rat Rat.instLinearOrderedRingRat) (padicNorm p q) (padicNorm p r))
Case conversion may be inaccurate. Consider using '#align padic_norm.nonarchimedean padicNorm.nonarchimedeanₓ'. -/
/-- The `p`-adic norm is nonarchimedean: the norm of `p + q` is at most the max of the norm of `p`
and the norm of `q`. -/
protected theorem nonarchimedean {q r : ℚ} :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
  by
  wlog hle : padicValRat p q ≤ padicValRat p r generalizing q r
  · rw [add_comm, max_comm]; exact this (le_of_not_le hle)
  exact nonarchimedean_aux hle
#align padic_norm.nonarchimedean padicNorm.nonarchimedean

/- warning: padic_norm.triangle_ineq -> padicNorm.triangle_ineq is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (q : Rat) (r : Rat), LE.le.{0} Rat Rat.hasLe (padicNorm p (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) q r)) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) (padicNorm p q) (padicNorm p r))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (q : Rat) (r : Rat), LE.le.{0} Rat Rat.instLERat (padicNorm p (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) q r)) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) (padicNorm p q) (padicNorm p r))
Case conversion may be inaccurate. Consider using '#align padic_norm.triangle_ineq padicNorm.triangle_ineqₓ'. -/
/-- The `p`-adic norm respects the triangle inequality: the norm of `p + q` is at most the norm of
`p` plus the norm of `q`. -/
theorem triangle_ineq (q r : ℚ) : padicNorm p (q + r) ≤ padicNorm p q + padicNorm p r :=
  calc
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) := padicNorm.nonarchimedean
    _ ≤ padicNorm p q + padicNorm p r :=
      max_le_add_of_nonneg (padicNorm.nonneg _) (padicNorm.nonneg _)
    
#align padic_norm.triangle_ineq padicNorm.triangle_ineq

/- warning: padic_norm.sub -> padicNorm.sub is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {q : Rat} {r : Rat}, LE.le.{0} Rat Rat.hasLe (padicNorm p (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) q r)) (LinearOrder.max.{0} Rat Rat.linearOrder (padicNorm p q) (padicNorm p r))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {q : Rat} {r : Rat}, LE.le.{0} Rat Rat.instLERat (padicNorm p (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) q r)) (Max.max.{0} Rat (LinearOrderedRing.toMax.{0} Rat Rat.instLinearOrderedRingRat) (padicNorm p q) (padicNorm p r))
Case conversion may be inaccurate. Consider using '#align padic_norm.sub padicNorm.subₓ'. -/
/-- The `p`-adic norm of a difference is at most the max of each component. Restates the archimedean
property of the `p`-adic norm. -/
protected theorem sub {q r : ℚ} : padicNorm p (q - r) ≤ max (padicNorm p q) (padicNorm p r) := by
  rw [sub_eq_add_neg, ← padicNorm.neg r] <;> apply padicNorm.nonarchimedean
#align padic_norm.sub padicNorm.sub

/- warning: padic_norm.add_eq_max_of_ne -> padicNorm.add_eq_max_of_ne is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {q : Rat} {r : Rat}, (Ne.{1} Rat (padicNorm p q) (padicNorm p r)) -> (Eq.{1} Rat (padicNorm p (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) q r)) (LinearOrder.max.{0} Rat Rat.linearOrder (padicNorm p q) (padicNorm p r)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {q : Rat} {r : Rat}, (Ne.{1} Rat (padicNorm p q) (padicNorm p r)) -> (Eq.{1} Rat (padicNorm p (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) q r)) (Max.max.{0} Rat (LinearOrderedRing.toMax.{0} Rat Rat.instLinearOrderedRingRat) (padicNorm p q) (padicNorm p r)))
Case conversion may be inaccurate. Consider using '#align padic_norm.add_eq_max_of_ne padicNorm.add_eq_max_of_neₓ'. -/
/-- If the `p`-adic norms of `q` and `r` are different, then the norm of `q + r` is equal to the max
of the norms of `q` and `r`. -/
theorem add_eq_max_of_ne {q r : ℚ} (hne : padicNorm p q ≠ padicNorm p r) :
    padicNorm p (q + r) = max (padicNorm p q) (padicNorm p r) :=
  by
  wlog hlt : padicNorm p r < padicNorm p q
  · rw [add_comm, max_comm]; exact this hne.symm (hne.lt_or_lt.resolve_right hlt)
  have : padicNorm p q ≤ max (padicNorm p (q + r)) (padicNorm p r) :=
    calc
      padicNorm p q = padicNorm p (q + r - r) := by congr <;> ring
      _ ≤ max (padicNorm p (q + r)) (padicNorm p (-r)) := padicNorm.nonarchimedean
      _ = max (padicNorm p (q + r)) (padicNorm p r) := by simp
      
  have hnge : padicNorm p r ≤ padicNorm p (q + r) :=
    by
    apply le_of_not_gt
    intro hgt
    rw [max_eq_right_of_lt hgt] at this
    apply not_lt_of_ge this
    assumption
  have : padicNorm p q ≤ padicNorm p (q + r) := by rwa [max_eq_left hnge] at this
  apply _root_.le_antisymm
  · apply padicNorm.nonarchimedean
  · rwa [max_eq_left_of_lt hlt]
#align padic_norm.add_eq_max_of_ne padicNorm.add_eq_max_of_ne

/-- The `p`-adic norm is an absolute value: positive-definite and multiplicative, satisfying the
triangle inequality. -/
instance : IsAbsoluteValue (padicNorm p)
    where
  abv_nonneg := padicNorm.nonneg
  abv_eq_zero _ := ⟨zero_of_padicNorm_eq_zero, fun hx => by simpa only [hx] ⟩
  abv_add := padicNorm.triangle_ineq
  abv_mul := padicNorm.mul

/- warning: padic_norm.dvd_iff_norm_le -> padicNorm.dvd_iff_norm_le is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {n : Nat} {z : Int}, Iff (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p n)) z) (LE.le.{0} Rat Rat.hasLe (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) z)) (HPow.hPow.{0, 0, 0} Rat Int Rat (instHPow.{0, 0} Rat Int (DivInvMonoid.Pow.{0} Rat (DivisionRing.toDivInvMonoid.{0} Rat Rat.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) p) (Neg.neg.{0} Int Int.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n))))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {n : Nat} {z : Int}, Iff (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n)) z) (LE.le.{0} Rat Rat.instLERat (padicNorm p (Int.cast.{0} Rat Rat.instIntCastRat z)) (HPow.hPow.{0, 0, 0} Rat Int Rat (instHPow.{0, 0} Rat Int (DivInvMonoid.Pow.{0} Rat (DivisionRing.toDivInvMonoid.{0} Rat Rat.divisionRing))) (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) p) (Neg.neg.{0} Int Int.instNegInt (Nat.cast.{0} Int instNatCastInt n))))
Case conversion may be inaccurate. Consider using '#align padic_norm.dvd_iff_norm_le padicNorm.dvd_iff_norm_leₓ'. -/
theorem dvd_iff_norm_le {n : ℕ} {z : ℤ} : ↑(p ^ n) ∣ z ↔ padicNorm p z ≤ p ^ (-n : ℤ) :=
  by
  unfold padicNorm; split_ifs with hz
  · norm_cast  at hz
    have : 0 ≤ (p ^ n : ℚ) := by apply pow_nonneg; exact_mod_cast le_of_lt hp.1.Pos
    simp [hz, this]
  · rw [zpow_le_iff_le, neg_le_neg_iff, padicValRat.of_int,
      padicValInt.of_ne_one_ne_zero hp.1.ne_one _]
    · norm_cast
      rw [← PartENat.coe_le_coe, PartENat.natCast_get, ← multiplicity.pow_dvd_iff_le_multiplicity]
      simp
    · exact_mod_cast hz
    · exact_mod_cast hp.1.one_lt
#align padic_norm.dvd_iff_norm_le padicNorm.dvd_iff_norm_le

/- warning: padic_norm.int_eq_one_iff -> padicNorm.int_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (m : Int), Iff (Eq.{1} Rat (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) m)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))) (Not (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) m))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (m : Int), Iff (Eq.{1} Rat (padicNorm p (Int.cast.{0} Rat Rat.instIntCastRat m)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))) (Not (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) m))
Case conversion may be inaccurate. Consider using '#align padic_norm.int_eq_one_iff padicNorm.int_eq_one_iffₓ'. -/
/-- The `p`-adic norm of an integer `m` is one iff `p` doesn't divide `m`. -/
theorem int_eq_one_iff (m : ℤ) : padicNorm p m = 1 ↔ ¬(p : ℤ) ∣ m :=
  by
  nth_rw 2 [← pow_one p]
  simp only [dvd_iff_norm_le, Int.cast_ofNat, Nat.cast_one, zpow_neg, zpow_one, not_le]
  constructor
  · intro h
    rw [h, inv_lt_one_iff_of_pos] <;> norm_cast
    · exact Nat.Prime.one_lt (Fact.out _)
    · exact Nat.Prime.pos (Fact.out _)
  · simp only [padicNorm]
    split_ifs
    · rw [inv_lt_zero, ← Nat.cast_zero, Nat.cast_lt]
      intro h; exact (Nat.not_lt_zero p h).elim
    · have : 1 < (p : ℚ) := by norm_cast <;> exact Nat.Prime.one_lt (Fact.out _ : Nat.Prime p)
      rw [← zpow_neg_one, zpow_lt_iff_lt this]
      have : 0 ≤ padicValRat p m; simp only [of_int, Nat.cast_nonneg]
      intro h
      rw [← zpow_zero (p : ℚ), zpow_inj] <;> linarith
#align padic_norm.int_eq_one_iff padicNorm.int_eq_one_iff

/- warning: padic_norm.int_lt_one_iff -> padicNorm.int_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (m : Int), Iff (LT.lt.{0} Rat Rat.hasLt (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) m)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) m)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (m : Int), Iff (LT.lt.{0} Rat Rat.instLTRat_1 (padicNorm p (Int.cast.{0} Rat Rat.instIntCastRat m)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))) (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) m)
Case conversion may be inaccurate. Consider using '#align padic_norm.int_lt_one_iff padicNorm.int_lt_one_iffₓ'. -/
theorem int_lt_one_iff (m : ℤ) : padicNorm p m < 1 ↔ (p : ℤ) ∣ m :=
  by
  rw [← not_iff_not, ← int_eq_one_iff, eq_iff_le_not_lt]
  simp only [padicNorm.of_int, true_and_iff]
#align padic_norm.int_lt_one_iff padicNorm.int_lt_one_iff

/- warning: padic_norm.of_nat -> padicNorm.of_nat is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (m : Nat), LE.le.{0} Rat Rat.hasLe (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) m)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (m : Nat), LE.le.{0} Rat Rat.instLERat (padicNorm p (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) m)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))
Case conversion may be inaccurate. Consider using '#align padic_norm.of_nat padicNorm.of_natₓ'. -/
theorem of_nat (m : ℕ) : padicNorm p m ≤ 1 :=
  padicNorm.of_int (m : ℤ)
#align padic_norm.of_nat padicNorm.of_nat

/- warning: padic_norm.nat_eq_one_iff -> padicNorm.nat_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (m : Nat), Iff (Eq.{1} Rat (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) m)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))) (Not (Dvd.Dvd.{0} Nat Nat.hasDvd p m))
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (m : Nat), Iff (Eq.{1} Rat (padicNorm p (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) m)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))) (Not (Dvd.dvd.{0} Nat Nat.instDvdNat p m))
Case conversion may be inaccurate. Consider using '#align padic_norm.nat_eq_one_iff padicNorm.nat_eq_one_iffₓ'. -/
/-- The `p`-adic norm of a natural `m` is one iff `p` doesn't divide `m`. -/
theorem nat_eq_one_iff (m : ℕ) : padicNorm p m = 1 ↔ ¬p ∣ m := by
  simp only [← Int.coe_nat_dvd, ← int_eq_one_iff, Int.cast_ofNat]
#align padic_norm.nat_eq_one_iff padicNorm.nat_eq_one_iff

/- warning: padic_norm.nat_lt_one_iff -> padicNorm.nat_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (m : Nat), Iff (LT.lt.{0} Rat Rat.hasLt (padicNorm p ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (StrictOrderedRing.toRing.{0} Rat (LinearOrderedRing.toStrictOrderedRing.{0} Rat Rat.linearOrderedRing))))))))) m)) (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne)))) (Dvd.Dvd.{0} Nat Nat.hasDvd p m)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] (m : Nat), Iff (LT.lt.{0} Rat Rat.instLTRat_1 (padicNorm p (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) m)) (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1))) (Dvd.dvd.{0} Nat Nat.instDvdNat p m)
Case conversion may be inaccurate. Consider using '#align padic_norm.nat_lt_one_iff padicNorm.nat_lt_one_iffₓ'. -/
theorem nat_lt_one_iff (m : ℕ) : padicNorm p m < 1 ↔ p ∣ m := by
  simp only [← Int.coe_nat_dvd, ← int_lt_one_iff, Int.cast_ofNat]
#align padic_norm.nat_lt_one_iff padicNorm.nat_lt_one_iff

open BigOperators

/- warning: padic_norm.sum_lt -> padicNorm.sum_lt is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {α : Type.{u1}} {F : α -> Rat} {t : Rat} {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (forall (i : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) -> (LT.lt.{0} Rat Rat.hasLt (padicNorm p (F i)) t)) -> (LT.lt.{0} Rat Rat.hasLt (padicNorm p (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (i : α) => F i))) t)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {α : Type.{u1}} {F : α -> Rat} {t : Rat} {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (forall (i : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) i s) -> (LT.lt.{0} Rat Rat.instLTRat_1 (padicNorm p (F i)) t)) -> (LT.lt.{0} Rat Rat.instLTRat_1 (padicNorm p (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (i : α) => F i))) t)
Case conversion may be inaccurate. Consider using '#align padic_norm.sum_lt padicNorm.sum_ltₓ'. -/
theorem sum_lt {α : Type _} {F : α → ℚ} {t : ℚ} {s : Finset α} :
    s.Nonempty → (∀ i ∈ s, padicNorm p (F i) < t) → padicNorm p (∑ i in s, F i) < t := by
  classical
    refine' s.induction_on (by rintro ⟨-, ⟨⟩⟩) _
    rintro a S haS IH - ht
    by_cases hs : S.nonempty
    · rw [Finset.sum_insert haS]
      exact
        lt_of_le_of_lt padicNorm.nonarchimedean
          (max_lt (ht a (Finset.mem_insert_self a S))
            (IH hs fun b hb => ht b (Finset.mem_insert_of_mem hb)))
    · simp_all
#align padic_norm.sum_lt padicNorm.sum_lt

/- warning: padic_norm.sum_le -> padicNorm.sum_le is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {α : Type.{u1}} {F : α -> Rat} {t : Rat} {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (forall (i : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) -> (LE.le.{0} Rat Rat.hasLe (padicNorm p (F i)) t)) -> (LE.le.{0} Rat Rat.hasLe (padicNorm p (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (i : α) => F i))) t)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {α : Type.{u1}} {F : α -> Rat} {t : Rat} {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (forall (i : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) i s) -> (LE.le.{0} Rat Rat.instLERat (padicNorm p (F i)) t)) -> (LE.le.{0} Rat Rat.instLERat (padicNorm p (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (i : α) => F i))) t)
Case conversion may be inaccurate. Consider using '#align padic_norm.sum_le padicNorm.sum_leₓ'. -/
theorem sum_le {α : Type _} {F : α → ℚ} {t : ℚ} {s : Finset α} :
    s.Nonempty → (∀ i ∈ s, padicNorm p (F i) ≤ t) → padicNorm p (∑ i in s, F i) ≤ t := by
  classical
    refine' s.induction_on (by rintro ⟨-, ⟨⟩⟩) _
    rintro a S haS IH - ht
    by_cases hs : S.nonempty
    · rw [Finset.sum_insert haS]
      exact
        padic_norm.nonarchimedean.trans
          (max_le (ht a (Finset.mem_insert_self a S))
            (IH hs fun b hb => ht b (Finset.mem_insert_of_mem hb)))
    · simp_all
#align padic_norm.sum_le padicNorm.sum_le

/- warning: padic_norm.sum_lt' -> padicNorm.sum_lt' is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {α : Type.{u1}} {F : α -> Rat} {t : Rat} {s : Finset.{u1} α}, (forall (i : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) -> (LT.lt.{0} Rat Rat.hasLt (padicNorm p (F i)) t)) -> (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) t) -> (LT.lt.{0} Rat Rat.hasLt (padicNorm p (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (i : α) => F i))) t)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {α : Type.{u1}} {F : α -> Rat} {t : Rat} {s : Finset.{u1} α}, (forall (i : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) i s) -> (LT.lt.{0} Rat Rat.instLTRat_1 (padicNorm p (F i)) t)) -> (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) t) -> (LT.lt.{0} Rat Rat.instLTRat_1 (padicNorm p (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (i : α) => F i))) t)
Case conversion may be inaccurate. Consider using '#align padic_norm.sum_lt' padicNorm.sum_lt'ₓ'. -/
theorem sum_lt' {α : Type _} {F : α → ℚ} {t : ℚ} {s : Finset α}
    (hF : ∀ i ∈ s, padicNorm p (F i) < t) (ht : 0 < t) : padicNorm p (∑ i in s, F i) < t :=
  by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_lt hs hF
#align padic_norm.sum_lt' padicNorm.sum_lt'

/- warning: padic_norm.sum_le' -> padicNorm.sum_le' is a dubious translation:
lean 3 declaration is
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {α : Type.{u1}} {F : α -> Rat} {t : Rat} {s : Finset.{u1} α}, (forall (i : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) -> (LE.le.{0} Rat Rat.hasLe (padicNorm p (F i)) t)) -> (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) t) -> (LE.le.{0} Rat Rat.hasLe (padicNorm p (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (i : α) => F i))) t)
but is expected to have type
  forall {p : Nat} [hp : Fact (Nat.Prime p)] {α : Type.{u1}} {F : α -> Rat} {t : Rat} {s : Finset.{u1} α}, (forall (i : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) i s) -> (LE.le.{0} Rat Rat.instLERat (padicNorm p (F i)) t)) -> (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) t) -> (LE.le.{0} Rat Rat.instLERat (padicNorm p (Finset.sum.{0, u1} Rat α Rat.addCommMonoid s (fun (i : α) => F i))) t)
Case conversion may be inaccurate. Consider using '#align padic_norm.sum_le' padicNorm.sum_le'ₓ'. -/
theorem sum_le' {α : Type _} {F : α → ℚ} {t : ℚ} {s : Finset α}
    (hF : ∀ i ∈ s, padicNorm p (F i) ≤ t) (ht : 0 ≤ t) : padicNorm p (∑ i in s, F i) ≤ t :=
  by
  obtain rfl | hs := Finset.eq_empty_or_nonempty s
  · simp [ht]
  · exact sum_le hs hF
#align padic_norm.sum_le' padicNorm.sum_le'

end padicNorm

