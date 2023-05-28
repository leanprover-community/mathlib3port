/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.nat.multiplicity
! leanprover-community/mathlib commit 290a7ba01fbcab1b64757bdaa270d28f4dcede35
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Intervals
import Mathbin.Algebra.GeomSum
import Mathbin.Data.Nat.Bitwise
import Mathbin.Data.Nat.Log
import Mathbin.Data.Nat.Parity
import Mathbin.Data.Nat.Prime
import Mathbin.RingTheory.Multiplicity

/-!
# Natural number multiplicity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains lemmas about the multiplicity function (the maximum prime power dividing a
number) when applied to naturals, in particular calculating it for factorials and binomial
coefficients.

## Multiplicity calculations

* `nat.multiplicity_factorial`: Legendre's Theorem. The multiplicity of `p` in `n!` is
  `n/p + ... + n/p^b` for any `b` such that `n/p^(b + 1) = 0`.
* `nat.multiplicity_factorial_mul`: The multiplicity of `p` in `(p * n)!` is `n` more than that of
  `n!`.
* `nat.multiplicity_choose`: The multiplicity of `p` in `n.choose k` is the number of carries when
  `k` and`n - k` are added in base `p`.

## Other declarations

* `nat.multiplicity_eq_card_pow_dvd`: The multiplicity of `m` in `n` is the number of positive
  natural numbers `i` such that `m ^ i` divides `n`.
* `nat.multiplicity_two_factorial_lt`: The multiplicity of `2` in `n!` is strictly less than `n`.
* `nat.prime.multiplicity_something`: Specialization of `multiplicity.something` to a prime in the
  naturals. Avoids having to provide `p ≠ 1` and other trivialities, along with translating between
  `prime` and `nat.prime`.

## Tags

Legendre, p-adic
-/


open Finset Nat multiplicity

open BigOperators Nat

namespace Nat

/- warning: nat.multiplicity_eq_card_pow_dvd -> Nat.multiplicity_eq_card_pow_dvd is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {b : Nat}, (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) -> (LT.lt.{0} Nat Nat.hasLt (Nat.log m n) b) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) m n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) (Finset.card.{0} Nat (Finset.filter.{0} Nat (fun (i : Nat) => Dvd.Dvd.{0} Nat Nat.hasDvd (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) m i) n) (fun (a : Nat) => Nat.decidableDvd (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) m a) n) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b)))))
but is expected to have type
  forall {m : Nat} {n : Nat} {b : Nat}, (Ne.{1} Nat m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) -> (LT.lt.{0} Nat instLTNat (Nat.log m n) b) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) m n) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) (Finset.card.{0} Nat (Finset.filter.{0} Nat (fun (i : Nat) => Dvd.dvd.{0} Nat Nat.instDvdNat (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) m i) n) (fun (a : Nat) => Nat.decidable_dvd (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) m a) n) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b)))))
Case conversion may be inaccurate. Consider using '#align nat.multiplicity_eq_card_pow_dvd Nat.multiplicity_eq_card_pow_dvdₓ'. -/
/-- The multiplicity of `m` in `n` is the number of positive natural numbers `i` such that `m ^ i`
divides `n`. This set is expressed by filtering `Ico 1 b` where `b` is any bound greater than
`log m n`. -/
theorem multiplicity_eq_card_pow_dvd {m n b : ℕ} (hm : m ≠ 1) (hn : 0 < n) (hb : log m n < b) :
    multiplicity m n = ↑((Finset.Ico 1 b).filterₓ fun i => m ^ i ∣ n).card :=
  calc
    multiplicity m n = ↑(Ico 1 <| (multiplicity m n).get (finite_nat_iff.2 ⟨hm, hn⟩) + 1).card := by
      simp
    _ = ↑((Finset.Ico 1 b).filterₓ fun i => m ^ i ∣ n).card :=
      congr_arg coe <|
        congr_arg card <|
          Finset.ext fun i =>
            by
            rw [mem_filter, mem_Ico, mem_Ico, lt_succ_iff, ← @PartENat.coe_le_coe i,
              PartENat.natCast_get, ← pow_dvd_iff_le_multiplicity, and_right_comm]
            refine' (and_iff_left_of_imp fun h => lt_of_le_of_lt _ hb).symm
            cases m
            · rw [zero_pow, zero_dvd_iff] at h
              exacts[(hn.ne' h.2).elim, h.1]
            exact
              le_log_of_pow_le (one_lt_iff_ne_zero_and_ne_one.2 ⟨m.succ_ne_zero, hm⟩)
                (le_of_dvd hn h.2)
    
#align nat.multiplicity_eq_card_pow_dvd Nat.multiplicity_eq_card_pow_dvd

namespace Prime

/- warning: nat.prime.multiplicity_one -> Nat.Prime.multiplicity_one is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} PartENat 0 (OfNat.mk.{0} PartENat 0 (Zero.zero.{0} PartENat PartENat.hasZero))))
but is expected to have type
  forall {p : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} PartENat 0 (Zero.toOfNat0.{0} PartENat PartENat.instZeroPartENat)))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_one Nat.Prime.multiplicity_oneₓ'. -/
theorem multiplicity_one {p : ℕ} (hp : p.Prime) : multiplicity p 1 = 0 :=
  multiplicity.one_right hp.Prime.not_unit
#align nat.prime.multiplicity_one Nat.Prime.multiplicity_one

/- warning: nat.prime.multiplicity_mul -> Nat.Prime.multiplicity_mul is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {m : Nat} {n : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) m n)) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.hasAdd) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p m) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p n)))
but is expected to have type
  forall {p : Nat} {m : Nat} {n : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) m n)) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.instAddPartENat) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p m) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p n)))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_mul Nat.Prime.multiplicity_mulₓ'. -/
theorem multiplicity_mul {p m n : ℕ} (hp : p.Prime) :
    multiplicity p (m * n) = multiplicity p m + multiplicity p n :=
  multiplicity.mul hp.Prime
#align nat.prime.multiplicity_mul Nat.Prime.multiplicity_mul

/- warning: nat.prime.multiplicity_pow -> Nat.Prime.multiplicity_pow is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {m : Nat} {n : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) m n)) (SMul.smul.{0, 0} Nat PartENat (AddMonoid.SMul.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))) n (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p m)))
but is expected to have type
  forall {p : Nat} {m : Nat} {n : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) m n)) (HSMul.hSMul.{0, 0, 0} Nat PartENat PartENat (instHSMul.{0, 0} Nat PartENat (AddMonoid.SMul.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) n (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p m)))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_pow Nat.Prime.multiplicity_powₓ'. -/
theorem multiplicity_pow {p m n : ℕ} (hp : p.Prime) :
    multiplicity p (m ^ n) = n • multiplicity p m :=
  multiplicity.pow hp.Prime
#align nat.prime.multiplicity_pow Nat.Prime.multiplicity_pow

/- warning: nat.prime.multiplicity_self -> Nat.Prime.multiplicity_self is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p p) (OfNat.ofNat.{0} PartENat 1 (OfNat.mk.{0} PartENat 1 (One.one.{0} PartENat PartENat.hasOne))))
but is expected to have type
  forall {p : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p p) (OfNat.ofNat.{0} PartENat 1 (One.toOfNat1.{0} PartENat PartENat.instOnePartENat)))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_self Nat.Prime.multiplicity_selfₓ'. -/
theorem multiplicity_self {p : ℕ} (hp : p.Prime) : multiplicity p p = 1 :=
  multiplicity_self hp.Prime.not_unit hp.NeZero
#align nat.prime.multiplicity_self Nat.Prime.multiplicity_self

/- warning: nat.prime.multiplicity_pow_self -> Nat.Prime.multiplicity_pow_self is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {n : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) n))
but is expected to have type
  forall {p : Nat} {n : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n)) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) n))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_pow_self Nat.Prime.multiplicity_pow_selfₓ'. -/
theorem multiplicity_pow_self {p n : ℕ} (hp : p.Prime) : multiplicity p (p ^ n) = n :=
  multiplicity_pow_self hp.NeZero hp.Prime.not_unit n
#align nat.prime.multiplicity_pow_self Nat.Prime.multiplicity_pow_self

/- warning: nat.prime.multiplicity_factorial -> Nat.Prime.multiplicity_factorial is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, (Nat.Prime p) -> (forall {n : Nat} {b : Nat}, (LT.lt.{0} Nat Nat.hasLt (Nat.log p n) b) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (Nat.factorial n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) (Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) n (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i))))))
but is expected to have type
  forall {p : Nat}, (Nat.Prime p) -> (forall {n : Nat} {b : Nat}, (LT.lt.{0} Nat instLTNat (Nat.log p n) b) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (Nat.factorial n)) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) (Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) n (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i))))))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_factorial Nat.Prime.multiplicity_factorialₓ'. -/
/-- **Legendre's Theorem**

The multiplicity of a prime in `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any bound greater than `log p n`. -/
theorem multiplicity_factorial {p : ℕ} (hp : p.Prime) :
    ∀ {n b : ℕ}, log p n < b → multiplicity p n ! = (∑ i in Ico 1 b, n / p ^ i : ℕ)
  | 0, b, hb => by simp [Ico, hp.multiplicity_one]
  | n + 1, b, hb =>
    calc
      multiplicity p (n + 1)! = multiplicity p n ! + multiplicity p (n + 1) := by
        rw [factorial_succ, hp.multiplicity_mul, add_comm]
      _ =
          (∑ i in Ico 1 b, n / p ^ i : ℕ) +
            ((Finset.Ico 1 b).filterₓ fun i => p ^ i ∣ n + 1).card :=
        by
        rw [multiplicity_factorial ((log_mono_right <| le_succ _).trans_lt hb), ←
          multiplicity_eq_card_pow_dvd hp.ne_one (succ_pos _) hb]
      _ = (∑ i in Ico 1 b, n / p ^ i + if p ^ i ∣ n + 1 then 1 else 0 : ℕ) := by
        rw [sum_add_distrib, sum_boole]; simp
      _ = (∑ i in Ico 1 b, (n + 1) / p ^ i : ℕ) :=
        congr_arg coe <| Finset.sum_congr rfl fun _ _ => (succ_div _ _).symm
      
#align nat.prime.multiplicity_factorial Nat.Prime.multiplicity_factorial

/- warning: nat.prime.multiplicity_factorial_mul_succ -> Nat.Prime.multiplicity_factorial_mul_succ is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {p : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (Nat.factorial (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.hasAdd) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.hasAdd) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (Nat.factorial (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) p n))) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (OfNat.ofNat.{0} PartENat 1 (OfNat.mk.{0} PartENat 1 (One.one.{0} PartENat PartENat.hasOne)))))
but is expected to have type
  forall {n : Nat} {p : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (Nat.factorial (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.instAddPartENat) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.instAddPartENat) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (Nat.factorial (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) p n))) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} PartENat 1 (One.toOfNat1.{0} PartENat PartENat.instOnePartENat))))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_factorial_mul_succ Nat.Prime.multiplicity_factorial_mul_succₓ'. -/
/-- The multiplicity of `p` in `(p * (n + 1))!` is one more than the sum
  of the multiplicities of `p` in `(p * n)!` and `n + 1`. -/
theorem multiplicity_factorial_mul_succ {n p : ℕ} (hp : p.Prime) :
    multiplicity p (p * (n + 1))! = multiplicity p (p * n)! + multiplicity p (n + 1) + 1 :=
  by
  have hp' := hp.prime
  have h0 : 2 ≤ p := hp.two_le
  have h1 : 1 ≤ p * n + 1 := Nat.le_add_left _ _
  have h2 : p * n + 1 ≤ p * (n + 1); linarith
  have h3 : p * n + 1 ≤ p * (n + 1) + 1; linarith
  have hm : multiplicity p (p * n)! ≠ ⊤ :=
    by
    rw [Ne.def, eq_top_iff_not_finite, Classical.not_not, finite_nat_iff]
    exact ⟨hp.ne_one, factorial_pos _⟩
  revert hm
  have h4 : ∀ m ∈ Ico (p * n + 1) (p * (n + 1)), multiplicity p m = 0 :=
    by
    intro m hm
    rw [multiplicity_eq_zero, ← not_dvd_iff_between_consec_multiples _ hp.pos]
    rw [mem_Ico] at hm
    exact ⟨n, lt_of_succ_le hm.1, hm.2⟩
  simp_rw [← prod_Ico_id_eq_factorial, multiplicity.Finset.prod hp', ← sum_Ico_consecutive _ h1 h3,
    add_assoc]
  intro h
  rw [PartENat.add_left_cancel_iff h, sum_Ico_succ_top h2, multiplicity.mul hp',
    hp.multiplicity_self, sum_congr rfl h4, sum_const_zero, zero_add, add_comm (1 : PartENat)]
#align nat.prime.multiplicity_factorial_mul_succ Nat.Prime.multiplicity_factorial_mul_succ

/- warning: nat.prime.multiplicity_factorial_mul -> Nat.Prime.multiplicity_factorial_mul is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {p : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (Nat.factorial (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) p n))) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.hasAdd) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (Nat.factorial n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) n)))
but is expected to have type
  forall {n : Nat} {p : Nat}, (Nat.Prime p) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (Nat.factorial (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) p n))) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.instAddPartENat) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (Nat.factorial n)) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) n)))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_factorial_mul Nat.Prime.multiplicity_factorial_mulₓ'. -/
/-- The multiplicity of `p` in `(p * n)!` is `n` more than that of `n!`. -/
theorem multiplicity_factorial_mul {n p : ℕ} (hp : p.Prime) :
    multiplicity p (p * n)! = multiplicity p n ! + n :=
  by
  induction' n with n ih
  · simp
  · simp only [succ_eq_add_one, multiplicity.mul, hp, hp.prime, ih, multiplicity_factorial_mul_succ,
      ← add_assoc, Nat.cast_one, Nat.cast_add, factorial_succ]
    congr 1
    rw [add_comm, add_assoc]
#align nat.prime.multiplicity_factorial_mul Nat.Prime.multiplicity_factorial_mul

/- warning: nat.prime.pow_dvd_factorial_iff -> Nat.Prime.pow_dvd_factorial_iff is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {n : Nat} {r : Nat} {b : Nat}, (Nat.Prime p) -> (LT.lt.{0} Nat Nat.hasLt (Nat.log p n) b) -> (Iff (Dvd.Dvd.{0} Nat Nat.hasDvd (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p r) (Nat.factorial n)) (LE.le.{0} Nat Nat.hasLe r (Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) n (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i)))))
but is expected to have type
  forall {p : Nat} {n : Nat} {r : Nat} {b : Nat}, (Nat.Prime p) -> (LT.lt.{0} Nat instLTNat (Nat.log p n) b) -> (Iff (Dvd.dvd.{0} Nat Nat.instDvdNat (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p r) (Nat.factorial n)) (LE.le.{0} Nat instLENat r (Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) n (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i)))))
Case conversion may be inaccurate. Consider using '#align nat.prime.pow_dvd_factorial_iff Nat.Prime.pow_dvd_factorial_iffₓ'. -/
/-- A prime power divides `n!` iff it is at most the sum of the quotients `n / p ^ i`.
  This sum is expressed over the set `Ico 1 b` where `b` is any bound greater than `log p n` -/
theorem pow_dvd_factorial_iff {p : ℕ} {n r b : ℕ} (hp : p.Prime) (hbn : log p n < b) :
    p ^ r ∣ n ! ↔ r ≤ ∑ i in Ico 1 b, n / p ^ i := by
  rw [← PartENat.coe_le_coe, ← hp.multiplicity_factorial hbn, ← pow_dvd_iff_le_multiplicity]
#align nat.prime.pow_dvd_factorial_iff Nat.Prime.pow_dvd_factorial_iff

/- warning: nat.prime.multiplicity_factorial_le_div_pred -> Nat.Prime.multiplicity_factorial_le_div_pred is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, (Nat.Prime p) -> (forall (n : Nat), LE.le.{0} PartENat PartENat.hasLe (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (Nat.factorial n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) n (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) p (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {p : Nat}, (Nat.Prime p) -> (forall (n : Nat), LE.le.{0} PartENat PartENat.instLEPartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (Nat.factorial n)) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) n (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) p (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_factorial_le_div_pred Nat.Prime.multiplicity_factorial_le_div_predₓ'. -/
theorem multiplicity_factorial_le_div_pred {p : ℕ} (hp : p.Prime) (n : ℕ) :
    multiplicity p n ! ≤ (n / (p - 1) : ℕ) :=
  by
  rw [hp.multiplicity_factorial (lt_succ_self _), PartENat.coe_le_coe]
  exact Nat.geom_sum_Ico_le hp.two_le _ _
#align nat.prime.multiplicity_factorial_le_div_pred Nat.Prime.multiplicity_factorial_le_div_pred

/- warning: nat.prime.multiplicity_choose_aux -> Nat.Prime.multiplicity_choose_aux is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {n : Nat} {b : Nat} {k : Nat}, (Nat.Prime p) -> (LE.le.{0} Nat Nat.hasLe k n) -> (Eq.{1} Nat (Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) n (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i))) (Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n k) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i)))) (Finset.card.{0} Nat (Finset.filter.{0} Nat (fun (i : Nat) => LE.le.{0} Nat Nat.hasLe (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i)) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n k) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i)))) (fun (a : Nat) => Nat.decidableLe (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p a) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p a)) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n k) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p a)))) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b)))))
but is expected to have type
  forall {p : Nat} {n : Nat} {b : Nat} {k : Nat}, (Nat.Prime p) -> (LE.le.{0} Nat instLENat k n) -> (Eq.{1} Nat (Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) n (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i))) (Finset.sum.{0, 0} Nat Nat Nat.addCommMonoid (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b) (fun (i : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n k) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i)))) (Finset.card.{0} Nat (Finset.filter.{0} Nat (fun (i : Nat) => LE.le.{0} Nat instLENat (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i)) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n k) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i)))) (fun (a : Nat) => Nat.decLe (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p a) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p a)) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n k) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p a)))) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b)))))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_choose_aux Nat.Prime.multiplicity_choose_auxₓ'. -/
theorem multiplicity_choose_aux {p n b k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    (∑ i in Finset.Ico 1 b, n / p ^ i) =
      ((∑ i in Finset.Ico 1 b, k / p ^ i) + ∑ i in Finset.Ico 1 b, (n - k) / p ^ i) +
        ((Finset.Ico 1 b).filterₓ fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card :=
  calc
    (∑ i in Finset.Ico 1 b, n / p ^ i) = ∑ i in Finset.Ico 1 b, (k + (n - k)) / p ^ i := by
      simp only [add_tsub_cancel_of_le hkn]
    _ =
        ∑ i in Finset.Ico 1 b,
          k / p ^ i + (n - k) / p ^ i + if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0 :=
      by simp only [Nat.add_div (pow_pos hp.pos _)]
    _ = _ := by simp [sum_add_distrib, sum_boole]
    
#align nat.prime.multiplicity_choose_aux Nat.Prime.multiplicity_choose_aux

/- warning: nat.prime.multiplicity_choose -> Nat.Prime.multiplicity_choose is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {n : Nat} {k : Nat} {b : Nat}, (Nat.Prime p) -> (LE.le.{0} Nat Nat.hasLe k n) -> (LT.lt.{0} Nat Nat.hasLt (Nat.log p n) b) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (Nat.choose n k)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) (Finset.card.{0} Nat (Finset.filter.{0} Nat (fun (i : Nat) => LE.le.{0} Nat Nat.hasLe (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i)) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n k) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p i)))) (fun (a : Nat) => Nat.decidableLe (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p a) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p a)) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n k) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p a)))) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b)))))
but is expected to have type
  forall {p : Nat} {n : Nat} {k : Nat} {b : Nat}, (Nat.Prime p) -> (LE.le.{0} Nat instLENat k n) -> (LT.lt.{0} Nat instLTNat (Nat.log p n) b) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (Nat.choose n k)) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) (Finset.card.{0} Nat (Finset.filter.{0} Nat (fun (i : Nat) => LE.le.{0} Nat instLENat (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i)) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n k) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p i)))) (fun (a : Nat) => Nat.decLe (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p a) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p a)) (HMod.hMod.{0, 0, 0} Nat Nat Nat (instHMod.{0} Nat Nat.instModNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n k) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p a)))) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) b)))))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_choose Nat.Prime.multiplicity_chooseₓ'. -/
/-- The multiplicity of `p` in `choose n k` is the number of carries when `k` and `n - k`
  are added in base `p`. The set is expressed by filtering `Ico 1 b` where `b`
  is any bound greater than `log p n`. -/
theorem multiplicity_choose {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hnb : log p n < b) :
    multiplicity p (choose n k) =
      ((Ico 1 b).filterₓ fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card :=
  have h₁ :
    multiplicity p (choose n k) + multiplicity p (k ! * (n - k)!) =
      ((Finset.Ico 1 b).filterₓ fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i).card +
        multiplicity p (k ! * (n - k)!) :=
    by
    rw [← hp.multiplicity_mul, ← mul_assoc, choose_mul_factorial_mul_factorial hkn,
      hp.multiplicity_factorial hnb, hp.multiplicity_mul,
      hp.multiplicity_factorial ((log_mono_right hkn).trans_lt hnb),
      hp.multiplicity_factorial (lt_of_le_of_lt (log_mono_right tsub_le_self) hnb),
      multiplicity_choose_aux hp hkn]
    simp [add_comm]
  (PartENat.add_right_cancel_iff
        (PartENat.ne_top_iff_dom.2 <|
          finite_nat_iff.2
            ⟨ne_of_gt hp.one_lt, mul_pos (factorial_pos k) (factorial_pos (n - k))⟩)).1
    h₁
#align nat.prime.multiplicity_choose Nat.Prime.multiplicity_choose

/- warning: nat.prime.multiplicity_le_multiplicity_choose_add -> Nat.Prime.multiplicity_le_multiplicity_choose_add is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, (Nat.Prime p) -> (forall (n : Nat) (k : Nat), LE.le.{0} PartENat PartENat.hasLe (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p n) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.hasAdd) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (Nat.choose n k)) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p k)))
but is expected to have type
  forall {p : Nat}, (Nat.Prime p) -> (forall (n : Nat) (k : Nat), LE.le.{0} PartENat PartENat.instLEPartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p n) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.instAddPartENat) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (Nat.choose n k)) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p k)))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_le_multiplicity_choose_add Nat.Prime.multiplicity_le_multiplicity_choose_addₓ'. -/
/-- A lower bound on the multiplicity of `p` in `choose n k`. -/
theorem multiplicity_le_multiplicity_choose_add {p : ℕ} (hp : p.Prime) :
    ∀ n k : ℕ, multiplicity p n ≤ multiplicity p (choose n k) + multiplicity p k
  | _, 0 => by simp
  | 0, _ + 1 => by simp
  | n + 1, k + 1 => by
    rw [← hp.multiplicity_mul]
    refine' multiplicity_le_multiplicity_of_dvd_right _
    rw [← succ_mul_choose_eq]
    exact dvd_mul_right _ _
#align nat.prime.multiplicity_le_multiplicity_choose_add Nat.Prime.multiplicity_le_multiplicity_choose_add

variable {p n k : ℕ}

/- warning: nat.prime.multiplicity_choose_prime_pow_add_multiplicity -> Nat.Prime.multiplicity_choose_prime_pow_add_multiplicity is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {n : Nat} {k : Nat}, (Nat.Prime p) -> (LE.le.{0} Nat Nat.hasLe k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p n)) -> (Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} PartENat (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.hasAdd) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (Nat.choose (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p n) k)) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p k)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) n))
but is expected to have type
  forall {p : Nat} {n : Nat} {k : Nat}, (Nat.Prime p) -> (LE.le.{0} Nat instLENat k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n)) -> (Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} PartENat (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.instAddPartENat) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (Nat.choose (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n) k)) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p k)) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) n))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_choose_prime_pow_add_multiplicity Nat.Prime.multiplicity_choose_prime_pow_add_multiplicityₓ'. -/
theorem multiplicity_choose_prime_pow_add_multiplicity (hp : p.Prime) (hkn : k ≤ p ^ n)
    (hk0 : k ≠ 0) : multiplicity p (choose (p ^ n) k) + multiplicity p k = n :=
  le_antisymm
    (by
      have hdisj :
        Disjoint ((Ico 1 n.succ).filterₓ fun i => p ^ i ≤ k % p ^ i + (p ^ n - k) % p ^ i)
          ((Ico 1 n.succ).filterₓ fun i => p ^ i ∣ k) :=
        by
        simp (config := { contextual := true }) [disjoint_right, *, dvd_iff_mod_eq_zero,
          Nat.mod_lt _ (pow_pos hp.pos _)]
      rw [multiplicity_choose hp hkn (lt_succ_self _),
        multiplicity_eq_card_pow_dvd (ne_of_gt hp.one_lt) hk0.bot_lt
          (lt_succ_of_le (log_mono_right hkn)),
        ← Nat.cast_add, PartENat.coe_le_coe, log_pow hp.one_lt, ← card_disjoint_union hdisj,
        filter_union_right]
      have filter_le_Ico := (Ico 1 n.succ).card_filter_le _
      rwa [card_Ico 1 n.succ] at filter_le_Ico)
    (by rw [← hp.multiplicity_pow_self] <;> exact multiplicity_le_multiplicity_choose_add hp _ _)
#align nat.prime.multiplicity_choose_prime_pow_add_multiplicity Nat.Prime.multiplicity_choose_prime_pow_add_multiplicity

/- warning: nat.prime.multiplicity_choose_prime_pow -> Nat.Prime.multiplicity_choose_prime_pow is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {n : Nat} {k : Nat} (hp : Nat.Prime p), (LE.le.{0} Nat Nat.hasLe k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p n)) -> (forall (hk0 : Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))), Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p (Nat.choose (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p n) k)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (Part.get.{0} Nat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p k) (Iff.mpr (multiplicity.Finite.{0} Nat Nat.monoid p k) (And (Ne.{1} Nat p (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) k)) (multiplicity.finite_nat_iff p k) (And.intro (Ne.{1} Nat p (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) k) (Nat.Prime.ne_one p hp) (Ne.bot_lt.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) Nat.orderBot k hk0)))))))
but is expected to have type
  forall {p : Nat} {n : Nat} {k : Nat} (hp : Nat.Prime p), (LE.le.{0} Nat instLENat k (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n)) -> (forall (hk0 : Ne.{1} Nat k (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))), Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p (Nat.choose (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n) k)) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (Part.get.{0} Nat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p k) (Iff.mpr (multiplicity.Finite.{0} Nat Nat.monoid p k) (And (Ne.{1} Nat p (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) k)) (multiplicity.finite_nat_iff p k) (And.intro (Ne.{1} Nat p (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) k) (Nat.Prime.ne_one p hp) (Ne.bot_lt.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring) Nat.orderBot k hk0)))))))
Case conversion may be inaccurate. Consider using '#align nat.prime.multiplicity_choose_prime_pow Nat.Prime.multiplicity_choose_prime_powₓ'. -/
theorem multiplicity_choose_prime_pow {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0) :
    multiplicity p (choose (p ^ n) k) =
      ↑(n - (multiplicity p k).get (finite_nat_iff.2 ⟨hp.ne_one, hk0.bot_lt⟩)) :=
  PartENat.eq_natCast_sub_of_add_eq_natCast <|
    multiplicity_choose_prime_pow_add_multiplicity hp hkn hk0
#align nat.prime.multiplicity_choose_prime_pow Nat.Prime.multiplicity_choose_prime_pow

#print Nat.Prime.dvd_choose_pow /-
theorem dvd_choose_pow (hp : Prime p) (hk : k ≠ 0) (hkp : k ≠ p ^ n) : p ∣ (p ^ n).choose k :=
  by
  obtain hkp | hkp := hkp.symm.lt_or_lt
  · simp [choose_eq_zero_of_lt hkp]
  refine' multiplicity_ne_zero.1 fun h => hkp.not_le <| Nat.le_of_dvd hk.bot_lt _
  have H := hp.multiplicity_choose_prime_pow_add_multiplicity hkp.le hk
  rw [h, zero_add, eq_coe_iff] at H
  exact H.1
#align nat.prime.dvd_choose_pow Nat.Prime.dvd_choose_pow
-/

#print Nat.Prime.dvd_choose_pow_iff /-
theorem dvd_choose_pow_iff (hp : Prime p) : p ∣ (p ^ n).choose k ↔ k ≠ 0 ∧ k ≠ p ^ n := by
  refine' ⟨fun h => ⟨_, _⟩, fun h => dvd_choose_pow hp h.1 h.2⟩ <;> rintro rfl <;>
    simpa [hp.ne_one] using h
#align nat.prime.dvd_choose_pow_iff Nat.Prime.dvd_choose_pow_iff
-/

end Prime

/- warning: nat.multiplicity_two_factorial_lt -> Nat.multiplicity_two_factorial_lt is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (LT.lt.{0} PartENat (Preorder.toHasLt.{0} PartENat (PartialOrder.toPreorder.{0} PartENat PartENat.partialOrder)) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Nat.factorial n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) n))
but is expected to have type
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (LT.lt.{0} PartENat (Preorder.toLT.{0} PartENat (PartialOrder.toPreorder.{0} PartENat PartENat.partialOrder)) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) (Nat.factorial n)) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) n))
Case conversion may be inaccurate. Consider using '#align nat.multiplicity_two_factorial_lt Nat.multiplicity_two_factorial_ltₓ'. -/
theorem multiplicity_two_factorial_lt : ∀ {n : ℕ} (h : n ≠ 0), multiplicity 2 n ! < n :=
  by
  have h2 := prime_two.prime
  refine' binary_rec _ _
  · contradiction
  · intro b n ih h
    by_cases hn : n = 0
    · subst hn; simp at h; simp [h, one_right h2.not_unit]
    have : multiplicity 2 (2 * n)! < (2 * n : ℕ) :=
      by
      rw [prime_two.multiplicity_factorial_mul]
      refine' (PartENat.add_lt_add_right (ih hn) (PartENat.natCast_ne_top _)).trans_le _
      rw [two_mul]; norm_cast
    cases b
    · simpa [bit0_eq_two_mul n]
    · suffices multiplicity 2 (2 * n + 1) + multiplicity 2 (2 * n)! < ↑(2 * n) + 1 by
        simpa [succ_eq_add_one, multiplicity.mul, h2, prime_two, Nat.bit1_eq_succ_bit0,
          bit0_eq_two_mul n]
      rw [multiplicity_eq_zero.2 (two_not_dvd_two_mul_add_one n), zero_add]
      refine' this.trans _; exact_mod_cast lt_succ_self _
#align nat.multiplicity_two_factorial_lt Nat.multiplicity_two_factorial_lt

end Nat

