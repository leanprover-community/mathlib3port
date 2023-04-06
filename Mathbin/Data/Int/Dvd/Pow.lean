/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module data.int.dvd.pow
! leanprover-community/mathlib commit e8638a0fcaf73e4500469f368ef9494e495099b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Dvd.Basic
import Mathbin.Data.Nat.Pow

/-!
# Basic lemmas about the divisibility relation in `ℤ` involving powers.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Nat

namespace Int

/- warning: int.sign_pow_bit1 -> Int.sign_pow_bit1 is a dubious translation:
lean 3 declaration is
  forall (k : Nat) (n : Int), Eq.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Int.sign n) (bit1.{0} Nat Nat.hasOne Nat.hasAdd k)) (Int.sign n)
but is expected to have type
  forall (k : Nat) (n : Int), Eq.{1} Int (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat (Int.sign n) (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat k)) (Int.sign n)
Case conversion may be inaccurate. Consider using '#align int.sign_pow_bit1 Int.sign_pow_bit1ₓ'. -/
@[simp]
theorem sign_pow_bit1 (k : ℕ) : ∀ n : ℤ, n.sign ^ bit1 k = n.sign
  | (n + 1 : ℕ) => one_pow (bit1 k)
  | 0 => zero_pow (Nat.zero_lt_bit1 k)
  | -[n+1] => (neg_pow_bit1 1 k).trans (congr_arg (fun x => -x) (one_pow (bit1 k)))
#align int.sign_pow_bit1 Int.sign_pow_bit1

/- warning: int.pow_dvd_of_le_of_pow_dvd -> Int.pow_dvd_of_le_of_pow_dvd is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {m : Nat} {n : Nat} {k : Int}, (LE.le.{0} Nat Nat.hasLe m n) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p n)) k) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p m)) k)
but is expected to have type
  forall {p : Nat} {m : Nat} {n : Nat} {k : Int}, (LE.le.{0} Nat instLENat m n) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n)) k) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p m)) k)
Case conversion may be inaccurate. Consider using '#align int.pow_dvd_of_le_of_pow_dvd Int.pow_dvd_of_le_of_pow_dvdₓ'. -/
--TODO: Do we really need this lemma?
theorem pow_dvd_of_le_of_pow_dvd {p m n : ℕ} {k : ℤ} (hmn : m ≤ n) (hdiv : ↑(p ^ n) ∣ k) :
    ↑(p ^ m) ∣ k :=
  (pow_dvd_pow _ hmn).natCast.trans hdiv
#align int.pow_dvd_of_le_of_pow_dvd Int.pow_dvd_of_le_of_pow_dvd

/- warning: int.dvd_of_pow_dvd -> Int.dvd_of_pow_dvd is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {k : Nat} {m : Int}, (LE.le.{0} Nat Nat.hasLe (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) k) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p k)) m) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) m)
but is expected to have type
  forall {p : Nat} {k : Nat} {m : Int}, (LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) k) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p k)) m) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int instNatCastInt p) m)
Case conversion may be inaccurate. Consider using '#align int.dvd_of_pow_dvd Int.dvd_of_pow_dvdₓ'. -/
theorem dvd_of_pow_dvd {p k : ℕ} {m : ℤ} (hk : 1 ≤ k) (hpk : ↑(p ^ k) ∣ m) : ↑p ∣ m :=
  (dvd_pow_self _ <| pos_iff_ne_zero.1 hk).natCast.trans hpk
#align int.dvd_of_pow_dvd Int.dvd_of_pow_dvd

end Int

