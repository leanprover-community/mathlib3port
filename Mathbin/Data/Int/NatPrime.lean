/-
Copyright (c) 2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Bryan Gin-ge Chen

! This file was ported from Lean 3 source module data.int.nat_prime
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Prime

/-!
# Lemmas about nat.prime using `int`s

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Nat

namespace Int

#print Int.not_prime_of_int_mul /-
theorem not_prime_of_int_mul {a b : ℤ} {c : ℕ} (ha : 1 < a.natAbs) (hb : 1 < b.natAbs)
    (hc : a * b = (c : ℤ)) : ¬Nat.Prime c :=
  not_prime_mul' (natAbs_mul_natAbs_eq hc) ha hb
#align int.not_prime_of_int_mul Int.not_prime_of_int_mul
-/

/- warning: int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul -> Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, (Nat.Prime p) -> (forall {m : Int} {n : Int} {k : Nat} {l : Nat}, (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p k)) m) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p l)) n) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k l) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) m n)) -> (Or (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) m) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) l (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) n)))
but is expected to have type
  forall {p : Nat}, (Nat.Prime p) -> (forall {m : Int} {n : Int} {k : Nat} {l : Nat}, (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p k)) m) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p l)) n) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k l) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) m n)) -> (Or (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) m) (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) l (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) n)))
Case conversion may be inaccurate. Consider using '#align int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mulₓ'. -/
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : Nat.Prime p) {m n : ℤ} {k l : ℕ}
    (hpm : ↑(p ^ k) ∣ m) (hpn : ↑(p ^ l) ∣ n) (hpmn : ↑(p ^ (k + l + 1)) ∣ m * n) :
    ↑(p ^ (k + 1)) ∣ m ∨ ↑(p ^ (l + 1)) ∣ n :=
  have hpm' : p ^ k ∣ m.natAbs := Int.coe_nat_dvd.1 <| Int.dvd_natAbs.2 hpm
  have hpn' : p ^ l ∣ n.natAbs := Int.coe_nat_dvd.1 <| Int.dvd_natAbs.2 hpn
  have hpmn' : p ^ (k + l + 1) ∣ m.natAbs * n.natAbs := by
    rw [← Int.natAbs_mul] <;> apply Int.coe_nat_dvd.1 <| Int.dvd_natAbs.2 hpmn
  let hsd := Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul p_prime hpm' hpn' hpmn'
  hsd.elim (fun hsd1 => Or.inl (by apply Int.dvd_natAbs.1; apply Int.coe_nat_dvd.2 hsd1))
    fun hsd2 => Or.inr (by apply Int.dvd_natAbs.1; apply Int.coe_nat_dvd.2 hsd2)
#align int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul Int.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul

/- warning: int.prime.dvd_nat_abs_of_coe_dvd_sq -> Int.Prime.dvd_natAbs_of_coe_dvd_sq is a dubious translation:
lean 3 declaration is
  forall {p : Nat}, (Nat.Prime p) -> (forall (k : Int), (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) k (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) -> (Dvd.Dvd.{0} Nat Nat.hasDvd p (Int.natAbs k)))
but is expected to have type
  forall {p : Nat}, (Nat.Prime p) -> (forall (k : Int), (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt p) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.instMonoidInt)) k (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) -> (Dvd.dvd.{0} Nat Nat.instDvdNat p (Int.natAbs k)))
Case conversion may be inaccurate. Consider using '#align int.prime.dvd_nat_abs_of_coe_dvd_sq Int.Prime.dvd_natAbs_of_coe_dvd_sqₓ'. -/
theorem Prime.dvd_natAbs_of_coe_dvd_sq {p : ℕ} (hp : p.Prime) (k : ℤ) (h : ↑p ∣ k ^ 2) :
    p ∣ k.natAbs := by
  apply @Nat.Prime.dvd_of_dvd_pow _ _ 2 hp
  rwa [sq, ← nat_abs_mul, ← coe_nat_dvd_left, ← sq]
#align int.prime.dvd_nat_abs_of_coe_dvd_sq Int.Prime.dvd_natAbs_of_coe_dvd_sq

end Int

