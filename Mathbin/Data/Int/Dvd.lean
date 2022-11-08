/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathbin.Data.Int.Order
import Mathbin.Data.Nat.Cast
import Mathbin.Data.Nat.Pow

/-!
# Basic lemmas about the divisibility relation in `ℤ`.
-/


open Nat

namespace Int

@[norm_cast]
theorem coe_nat_dvd {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
  ⟨fun ⟨a, ae⟩ =>
    m.eq_zero_or_pos.elim (fun m0 => by simp [m0] at ae <;> simp [ae, m0]) fun m0l => by
      cases' eq_coe_of_zero_le (@nonneg_of_mul_nonneg_right ℤ _ m a (by simp [ae.symm]) (by simpa using m0l)) with k e
      subst a
      exact ⟨k, Int.coe_nat_inj ae⟩,
    fun ⟨k, e⟩ => Dvd.intro k <| by rw [e, Int.coe_nat_mul]⟩

theorem coe_nat_dvd_left {n : ℕ} {z : ℤ} : (↑n : ℤ) ∣ z ↔ n ∣ z.natAbs := by
  rcases nat_abs_eq z with (eq | eq) <;> rw [Eq] <;> simp [coe_nat_dvd]

theorem coe_nat_dvd_right {n : ℕ} {z : ℤ} : z ∣ (↑n : ℤ) ↔ z.natAbs ∣ n := by
  rcases nat_abs_eq z with (eq | eq) <;> rw [Eq] <;> simp [coe_nat_dvd]

@[simp]
theorem sign_pow_bit1 (k : ℕ) : ∀ n : ℤ, n.sign ^ bit1 k = n.sign
  | (n + 1 : ℕ) => one_pow (bit1 k)
  | 0 => zero_pow (Nat.zero_lt_bit1 k)
  | -[n+1] => (neg_pow_bit1 1 k).trans (congr_arg (fun x => -x) (one_pow (bit1 k)))

/- warning: int.le_of_dvd -> Int.le_of_dvd is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (LT.lt.{0} Int Int.hasLt (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) b) -> (Dvd.Dvd.{0} Int (semigroupHasDvd.{0} Int Int.semigroup) a b) -> (LE.le.{0} Int Int.hasLe a b)
but is expected to have type
  forall {a : Int} {b : Int}, (LT.lt.{0} Int Int.instLTInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) b) -> (Dvd.dvd.{0} Int Int.instDvdInt a b) -> (LE.le.{0} Int Int.instLEInt a b)
Case conversion may be inaccurate. Consider using '#align int.le_of_dvd Int.le_of_dvdₓ'. -/
theorem le_of_dvd {a b : ℤ} (bpos : 0 < b) (H : a ∣ b) : a ≤ b :=
  match a, b, eq_succ_of_zero_lt bpos, H with
  | (m : ℕ), _, ⟨n, rfl⟩, H => coe_nat_le_coe_nat_of_le <| Nat.le_of_dvd n.succ_pos <| coe_nat_dvd.1 H
  | -[m+1], _, ⟨n, rfl⟩, _ => le_trans (le_of_lt <| neg_succ_lt_zero _) (coe_zero_le _)

/- warning: int.eq_one_of_dvd_one -> Int.eq_one_of_dvd_one is a dubious translation:
lean 3 declaration is
  forall {a : Int}, (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a) -> (Dvd.Dvd.{0} Int (semigroupHasDvd.{0} Int Int.semigroup) a (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) -> (Eq.{1} Int a (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {a : Int}, (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a) -> (Dvd.dvd.{0} Int Int.instDvdInt a (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) -> (Eq.{1} Int a (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align int.eq_one_of_dvd_one Int.eq_one_of_dvd_oneₓ'. -/
theorem eq_one_of_dvd_one {a : ℤ} (H : 0 ≤ a) (H' : a ∣ 1) : a = 1 :=
  match a, eq_coe_of_zero_le H, H' with
  | _, ⟨n, rfl⟩, H' => congr_arg coe <| Nat.eq_one_of_dvd_one <| coe_nat_dvd.1 H'

#print Int.eq_one_of_mul_eq_one_right /-
theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : 0 ≤ a) (H' : a * b = 1) : a = 1 :=
  eq_one_of_dvd_one H ⟨b, H'.symm⟩
-/

#print Int.eq_one_of_mul_eq_one_left /-
theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : 0 ≤ b) (H' : a * b = 1) : b = 1 :=
  eq_one_of_mul_eq_one_right H (by rw [mul_comm, H'])
-/

theorem of_nat_dvd_of_dvd_nat_abs {a : ℕ} : ∀ {z : ℤ} (haz : a ∣ z.natAbs), ↑a ∣ z
  | Int.ofNat _, haz => Int.coe_nat_dvd.2 haz
  | -[k+1], haz => by
    change ↑a ∣ -(k + 1 : ℤ)
    apply dvd_neg_of_dvd
    apply Int.coe_nat_dvd.2
    exact haz

theorem dvd_nat_abs_of_of_nat_dvd {a : ℕ} : ∀ {z : ℤ} (haz : ↑a ∣ z), a ∣ z.natAbs
  | Int.ofNat _, haz => Int.coe_nat_dvd.1 (Int.dvd_nat_abs.2 haz)
  | -[k+1], haz =>
    have haz' : (↑a : ℤ) ∣ (↑(k + 1) : ℤ) := dvd_of_dvd_neg haz
    Int.coe_nat_dvd.1 haz'

theorem pow_dvd_of_le_of_pow_dvd {p m n : ℕ} {k : ℤ} (hmn : m ≤ n) (hdiv : ↑(p ^ n) ∣ k) : ↑(p ^ m) ∣ k := by
  induction k
  · apply Int.coe_nat_dvd.2
    apply pow_dvd_of_le_of_pow_dvd hmn
    apply Int.coe_nat_dvd.1 hdiv
    
  change -[k+1] with -(↑(k + 1) : ℤ)
  apply dvd_neg_of_dvd
  apply Int.coe_nat_dvd.2
  apply pow_dvd_of_le_of_pow_dvd hmn
  apply Int.coe_nat_dvd.1
  apply dvd_of_dvd_neg
  exact hdiv

theorem dvd_of_pow_dvd {p k : ℕ} {m : ℤ} (hk : 1 ≤ k) (hpk : ↑(p ^ k) ∣ m) : ↑p ∣ m := by
  rw [← pow_one p] <;> exact pow_dvd_of_le_of_pow_dvd hk hpk

/- warning: int.dvd_antisymm -> Int.dvd_antisymm is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a) -> (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) b) -> (Dvd.Dvd.{0} Int (semigroupHasDvd.{0} Int Int.semigroup) a b) -> (Dvd.Dvd.{0} Int (semigroupHasDvd.{0} Int Int.semigroup) b a) -> (Eq.{1} Int a b)
but is expected to have type
  forall {a : Int} {b : Int}, (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a) -> (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) b) -> (Dvd.dvd.{0} Int Int.instDvdInt a b) -> (Dvd.dvd.{0} Int Int.instDvdInt b a) -> (Eq.{1} Int a b)
Case conversion may be inaccurate. Consider using '#align int.dvd_antisymm Int.dvd_antisymmₓ'. -/
theorem dvd_antisymm {a b : ℤ} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b := by
  rw [← abs_of_nonneg H1, ← abs_of_nonneg H2, abs_eq_nat_abs, abs_eq_nat_abs]
  rw [coe_nat_dvd, coe_nat_dvd, coe_nat_inj']
  apply Nat.dvd_antisymm

end Int

