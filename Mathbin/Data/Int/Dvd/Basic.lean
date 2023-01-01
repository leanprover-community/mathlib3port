/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module data.int.dvd.basic
! leanprover-community/mathlib commit 9aba7801eeecebb61f58a5763c2b6dd1b47dc6ef
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Order.Basic
import Mathbin.Data.Nat.Cast.Basic

/-!
# Basic lemmas about the divisibility relation in `ℤ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/996
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Nat

namespace Int

/- warning: int.coe_nat_dvd -> Int.coe_nat_dvd is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, Iff (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) (Dvd.Dvd.{0} Nat Nat.hasDvd m n)
but is expected to have type
  forall {m : Nat} {n : Nat}, Iff (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt m) (Nat.cast.{0} Int Int.instNatCastInt n)) (Dvd.dvd.{0} Nat Nat.instDvdNat m n)
Case conversion may be inaccurate. Consider using '#align int.coe_nat_dvd Int.coe_nat_dvdₓ'. -/
@[norm_cast]
theorem coe_nat_dvd {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
  ⟨fun ⟨a, ae⟩ =>
    m.eq_zero_or_pos.elim (fun m0 => by simp [m0] at ae <;> simp [ae, m0]) fun m0l =>
      by
      cases'
        eq_coe_of_zero_le
          (@nonneg_of_mul_nonneg_right ℤ _ m a (by simp [ae.symm]) (by simpa using m0l)) with
        k e
      subst a
      exact ⟨k, Int.ofNat.inj ae⟩,
    fun ⟨k, e⟩ => Dvd.intro k <| by rw [e, Int.ofNat_mul]⟩
#align int.coe_nat_dvd Int.coe_nat_dvd

/- warning: int.coe_nat_dvd_left -> Int.coe_nat_dvd_left is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {z : Int}, Iff (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n) z) (Dvd.Dvd.{0} Nat Nat.hasDvd n (Int.natAbs z))
but is expected to have type
  forall {n : Nat} {z : Int}, Iff (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt n) z) (Dvd.dvd.{0} Nat Nat.instDvdNat n (Int.natAbs z))
Case conversion may be inaccurate. Consider using '#align int.coe_nat_dvd_left Int.coe_nat_dvd_leftₓ'. -/
theorem coe_nat_dvd_left {n : ℕ} {z : ℤ} : (↑n : ℤ) ∣ z ↔ n ∣ z.natAbs := by
  rcases nat_abs_eq z with (eq | eq) <;> rw [Eq] <;> simp [coe_nat_dvd]
#align int.coe_nat_dvd_left Int.coe_nat_dvd_left

/- warning: int.coe_nat_dvd_right -> Int.coe_nat_dvd_right is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {z : Int}, Iff (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) z ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) (Dvd.Dvd.{0} Nat Nat.hasDvd (Int.natAbs z) n)
but is expected to have type
  forall {n : Nat} {z : Int}, Iff (Dvd.dvd.{0} Int Int.instDvdInt z (Nat.cast.{0} Int Int.instNatCastInt n)) (Dvd.dvd.{0} Nat Nat.instDvdNat (Int.natAbs z) n)
Case conversion may be inaccurate. Consider using '#align int.coe_nat_dvd_right Int.coe_nat_dvd_rightₓ'. -/
theorem coe_nat_dvd_right {n : ℕ} {z : ℤ} : z ∣ (↑n : ℤ) ↔ z.natAbs ∣ n := by
  rcases nat_abs_eq z with (eq | eq) <;> rw [Eq] <;> simp [coe_nat_dvd]
#align int.coe_nat_dvd_right Int.coe_nat_dvd_right

/- warning: int.le_of_dvd -> Int.le_of_dvd is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (LT.lt.{0} Int Int.hasLt (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) b) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) a b) -> (LE.le.{0} Int Int.hasLe a b)
but is expected to have type
  forall {a : Int} {b : Int}, (LT.lt.{0} Int Int.instLTInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) b) -> (Dvd.dvd.{0} Int Int.instDvdInt a b) -> (LE.le.{0} Int Int.instLEInt a b)
Case conversion may be inaccurate. Consider using '#align int.le_of_dvd Int.le_of_dvdₓ'. -/
theorem le_of_dvd {a b : ℤ} (bpos : 0 < b) (H : a ∣ b) : a ≤ b :=
  match a, b, eq_succ_of_zero_lt bpos, H with
  | (m : ℕ), _, ⟨n, rfl⟩, H =>
    coe_nat_le_coe_nat_of_le <| Nat.le_of_dvd n.succ_pos <| coe_nat_dvd.1 H
  | -[m+1], _, ⟨n, rfl⟩, _ => le_trans (le_of_lt <| negSucc_lt_zero _) (ofNat_zero_le _)
#align int.le_of_dvd Int.le_of_dvd

/- warning: int.eq_one_of_dvd_one -> Int.eq_one_of_dvd_one is a dubious translation:
lean 3 declaration is
  forall {a : Int}, (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) a (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) -> (Eq.{1} Int a (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {a : Int}, (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a) -> (Dvd.dvd.{0} Int Int.instDvdInt a (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) -> (Eq.{1} Int a (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align int.eq_one_of_dvd_one Int.eq_one_of_dvd_oneₓ'. -/
theorem eq_one_of_dvd_one {a : ℤ} (H : 0 ≤ a) (H' : a ∣ 1) : a = 1 :=
  match a, eq_ofNat_of_zero_le H, H' with
  | _, ⟨n, rfl⟩, H' => congr_arg coe <| Nat.eq_one_of_dvd_one <| coe_nat_dvd.1 H'
#align int.eq_one_of_dvd_one Int.eq_one_of_dvd_one

#print Int.eq_one_of_mul_eq_one_right /-
theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : 0 ≤ a) (H' : a * b = 1) : a = 1 :=
  eq_one_of_dvd_one H ⟨b, H'.symm⟩
#align int.eq_one_of_mul_eq_one_right Int.eq_one_of_mul_eq_one_right
-/

#print Int.eq_one_of_mul_eq_one_left /-
theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : 0 ≤ b) (H' : a * b = 1) : b = 1 :=
  eq_one_of_mul_eq_one_right H (by rw [mul_comm, H'])
#align int.eq_one_of_mul_eq_one_left Int.eq_one_of_mul_eq_one_left
-/

/- warning: int.of_nat_dvd_of_dvd_nat_abs -> Int.ofNat_dvd_of_dvd_natAbs is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {z : Int}, (Dvd.Dvd.{0} Nat Nat.hasDvd a (Int.natAbs z)) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) a) z)
but is expected to have type
  forall {a : Nat} {z : Int}, (Dvd.dvd.{0} Nat Nat.instDvdNat a (Int.natAbs z)) -> (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt a) z)
Case conversion may be inaccurate. Consider using '#align int.of_nat_dvd_of_dvd_nat_abs Int.ofNat_dvd_of_dvd_natAbsₓ'. -/
theorem ofNat_dvd_of_dvd_natAbs {a : ℕ} : ∀ {z : ℤ} (haz : a ∣ z.natAbs), ↑a ∣ z
  | Int.ofNat _, haz => Int.coe_nat_dvd.2 haz
  | -[k+1], haz => by
    change ↑a ∣ -(k + 1 : ℤ)
    apply dvd_neg_of_dvd
    apply Int.coe_nat_dvd.2
    exact haz
#align int.of_nat_dvd_of_dvd_nat_abs Int.ofNat_dvd_of_dvd_natAbs

/- warning: int.dvd_nat_abs_of_of_nat_dvd -> Int.dvd_natAbs_of_ofNat_dvd is a dubious translation:
lean 3 declaration is
  forall {a : Nat} {z : Int}, (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) a) z) -> (Dvd.Dvd.{0} Nat Nat.hasDvd a (Int.natAbs z))
but is expected to have type
  forall {a : Nat} {z : Int}, (Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt a) z) -> (Dvd.dvd.{0} Nat Nat.instDvdNat a (Int.natAbs z))
Case conversion may be inaccurate. Consider using '#align int.dvd_nat_abs_of_of_nat_dvd Int.dvd_natAbs_of_ofNat_dvdₓ'. -/
theorem dvd_natAbs_of_ofNat_dvd {a : ℕ} : ∀ {z : ℤ} (haz : ↑a ∣ z), a ∣ z.natAbs
  | Int.ofNat _, haz => Int.coe_nat_dvd.1 (Int.dvd_natAbs.2 haz)
  | -[k+1], haz =>
    have haz' : (↑a : ℤ) ∣ (↑(k + 1) : ℤ) := dvd_of_dvd_neg haz
    Int.coe_nat_dvd.1 haz'
#align int.dvd_nat_abs_of_of_nat_dvd Int.dvd_natAbs_of_ofNat_dvd

/- warning: int.dvd_antisymm -> Int.dvd_antisymm is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a) -> (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) b) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) a b) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) b a) -> (Eq.{1} Int a b)
but is expected to have type
  forall {a : Int} {b : Int}, (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a) -> (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) b) -> (Dvd.dvd.{0} Int Int.instDvdInt a b) -> (Dvd.dvd.{0} Int Int.instDvdInt b a) -> (Eq.{1} Int a b)
Case conversion may be inaccurate. Consider using '#align int.dvd_antisymm Int.dvd_antisymmₓ'. -/
theorem dvd_antisymm {a b : ℤ} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b :=
  by
  rw [← abs_of_nonneg H1, ← abs_of_nonneg H2, abs_eq_nat_abs, abs_eq_nat_abs]
  rw [coe_nat_dvd, coe_nat_dvd, coe_nat_inj']
  apply Nat.dvd_antisymm
#align int.dvd_antisymm Int.dvd_antisymm

end Int

