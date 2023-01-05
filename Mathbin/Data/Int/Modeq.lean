/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.int.modeq
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Modeq
import Mathbin.Tactic.Ring

/-!

# Congruences modulo an integer

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the equivalence relation `a ≡ b [ZMOD n]` on the integers, similarly to how
`data.nat.modeq` defines them for the natural numbers. The notation is short for `n.modeq a b`,
which is defined to be `a % n = b % n` for integers `a b n`.

## Tags

modeq, congruence, mod, MOD, modulo, integers

-/


namespace Int

#print Int.ModEq /-
/-- `a ≡ b [ZMOD n]` when `a % n = b % n`. -/
def ModEq (n a b : ℤ) :=
  a % n = b % n deriving Decidable
#align int.modeq Int.ModEq
-/

-- mathport name: «expr ≡ [ZMOD ]»
notation:50 a " ≡ " b " [ZMOD " n "]" => ModEq n a b

variable {m n a b c d : ℤ}

namespace Modeq

#print Int.ModEq.refl /-
@[refl]
protected theorem refl (a : ℤ) : a ≡ a [ZMOD n] :=
  @rfl _ _
#align int.modeq.refl Int.ModEq.refl
-/

#print Int.ModEq.rfl /-
protected theorem rfl : a ≡ a [ZMOD n] :=
  ModEq.refl _
#align int.modeq.rfl Int.ModEq.rfl
-/

instance : IsRefl _ (ModEq n) :=
  ⟨ModEq.refl⟩

#print Int.ModEq.symm /-
@[symm]
protected theorem symm : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] :=
  Eq.symm
#align int.modeq.symm Int.ModEq.symm
-/

#print Int.ModEq.trans /-
@[trans]
protected theorem trans : a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n] :=
  Eq.trans
#align int.modeq.trans Int.ModEq.trans
-/

end Modeq

#print Int.coe_nat_modEq_iff /-
theorem coe_nat_modEq_iff {a b n : ℕ} : a ≡ b [ZMOD n] ↔ a ≡ b [MOD n] := by
  unfold modeq Nat.ModEq <;> rw [← Int.ofNat_inj] <;> simp [coe_nat_mod]
#align int.coe_nat_modeq_iff Int.coe_nat_modEq_iff
-/

/- warning: int.modeq_zero_iff_dvd -> Int.modEq_zero_iff_dvd is a dubious translation:
lean 3 declaration is
  forall {n : Int} {a : Int}, Iff (Int.ModEq n a (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) n a)
but is expected to have type
  forall {n : Int} {a : Int}, Iff (Int.ModEq n a (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Dvd.dvd.{0} Int Int.instDvdInt n a)
Case conversion may be inaccurate. Consider using '#align int.modeq_zero_iff_dvd Int.modEq_zero_iff_dvdₓ'. -/
theorem modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a := by rw [modeq, zero_mod, dvd_iff_mod_eq_zero]
#align int.modeq_zero_iff_dvd Int.modEq_zero_iff_dvd

/- warning: has_dvd.dvd.modeq_zero_int -> Dvd.dvd.modEq_zero_int is a dubious translation:
lean 3 declaration is
  forall {n : Int} {a : Int}, (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) n a) -> (Int.ModEq n a (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))))
but is expected to have type
  forall {n : Int} {a : Int}, (Dvd.dvd.{0} Int Int.instDvdInt n a) -> (Int.ModEq n a (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)))
Case conversion may be inaccurate. Consider using '#align has_dvd.dvd.modeq_zero_int Dvd.dvd.modEq_zero_intₓ'. -/
theorem Dvd.dvd.modEq_zero_int (h : n ∣ a) : a ≡ 0 [ZMOD n] :=
  modEq_zero_iff_dvd.2 h
#align has_dvd.dvd.modeq_zero_int Dvd.dvd.modEq_zero_int

/- warning: has_dvd.dvd.zero_modeq_int -> Dvd.dvd.zero_modEq_int is a dubious translation:
lean 3 declaration is
  forall {n : Int} {a : Int}, (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) n a) -> (Int.ModEq n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a)
but is expected to have type
  forall {n : Int} {a : Int}, (Dvd.dvd.{0} Int Int.instDvdInt n a) -> (Int.ModEq n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a)
Case conversion may be inaccurate. Consider using '#align has_dvd.dvd.zero_modeq_int Dvd.dvd.zero_modEq_intₓ'. -/
theorem Dvd.dvd.zero_modEq_int (h : n ∣ a) : 0 ≡ a [ZMOD n] :=
  h.modeq_zero_int.symm
#align has_dvd.dvd.zero_modeq_int Dvd.dvd.zero_modEq_int

/- warning: int.modeq_iff_dvd -> Int.modEq_iff_dvd is a dubious translation:
lean 3 declaration is
  forall {n : Int} {a : Int} {b : Int}, Iff (Int.ModEq n a b) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) n (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))
but is expected to have type
  forall {n : Int} {a : Int} {b : Int}, Iff (Int.ModEq n a b) (Dvd.dvd.{0} Int Int.instDvdInt n (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))
Case conversion may be inaccurate. Consider using '#align int.modeq_iff_dvd Int.modEq_iff_dvdₓ'. -/
theorem modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a := by
  rw [modeq, eq_comm] <;> simp [mod_eq_mod_iff_mod_sub_eq_zero, dvd_iff_mod_eq_zero]
#align int.modeq_iff_dvd Int.modEq_iff_dvd

#print Int.modEq_iff_add_fac /-
theorem modEq_iff_add_fac {a b n : ℤ} : a ≡ b [ZMOD n] ↔ ∃ t, b = a + n * t :=
  by
  rw [modeq_iff_dvd]
  exact exists_congr fun t => sub_eq_iff_eq_add'
#align int.modeq_iff_add_fac Int.modEq_iff_add_fac
-/

/- warning: int.modeq.dvd -> Int.ModEq.dvd is a dubious translation:
lean 3 declaration is
  forall {n : Int} {a : Int} {b : Int}, (Int.ModEq n a b) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) n (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a))
but is expected to have type
  forall {n : Int} {a : Int} {b : Int}, (Int.ModEq n a b) -> (Dvd.dvd.{0} Int Int.instDvdInt n (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a))
Case conversion may be inaccurate. Consider using '#align int.modeq.dvd Int.ModEq.dvdₓ'. -/
theorem ModEq.dvd : a ≡ b [ZMOD n] → n ∣ b - a :=
  modEq_iff_dvd.1
#align int.modeq.dvd Int.ModEq.dvd

/- warning: int.modeq_of_dvd -> Int.modEq_of_dvd is a dubious translation:
lean 3 declaration is
  forall {n : Int} {a : Int} {b : Int}, (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) n (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) b a)) -> (Int.ModEq n a b)
but is expected to have type
  forall {n : Int} {a : Int} {b : Int}, (Dvd.dvd.{0} Int Int.instDvdInt n (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) b a)) -> (Int.ModEq n a b)
Case conversion may be inaccurate. Consider using '#align int.modeq_of_dvd Int.modEq_of_dvdₓ'. -/
theorem modEq_of_dvd : n ∣ b - a → a ≡ b [ZMOD n] :=
  modEq_iff_dvd.2
#align int.modeq_of_dvd Int.modEq_of_dvd

#print Int.mod_modEq /-
theorem mod_modEq (a n) : a % n ≡ a [ZMOD n] :=
  emod_emod _ _
#align int.mod_modeq Int.mod_modEq
-/

namespace Modeq

/- warning: int.modeq.modeq_of_dvd -> Int.ModEq.modEq_of_dvd is a dubious translation:
lean 3 declaration is
  forall {m : Int} {n : Int} {a : Int} {b : Int}, (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) m n) -> (Int.ModEq n a b) -> (Int.ModEq m a b)
but is expected to have type
  forall {m : Int} {n : Int} {a : Int} {b : Int}, (Dvd.dvd.{0} Int Int.instDvdInt m n) -> (Int.ModEq n a b) -> (Int.ModEq m a b)
Case conversion may be inaccurate. Consider using '#align int.modeq.modeq_of_dvd Int.ModEq.modEq_of_dvdₓ'. -/
protected theorem modEq_of_dvd (d : m ∣ n) (h : a ≡ b [ZMOD n]) : a ≡ b [ZMOD m] :=
  modEq_iff_dvd.2 <| d.trans h.Dvd
#align int.modeq.modeq_of_dvd Int.ModEq.modEq_of_dvd

#print Int.ModEq.mul_left' /-
protected theorem mul_left' (hc : 0 ≤ c) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD c * n] :=
  Or.cases_on hc.lt_or_eq
    (fun hc => by unfold modeq <;> simp [mul_mod_mul_of_pos hc, show _ = _ from h]) fun hc => by
    simp [hc.symm]
#align int.modeq.mul_left' Int.ModEq.mul_left'
-/

#print Int.ModEq.mul_right' /-
protected theorem mul_right' (hc : 0 ≤ c) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n * c] := by
  rw [mul_comm a, mul_comm b, mul_comm n] <;> exact h.mul_left' hc
#align int.modeq.mul_right' Int.ModEq.mul_right'
-/

#print Int.ModEq.add /-
protected theorem add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
  modEq_iff_dvd.2 <| by
    convert dvd_add h₁.dvd h₂.dvd
    ring
#align int.modeq.add Int.ModEq.add
-/

#print Int.ModEq.add_left /-
protected theorem add_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c + a ≡ c + b [ZMOD n] :=
  ModEq.rfl.add h
#align int.modeq.add_left Int.ModEq.add_left
-/

#print Int.ModEq.add_right /-
protected theorem add_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n] :=
  h.add ModEq.rfl
#align int.modeq.add_right Int.ModEq.add_right
-/

#print Int.ModEq.add_left_cancel /-
protected theorem add_left_cancel (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    c ≡ d [ZMOD n] :=
  have : d - c = b + d - (a + c) - (b - a) := by ring
  modEq_iff_dvd.2 <| by
    rw [this]
    exact dvd_sub h₂.dvd h₁.dvd
#align int.modeq.add_left_cancel Int.ModEq.add_left_cancel
-/

#print Int.ModEq.add_left_cancel' /-
protected theorem add_left_cancel' (c : ℤ) (h : c + a ≡ c + b [ZMOD n]) : a ≡ b [ZMOD n] :=
  ModEq.rfl.add_left_cancel h
#align int.modeq.add_left_cancel' Int.ModEq.add_left_cancel'
-/

#print Int.ModEq.add_right_cancel /-
protected theorem add_right_cancel (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    a ≡ b [ZMOD n] := by
  rw [add_comm a, add_comm b] at h₂
  exact h₁.add_left_cancel h₂
#align int.modeq.add_right_cancel Int.ModEq.add_right_cancel
-/

#print Int.ModEq.add_right_cancel' /-
protected theorem add_right_cancel' (c : ℤ) (h : a + c ≡ b + c [ZMOD n]) : a ≡ b [ZMOD n] :=
  ModEq.rfl.add_right_cancel h
#align int.modeq.add_right_cancel' Int.ModEq.add_right_cancel'
-/

#print Int.ModEq.neg /-
protected theorem neg (h : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] :=
  h.add_left_cancel (by simp_rw [← sub_eq_add_neg, sub_self])
#align int.modeq.neg Int.ModEq.neg
-/

#print Int.ModEq.sub /-
protected theorem sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n] :=
  by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h₁.add h₂.neg
#align int.modeq.sub Int.ModEq.sub
-/

#print Int.ModEq.sub_left /-
protected theorem sub_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c - a ≡ c - b [ZMOD n] :=
  ModEq.rfl.sub h
#align int.modeq.sub_left Int.ModEq.sub_left
-/

#print Int.ModEq.sub_right /-
protected theorem sub_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a - c ≡ b - c [ZMOD n] :=
  h.sub ModEq.rfl
#align int.modeq.sub_right Int.ModEq.sub_right
-/

#print Int.ModEq.mul_left /-
protected theorem mul_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD n] :=
  Or.cases_on (le_total 0 c) (fun hc => (h.mul_left' hc).modeq_of_dvd (dvd_mul_left _ _)) fun hc =>
    by
    rw [← neg_neg c, neg_mul, neg_mul _ b] <;>
      exact ((h.mul_left' <| neg_nonneg.2 hc).modeq_of_dvd (dvd_mul_left _ _)).neg
#align int.modeq.mul_left Int.ModEq.mul_left
-/

#print Int.ModEq.mul_right /-
protected theorem mul_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] :=
  by
  rw [mul_comm a, mul_comm b]
  exact h.mul_left c
#align int.modeq.mul_right Int.ModEq.mul_right
-/

#print Int.ModEq.mul /-
protected theorem mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)
#align int.modeq.mul Int.ModEq.mul
-/

/- warning: int.modeq.pow -> Int.ModEq.pow is a dubious translation:
lean 3 declaration is
  forall {n : Int} {a : Int} {b : Int} (m : Nat), (Int.ModEq n a b) -> (Int.ModEq n (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) a m) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) b m))
but is expected to have type
  forall {n : Int} {a : Int} {b : Int} (m : Nat), (Int.ModEq n a b) -> (Int.ModEq n (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat a m) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat b m))
Case conversion may be inaccurate. Consider using '#align int.modeq.pow Int.ModEq.powₓ'. -/
protected theorem pow (m : ℕ) (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] :=
  by
  induction' m with d hd; · rfl
  rw [pow_succ, pow_succ]
  exact h.mul hd
#align int.modeq.pow Int.ModEq.pow

#print Int.ModEq.of_modEq_mul_left /-
theorem of_modEq_mul_left (m : ℤ) (h : a ≡ b [ZMOD m * n]) : a ≡ b [ZMOD n] := by
  rw [modeq_iff_dvd] at * <;> exact (dvd_mul_left n m).trans h
#align int.modeq.of_modeq_mul_left Int.ModEq.of_modEq_mul_left
-/

#print Int.ModEq.of_modEq_mul_right /-
theorem of_modEq_mul_right (m : ℤ) : a ≡ b [ZMOD n * m] → a ≡ b [ZMOD n] :=
  mul_comm m n ▸ of_modEq_mul_left _
#align int.modeq.of_modeq_mul_right Int.ModEq.of_modEq_mul_right
-/

end Modeq

#print Int.modEq_one /-
theorem modEq_one : a ≡ b [ZMOD 1] :=
  modEq_of_dvd (one_dvd _)
#align int.modeq_one Int.modEq_one
-/

#print Int.modEq_sub /-
theorem modEq_sub (a b : ℤ) : a ≡ b [ZMOD a - b] :=
  (modEq_of_dvd dvd_rfl).symm
#align int.modeq_sub Int.modEq_sub
-/

#print Int.modEq_and_modEq_iff_modEq_mul /-
theorem modEq_and_modEq_iff_modEq_mul {a b m n : ℤ} (hmn : m.natAbs.Coprime n.natAbs) :
    a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m * n] :=
  ⟨fun h => by
    rw [modeq_iff_dvd, modeq_iff_dvd] at h
    rw [modeq_iff_dvd, ← nat_abs_dvd, ← dvd_nat_abs, coe_nat_dvd, nat_abs_mul]
    refine' hmn.mul_dvd_of_dvd_of_dvd _ _ <;> rw [← coe_nat_dvd, nat_abs_dvd, dvd_nat_abs] <;>
      tauto,
    fun h => ⟨h.of_modeq_mul_right _, h.of_modeq_mul_left _⟩⟩
#align int.modeq_and_modeq_iff_modeq_mul Int.modEq_and_modEq_iff_modEq_mul
-/

#print Int.gcd_a_modEq /-
theorem gcd_a_modEq (a b : ℕ) : (a : ℤ) * Nat.gcdA a b ≡ Nat.gcd a b [ZMOD b] :=
  by
  rw [← add_zero ((a : ℤ) * _), Nat.gcd_eq_gcd_ab]
  exact (dvd_mul_right _ _).zero_modeq_int.add_left _
#align int.gcd_a_modeq Int.gcd_a_modEq
-/

#print Int.modEq_add_fac /-
theorem modEq_add_fac {a b n : ℤ} (c : ℤ) (ha : a ≡ b [ZMOD n]) : a + n * c ≡ b [ZMOD n] :=
  calc
    a + n * c ≡ b + n * c [ZMOD n] := ha.add_right _
    _ ≡ b + 0 [ZMOD n] := (dvd_mul_right _ _).modeq_zero_int.add_left _
    _ ≡ b [ZMOD n] := by rw [add_zero]
    
#align int.modeq_add_fac Int.modEq_add_fac
-/

#print Int.modEq_add_fac_self /-
theorem modEq_add_fac_self {a t n : ℤ} : a + n * t ≡ a [ZMOD n] :=
  modEq_add_fac _ ModEq.rfl
#align int.modeq_add_fac_self Int.modEq_add_fac_self
-/

#print Int.mod_coprime /-
theorem mod_coprime {a b : ℕ} (hab : Nat.Coprime a b) : ∃ y : ℤ, a * y ≡ 1 [ZMOD b] :=
  ⟨Nat.gcdA a b,
    have hgcd : Nat.gcd a b = 1 := Nat.Coprime.gcd_eq_one hab
    calc
      ↑a * Nat.gcdA a b ≡ ↑a * Nat.gcdA a b + ↑b * Nat.gcdB a b [ZMOD ↑b] :=
        modeq.symm <| modEq_add_fac _ <| ModEq.refl _
      _ ≡ 1 [ZMOD ↑b] := by rw [← Nat.gcd_eq_gcd_ab, hgcd] <;> rfl
      ⟩
#align int.mod_coprime Int.mod_coprime
-/

#print Int.exists_unique_equiv /-
theorem exists_unique_equiv (a : ℤ) {b : ℤ} (hb : 0 < b) :
    ∃ z : ℤ, 0 ≤ z ∧ z < b ∧ z ≡ a [ZMOD b] :=
  ⟨a % b, emod_nonneg _ (ne_of_gt hb),
    by
    have : a % b < |b| := emod_lt _ (ne_of_gt hb)
    rwa [abs_of_pos hb] at this, by simp [modeq]⟩
#align int.exists_unique_equiv Int.exists_unique_equiv
-/

#print Int.exists_unique_equiv_nat /-
theorem exists_unique_equiv_nat (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℕ, ↑z < b ∧ ↑z ≡ a [ZMOD b] :=
  let ⟨z, hz1, hz2, hz3⟩ := exists_unique_equiv a hb
  ⟨z.natAbs, by
    constructor <;> rw [← of_nat_eq_coe, of_nat_nat_abs_eq_of_nonneg hz1] <;> assumption⟩
#align int.exists_unique_equiv_nat Int.exists_unique_equiv_nat
-/

#print Int.mod_mul_right_mod /-
@[simp]
theorem mod_mul_right_mod (a b c : ℤ) : a % (b * c) % b = a % b :=
  (mod_modEq _ _).of_modeq_mul_right _
#align int.mod_mul_right_mod Int.mod_mul_right_mod
-/

#print Int.mod_mul_left_mod /-
@[simp]
theorem mod_mul_left_mod (a b c : ℤ) : a % (b * c) % c = a % c :=
  (mod_modEq _ _).of_modeq_mul_left _
#align int.mod_mul_left_mod Int.mod_mul_left_mod
-/

end Int

