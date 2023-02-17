/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.lemmas
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rat.Defs
import Mathbin.Data.Int.Cast.Lemmas
import Mathbin.Data.Int.Div
import Mathbin.Algebra.GroupWithZero.Units.Lemmas
import Mathbin.Tactic.NthRewrite.Default

/-!
# Further lemmas for the Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


namespace Rat

open Rat

/- warning: rat.num_dvd -> Rat.num_dvd is a dubious translation:
lean 3 declaration is
  forall (a : Int) {b : Int}, (Ne.{1} Int b (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) (Rat.num (Rat.mk a b)) a)
but is expected to have type
  forall (a : Int) {b : Int}, (Ne.{1} Int b (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Dvd.dvd.{0} Int Int.instDvdInt (Rat.num (Rat.divInt a b)) a)
Case conversion may be inaccurate. Consider using '#align rat.num_dvd Rat.num_dvdₓ'. -/
theorem num_dvd (a) {b : ℤ} (b0 : b ≠ 0) : (a /. b).num ∣ a :=
  by
  cases' e : a /. b with n d h c
  rw [Rat.num_den', Rat.divInt_eq_iff b0 (ne_of_gt (Int.coe_nat_pos.2 h))] at e
  refine' Int.natAbs_dvd.1 <| Int.dvd_natAbs.1 <| Int.coe_nat_dvd.2 <| c.dvd_of_dvd_mul_right _
  have := congr_arg Int.natAbs e
  simp only [Int.natAbs_mul, Int.natAbs_ofNat] at this; simp [this]
#align rat.num_dvd Rat.num_dvd

/- warning: rat.denom_dvd -> Rat.den_dvd is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den (Rat.mk a b))) b
but is expected to have type
  forall (a : Int) (b : Int), Dvd.dvd.{0} Int Int.instDvdInt (Nat.cast.{0} Int Int.instNatCastInt (Rat.den (Rat.divInt a b))) b
Case conversion may be inaccurate. Consider using '#align rat.denom_dvd Rat.den_dvdₓ'. -/
theorem den_dvd (a b : ℤ) : ((a /. b).den : ℤ) ∣ b :=
  by
  by_cases b0 : b = 0; · simp [b0]
  cases' e : a /. b with n d h c
  rw [num_denom', mk_eq b0 (ne_of_gt (Int.coe_nat_pos.2 h))] at e
  refine' Int.dvd_natAbs.1 <| Int.coe_nat_dvd.2 <| c.symm.dvd_of_dvd_mul_left _
  rw [← Int.natAbs_mul, ← Int.coe_nat_dvd, Int.dvd_natAbs, ← e]; simp
#align rat.denom_dvd Rat.den_dvd

/- warning: rat.num_denom_mk -> Rat.num_den_mk is a dubious translation:
lean 3 declaration is
  forall {q : Rat} {n : Int} {d : Int}, (Ne.{1} Int d (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Eq.{1} Rat q (Rat.mk n d)) -> (Exists.{1} Int (fun (c : Int) => And (Eq.{1} Int n (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) c (Rat.num q))) (Eq.{1} Int d (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) c ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den q))))))
but is expected to have type
  forall {q : Rat} {n : Int} {d : Int}, (Ne.{1} Int d (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Eq.{1} Rat q (Rat.divInt n d)) -> (Exists.{1} Int (fun (c : Int) => And (Eq.{1} Int n (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) c (Rat.num q))) (Eq.{1} Int d (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) c (Nat.cast.{0} Int Int.instNatCastInt (Rat.den q))))))
Case conversion may be inaccurate. Consider using '#align rat.num_denom_mk Rat.num_den_mkₓ'. -/
theorem num_den_mk {q : ℚ} {n d : ℤ} (hd : d ≠ 0) (qdf : q = n /. d) :
    ∃ c : ℤ, n = c * q.num ∧ d = c * q.den :=
  by
  obtain rfl | hn := eq_or_ne n 0
  · simp [qdf]
  have : q.num * d = n * ↑q.denom :=
    by
    refine' (Rat.divInt_eq_iff _ hd).mp _
    · exact int.coe_nat_ne_zero.mpr (Rat.den_nz _)
    · rwa [num_denom]
  have hqdn : q.num ∣ n := by
    rw [qdf]
    exact Rat.num_dvd _ hd
  refine' ⟨n / q.num, _, _⟩
  · rw [Int.ediv_mul_cancel hqdn]
  · refine' Int.eq_mul_div_of_mul_eq_mul_of_dvd_left _ hqdn this
    rw [qdf]
    exact Rat.num_ne_zero_of_ne_zero ((mk_ne_zero hd).mpr hn)
#align rat.num_denom_mk Rat.num_den_mk

/- warning: rat.mk_pnat_num clashes with [anonymous] -> [anonymous]
warning: rat.mk_pnat_num -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (n : Int) (d : PNat), Eq.{1} Int (Rat.num ([anonymous] n d)) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Nat.gcd (Int.natAbs n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) d))))
but is expected to have type
  forall {n : Type.{u}} {d : Type.{v}}, (Nat -> n -> d) -> Nat -> (List.{u} n) -> (List.{v} d)
Case conversion may be inaccurate. Consider using '#align rat.mk_pnat_num [anonymous]ₓ'. -/
theorem [anonymous] (n : ℤ) (d : ℕ+) : ([anonymous] n d).num = n / Nat.gcd n.natAbs d := by
  cases d <;> rfl
#align rat.mk_pnat_num [anonymous]

/- warning: rat.mk_pnat_denom clashes with [anonymous] -> [anonymous]
warning: rat.mk_pnat_denom -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (n : Int) (d : PNat), Eq.{1} Nat (Rat.den ([anonymous] n d)) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) d) (Nat.gcd (Int.natAbs n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) d)))
but is expected to have type
  forall {n : Type.{u}} {d : Type.{v}}, (Nat -> n -> d) -> Nat -> (List.{u} n) -> (List.{v} d)
Case conversion may be inaccurate. Consider using '#align rat.mk_pnat_denom [anonymous]ₓ'. -/
theorem [anonymous] (n : ℤ) (d : ℕ+) : ([anonymous] n d).den = d / Nat.gcd n.natAbs d := by
  cases d <;> rfl
#align rat.mk_pnat_denom [anonymous]

/- warning: rat.num_mk -> Rat.num_mk is a dubious translation:
lean 3 declaration is
  forall (n : Int) (d : Int), Eq.{1} Int (Rat.num (Rat.mk n d)) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (Int.sign d) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Int.gcd n d)))
but is expected to have type
  forall (n : Int) (d : Int), Eq.{1} Int (Rat.num (Rat.divInt n d)) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Int.sign d) n) (Nat.cast.{0} Int Int.instNatCastInt (Int.gcd n d)))
Case conversion may be inaccurate. Consider using '#align rat.num_mk Rat.num_mkₓ'. -/
theorem num_mk (n d : ℤ) : (n /. d).num = d.sign * n / n.gcd d := by
  rcases d with ((_ | _) | _) <;>
    simp [Rat.mk, mk_nat, mk_pnat, Nat.succPNat, Int.sign, Int.gcd, -Nat.cast_succ, -Int.ofNat_succ,
      Int.zero_div]
#align rat.num_mk Rat.num_mk

/- warning: rat.denom_mk -> Rat.den_mk is a dubious translation:
lean 3 declaration is
  forall (n : Int) (d : Int), Eq.{1} Nat (Rat.den (Rat.mk n d)) (ite.{1} Nat (Eq.{1} Int d (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Int.decidableEq d (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) (Int.natAbs d) (Int.gcd n d)))
but is expected to have type
  forall (n : Int) (d : Int), Eq.{1} Nat (Rat.den (Rat.divInt n d)) (ite.{1} Nat (Eq.{1} Int d (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Int.instDecidableEqInt d (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) (Int.natAbs d) (Int.gcd n d)))
Case conversion may be inaccurate. Consider using '#align rat.denom_mk Rat.den_mkₓ'. -/
theorem den_mk (n d : ℤ) : (n /. d).den = if d = 0 then 1 else d.natAbs / n.gcd d := by
  rcases d with ((_ | _) | _) <;>
    simp [Rat.mk, mk_nat, mk_pnat, Nat.succPNat, Int.sign, Int.gcd, -Nat.cast_succ, -Int.ofNat_succ]
#align rat.denom_mk Rat.den_mk

/- warning: rat.mk_pnat_denom_dvd clashes with [anonymous] -> [anonymous]
warning: rat.mk_pnat_denom_dvd -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (n : Int) (d : PNat), Dvd.Dvd.{0} Nat Nat.hasDvd (Rat.den ([anonymous] n d)) (Subtype.val.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) d)
but is expected to have type
  forall {n : Type.{u}} {d : Type.{v}}, (Nat -> n -> d) -> Nat -> (List.{u} n) -> (List.{v} d)
Case conversion may be inaccurate. Consider using '#align rat.mk_pnat_denom_dvd [anonymous]ₓ'. -/
theorem [anonymous] (n : ℤ) (d : ℕ+) : ([anonymous] n d).den ∣ d.1 :=
  by
  rw [mk_pnat_denom]
  apply Nat.div_dvd_of_dvd
  apply Nat.gcd_dvd_right
#align rat.mk_pnat_denom_dvd [anonymous]

#print Rat.add_den_dvd /-
theorem add_den_dvd (q₁ q₂ : ℚ) : (q₁ + q₂).den ∣ q₁.den * q₂.den :=
  by
  cases q₁
  cases q₂
  apply mk_pnat_denom_dvd
#align rat.add_denom_dvd Rat.add_den_dvd
-/

#print Rat.mul_den_dvd /-
theorem mul_den_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).den ∣ q₁.den * q₂.den :=
  by
  cases q₁
  cases q₂
  apply mk_pnat_denom_dvd
#align rat.mul_denom_dvd Rat.mul_den_dvd
-/

#print Rat.mul_num /-
theorem mul_num (q₁ q₂ : ℚ) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  cases q₁ <;> cases q₂ <;> rfl
#align rat.mul_num Rat.mul_num
-/

#print Rat.mul_den /-
theorem mul_den (q₁ q₂ : ℚ) :
    (q₁ * q₂).den = q₁.den * q₂.den / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  cases q₁ <;> cases q₂ <;> rfl
#align rat.mul_denom Rat.mul_den
-/

#print Rat.mul_self_num /-
theorem mul_self_num (q : ℚ) : (q * q).num = q.num * q.num := by
  rw [mul_num, Int.natAbs_mul, Nat.coprime.gcd_eq_one, Int.ofNat_one, Int.div_one] <;>
    exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)
#align rat.mul_self_num Rat.mul_self_num
-/

#print Rat.mul_self_den /-
theorem mul_self_den (q : ℚ) : (q * q).den = q.den * q.den := by
  rw [Rat.mul_den, Int.natAbs_mul, Nat.coprime.gcd_eq_one, Nat.div_one] <;>
    exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)
#align rat.mul_self_denom Rat.mul_self_den
-/

/- warning: rat.add_num_denom -> Rat.add_num_den is a dubious translation:
lean 3 declaration is
  forall (q : Rat) (r : Rat), Eq.{1} Rat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) q r) (Rat.mk (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (Rat.num q) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den r))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den q)) (Rat.num r))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den q)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den r))))
but is expected to have type
  forall (q : Rat) (r : Rat), Eq.{1} Rat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) q r) (Rat.divInt (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Rat.num q) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den r))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den q)) (Rat.num r))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den q)) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den r))))
Case conversion may be inaccurate. Consider using '#align rat.add_num_denom Rat.add_num_denₓ'. -/
theorem add_num_den (q r : ℚ) :
    q + r = (q.num * r.den + q.den * r.num : ℤ) /. (↑q.den * ↑r.den : ℤ) :=
  by
  have hqd : (q.den : ℤ) ≠ 0 := Int.coe_nat_ne_zero_iff_pos.2 q.3
  have hrd : (r.den : ℤ) ≠ 0 := Int.coe_nat_ne_zero_iff_pos.2 r.3
  conv_lhs => rw [← @num_denom q, ← @num_denom r, Rat.add_def'' hqd hrd] <;> simp [mul_comm]
#align rat.add_num_denom Rat.add_num_den

section Casts

#print Rat.exists_eq_mul_div_num_and_eq_mul_div_den /-
theorem exists_eq_mul_div_num_and_eq_mul_div_den (n : ℤ) {d : ℤ} (d_ne_zero : d ≠ 0) :
    ∃ c : ℤ, n = c * ((n : ℚ) / d).num ∧ (d : ℤ) = c * ((n : ℚ) / d).den :=
  haveI : (n : ℚ) / d = Rat.mk n d := by rw [← Rat.divInt_eq_div]
  Rat.num_den_mk d_ne_zero this
#align rat.exists_eq_mul_div_num_and_eq_mul_div_denom Rat.exists_eq_mul_div_num_and_eq_mul_div_den
-/

#print Rat.mul_num_den' /-
theorem mul_num_den' (q r : ℚ) : (q * r).num * q.den * r.den = q.num * r.num * (q * r).den :=
  by
  let s := q.num * r.num /. (q.denom * r.denom : ℤ)
  have hs : (q.denom * r.denom : ℤ) ≠ 0 := int.coe_nat_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_denom⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_denom (q.num * r.num) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  nth_rw 1 [c_mul_denom]
  repeat' rw [mul_assoc]
  apply mul_eq_mul_left_iff.2
  rw [or_iff_not_imp_right]
  intro c_pos
  have h : _ = s :=
    @mul_def q.num q.denom r.num r.denom (int.coe_nat_ne_zero_iff_pos.mpr q.pos)
      (int.coe_nat_ne_zero_iff_pos.mpr r.pos)
  rw [num_denom, num_denom] at h
  rw [h]
  rw [mul_comm]
  apply rat.eq_iff_mul_eq_mul.mp
  rw [← mk_eq_div]
#align rat.mul_num_denom' Rat.mul_num_den'
-/

#print Rat.add_num_den' /-
theorem add_num_den' (q r : ℚ) :
    (q + r).num * q.den * r.den = (q.num * r.den + r.num * q.den) * (q + r).den :=
  by
  let s := mk (q.num * r.denom + r.num * q.denom) (q.denom * r.denom : ℤ)
  have hs : (q.denom * r.denom : ℤ) ≠ 0 := int.coe_nat_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_denom⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_denom (q.num * r.denom + r.num * q.denom) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  nth_rw 1 [c_mul_denom]
  repeat' rw [mul_assoc]
  apply mul_eq_mul_left_iff.2
  rw [or_iff_not_imp_right]
  intro c_pos
  have h : _ = s :=
    @add_def q.num q.denom r.num r.denom (int.coe_nat_ne_zero_iff_pos.mpr q.pos)
      (int.coe_nat_ne_zero_iff_pos.mpr r.pos)
  rw [num_denom, num_denom] at h
  rw [h]
  rw [mul_comm]
  apply rat.eq_iff_mul_eq_mul.mp
  rw [← mk_eq_div]
#align rat.add_num_denom' Rat.add_num_den'
-/

/- warning: rat.substr_num_denom' -> Rat.substr_num_den' is a dubious translation:
lean 3 declaration is
  forall (q : Rat) (r : Rat), Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (Rat.num (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) q r)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den q))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den r))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (Rat.num q) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den r))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (Rat.num r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den q)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat (SubNegMonoid.toHasSub.{0} Rat (AddGroup.toSubNegMonoid.{0} Rat Rat.addGroup))) q r))))
but is expected to have type
  forall (q : Rat) (r : Rat), Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Rat.num (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) q r)) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den q))) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den r))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Rat.num q) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den r))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Rat.num r) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den q)))) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) q r))))
Case conversion may be inaccurate. Consider using '#align rat.substr_num_denom' Rat.substr_num_den'ₓ'. -/
theorem substr_num_den' (q r : ℚ) :
    (q - r).num * q.den * r.den = (q.num * r.den - r.num * q.den) * (q - r).den := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_mul, ← num_neg_eq_neg_num, ← denom_neg_eq_denom r,
    add_num_denom' q (-r)]
#align rat.substr_num_denom' Rat.substr_num_den'

end Casts

#print Rat.inv_def'' /-
theorem inv_def'' {q : ℚ} : q⁻¹ = (q.den : ℚ) / q.num :=
  by
  conv_lhs => rw [← @num_denom q]
  rw [inv_def, mk_eq_div, Int.cast_ofNat]
#align rat.inv_def' Rat.inv_def''
-/

#print Rat.inv_neg /-
protected theorem inv_neg (q : ℚ) : (-q)⁻¹ = -q⁻¹ :=
  by
  rw [← @num_denom q]
  simp [-num_denom]
#align rat.inv_neg Rat.inv_neg
-/

#print Rat.mul_den_eq_num /-
@[simp]
theorem mul_den_eq_num {q : ℚ} : q * q.den = q.num :=
  by
  suffices mk q.num ↑q.denom * mk (↑q.denom) 1 = mk q.num 1
    by
    conv => pattern (occs := 1) q <;> (rw [← @num_denom q])
    rwa [coe_int_eq_mk, coe_nat_eq_mk]
  have : (q.denom : ℤ) ≠ 0 := ne_of_gt (by exact_mod_cast q.pos)
  rw [Rat.mul_def' this one_ne_zero, mul_comm (q.denom : ℤ) 1, div_mk_div_cancel_left this]
#align rat.mul_denom_eq_num Rat.mul_den_eq_num
-/

/- warning: rat.denom_div_cast_eq_one_iff -> Rat.den_div_cast_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall (m : Int) (n : Int), (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Iff (Eq.{1} Nat (Rat.den (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) n))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) n m))
but is expected to have type
  forall (m : Int) (n : Int), (Ne.{1} Int n (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Iff (Eq.{1} Nat (Rat.den (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Int.cast.{0} Rat Rat.instIntCastRat m) (Int.cast.{0} Rat Rat.instIntCastRat n))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Dvd.dvd.{0} Int Int.instDvdInt n m))
Case conversion may be inaccurate. Consider using '#align rat.denom_div_cast_eq_one_iff Rat.den_div_cast_eq_one_iffₓ'. -/
theorem den_div_cast_eq_one_iff (m n : ℤ) (hn : n ≠ 0) : ((m : ℚ) / n).den = 1 ↔ n ∣ m :=
  by
  replace hn : (n : ℚ) ≠ 0; · rwa [Ne.def, ← Int.cast_zero, coe_int_inj]
  constructor
  · intro h
    lift (m : ℚ) / n to ℤ using h with k hk
    use k
    rwa [eq_div_iff_mul_eq hn, ← Int.cast_mul, mul_comm, eq_comm, coe_int_inj] at hk
  · rintro ⟨d, rfl⟩
    rw [Int.cast_mul, mul_comm, mul_div_cancel _ hn, Rat.coe_int_den]
#align rat.denom_div_cast_eq_one_iff Rat.den_div_cast_eq_one_iff

#print Rat.num_div_eq_of_coprime /-
theorem num_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.coprime a.natAbs b.natAbs) :
    (a / b : ℚ).num = a := by
  lift b to ℕ using le_of_lt hb0
  norm_cast  at hb0 h
  rw [← Rat.divInt_eq_div, ← [anonymous] a b hb0, [anonymous], PNat.mk_coe, h.gcd_eq_one,
    Int.ofNat_one, Int.div_one]
#align rat.num_div_eq_of_coprime Rat.num_div_eq_of_coprime
-/

#print Rat.den_div_eq_of_coprime /-
theorem den_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.coprime a.natAbs b.natAbs) :
    ((a / b : ℚ).den : ℤ) = b := by
  lift b to ℕ using le_of_lt hb0
  norm_cast  at hb0 h
  rw [← Rat.divInt_eq_div, ← [anonymous] a b hb0, [anonymous], PNat.mk_coe, h.gcd_eq_one,
    Nat.div_one]
#align rat.denom_div_eq_of_coprime Rat.den_div_eq_of_coprime
-/

#print Rat.div_int_inj /-
theorem div_int_inj {a b c d : ℤ} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : Nat.coprime a.natAbs b.natAbs)
    (h2 : Nat.coprime c.natAbs d.natAbs) (h : (a : ℚ) / b = (c : ℚ) / d) : a = c ∧ b = d :=
  by
  apply And.intro
  · rw [← num_div_eq_of_coprime hb0 h1, h, num_div_eq_of_coprime hd0 h2]
  · rw [← denom_div_eq_of_coprime hb0 h1, h, denom_div_eq_of_coprime hd0 h2]
#align rat.div_int_inj Rat.div_int_inj
-/

#print Rat.coe_int_div_self /-
@[norm_cast]
theorem coe_int_div_self (n : ℤ) : ((n / n : ℤ) : ℚ) = n / n :=
  by
  by_cases hn : n = 0
  · subst hn
    simp only [Int.cast_zero, Int.zero_div, zero_div]
  · have : (n : ℚ) ≠ 0 := by rwa [← coe_int_inj] at hn
    simp only [Int.ediv_self hn, Int.cast_one, Ne.def, not_false_iff, div_self this]
#align rat.coe_int_div_self Rat.coe_int_div_self
-/

#print Rat.coe_nat_div_self /-
@[norm_cast]
theorem coe_nat_div_self (n : ℕ) : ((n / n : ℕ) : ℚ) = n / n :=
  coe_int_div_self n
#align rat.coe_nat_div_self Rat.coe_nat_div_self
-/

/- warning: rat.coe_int_div -> Rat.coe_int_div is a dubious translation:
lean 3 declaration is
  forall (a : Int) (b : Int), (Dvd.Dvd.{0} Int (semigroupDvd.{0} Int Int.semigroup) b a) -> (Eq.{1} Rat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) a b)) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.hasDiv) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) b)))
but is expected to have type
  forall (a : Int) (b : Int), (Dvd.dvd.{0} Int Int.instDvdInt b a) -> (Eq.{1} Rat (Int.cast.{0} Rat Rat.instIntCastRat (HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) a b)) (HDiv.hDiv.{0, 0, 0} Rat Rat Rat (instHDiv.{0} Rat Rat.instDivRat) (Int.cast.{0} Rat Rat.instIntCastRat a) (Int.cast.{0} Rat Rat.instIntCastRat b)))
Case conversion may be inaccurate. Consider using '#align rat.coe_int_div Rat.coe_int_divₓ'. -/
theorem coe_int_div (a b : ℤ) (h : b ∣ a) : ((a / b : ℤ) : ℚ) = a / b :=
  by
  rcases h with ⟨c, rfl⟩
  simp only [mul_comm b, Int.mul_ediv_assoc c (dvd_refl b), Int.cast_mul, mul_div_assoc,
    coe_int_div_self]
#align rat.coe_int_div Rat.coe_int_div

#print Rat.coe_nat_div /-
theorem coe_nat_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : ℚ) = a / b :=
  by
  rcases h with ⟨c, rfl⟩
  simp only [mul_comm b, Nat.mul_div_assoc c (dvd_refl b), Nat.cast_mul, mul_div_assoc,
    coe_nat_div_self]
#align rat.coe_nat_div Rat.coe_nat_div
-/

#print Rat.inv_coe_int_num_of_pos /-
theorem inv_coe_int_num_of_pos {a : ℤ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 :=
  by
  rw [Rat.inv_def'', Rat.coe_int_num, Rat.coe_int_den, Nat.cast_one, ← Int.cast_one]
  apply num_div_eq_of_coprime ha0
  rw [Int.natAbs_one]
  exact Nat.coprime_one_left _
#align rat.inv_coe_int_num_of_pos Rat.inv_coe_int_num_of_pos
-/

#print Rat.inv_coe_nat_num_of_pos /-
theorem inv_coe_nat_num_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 :=
  inv_coe_int_num_of_pos (by exact_mod_cast ha0 : 0 < (a : ℤ))
#align rat.inv_coe_nat_num_of_pos Rat.inv_coe_nat_num_of_pos
-/

#print Rat.inv_coe_int_den_of_pos /-
theorem inv_coe_int_den_of_pos {a : ℤ} (ha0 : 0 < a) : ((a : ℚ)⁻¹.den : ℤ) = a :=
  by
  rw [Rat.inv_def'', Rat.coe_int_num, Rat.coe_int_den, Nat.cast_one, ← Int.cast_one]
  apply denom_div_eq_of_coprime ha0
  rw [Int.natAbs_one]
  exact Nat.coprime_one_left _
#align rat.inv_coe_int_denom_of_pos Rat.inv_coe_int_den_of_pos
-/

#print Rat.inv_coe_nat_den_of_pos /-
theorem inv_coe_nat_den_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.den = a :=
  by
  rw [← Int.ofNat_inj, ← Int.cast_ofNat a, inv_coe_int_denom_of_pos]
  rwa [← Nat.cast_zero, Nat.cast_lt]
#align rat.inv_coe_nat_denom_of_pos Rat.inv_coe_nat_den_of_pos
-/

#print Rat.inv_coe_int_num /-
@[simp]
theorem inv_coe_int_num (a : ℤ) : (a : ℚ)⁻¹.num = Int.sign a := by
  induction a using Int.induction_on <;>
    simp [← Int.negSucc_coe', Int.negSucc_coe, -neg_add_rev, Rat.inv_neg, Int.ofNat_add_one_out,
      -Nat.cast_succ, inv_coe_nat_num_of_pos, -Int.cast_negSucc, @eq_comm ℤ 1,
      Int.sign_eq_one_of_pos]
#align rat.inv_coe_int_num Rat.inv_coe_int_num
-/

#print Rat.inv_coe_nat_num /-
@[simp]
theorem inv_coe_nat_num (a : ℕ) : (a : ℚ)⁻¹.num = Int.sign a :=
  inv_coe_int_num a
#align rat.inv_coe_nat_num Rat.inv_coe_nat_num
-/

/- warning: rat.inv_coe_int_denom -> Rat.inv_coe_int_den is a dubious translation:
lean 3 declaration is
  forall (a : Int), Eq.{1} Nat (Rat.den (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Rat (HasLiftT.mk.{1, 1} Int Rat (CoeTCₓ.coe.{1, 1} Int Rat (Int.castCoe.{0} Rat Rat.hasIntCast))) a))) (ite.{1} Nat (Eq.{1} Int a (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (Int.decidableEq a (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Int.natAbs a))
but is expected to have type
  forall (a : Int), Eq.{1} Nat (Rat.den (Inv.inv.{0} Rat Rat.instInvRat (Int.cast.{0} Rat Rat.instIntCastRat a))) (ite.{1} Nat (Eq.{1} Int a (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (Int.instDecidableEqInt a (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Int.natAbs a))
Case conversion may be inaccurate. Consider using '#align rat.inv_coe_int_denom Rat.inv_coe_int_denₓ'. -/
@[simp]
theorem inv_coe_int_den (a : ℤ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a.natAbs := by
  induction a using Int.induction_on <;>
    simp [← Int.negSucc_coe', Int.negSucc_coe, -neg_add_rev, Rat.inv_neg, Int.ofNat_add_one_out,
      -Nat.cast_succ, inv_coe_nat_denom_of_pos, -Int.cast_negSucc]
#align rat.inv_coe_int_denom Rat.inv_coe_int_den

/- warning: rat.inv_coe_nat_denom -> Rat.inv_coe_nat_den is a dubious translation:
lean 3 declaration is
  forall (a : Nat), Eq.{1} Nat (Rat.den (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Rat (HasLiftT.mk.{1, 1} Nat Rat (CoeTCₓ.coe.{1, 1} Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (NonAssocRing.toAddGroupWithOne.{0} Rat (Ring.toNonAssocRing.{0} Rat (CommRing.toRing.{0} Rat Rat.commRing)))))))) a))) (ite.{1} Nat (Eq.{1} Nat a (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Nat.decidableEq a (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) a)
but is expected to have type
  forall (a : Nat), Eq.{1} Nat (Rat.den (Inv.inv.{0} Rat Rat.instInvRat (Nat.cast.{0} Rat (NonAssocRing.toNatCast.{0} Rat (Ring.toNonAssocRing.{0} Rat (CommRing.toRing.{0} Rat Rat.commRing))) a))) (ite.{1} Nat (Eq.{1} Nat a (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (instDecidableEqNat a (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) a)
Case conversion may be inaccurate. Consider using '#align rat.inv_coe_nat_denom Rat.inv_coe_nat_denₓ'. -/
@[simp]
theorem inv_coe_nat_den (a : ℕ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a := by
  simpa using inv_coe_int_denom a
#align rat.inv_coe_nat_denom Rat.inv_coe_nat_den

#print Rat.forall /-
protected theorem forall {p : ℚ → Prop} : (∀ r, p r) ↔ ∀ a b : ℤ, p (a / b) :=
  ⟨fun h _ _ => h _, fun h q => show q = q.num / q.den by simp [Rat.div_num_den].symm ▸ h q.1 q.2⟩
#align rat.forall Rat.forall
-/

#print Rat.exists /-
protected theorem exists {p : ℚ → Prop} : (∃ r, p r) ↔ ∃ a b : ℤ, p (a / b) :=
  ⟨fun ⟨r, hr⟩ => ⟨r.num, r.den, by rwa [← mk_eq_div, num_denom]⟩, fun ⟨a, b, h⟩ => ⟨_, h⟩⟩
#align rat.exists Rat.exists
-/

/-!
### Denominator as `ℕ+`
-/


section PnatDenom

#print Rat.pnatDen /-
/-- Denominator as `ℕ+`. -/
def pnatDen (x : ℚ) : ℕ+ :=
  ⟨x.den, x.Pos⟩
#align rat.pnat_denom Rat.pnatDen
-/

#print Rat.coe_pnatDen /-
@[simp]
theorem coe_pnatDen (x : ℚ) : (x.pnatDen : ℕ) = x.den :=
  rfl
#align rat.coe_pnat_denom Rat.coe_pnatDen
-/

/- warning: rat.mk_pnat_pnat_denom_eq clashes with [anonymous] -> [anonymous]
warning: rat.mk_pnat_pnat_denom_eq -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (x : Rat), Eq.{1} Rat ([anonymous] (Rat.num x) (Rat.pnatDen x)) x
but is expected to have type
  forall {x : Type.{u}} {β : Type.{v}}, (Nat -> x -> β) -> Nat -> (List.{u} x) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align rat.mk_pnat_pnat_denom_eq [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (x : ℚ) : [anonymous] x.num x.pnatDen = x := by
  rw [pnat_denom, mk_pnat_eq, num_denom]
#align rat.mk_pnat_pnat_denom_eq [anonymous]

#print Rat.pnatDen_eq_iff_den_eq /-
theorem pnatDen_eq_iff_den_eq {x : ℚ} {n : ℕ+} : x.pnatDen = n ↔ x.den = ↑n :=
  Subtype.ext_iff
#align rat.pnat_denom_eq_iff_denom_eq Rat.pnatDen_eq_iff_den_eq
-/

#print Rat.pnatDen_one /-
@[simp]
theorem pnatDen_one : (1 : ℚ).pnatDen = 1 :=
  rfl
#align rat.pnat_denom_one Rat.pnatDen_one
-/

#print Rat.pnatDen_zero /-
@[simp]
theorem pnatDen_zero : (0 : ℚ).pnatDen = 1 :=
  rfl
#align rat.pnat_denom_zero Rat.pnatDen_zero
-/

end PnatDenom

end Rat

