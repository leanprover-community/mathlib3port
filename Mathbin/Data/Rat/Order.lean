/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.order
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Field.Defs
import Mathbin.Data.Rat.Basic
import Mathbin.Data.Int.Cast.Lemmas
import Mathbin.Tactic.AssertExists

/-!
# Order for Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define the order on `ℚ`, prove that `ℚ` is a discrete, linearly ordered field, and define
functions such as `abs` and `sqrt` that depend on this order.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering, sqrt, abs
-/


namespace Rat

variable (a b c : ℚ)

open Rat

#print Rat.Nonneg /-
/-- A rational number is called nonnegative if its numerator is nonnegative. -/
protected def Nonneg (r : ℚ) : Prop :=
  0 ≤ r.num
#align rat.nonneg Rat.Nonneg
-/

/- warning: rat.mk_nonneg -> Rat.divInt_nonneg is a dubious translation:
lean 3 declaration is
  forall (a : Int) {b : Int}, (LT.lt.{0} Int Int.hasLt (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) b) -> (Iff (Rat.Nonneg (Rat.mk a b)) (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) a))
but is expected to have type
  forall (a : Int) {b : Int}, (LT.lt.{0} Int Int.instLTInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) b) -> (Iff (Rat.Nonneg (Rat.divInt a b)) (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) a))
Case conversion may be inaccurate. Consider using '#align rat.mk_nonneg Rat.divInt_nonnegₓ'. -/
@[simp]
theorem divInt_nonneg (a : ℤ) {b : ℤ} (h : 0 < b) : (a /. b).Nonneg ↔ 0 ≤ a :=
  by
  generalize ha : a /. b = x; cases' x with n₁ d₁ h₁ c₁; rw [num_denom'] at ha
  simp [Rat.Nonneg]
  have d0 := Int.ofNat_lt.2 h₁
  have := (mk_eq (ne_of_gt h) (ne_of_gt d0)).1 ha
  constructor <;> intro h₂
  · apply nonneg_of_mul_nonneg_left _ d0
    rw [this]
    exact mul_nonneg h₂ (le_of_lt h)
  · apply nonneg_of_mul_nonneg_left _ h
    rw [← this]
    exact mul_nonneg h₂ (Int.ofNat_zero_le _)
#align rat.mk_nonneg Rat.divInt_nonneg

#print Rat.nonneg_add /-
protected theorem nonneg_add {a b} : Rat.Nonneg a → Rat.Nonneg b → Rat.Nonneg (a + b) :=
  (numDenCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenCasesOn' b) fun n₂ d₂ h₂ =>
      by
      have d₁0 : 0 < (d₁ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₁)
      have d₂0 : 0 < (d₂ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₂)
      simp [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0]
      intro n₁0 n₂0
      apply add_nonneg <;> apply mul_nonneg <;> · first |assumption|apply Int.ofNat_zero_le
#align rat.nonneg_add Rat.nonneg_add
-/

#print Rat.nonneg_mul /-
protected theorem nonneg_mul {a b} : Rat.Nonneg a → Rat.Nonneg b → Rat.Nonneg (a * b) :=
  (numDenCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenCasesOn' b) fun n₂ d₂ h₂ =>
      by
      have d₁0 : 0 < (d₁ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₁)
      have d₂0 : 0 < (d₂ : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h₂)
      simp (config := { contextual := true }) [d₁0, d₂0, h₁, h₂, mul_pos d₁0 d₂0, mul_nonneg]
#align rat.nonneg_mul Rat.nonneg_mul
-/

#print Rat.nonneg_antisymm /-
protected theorem nonneg_antisymm {a} : Rat.Nonneg a → Rat.Nonneg (-a) → a = 0 :=
  (numDenCasesOn' a) fun n d h =>
    by
    have d0 : 0 < (d : ℤ) := Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h)
    simp [d0, h]
    exact fun h₁ h₂ => le_antisymm h₂ h₁
#align rat.nonneg_antisymm Rat.nonneg_antisymm
-/

#print Rat.nonneg_total /-
protected theorem nonneg_total : Rat.Nonneg a ∨ Rat.Nonneg (-a) := by
  cases' a with n <;> exact Or.imp_right neg_nonneg_of_nonpos (le_total 0 n)
#align rat.nonneg_total Rat.nonneg_total
-/

#print Rat.decidableNonneg /-
instance decidableNonneg : Decidable (Rat.Nonneg a) := by
  cases a <;> unfold Rat.Nonneg <;> infer_instance
#align rat.decidable_nonneg Rat.decidableNonneg
-/

#print Rat.le' /-
/-- Relation `a ≤ b` on `ℚ` defined as `a ≤ b ↔ rat.nonneg (b - a)`. Use `a ≤ b` instead of
`rat.le a b`. -/
protected def le' (a b : ℚ) :=
  Rat.Nonneg (b - a)
#align rat.le Rat.le'
-/

instance : LE ℚ :=
  ⟨Rat.le'⟩

instance decidableLe : DecidableRel ((· ≤ ·) : ℚ → ℚ → Prop)
  | a, b => show Decidable (Rat.Nonneg (b - a)) by infer_instance
#align rat.decidable_le Rat.decidableLe

/- warning: rat.le_def -> Rat.le_def is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int} {c : Int} {d : Int}, (LT.lt.{0} Int Int.hasLt (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) b) -> (LT.lt.{0} Int Int.hasLt (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) d) -> (Iff (LE.le.{0} Rat Rat.hasLe (Rat.mk a b) (Rat.mk c d)) (LE.le.{0} Int Int.hasLe (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) a d) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) c b)))
but is expected to have type
  forall {a : Int} {b : Int} {c : Int} {d : Int}, (LT.lt.{0} Int Int.instLTInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) b) -> (LT.lt.{0} Int Int.instLTInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) d) -> (Iff (LE.le.{0} Rat Rat.instLERat (Rat.divInt a b) (Rat.divInt c d)) (LE.le.{0} Int Int.instLEInt (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) a d) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) c b)))
Case conversion may be inaccurate. Consider using '#align rat.le_def Rat.le_defₓ'. -/
protected theorem le_def {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  show Rat.Nonneg _ ↔ _
  rw [← sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, mul_pos d0 b0]
#align rat.le_def Rat.le_def

/- warning: rat.le_refl -> Rat.le_refl is a dubious translation:
lean 3 declaration is
  forall (a : Rat), LE.le.{0} Rat Rat.hasLe a a
but is expected to have type
  forall (a : Rat), LE.le.{0} Rat Rat.instLERat a a
Case conversion may be inaccurate. Consider using '#align rat.le_refl Rat.le_reflₓ'. -/
protected theorem le_refl : a ≤ a :=
  show Rat.Nonneg (a - a) by rw [sub_self] <;> exact le_refl (0 : ℤ)
#align rat.le_refl Rat.le_refl

/- warning: rat.le_total -> Rat.le_total is a dubious translation:
lean 3 declaration is
  forall (a : Rat) (b : Rat), Or (LE.le.{0} Rat Rat.hasLe a b) (LE.le.{0} Rat Rat.hasLe b a)
but is expected to have type
  forall (a : Rat) (b : Rat), Or (LE.le.{0} Rat Rat.instLERat a b) (LE.le.{0} Rat Rat.instLERat b a)
Case conversion may be inaccurate. Consider using '#align rat.le_total Rat.le_totalₓ'. -/
protected theorem le_total : a ≤ b ∨ b ≤ a := by
  have := Rat.nonneg_total (b - a) <;> rwa [neg_sub] at this
#align rat.le_total Rat.le_total

/- warning: rat.le_antisymm -> Rat.le_antisymm is a dubious translation:
lean 3 declaration is
  forall {a : Rat} {b : Rat}, (LE.le.{0} Rat Rat.hasLe a b) -> (LE.le.{0} Rat Rat.hasLe b a) -> (Eq.{1} Rat a b)
but is expected to have type
  forall {a : Rat} {b : Rat}, (LE.le.{0} Rat Rat.instLERat a b) -> (LE.le.{0} Rat Rat.instLERat b a) -> (Eq.{1} Rat a b)
Case conversion may be inaccurate. Consider using '#align rat.le_antisymm Rat.le_antisymmₓ'. -/
protected theorem le_antisymm {a b : ℚ} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  by
  have := eq_neg_of_add_eq_zero_left (Rat.nonneg_antisymm hba <| by rwa [← sub_eq_add_neg, neg_sub])
  rwa [neg_neg] at this
#align rat.le_antisymm Rat.le_antisymm

/- warning: rat.le_trans -> Rat.le_trans is a dubious translation:
lean 3 declaration is
  forall {a : Rat} {b : Rat} {c : Rat}, (LE.le.{0} Rat Rat.hasLe a b) -> (LE.le.{0} Rat Rat.hasLe b c) -> (LE.le.{0} Rat Rat.hasLe a c)
but is expected to have type
  forall {a : Rat} {b : Rat} {c : Rat}, (LE.le.{0} Rat Rat.instLERat a b) -> (LE.le.{0} Rat Rat.instLERat b c) -> (LE.le.{0} Rat Rat.instLERat a c)
Case conversion may be inaccurate. Consider using '#align rat.le_trans Rat.le_transₓ'. -/
protected theorem le_trans {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  by
  have : Rat.Nonneg (b - a + (c - b)) := Rat.nonneg_add hab hbc
  simpa [sub_eq_add_neg, add_comm, add_left_comm]
#align rat.le_trans Rat.le_trans

instance : LinearOrder ℚ where
  le := Rat.le'
  le_refl := Rat.le_refl
  le_trans := @Rat.le_trans
  le_antisymm := @Rat.le_antisymm
  le_total := Rat.le_total
  DecidableEq := by infer_instance
  decidableLe a b := Rat.decidableNonneg (b - a)

-- Extra instances to short-circuit type class resolution
instance : LT ℚ := by infer_instance

instance : DistribLattice ℚ := by infer_instance

instance : Lattice ℚ := by infer_instance

instance : SemilatticeInf ℚ := by infer_instance

instance : SemilatticeSup ℚ := by infer_instance

instance : HasInf ℚ := by infer_instance

instance : HasSup ℚ := by infer_instance

instance : PartialOrder ℚ := by infer_instance

instance : Preorder ℚ := by infer_instance

/- warning: rat.le_def' -> Rat.le_def' is a dubious translation:
lean 3 declaration is
  forall {p : Rat} {q : Rat}, Iff (LE.le.{0} Rat Rat.hasLe p q) (LE.le.{0} Int Int.hasLe (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (Rat.num p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den q))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) (Rat.num q) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den p))))
but is expected to have type
  forall {p : Rat} {q : Rat}, Iff (LE.le.{0} Rat Rat.instLERat p q) (LE.le.{0} Int Int.instLEInt (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Rat.num p) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den q))) (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) (Rat.num q) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den p))))
Case conversion may be inaccurate. Consider using '#align rat.le_def' Rat.le_def'ₓ'. -/
protected theorem le_def' {p q : ℚ} : p ≤ q ↔ p.num * q.denom ≤ q.num * p.denom :=
  by
  rw [← @num_denom q, ← @num_denom p]
  conv_rhs => simp only [num_denom]
  exact Rat.le_def (by exact_mod_cast p.pos) (by exact_mod_cast q.pos)
#align rat.le_def' Rat.le_def'

#print Rat.lt_def /-
protected theorem lt_def {p q : ℚ} : p < q ↔ p.num * q.denom < q.num * p.denom :=
  by
  rw [lt_iff_le_and_ne, Rat.le_def']
  suffices p ≠ q ↔ p.num * q.denom ≠ q.num * p.denom
    by
    constructor <;> intro h
    · exact lt_iff_le_and_ne.elim_right ⟨h.left, this.elim_left h.right⟩
    · have tmp := lt_iff_le_and_ne.elim_left h
      exact ⟨tmp.left, this.elim_right tmp.right⟩
  exact not_iff_not.elim_right eq_iff_mul_eq_mul
#align rat.lt_def Rat.lt_def
-/

/- warning: rat.nonneg_iff_zero_le -> Rat.nonneg_iff_zero_le is a dubious translation:
lean 3 declaration is
  forall {a : Rat}, Iff (Rat.Nonneg a) (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) a)
but is expected to have type
  forall {a : Rat}, Iff (Rat.Nonneg a) (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) a)
Case conversion may be inaccurate. Consider using '#align rat.nonneg_iff_zero_le Rat.nonneg_iff_zero_leₓ'. -/
theorem nonneg_iff_zero_le {a} : Rat.Nonneg a ↔ 0 ≤ a :=
  show Rat.Nonneg a ↔ Rat.Nonneg (a - 0) by simp
#align rat.nonneg_iff_zero_le Rat.nonneg_iff_zero_le

/- warning: rat.num_nonneg_iff_zero_le -> Rat.num_nonneg_iff_zero_le is a dubious translation:
lean 3 declaration is
  forall {a : Rat}, Iff (LE.le.{0} Int Int.hasLe (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero))) (Rat.num a)) (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) a)
but is expected to have type
  forall {a : Rat}, Iff (LE.le.{0} Int Int.instLEInt (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) (Rat.num a)) (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) a)
Case conversion may be inaccurate. Consider using '#align rat.num_nonneg_iff_zero_le Rat.num_nonneg_iff_zero_leₓ'. -/
theorem num_nonneg_iff_zero_le : ∀ {a : ℚ}, 0 ≤ a.num ↔ 0 ≤ a
  | ⟨n, d, h, c⟩ => @nonneg_iff_zero_le ⟨n, d, h, c⟩
#align rat.num_nonneg_iff_zero_le Rat.num_nonneg_iff_zero_le

/- warning: rat.add_le_add_left -> Rat.add_le_add_left is a dubious translation:
lean 3 declaration is
  forall {a : Rat} {b : Rat} {c : Rat}, Iff (LE.le.{0} Rat Rat.hasLe (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) c a) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) c b)) (LE.le.{0} Rat Rat.hasLe a b)
but is expected to have type
  forall {a : Rat} {b : Rat} {c : Rat}, Iff (LE.le.{0} Rat Rat.instLERat (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) c a) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) c b)) (LE.le.{0} Rat Rat.instLERat a b)
Case conversion may be inaccurate. Consider using '#align rat.add_le_add_left Rat.add_le_add_leftₓ'. -/
protected theorem add_le_add_left {a b c : ℚ} : c + a ≤ c + b ↔ a ≤ b := by
  unfold LE.le Rat.le' <;> rw [add_sub_add_left_eq_sub]
#align rat.add_le_add_left Rat.add_le_add_left

/- warning: rat.mul_nonneg -> Rat.mul_nonneg is a dubious translation:
lean 3 declaration is
  forall {a : Rat} {b : Rat}, (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) a) -> (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) b) -> (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.hasMul) a b))
but is expected to have type
  forall {a : Rat} {b : Rat}, (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) a) -> (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) b) -> (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) (HMul.hMul.{0, 0, 0} Rat Rat Rat (instHMul.{0} Rat Rat.instMulRat) a b))
Case conversion may be inaccurate. Consider using '#align rat.mul_nonneg Rat.mul_nonnegₓ'. -/
protected theorem mul_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  rw [← nonneg_iff_zero_le] at ha hb⊢ <;> exact Rat.nonneg_mul ha hb
#align rat.mul_nonneg Rat.mul_nonneg

instance : LinearOrderedField ℚ :=
  { Rat.field, Rat.linearOrder,
    Rat.semiring with
    zero_le_one := by decide
    add_le_add_left := fun a b ab c => Rat.add_le_add_left.2 ab
    mul_pos := fun a b ha hb =>
      lt_of_le_of_ne (Rat.mul_nonneg (le_of_lt ha) (le_of_lt hb))
        (mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm).symm }

-- Extra instances to short-circuit type class resolution
instance : LinearOrderedCommRing ℚ := by infer_instance

instance : LinearOrderedRing ℚ := by infer_instance

instance : OrderedRing ℚ := by infer_instance

instance : LinearOrderedSemiring ℚ := by infer_instance

instance : OrderedSemiring ℚ := by infer_instance

instance : LinearOrderedAddCommGroup ℚ := by infer_instance

instance : OrderedAddCommGroup ℚ := by infer_instance

instance : OrderedCancelAddCommMonoid ℚ := by infer_instance

instance : OrderedAddCommMonoid ℚ := by infer_instance

#print Rat.num_pos_iff_pos /-
theorem num_pos_iff_pos {a : ℚ} : 0 < a.num ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le <| by
    simpa [(by cases a <;> rfl : (-a).num = -a.num)] using @num_nonneg_iff_zero_le (-a)
#align rat.num_pos_iff_pos Rat.num_pos_iff_pos
-/

#print Rat.div_lt_div_iff_mul_lt_mul /-
theorem div_lt_div_iff_mul_lt_mul {a b c d : ℤ} (b_pos : 0 < b) (d_pos : 0 < d) :
    (a : ℚ) / b < c / d ↔ a * d < c * b :=
  by
  simp only [lt_iff_le_not_le]
  apply and_congr
  · simp [div_num_denom, Rat.le_def b_pos d_pos]
  · apply not_congr
    simp [div_num_denom, Rat.le_def d_pos b_pos]
#align rat.div_lt_div_iff_mul_lt_mul Rat.div_lt_div_iff_mul_lt_mul
-/

#print Rat.lt_one_iff_num_lt_denom /-
theorem lt_one_iff_num_lt_denom {q : ℚ} : q < 1 ↔ q.num < q.denom := by simp [Rat.lt_def]
#align rat.lt_one_iff_num_lt_denom Rat.lt_one_iff_num_lt_denom
-/

/- warning: rat.abs_def -> Rat.abs_def is a dubious translation:
lean 3 declaration is
  forall (q : Rat), Eq.{1} Rat (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup) q) (Rat.mk ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Int.natAbs (Rat.num q))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) (Rat.den q)))
but is expected to have type
  forall (q : Rat), Eq.{1} Rat (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat) q) (Rat.divInt (Nat.cast.{0} Int Int.instNatCastInt (Int.natAbs (Rat.num q))) (Nat.cast.{0} Int Int.instNatCastInt (Rat.den q)))
Case conversion may be inaccurate. Consider using '#align rat.abs_def Rat.abs_defₓ'. -/
theorem abs_def (q : ℚ) : |q| = q.num.natAbs /. q.denom :=
  by
  cases' le_total q 0 with hq hq
  · rw [abs_of_nonpos hq]
    rw [← @num_denom q, ← mk_zero_one, Rat.le_def (Int.coe_nat_pos.2 q.pos) zero_lt_one, mul_one,
      zero_mul] at hq
    rw [Int.ofNat_natAbs_of_nonpos hq, ← neg_def, num_denom]
  · rw [abs_of_nonneg hq]
    rw [← @num_denom q, ← mk_zero_one, Rat.le_def zero_lt_one (Int.coe_nat_pos.2 q.pos), mul_one,
      zero_mul] at hq
    rw [Int.natAbs_of_nonneg hq, num_denom]
#align rat.abs_def Rat.abs_def

end Rat

-- We make some assertions here about declarations that do not need to be in the import dependencies
-- for this file, but have been in the past.
assert_not_exists fintype

assert_not_exists Set.Icc

assert_not_exists GaloisConnection

-- These are less significant, but should not be relaxed until at least after port to Lean 4.
assert_not_exists LinearOrderedCommGroupWithZero

-- This one doesn't exist anywhere!
-- assert_not_exists positive.add_comm_semigroup
