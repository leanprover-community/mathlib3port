/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes

! This file was ported from Lean 3 source module ring_theory.multiplicity
! leanprover-community/mathlib commit e8638a0fcaf73e4500469f368ef9494e495099b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Associated
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.RingTheory.Valuation.Basic

/-!
# Multiplicity of a divisor

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For a commutative monoid, this file introduces the notion of multiplicity of a divisor and proves
several basic results on it.

## Main definitions

* `multiplicity a b`: for two elements `a` and `b` of a commutative monoid returns the largest
  number `n` such that `a ^ n ∣ b` or infinity, written `⊤`, if `a ^ n ∣ b` for all natural numbers
  `n`.
* `multiplicity.finite a b`: a predicate denoting that the multiplicity of `a` in `b` is finite.
-/


variable {α : Type _}

open Nat Part

open BigOperators

#print multiplicity /-
/-- `multiplicity a b` returns the largest natural number `n` such that
  `a ^ n ∣ b`, as an `part_enat` or natural with infinity. If `∀ n, a ^ n ∣ b`,
  then it returns `⊤`-/
def multiplicity [Monoid α] [DecidableRel ((· ∣ ·) : α → α → Prop)] (a b : α) : PartENat :=
  PartENat.find fun n => ¬a ^ (n + 1) ∣ b
#align multiplicity multiplicity
-/

namespace multiplicity

section Monoid

variable [Monoid α]

#print multiplicity.Finite /-
/-- `multiplicity.finite a b` indicates that the multiplicity of `a` in `b` is finite. -/
@[reducible]
def Finite (a b : α) : Prop :=
  ∃ n : ℕ, ¬a ^ (n + 1) ∣ b
#align multiplicity.finite multiplicity.Finite
-/

#print multiplicity.finite_iff_dom /-
theorem finite_iff_dom [DecidableRel ((· ∣ ·) : α → α → Prop)] {a b : α} :
    Finite a b ↔ (multiplicity a b).Dom :=
  Iff.rfl
#align multiplicity.finite_iff_dom multiplicity.finite_iff_dom
-/

#print multiplicity.finite_def /-
theorem finite_def {a b : α} : Finite a b ↔ ∃ n : ℕ, ¬a ^ (n + 1) ∣ b :=
  Iff.rfl
#align multiplicity.finite_def multiplicity.finite_def
-/

/- warning: multiplicity.not_dvd_one_of_finite_one_right -> multiplicity.not_dvd_one_of_finite_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α}, (multiplicity.Finite.{u1} α _inst_1 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))) -> (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α}, (multiplicity.Finite.{u1} α _inst_1 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))) -> (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align multiplicity.not_dvd_one_of_finite_one_right multiplicity.not_dvd_one_of_finite_one_rightₓ'. -/
theorem not_dvd_one_of_finite_one_right {a : α} : Finite a 1 → ¬a ∣ 1 := fun ⟨n, hn⟩ ⟨d, hd⟩ =>
  hn ⟨d ^ (n + 1), (pow_mul_pow_eq_one (n + 1) hd.symm).symm⟩
#align multiplicity.not_dvd_one_of_finite_one_right multiplicity.not_dvd_one_of_finite_one_right

/- warning: multiplicity.int.coe_nat_multiplicity -> multiplicity.Int.coe_nat_multiplicity is a dubious translation:
lean 3 declaration is
  forall (a : Nat) (b : Nat), Eq.{1} PartENat (multiplicity.{0} Int Int.monoid (fun (a : Int) (b : Int) => Int.decidableDvd a b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) b)) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) a b)
but is expected to have type
  forall (a : Nat) (b : Nat), Eq.{1} PartENat (multiplicity.{0} Int Int.instMonoidInt (fun (a : Int) (b : Int) => Int.decidableDvd a b) (Nat.cast.{0} Int instNatCastInt a) (Nat.cast.{0} Int instNatCastInt b)) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) a b)
Case conversion may be inaccurate. Consider using '#align multiplicity.int.coe_nat_multiplicity multiplicity.Int.coe_nat_multiplicityₓ'. -/
@[norm_cast]
theorem Int.coe_nat_multiplicity (a b : ℕ) : multiplicity (a : ℤ) (b : ℤ) = multiplicity a b :=
  by
  apply Part.ext'
  · repeat' rw [← finite_iff_dom, finite_def]
    norm_cast
  · intro h1 h2
    apply _root_.le_antisymm <;>
      · apply Nat.find_mono
        norm_cast
        simp
#align multiplicity.int.coe_nat_multiplicity multiplicity.Int.coe_nat_multiplicity

#print multiplicity.not_finite_iff_forall /-
theorem not_finite_iff_forall {a b : α} : ¬Finite a b ↔ ∀ n : ℕ, a ^ n ∣ b :=
  ⟨fun h n =>
    Nat.casesOn n
      (by
        rw [pow_zero]
        exact one_dvd _)
      (by simpa [Finite, Classical.not_not] using h),
    by simp [Finite, multiplicity, Classical.not_not] <;> tauto⟩
#align multiplicity.not_finite_iff_forall multiplicity.not_finite_iff_forall
-/

#print multiplicity.not_unit_of_finite /-
theorem not_unit_of_finite {a b : α} (h : Finite a b) : ¬IsUnit a :=
  let ⟨n, hn⟩ := h
  hn ∘ IsUnit.dvd ∘ IsUnit.pow (n + 1)
#align multiplicity.not_unit_of_finite multiplicity.not_unit_of_finite
-/

/- warning: multiplicity.finite_of_finite_mul_right -> multiplicity.finite_of_finite_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} {c : α}, (multiplicity.Finite.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b c)) -> (multiplicity.Finite.{u1} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} {c : α}, (multiplicity.Finite.{u1} α _inst_1 a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b c)) -> (multiplicity.Finite.{u1} α _inst_1 a b)
Case conversion may be inaccurate. Consider using '#align multiplicity.finite_of_finite_mul_right multiplicity.finite_of_finite_mul_rightₓ'. -/
theorem finite_of_finite_mul_right {a b c : α} : Finite a (b * c) → Finite a b := fun ⟨n, hn⟩ =>
  ⟨n, fun h => hn (h.trans (dvd_mul_right _ _))⟩
#align multiplicity.finite_of_finite_mul_right multiplicity.finite_of_finite_mul_right

variable [DecidableRel ((· ∣ ·) : α → α → Prop)]

/- warning: multiplicity.pow_dvd_of_le_multiplicity -> multiplicity.pow_dvd_of_le_multiplicity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)))] {a : α} {b : α} {k : Nat}, (LE.le.{0} PartENat PartENat.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) k) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b)) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a k) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.761 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.763 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) x._@.Mathlib.RingTheory.Multiplicity._hyg.761 x._@.Mathlib.RingTheory.Multiplicity._hyg.763)] {a : α} {b : α} {k : Nat}, (LE.le.{0} PartENat PartENat.instLEPartENat (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) k) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b)) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a k) b)
Case conversion may be inaccurate. Consider using '#align multiplicity.pow_dvd_of_le_multiplicity multiplicity.pow_dvd_of_le_multiplicityₓ'. -/
theorem pow_dvd_of_le_multiplicity {a b : α} {k : ℕ} :
    (k : PartENat) ≤ multiplicity a b → a ^ k ∣ b :=
  by
  rw [← PartENat.some_eq_natCast]
  exact
    Nat.casesOn k
      (fun _ => by
        rw [pow_zero]
        exact one_dvd _)
      fun k ⟨h₁, h₂⟩ => by_contradiction fun hk => Nat.find_min _ (lt_of_succ_le (h₂ ⟨k, hk⟩)) hk
#align multiplicity.pow_dvd_of_le_multiplicity multiplicity.pow_dvd_of_le_multiplicity

#print multiplicity.pow_multiplicity_dvd /-
theorem pow_multiplicity_dvd {a b : α} (h : Finite a b) : a ^ get (multiplicity a b) h ∣ b :=
  pow_dvd_of_le_multiplicity (by rw [PartENat.natCast_get])
#align multiplicity.pow_multiplicity_dvd multiplicity.pow_multiplicity_dvd
-/

/- warning: multiplicity.is_greatest -> multiplicity.is_greatest is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)))] {a : α} {b : α} {m : Nat}, (LT.lt.{0} PartENat (Preorder.toLT.{0} PartENat (PartialOrder.toPreorder.{0} PartENat PartENat.partialOrder)) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) m)) -> (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a m) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.1017 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.1019 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) x._@.Mathlib.RingTheory.Multiplicity._hyg.1017 x._@.Mathlib.RingTheory.Multiplicity._hyg.1019)] {a : α} {b : α} {m : Nat}, (LT.lt.{0} PartENat (Preorder.toLT.{0} PartENat (PartialOrder.toPreorder.{0} PartENat PartENat.partialOrder)) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) m)) -> (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a m) b))
Case conversion may be inaccurate. Consider using '#align multiplicity.is_greatest multiplicity.is_greatestₓ'. -/
theorem is_greatest {a b : α} {m : ℕ} (hm : multiplicity a b < m) : ¬a ^ m ∣ b := fun h => by
  rw [PartENat.lt_coe_iff] at hm <;> exact Nat.find_spec hm.fst ((pow_dvd_pow _ hm.snd).trans h)
#align multiplicity.is_greatest multiplicity.is_greatest

#print multiplicity.is_greatest' /-
theorem is_greatest' {a b : α} {m : ℕ} (h : Finite a b) (hm : get (multiplicity a b) h < m) :
    ¬a ^ m ∣ b :=
  is_greatest (by rwa [← PartENat.coe_lt_coe, PartENat.natCast_get] at hm)
#align multiplicity.is_greatest' multiplicity.is_greatest'
-/

#print multiplicity.pos_of_dvd /-
theorem pos_of_dvd {a b : α} (hfin : Finite a b) (hdiv : a ∣ b) : 0 < (multiplicity a b).get hfin :=
  by
  refine' zero_lt_iff.2 fun h => _
  simpa [hdiv] using is_greatest' hfin (lt_one_iff.mpr h)
#align multiplicity.pos_of_dvd multiplicity.pos_of_dvd
-/

/- warning: multiplicity.unique -> multiplicity.unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)))] {a : α} {b : α} {k : Nat}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a k) b) -> (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) b)) -> (Eq.{1} PartENat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) k) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.1289 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.1291 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) x._@.Mathlib.RingTheory.Multiplicity._hyg.1289 x._@.Mathlib.RingTheory.Multiplicity._hyg.1291)] {a : α} {b : α} {k : Nat}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a k) b) -> (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) b)) -> (Eq.{1} PartENat (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) k) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b))
Case conversion may be inaccurate. Consider using '#align multiplicity.unique multiplicity.uniqueₓ'. -/
theorem unique {a b : α} {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    (k : PartENat) = multiplicity a b :=
  le_antisymm (le_of_not_gt fun hk' => is_greatest hk' hk) <|
    by
    have : Finite a b := ⟨k, hsucc⟩
    rw [PartENat.le_coe_iff]
    exact ⟨this, Nat.find_min' _ hsucc⟩
#align multiplicity.unique multiplicity.unique

#print multiplicity.unique' /-
theorem unique' {a b : α} {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    k = get (multiplicity a b) ⟨k, hsucc⟩ := by
  rw [← PartENat.natCast_inj, PartENat.natCast_get, Unique hk hsucc]
#align multiplicity.unique' multiplicity.unique'
-/

/- warning: multiplicity.le_multiplicity_of_pow_dvd -> multiplicity.le_multiplicity_of_pow_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)))] {a : α} {b : α} {k : Nat}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a k) b) -> (LE.le.{0} PartENat PartENat.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) k) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.1541 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.1543 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) x._@.Mathlib.RingTheory.Multiplicity._hyg.1541 x._@.Mathlib.RingTheory.Multiplicity._hyg.1543)] {a : α} {b : α} {k : Nat}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a k) b) -> (LE.le.{0} PartENat PartENat.instLEPartENat (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) k) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b))
Case conversion may be inaccurate. Consider using '#align multiplicity.le_multiplicity_of_pow_dvd multiplicity.le_multiplicity_of_pow_dvdₓ'. -/
theorem le_multiplicity_of_pow_dvd {a b : α} {k : ℕ} (hk : a ^ k ∣ b) :
    (k : PartENat) ≤ multiplicity a b :=
  le_of_not_gt fun hk' => is_greatest hk' hk
#align multiplicity.le_multiplicity_of_pow_dvd multiplicity.le_multiplicity_of_pow_dvd

/- warning: multiplicity.pow_dvd_iff_le_multiplicity -> multiplicity.pow_dvd_iff_le_multiplicity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)))] {a : α} {b : α} {k : Nat}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a k) b) (LE.le.{0} PartENat PartENat.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) k) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.1603 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.1605 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) x._@.Mathlib.RingTheory.Multiplicity._hyg.1603 x._@.Mathlib.RingTheory.Multiplicity._hyg.1605)] {a : α} {b : α} {k : Nat}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a k) b) (LE.le.{0} PartENat PartENat.instLEPartENat (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) k) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b))
Case conversion may be inaccurate. Consider using '#align multiplicity.pow_dvd_iff_le_multiplicity multiplicity.pow_dvd_iff_le_multiplicityₓ'. -/
theorem pow_dvd_iff_le_multiplicity {a b : α} {k : ℕ} :
    a ^ k ∣ b ↔ (k : PartENat) ≤ multiplicity a b :=
  ⟨le_multiplicity_of_pow_dvd, pow_dvd_of_le_multiplicity⟩
#align multiplicity.pow_dvd_iff_le_multiplicity multiplicity.pow_dvd_iff_le_multiplicity

/- warning: multiplicity.multiplicity_lt_iff_neg_dvd -> multiplicity.multiplicity_lt_iff_neg_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)))] {a : α} {b : α} {k : Nat}, Iff (LT.lt.{0} PartENat (Preorder.toLT.{0} PartENat (PartialOrder.toPreorder.{0} PartENat PartENat.partialOrder)) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) k)) (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a k) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.1665 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.1667 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) x._@.Mathlib.RingTheory.Multiplicity._hyg.1665 x._@.Mathlib.RingTheory.Multiplicity._hyg.1667)] {a : α} {b : α} {k : Nat}, Iff (LT.lt.{0} PartENat (Preorder.toLT.{0} PartENat (PartialOrder.toPreorder.{0} PartENat PartENat.partialOrder)) (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) k)) (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a k) b))
Case conversion may be inaccurate. Consider using '#align multiplicity.multiplicity_lt_iff_neg_dvd multiplicity.multiplicity_lt_iff_neg_dvdₓ'. -/
theorem multiplicity_lt_iff_neg_dvd {a b : α} {k : ℕ} :
    multiplicity a b < (k : PartENat) ↔ ¬a ^ k ∣ b := by rw [pow_dvd_iff_le_multiplicity, not_le]
#align multiplicity.multiplicity_lt_iff_neg_dvd multiplicity.multiplicity_lt_iff_neg_dvd

/- warning: multiplicity.eq_coe_iff -> multiplicity.eq_coe_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)))] {a : α} {b : α} {n : Nat}, Iff (Eq.{1} PartENat (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) n)) (And (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n) b) (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.1755 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.1757 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) x._@.Mathlib.RingTheory.Multiplicity._hyg.1755 x._@.Mathlib.RingTheory.Multiplicity._hyg.1757)] {a : α} {b : α} {n : Nat}, Iff (Eq.{1} PartENat (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) n)) (And (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n) b) (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) b)))
Case conversion may be inaccurate. Consider using '#align multiplicity.eq_coe_iff multiplicity.eq_coe_iffₓ'. -/
theorem eq_coe_iff {a b : α} {n : ℕ} :
    multiplicity a b = (n : PartENat) ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b :=
  by
  rw [← PartENat.some_eq_natCast]
  exact
    ⟨fun h =>
      let ⟨h₁, h₂⟩ := eq_some_iff.1 h
      h₂ ▸
        ⟨pow_multiplicity_dvd _,
          IsGreatest
            (by
              rw [PartENat.lt_coe_iff]
              exact ⟨h₁, lt_succ_self _⟩)⟩,
      fun h => eq_some_iff.2 ⟨⟨n, h.2⟩, Eq.symm <| unique' h.1 h.2⟩⟩
#align multiplicity.eq_coe_iff multiplicity.eq_coe_iff

#print multiplicity.eq_top_iff /-
theorem eq_top_iff {a b : α} : multiplicity a b = ⊤ ↔ ∀ n : ℕ, a ^ n ∣ b :=
  (PartENat.find_eq_top_iff _).trans <|
    by
    simp only [Classical.not_not]
    exact
      ⟨fun h n =>
        Nat.casesOn n
          (by
            rw [pow_zero]
            exact one_dvd _)
          fun n => h _,
        fun h n => h _⟩
#align multiplicity.eq_top_iff multiplicity.eq_top_iff
-/

#print multiplicity.isUnit_left /-
@[simp]
theorem isUnit_left {a : α} (b : α) (ha : IsUnit a) : multiplicity a b = ⊤ :=
  eq_top_iff.2 fun _ => IsUnit.dvd (ha.pow _)
#align multiplicity.is_unit_left multiplicity.isUnit_left
-/

/- warning: multiplicity.one_left -> multiplicity.one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)))] (b : α), Eq.{1} PartENat (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))) b) (Top.top.{0} PartENat PartENat.hasTop)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.2134 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.2136 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) x._@.Mathlib.RingTheory.Multiplicity._hyg.2134 x._@.Mathlib.RingTheory.Multiplicity._hyg.2136)] (b : α), Eq.{1} PartENat (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))) b) (Top.top.{0} PartENat PartENat.instTopPartENat)
Case conversion may be inaccurate. Consider using '#align multiplicity.one_left multiplicity.one_leftₓ'. -/
@[simp]
theorem one_left (b : α) : multiplicity 1 b = ⊤ :=
  isUnit_left b isUnit_one
#align multiplicity.one_left multiplicity.one_left

/- warning: multiplicity.get_one_right -> multiplicity.get_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)))] {a : α} (ha : multiplicity.Finite.{u1} α _inst_1 a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))), Eq.{1} Nat (Part.get.{0} Nat (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))))) ha) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.2176 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.2178 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) x._@.Mathlib.RingTheory.Multiplicity._hyg.2176 x._@.Mathlib.RingTheory.Multiplicity._hyg.2178)] {a : α} (ha : multiplicity.Finite.{u1} α _inst_1 a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))), Eq.{1} Nat (Part.get.{0} Nat (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1)))) ha) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align multiplicity.get_one_right multiplicity.get_one_rightₓ'. -/
@[simp]
theorem get_one_right {a : α} (ha : Finite a 1) : get (multiplicity a 1) ha = 0 :=
  by
  rw [PartENat.get_eq_iff_eq_coe, eq_coe_iff, pow_zero]
  simp [not_dvd_one_of_finite_one_right ha]
#align multiplicity.get_one_right multiplicity.get_one_right

#print multiplicity.unit_left /-
@[simp]
theorem unit_left (a : α) (u : αˣ) : multiplicity (u : α) a = ⊤ :=
  isUnit_left a u.IsUnit
#align multiplicity.unit_left multiplicity.unit_left
-/

#print multiplicity.multiplicity_eq_zero /-
theorem multiplicity_eq_zero {a b : α} : multiplicity a b = 0 ↔ ¬a ∣ b :=
  by
  rw [← Nat.cast_zero, eq_coe_iff]
  simp
#align multiplicity.multiplicity_eq_zero multiplicity.multiplicity_eq_zero
-/

#print multiplicity.multiplicity_ne_zero /-
theorem multiplicity_ne_zero {a b : α} : multiplicity a b ≠ 0 ↔ a ∣ b :=
  multiplicity_eq_zero.not_left
#align multiplicity.multiplicity_ne_zero multiplicity.multiplicity_ne_zero
-/

#print multiplicity.eq_top_iff_not_finite /-
theorem eq_top_iff_not_finite {a b : α} : multiplicity a b = ⊤ ↔ ¬Finite a b :=
  Part.eq_none_iff'
#align multiplicity.eq_top_iff_not_finite multiplicity.eq_top_iff_not_finite
-/

#print multiplicity.ne_top_iff_finite /-
theorem ne_top_iff_finite {a b : α} : multiplicity a b ≠ ⊤ ↔ Finite a b := by
  rw [Ne.def, eq_top_iff_not_finite, Classical.not_not]
#align multiplicity.ne_top_iff_finite multiplicity.ne_top_iff_finite
-/

#print multiplicity.lt_top_iff_finite /-
theorem lt_top_iff_finite {a b : α} : multiplicity a b < ⊤ ↔ Finite a b := by
  rw [lt_top_iff_ne_top, ne_top_iff_finite]
#align multiplicity.lt_top_iff_finite multiplicity.lt_top_iff_finite
-/

/- warning: multiplicity.exists_eq_pow_mul_and_not_dvd -> multiplicity.exists_eq_pow_mul_and_not_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)))] {a : α} {b : α} (hfin : multiplicity.Finite.{u1} α _inst_1 a b), Exists.{succ u1} α (fun (c : α) => And (Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a (Part.get.{0} Nat (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b) hfin)) c)) (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a c)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.2642 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.2644 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) x._@.Mathlib.RingTheory.Multiplicity._hyg.2642 x._@.Mathlib.RingTheory.Multiplicity._hyg.2644)] {a : α} {b : α} (hfin : multiplicity.Finite.{u1} α _inst_1 a b), Exists.{succ u1} α (fun (c : α) => And (Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a (Part.get.{0} Nat (multiplicity.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) a b) hfin)) c)) (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a c)))
Case conversion may be inaccurate. Consider using '#align multiplicity.exists_eq_pow_mul_and_not_dvd multiplicity.exists_eq_pow_mul_and_not_dvdₓ'. -/
theorem exists_eq_pow_mul_and_not_dvd {a b : α} (hfin : Finite a b) :
    ∃ c : α, b = a ^ (multiplicity a b).get hfin * c ∧ ¬a ∣ c :=
  by
  obtain ⟨c, hc⟩ := multiplicity.pow_multiplicity_dvd hfin
  refine' ⟨c, hc, _⟩
  rintro ⟨k, hk⟩
  rw [hk, ← mul_assoc, ← pow_succ'] at hc
  have h₁ : a ^ ((multiplicity a b).get hfin + 1) ∣ b := ⟨k, hc⟩
  exact (multiplicity.eq_coe_iff.1 (by simp)).2 h₁
#align multiplicity.exists_eq_pow_mul_and_not_dvd multiplicity.exists_eq_pow_mul_and_not_dvd

open Classical

#print multiplicity.multiplicity_le_multiplicity_iff /-
theorem multiplicity_le_multiplicity_iff {a b c d : α} :
    multiplicity a b ≤ multiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b → c ^ n ∣ d :=
  ⟨fun h n hab => pow_dvd_of_le_multiplicity (le_trans (le_multiplicity_of_pow_dvd hab) h), fun h =>
    if hab : Finite a b then by
      rw [← PartENat.natCast_get (finite_iff_dom.1 hab)] <;>
        exact le_multiplicity_of_pow_dvd (h _ (pow_multiplicity_dvd _))
    else by
      have : ∀ n : ℕ, c ^ n ∣ d := fun n => h n (not_finite_iff_forall.1 hab _)
      rw [eq_top_iff_not_finite.2 hab, eq_top_iff_not_finite.2 (not_finite_iff_forall.2 this)]⟩
#align multiplicity.multiplicity_le_multiplicity_iff multiplicity.multiplicity_le_multiplicity_iff
-/

#print multiplicity.multiplicity_eq_multiplicity_iff /-
theorem multiplicity_eq_multiplicity_iff {a b c d : α} :
    multiplicity a b = multiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b ↔ c ^ n ∣ d :=
  ⟨fun h n =>
    ⟨multiplicity_le_multiplicity_iff.mp h.le n, multiplicity_le_multiplicity_iff.mp h.ge n⟩,
    fun h =>
    le_antisymm (multiplicity_le_multiplicity_iff.mpr fun n => (h n).mp)
      (multiplicity_le_multiplicity_iff.mpr fun n => (h n).mpr)⟩
#align multiplicity.multiplicity_eq_multiplicity_iff multiplicity.multiplicity_eq_multiplicity_iff
-/

#print multiplicity.multiplicity_le_multiplicity_of_dvd_right /-
theorem multiplicity_le_multiplicity_of_dvd_right {a b c : α} (h : b ∣ c) :
    multiplicity a b ≤ multiplicity a c :=
  multiplicity_le_multiplicity_iff.2 fun n hb => hb.trans h
#align multiplicity.multiplicity_le_multiplicity_of_dvd_right multiplicity.multiplicity_le_multiplicity_of_dvd_right
-/

#print multiplicity.eq_of_associated_right /-
theorem eq_of_associated_right {a b c : α} (h : Associated b c) :
    multiplicity a b = multiplicity a c :=
  le_antisymm (multiplicity_le_multiplicity_of_dvd_right h.Dvd)
    (multiplicity_le_multiplicity_of_dvd_right h.symm.Dvd)
#align multiplicity.eq_of_associated_right multiplicity.eq_of_associated_right
-/

#print multiplicity.dvd_of_multiplicity_pos /-
theorem dvd_of_multiplicity_pos {a b : α} (h : (0 : PartENat) < multiplicity a b) : a ∣ b :=
  by
  rw [← pow_one a]
  apply pow_dvd_of_le_multiplicity
  simpa only [Nat.cast_one, PartENat.pos_iff_one_le] using h
#align multiplicity.dvd_of_multiplicity_pos multiplicity.dvd_of_multiplicity_pos
-/

#print multiplicity.dvd_iff_multiplicity_pos /-
theorem dvd_iff_multiplicity_pos {a b : α} : (0 : PartENat) < multiplicity a b ↔ a ∣ b :=
  ⟨dvd_of_multiplicity_pos, fun hdvd =>
    lt_of_le_of_ne (zero_le _) fun heq =>
      is_greatest
        (show multiplicity a b < ↑1 by
          simpa only [HEq, Nat.cast_zero] using part_enat.coe_lt_coe.mpr zero_lt_one)
        (by rwa [pow_one a])⟩
#align multiplicity.dvd_iff_multiplicity_pos multiplicity.dvd_iff_multiplicity_pos
-/

#print multiplicity.finite_nat_iff /-
theorem finite_nat_iff {a b : ℕ} : Finite a b ↔ a ≠ 1 ∧ 0 < b :=
  by
  rw [← not_iff_not, not_finite_iff_forall, not_and_or, Ne.def, Classical.not_not, not_lt,
    le_zero_iff]
  exact
    ⟨fun h =>
      or_iff_not_imp_right.2 fun hb =>
        have ha : a ≠ 0 := fun ha => by simpa [ha] using h 1
        by_contradiction fun ha1 : a ≠ 1 =>
          have ha_gt_one : 1 < a :=
            lt_of_not_ge fun ha' => by
              clear h
              revert ha ha1
              decide!
          not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero hb) (h b)) (lt_pow_self ha_gt_one b),
      fun h => by cases h <;> simp [*]⟩
#align multiplicity.finite_nat_iff multiplicity.finite_nat_iff
-/

alias dvd_iff_multiplicity_pos ↔ _ _root_.has_dvd.dvd.multiplicity_pos
#align has_dvd.dvd.multiplicity_pos Dvd.Dvd.multiplicity_pos

end Monoid

section CommMonoid

variable [CommMonoid α]

/- warning: multiplicity.finite_of_finite_mul_left -> multiplicity.finite_of_finite_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α} {c : α}, (multiplicity.Finite.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) b c)) -> (multiplicity.Finite.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α} {c : α}, (multiplicity.Finite.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) b c)) -> (multiplicity.Finite.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a c)
Case conversion may be inaccurate. Consider using '#align multiplicity.finite_of_finite_mul_left multiplicity.finite_of_finite_mul_leftₓ'. -/
theorem finite_of_finite_mul_left {a b c : α} : Finite a (b * c) → Finite a c := by
  rw [mul_comm] <;> exact finite_of_finite_mul_right
#align multiplicity.finite_of_finite_mul_left multiplicity.finite_of_finite_mul_left

variable [DecidableRel ((· ∣ ·) : α → α → Prop)]

#print multiplicity.isUnit_right /-
theorem isUnit_right {a b : α} (ha : ¬IsUnit a) (hb : IsUnit b) : multiplicity a b = 0 :=
  eq_coe_iff.2
    ⟨show a ^ 0 ∣ b by simp only [pow_zero, one_dvd],
      by
      rw [pow_one]
      exact fun h => mt (isUnit_of_dvd_unit h) ha hb⟩
#align multiplicity.is_unit_right multiplicity.isUnit_right
-/

/- warning: multiplicity.one_right -> multiplicity.one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))] {a : α}, (Not (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)) -> (Eq.{1} PartENat (multiplicity.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))) (OfNat.ofNat.{0} PartENat 0 (OfNat.mk.{0} PartENat 0 (Zero.zero.{0} PartENat PartENat.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.4001 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.4003 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) x._@.Mathlib.RingTheory.Multiplicity._hyg.4001 x._@.Mathlib.RingTheory.Multiplicity._hyg.4003)] {a : α}, (Not (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)) -> (Eq.{1} PartENat (multiplicity.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) (OfNat.ofNat.{0} PartENat 0 (Zero.toOfNat0.{0} PartENat PartENat.instZeroPartENat)))
Case conversion may be inaccurate. Consider using '#align multiplicity.one_right multiplicity.one_rightₓ'. -/
theorem one_right {a : α} (ha : ¬IsUnit a) : multiplicity a 1 = 0 :=
  isUnit_right ha isUnit_one
#align multiplicity.one_right multiplicity.one_right

#print multiplicity.unit_right /-
theorem unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : multiplicity a u = 0 :=
  isUnit_right ha u.IsUnit
#align multiplicity.unit_right multiplicity.unit_right
-/

open Classical

#print multiplicity.multiplicity_le_multiplicity_of_dvd_left /-
theorem multiplicity_le_multiplicity_of_dvd_left {a b c : α} (hdvd : a ∣ b) :
    multiplicity b c ≤ multiplicity a c :=
  multiplicity_le_multiplicity_iff.2 fun n h => (pow_dvd_pow_of_dvd hdvd n).trans h
#align multiplicity.multiplicity_le_multiplicity_of_dvd_left multiplicity.multiplicity_le_multiplicity_of_dvd_left
-/

#print multiplicity.eq_of_associated_left /-
theorem eq_of_associated_left {a b c : α} (h : Associated a b) :
    multiplicity b c = multiplicity a c :=
  le_antisymm (multiplicity_le_multiplicity_of_dvd_left h.Dvd)
    (multiplicity_le_multiplicity_of_dvd_left h.symm.Dvd)
#align multiplicity.eq_of_associated_left multiplicity.eq_of_associated_left
-/

alias dvd_iff_multiplicity_pos ↔ _ _root_.has_dvd.dvd.multiplicity_pos
#align has_dvd.dvd.multiplicity_pos Dvd.Dvd.multiplicity_pos

end CommMonoid

section MonoidWithZero

variable [MonoidWithZero α]

/- warning: multiplicity.ne_zero_of_finite -> multiplicity.ne_zero_of_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : α} {b : α}, (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a b) -> (Ne.{succ u1} α b (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] {a : α} {b : α}, (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) a b) -> (Ne.{succ u1} α b (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align multiplicity.ne_zero_of_finite multiplicity.ne_zero_of_finiteₓ'. -/
theorem ne_zero_of_finite {a b : α} (h : Finite a b) : b ≠ 0 :=
  let ⟨n, hn⟩ := h
  fun hb => by simpa [hb] using hn
#align multiplicity.ne_zero_of_finite multiplicity.ne_zero_of_finite

variable [DecidableRel ((· ∣ ·) : α → α → Prop)]

/- warning: multiplicity.zero -> multiplicity.zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α _inst_1))))] (a : α), Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))))))) (Top.top.{0} PartENat PartENat.hasTop)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.4287 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.4289 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α _inst_1))) x._@.Mathlib.RingTheory.Multiplicity._hyg.4287 x._@.Mathlib.RingTheory.Multiplicity._hyg.4289)] (a : α), Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1)))) (Top.top.{0} PartENat PartENat.instTopPartENat)
Case conversion may be inaccurate. Consider using '#align multiplicity.zero multiplicity.zeroₓ'. -/
@[simp]
protected theorem zero (a : α) : multiplicity a 0 = ⊤ :=
  Part.eq_none_iff.2 fun n ⟨⟨k, hk⟩, _⟩ => hk (dvd_zero _)
#align multiplicity.zero multiplicity.zero

/- warning: multiplicity.multiplicity_zero_eq_zero_of_ne_zero -> multiplicity.multiplicity_zero_eq_zero_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α _inst_1))))] (a : α), (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1))))))) -> (Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α _inst_1)))))) a) (OfNat.ofNat.{0} PartENat 0 (OfNat.mk.{0} PartENat 0 (Zero.zero.{0} PartENat PartENat.hasZero))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.4365 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.4367 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α _inst_1))) x._@.Mathlib.RingTheory.Multiplicity._hyg.4365 x._@.Mathlib.RingTheory.Multiplicity._hyg.4367)] (a : α), (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1)))) -> (Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α _inst_1))) a) (OfNat.ofNat.{0} PartENat 0 (Zero.toOfNat0.{0} PartENat PartENat.instZeroPartENat)))
Case conversion may be inaccurate. Consider using '#align multiplicity.multiplicity_zero_eq_zero_of_ne_zero multiplicity.multiplicity_zero_eq_zero_of_ne_zeroₓ'. -/
@[simp]
theorem multiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a ≠ 0) : multiplicity 0 a = 0 :=
  multiplicity.multiplicity_eq_zero.2 <| mt zero_dvd_iff.1 ha
#align multiplicity.multiplicity_zero_eq_zero_of_ne_zero multiplicity.multiplicity_zero_eq_zero_of_ne_zero

end MonoidWithZero

section CommMonoidWithZero

variable [CommMonoidWithZero α]

variable [DecidableRel ((· ∣ ·) : α → α → Prop)]

/- warning: multiplicity.multiplicity_mk_eq_multiplicity -> multiplicity.multiplicity_mk_eq_multiplicity is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))))] [_inst_3 : DecidableRel.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Dvd.Dvd.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (semigroupDvd.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (SemigroupWithZero.toSemigroup.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toSemigroupWithZero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (CommMonoidWithZero.toMonoidWithZero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.commMonoidWithZero.{u1} α _inst_1))))))] {a : α} {b : α}, Eq.{1} PartENat (multiplicity.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMonoid.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (CommMonoidWithZero.toMonoidWithZero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.commMonoidWithZero.{u1} α _inst_1))) (fun (a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (b : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) => _inst_3 a b) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) a) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) b)) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) (fun (a : α) (b : α) => _inst_2 a b) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.4452 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.4454 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) x._@.Mathlib.RingTheory.Multiplicity._hyg.4452 x._@.Mathlib.RingTheory.Multiplicity._hyg.4454)] [_inst_3 : DecidableRel.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.4478 : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (x._@.Mathlib.RingTheory.Multiplicity._hyg.4480 : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) => Dvd.dvd.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (semigroupDvd.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (SemigroupWithZero.toSemigroup.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toSemigroupWithZero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (CommMonoidWithZero.toMonoidWithZero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.4478 x._@.Mathlib.RingTheory.Multiplicity._hyg.4480)] {a : α} {b : α}, Eq.{1} PartENat (multiplicity.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (MonoidWithZero.toMonoid.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (CommMonoidWithZero.toMonoidWithZero.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α _inst_1))) (fun (a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) (b : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))) => _inst_3 a b) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) a) (Associates.mk.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) b)) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)) (fun (a : α) (b : α) => _inst_2 a b) a b)
Case conversion may be inaccurate. Consider using '#align multiplicity.multiplicity_mk_eq_multiplicity multiplicity.multiplicity_mk_eq_multiplicityₓ'. -/
theorem multiplicity_mk_eq_multiplicity
    [DecidableRel ((· ∣ ·) : Associates α → Associates α → Prop)] {a b : α} :
    multiplicity (Associates.mk a) (Associates.mk b) = multiplicity a b :=
  by
  by_cases h : Finite a b
  · rw [← PartENat.natCast_get (finite_iff_dom.mp h)]
    refine'
        (multiplicity.unique
            (show Associates.mk a ^ (multiplicity a b).get h ∣ Associates.mk b from _) _).symm <;>
      rw [← Associates.mk_pow, Associates.mk_dvd_mk]
    · exact pow_multiplicity_dvd h
    ·
      exact
        IsGreatest
          ((PartENat.lt_coe_iff _ _).mpr (Exists.intro (finite_iff_dom.mp h) (Nat.lt_succ_self _)))
  · suffices ¬Finite (Associates.mk a) (Associates.mk b)
      by
      rw [finite_iff_dom, PartENat.not_dom_iff_eq_top] at h this
      rw [h, this]
    refine'
      not_finite_iff_forall.mpr fun n =>
        by
        rw [← Associates.mk_pow, Associates.mk_dvd_mk]
        exact not_finite_iff_forall.mp h n
#align multiplicity.multiplicity_mk_eq_multiplicity multiplicity.multiplicity_mk_eq_multiplicity

end CommMonoidWithZero

section Semiring

variable [Semiring α] [DecidableRel ((· ∣ ·) : α → α → Prop)]

/- warning: multiplicity.min_le_multiplicity_add -> multiplicity.min_le_multiplicity_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)))))] {p : α} {a : α} {b : α}, LE.le.{0} PartENat PartENat.hasLe (LinearOrder.min.{0} PartENat PartENat.linearOrder (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (fun (a : α) (b : α) => _inst_2 a b) p a) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (fun (a : α) (b : α) => _inst_2 a b) p b)) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (fun (a : α) (b : α) => _inst_2 a b) p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.4899 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.4901 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)))) x._@.Mathlib.RingTheory.Multiplicity._hyg.4899 x._@.Mathlib.RingTheory.Multiplicity._hyg.4901)] {p : α} {a : α} {b : α}, LE.le.{0} PartENat PartENat.instLEPartENat (Min.min.{0} PartENat (LinearOrder.toMin.{0} PartENat PartENat.linearOrder) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (fun (a : α) (b : α) => _inst_2 a b) p a) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (fun (a : α) (b : α) => _inst_2 a b) p b)) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) (fun (a : α) (b : α) => _inst_2 a b) p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a b))
Case conversion may be inaccurate. Consider using '#align multiplicity.min_le_multiplicity_add multiplicity.min_le_multiplicity_addₓ'. -/
theorem min_le_multiplicity_add {p a b : α} :
    min (multiplicity p a) (multiplicity p b) ≤ multiplicity p (a + b) :=
  (le_total (multiplicity p a) (multiplicity p b)).elim
    (fun h => by
      rw [min_eq_left h, multiplicity_le_multiplicity_iff] <;>
        exact fun n hn => dvd_add hn (multiplicity_le_multiplicity_iff.1 h n hn))
    fun h => by
    rw [min_eq_right h, multiplicity_le_multiplicity_iff] <;>
      exact fun n hn => dvd_add (multiplicity_le_multiplicity_iff.1 h n hn) hn
#align multiplicity.min_le_multiplicity_add multiplicity.min_le_multiplicity_add

end Semiring

section Ring

variable [Ring α] [DecidableRel ((· ∣ ·) : α → α → Prop)]

/- warning: multiplicity.neg -> multiplicity.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))))] (a : α) (b : α), Eq.{1} PartENat (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) a (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1))))) b)) (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.5104 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.5106 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (Semiring.toNonUnitalSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.5104 x._@.Mathlib.RingTheory.Multiplicity._hyg.5106)] (a : α) (b : α), Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) a (Neg.neg.{u1} α (Ring.toNeg.{u1} α _inst_1) b)) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) a b)
Case conversion may be inaccurate. Consider using '#align multiplicity.neg multiplicity.negₓ'. -/
@[simp]
protected theorem neg (a b : α) : multiplicity a (-b) = multiplicity a b :=
  Part.ext' (by simp only [multiplicity, PartENat.find, dvd_neg]) fun h₁ h₂ =>
    PartENat.natCast_inj.1
      (by
        rw [PartENat.natCast_get] <;>
          exact
            Eq.symm
              (Unique (pow_multiplicity_dvd _).neg_right
                (mt dvd_neg.1 (is_greatest' _ (lt_succ_self _)))))
#align multiplicity.neg multiplicity.neg

/- warning: multiplicity.int.nat_abs -> multiplicity.Int.natAbs is a dubious translation:
lean 3 declaration is
  forall (a : Nat) (b : Int), Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) a (Int.natAbs b)) (multiplicity.{0} Int Int.monoid (fun (a : Int) (b : Int) => Int.decidableDvd a b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) a) b)
but is expected to have type
  forall (a : Nat) (b : Int), Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) a (Int.natAbs b)) (multiplicity.{0} Int Int.instMonoidInt (fun (a : Int) (b : Int) => Int.decidableDvd a b) (Nat.cast.{0} Int instNatCastInt a) b)
Case conversion may be inaccurate. Consider using '#align multiplicity.int.nat_abs multiplicity.Int.natAbsₓ'. -/
theorem Int.natAbs (a : ℕ) (b : ℤ) : multiplicity a b.natAbs = multiplicity (a : ℤ) b :=
  by
  cases' Int.natAbs_eq b with h h <;> conv_rhs => rw [h]
  · rw [int.coe_nat_multiplicity]
  · rw [multiplicity.neg, int.coe_nat_multiplicity]
#align multiplicity.int.nat_abs multiplicity.Int.natAbs

/- warning: multiplicity.multiplicity_add_of_gt -> multiplicity.multiplicity_add_of_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))))] {p : α} {a : α} {b : α}, (LT.lt.{0} PartENat (Preorder.toLT.{0} PartENat (PartialOrder.toPreorder.{0} PartENat PartENat.partialOrder)) (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p b) (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p a)) -> (Eq.{1} PartENat (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a b)) (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.5398 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.5400 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (Semiring.toNonUnitalSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.5398 x._@.Mathlib.RingTheory.Multiplicity._hyg.5400)] {p : α} {a : α} {b : α}, (LT.lt.{0} PartENat (Preorder.toLT.{0} PartENat (PartialOrder.toPreorder.{0} PartENat PartENat.partialOrder)) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p b) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p a)) -> (Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a b)) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p b))
Case conversion may be inaccurate. Consider using '#align multiplicity.multiplicity_add_of_gt multiplicity.multiplicity_add_of_gtₓ'. -/
theorem multiplicity_add_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a) :
    multiplicity p (a + b) = multiplicity p b :=
  by
  apply le_antisymm
  · apply PartENat.le_of_lt_add_one
    cases' part_enat.ne_top_iff.mp (PartENat.ne_top_of_lt h) with k hk
    rw [hk]
    rw_mod_cast [multiplicity_lt_iff_neg_dvd, dvd_add_right]
    intro h_dvd
    apply multiplicity.is_greatest _ h_dvd
    rw [hk]
    apply_mod_cast Nat.lt_succ_self
    rw [pow_dvd_iff_le_multiplicity, Nat.cast_add, ← hk, Nat.cast_one]
    exact PartENat.add_one_le_of_lt h
  · convert min_le_multiplicity_add
    rw [min_eq_right (le_of_lt h)]
#align multiplicity.multiplicity_add_of_gt multiplicity.multiplicity_add_of_gt

/- warning: multiplicity.multiplicity_sub_of_gt -> multiplicity.multiplicity_sub_of_gt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))))] {p : α} {a : α} {b : α}, (LT.lt.{0} PartENat (Preorder.toLT.{0} PartENat (PartialOrder.toPreorder.{0} PartENat PartENat.partialOrder)) (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p b) (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p a)) -> (Eq.{1} PartENat (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1)))))) a b)) (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.5831 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.5833 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (Semiring.toNonUnitalSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.5831 x._@.Mathlib.RingTheory.Multiplicity._hyg.5833)] {p : α} {a : α} {b : α}, (LT.lt.{0} PartENat (Preorder.toLT.{0} PartENat (PartialOrder.toPreorder.{0} PartENat PartENat.partialOrder)) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p b) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p a)) -> (Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) a b)) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p b))
Case conversion may be inaccurate. Consider using '#align multiplicity.multiplicity_sub_of_gt multiplicity.multiplicity_sub_of_gtₓ'. -/
theorem multiplicity_sub_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a) :
    multiplicity p (a - b) = multiplicity p b := by
  rw [sub_eq_add_neg, multiplicity_add_of_gt] <;> rwa [multiplicity.neg]
#align multiplicity.multiplicity_sub_of_gt multiplicity.multiplicity_sub_of_gt

/- warning: multiplicity.multiplicity_add_eq_min -> multiplicity.multiplicity_add_eq_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))))] {p : α} {a : α} {b : α}, (Ne.{1} PartENat (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p a) (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p b)) -> (Eq.{1} PartENat (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a b)) (LinearOrder.min.{0} PartENat PartENat.linearOrder (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p a) (multiplicity.{u1} α (Ring.toMonoid.{u1} α _inst_1) (fun (a : α) (b : α) => _inst_2 a b) p b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.5988 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.5990 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (Semiring.toNonUnitalSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.5988 x._@.Mathlib.RingTheory.Multiplicity._hyg.5990)] {p : α} {a : α} {b : α}, (Ne.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p a) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p b)) -> (Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a b)) (Min.min.{0} PartENat (LinearOrder.toMin.{0} PartENat PartENat.linearOrder) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p a) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p b)))
Case conversion may be inaccurate. Consider using '#align multiplicity.multiplicity_add_eq_min multiplicity.multiplicity_add_eq_minₓ'. -/
theorem multiplicity_add_eq_min {p a b : α} (h : multiplicity p a ≠ multiplicity p b) :
    multiplicity p (a + b) = min (multiplicity p a) (multiplicity p b) :=
  by
  rcases lt_trichotomy (multiplicity p a) (multiplicity p b) with (hab | hab | hab)
  · rw [add_comm, multiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [multiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab
#align multiplicity.multiplicity_add_eq_min multiplicity.multiplicity_add_eq_min

end Ring

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

/- warning: multiplicity.finite_mul_aux -> multiplicity.finite_mul_aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {n : Nat} {m : Nat} {a : α} {b : α}, (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) a)) -> (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) b)) -> (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n m) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {n : α} {m : α} {a : Nat} {b : Nat}, (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) n)) -> (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) b (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) m)) -> (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) n m))))
Case conversion may be inaccurate. Consider using '#align multiplicity.finite_mul_aux multiplicity.finite_mul_auxₓ'. -/
theorem finite_mul_aux {p : α} (hp : Prime p) :
    ∀ {n m : ℕ} {a b : α}, ¬p ^ (n + 1) ∣ a → ¬p ^ (m + 1) ∣ b → ¬p ^ (n + m + 1) ∣ a * b
  | n, m => fun a b ha hb ⟨s, hs⟩ =>
    have : p ∣ a * b := ⟨p ^ (n + m) * s, by simp [hs, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩
    (hp.2.2 a b this).elim
      (fun ⟨x, hx⟩ =>
        have hn0 : 0 < n :=
          Nat.pos_of_ne_zero fun hn0 => by clear _fun_match _fun_match <;> simpa [hx, hn0] using ha
        have wf : n - 1 < n := tsub_lt_self hn0 (by decide)
        have hpx : ¬p ^ (n - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
          ha
            (hx.symm ▸
              ⟨y,
                mul_right_cancel₀ hp.1 <| by
                  rw [tsub_add_cancel_of_le (succ_le_of_lt hn0)] at hy <;>
                    simp [hy, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩)
        have : 1 ≤ n + m := le_trans hn0 (Nat.le_add_right n m)
        finite_mul_aux hpx hb
          ⟨s,
            mul_right_cancel₀ hp.1
              (by
                rw [tsub_add_eq_add_tsub (succ_le_of_lt hn0), tsub_add_cancel_of_le this]
                clear _fun_match _fun_match finite_mul_aux
                simp_all [mul_comm, mul_assoc, mul_left_comm, pow_add])⟩)
      fun ⟨x, hx⟩ =>
      have hm0 : 0 < m :=
        Nat.pos_of_ne_zero fun hm0 => by clear _fun_match _fun_match <;> simpa [hx, hm0] using hb
      have wf : m - 1 < m := tsub_lt_self hm0 (by decide)
      have hpx : ¬p ^ (m - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
        hb
          (hx.symm ▸
            ⟨y,
              mul_right_cancel₀ hp.1 <| by
                rw [tsub_add_cancel_of_le (succ_le_of_lt hm0)] at hy <;>
                  simp [hy, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩)
      finite_mul_aux ha hpx
        ⟨s,
          mul_right_cancel₀ hp.1
            (by
              rw [add_assoc, tsub_add_cancel_of_le (succ_le_of_lt hm0)]
              clear _fun_match _fun_match finite_mul_aux
              simp_all [mul_comm, mul_assoc, mul_left_comm, pow_add])⟩
#align multiplicity.finite_mul_aux multiplicity.finite_mul_aux

/- warning: multiplicity.finite_mul -> multiplicity.finite_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {a : α} {b : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) -> (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b) -> (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {a : α} {b : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) -> (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b) -> (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align multiplicity.finite_mul multiplicity.finite_mulₓ'. -/
theorem finite_mul {p a b : α} (hp : Prime p) : Finite p a → Finite p b → Finite p (a * b) :=
  fun ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, finite_mul_aux hp hn hm⟩
#align multiplicity.finite_mul multiplicity.finite_mul

/- warning: multiplicity.finite_mul_iff -> multiplicity.finite_mul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {a : α} {b : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (Iff (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) (And (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α} {a : α} {b : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (Iff (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) (And (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b)))
Case conversion may be inaccurate. Consider using '#align multiplicity.finite_mul_iff multiplicity.finite_mul_iffₓ'. -/
theorem finite_mul_iff {p a b : α} (hp : Prime p) : Finite p (a * b) ↔ Finite p a ∧ Finite p b :=
  ⟨fun h => ⟨finite_of_finite_mul_right h, finite_of_finite_mul_left h⟩, fun h =>
    finite_mul hp h.1 h.2⟩
#align multiplicity.finite_mul_iff multiplicity.finite_mul_iff

#print multiplicity.finite_pow /-
theorem finite_pow {p a : α} (hp : Prime p) : ∀ {k : ℕ} (ha : Finite p a), Finite p (a ^ k)
  | 0, ha => ⟨0, by simp [mt isUnit_iff_dvd_one.2 hp.2.1]⟩
  | k + 1, ha => by rw [pow_succ] <;> exact finite_mul hp ha (finite_pow ha)
#align multiplicity.finite_pow multiplicity.finite_pow
-/

variable [DecidableRel ((· ∣ ·) : α → α → Prop)]

/- warning: multiplicity.multiplicity_self -> multiplicity.multiplicity_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))] {a : α}, (Not (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) a)) -> (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) a a) (OfNat.ofNat.{0} PartENat 1 (OfNat.mk.{0} PartENat 1 (One.one.{0} PartENat PartENat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.7164 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.7166 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.7164 x._@.Mathlib.RingTheory.Multiplicity._hyg.7166)] {a : α}, (Not (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) a)) -> (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) a a) (OfNat.ofNat.{0} PartENat 1 (One.toOfNat1.{0} PartENat PartENat.instOnePartENat)))
Case conversion may be inaccurate. Consider using '#align multiplicity.multiplicity_self multiplicity.multiplicity_selfₓ'. -/
@[simp]
theorem multiplicity_self {a : α} (ha : ¬IsUnit a) (ha0 : a ≠ 0) : multiplicity a a = 1 :=
  by
  rw [← Nat.cast_one]
  exact
    eq_coe_iff.2
      ⟨by simp, fun ⟨b, hb⟩ =>
        ha
          (isUnit_iff_dvd_one.2
            ⟨b,
              mul_left_cancel₀ ha0 <| by
                clear _fun_match
                simpa [pow_succ, mul_assoc] using hb⟩)⟩
#align multiplicity.multiplicity_self multiplicity.multiplicity_self

#print multiplicity.get_multiplicity_self /-
@[simp]
theorem get_multiplicity_self {a : α} (ha : Finite a a) : get (multiplicity a a) ha = 1 :=
  PartENat.get_eq_iff_eq_coe.2
    (eq_coe_iff.2
      ⟨by simp, fun ⟨b, hb⟩ => by
        rw [← mul_one a, pow_add, pow_one, mul_assoc, mul_assoc,
            mul_right_inj' (ne_zero_of_finite ha)] at hb <;>
          exact
            mt isUnit_iff_dvd_one.2 (not_unit_of_finite ha) ⟨b, by clear _fun_match <;> simp_all⟩⟩)
#align multiplicity.get_multiplicity_self multiplicity.get_multiplicity_self
-/

/- warning: multiplicity.mul' -> multiplicity.mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))] {p : α} {a : α} {b : α} (hp : Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) (h : Part.Dom.{0} Nat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b))), Eq.{1} Nat (Part.get.{0} Nat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) h) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Part.get.{0} Nat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p a) (And.left (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b) (Iff.mp (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) (And (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b)) (multiplicity.finite_mul_iff.{u1} α _inst_1 p a b hp) h))) (Part.get.{0} Nat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p b) (And.right (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b) (Iff.mp (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) (And (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b)) (multiplicity.finite_mul_iff.{u1} α _inst_1 p a b hp) h))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.7422 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.7424 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.7422 x._@.Mathlib.RingTheory.Multiplicity._hyg.7424)] {p : α} {a : α} {b : α} (hp : Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) (h : Part.Dom.{0} Nat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b))), Eq.{1} Nat (Part.get.{0} Nat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) h) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Part.get.{0} Nat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p a) (And.left (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b) (Iff.mp (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) (And (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b)) (multiplicity.finite_mul_iff.{u1} α _inst_1 p a b hp) h))) (Part.get.{0} Nat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p b) (And.right (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b) (Iff.mp (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) (And (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p a) (multiplicity.Finite.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p b)) (multiplicity.finite_mul_iff.{u1} α _inst_1 p a b hp) h))))
Case conversion may be inaccurate. Consider using '#align multiplicity.mul' multiplicity.mul'ₓ'. -/
protected theorem mul' {p a b : α} (hp : Prime p) (h : (multiplicity p (a * b)).Dom) :
    get (multiplicity p (a * b)) h =
      get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
        get (multiplicity p b) ((finite_mul_iff hp).1 h).2 :=
  by
  have hdiva : p ^ get (multiplicity p a) ((finite_mul_iff hp).1 h).1 ∣ a := pow_multiplicity_dvd _
  have hdivb : p ^ get (multiplicity p b) ((finite_mul_iff hp).1 h).2 ∣ b := pow_multiplicity_dvd _
  have hpoweq :
    p ^
        (get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
          get (multiplicity p b) ((finite_mul_iff hp).1 h).2) =
      p ^ get (multiplicity p a) ((finite_mul_iff hp).1 h).1 *
        p ^ get (multiplicity p b) ((finite_mul_iff hp).1 h).2 :=
    by simp [pow_add]
  have hdiv :
    p ^
        (get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
          get (multiplicity p b) ((finite_mul_iff hp).1 h).2) ∣
      a * b :=
    by rw [hpoweq] <;> apply mul_dvd_mul <;> assumption
  have hsucc :
    ¬p ^
          (get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
              get (multiplicity p b) ((finite_mul_iff hp).1 h).2 +
            1) ∣
        a * b :=
    fun h =>
    not_or_of_not (is_greatest' _ (lt_succ_self _)) (is_greatest' _ (lt_succ_self _))
      (_root_.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul hp hdiva hdivb h)
  rw [← PartENat.natCast_inj, PartENat.natCast_get, eq_coe_iff] <;> exact ⟨hdiv, hsucc⟩
#align multiplicity.mul' multiplicity.mul'

open Classical

/- warning: multiplicity.mul -> multiplicity.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))] {p : α} {a : α} {b : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.hasAdd) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p a) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.7933 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.7935 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.7933 x._@.Mathlib.RingTheory.Multiplicity._hyg.7935)] {p : α} {a : α} {b : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))) a b)) (HAdd.hAdd.{0, 0, 0} PartENat PartENat PartENat (instHAdd.{0} PartENat PartENat.instAddPartENat) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p a) (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p b)))
Case conversion may be inaccurate. Consider using '#align multiplicity.mul multiplicity.mulₓ'. -/
protected theorem mul {p a b : α} (hp : Prime p) :
    multiplicity p (a * b) = multiplicity p a + multiplicity p b :=
  if h : Finite p a ∧ Finite p b then by
    rw [← PartENat.natCast_get (finite_iff_dom.1 h.1), ←
        PartENat.natCast_get (finite_iff_dom.1 h.2), ←
        PartENat.natCast_get (finite_iff_dom.1 (finite_mul hp h.1 h.2)), ← Nat.cast_add,
        PartENat.natCast_inj, multiplicity.mul' hp] <;>
      rfl
  else by
    rw [eq_top_iff_not_finite.2 (mt (finite_mul_iff hp).1 h)]
    cases' not_and_or.1 h with h h <;> simp [eq_top_iff_not_finite.2 h]
#align multiplicity.mul multiplicity.mul

#print multiplicity.Finset.prod /-
theorem Finset.prod {β : Type _} {p : α} (hp : Prime p) (s : Finset β) (f : β → α) :
    multiplicity p (∏ x in s, f x) = ∑ x in s, multiplicity p (f x) := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp only [Finset.sum_empty, Finset.prod_empty]
      convert one_right hp.not_unit
    · simp [has, ← ih]
      convert multiplicity.mul hp
#align multiplicity.finset.prod multiplicity.Finset.prod
-/

#print multiplicity.pow' /-
protected theorem pow' {p a : α} (hp : Prime p) (ha : Finite p a) :
    ∀ {k : ℕ}, get (multiplicity p (a ^ k)) (finite_pow hp ha) = k * get (multiplicity p a) ha
  | 0 => by simp [one_right hp.not_unit]
  | k + 1 =>
    by
    have : multiplicity p (a ^ (k + 1)) = multiplicity p (a * a ^ k) := by rw [pow_succ]
    rw [get_eq_get_of_eq _ _ this, multiplicity.mul' hp, pow', add_mul, one_mul, add_comm]
#align multiplicity.pow' multiplicity.pow'
-/

/- warning: multiplicity.pow -> multiplicity.pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))] {p : α} {a : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {k : Nat}, Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a k)) (SMul.smul.{0, 0} Nat PartENat (AddMonoid.SMul.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))) k (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.8419 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.8421 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.8419 x._@.Mathlib.RingTheory.Multiplicity._hyg.8421)] {p : α} {a : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {k : Nat}, Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a k)) (HSMul.hSMul.{0, 0, 0} Nat PartENat PartENat (instHSMul.{0, 0} Nat PartENat (AddMonoid.SMul.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) k (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p a)))
Case conversion may be inaccurate. Consider using '#align multiplicity.pow multiplicity.powₓ'. -/
theorem pow {p a : α} (hp : Prime p) : ∀ {k : ℕ}, multiplicity p (a ^ k) = k • multiplicity p a
  | 0 => by simp [one_right hp.not_unit]
  | succ k => by simp [pow_succ, succ_nsmul, pow, multiplicity.mul hp]
#align multiplicity.pow multiplicity.pow

/- warning: multiplicity.multiplicity_pow_self -> multiplicity.multiplicity_pow_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))] {p : α}, (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))))) -> (Not (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p)) -> (forall (n : Nat), Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.8514 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.8516 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.8514 x._@.Mathlib.RingTheory.Multiplicity._hyg.8516)] {p : α}, (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) -> (Not (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p)) -> (forall (n : Nat), Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n)) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) n))
Case conversion may be inaccurate. Consider using '#align multiplicity.multiplicity_pow_self multiplicity.multiplicity_pow_selfₓ'. -/
theorem multiplicity_pow_self {p : α} (h0 : p ≠ 0) (hu : ¬IsUnit p) (n : ℕ) :
    multiplicity p (p ^ n) = n := by
  rw [eq_coe_iff]
  use dvd_rfl
  rw [pow_dvd_pow_iff h0 hu]
  apply Nat.not_succ_le_self
#align multiplicity.multiplicity_pow_self multiplicity.multiplicity_pow_self

/- warning: multiplicity.multiplicity_pow_self_of_prime -> multiplicity.multiplicity_pow_self_of_prime is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))))] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall (n : Nat), Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat PartENat (HasLiftT.mk.{1, 1} Nat PartENat (CoeTCₓ.coe.{1, 1} Nat PartENat (Nat.castCoe.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne))))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.RingTheory.Multiplicity._hyg.8661 : α) (x._@.Mathlib.RingTheory.Multiplicity._hyg.8663 : α) => Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) x._@.Mathlib.RingTheory.Multiplicity._hyg.8661 x._@.Mathlib.RingTheory.Multiplicity._hyg.8663)] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall (n : Nat), Eq.{1} PartENat (multiplicity.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) (fun (a : α) (b : α) => _inst_2 a b) p (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p n)) (Nat.cast.{0} PartENat (AddMonoidWithOne.toNatCast.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)) n))
Case conversion may be inaccurate. Consider using '#align multiplicity.multiplicity_pow_self_of_prime multiplicity.multiplicity_pow_self_of_primeₓ'. -/
theorem multiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : ℕ) :
    multiplicity p (p ^ n) = n :=
  multiplicity_pow_self hp.NeZero hp.not_unit n
#align multiplicity.multiplicity_pow_self_of_prime multiplicity.multiplicity_pow_self_of_prime

end CancelCommMonoidWithZero

section Valuation

variable {R : Type _} [CommRing R] [IsDomain R] {p : R} [DecidableRel (Dvd.Dvd : R → R → Prop)]

/- warning: multiplicity.add_valuation -> multiplicity.addValuation is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] {p : R} [_inst_3 : DecidableRel.{succ u1} R (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R _inst_1)))))))], (Prime.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) p) -> (AddValuation.{u1, 0} R (CommRing.toRing.{u1} R _inst_1) PartENat PartENat.linearOrderedAddCommMonoidWithTop)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))] {p : R} [_inst_3 : DecidableRel.{succ u1} R (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalCommSemiring.{u1} R (CommRing.toNonUnitalCommRing.{u1} R _inst_1)))))))], (Prime.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) _inst_2)) p) -> (AddValuation.{u1, 0} R (CommRing.toRing.{u1} R _inst_1) PartENat PartENat.instLinearOrderedAddCommMonoidWithTopPartENat)
Case conversion may be inaccurate. Consider using '#align multiplicity.add_valuation multiplicity.addValuationₓ'. -/
/-- `multiplicity` of a prime inan integral domain as an additive valuation to `part_enat`. -/
noncomputable def addValuation (hp : Prime p) : AddValuation R PartENat :=
  AddValuation.of (multiplicity p) (multiplicity.zero _) (one_right hp.not_unit)
    (fun _ _ => min_le_multiplicity_add) fun a b => multiplicity.mul hp
#align multiplicity.add_valuation multiplicity.addValuation

/- warning: multiplicity.add_valuation_apply -> multiplicity.addValuation_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] {p : R} [_inst_3 : DecidableRel.{succ u1} R (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalRing.{u1} R (CommRing.toNonUnitalCommRing.{u1} R _inst_1)))))))] {hp : Prime.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) p} {r : R}, Eq.{1} PartENat (coeFn.{succ u1, succ u1} (AddValuation.{u1, 0} R (CommRing.toRing.{u1} R _inst_1) PartENat PartENat.linearOrderedAddCommMonoidWithTop) (fun (_x : AddValuation.{u1, 0} R (CommRing.toRing.{u1} R _inst_1) PartENat PartENat.linearOrderedAddCommMonoidWithTop) => R -> PartENat) (AddValuation.hasCoeToFun.{u1, 0} R PartENat PartENat.linearOrderedAddCommMonoidWithTop (CommRing.toRing.{u1} R _inst_1)) (multiplicity.addValuation.{u1} R _inst_1 _inst_2 p (fun (a : R) (b : R) => _inst_3 a b) hp) r) (multiplicity.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)) (fun (a : R) (b : R) => _inst_3 a b) p r)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))] {p : R} [_inst_3 : DecidableRel.{succ u1} R (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} R (NonUnitalCommRing.toNonUnitalCommSemiring.{u1} R (CommRing.toNonUnitalCommRing.{u1} R _inst_1)))))))] {hp : Prime.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) _inst_2)) p} {r : R}, Eq.{1} (Multiplicative.{0} (OrderDual.{0} PartENat)) (ZeroHom.toFun.{u1, 0} R (Multiplicative.{0} (OrderDual.{0} PartENat)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (MulZeroOneClass.toZero.{0} (Multiplicative.{0} (OrderDual.{0} PartENat)) (MonoidWithZero.toMulZeroOneClass.{0} (Multiplicative.{0} (OrderDual.{0} PartENat)) (CommMonoidWithZero.toMonoidWithZero.{0} (Multiplicative.{0} (OrderDual.{0} PartENat)) (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{0} (Multiplicative.{0} (OrderDual.{0} PartENat)) (instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual.{0} PartENat PartENat.instLinearOrderedAddCommMonoidWithTopPartENat))))) (MonoidWithZeroHom.toZeroHom.{u1, 0} R (Multiplicative.{0} (OrderDual.{0} PartENat)) (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) (MonoidWithZero.toMulZeroOneClass.{0} (Multiplicative.{0} (OrderDual.{0} PartENat)) (CommMonoidWithZero.toMonoidWithZero.{0} (Multiplicative.{0} (OrderDual.{0} PartENat)) (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{0} (Multiplicative.{0} (OrderDual.{0} PartENat)) (instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual.{0} PartENat PartENat.instLinearOrderedAddCommMonoidWithTopPartENat)))) (Valuation.toMonoidWithZeroHom.{u1, 0} R (Multiplicative.{0} (OrderDual.{0} PartENat)) (instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual.{0} PartENat PartENat.instLinearOrderedAddCommMonoidWithTopPartENat) (CommRing.toRing.{u1} R _inst_1) (multiplicity.addValuation.{u1} R _inst_1 _inst_2 p (fun (a : R) (b : R) => _inst_3 a b) hp))) r) (multiplicity.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) (fun (a : R) (b : R) => _inst_3 a b) p r)
Case conversion may be inaccurate. Consider using '#align multiplicity.add_valuation_apply multiplicity.addValuation_applyₓ'. -/
@[simp]
theorem addValuation_apply {hp : Prime p} {r : R} : addValuation hp r = multiplicity p r :=
  rfl
#align multiplicity.add_valuation_apply multiplicity.addValuation_apply

end Valuation

end multiplicity

section Nat

open multiplicity

/- warning: multiplicity_eq_zero_of_coprime -> multiplicity_eq_zero_of_coprime is a dubious translation:
lean 3 declaration is
  forall {p : Nat} {a : Nat} {b : Nat}, (Ne.{1} Nat p (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> (LE.le.{0} PartENat PartENat.hasLe (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p a) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p b)) -> (Nat.coprime a b) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidableDvd a b) p a) (OfNat.ofNat.{0} PartENat 0 (OfNat.mk.{0} PartENat 0 (Zero.zero.{0} PartENat PartENat.hasZero))))
but is expected to have type
  forall {p : Nat} {a : Nat} {b : Nat}, (Ne.{1} Nat p (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> (LE.le.{0} PartENat PartENat.instLEPartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p a) (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p b)) -> (Nat.coprime a b) -> (Eq.{1} PartENat (multiplicity.{0} Nat Nat.monoid (fun (a : Nat) (b : Nat) => Nat.decidable_dvd a b) p a) (OfNat.ofNat.{0} PartENat 0 (Zero.toOfNat0.{0} PartENat PartENat.instZeroPartENat)))
Case conversion may be inaccurate. Consider using '#align multiplicity_eq_zero_of_coprime multiplicity_eq_zero_of_coprimeₓ'. -/
theorem multiplicity_eq_zero_of_coprime {p a b : ℕ} (hp : p ≠ 1)
    (hle : multiplicity p a ≤ multiplicity p b) (hab : Nat.coprime a b) : multiplicity p a = 0 :=
  by
  rw [multiplicity_le_multiplicity_iff] at hle
  rw [← nonpos_iff_eq_zero, ← not_lt, PartENat.pos_iff_one_le, ← Nat.cast_one, ←
    pow_dvd_iff_le_multiplicity]
  intro h
  have := Nat.dvd_gcd h (hle _ h)
  rw [coprime.gcd_eq_one hab, Nat.dvd_one, pow_one] at this
  exact hp this
#align multiplicity_eq_zero_of_coprime multiplicity_eq_zero_of_coprime

end Nat

