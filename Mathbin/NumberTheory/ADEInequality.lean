/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module number_theory.ADE_inequality
! leanprover-community/mathlib commit 1ead22342e1a078bd44744ace999f85756555d35
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Sort
import Mathbin.Data.Pnat.Interval
import Mathbin.Data.Rat.Order
import Mathbin.Data.Pnat.Basic
import Mathbin.Tactic.NormNum
import Mathbin.Tactic.FieldSimp
import Mathbin.Tactic.IntervalCases

/-!
# The inequality `p⁻¹ + q⁻¹ + r⁻¹ > 1`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we classify solutions to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`, for positive natural numbers `p`, `q`, and `r`.

The solutions are exactly of the form.
* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`

This inequality shows up in Lie theory,
in the classification of Dynkin diagrams, root systems, and semisimple Lie algebras.

## Main declarations

* `pqr.A' q r`, the multiset `{1,q,r}`
* `pqr.D' r`, the multiset `{2,2,r}`
* `pqr.E6`, the multiset `{2,3,3}`
* `pqr.E7`, the multiset `{2,3,4}`
* `pqr.E8`, the multiset `{2,3,5}`
* `pqr.classification`, the classification of solutions to `p⁻¹ + q⁻¹ + r⁻¹ > 1`

-/


namespace ADEInequality

open Multiset

#print ADEInequality.A' /-
/-- `A' q r := {1,q,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`. -/
def A' (q r : ℕ+) : Multiset ℕ+ :=
  {1, q, r}
#align ADE_inequality.A' ADEInequality.A'
-/

#print ADEInequality.A /-
/-- `A r := {1,1,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $A_r$. -/
def A (r : ℕ+) : Multiset ℕ+ :=
  A' 1 r
#align ADE_inequality.A ADEInequality.A
-/

#print ADEInequality.D' /-
/-- `D' r := {2,2,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $D_{r+2}$. -/
def D' (r : ℕ+) : Multiset ℕ+ :=
  {2, 2, r}
#align ADE_inequality.D' ADEInequality.D'
-/

#print ADEInequality.E' /-
/-- `E' r := {2,3,r}` is a `multiset ℕ+`.
For `r ∈ {3,4,5}` is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $E_{r+3}$. -/
def E' (r : ℕ+) : Multiset ℕ+ :=
  {2, 3, r}
#align ADE_inequality.E' ADEInequality.E'
-/

#print ADEInequality.E6 /-
/-- `E6 := {2,3,3}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_6$. -/
def E6 : Multiset ℕ+ :=
  E' 3
#align ADE_inequality.E6 ADEInequality.E6
-/

#print ADEInequality.E7 /-
/-- `E7 := {2,3,4}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_7$. -/
def E7 : Multiset ℕ+ :=
  E' 4
#align ADE_inequality.E7 ADEInequality.E7
-/

#print ADEInequality.E8 /-
/-- `E8 := {2,3,5}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_8$. -/
def E8 : Multiset ℕ+ :=
  E' 5
#align ADE_inequality.E8 ADEInequality.E8
-/

#print ADEInequality.sumInv /-
/-- `sum_inv pqr` for a `pqr : multiset ℕ+` is the sum of the inverses
of the elements of `pqr`, as rational number.

The intended argument is a multiset `{p,q,r}` of cardinality `3`. -/
def sumInv (pqr : Multiset ℕ+) : ℚ :=
  Multiset.sum <| pqr.map fun x => x⁻¹
#align ADE_inequality.sum_inv ADEInequality.sumInv
-/

/- warning: ADE_inequality.sum_inv_pqr -> ADEInequality.sumInv_pqr is a dubious translation:
lean 3 declaration is
  forall (p : PNat) (q : PNat) (r : PNat), Eq.{1} Rat (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasSingleton.{0} PNat) r)))) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.hasAdd) (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Rat (HasLiftT.mk.{1, 1} PNat Rat (CoeTCₓ.coe.{1, 1} PNat Rat (coeTrans.{1, 1, 1} PNat Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))) coePNatNat))) p)) (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Rat (HasLiftT.mk.{1, 1} PNat Rat (CoeTCₓ.coe.{1, 1} PNat Rat (coeTrans.{1, 1, 1} PNat Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))) coePNatNat))) q))) (Inv.inv.{0} Rat Rat.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Rat (HasLiftT.mk.{1, 1} PNat Rat (CoeTCₓ.coe.{1, 1} PNat Rat (coeTrans.{1, 1, 1} PNat Nat Rat (Nat.castCoe.{0} Rat (AddMonoidWithOne.toNatCast.{0} Rat (AddGroupWithOne.toAddMonoidWithOne.{0} Rat (AddCommGroupWithOne.toAddGroupWithOne.{0} Rat (Ring.toAddCommGroupWithOne.{0} Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing)))))) coePNatNat))) r)))
but is expected to have type
  forall (p : PNat) (q : PNat) (r : PNat), Eq.{1} Rat (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instSingletonMultiset.{0} PNat) r)))) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) (HAdd.hAdd.{0, 0, 0} Rat Rat Rat (instHAdd.{0} Rat Rat.instAddRat) (Inv.inv.{0} Rat Rat.instInvRat (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) (PNat.val p))) (Inv.inv.{0} Rat Rat.instInvRat (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) (PNat.val q)))) (Inv.inv.{0} Rat Rat.instInvRat (Nat.cast.{0} Rat (Semiring.toNatCast.{0} Rat Rat.semiring) (PNat.val r))))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.sum_inv_pqr ADEInequality.sumInv_pqrₓ'. -/
theorem sumInv_pqr (p q r : ℕ+) : sumInv {p, q, r} = p⁻¹ + q⁻¹ + r⁻¹ := by
  simp only [sum_inv, coe_coe, add_zero, insert_eq_cons, add_assoc, map_cons, sum_cons,
    map_singleton, sum_singleton]
#align ADE_inequality.sum_inv_pqr ADEInequality.sumInv_pqr

#print ADEInequality.Admissible /-
/-- A multiset `pqr` of positive natural numbers is `admissible`
if it is equal to `A' q r`, or `D' r`, or one of `E6`, `E7`, or `E8`. -/
def Admissible (pqr : Multiset ℕ+) : Prop :=
  (∃ q r, A' q r = pqr) ∨ (∃ r, D' r = pqr) ∨ E' 3 = pqr ∨ E' 4 = pqr ∨ E' 5 = pqr
#align ADE_inequality.admissible ADEInequality.Admissible
-/

#print ADEInequality.admissible_A' /-
theorem admissible_A' (q r : ℕ+) : Admissible (A' q r) :=
  Or.inl ⟨q, r, rfl⟩
#align ADE_inequality.admissible_A' ADEInequality.admissible_A'
-/

#print ADEInequality.admissible_D' /-
theorem admissible_D' (n : ℕ+) : Admissible (D' n) :=
  Or.inr <| Or.inl ⟨n, rfl⟩
#align ADE_inequality.admissible_D' ADEInequality.admissible_D'
-/

/- warning: ADE_inequality.admissible_E'3 -> ADEInequality.admissible_E'3 is a dubious translation:
lean 3 declaration is
  ADEInequality.Admissible (ADEInequality.E' (OfNat.ofNat.{0} PNat 3 (OfNat.mk.{0} PNat 3 (bit1.{0} PNat PNat.hasOne PNat.hasAdd (One.one.{0} PNat PNat.hasOne)))))
but is expected to have type
  ADEInequality.Admissible (ADEInequality.E' (OfNat.ofNat.{0} PNat 3 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.admissible_E'3 ADEInequality.admissible_E'3ₓ'. -/
theorem admissible_E'3 : Admissible (E' 3) :=
  Or.inr <| Or.inr <| Or.inl rfl
#align ADE_inequality.admissible_E'3 ADEInequality.admissible_E'3

/- warning: ADE_inequality.admissible_E'4 -> ADEInequality.admissible_E'4 is a dubious translation:
lean 3 declaration is
  ADEInequality.Admissible (ADEInequality.E' (OfNat.ofNat.{0} PNat 4 (OfNat.mk.{0} PNat 4 (bit0.{0} PNat PNat.hasAdd (bit0.{0} PNat PNat.hasAdd (One.one.{0} PNat PNat.hasOne))))))
but is expected to have type
  ADEInequality.Admissible (ADEInequality.E' (OfNat.ofNat.{0} PNat 4 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.admissible_E'4 ADEInequality.admissible_E'4ₓ'. -/
theorem admissible_E'4 : Admissible (E' 4) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
#align ADE_inequality.admissible_E'4 ADEInequality.admissible_E'4

/- warning: ADE_inequality.admissible_E'5 -> ADEInequality.admissible_E'5 is a dubious translation:
lean 3 declaration is
  ADEInequality.Admissible (ADEInequality.E' (OfNat.ofNat.{0} PNat 5 (OfNat.mk.{0} PNat 5 (bit1.{0} PNat PNat.hasOne PNat.hasAdd (bit0.{0} PNat PNat.hasAdd (One.one.{0} PNat PNat.hasOne))))))
but is expected to have type
  ADEInequality.Admissible (ADEInequality.E' (OfNat.ofNat.{0} PNat 5 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4)))))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.admissible_E'5 ADEInequality.admissible_E'5ₓ'. -/
theorem admissible_E'5 : Admissible (E' 5) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
#align ADE_inequality.admissible_E'5 ADEInequality.admissible_E'5

#print ADEInequality.admissible_E6 /-
theorem admissible_E6 : Admissible E6 :=
  admissible_E'3
#align ADE_inequality.admissible_E6 ADEInequality.admissible_E6
-/

#print ADEInequality.admissible_E7 /-
theorem admissible_E7 : Admissible E7 :=
  admissible_E'4
#align ADE_inequality.admissible_E7 ADEInequality.admissible_E7
-/

#print ADEInequality.admissible_E8 /-
theorem admissible_E8 : Admissible E8 :=
  admissible_E'5
#align ADE_inequality.admissible_E8 ADEInequality.admissible_E8
-/

/- warning: ADE_inequality.admissible.one_lt_sum_inv -> ADEInequality.Admissible.one_lt_sumInv is a dubious translation:
lean 3 declaration is
  forall {pqr : Multiset.{0} PNat}, (ADEInequality.Admissible pqr) -> (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))) (ADEInequality.sumInv pqr))
but is expected to have type
  forall {pqr : Multiset.{0} PNat}, (ADEInequality.Admissible pqr) -> (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)) (ADEInequality.sumInv pqr))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.admissible.one_lt_sum_inv ADEInequality.Admissible.one_lt_sumInvₓ'. -/
theorem Admissible.one_lt_sumInv {pqr : Multiset ℕ+} : Admissible pqr → 1 < sumInv pqr :=
  by
  rw [admissible]
  rintro (⟨p', q', H⟩ | ⟨n, H⟩ | H | H | H)
  · rw [← H, A', sum_inv_pqr, add_assoc]
    simp only [lt_add_iff_pos_right, PNat.one_coe, inv_one, Nat.cast_one, coe_coe]
    apply add_pos <;> simp only [PNat.pos, Nat.cast_pos, inv_pos]
  · rw [← H, D', sum_inv_pqr]
    simp only [lt_add_iff_pos_right, PNat.one_coe, inv_one, Nat.cast_one, coe_coe, PNat.coe_bit0,
      Nat.cast_bit0]
    norm_num
  all_goals rw [← H, E', sum_inv_pqr]; norm_num
#align ADE_inequality.admissible.one_lt_sum_inv ADEInequality.Admissible.one_lt_sumInv

/- warning: ADE_inequality.lt_three -> ADEInequality.lt_three is a dubious translation:
lean 3 declaration is
  forall {p : PNat} {q : PNat} {r : PNat}, (LE.le.{0} PNat (Preorder.toHasLe.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) p q) -> (LE.le.{0} PNat (Preorder.toHasLe.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) q r) -> (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasSingleton.{0} PNat) r))))) -> (LT.lt.{0} PNat (Preorder.toHasLt.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) p (OfNat.ofNat.{0} PNat 3 (OfNat.mk.{0} PNat 3 (bit1.{0} PNat PNat.hasOne PNat.hasAdd (One.one.{0} PNat PNat.hasOne)))))
but is expected to have type
  forall {p : PNat} {q : PNat} {r : PNat}, (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) p q) -> (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) q r) -> (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instSingletonMultiset.{0} PNat) r))))) -> (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) p (OfNat.ofNat.{0} PNat 3 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.lt_three ADEInequality.lt_threeₓ'. -/
theorem lt_three {p q r : ℕ+} (hpq : p ≤ q) (hqr : q ≤ r) (H : 1 < sumInv {p, q, r}) : p < 3 :=
  by
  have h3 : (0 : ℚ) < 3 := by norm_num
  contrapose! H; rw [sum_inv_pqr]
  have h3q := H.trans hpq
  have h3r := h3q.trans hqr
  calc
    (p⁻¹ + q⁻¹ + r⁻¹ : ℚ) ≤ 3⁻¹ + 3⁻¹ + 3⁻¹ := add_le_add (add_le_add _ _) _
    _ = 1 := by norm_num
    
  all_goals rw [inv_le_inv _ h3] <;> [assumption_mod_cast;norm_num]
#align ADE_inequality.lt_three ADEInequality.lt_three

/- warning: ADE_inequality.lt_four -> ADEInequality.lt_four is a dubious translation:
lean 3 declaration is
  forall {q : PNat} {r : PNat}, (LE.le.{0} PNat (Preorder.toHasLe.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) q r) -> (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) (OfNat.ofNat.{0} PNat 2 (OfNat.mk.{0} PNat 2 (bit0.{0} PNat PNat.hasAdd (One.one.{0} PNat PNat.hasOne)))) (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasSingleton.{0} PNat) r))))) -> (LT.lt.{0} PNat (Preorder.toHasLt.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) q (OfNat.ofNat.{0} PNat 4 (OfNat.mk.{0} PNat 4 (bit0.{0} PNat PNat.hasAdd (bit0.{0} PNat PNat.hasAdd (One.one.{0} PNat PNat.hasOne))))))
but is expected to have type
  forall {q : PNat} {r : PNat}, (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) q r) -> (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) (OfNat.ofNat.{0} PNat 2 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instSingletonMultiset.{0} PNat) r))))) -> (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) q (OfNat.ofNat.{0} PNat 4 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3)))))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.lt_four ADEInequality.lt_fourₓ'. -/
theorem lt_four {q r : ℕ+} (hqr : q ≤ r) (H : 1 < sumInv {2, q, r}) : q < 4 :=
  by
  have h4 : (0 : ℚ) < 4 := by norm_num
  contrapose! H; rw [sum_inv_pqr]
  have h4r := H.trans hqr
  simp only [PNat.coe_bit0, Nat.cast_bit0, PNat.one_coe, Nat.cast_one, coe_coe]
  calc
    (2⁻¹ + q⁻¹ + r⁻¹ : ℚ) ≤ 2⁻¹ + 4⁻¹ + 4⁻¹ := add_le_add (add_le_add le_rfl _) _
    _ = 1 := by norm_num
    
  all_goals rw [inv_le_inv _ h4] <;> [assumption_mod_cast;norm_num]
#align ADE_inequality.lt_four ADEInequality.lt_four

/- warning: ADE_inequality.lt_six -> ADEInequality.lt_six is a dubious translation:
lean 3 declaration is
  forall {r : PNat}, (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) (OfNat.ofNat.{0} PNat 2 (OfNat.mk.{0} PNat 2 (bit0.{0} PNat PNat.hasAdd (One.one.{0} PNat PNat.hasOne)))) (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) (OfNat.ofNat.{0} PNat 3 (OfNat.mk.{0} PNat 3 (bit1.{0} PNat PNat.hasOne PNat.hasAdd (One.one.{0} PNat PNat.hasOne)))) (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasSingleton.{0} PNat) r))))) -> (LT.lt.{0} PNat (Preorder.toHasLt.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) r (OfNat.ofNat.{0} PNat 6 (OfNat.mk.{0} PNat 6 (bit0.{0} PNat PNat.hasAdd (bit1.{0} PNat PNat.hasOne PNat.hasAdd (One.one.{0} PNat PNat.hasOne))))))
but is expected to have type
  forall {r : PNat}, (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) (OfNat.ofNat.{0} PNat 2 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) (OfNat.ofNat.{0} PNat 3 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instSingletonMultiset.{0} PNat) r))))) -> (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) r (OfNat.ofNat.{0} PNat 6 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)))))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.lt_six ADEInequality.lt_sixₓ'. -/
theorem lt_six {r : ℕ+} (H : 1 < sumInv {2, 3, r}) : r < 6 :=
  by
  have h6 : (0 : ℚ) < 6 := by norm_num
  contrapose! H; rw [sum_inv_pqr]
  simp only [PNat.coe_bit0, Nat.cast_bit0, PNat.one_coe, Nat.cast_bit1, Nat.cast_one, PNat.coe_bit1,
    coe_coe]
  calc
    (2⁻¹ + 3⁻¹ + r⁻¹ : ℚ) ≤ 2⁻¹ + 3⁻¹ + 6⁻¹ := add_le_add (add_le_add le_rfl le_rfl) _
    _ = 1 := by norm_num
    
  rw [inv_le_inv _ h6] <;> [assumption_mod_cast;norm_num]
#align ADE_inequality.lt_six ADEInequality.lt_six

/- warning: ADE_inequality.admissible_of_one_lt_sum_inv_aux' -> ADEInequality.admissible_of_one_lt_sumInv_aux' is a dubious translation:
lean 3 declaration is
  forall {p : PNat} {q : PNat} {r : PNat}, (LE.le.{0} PNat (Preorder.toHasLe.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) p q) -> (LE.le.{0} PNat (Preorder.toHasLe.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) q r) -> (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasSingleton.{0} PNat) r))))) -> (ADEInequality.Admissible (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasSingleton.{0} PNat) r))))
but is expected to have type
  forall {p : PNat} {q : PNat} {r : PNat}, (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) p q) -> (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) q r) -> (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instSingletonMultiset.{0} PNat) r))))) -> (ADEInequality.Admissible (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instSingletonMultiset.{0} PNat) r))))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.admissible_of_one_lt_sum_inv_aux' ADEInequality.admissible_of_one_lt_sumInv_aux'ₓ'. -/
theorem admissible_of_one_lt_sumInv_aux' {p q r : ℕ+} (hpq : p ≤ q) (hqr : q ≤ r)
    (H : 1 < sumInv {p, q, r}) : Admissible {p, q, r} :=
  by
  have hp3 : p < 3 := lt_three hpq hqr H
  interval_cases
  · exact admissible_A' q r
  have hq4 : q < 4 := lt_four hqr H
  interval_cases
  · exact admissible_D' r
  have hr6 : r < 6 := lt_six H
  interval_cases
  · exact admissible_E6
  · exact admissible_E7
  · exact admissible_E8
#align ADE_inequality.admissible_of_one_lt_sum_inv_aux' ADEInequality.admissible_of_one_lt_sumInv_aux'

/- warning: ADE_inequality.admissible_of_one_lt_sum_inv_aux -> ADEInequality.admissible_of_one_lt_sumInv_aux is a dubious translation:
lean 3 declaration is
  forall {pqr : List.{0} PNat}, (List.Sorted.{0} PNat (LE.le.{0} PNat (Preorder.toHasLe.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))) pqr) -> (Eq.{1} Nat (List.length.{0} PNat pqr) (OfNat.ofNat.{0} Nat 3 (OfNat.mk.{0} Nat 3 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))) (ADEInequality.sumInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (List.{0} PNat) (Multiset.{0} PNat) (HasLiftT.mk.{1, 1} (List.{0} PNat) (Multiset.{0} PNat) (CoeTCₓ.coe.{1, 1} (List.{0} PNat) (Multiset.{0} PNat) (coeBase.{1, 1} (List.{0} PNat) (Multiset.{0} PNat) (Multiset.hasCoe.{0} PNat)))) pqr))) -> (ADEInequality.Admissible ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (List.{0} PNat) (Multiset.{0} PNat) (HasLiftT.mk.{1, 1} (List.{0} PNat) (Multiset.{0} PNat) (CoeTCₓ.coe.{1, 1} (List.{0} PNat) (Multiset.{0} PNat) (coeBase.{1, 1} (List.{0} PNat) (Multiset.{0} PNat) (Multiset.hasCoe.{0} PNat)))) pqr))
but is expected to have type
  forall {pqr : List.{0} PNat}, (List.Sorted.{0} PNat (fun (x._@.Mathlib.NumberTheory.ADEInequality._hyg.2199 : PNat) (x._@.Mathlib.NumberTheory.ADEInequality._hyg.2201 : PNat) => LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) x._@.Mathlib.NumberTheory.ADEInequality._hyg.2199 x._@.Mathlib.NumberTheory.ADEInequality._hyg.2201) pqr) -> (Eq.{1} Nat (List.length.{0} PNat pqr) (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))) -> (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)) (ADEInequality.sumInv (Multiset.ofList.{0} PNat pqr))) -> (ADEInequality.Admissible (Multiset.ofList.{0} PNat pqr))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.admissible_of_one_lt_sum_inv_aux ADEInequality.admissible_of_one_lt_sumInv_auxₓ'. -/
theorem admissible_of_one_lt_sumInv_aux :
    ∀ {pqr : List ℕ+} (hs : pqr.Sorted (· ≤ ·)) (hl : pqr.length = 3) (H : 1 < sumInv pqr),
      Admissible pqr
  | [p, q, r], hs, hl, H =>
    by
    obtain ⟨⟨hpq, -⟩, hqr⟩ : (p ≤ q ∧ p ≤ r) ∧ q ≤ r
    simpa using hs
    exact admissible_of_one_lt_sum_inv_aux' hpq hqr H
#align ADE_inequality.admissible_of_one_lt_sum_inv_aux ADEInequality.admissible_of_one_lt_sumInv_aux

/- warning: ADE_inequality.admissible_of_one_lt_sum_inv -> ADEInequality.admissible_of_one_lt_sumInv is a dubious translation:
lean 3 declaration is
  forall {p : PNat} {q : PNat} {r : PNat}, (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasSingleton.{0} PNat) r))))) -> (ADEInequality.Admissible (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasSingleton.{0} PNat) r))))
but is expected to have type
  forall {p : PNat} {q : PNat} {r : PNat}, (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instSingletonMultiset.{0} PNat) r))))) -> (ADEInequality.Admissible (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instSingletonMultiset.{0} PNat) r))))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.admissible_of_one_lt_sum_inv ADEInequality.admissible_of_one_lt_sumInvₓ'. -/
theorem admissible_of_one_lt_sumInv {p q r : ℕ+} (H : 1 < sumInv {p, q, r}) :
    Admissible {p, q, r} := by
  simp only [admissible]
  let S := sort ((· ≤ ·) : ℕ+ → ℕ+ → Prop) {p, q, r}
  have hS : S.sorted (· ≤ ·) := sort_sorted _ _
  have hpqr : ({p, q, r} : Multiset ℕ+) = S := (sort_eq LE.le {p, q, r}).symm
  simp only [hpqr] at *
  apply admissible_of_one_lt_sum_inv_aux hS _ H
  simp only [S, length_sort]
  decide
#align ADE_inequality.admissible_of_one_lt_sum_inv ADEInequality.admissible_of_one_lt_sumInv

/- warning: ADE_inequality.classification -> ADEInequality.classification is a dubious translation:
lean 3 declaration is
  forall (p : PNat) (q : PNat) (r : PNat), Iff (LT.lt.{0} Rat Rat.hasLt (OfNat.ofNat.{0} Rat 1 (OfNat.mk.{0} Rat 1 (One.one.{0} Rat Rat.hasOne))) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasSingleton.{0} PNat) r))))) (ADEInequality.Admissible (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasInsert.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.hasSingleton.{0} PNat) r))))
but is expected to have type
  forall (p : PNat) (q : PNat) (r : PNat), Iff (LT.lt.{0} Rat Rat.instLTRat_1 (OfNat.ofNat.{0} Rat 1 (Rat.instOfNatRat 1)) (ADEInequality.sumInv (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instSingletonMultiset.{0} PNat) r))))) (ADEInequality.Admissible (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) p (Insert.insert.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instInsertMultiset.{0} PNat) q (Singleton.singleton.{0, 0} PNat (Multiset.{0} PNat) (Multiset.instSingletonMultiset.{0} PNat) r))))
Case conversion may be inaccurate. Consider using '#align ADE_inequality.classification ADEInequality.classificationₓ'. -/
/-- A multiset `{p,q,r}` of positive natural numbers
is a solution to `(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1` if and only if
it is `admissible` which means it is one of:

* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`
-/
theorem classification (p q r : ℕ+) : 1 < sumInv {p, q, r} ↔ Admissible {p, q, r} :=
  ⟨admissible_of_one_lt_sumInv, Admissible.one_lt_sumInv⟩
#align ADE_inequality.classification ADEInequality.classification

end ADEInequality

