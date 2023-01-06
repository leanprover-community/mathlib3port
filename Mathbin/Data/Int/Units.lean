/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

! This file was ported from Lean 3 source module data.int.units
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Units
import Mathbin.Data.Int.Basic
import Mathbin.Algebra.Ring.Units

/-!
# Lemmas about units in `ℤ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Int

/-! ### units -/


/- warning: int.units_nat_abs -> Int.units_natAbs is a dubious translation:
lean 3 declaration is
  forall (u : Units.{0} Int Int.monoid), Eq.{1} Nat (Int.natAbs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Units.{0} Int Int.monoid) Int (HasLiftT.mk.{1, 1} (Units.{0} Int Int.monoid) Int (CoeTCₓ.coe.{1, 1} (Units.{0} Int Int.monoid) Int (coeBase.{1, 1} (Units.{0} Int Int.monoid) Int (Units.hasCoe.{0} Int Int.monoid)))) u)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  forall (u : Units.{0} Int Int.instMonoidInt), Eq.{1} Nat (Int.natAbs (Units.val.{0} Int Int.instMonoidInt u)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align int.units_nat_abs Int.units_natAbsₓ'. -/
@[simp]
theorem units_natAbs (u : ℤˣ) : natAbs u = 1 :=
  Units.ext_iff.1 <|
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← nat_abs_mul, Units.mul_inv] <;> rfl, by
        rw [← nat_abs_mul, Units.inv_mul] <;> rfl⟩
#align int.units_nat_abs Int.units_natAbs

/- warning: int.units_eq_one_or -> Int.units_eq_one_or is a dubious translation:
lean 3 declaration is
  forall (u : Units.{0} Int Int.monoid), Or (Eq.{1} (Units.{0} Int Int.monoid) u (OfNat.ofNat.{0} (Units.{0} Int Int.monoid) 1 (OfNat.mk.{0} (Units.{0} Int Int.monoid) 1 (One.one.{0} (Units.{0} Int Int.monoid) (MulOneClass.toHasOne.{0} (Units.{0} Int Int.monoid) (Units.mulOneClass.{0} Int Int.monoid)))))) (Eq.{1} (Units.{0} Int Int.monoid) u (Neg.neg.{0} (Units.{0} Int Int.monoid) (Units.hasNeg.{0} Int Int.monoid (NonUnitalNonAssocRing.toHasDistribNeg.{0} Int (NonAssocRing.toNonUnitalNonAssocRing.{0} Int (Ring.toNonAssocRing.{0} Int Int.ring)))) (OfNat.ofNat.{0} (Units.{0} Int Int.monoid) 1 (OfNat.mk.{0} (Units.{0} Int Int.monoid) 1 (One.one.{0} (Units.{0} Int Int.monoid) (MulOneClass.toHasOne.{0} (Units.{0} Int Int.monoid) (Units.mulOneClass.{0} Int Int.monoid)))))))
but is expected to have type
  forall (u : Units.{0} Int Int.instMonoidInt), Or (Eq.{1} (Units.{0} Int Int.instMonoidInt) u (OfNat.ofNat.{0} (Units.{0} Int Int.instMonoidInt) 1 (One.toOfNat1.{0} (Units.{0} Int Int.instMonoidInt) (InvOneClass.toOne.{0} (Units.{0} Int Int.instMonoidInt) (DivInvOneMonoid.toInvOneClass.{0} (Units.{0} Int Int.instMonoidInt) (DivisionMonoid.toDivInvOneMonoid.{0} (Units.{0} Int Int.instMonoidInt) (DivisionCommMonoid.toDivisionMonoid.{0} (Units.{0} Int Int.instMonoidInt) (CommGroup.toDivisionCommMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Units.instCommGroupUnitsToMonoid.{0} Int Int.instCommMonoidInt))))))))) (Eq.{1} (Units.{0} Int Int.instMonoidInt) u (Neg.neg.{0} (Units.{0} Int Int.instMonoidInt) (Units.instNegUnits.{0} Int Int.instMonoidInt (NonUnitalNonAssocRing.toHasDistribNeg.{0} Int (NonAssocRing.toNonUnitalNonAssocRing.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)))) (OfNat.ofNat.{0} (Units.{0} Int Int.instMonoidInt) 1 (One.toOfNat1.{0} (Units.{0} Int Int.instMonoidInt) (InvOneClass.toOne.{0} (Units.{0} Int Int.instMonoidInt) (DivInvOneMonoid.toInvOneClass.{0} (Units.{0} Int Int.instMonoidInt) (DivisionMonoid.toDivInvOneMonoid.{0} (Units.{0} Int Int.instMonoidInt) (DivisionCommMonoid.toDivisionMonoid.{0} (Units.{0} Int Int.instMonoidInt) (CommGroup.toDivisionCommMonoid.{0} (Units.{0} Int Int.instMonoidInt) (Units.instCommGroupUnitsToMonoid.{0} Int Int.instCommMonoidInt))))))))))
Case conversion may be inaccurate. Consider using '#align int.units_eq_one_or Int.units_eq_one_orₓ'. -/
theorem units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 := by
  simpa only [Units.ext_iff, units_nat_abs] using nat_abs_eq u
#align int.units_eq_one_or Int.units_eq_one_or

/- warning: int.is_unit_eq_one_or -> Int.isUnit_eq_one_or is a dubious translation:
lean 3 declaration is
  forall {a : Int}, (IsUnit.{0} Int Int.monoid a) -> (Or (Eq.{1} Int a (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (Eq.{1} Int a (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))))
but is expected to have type
  forall {a : Int}, (IsUnit.{0} Int Int.instMonoidInt a) -> (Or (Eq.{1} Int a (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (Eq.{1} Int a (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))))
Case conversion may be inaccurate. Consider using '#align int.is_unit_eq_one_or Int.isUnit_eq_one_orₓ'. -/
theorem isUnit_eq_one_or {a : ℤ} : IsUnit a → a = 1 ∨ a = -1
  | ⟨x, hx⟩ => hx ▸ (units_eq_one_or _).imp (congr_arg coe) (congr_arg coe)
#align int.is_unit_eq_one_or Int.isUnit_eq_one_or

/- warning: int.is_unit_iff -> Int.isUnit_iff is a dubious translation:
lean 3 declaration is
  forall {a : Int}, Iff (IsUnit.{0} Int Int.monoid a) (Or (Eq.{1} Int a (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (Eq.{1} Int a (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))))
but is expected to have type
  forall {a : Int}, Iff (IsUnit.{0} Int Int.instMonoidInt a) (Or (Eq.{1} Int a (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (Eq.{1} Int a (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))))
Case conversion may be inaccurate. Consider using '#align int.is_unit_iff Int.isUnit_iffₓ'. -/
theorem isUnit_iff {a : ℤ} : IsUnit a ↔ a = 1 ∨ a = -1 :=
  by
  refine' ⟨fun h => is_unit_eq_one_or h, fun h => _⟩
  rcases h with (rfl | rfl)
  · exact isUnit_one
  · exact is_unit_one.neg
#align int.is_unit_iff Int.isUnit_iff

/- warning: int.is_unit_eq_or_eq_neg -> Int.isUnit_eq_or_eq_neg is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int}, (IsUnit.{0} Int Int.monoid a) -> (IsUnit.{0} Int Int.monoid b) -> (Or (Eq.{1} Int a b) (Eq.{1} Int a (Neg.neg.{0} Int Int.hasNeg b)))
but is expected to have type
  forall {a : Int} {b : Int}, (IsUnit.{0} Int Int.instMonoidInt a) -> (IsUnit.{0} Int Int.instMonoidInt b) -> (Or (Eq.{1} Int a b) (Eq.{1} Int a (Neg.neg.{0} Int Int.instNegInt b)))
Case conversion may be inaccurate. Consider using '#align int.is_unit_eq_or_eq_neg Int.isUnit_eq_or_eq_negₓ'. -/
theorem isUnit_eq_or_eq_neg {a b : ℤ} (ha : IsUnit a) (hb : IsUnit b) : a = b ∨ a = -b :=
  by
  rcases is_unit_eq_one_or hb with (rfl | rfl)
  · exact is_unit_eq_one_or ha
  · rwa [or_comm', neg_neg, ← is_unit_iff]
#align int.is_unit_eq_or_eq_neg Int.isUnit_eq_or_eq_neg

#print Int.eq_one_or_neg_one_of_mul_eq_one /-
theorem eq_one_or_neg_one_of_mul_eq_one {z w : ℤ} (h : z * w = 1) : z = 1 ∨ z = -1 :=
  isUnit_iff.mp (isUnit_of_mul_eq_one z w h)
#align int.eq_one_or_neg_one_of_mul_eq_one Int.eq_one_or_neg_one_of_mul_eq_one
-/

#print Int.eq_one_or_neg_one_of_mul_eq_one' /-
theorem eq_one_or_neg_one_of_mul_eq_one' {z w : ℤ} (h : z * w = 1) :
    z = 1 ∧ w = 1 ∨ z = -1 ∧ w = -1 :=
  by
  have h' : w * z = 1 := mul_comm z w ▸ h
  rcases eq_one_or_neg_one_of_mul_eq_one h with (rfl | rfl) <;>
      rcases eq_one_or_neg_one_of_mul_eq_one h' with (rfl | rfl) <;>
    tauto
#align int.eq_one_or_neg_one_of_mul_eq_one' Int.eq_one_or_neg_one_of_mul_eq_one'
-/

#print Int.mul_eq_one_iff_eq_one_or_neg_one /-
theorem mul_eq_one_iff_eq_one_or_neg_one {z w : ℤ} : z * w = 1 ↔ z = 1 ∧ w = 1 ∨ z = -1 ∧ w = -1 :=
  by
  refine' ⟨eq_one_or_neg_one_of_mul_eq_one', fun h => Or.elim h (fun H => _) fun H => _⟩ <;>
      rcases H with ⟨rfl, rfl⟩ <;>
    rfl
#align int.mul_eq_one_iff_eq_one_or_neg_one Int.mul_eq_one_iff_eq_one_or_neg_one
-/

#print Int.eq_one_or_neg_one_of_mul_eq_neg_one' /-
theorem eq_one_or_neg_one_of_mul_eq_neg_one' {z w : ℤ} (h : z * w = -1) :
    z = 1 ∧ w = -1 ∨ z = -1 ∧ w = 1 :=
  by
  rcases is_unit_eq_one_or (is_unit.mul_iff.mp (int.is_unit_iff.mpr (Or.inr h))).1 with (rfl | rfl)
  · exact Or.inl ⟨rfl, one_mul w ▸ h⟩
  · exact Or.inr ⟨rfl, neg_inj.mp (neg_one_mul w ▸ h)⟩
#align int.eq_one_or_neg_one_of_mul_eq_neg_one' Int.eq_one_or_neg_one_of_mul_eq_neg_one'
-/

#print Int.mul_eq_neg_one_iff_eq_one_or_neg_one /-
theorem mul_eq_neg_one_iff_eq_one_or_neg_one {z w : ℤ} :
    z * w = -1 ↔ z = 1 ∧ w = -1 ∨ z = -1 ∧ w = 1 := by
  refine' ⟨eq_one_or_neg_one_of_mul_eq_neg_one', fun h => Or.elim h (fun H => _) fun H => _⟩ <;>
      rcases H with ⟨rfl, rfl⟩ <;>
    rfl
#align int.mul_eq_neg_one_iff_eq_one_or_neg_one Int.mul_eq_neg_one_iff_eq_one_or_neg_one
-/

/- warning: int.is_unit_iff_nat_abs_eq -> Int.isUnit_iff_natAbs_eq is a dubious translation:
lean 3 declaration is
  forall {n : Int}, Iff (IsUnit.{0} Int Int.monoid n) (Eq.{1} Nat (Int.natAbs n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {n : Int}, Iff (IsUnit.{0} Int Int.instMonoidInt n) (Eq.{1} Nat (Int.natAbs n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align int.is_unit_iff_nat_abs_eq Int.isUnit_iff_natAbs_eqₓ'. -/
theorem isUnit_iff_natAbs_eq {n : ℤ} : IsUnit n ↔ n.natAbs = 1 := by
  simp [nat_abs_eq_iff, is_unit_iff, Nat.cast_zero]
#align int.is_unit_iff_nat_abs_eq Int.isUnit_iff_natAbs_eq

alias is_unit_iff_nat_abs_eq ↔ is_unit.nat_abs_eq _

/- warning: int.of_nat_is_unit -> Int.ofNat_isUnit is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Iff (IsUnit.{0} Int Int.monoid ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) (IsUnit.{0} Nat Nat.monoid n)
but is expected to have type
  forall {n : Nat}, Iff (IsUnit.{0} Int Int.instMonoidInt (Nat.cast.{0} Int Int.instNatCastInt n)) (IsUnit.{0} Nat Nat.monoid n)
Case conversion may be inaccurate. Consider using '#align int.of_nat_is_unit Int.ofNat_isUnitₓ'. -/
@[norm_cast]
theorem ofNat_isUnit {n : ℕ} : IsUnit (n : ℤ) ↔ IsUnit n := by
  rw [Nat.isUnit_iff, is_unit_iff_nat_abs_eq, nat_abs_of_nat]
#align int.of_nat_is_unit Int.ofNat_isUnit

/- warning: int.is_unit_mul_self -> Int.isUnit_mul_self is a dubious translation:
lean 3 declaration is
  forall {a : Int}, (IsUnit.{0} Int Int.monoid a) -> (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.hasMul) a a) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {a : Int}, (IsUnit.{0} Int Int.instMonoidInt a) -> (Eq.{1} Int (HMul.hMul.{0, 0, 0} Int Int Int (instHMul.{0} Int Int.instMulInt) a a) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align int.is_unit_mul_self Int.isUnit_mul_selfₓ'. -/
theorem isUnit_mul_self {a : ℤ} (ha : IsUnit a) : a * a = 1 :=
  (isUnit_eq_one_or ha).elim (fun h => h.symm ▸ rfl) fun h => h.symm ▸ rfl
#align int.is_unit_mul_self Int.isUnit_mul_self

/- warning: int.is_unit_add_is_unit_eq_is_unit_add_is_unit -> Int.isUnit_add_isUnit_eq_isUnit_add_isUnit is a dubious translation:
lean 3 declaration is
  forall {a : Int} {b : Int} {c : Int} {d : Int}, (IsUnit.{0} Int Int.monoid a) -> (IsUnit.{0} Int Int.monoid b) -> (IsUnit.{0} Int Int.monoid c) -> (IsUnit.{0} Int Int.monoid d) -> (Iff (Eq.{1} Int (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) a b) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) c d)) (Or (And (Eq.{1} Int a c) (Eq.{1} Int b d)) (And (Eq.{1} Int a d) (Eq.{1} Int b c))))
but is expected to have type
  forall {a : Int} {b : Int} {c : Int} {d : Int}, (IsUnit.{0} Int Int.instMonoidInt a) -> (IsUnit.{0} Int Int.instMonoidInt b) -> (IsUnit.{0} Int Int.instMonoidInt c) -> (IsUnit.{0} Int Int.instMonoidInt d) -> (Iff (Eq.{1} Int (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) a b) (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) c d)) (Or (And (Eq.{1} Int a c) (Eq.{1} Int b d)) (And (Eq.{1} Int a d) (Eq.{1} Int b c))))
Case conversion may be inaccurate. Consider using '#align int.is_unit_add_is_unit_eq_is_unit_add_is_unit Int.isUnit_add_isUnit_eq_isUnit_add_isUnitₓ'. -/
theorem isUnit_add_isUnit_eq_isUnit_add_isUnit {a b c d : ℤ} (ha : IsUnit a) (hb : IsUnit b)
    (hc : IsUnit c) (hd : IsUnit d) : a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c :=
  by
  rw [is_unit_iff] at ha hb hc hd
  cases ha <;> cases hb <;> cases hc <;> cases hd <;> subst ha <;> subst hb <;> subst hc <;>
      subst hd <;>
    tidy
#align int.is_unit_add_is_unit_eq_is_unit_add_is_unit Int.isUnit_add_isUnit_eq_isUnit_add_isUnit

#print Int.eq_one_or_neg_one_of_mul_eq_neg_one /-
theorem eq_one_or_neg_one_of_mul_eq_neg_one {z w : ℤ} (h : z * w = -1) : z = 1 ∨ z = -1 :=
  Or.elim (eq_one_or_neg_one_of_mul_eq_neg_one' h) (fun H => Or.inl H.1) fun H => Or.inr H.1
#align int.eq_one_or_neg_one_of_mul_eq_neg_one Int.eq_one_or_neg_one_of_mul_eq_neg_one
-/

end Int

