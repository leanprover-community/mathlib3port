/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module set_theory.cardinal.continuum
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of continuum

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `cardinal.continuum` (notation: `𝔠`, localized in `cardinal`) to be `2 ^ ℵ₀`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `cardinal.continuum` in locale `cardinal`.
-/


namespace Cardinal

universe u v

open Cardinal

#print Cardinal.continuum /-
/-- Cardinality of continuum. -/
def continuum : Cardinal.{u} :=
  2 ^ aleph0.{u}
#align cardinal.continuum Cardinal.continuum
-/

-- mathport name: cardinal.continuum
scoped notation "𝔠" => Cardinal.continuum

/- warning: cardinal.two_power_aleph_0 -> Cardinal.two_power_aleph0 is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) Cardinal.aleph0.{u1}) Cardinal.continuum.{u1}
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Cardinal.aleph0.{u1}) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.two_power_aleph_0 Cardinal.two_power_aleph0ₓ'. -/
@[simp]
theorem two_power_aleph0 : 2 ^ aleph0.{u} = continuum.{u} :=
  rfl
#align cardinal.two_power_aleph_0 Cardinal.two_power_aleph0

/- warning: cardinal.lift_continuum -> Cardinal.lift_continuum is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ (max u2 u1))} Cardinal.{max u2 u1} (Cardinal.lift.{u1, u2} Cardinal.continuum.{u2}) Cardinal.continuum.{max u2 u1}
but is expected to have type
  Eq.{max (succ (succ u2)) (succ (succ u1))} Cardinal.{max u1 u2} (Cardinal.lift.{u2, u1} Cardinal.continuum.{u1}) Cardinal.continuum.{max u2 u1}
Case conversion may be inaccurate. Consider using '#align cardinal.lift_continuum Cardinal.lift_continuumₓ'. -/
@[simp]
theorem lift_continuum : lift.{v} 𝔠 = 𝔠 := by
  rw [← two_power_aleph_0, lift_two_power, lift_aleph_0, two_power_aleph_0]
#align cardinal.lift_continuum Cardinal.lift_continuum

/-!
### Inequalities
-/


#print Cardinal.aleph0_lt_continuum /-
theorem aleph0_lt_continuum : ℵ₀ < 𝔠 :=
  cantor ℵ₀
#align cardinal.aleph_0_lt_continuum Cardinal.aleph0_lt_continuum
-/

#print Cardinal.aleph0_le_continuum /-
theorem aleph0_le_continuum : ℵ₀ ≤ 𝔠 :=
  aleph0_lt_continuum.le
#align cardinal.aleph_0_le_continuum Cardinal.aleph0_le_continuum
-/

/- warning: cardinal.beth_one -> Cardinal.beth_one is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.beth.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) Cardinal.continuum.{u1}
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.beth.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.beth_one Cardinal.beth_oneₓ'. -/
@[simp]
theorem beth_one : beth 1 = 𝔠 := by simpa using beth_succ 0
#align cardinal.beth_one Cardinal.beth_one

/- warning: cardinal.nat_lt_continuum -> Cardinal.nat_lt_continuum is a dubious translation:
lean 3 declaration is
  forall (n : Nat), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) Cardinal.continuum.{u1}
but is expected to have type
  forall (n : Nat), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.nat_lt_continuum Cardinal.nat_lt_continuumₓ'. -/
theorem nat_lt_continuum (n : ℕ) : ↑n < 𝔠 :=
  (nat_lt_aleph0 n).trans aleph0_lt_continuum
#align cardinal.nat_lt_continuum Cardinal.nat_lt_continuum

#print Cardinal.mk_set_nat /-
theorem mk_set_nat : (#Set ℕ) = 𝔠 := by simp
#align cardinal.mk_set_nat Cardinal.mk_set_nat
-/

#print Cardinal.continuum_pos /-
theorem continuum_pos : 0 < 𝔠 :=
  nat_lt_continuum 0
#align cardinal.continuum_pos Cardinal.continuum_pos
-/

#print Cardinal.continuum_ne_zero /-
theorem continuum_ne_zero : 𝔠 ≠ 0 :=
  continuum_pos.ne'
#align cardinal.continuum_ne_zero Cardinal.continuum_ne_zero
-/

/- warning: cardinal.aleph_one_le_continuum -> Cardinal.aleph_one_le_continuum is a dubious translation:
lean 3 declaration is
  LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.aleph.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) Cardinal.continuum.{u1}
but is expected to have type
  LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.aleph.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_one_le_continuum Cardinal.aleph_one_le_continuumₓ'. -/
theorem aleph_one_le_continuum : aleph 1 ≤ 𝔠 :=
  by
  rw [← succ_aleph_0]
  exact Order.succ_le_of_lt aleph_0_lt_continuum
#align cardinal.aleph_one_le_continuum Cardinal.aleph_one_le_continuum

#print Cardinal.continuum_toNat /-
@[simp]
theorem continuum_toNat : continuum.toNat = 0 :=
  toNat_apply_of_aleph0_le aleph0_le_continuum
#align cardinal.continuum_to_nat Cardinal.continuum_toNat
-/

/- warning: cardinal.continuum_to_part_enat -> Cardinal.continuum_toPartENat is a dubious translation:
lean 3 declaration is
  Eq.{1} PartENat (coeFn.{succ (succ u1), succ (succ u1)} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) (fun (_x : AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) => Cardinal.{u1} -> PartENat) (AddMonoidHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) Cardinal.toPartENat.{u1} Cardinal.continuum.{u1}) (Top.top.{0} PartENat PartENat.hasTop)
but is expected to have type
  Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Cardinal.{u1}) => PartENat) Cardinal.continuum.{u1}) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Cardinal.{u1}) => PartENat) _x) (AddHomClass.toFunLike.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddZeroClass.toAdd.{succ u1} Cardinal.{u1} (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) (AddZeroClass.toAdd.{0} PartENat (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) (AddMonoidHomClass.toAddHomClass.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat))) (AddMonoidHom.addMonoidHomClass.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))))) Cardinal.toPartENat.{u1} Cardinal.continuum.{u1}) (Top.top.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Cardinal.{u1}) => PartENat) Cardinal.continuum.{u1}) PartENat.instTopPartENat)
Case conversion may be inaccurate. Consider using '#align cardinal.continuum_to_part_enat Cardinal.continuum_toPartENatₓ'. -/
@[simp]
theorem continuum_toPartENat : continuum.toPartENat = ⊤ :=
  toPartENat_apply_of_aleph0_le aleph0_le_continuum
#align cardinal.continuum_to_part_enat Cardinal.continuum_toPartENat

/-!
### Addition
-/


/- warning: cardinal.aleph_0_add_continuum -> Cardinal.aleph0_add_continuum is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) Cardinal.aleph0.{u1} Cardinal.continuum.{u1}) Cardinal.continuum.{u1}
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) Cardinal.aleph0.{u1} Cardinal.continuum.{u1}) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_add_continuum Cardinal.aleph0_add_continuumₓ'. -/
@[simp]
theorem aleph0_add_continuum : ℵ₀ + 𝔠 = 𝔠 :=
  add_eq_right aleph0_le_continuum aleph0_le_continuum
#align cardinal.aleph_0_add_continuum Cardinal.aleph0_add_continuum

/- warning: cardinal.continuum_add_aleph_0 -> Cardinal.continuum_add_aleph0 is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) Cardinal.continuum.{u1} Cardinal.aleph0.{u1}) Cardinal.continuum.{u1}
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) Cardinal.continuum.{u1} Cardinal.aleph0.{u1}) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.continuum_add_aleph_0 Cardinal.continuum_add_aleph0ₓ'. -/
@[simp]
theorem continuum_add_aleph0 : 𝔠 + ℵ₀ = 𝔠 :=
  (add_comm _ _).trans aleph0_add_continuum
#align cardinal.continuum_add_aleph_0 Cardinal.continuum_add_aleph0

/- warning: cardinal.continuum_add_self -> Cardinal.continuum_add_self is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) Cardinal.continuum.{u1} Cardinal.continuum.{u1}) Cardinal.continuum.{u1}
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) Cardinal.continuum.{u1} Cardinal.continuum.{u1}) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.continuum_add_self Cardinal.continuum_add_selfₓ'. -/
@[simp]
theorem continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
  add_eq_right aleph0_le_continuum le_rfl
#align cardinal.continuum_add_self Cardinal.continuum_add_self

/- warning: cardinal.nat_add_continuum -> Cardinal.nat_add_continuum is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) Cardinal.continuum.{u1}) Cardinal.continuum.{u1}
but is expected to have type
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) Cardinal.continuum.{u1}) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.nat_add_continuum Cardinal.nat_add_continuumₓ'. -/
@[simp]
theorem nat_add_continuum (n : ℕ) : ↑n + 𝔠 = 𝔠 :=
  add_eq_right aleph0_le_continuum (nat_lt_continuum n).le
#align cardinal.nat_add_continuum Cardinal.nat_add_continuum

/- warning: cardinal.continuum_add_nat -> Cardinal.continuum_add_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) Cardinal.continuum.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) Cardinal.continuum.{u1}
but is expected to have type
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) Cardinal.continuum.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.continuum_add_nat Cardinal.continuum_add_natₓ'. -/
@[simp]
theorem continuum_add_nat (n : ℕ) : 𝔠 + n = 𝔠 :=
  (add_comm _ _).trans (nat_add_continuum n)
#align cardinal.continuum_add_nat Cardinal.continuum_add_nat

/-!
### Multiplication
-/


/- warning: cardinal.continuum_mul_self -> Cardinal.continuum_mul_self is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) Cardinal.continuum.{u1} Cardinal.continuum.{u1}) Cardinal.continuum.{u1}
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) Cardinal.continuum.{u1} Cardinal.continuum.{u1}) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.continuum_mul_self Cardinal.continuum_mul_selfₓ'. -/
@[simp]
theorem continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
  mul_eq_left aleph0_le_continuum le_rfl continuum_ne_zero
#align cardinal.continuum_mul_self Cardinal.continuum_mul_self

/- warning: cardinal.continuum_mul_aleph_0 -> Cardinal.continuum_mul_aleph0 is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) Cardinal.continuum.{u1} Cardinal.aleph0.{u1}) Cardinal.continuum.{u1}
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) Cardinal.continuum.{u1} Cardinal.aleph0.{u1}) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.continuum_mul_aleph_0 Cardinal.continuum_mul_aleph0ₓ'. -/
@[simp]
theorem continuum_mul_aleph0 : 𝔠 * ℵ₀ = 𝔠 :=
  mul_eq_left aleph0_le_continuum aleph0_le_continuum aleph0_ne_zero
#align cardinal.continuum_mul_aleph_0 Cardinal.continuum_mul_aleph0

/- warning: cardinal.aleph_0_mul_continuum -> Cardinal.aleph0_mul_continuum is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) Cardinal.aleph0.{u1} Cardinal.continuum.{u1}) Cardinal.continuum.{u1}
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) Cardinal.aleph0.{u1} Cardinal.continuum.{u1}) Cardinal.continuum.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_mul_continuum Cardinal.aleph0_mul_continuumₓ'. -/
@[simp]
theorem aleph0_mul_continuum : ℵ₀ * 𝔠 = 𝔠 :=
  (mul_comm _ _).trans continuum_mul_aleph0
#align cardinal.aleph_0_mul_continuum Cardinal.aleph0_mul_continuum

/- warning: cardinal.nat_mul_continuum -> Cardinal.nat_mul_continuum is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) Cardinal.continuum.{u1}) Cardinal.continuum.{u1})
but is expected to have type
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) Cardinal.continuum.{u1}) Cardinal.continuum.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.nat_mul_continuum Cardinal.nat_mul_continuumₓ'. -/
@[simp]
theorem nat_mul_continuum {n : ℕ} (hn : n ≠ 0) : ↑n * 𝔠 = 𝔠 :=
  mul_eq_right aleph0_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)
#align cardinal.nat_mul_continuum Cardinal.nat_mul_continuum

/- warning: cardinal.continuum_mul_nat -> Cardinal.continuum_mul_nat is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) Cardinal.continuum.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) Cardinal.continuum.{u1})
but is expected to have type
  forall {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) Cardinal.continuum.{u1} (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) Cardinal.continuum.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.continuum_mul_nat Cardinal.continuum_mul_natₓ'. -/
@[simp]
theorem continuum_mul_nat {n : ℕ} (hn : n ≠ 0) : 𝔠 * n = 𝔠 :=
  (mul_comm _ _).trans (nat_mul_continuum hn)
#align cardinal.continuum_mul_nat Cardinal.continuum_mul_nat

/-!
### Power
-/


#print Cardinal.aleph0_power_aleph0 /-
@[simp]
theorem aleph0_power_aleph0 : aleph0.{u} ^ aleph0.{u} = 𝔠 :=
  power_self_eq le_rfl
#align cardinal.aleph_0_power_aleph_0 Cardinal.aleph0_power_aleph0
-/

/- warning: cardinal.nat_power_aleph_0 -> Cardinal.nat_power_aleph0 is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, (LE.le.{0} Nat Nat.hasLe (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) n) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) Cardinal.aleph0.{u1}) Cardinal.continuum.{u1})
but is expected to have type
  forall {n : Nat}, (LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) n) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) Cardinal.aleph0.{u1}) Cardinal.continuum.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.nat_power_aleph_0 Cardinal.nat_power_aleph0ₓ'. -/
@[simp]
theorem nat_power_aleph0 {n : ℕ} (hn : 2 ≤ n) : (n ^ aleph0.{u} : Cardinal.{u}) = 𝔠 :=
  nat_power_eq le_rfl hn
#align cardinal.nat_power_aleph_0 Cardinal.nat_power_aleph0

#print Cardinal.continuum_power_aleph0 /-
@[simp]
theorem continuum_power_aleph0 : continuum.{u} ^ aleph0.{u} = 𝔠 := by
  rw [← two_power_aleph_0, ← power_mul, mul_eq_left le_rfl le_rfl aleph_0_ne_zero]
#align cardinal.continuum_power_aleph_0 Cardinal.continuum_power_aleph0
-/

end Cardinal

