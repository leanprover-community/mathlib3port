/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.group.commute
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Semiconj

/-!
# Commuting pairs of elements in monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the predicate `commute a b := a * b = b * a` and provide some operations on terms `(h :
commute a b)`. E.g., if `a`, `b`, and c are elements of a semiring, and that `hb : commute a b` and
`hc : commute a c`.  Then `hb.pow_left 5` proves `commute (a ^ 5) b` and `(hb.pow_right 2).add_right
(hb.mul_right hc)` proves `commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(hb.pow_left 5).eq]` rather than just `rw [hb.pow_left 5]`.

This file defines only a few operations (`mul_left`, `inv_right`, etc).  Other operations
(`pow_right`, field inverse etc) are in the files that define corresponding notions.

## Implementation details

Most of the proofs come from the properties of `semiconj_by`.
-/


variable {G : Type _}

#print Commute /-
/-- Two elements commute if `a * b = b * a`. -/
@[to_additive AddCommute "Two elements additively commute if `a + b = b + a`"]
def Commute {S : Type _} [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b
#align commute Commute
#align add_commute AddCommute
-/

namespace Commute

section Mul

variable {S : Type _} [Mul S]

#print Commute.eq /-
/-- Equality behind `commute a b`; useful for rewriting. -/
@[to_additive "Equality behind `add_commute a b`; useful for rewriting."]
protected theorem eq {a b : S} (h : Commute a b) : a * b = b * a :=
  h
#align commute.eq Commute.eq
#align add_commute.eq AddCommute.eq
-/

#print Commute.refl /-
/-- Any element commutes with itself. -/
@[refl, simp, to_additive "Any element commutes with itself."]
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a * a)
#align commute.refl Commute.refl
#align add_commute.refl AddCommute.refl
-/

#print Commute.symm /-
/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[symm, to_additive "If `a` commutes with `b`, then `b` commutes with `a`."]
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h
#align commute.symm Commute.symm
#align add_commute.symm AddCommute.symm
-/

#print Commute.semiconjBy /-
@[to_additive]
protected theorem semiconjBy {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h
#align commute.semiconj_by Commute.semiconjBy
#align add_commute.semiconj_by AddCommute.semiconjBy
-/

#print Commute.symm_iff /-
@[to_additive]
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩
#align commute.symm_iff Commute.symm_iff
#align add_commute.symm_iff AddCommute.symm_iff
-/

@[to_additive]
instance : IsRefl S Commute :=
  ⟨Commute.refl⟩

#print Commute.on_isRefl /-
-- This instance is useful for `finset.noncomm_prod`
@[to_additive]
instance on_isRefl {f : G → S} : IsRefl G fun a b => Commute (f a) (f b) :=
  ⟨fun _ => Commute.refl _⟩
#align commute.on_is_refl Commute.on_isRefl
#align add_commute.on_is_refl AddCommute.on_isRefl
-/

end Mul

section Semigroup

variable {S : Type _} [Semigroup S] {a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[simp, to_additive "If `a` commutes with both `b` and `c`, then it commutes with their sum."]
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  hab.mul_right hac
#align commute.mul_right Commute.mul_rightₓ
#align add_commute.add_right AddCommute.add_rightₓ

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[simp, to_additive "If both `a` and `b` commute with `c`, then their product commutes with `c`."]
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  hac.mul_left hbc
#align commute.mul_left Commute.mul_leftₓ
#align add_commute.add_left AddCommute.add_leftₓ

@[to_additive]
protected theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b := by
  simp only [mul_assoc, h.eq]
#align commute.right_comm Commute.right_commₓ
#align add_commute.right_comm AddCommute.right_commₓ

@[to_additive]
protected theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) := by
  simp only [← mul_assoc, h.eq]
#align commute.left_comm Commute.left_commₓ
#align add_commute.left_comm AddCommute.left_commₓ

end Semigroup

@[to_additive]
protected theorem all {S : Type _} [CommSemigroup S] (a b : S) : Commute a b :=
  mul_comm a b
#align commute.all Commute.allₓ
#align add_commute.all AddCommute.allₓ

section MulOneClass

variable {M : Type _} [MulOneClass M]

@[simp, to_additive]
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a
#align commute.one_right Commute.one_rightₓ
#align add_commute.zero_right AddCommute.zero_rightₓ

@[simp, to_additive]
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a
#align commute.one_left Commute.one_leftₓ
#align add_commute.zero_left AddCommute.zero_leftₓ

end MulOneClass

section Monoid

variable {M : Type _} [Monoid M] {a b : M} {u u₁ u₂ : Mˣ}

@[simp, to_additive]
theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) :=
  h.pow_right n
#align commute.pow_right Commute.pow_rightₓ
#align add_commute.nsmul_right AddCommute.smul_rightₓ

@[simp, to_additive]
theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm
#align commute.pow_left Commute.pow_leftₓ
#align add_commute.nsmul_left AddCommute.smul_leftₓ

@[simp, to_additive]
theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) :=
  (h.pow_left m).pow_right n
#align commute.pow_pow Commute.pow_powₓ
#align add_commute.nsmul_nsmul AddCommute.smul_smulₓ

@[simp, to_additive]
theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n
#align commute.self_pow Commute.self_powₓ
#align add_commute.self_nsmul AddCommute.self_smulₓ

/- warning: commute.pow_self -> Commute.pow_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : M) (n : Nat), Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a n) a
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : M) (n : Nat), Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a n) a
Case conversion may be inaccurate. Consider using '#align commute.pow_self Commute.pow_selfₓ'. -/
@[simp, to_additive]
theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n
#align commute.pow_self Commute.pow_self

@[simp, to_additive]
theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n
#align commute.pow_pow_self Commute.pow_pow_selfₓ
#align add_commute.nsmul_nsmul_self AddCommute.smul_smul_selfₓ

/- warning: pow_succ' -> pow_succ' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : M) (n : Nat), Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a n) a)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : M) (n : Nat), Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) a n) a)
Case conversion may be inaccurate. Consider using '#align pow_succ' pow_succ'ₓ'. -/
@[to_additive succ_nsmul']
theorem pow_succ' (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  (pow_succ a n).trans (self_pow _ _)
#align pow_succ' pow_succ'
#align succ_nsmul' succ_nsmul'

/- warning: commute.units_inv_right -> Commute.units_inv_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {u : Units.{u1} M _inst_1}, (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u)) -> (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) (Inv.inv.{u1} (Units.{u1} M _inst_1) (Units.hasInv.{u1} M _inst_1) u)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {u : Units.{u1} M _inst_1}, (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a (Units.val.{u1} M _inst_1 u)) -> (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a (Units.val.{u1} M _inst_1 (Inv.inv.{u1} (Units.{u1} M _inst_1) (Units.instInvUnits.{u1} M _inst_1) u)))
Case conversion may be inaccurate. Consider using '#align commute.units_inv_right Commute.units_inv_rightₓ'. -/
@[to_additive]
theorem units_inv_right : Commute a u → Commute a ↑u⁻¹ :=
  SemiconjBy.units_inv_right
#align commute.units_inv_right Commute.units_inv_right
#align add_commute.add_units_neg_right AddCommute.addUnits_neg_right

/- warning: commute.units_inv_right_iff -> Commute.units_inv_right_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {u : Units.{u1} M _inst_1}, Iff (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) (Inv.inv.{u1} (Units.{u1} M _inst_1) (Units.hasInv.{u1} M _inst_1) u))) (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {u : Units.{u1} M _inst_1}, Iff (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a (Units.val.{u1} M _inst_1 (Inv.inv.{u1} (Units.{u1} M _inst_1) (Units.instInvUnits.{u1} M _inst_1) u))) (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a (Units.val.{u1} M _inst_1 u))
Case conversion may be inaccurate. Consider using '#align commute.units_inv_right_iff Commute.units_inv_right_iffₓ'. -/
@[simp, to_additive]
theorem units_inv_right_iff : Commute a ↑u⁻¹ ↔ Commute a u :=
  SemiconjBy.units_inv_right_iff
#align commute.units_inv_right_iff Commute.units_inv_right_iff
#align add_commute.add_units_neg_right_iff AddCommute.addUnits_neg_right_iff

/- warning: commute.units_inv_left -> Commute.units_inv_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {u : Units.{u1} M _inst_1}, (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u) a) -> (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) (Inv.inv.{u1} (Units.{u1} M _inst_1) (Units.hasInv.{u1} M _inst_1) u)) a)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {u : Units.{u1} M _inst_1}, (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Units.val.{u1} M _inst_1 u) a) -> (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Units.val.{u1} M _inst_1 (Inv.inv.{u1} (Units.{u1} M _inst_1) (Units.instInvUnits.{u1} M _inst_1) u)) a)
Case conversion may be inaccurate. Consider using '#align commute.units_inv_left Commute.units_inv_leftₓ'. -/
@[to_additive]
theorem units_inv_left : Commute (↑u) a → Commute (↑u⁻¹) a :=
  SemiconjBy.units_inv_symm_left
#align commute.units_inv_left Commute.units_inv_left
#align add_commute.add_units_neg_left AddCommute.addUnits_neg_left

/- warning: commute.units_inv_left_iff -> Commute.units_inv_left_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {u : Units.{u1} M _inst_1}, Iff (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) (Inv.inv.{u1} (Units.{u1} M _inst_1) (Units.hasInv.{u1} M _inst_1) u)) a) (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u) a)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {u : Units.{u1} M _inst_1}, Iff (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Units.val.{u1} M _inst_1 (Inv.inv.{u1} (Units.{u1} M _inst_1) (Units.instInvUnits.{u1} M _inst_1) u)) a) (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Units.val.{u1} M _inst_1 u) a)
Case conversion may be inaccurate. Consider using '#align commute.units_inv_left_iff Commute.units_inv_left_iffₓ'. -/
@[simp, to_additive]
theorem units_inv_left_iff : Commute (↑u⁻¹) a ↔ Commute (↑u) a :=
  SemiconjBy.units_inv_symm_left_iff
#align commute.units_inv_left_iff Commute.units_inv_left_iff
#align add_commute.add_units_neg_left_iff AddCommute.addUnits_neg_left_iff

/- warning: commute.units_coe -> Commute.units_val is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {u₁ : Units.{u1} M _inst_1} {u₂ : Units.{u1} M _inst_1}, (Commute.{u1} (Units.{u1} M _inst_1) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1)) u₁ u₂) -> (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u₁) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u₂))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {u₁ : Units.{u1} M _inst_1} {u₂ : Units.{u1} M _inst_1}, (Commute.{u1} (Units.{u1} M _inst_1) (MulOneClass.toMul.{u1} (Units.{u1} M _inst_1) (Units.instMulOneClassUnits.{u1} M _inst_1)) u₁ u₂) -> (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Units.val.{u1} M _inst_1 u₁) (Units.val.{u1} M _inst_1 u₂))
Case conversion may be inaccurate. Consider using '#align commute.units_coe Commute.units_valₓ'. -/
@[to_additive]
theorem units_val : Commute u₁ u₂ → Commute (u₁ : M) u₂ :=
  SemiconjBy.units_val
#align commute.units_coe Commute.units_val
#align add_commute.add_units_coe AddCommute.addUnits_val

/- warning: commute.units_of_coe -> Commute.units_of_val is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {u₁ : Units.{u1} M _inst_1} {u₂ : Units.{u1} M _inst_1}, (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u₁) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u₂)) -> (Commute.{u1} (Units.{u1} M _inst_1) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1)) u₁ u₂)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {u₁ : Units.{u1} M _inst_1} {u₂ : Units.{u1} M _inst_1}, (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Units.val.{u1} M _inst_1 u₁) (Units.val.{u1} M _inst_1 u₂)) -> (Commute.{u1} (Units.{u1} M _inst_1) (MulOneClass.toMul.{u1} (Units.{u1} M _inst_1) (Units.instMulOneClassUnits.{u1} M _inst_1)) u₁ u₂)
Case conversion may be inaccurate. Consider using '#align commute.units_of_coe Commute.units_of_valₓ'. -/
@[to_additive]
theorem units_of_val : Commute (u₁ : M) u₂ → Commute u₁ u₂ :=
  SemiconjBy.units_of_val
#align commute.units_of_coe Commute.units_of_val
#align add_commute.add_units_of_coe AddCommute.addUnits_of_val

/- warning: commute.units_coe_iff -> Commute.units_val_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {u₁ : Units.{u1} M _inst_1} {u₂ : Units.{u1} M _inst_1}, Iff (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u₁) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u₂)) (Commute.{u1} (Units.{u1} M _inst_1) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1)) u₁ u₂)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {u₁ : Units.{u1} M _inst_1} {u₂ : Units.{u1} M _inst_1}, Iff (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Units.val.{u1} M _inst_1 u₁) (Units.val.{u1} M _inst_1 u₂)) (Commute.{u1} (Units.{u1} M _inst_1) (MulOneClass.toMul.{u1} (Units.{u1} M _inst_1) (Units.instMulOneClassUnits.{u1} M _inst_1)) u₁ u₂)
Case conversion may be inaccurate. Consider using '#align commute.units_coe_iff Commute.units_val_iffₓ'. -/
@[simp, to_additive]
theorem units_val_iff : Commute (u₁ : M) u₂ ↔ Commute u₁ u₂ :=
  SemiconjBy.units_val_iff
#align commute.units_coe_iff Commute.units_val_iff
#align add_commute.add_units_coe_iff AddCommute.addUnits_val_iff

/- warning: units.left_of_mul -> Units.leftOfMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (u : Units.{u1} M _inst_1) (a : M) (b : M), (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u)) -> (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a b) -> (Units.{u1} M _inst_1)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (u : Units.{u1} M _inst_1) (a : M) (b : M), (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b) (Units.val.{u1} M _inst_1 u)) -> (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a b) -> (Units.{u1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align units.left_of_mul Units.leftOfMulₓ'. -/
/-- If the product of two commuting elements is a unit, then the left multiplier is a unit. -/
@[to_additive
      "If the sum of two commuting elements is an additive unit, then the left summand is an\nadditive unit."]
def Units.leftOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ
    where
  val := a
  inv := b * ↑u⁻¹
  val_inv := by rw [← mul_assoc, hu, u.mul_inv]
  inv_val := by
    have : Commute a u := hu ▸ (Commute.refl _).mul_right hc
    rw [← this.units_inv_right.right_comm, ← hc.eq, hu, u.mul_inv]
#align units.left_of_mul Units.leftOfMul
#align add_units.left_of_add AddUnits.leftOfAdd

/- warning: units.right_of_mul -> Units.rightOfMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (u : Units.{u1} M _inst_1) (a : M) (b : M), (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) u)) -> (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a b) -> (Units.{u1} M _inst_1)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (u : Units.{u1} M _inst_1) (a : M) (b : M), (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b) (Units.val.{u1} M _inst_1 u)) -> (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a b) -> (Units.{u1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align units.right_of_mul Units.rightOfMulₓ'. -/
/-- If the product of two commuting elements is a unit, then the right multiplier is a unit. -/
@[to_additive
      "If the sum of two commuting elements is an additive unit, then the right summand is\nan additive unit."]
def Units.rightOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ :=
  u.leftOfMul b a (hc.Eq ▸ hu) hc.symm
#align units.right_of_mul Units.rightOfMul
#align add_units.right_of_add AddUnits.rightOfAdd

/- warning: commute.is_unit_mul_iff -> Commute.isUnit_mul_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {b : M}, (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a b) -> (Iff (IsUnit.{u1} M _inst_1 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b)) (And (IsUnit.{u1} M _inst_1 a) (IsUnit.{u1} M _inst_1 b)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M} {b : M}, (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) a b) -> (Iff (IsUnit.{u1} M _inst_1 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b)) (And (IsUnit.{u1} M _inst_1 a) (IsUnit.{u1} M _inst_1 b)))
Case conversion may be inaccurate. Consider using '#align commute.is_unit_mul_iff Commute.isUnit_mul_iffₓ'. -/
@[to_additive]
theorem isUnit_mul_iff (h : Commute a b) : IsUnit (a * b) ↔ IsUnit a ∧ IsUnit b :=
  ⟨fun ⟨u, hu⟩ => ⟨(u.leftOfMul a b hu.symm h).IsUnit, (u.rightOfMul a b hu.symm h).IsUnit⟩,
    fun H => H.1.mul H.2⟩
#align commute.is_unit_mul_iff Commute.isUnit_mul_iff
#align add_commute.is_add_unit_add_iff AddCommute.isAddUnit_add_iff

/- warning: is_unit_mul_self_iff -> isUnit_mul_self_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M}, Iff (IsUnit.{u1} M _inst_1 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a a)) (IsUnit.{u1} M _inst_1 a)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {a : M}, Iff (IsUnit.{u1} M _inst_1 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a a)) (IsUnit.{u1} M _inst_1 a)
Case conversion may be inaccurate. Consider using '#align is_unit_mul_self_iff isUnit_mul_self_iffₓ'. -/
@[simp, to_additive]
theorem isUnit_mul_self_iff : IsUnit (a * a) ↔ IsUnit a :=
  (Commute.refl a).is_unit_mul_iff.trans (and_self_iff _)
#align is_unit_mul_self_iff isUnit_mul_self_iff
#align is_add_unit_add_self_iff isAddUnit_add_self_iff

end Monoid

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

/- warning: commute.inv_inv -> Commute.inv_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) a) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) b))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) a) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) b))
Case conversion may be inaccurate. Consider using '#align commute.inv_inv Commute.inv_invₓ'. -/
@[to_additive]
theorem inv_inv : Commute a b → Commute a⁻¹ b⁻¹ :=
  SemiconjBy.inv_inv_symm
#align commute.inv_inv Commute.inv_inv
#align add_commute.neg_neg AddCommute.neg_neg

/- warning: commute.inv_inv_iff -> Commute.inv_inv_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] {a : G} {b : G}, Iff (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) a) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)) b)) (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)))) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} G] {a : G} {b : G}, Iff (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) a) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G _inst_1))) b)) (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G _inst_1)))) a b)
Case conversion may be inaccurate. Consider using '#align commute.inv_inv_iff Commute.inv_inv_iffₓ'. -/
@[simp, to_additive]
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_inv_symm_iff
#align commute.inv_inv_iff Commute.inv_inv_iff
#align add_commute.neg_neg_iff AddCommute.neg_neg_iff

end DivisionMonoid

section Group

variable [Group G] {a b : G}

/- warning: commute.inv_right -> Commute.inv_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b))
Case conversion may be inaccurate. Consider using '#align commute.inv_right Commute.inv_rightₓ'. -/
@[to_additive]
theorem inv_right : Commute a b → Commute a b⁻¹ :=
  SemiconjBy.inv_right
#align commute.inv_right Commute.inv_right
#align add_commute.neg_right AddCommute.neg_right

/- warning: commute.inv_right_iff -> Commute.inv_right_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) b)) (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) b)) (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b)
Case conversion may be inaccurate. Consider using '#align commute.inv_right_iff Commute.inv_right_iffₓ'. -/
@[simp, to_additive]
theorem inv_right_iff : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff
#align commute.inv_right_iff Commute.inv_right_iff
#align add_commute.neg_right_iff AddCommute.neg_right_iff

/- warning: commute.inv_left -> Commute.inv_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) b)
Case conversion may be inaccurate. Consider using '#align commute.inv_left Commute.inv_leftₓ'. -/
@[to_additive]
theorem inv_left : Commute a b → Commute a⁻¹ b :=
  SemiconjBy.inv_symm_left
#align commute.inv_left Commute.inv_left
#align add_commute.neg_left AddCommute.neg_left

/- warning: commute.inv_left_iff -> Commute.inv_left_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) b) (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, Iff (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) b) (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b)
Case conversion may be inaccurate. Consider using '#align commute.inv_left_iff Commute.inv_left_iffₓ'. -/
@[simp, to_additive]
theorem inv_left_iff : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff
#align commute.inv_left_iff Commute.inv_left_iff
#align add_commute.neg_left_iff AddCommute.neg_left_iff

/- warning: commute.inv_mul_cancel -> Commute.inv_mul_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) b) a) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) b) a) b)
Case conversion may be inaccurate. Consider using '#align commute.inv_mul_cancel Commute.inv_mul_cancelₓ'. -/
@[to_additive]
protected theorem inv_mul_cancel (h : Commute a b) : a⁻¹ * b * a = b := by
  rw [h.inv_left.eq, inv_mul_cancel_right]
#align commute.inv_mul_cancel Commute.inv_mul_cancel
#align add_commute.neg_add_cancel AddCommute.neg_add_cancel

/- warning: commute.inv_mul_cancel_assoc -> Commute.inv_mul_cancel_assoc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a)) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a)) b)
Case conversion may be inaccurate. Consider using '#align commute.inv_mul_cancel_assoc Commute.inv_mul_cancel_assocₓ'. -/
@[to_additive]
theorem inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b := by
  rw [← mul_assoc, h.inv_mul_cancel]
#align commute.inv_mul_cancel_assoc Commute.inv_mul_cancel_assoc
#align add_commute.neg_add_cancel_assoc AddCommute.neg_add_cancel_assoc

/- warning: commute.mul_inv_cancel -> Commute.mul_inv_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a)) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a)) b)
Case conversion may be inaccurate. Consider using '#align commute.mul_inv_cancel Commute.mul_inv_cancelₓ'. -/
@[to_additive]
protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]
#align commute.mul_inv_cancel Commute.mul_inv_cancel
#align add_commute.add_neg_cancel AddCommute.add_neg_cancel

/- warning: commute.mul_inv_cancel_assoc -> Commute.mul_inv_cancel_assoc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))) b)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {a : G} {b : G}, (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) a b) -> (Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))) b)
Case conversion may be inaccurate. Consider using '#align commute.mul_inv_cancel_assoc Commute.mul_inv_cancel_assocₓ'. -/
@[to_additive]
theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, h.mul_inv_cancel]
#align commute.mul_inv_cancel_assoc Commute.mul_inv_cancel_assoc
#align add_commute.add_neg_cancel_assoc AddCommute.add_neg_cancel_assoc

end Group

end Commute

section CommGroup

variable [CommGroup G] (a b : G)

/- warning: mul_inv_cancel_comm -> mul_inv_cancel_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) a)) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a b) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) a)) b
Case conversion may be inaccurate. Consider using '#align mul_inv_cancel_comm mul_inv_cancel_commₓ'. -/
@[simp, to_additive]
theorem mul_inv_cancel_comm : a * b * a⁻¹ = b :=
  (Commute.all a b).mul_inv_cancel
#align mul_inv_cancel_comm mul_inv_cancel_comm
#align add_neg_cancel_comm add_neg_cancel_comm

/- warning: mul_inv_cancel_comm_assoc -> mul_inv_cancel_comm_assoc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) a))) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) a (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) a))) b
Case conversion may be inaccurate. Consider using '#align mul_inv_cancel_comm_assoc mul_inv_cancel_comm_assocₓ'. -/
@[simp, to_additive]
theorem mul_inv_cancel_comm_assoc : a * (b * a⁻¹) = b :=
  (Commute.all a b).mul_inv_cancel_assoc
#align mul_inv_cancel_comm_assoc mul_inv_cancel_comm_assoc
#align add_neg_cancel_comm_assoc add_neg_cancel_comm_assoc

/- warning: inv_mul_cancel_comm -> inv_mul_cancel_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) a) b) a) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) a) b) a) b
Case conversion may be inaccurate. Consider using '#align inv_mul_cancel_comm inv_mul_cancel_commₓ'. -/
@[simp, to_additive]
theorem inv_mul_cancel_comm : a⁻¹ * b * a = b :=
  (Commute.all a b).inv_mul_cancel
#align inv_mul_cancel_comm inv_mul_cancel_comm
#align neg_add_cancel_comm neg_add_cancel_comm

/- warning: inv_mul_cancel_comm_assoc -> inv_mul_cancel_comm_assoc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) a) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b a)) b
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1))))) a) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))))) b a)) b
Case conversion may be inaccurate. Consider using '#align inv_mul_cancel_comm_assoc inv_mul_cancel_comm_assocₓ'. -/
@[simp, to_additive]
theorem inv_mul_cancel_comm_assoc : a⁻¹ * (b * a) = b :=
  (Commute.all a b).inv_mul_cancel_assoc
#align inv_mul_cancel_comm_assoc inv_mul_cancel_comm_assoc
#align neg_add_cancel_comm_assoc neg_add_cancel_comm_assoc

end CommGroup

