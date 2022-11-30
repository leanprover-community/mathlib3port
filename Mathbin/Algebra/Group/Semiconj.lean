/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Some proofs and docs came from `algebra/commute` (c) Neil Strickland
-/
import Mathbin.Algebra.Group.Units

/-!
# Semiconjugate elements of a semigroup

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/717
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`semiconj_by a x y`), if `a * x = y * a`.
In this file we  provide operations on `semiconj_by _ _ _`.

In the names of these operations, we treat `a` as the “left” argument, and both `x` and `y` as
“right” arguments. This way most names in this file agree with the names of the corresponding lemmas
for `commute a b = semiconj_by a b b`. As a side effect, some lemmas have only `_right` version.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(h.pow_right 5).eq]` rather than just `rw [h.pow_right 5]`.

This file provides only basic operations (`mul_left`, `mul_right`, `inv_right` etc). Other
operations (`pow_right`, field inverse etc) are in the files that define corresponding notions.
-/


universe u v

variable {G : Type _}

#print SemiconjBy /-
/-- `x` is semiconjugate to `y` by `a`, if `a * x = y * a`. -/
@[to_additive AddSemiconjBy "`x` is additive semiconjugate to `y` by `a` if `a + x = y + a`"]
def SemiconjBy {M : Type u} [Mul M] (a x y : M) : Prop :=
  a * x = y * a
#align semiconj_by SemiconjBy
-/

namespace SemiconjBy

#print SemiconjBy.eq /-
/-- Equality behind `semiconj_by a x y`; useful for rewriting. -/
@[to_additive "Equality behind `add_semiconj_by a x y`; useful for rewriting."]
protected theorem eq {S : Type u} [Mul S] {a x y : S} (h : SemiconjBy a x y) : a * x = y * a :=
  h
#align semiconj_by.eq SemiconjBy.eq
-/

section Semigroup

variable {S : Type u} [Semigroup S] {a b x y z x' y' : S}

/- warning: semiconj_by.mul_right -> SemiconjBy.mul_right is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u}} [_inst_1 : Semigroup.{u} S] {a : S} {x : S} {y : S} {x' : S} {y' : S}, (SemiconjBy.{u} S (Semigroup.toHasMul.{u} S _inst_1) a x y) -> (SemiconjBy.{u} S (Semigroup.toHasMul.{u} S _inst_1) a x' y') -> (SemiconjBy.{u} S (Semigroup.toHasMul.{u} S _inst_1) a (HMul.hMul.{u, u, u} S S S (instHMul.{u} S (Semigroup.toHasMul.{u} S _inst_1)) x x') (HMul.hMul.{u, u, u} S S S (instHMul.{u} S (Semigroup.toHasMul.{u} S _inst_1)) y y'))
but is expected to have type
  forall {S : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.77 : Semigroup.{u_1} S] {a : S} {x : S} {y : S} {x' : S} {y' : S}, (SemiconjBy.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Semiconj._hyg.77) a x y) -> (SemiconjBy.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Semiconj._hyg.77) a x' y') -> (SemiconjBy.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Semiconj._hyg.77) a (HMul.hMul.{u_1, u_1, u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Semiconj._hyg.77)) x x') (HMul.hMul.{u_1, u_1, u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Semiconj._hyg.77)) y y'))
Case conversion may be inaccurate. Consider using '#align semiconj_by.mul_right SemiconjBy.mul_rightₓ'. -/
/-- If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x * x'` to `y * y'`. -/
@[simp,
  to_additive
      "If `a` semiconjugates `x` to `y` and `x'` to `y'`, then it semiconjugates\n`x + x'` to `y + y'`."]
theorem mul_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x * x') (y * y') := by unfold SemiconjBy <;> assoc_rw [h.eq, h'.eq]
#align semiconj_by.mul_right SemiconjBy.mul_right

/- warning: semiconj_by.mul_left -> SemiconjBy.mul_left is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u}} [_inst_1 : Semigroup.{u} S] {a : S} {b : S} {x : S} {y : S} {z : S}, (SemiconjBy.{u} S (Semigroup.toHasMul.{u} S _inst_1) a y z) -> (SemiconjBy.{u} S (Semigroup.toHasMul.{u} S _inst_1) b x y) -> (SemiconjBy.{u} S (Semigroup.toHasMul.{u} S _inst_1) (HMul.hMul.{u, u, u} S S S (instHMul.{u} S (Semigroup.toHasMul.{u} S _inst_1)) a b) x z)
but is expected to have type
  forall {S : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.150 : Semigroup.{u_1} S] {a : S} {b : S} {x : S} {y : S} {z : S}, (SemiconjBy.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Semiconj._hyg.150) a y z) -> (SemiconjBy.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Semiconj._hyg.150) b x y) -> (SemiconjBy.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Semiconj._hyg.150) (HMul.hMul.{u_1, u_1, u_1} S S S (instHMul.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Semiconj._hyg.150)) a b) x z)
Case conversion may be inaccurate. Consider using '#align semiconj_by.mul_left SemiconjBy.mul_leftₓ'. -/
/-- If both `a` and `b` semiconjugate `x` to `y`, then so does `a * b`. -/
@[to_additive "If both `a` and `b` semiconjugate `x` to `y`, then so does `a + b`."]
theorem mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b x y) : SemiconjBy (a * b) x z := by
  unfold SemiconjBy <;> assoc_rw [hb.eq, ha.eq, mul_assoc]
#align semiconj_by.mul_left SemiconjBy.mul_left

/- warning: semiconj_by.transitive -> SemiconjBy.transitive is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u}} [_inst_1 : Semigroup.{u} S], Transitive.{succ u} S (fun (a : S) (b : S) => Exists.{succ u} S (fun (c : S) => SemiconjBy.{u} S (Semigroup.toHasMul.{u} S _inst_1) c a b))
but is expected to have type
  forall {S : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.218 : Semigroup.{u_1} S], Transitive.{succ u_1} S (fun (a : S) (b : S) => Exists.{succ u_1} S (fun (c : S) => SemiconjBy.{u_1} S (Semigroup.toMul.{u_1} S inst._@.Mathlib.Algebra.Group.Semiconj._hyg.218) c a b))
Case conversion may be inaccurate. Consider using '#align semiconj_by.transitive SemiconjBy.transitiveₓ'. -/
/-- The relation “there exists an element that semiconjugates `a` to `b`” on a semigroup
is transitive. -/
@[to_additive
      "The relation “there exists an element that semiconjugates `a` to `b`” on an additive\nsemigroup is transitive."]
protected theorem transitive : Transitive fun a b : S => ∃ c, SemiconjBy c a b :=
  fun a b c ⟨x, hx⟩ ⟨y, hy⟩ => ⟨y * x, hy.mul_left hx⟩
#align semiconj_by.transitive SemiconjBy.transitive

end Semigroup

section MulOneClass

variable {M : Type u} [MulOneClass M]

/- warning: semiconj_by.one_right -> SemiconjBy.one_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M] (a : M), SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M _inst_1) a (OfNat.ofNat.{u} M 1 (OfNat.mk.{u} M 1 (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1)))) (OfNat.ofNat.{u} M 1 (OfNat.mk.{u} M 1 (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.363 : MulOneClass.{u_1} M] (a : M), SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.363) a (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (MulOneClass.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.363))) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (MulOneClass.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.363)))
Case conversion may be inaccurate. Consider using '#align semiconj_by.one_right SemiconjBy.one_rightₓ'. -/
/-- Any element semiconjugates `1` to `1`. -/
@[simp, to_additive "Any element additively semiconjugates `0` to `0`."]
theorem one_right (a : M) : SemiconjBy a 1 1 := by rw [SemiconjBy, mul_one, one_mul]
#align semiconj_by.one_right SemiconjBy.one_right

/- warning: semiconj_by.one_left -> SemiconjBy.one_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M] (x : M), SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M _inst_1) (OfNat.ofNat.{u} M 1 (OfNat.mk.{u} M 1 (One.one.{u} M (MulOneClass.toHasOne.{u} M _inst_1)))) x x
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.408 : MulOneClass.{u_1} M] (x : M), SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.408) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (MulOneClass.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.408))) x x
Case conversion may be inaccurate. Consider using '#align semiconj_by.one_left SemiconjBy.one_leftₓ'. -/
/-- One semiconjugates any element to itself. -/
@[simp, to_additive "Zero additively semiconjugates any element to itself."]
theorem one_left (x : M) : SemiconjBy 1 x x :=
  Eq.symm <| one_right x
#align semiconj_by.one_left SemiconjBy.one_left

/- warning: semiconj_by.reflexive -> SemiconjBy.reflexive is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : MulOneClass.{u} M], Reflexive.{succ u} M (fun (a : M) (b : M) => Exists.{succ u} M (fun (c : M) => SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M _inst_1) c a b))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.427 : MulOneClass.{u_1} M], Reflexive.{succ u_1} M (fun (a : M) (b : M) => Exists.{succ u_1} M (fun (c : M) => SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.427) c a b))
Case conversion may be inaccurate. Consider using '#align semiconj_by.reflexive SemiconjBy.reflexiveₓ'. -/
/-- The relation “there exists an element that semiconjugates `a` to `b`” on a monoid (or, more
generally, on ` mul_one_class` type) is reflexive. -/
@[to_additive
      "The relation “there exists an element that semiconjugates `a` to `b`” on an additive\nmonoid (or, more generally, on a `add_zero_class` type) is reflexive."]
protected theorem reflexive : Reflexive fun a b : M => ∃ c, SemiconjBy c a b := fun a =>
  ⟨1, one_left a⟩
#align semiconj_by.reflexive SemiconjBy.reflexive

end MulOneClass

section Monoid

variable {M : Type u} [Monoid M]

/- warning: semiconj_by.units_inv_right -> SemiconjBy.units_inv_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : Monoid.{u} M] {a : M} {x : Units.{u} M _inst_1} {y : Units.{u} M _inst_1}, (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) x) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) y)) -> (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) (Inv.inv.{u} (Units.{u} M _inst_1) (Units.hasInv.{u} M _inst_1) x)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) (Inv.inv.{u} (Units.{u} M _inst_1) (Units.hasInv.{u} M _inst_1) y)))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482 : Monoid.{u_1} M] {a : M} {x : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482} {y : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482}, (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482)) a (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482 x) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482 y)) -> (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482)) a (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482 (Inv.inv.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482) (Units.instInvUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482) x)) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482 (Inv.inv.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482) (Units.instInvUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.482) y)))
Case conversion may be inaccurate. Consider using '#align semiconj_by.units_inv_right SemiconjBy.units_inv_rightₓ'. -/
/-- If `a` semiconjugates a unit `x` to a unit `y`, then it semiconjugates `x⁻¹` to `y⁻¹`. -/
@[to_additive
      "If `a` semiconjugates an additive unit `x` to an additive unit `y`, then it\nsemiconjugates `-x` to `-y`."]
theorem units_inv_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹ :=
  calc
    a * ↑x⁻¹ = ↑y⁻¹ * (y * a) * ↑x⁻¹ := by rw [Units.inv_mul_cancel_left]
    _ = ↑y⁻¹ * a := by rw [← h.eq, mul_assoc, Units.mul_inv_cancel_right]
    
#align semiconj_by.units_inv_right SemiconjBy.units_inv_right

/- warning: semiconj_by.units_inv_right_iff -> SemiconjBy.units_inv_right_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : Monoid.{u} M] {a : M} {x : Units.{u} M _inst_1} {y : Units.{u} M _inst_1}, Iff (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) (Inv.inv.{u} (Units.{u} M _inst_1) (Units.hasInv.{u} M _inst_1) x)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) (Inv.inv.{u} (Units.{u} M _inst_1) (Units.hasInv.{u} M _inst_1) y))) (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) x) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) y))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624 : Monoid.{u_1} M] {a : M} {x : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624} {y : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624}, Iff (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624)) a (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624 (Inv.inv.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624) (Units.instInvUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624) x)) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624 (Inv.inv.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624) (Units.instInvUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624) y))) (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624)) a (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624 x) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.624 y))
Case conversion may be inaccurate. Consider using '#align semiconj_by.units_inv_right_iff SemiconjBy.units_inv_right_iffₓ'. -/
@[simp, to_additive]
theorem units_inv_right_iff {a : M} {x y : Mˣ} : SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y :=
  ⟨units_inv_right, units_inv_right⟩
#align semiconj_by.units_inv_right_iff SemiconjBy.units_inv_right_iff

/- warning: semiconj_by.units_inv_symm_left -> SemiconjBy.units_inv_symm_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : Monoid.{u} M] {a : Units.{u} M _inst_1} {x : M} {y : M}, (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) a) x y) -> (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) (Inv.inv.{u} (Units.{u} M _inst_1) (Units.hasInv.{u} M _inst_1) a)) y x)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.665 : Monoid.{u_1} M] {a : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.665} {x : M} {y : M}, (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.665)) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.665 a) x y) -> (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.665)) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.665 (Inv.inv.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.665) (Units.instInvUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.665) a)) y x)
Case conversion may be inaccurate. Consider using '#align semiconj_by.units_inv_symm_left SemiconjBy.units_inv_symm_leftₓ'. -/
/-- If a unit `a` semiconjugates `x` to `y`, then `a⁻¹` semiconjugates `y` to `x`. -/
@[to_additive
      "If an additive unit `a` semiconjugates `x` to `y`, then `-a` semiconjugates `y` to\n`x`."]
theorem units_inv_symm_left {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x :=
  calc
    ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) := by rw [Units.mul_inv_cancel_right]
    _ = x * ↑a⁻¹ := by rw [← h.eq, ← mul_assoc, Units.inv_mul_cancel_left]
    
#align semiconj_by.units_inv_symm_left SemiconjBy.units_inv_symm_left

/- warning: semiconj_by.units_inv_symm_left_iff -> SemiconjBy.units_inv_symm_left_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : Monoid.{u} M] {a : Units.{u} M _inst_1} {x : M} {y : M}, Iff (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) (Inv.inv.{u} (Units.{u} M _inst_1) (Units.hasInv.{u} M _inst_1) a)) y x) (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) a) x y)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.807 : Monoid.{u_1} M] {a : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.807} {x : M} {y : M}, Iff (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.807)) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.807 (Inv.inv.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.807) (Units.instInvUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.807) a)) y x) (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.807)) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.807 a) x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.units_inv_symm_left_iff SemiconjBy.units_inv_symm_left_iffₓ'. -/
@[simp, to_additive]
theorem units_inv_symm_left_iff {a : Mˣ} {x y : M} : SemiconjBy (↑a⁻¹) y x ↔ SemiconjBy (↑a) x y :=
  ⟨units_inv_symm_left, units_inv_symm_left⟩
#align semiconj_by.units_inv_symm_left_iff SemiconjBy.units_inv_symm_left_iff

/- warning: semiconj_by.units_coe -> SemiconjBy.units_val is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : Monoid.{u} M] {a : Units.{u} M _inst_1} {x : Units.{u} M _inst_1} {y : Units.{u} M _inst_1}, (SemiconjBy.{u} (Units.{u} M _inst_1) (MulOneClass.toHasMul.{u} (Units.{u} M _inst_1) (Units.mulOneClass.{u} M _inst_1)) a x y) -> (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) a) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) x) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) y))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848 : Monoid.{u_1} M] {a : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848} {x : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848} {y : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848}, (SemiconjBy.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848) (MulOneClass.toMul.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848) (Units.instMulOneClassUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848)) a x y) -> (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848)) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848 a) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848 x) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.848 y))
Case conversion may be inaccurate. Consider using '#align semiconj_by.units_coe SemiconjBy.units_valₓ'. -/
@[to_additive]
theorem units_val {a x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy (a : M) x y :=
  congr_arg Units.val h
#align semiconj_by.units_coe SemiconjBy.units_val

/- warning: semiconj_by.units_of_coe -> SemiconjBy.units_of_val is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : Monoid.{u} M] {a : Units.{u} M _inst_1} {x : Units.{u} M _inst_1} {y : Units.{u} M _inst_1}, (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) a) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) x) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) y)) -> (SemiconjBy.{u} (Units.{u} M _inst_1) (MulOneClass.toHasMul.{u} (Units.{u} M _inst_1) (Units.mulOneClass.{u} M _inst_1)) a x y)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883 : Monoid.{u_1} M] {a : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883} {x : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883} {y : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883}, (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883)) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883 a) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883 x) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883 y)) -> (SemiconjBy.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883) (MulOneClass.toMul.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883) (Units.instMulOneClassUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.883)) a x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.units_of_coe SemiconjBy.units_of_valₓ'. -/
@[to_additive]
theorem units_of_val {a x y : Mˣ} (h : SemiconjBy (a : M) x y) : SemiconjBy a x y :=
  Units.ext h
#align semiconj_by.units_of_coe SemiconjBy.units_of_val

/- warning: semiconj_by.units_coe_iff -> SemiconjBy.units_val_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : Monoid.{u} M] {a : Units.{u} M _inst_1} {x : Units.{u} M _inst_1} {y : Units.{u} M _inst_1}, Iff (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) a) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) x) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) y)) (SemiconjBy.{u} (Units.{u} M _inst_1) (MulOneClass.toHasMul.{u} (Units.{u} M _inst_1) (Units.mulOneClass.{u} M _inst_1)) a x y)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917 : Monoid.{u_1} M] {a : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917} {x : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917} {y : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917}, Iff (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917)) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917 a) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917 x) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917 y)) (SemiconjBy.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917) (MulOneClass.toMul.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917) (Units.instMulOneClassUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.917)) a x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.units_coe_iff SemiconjBy.units_val_iffₓ'. -/
@[simp, to_additive]
theorem units_val_iff {a x y : Mˣ} : SemiconjBy (a : M) x y ↔ SemiconjBy a x y :=
  ⟨units_of_val, units_val⟩
#align semiconj_by.units_coe_iff SemiconjBy.units_val_iff

/- warning: semiconj_by.pow_right -> SemiconjBy.pow_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : Monoid.{u} M] {a : M} {x : M} {y : M}, (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) a x y) -> (forall (n : Nat), SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) a (HPow.hPow.{u, 0, u} M Nat M (instHPow.{u, 0} M Nat (Monoid.hasPow.{u} M _inst_1)) x n) (HPow.hPow.{u, 0, u} M Nat M (instHPow.{u, 0} M Nat (Monoid.hasPow.{u} M _inst_1)) y n))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.956 : Monoid.{u_1} M] {a : M} {x : M} {y : M}, (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.956)) a x y) -> (forall (n : Nat), SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.956)) a (HPow.hPow.{u_1, 0, u_1} M Nat M (instHPow.{u_1, 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.956)) x n) (HPow.hPow.{u_1, 0, u_1} M Nat M (instHPow.{u_1, 0} M Nat (Monoid.Pow.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.956)) y n))
Case conversion may be inaccurate. Consider using '#align semiconj_by.pow_right SemiconjBy.pow_rightₓ'. -/
@[simp, to_additive]
theorem pow_right {a x y : M} (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (x ^ n) (y ^ n) := by
  induction' n with n ih
  · rw [pow_zero, pow_zero]
    exact SemiconjBy.one_right _
  · rw [pow_succ, pow_succ]
    exact h.mul_right ih
#align semiconj_by.pow_right SemiconjBy.pow_right

end Monoid

section DivisionMonoid

variable [DivisionMonoid G] {a x y : G}

/- warning: semiconj_by.inv_inv_symm_iff -> SemiconjBy.inv_inv_symm_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} G] {a : G} {x : G} {y : G}, Iff (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)))) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)) a) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)) x) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)) y)) (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)))) a y x)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1082 : DivisionMonoid.{u_1} G] {a : G} {x : G} {y : G}, Iff (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1082)))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1082))) a) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1082))) x) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1082))) y)) (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1082)))) a y x)
Case conversion may be inaccurate. Consider using '#align semiconj_by.inv_inv_symm_iff SemiconjBy.inv_inv_symm_iffₓ'. -/
@[simp, to_additive]
theorem inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x :=
  inv_involutive.Injective.eq_iff.symm.trans <| by
    simp_rw [mul_inv_rev, inv_inv, eq_comm, SemiconjBy]
#align semiconj_by.inv_inv_symm_iff SemiconjBy.inv_inv_symm_iff

/- warning: semiconj_by.inv_inv_symm -> SemiconjBy.inv_inv_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} G] {a : G} {x : G} {y : G}, (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)))) a x y) -> (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)))) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)) a) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)) y) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G _inst_1)) x))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1151 : DivisionMonoid.{u_1} G] {a : G} {x : G} {y : G}, (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1151)))) a x y) -> (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (DivisionMonoid.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1151)))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1151))) a) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1151))) y) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1151))) x))
Case conversion may be inaccurate. Consider using '#align semiconj_by.inv_inv_symm SemiconjBy.inv_inv_symmₓ'. -/
@[to_additive]
theorem inv_inv_symm : SemiconjBy a x y → SemiconjBy a⁻¹ y⁻¹ x⁻¹ :=
  inv_inv_symm_iff.2
#align semiconj_by.inv_inv_symm SemiconjBy.inv_inv_symm

end DivisionMonoid

section Group

variable [Group G] {a x y : G}

/- warning: semiconj_by.inv_right_iff -> SemiconjBy.inv_right_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] {a : G} {x : G} {y : G}, Iff (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))) a (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) x) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) y)) (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))) a x y)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1198 : Group.{u_1} G] {a : G} {x : G} {y : G}, Iff (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1198)))) a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1198)))) x) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1198)))) y)) (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1198)))) a x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.inv_right_iff SemiconjBy.inv_right_iffₓ'. -/
@[simp, to_additive]
theorem inv_right_iff : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  @units_inv_right_iff G _ a ⟨x, x⁻¹, mul_inv_self x, inv_mul_self x⟩
    ⟨y, y⁻¹, mul_inv_self y, inv_mul_self y⟩
#align semiconj_by.inv_right_iff SemiconjBy.inv_right_iff

/- warning: semiconj_by.inv_right -> SemiconjBy.inv_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] {a : G} {x : G} {y : G}, (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))) a x y) -> (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))) a (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) x) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) y))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1252 : Group.{u_1} G] {a : G} {x : G} {y : G}, (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1252)))) a x y) -> (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1252)))) a (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1252)))) x) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1252)))) y))
Case conversion may be inaccurate. Consider using '#align semiconj_by.inv_right SemiconjBy.inv_rightₓ'. -/
@[to_additive]
theorem inv_right : SemiconjBy a x y → SemiconjBy a x⁻¹ y⁻¹ :=
  inv_right_iff.2
#align semiconj_by.inv_right SemiconjBy.inv_right

/- warning: semiconj_by.inv_symm_left_iff -> SemiconjBy.inv_symm_left_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] {a : G} {x : G} {y : G}, Iff (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) a) y x) (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))) a x y)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1280 : Group.{u_1} G] {a : G} {x : G} {y : G}, Iff (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1280)))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1280)))) a) y x) (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1280)))) a x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by.inv_symm_left_iff SemiconjBy.inv_symm_left_iffₓ'. -/
@[simp, to_additive]
theorem inv_symm_left_iff : SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y :=
  @units_inv_symm_left_iff G _ ⟨a, a⁻¹, mul_inv_self a, inv_mul_self a⟩ _ _
#align semiconj_by.inv_symm_left_iff SemiconjBy.inv_symm_left_iff

/- warning: semiconj_by.inv_symm_left -> SemiconjBy.inv_symm_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] {a : G} {x : G} {y : G}, (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))) a x y) -> (SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) a) y x)
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1321 : Group.{u_1} G] {a : G} {x : G} {y : G}, (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1321)))) a x y) -> (SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1321)))) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1321)))) a) y x)
Case conversion may be inaccurate. Consider using '#align semiconj_by.inv_symm_left SemiconjBy.inv_symm_leftₓ'. -/
@[to_additive]
theorem inv_symm_left : SemiconjBy a x y → SemiconjBy a⁻¹ y x :=
  inv_symm_left_iff.2
#align semiconj_by.inv_symm_left SemiconjBy.inv_symm_left

/- warning: semiconj_by.conj_mk -> SemiconjBy.conj_mk is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u_1}} [_inst_1 : Group.{u_1} G] (a : G) (x : G), SemiconjBy.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)))) a x (HMul.hMul.{u_1, u_1, u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) (HMul.hMul.{u_1, u_1, u_1} G G G (instHMul.{u_1} G (MulOneClass.toHasMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1))))) a x) (Inv.inv.{u_1} G (DivInvMonoid.toHasInv.{u_1} G (Group.toDivInvMonoid.{u_1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1346 : Group.{u_1} G] (a : G) (x : G), SemiconjBy.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1346)))) a x (HMul.hMul.{u_1, u_1, u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1346))))) (HMul.hMul.{u_1, u_1, u_1} G G G (instHMul.{u_1} G (MulOneClass.toMul.{u_1} G (Monoid.toMulOneClass.{u_1} G (DivInvMonoid.toMonoid.{u_1} G (Group.toDivInvMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1346))))) a x) (Inv.inv.{u_1} G (InvOneClass.toInv.{u_1} G (DivInvOneMonoid.toInvOneClass.{u_1} G (DivisionMonoid.toDivInvOneMonoid.{u_1} G (Group.toDivisionMonoid.{u_1} G inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1346)))) a))
Case conversion may be inaccurate. Consider using '#align semiconj_by.conj_mk SemiconjBy.conj_mkₓ'. -/
/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive "`a` semiconjugates `x` to `a + x + -a`."]
theorem conj_mk (a x : G) : SemiconjBy a x (a * x * a⁻¹) := by
  unfold SemiconjBy <;> rw [mul_assoc, inv_mul_self, mul_one]
#align semiconj_by.conj_mk SemiconjBy.conj_mk

end Group

end SemiconjBy

/- warning: semiconj_by_iff_eq -> semiconjBy_iff_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : CancelCommMonoid.{u} M] {a : M} {x : M} {y : M}, Iff (SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M (RightCancelMonoid.toMonoid.{u} M (CancelMonoid.toRightCancelMonoid.{u} M (CancelCommMonoid.toCancelMonoid.{u} M _inst_1))))) a x y) (Eq.{succ u} M x y)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1410 : CancelCommMonoid.{u_1} M] {a : M} {x : M} {y : M}, Iff (SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (RightCancelMonoid.toMonoid.{u_1} M (CancelMonoid.toRightCancelMonoid.{u_1} M (CancelCommMonoid.toCancelMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1410))))) a x y) (Eq.{succ u_1} M x y)
Case conversion may be inaccurate. Consider using '#align semiconj_by_iff_eq semiconjBy_iff_eqₓ'. -/
@[simp, to_additive addSemiconjBy_iff_eq]
theorem semiconjBy_iff_eq {M : Type u} [CancelCommMonoid M] {a x y : M} :
    SemiconjBy a x y ↔ x = y :=
  ⟨fun h => mul_left_cancel (h.trans (mul_comm _ _)), fun h => by rw [h, SemiconjBy, mul_comm]⟩
#align semiconj_by_iff_eq semiconjBy_iff_eq

/- warning: units.mk_semiconj_by -> Units.mk_semiconjBy is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u}} [_inst_1 : Monoid.{u} M] (u : Units.{u} M _inst_1) (x : M), SemiconjBy.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) u) x (HMul.hMul.{u, u, u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1))) (HMul.hMul.{u, u, u} M M M (instHMul.{u} M (MulOneClass.toHasMul.{u} M (Monoid.toMulOneClass.{u} M _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) u) x) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} M _inst_1) M (HasLiftT.mk.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.coe.{succ u, succ u} (Units.{u} M _inst_1) M (CoeTCₓ.mk.{succ u, succ u} (Units.{u} M _inst_1) M (Units.val.{u} M _inst_1)))) (Inv.inv.{u} (Units.{u} M _inst_1) (Units.hasInv.{u} M _inst_1) u)))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1485 : Monoid.{u_1} M] (u : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1485) (x : M), SemiconjBy.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1485)) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1485 u) x (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1485))) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1485))) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1485 u) x) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1485 (Inv.inv.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1485) (Units.instInvUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Semiconj._hyg.1485) u)))
Case conversion may be inaccurate. Consider using '#align units.mk_semiconj_by Units.mk_semiconjByₓ'. -/
/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive "`a` semiconjugates `x` to `a + x + -a`."]
theorem Units.mk_semiconjBy {M : Type u} [Monoid M] (u : Mˣ) (x : M) :
    SemiconjBy (↑u) x (u * x * ↑u⁻¹) := by unfold SemiconjBy <;> rw [Units.inv_mul_cancel_right]
#align units.mk_semiconj_by Units.mk_semiconjBy

