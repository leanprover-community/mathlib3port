/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies

! This file was ported from Lean 3 source module analysis.normed.ring.seminorm
! leanprover-community/mathlib commit ce38d86c0b2d427ce208c3cee3159cb421d2b3c4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Field.Basic

/-!
# Seminorms and norms on rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines seminorms and norms on rings. These definitions are useful when one needs to
consider multiple (semi)norms on a given ring.

## Main declarations

For a ring `R`:
* `ring_seminorm`: A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes
  nonnegative values, is subadditive and submultiplicative and such that `f (-x) = f x` for all
  `x ∈ R`.
* `ring_norm`: A seminorm `f` is a norm if `f x = 0` if and only if `x = 0`.
* `mul_ring_seminorm`: A multiplicative seminorm on a ring `R` is a ring seminorm that preserves
  multiplication.
* `mul_ring_norm`: A multiplicative norm on a ring `R` is a ring norm that preserves multiplication.

## Notes

The corresponding hom classes are defined in `analysis.order.hom.basic` to be used by absolute
values.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/


open NNReal

variable {F R S : Type _} (x y : R) (r : ℝ)

#print RingSeminorm /-
/-- A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes nonnegative
  values, is subadditive and submultiplicative and such that `f (-x) = f x` for all `x ∈ R`. -/
structure RingSeminorm (R : Type _) [NonUnitalNonAssocRing R] extends AddGroupSeminorm R where
  mul_le' : ∀ x y : R, to_fun (x * y) ≤ to_fun x * to_fun y
#align ring_seminorm RingSeminorm
-/

#print RingNorm /-
/-- A function `f : R → ℝ` is a norm on a (nonunital) ring if it is a seminorm and `f x = 0`
  implies `x = 0`. -/
structure RingNorm (R : Type _) [NonUnitalNonAssocRing R] extends RingSeminorm R, AddGroupNorm R
#align ring_norm RingNorm
-/

#print MulRingSeminorm /-
/-- A multiplicative seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero and
multiplication, takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
-/
structure MulRingSeminorm (R : Type _) [NonAssocRing R] extends AddGroupSeminorm R,
  MonoidWithZeroHom R ℝ
#align mul_ring_seminorm MulRingSeminorm
-/

#print MulRingNorm /-
/-- A multiplicative norm on a ring `R` is a multiplicative ring seminorm such that `f x = 0`
implies `x = 0`. -/
structure MulRingNorm (R : Type _) [NonAssocRing R] extends MulRingSeminorm R, AddGroupNorm R
#align mul_ring_norm MulRingNorm
-/

attribute [nolint doc_blame]
  RingSeminorm.toAddGroupSeminorm RingNorm.toAddGroupNorm RingNorm.toRingSeminorm MulRingSeminorm.toAddGroupSeminorm MulRingSeminorm.toMonoidWithZeroHom MulRingNorm.toAddGroupNorm MulRingNorm.toMulRingSeminorm

namespace RingSeminorm

section NonUnitalRing

variable [NonUnitalRing R]

#print RingSeminorm.ringSeminormClass /-
instance ringSeminormClass : RingSeminormClass (RingSeminorm R) R ℝ
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
#align ring_seminorm.ring_seminorm_class RingSeminorm.ringSeminormClass
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (RingSeminorm R) fun _ => R → ℝ :=
  FunLike.hasCoeToFun

/- warning: ring_seminorm.to_fun_eq_coe -> RingSeminorm.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] (p : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)), Eq.{succ u1} (R -> Real) (RingSeminorm.toFun.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) p) (coeFn.{succ u1, succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (fun (_x : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) => R -> Real) (RingSeminorm.hasCoeToFun.{u1} R _inst_1) p)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] (p : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)), Eq.{succ u1} (R -> Real) (FunLike.coe.{succ u1, succ u1, 1} (AddGroupSeminorm.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) R (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.956 : R) => Real) (SubadditiveHomClass.toFunLike.{u1, u1, 0} (AddGroupSeminorm.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) R Real (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (AddGroupSeminormClass.toSubadditiveHomClass.{u1, u1, 0} (AddGroupSeminorm.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) R Real (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) Real.orderedAddCommMonoid (AddGroupSeminorm.addGroupSeminormClass.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))) (RingSeminorm.toAddGroupSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) p)) (FunLike.coe.{succ u1, succ u1, 1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) Real.orderedSemiring (RingSeminorm.ringSeminormClass.{u1} R _inst_1))) p)
Case conversion may be inaccurate. Consider using '#align ring_seminorm.to_fun_eq_coe RingSeminorm.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe (p : RingSeminorm R) : p.toFun = p :=
  rfl
#align ring_seminorm.to_fun_eq_coe RingSeminorm.toFun_eq_coe

/- warning: ring_seminorm.ext -> RingSeminorm.ext is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] {p : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)} {q : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)}, (forall (x : R), Eq.{1} Real (coeFn.{succ u1, succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (fun (_x : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) => R -> Real) (RingSeminorm.hasCoeToFun.{u1} R _inst_1) p x) (coeFn.{succ u1, succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (fun (_x : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) => R -> Real) (RingSeminorm.hasCoeToFun.{u1} R _inst_1) q x)) -> (Eq.{succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) p q)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] {p : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)} {q : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)}, (forall (x : R), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) Real.orderedSemiring (RingSeminorm.ringSeminormClass.{u1} R _inst_1))) p x) (FunLike.coe.{succ u1, succ u1, 1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) Real.orderedSemiring (RingSeminorm.ringSeminormClass.{u1} R _inst_1))) q x)) -> (Eq.{succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) p q)
Case conversion may be inaccurate. Consider using '#align ring_seminorm.ext RingSeminorm.extₓ'. -/
@[ext]
theorem ext {p q : RingSeminorm R} : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align ring_seminorm.ext RingSeminorm.ext

instance : Zero (RingSeminorm R) :=
  ⟨{ AddGroupSeminorm.hasZero.zero with mul_le' := fun _ _ => (MulZeroClass.zero_mul _).ge }⟩

/- warning: ring_seminorm.eq_zero_iff -> RingSeminorm.eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] {p : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)}, Iff (Eq.{succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) p (OfNat.ofNat.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 0 (OfNat.mk.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 0 (Zero.zero.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (RingSeminorm.hasZero.{u1} R _inst_1))))) (forall (x : R), Eq.{1} Real (coeFn.{succ u1, succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (fun (_x : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) => R -> Real) (RingSeminorm.hasCoeToFun.{u1} R _inst_1) p x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] {p : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)}, Iff (Eq.{succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) p (OfNat.ofNat.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 0 (Zero.toOfNat0.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (RingSeminorm.instZeroRingSeminormToNonUnitalNonAssocRing.{u1} R _inst_1)))) (forall (x : R), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) Real.orderedSemiring (RingSeminorm.ringSeminormClass.{u1} R _inst_1))) p x) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) 0 (Zero.toOfNat0.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align ring_seminorm.eq_zero_iff RingSeminorm.eq_zero_iffₓ'. -/
theorem eq_zero_iff {p : RingSeminorm R} : p = 0 ↔ ∀ x, p x = 0 :=
  FunLike.ext_iff
#align ring_seminorm.eq_zero_iff RingSeminorm.eq_zero_iff

/- warning: ring_seminorm.ne_zero_iff -> RingSeminorm.ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] {p : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)}, Iff (Ne.{succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) p (OfNat.ofNat.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 0 (OfNat.mk.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 0 (Zero.zero.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (RingSeminorm.hasZero.{u1} R _inst_1))))) (Exists.{succ u1} R (fun (x : R) => Ne.{1} Real (coeFn.{succ u1, succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (fun (_x : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) => R -> Real) (RingSeminorm.hasCoeToFun.{u1} R _inst_1) p x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] {p : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)}, Iff (Ne.{succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) p (OfNat.ofNat.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 0 (Zero.toOfNat0.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (RingSeminorm.instZeroRingSeminormToNonUnitalNonAssocRing.{u1} R _inst_1)))) (Exists.{succ u1} R (fun (x : R) => Ne.{1} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) Real.orderedSemiring (RingSeminorm.ringSeminormClass.{u1} R _inst_1))) p x) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) 0 (Zero.toOfNat0.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align ring_seminorm.ne_zero_iff RingSeminorm.ne_zero_iffₓ'. -/
theorem ne_zero_iff {p : RingSeminorm R} : p ≠ 0 ↔ ∃ x, p x ≠ 0 := by simp [eq_zero_iff]
#align ring_seminorm.ne_zero_iff RingSeminorm.ne_zero_iff

instance : Inhabited (RingSeminorm R) :=
  ⟨0⟩

/-- The trivial seminorm on a ring `R` is the `ring_seminorm` taking value `0` at `0` and `1` at
every other element. -/
instance [DecidableEq R] : One (RingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      mul_le' := fun x y => by
        by_cases h : x * y = 0
        ·
          refine' (if_pos h).trans_le (mul_nonneg _ _) <;>
            · change _ ≤ ite _ _ _
              split_ifs
              exacts[le_rfl, zero_le_one]
        · change ite _ _ _ ≤ ite _ _ _ * ite _ _ _
          simp only [if_false, h, left_ne_zero_of_mul h, right_ne_zero_of_mul h, mul_one] }⟩

/- warning: ring_seminorm.apply_one -> RingSeminorm.apply_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R), Eq.{1} Real (coeFn.{succ u1, succ u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (fun (_x : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) => R -> Real) (RingSeminorm.hasCoeToFun.{u1} R _inst_1) (OfNat.ofNat.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 1 (OfNat.mk.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 1 (One.one.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (RingSeminorm.hasOne.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b))))) x) (ite.{1} Real (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))))) (_inst_2 x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) R Real (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) Real.orderedSemiring (RingSeminorm.ringSeminormClass.{u1} R _inst_1))) (OfNat.ofNat.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 1 (One.toOfNat1.{u1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (RingSeminorm.instOneRingSeminormToNonUnitalNonAssocRing.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b)))) x) (ite.{1} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (SemigroupWithZero.toZero.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1)))))) (_inst_2 x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (SemigroupWithZero.toZero.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1)))))) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) 0 (Zero.toOfNat0.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) Real.instZeroReal)) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) 1 (One.toOfNat1.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) x) Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align ring_seminorm.apply_one RingSeminorm.apply_oneₓ'. -/
@[simp]
theorem apply_one [DecidableEq R] (x : R) : (1 : RingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl
#align ring_seminorm.apply_one RingSeminorm.apply_one

end NonUnitalRing

section Ring

variable [Ring R] (p : RingSeminorm R)

/- warning: ring_seminorm.seminorm_one_eq_one_iff_ne_zero -> RingSeminorm.seminorm_one_eq_one_iff_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (p : RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))), (LE.le.{0} Real Real.hasLe (coeFn.{succ u1, succ u1} (RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (fun (_x : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))) => R -> Real) (RingSeminorm.hasCoeToFun.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) p (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Iff (Eq.{1} Real (coeFn.{succ u1, succ u1} (RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (fun (_x : RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))) => R -> Real) (RingSeminorm.hasCoeToFun.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) p (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R _inst_1)))))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Ne.{succ u1} (RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) p (OfNat.ofNat.{u1} (RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) 0 (OfNat.mk.{u1} (RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) 0 (Zero.zero.{u1} (RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (RingSeminorm.hasZero.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] (p : RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))), (LE.le.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) Real.instLEReal (FunLike.coe.{succ u1, succ u1, 1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))) R Real (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) Real.orderedSemiring (RingSeminorm.ringSeminormClass.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)))) p (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) 1 (One.toOfNat1.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) Real.instOneReal))) -> (Iff (Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (FunLike.coe.{succ u1, succ u1, 1} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (RingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))) R Real (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)) Real.orderedSemiring (RingSeminorm.ringSeminormClass.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1)))) p (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) 1 (One.toOfNat1.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.319 : R) => Real) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R _inst_1))))) Real.instOneReal))) (Ne.{succ u1} (RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) p (OfNat.ofNat.{u1} (RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) 0 (Zero.toOfNat0.{u1} (RingSeminorm.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) (RingSeminorm.instZeroRingSeminormToNonUnitalNonAssocRing.{u1} R (Ring.toNonUnitalRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align ring_seminorm.seminorm_one_eq_one_iff_ne_zero RingSeminorm.seminorm_one_eq_one_iff_ne_zeroₓ'. -/
theorem seminorm_one_eq_one_iff_ne_zero (hp : p 1 ≤ 1) : p 1 = 1 ↔ p ≠ 0 :=
  by
  refine' ⟨fun h => ne_zero_iff.mpr ⟨1, by rw [h]; exact one_ne_zero⟩, fun h => _⟩
  obtain hp0 | hp0 := (map_nonneg p (1 : R)).eq_or_gt
  · cases h (ext fun x => (map_nonneg _ _).antisymm' _)
    simpa only [hp0, mul_one, MulZeroClass.mul_zero] using map_mul_le_mul p x 1
  · refine' hp.antisymm ((le_mul_iff_one_le_left hp0).1 _)
    simpa only [one_mul] using map_mul_le_mul p (1 : R) _
#align ring_seminorm.seminorm_one_eq_one_iff_ne_zero RingSeminorm.seminorm_one_eq_one_iff_ne_zero

end Ring

end RingSeminorm

#print normRingSeminorm /-
/-- The norm of a `non_unital_semi_normed_ring` as a `ring_seminorm`. -/
def normRingSeminorm (R : Type _) [NonUnitalSeminormedRing R] : RingSeminorm R :=
  { normAddGroupSeminorm R with
    toFun := norm
    mul_le' := norm_mul_le }
#align norm_ring_seminorm normRingSeminorm
-/

namespace RingNorm

variable [NonUnitalRing R]

#print RingNorm.ringNormClass /-
instance ringNormClass : RingNormClass (RingNorm R) R ℝ
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero'
#align ring_norm.ring_norm_class RingNorm.ringNormClass
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (RingNorm R) fun _ => R → ℝ :=
  ⟨fun p => p.toFun⟩

/- warning: ring_norm.to_fun_eq_coe clashes with [anonymous] -> [anonymous]
warning: ring_norm.to_fun_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u_2}} [_inst_1 : NonUnitalRing.{u_2} R] (p : RingNorm.{u_2} R (NonUnitalRing.toNonUnitalNonAssocRing.{u_2} R _inst_1)), Eq.{max (succ u_2) 1} (R -> Real) (RingNorm.toFun.{u_2} R (NonUnitalRing.toNonUnitalNonAssocRing.{u_2} R _inst_1) p) (coeFn.{succ u_2, max (succ u_2) 1} (RingNorm.{u_2} R (NonUnitalRing.toNonUnitalNonAssocRing.{u_2} R _inst_1)) (fun (_x : RingNorm.{u_2} R (NonUnitalRing.toNonUnitalNonAssocRing.{u_2} R _inst_1)) => R -> Real) (RingNorm.hasCoeToFun.{u_2} R _inst_1) p)
but is expected to have type
  forall {R : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> R -> _inst_1) -> Nat -> (List.{u} R) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align ring_norm.to_fun_eq_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (p : RingNorm R) : p.toFun = p :=
  rfl
#align ring_norm.to_fun_eq_coe [anonymous]

/- warning: ring_norm.ext -> RingNorm.ext is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] {p : RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)} {q : RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)}, (forall (x : R), Eq.{1} Real (coeFn.{succ u1, succ u1} (RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (fun (_x : RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) => R -> Real) (RingNorm.hasCoeToFun.{u1} R _inst_1) p x) (coeFn.{succ u1, succ u1} (RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (fun (_x : RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) => R -> Real) (RingNorm.hasCoeToFun.{u1} R _inst_1) q x)) -> (Eq.{succ u1} (RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) p q)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} R] {p : RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)} {q : RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)}, (forall (x : R), Eq.{1} Real (AddGroupSeminorm.toFun.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (RingSeminorm.toAddGroupSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) (RingNorm.toRingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) p)) x) (AddGroupSeminorm.toFun.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (RingSeminorm.toAddGroupSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) (RingNorm.toRingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) q)) x)) -> (Eq.{succ u1} (RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) p q)
Case conversion may be inaccurate. Consider using '#align ring_norm.ext RingNorm.extₓ'. -/
@[ext]
theorem ext {p q : RingNorm R} : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align ring_norm.ext RingNorm.ext

variable (R)

/-- The trivial norm on a ring `R` is the `ring_norm` taking value `0` at `0` and `1` at every
  other element. -/
instance [DecidableEq R] : One (RingNorm R) :=
  ⟨{ (1 : RingSeminorm R), (1 : AddGroupNorm R) with }⟩

/- warning: ring_norm.apply_one -> RingNorm.apply_one is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : NonUnitalRing.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R), Eq.{1} Real (coeFn.{succ u1, succ u1} (RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (fun (_x : RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) => R -> Real) (RingNorm.hasCoeToFun.{u1} R _inst_1) (OfNat.ofNat.{u1} (RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 1 (OfNat.mk.{u1} (RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 1 (One.one.{u1} (RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (RingNorm.hasOne.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b))))) x) (ite.{1} Real (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))))) (_inst_2 x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : NonUnitalRing.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] (x : R), Eq.{1} Real (AddGroupSeminorm.toFun.{u1} R (AddCommGroup.toAddGroup.{u1} R (NonUnitalNonAssocRing.toAddCommGroup.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1))) (RingSeminorm.toAddGroupSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) (RingNorm.toRingSeminorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1) (OfNat.ofNat.{u1} (RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) 1 (One.toOfNat1.{u1} (RingNorm.{u1} R (NonUnitalRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (RingNorm.instOneRingNormToNonUnitalNonAssocRing.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b)))))) x) (ite.{1} Real (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (SemigroupWithZero.toZero.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1)))))) (_inst_2 x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (SemigroupWithZero.toZero.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (NonUnitalRing.toNonUnitalSemiring.{u1} R _inst_1)))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align ring_norm.apply_one RingNorm.apply_oneₓ'. -/
@[simp]
theorem apply_one [DecidableEq R] (x : R) : (1 : RingNorm R) x = if x = 0 then 0 else 1 :=
  rfl
#align ring_norm.apply_one RingNorm.apply_one

instance [DecidableEq R] : Inhabited (RingNorm R) :=
  ⟨1⟩

end RingNorm

namespace MulRingSeminorm

variable [NonAssocRing R]

#print MulRingSeminorm.mulRingSeminormClass /-
instance mulRingSeminormClass : MulRingSeminormClass (MulRingSeminorm R) R ℝ
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_zero f := f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
#align mul_ring_seminorm.mul_ring_seminorm_class MulRingSeminorm.mulRingSeminormClass
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (MulRingSeminorm R) fun _ => R → ℝ :=
  FunLike.hasCoeToFun

/- warning: mul_ring_seminorm.to_fun_eq_coe -> MulRingSeminorm.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] (p : MulRingSeminorm.{u1} R _inst_1), Eq.{succ u1} (R -> Real) (MulRingSeminorm.toFun.{u1} R _inst_1 p) (coeFn.{succ u1, succ u1} (MulRingSeminorm.{u1} R _inst_1) (fun (_x : MulRingSeminorm.{u1} R _inst_1) => R -> Real) (MulRingSeminorm.hasCoeToFun.{u1} R _inst_1) p)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] (p : MulRingSeminorm.{u1} R _inst_1), Eq.{succ u1} (R -> Real) (FunLike.coe.{succ u1, succ u1, 1} (AddGroupSeminorm.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (NonAssocRing.toAddCommGroupWithOne.{u1} R _inst_1)))) R (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.956 : R) => Real) (SubadditiveHomClass.toFunLike.{u1, u1, 0} (AddGroupSeminorm.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (NonAssocRing.toAddCommGroupWithOne.{u1} R _inst_1)))) R Real (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (SubNegMonoid.toAddMonoid.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (NonAssocRing.toAddCommGroupWithOne.{u1} R _inst_1))))))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (AddGroupSeminormClass.toSubadditiveHomClass.{u1, u1, 0} (AddGroupSeminorm.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (NonAssocRing.toAddCommGroupWithOne.{u1} R _inst_1)))) R Real (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (NonAssocRing.toAddCommGroupWithOne.{u1} R _inst_1))) Real.orderedAddCommMonoid (AddGroupSeminorm.addGroupSeminormClass.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (NonAssocRing.toAddCommGroupWithOne.{u1} R _inst_1)))))) (MulRingSeminorm.toAddGroupSeminorm.{u1} R _inst_1 p)) (FunLike.coe.{succ u1, succ u1, 1} (MulRingSeminorm.{u1} R _inst_1) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1) Real.orderedSemiring (MulRingSeminormClass.toRingSeminormClass.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real _inst_1 Real.orderedSemiring (MulRingSeminorm.mulRingSeminormClass.{u1} R _inst_1)))) p)
Case conversion may be inaccurate. Consider using '#align mul_ring_seminorm.to_fun_eq_coe MulRingSeminorm.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe (p : MulRingSeminorm R) : p.toFun = p :=
  rfl
#align mul_ring_seminorm.to_fun_eq_coe MulRingSeminorm.toFun_eq_coe

/- warning: mul_ring_seminorm.ext -> MulRingSeminorm.ext is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] {p : MulRingSeminorm.{u1} R _inst_1} {q : MulRingSeminorm.{u1} R _inst_1}, (forall (x : R), Eq.{1} Real (coeFn.{succ u1, succ u1} (MulRingSeminorm.{u1} R _inst_1) (fun (_x : MulRingSeminorm.{u1} R _inst_1) => R -> Real) (MulRingSeminorm.hasCoeToFun.{u1} R _inst_1) p x) (coeFn.{succ u1, succ u1} (MulRingSeminorm.{u1} R _inst_1) (fun (_x : MulRingSeminorm.{u1} R _inst_1) => R -> Real) (MulRingSeminorm.hasCoeToFun.{u1} R _inst_1) q x)) -> (Eq.{succ u1} (MulRingSeminorm.{u1} R _inst_1) p q)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] {p : MulRingSeminorm.{u1} R _inst_1} {q : MulRingSeminorm.{u1} R _inst_1}, (forall (x : R), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (MulRingSeminorm.{u1} R _inst_1) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1) Real.orderedSemiring (MulRingSeminormClass.toRingSeminormClass.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real _inst_1 Real.orderedSemiring (MulRingSeminorm.mulRingSeminormClass.{u1} R _inst_1)))) p x) (FunLike.coe.{succ u1, succ u1, 1} (MulRingSeminorm.{u1} R _inst_1) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1) Real.orderedSemiring (MulRingSeminormClass.toRingSeminormClass.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real _inst_1 Real.orderedSemiring (MulRingSeminorm.mulRingSeminormClass.{u1} R _inst_1)))) q x)) -> (Eq.{succ u1} (MulRingSeminorm.{u1} R _inst_1) p q)
Case conversion may be inaccurate. Consider using '#align mul_ring_seminorm.ext MulRingSeminorm.extₓ'. -/
@[ext]
theorem ext {p q : MulRingSeminorm R} : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align mul_ring_seminorm.ext MulRingSeminorm.ext

variable [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

/-- The trivial seminorm on a ring `R` is the `mul_ring_seminorm` taking value `0` at `0` and `1` at
every other element. -/
instance : One (MulRingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      map_one' := if_neg one_ne_zero
      map_mul' := fun x y => by
        obtain rfl | hx := eq_or_ne x 0
        · simp
        obtain rfl | hy := eq_or_ne y 0
        · simp
        · simp [hx, hy] }⟩

/- warning: mul_ring_seminorm.apply_one -> MulRingSeminorm.apply_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] [_inst_3 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_4 : Nontrivial.{u1} R] (x : R), Eq.{1} Real (coeFn.{succ u1, succ u1} (MulRingSeminorm.{u1} R _inst_1) (fun (_x : MulRingSeminorm.{u1} R _inst_1) => R -> Real) (MulRingSeminorm.hasCoeToFun.{u1} R _inst_1) (OfNat.ofNat.{u1} (MulRingSeminorm.{u1} R _inst_1) 1 (OfNat.mk.{u1} (MulRingSeminorm.{u1} R _inst_1) 1 (One.one.{u1} (MulRingSeminorm.{u1} R _inst_1) (MulRingSeminorm.hasOne.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) _inst_3 _inst_4)))) x) (ite.{1} Real (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))))) (_inst_2 x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] [_inst_3 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_4 : Nontrivial.{u1} R] (x : R), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (MulRingSeminorm.{u1} R _inst_1) R (fun (_x : R) => (fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (RingSeminormClass.toSubmultiplicativeHomClass.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1) Real.orderedSemiring (MulRingSeminormClass.toRingSeminormClass.{u1, u1, 0} (MulRingSeminorm.{u1} R _inst_1) R Real _inst_1 Real.orderedSemiring (MulRingSeminorm.mulRingSeminormClass.{u1} R _inst_1)))) (OfNat.ofNat.{u1} (MulRingSeminorm.{u1} R _inst_1) 1 (One.toOfNat1.{u1} (MulRingSeminorm.{u1} R _inst_1) (MulRingSeminorm.instOneMulRingSeminorm.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) _inst_3 _inst_4))) x) (ite.{1} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) x) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))))) (_inst_2 x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))))) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) x) 0 (Zero.toOfNat0.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) x) Real.instZeroReal)) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) x) 1 (One.toOfNat1.{0} ((fun (a._@.Mathlib.Analysis.Normed.Ring.Seminorm._hyg.1434 : R) => Real) x) Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align mul_ring_seminorm.apply_one MulRingSeminorm.apply_oneₓ'. -/
@[simp]
theorem apply_one (x : R) : (1 : MulRingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl
#align mul_ring_seminorm.apply_one MulRingSeminorm.apply_one

instance : Inhabited (MulRingSeminorm R) :=
  ⟨1⟩

end MulRingSeminorm

namespace MulRingNorm

variable [NonAssocRing R]

#print MulRingNorm.mulRingNormClass /-
instance mulRingNormClass : MulRingNormClass (MulRingNorm R) R ℝ
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_zero f := f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero'
#align mul_ring_norm.mul_ring_norm_class MulRingNorm.mulRingNormClass
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (MulRingNorm R) fun _ => R → ℝ :=
  ⟨fun p => p.toFun⟩

/- warning: mul_ring_norm.to_fun_eq_coe clashes with [anonymous] -> [anonymous]
warning: mul_ring_norm.to_fun_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u_2}} [_inst_1 : NonAssocRing.{u_2} R] (p : MulRingNorm.{u_2} R _inst_1), Eq.{max (succ u_2) 1} (R -> Real) (MulRingNorm.toFun.{u_2} R _inst_1 p) (coeFn.{succ u_2, max (succ u_2) 1} (MulRingNorm.{u_2} R _inst_1) (fun (_x : MulRingNorm.{u_2} R _inst_1) => R -> Real) (MulRingNorm.hasCoeToFun.{u_2} R _inst_1) p)
but is expected to have type
  forall {R : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> R -> _inst_1) -> Nat -> (List.{u} R) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align mul_ring_norm.to_fun_eq_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (p : MulRingNorm R) : p.toFun = p :=
  rfl
#align mul_ring_norm.to_fun_eq_coe [anonymous]

/- warning: mul_ring_norm.ext -> MulRingNorm.ext is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] {p : MulRingNorm.{u1} R _inst_1} {q : MulRingNorm.{u1} R _inst_1}, (forall (x : R), Eq.{1} Real (coeFn.{succ u1, succ u1} (MulRingNorm.{u1} R _inst_1) (fun (_x : MulRingNorm.{u1} R _inst_1) => R -> Real) (MulRingNorm.hasCoeToFun.{u1} R _inst_1) p x) (coeFn.{succ u1, succ u1} (MulRingNorm.{u1} R _inst_1) (fun (_x : MulRingNorm.{u1} R _inst_1) => R -> Real) (MulRingNorm.hasCoeToFun.{u1} R _inst_1) q x)) -> (Eq.{succ u1} (MulRingNorm.{u1} R _inst_1) p q)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonAssocRing.{u1} R] {p : MulRingNorm.{u1} R _inst_1} {q : MulRingNorm.{u1} R _inst_1}, (forall (x : R), Eq.{1} Real (AddGroupSeminorm.toFun.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (NonAssocRing.toAddCommGroupWithOne.{u1} R _inst_1))) (MulRingSeminorm.toAddGroupSeminorm.{u1} R _inst_1 (MulRingNorm.toMulRingSeminorm.{u1} R _inst_1 p)) x) (AddGroupSeminorm.toFun.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (NonAssocRing.toAddCommGroupWithOne.{u1} R _inst_1))) (MulRingSeminorm.toAddGroupSeminorm.{u1} R _inst_1 (MulRingNorm.toMulRingSeminorm.{u1} R _inst_1 q)) x)) -> (Eq.{succ u1} (MulRingNorm.{u1} R _inst_1) p q)
Case conversion may be inaccurate. Consider using '#align mul_ring_norm.ext MulRingNorm.extₓ'. -/
@[ext]
theorem ext {p q : MulRingNorm R} : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align mul_ring_norm.ext MulRingNorm.ext

variable (R) [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

/-- The trivial norm on a ring `R` is the `mul_ring_norm` taking value `0` at `0` and `1` at every
other element. -/
instance : One (MulRingNorm R) :=
  ⟨{ (1 : MulRingSeminorm R), (1 : AddGroupNorm R) with }⟩

/- warning: mul_ring_norm.apply_one -> MulRingNorm.apply_one is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] [_inst_3 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1))))] [_inst_4 : Nontrivial.{u1} R] (x : R), Eq.{1} Real (coeFn.{succ u1, succ u1} (MulRingNorm.{u1} R _inst_1) (fun (_x : MulRingNorm.{u1} R _inst_1) => R -> Real) (MulRingNorm.hasCoeToFun.{u1} R _inst_1) (OfNat.ofNat.{u1} (MulRingNorm.{u1} R _inst_1) 1 (OfNat.mk.{u1} (MulRingNorm.{u1} R _inst_1) 1 (One.one.{u1} (MulRingNorm.{u1} R _inst_1) (MulRingNorm.hasOne.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) _inst_3 _inst_4)))) x) (ite.{1} Real (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))))) (_inst_2 x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : NonAssocRing.{u1} R] [_inst_2 : DecidableEq.{succ u1} R] [_inst_3 : NoZeroDivisors.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R _inst_1)) (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))] [_inst_4 : Nontrivial.{u1} R] (x : R), Eq.{1} Real (AddGroupSeminorm.toFun.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (NonAssocRing.toAddCommGroupWithOne.{u1} R _inst_1))) (MulRingSeminorm.toAddGroupSeminorm.{u1} R _inst_1 (MulRingNorm.toMulRingSeminorm.{u1} R _inst_1 (OfNat.ofNat.{u1} (MulRingNorm.{u1} R _inst_1) 1 (One.toOfNat1.{u1} (MulRingNorm.{u1} R _inst_1) (MulRingNorm.instOneMulRingNorm.{u1} R _inst_1 (fun (a : R) (b : R) => _inst_2 a b) _inst_3 _inst_4))))) x) (ite.{1} Real (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))))) (_inst_2 x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R _inst_1)))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align mul_ring_norm.apply_one MulRingNorm.apply_oneₓ'. -/
@[simp]
theorem apply_one (x : R) : (1 : MulRingNorm R) x = if x = 0 then 0 else 1 :=
  rfl
#align mul_ring_norm.apply_one MulRingNorm.apply_one

instance : Inhabited (MulRingNorm R) :=
  ⟨1⟩

end MulRingNorm

/- warning: ring_seminorm.to_ring_norm -> RingSeminorm.toRingNorm is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] (f : RingSeminorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))), (Ne.{succ u1} (RingSeminorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) f (OfNat.ofNat.{u1} (RingSeminorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) 0 (OfNat.mk.{u1} (RingSeminorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) 0 (Zero.zero.{u1} (RingSeminorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) (RingSeminorm.hasZero.{u1} K (NonUnitalCommRing.toNonUnitalRing.{u1} K (CommRing.toNonUnitalCommRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_1))))))))) -> (RingNorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : Field.{u1} K] (f : RingSeminorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))), (Ne.{succ u1} (RingSeminorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) f (OfNat.ofNat.{u1} (RingSeminorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) 0 (Zero.toOfNat0.{u1} (RingSeminorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1))))) (RingSeminorm.instZeroRingSeminormToNonUnitalNonAssocRing.{u1} K (NonUnitalCommRing.toNonUnitalRing.{u1} K (CommRing.toNonUnitalCommRing.{u1} K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_1)))))))) -> (RingNorm.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ring_seminorm.to_ring_norm RingSeminorm.toRingNormₓ'. -/
/-- A nonzero ring seminorm on a field `K` is a ring norm. -/
def RingSeminorm.toRingNorm {K : Type _} [Field K] (f : RingSeminorm K) (hnt : f ≠ 0) :
    RingNorm K :=
  { f with
    eq_zero_of_map_eq_zero' := fun x hx =>
      by
      obtain ⟨c, hc⟩ := ring_seminorm.ne_zero_iff.mp hnt
      by_contra hn0
      have hc0 : f c = 0 :=
        by
        rw [← mul_one c, ← mul_inv_cancel hn0, ← mul_assoc, mul_comm c, mul_assoc]
        exact
          le_antisymm
            (le_trans (map_mul_le_mul f _ _)
              (by rw [← RingSeminorm.toFun_eq_coe, hx, MulZeroClass.zero_mul]))
            (map_nonneg f _)
      exact hc hc0 }
#align ring_seminorm.to_ring_norm RingSeminorm.toRingNorm

#print normRingNorm /-
/-- The norm of a normed_ring as a ring_norm. -/
@[simps]
def normRingNorm (R : Type _) [NonUnitalNormedRing R] : RingNorm R :=
  { normAddGroupNorm R, normRingSeminorm R with }
#align norm_ring_norm normRingNorm
-/

