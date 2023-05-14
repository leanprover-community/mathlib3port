/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro

! This file was ported from Lean 3 source module ring_theory.ideal.basic
! leanprover-community/mathlib commit 23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Associated
import Mathbin.LinearAlgebra.Basic
import Mathbin.Order.Atoms
import Mathbin.Order.CompactlyGenerated
import Mathbin.Tactic.Abel
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.LinearAlgebra.Finsupp

/-!

# Ideals over a ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `ideal R`, the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`ideal R` is implemented using `submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/


universe u v w

variable {α : Type u} {β : Type v}

open Set Function

open Classical BigOperators Pointwise

#print Ideal /-
/-- A (left) ideal in a semiring `R` is an additive submonoid `s` such that
`a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup.  -/
@[reducible]
def Ideal (R : Type u) [Semiring R] :=
  Submodule R R
#align ideal Ideal
-/

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/- warning: ideal.zero_mem -> Ideal.zero_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1), Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) I
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1), Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))) I
Case conversion may be inaccurate. Consider using '#align ideal.zero_mem Ideal.zero_memₓ'. -/
protected theorem zero_mem : (0 : α) ∈ I :=
  I.zero_mem
#align ideal.zero_mem Ideal.zero_mem

/- warning: ideal.add_mem -> Ideal.add_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) a I) -> (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) b I) -> (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a b) I)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) {a : α} {b : α}, (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) a I) -> (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) b I) -> (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a b) I)
Case conversion may be inaccurate. Consider using '#align ideal.add_mem Ideal.add_memₓ'. -/
protected theorem add_mem : a ∈ I → b ∈ I → a + b ∈ I :=
  I.add_mem
#align ideal.add_mem Ideal.add_mem

variable (a)

/- warning: ideal.mul_mem_left -> Ideal.mul_mem_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) (a : α) {b : α}, (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) b I) -> (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a b) I)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) (a : α) {b : α}, (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) b I) -> (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a b) I)
Case conversion may be inaccurate. Consider using '#align ideal.mul_mem_left Ideal.mul_mem_leftₓ'. -/
theorem mul_mem_left : b ∈ I → a * b ∈ I :=
  I.smul_mem a
#align ideal.mul_mem_left Ideal.mul_mem_left

variable {a}

#print Ideal.ext /-
@[ext]
theorem ext {I J : Ideal α} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  Submodule.ext h
#align ideal.ext Ideal.ext
-/

/- warning: ideal.sum_mem -> Ideal.sum_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) {ι : Type.{u2}} {t : Finset.{u2} ι} {f : ι -> α}, (forall (c : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) c t) -> (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (f c) I)) -> (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (Finset.sum.{u1, u2} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) t (fun (i : ι) => f i)) I)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Semiring.{u2} α] (I : Ideal.{u2} α _inst_1) {ι : Type.{u1}} {t : Finset.{u1} ι} {f : ι -> α}, (forall (c : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) c t) -> (Membership.mem.{u2, u2} α (Ideal.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (Ideal.{u2} α _inst_1) α (Submodule.setLike.{u2, u2} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (Semiring.toModule.{u2} α _inst_1))) (f c) I)) -> (Membership.mem.{u2, u2} α (Ideal.{u2} α _inst_1) (SetLike.instMembership.{u2, u2} (Ideal.{u2} α _inst_1) α (Submodule.setLike.{u2, u2} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (Semiring.toModule.{u2} α _inst_1))) (Finset.sum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) t (fun (i : ι) => f i)) I)
Case conversion may be inaccurate. Consider using '#align ideal.sum_mem Ideal.sum_memₓ'. -/
theorem sum_mem (I : Ideal α) {ι : Type _} {t : Finset ι} {f : ι → α} :
    (∀ c ∈ t, f c ∈ I) → (∑ i in t, f i) ∈ I :=
  Submodule.sum_mem I
#align ideal.sum_mem Ideal.sum_mem

/- warning: ideal.eq_top_of_unit_mem -> Ideal.eq_top_of_unit_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) (x : α) (y : α), (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) y x) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))) -> (Eq.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) (x : α) (y : α), (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) y x) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_1)))) -> (Eq.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align ideal.eq_top_of_unit_mem Ideal.eq_top_of_unit_memₓ'. -/
theorem eq_top_of_unit_mem (x y : α) (hx : x ∈ I) (h : y * x = 1) : I = ⊤ :=
  eq_top_iff.2 fun z _ =>
    calc
      z = z * (y * x) := by simp [h]
      _ = z * y * x := (Eq.symm <| mul_assoc z y x)
      _ ∈ I := I.mul_mem_left _ hx
      
#align ideal.eq_top_of_unit_mem Ideal.eq_top_of_unit_mem

/- warning: ideal.eq_top_of_is_unit_mem -> Ideal.eq_top_of_isUnit_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) {x : α}, (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I) -> (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) x) -> (Eq.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) {x : α}, (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I) -> (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) x) -> (Eq.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align ideal.eq_top_of_is_unit_mem Ideal.eq_top_of_isUnit_memₓ'. -/
theorem eq_top_of_isUnit_mem {x} (hx : x ∈ I) (h : IsUnit x) : I = ⊤ :=
  let ⟨y, hy⟩ := h.exists_left_inv
  eq_top_of_unit_mem I x y hx hy
#align ideal.eq_top_of_is_unit_mem Ideal.eq_top_of_isUnit_mem

/- warning: ideal.eq_top_iff_one -> Ideal.eq_top_iff_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1), Iff (Eq.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) I)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1), Iff (Eq.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_1))) I)
Case conversion may be inaccurate. Consider using '#align ideal.eq_top_iff_one Ideal.eq_top_iff_oneₓ'. -/
theorem eq_top_iff_one : I = ⊤ ↔ (1 : α) ∈ I :=
  ⟨by rintro rfl <;> trivial, fun h => eq_top_of_unit_mem _ _ 1 h (by simp)⟩
#align ideal.eq_top_iff_one Ideal.eq_top_iff_one

/- warning: ideal.ne_top_iff_one -> Ideal.ne_top_iff_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1), Iff (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Not (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) I))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1), Iff (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Not (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_1))) I))
Case conversion may be inaccurate. Consider using '#align ideal.ne_top_iff_one Ideal.ne_top_iff_oneₓ'. -/
theorem ne_top_iff_one : I ≠ ⊤ ↔ (1 : α) ∉ I :=
  not_congr I.eq_top_iff_one
#align ideal.ne_top_iff_one Ideal.ne_top_iff_one

/- warning: ideal.unit_mul_mem_iff_mem -> Ideal.unit_mul_mem_iff_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) {x : α} {y : α}, (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) y) -> (Iff (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) y x) I) (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) {x : α} {y : α}, (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) y) -> (Iff (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) y x) I) (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I))
Case conversion may be inaccurate. Consider using '#align ideal.unit_mul_mem_iff_mem Ideal.unit_mul_mem_iff_memₓ'. -/
@[simp]
theorem unit_mul_mem_iff_mem {x y : α} (hy : IsUnit y) : y * x ∈ I ↔ x ∈ I :=
  by
  refine' ⟨fun h => _, fun h => I.mul_mem_left y h⟩
  obtain ⟨y', hy'⟩ := hy.exists_left_inv
  have := I.mul_mem_left y' h
  rwa [← mul_assoc, hy', one_mul] at this
#align ideal.unit_mul_mem_iff_mem Ideal.unit_mul_mem_iff_mem

#print Ideal.span /-
/-- The ideal generated by a subset of a ring -/
def span (s : Set α) : Ideal α :=
  Submodule.span α s
#align ideal.span Ideal.span
-/

#print Ideal.submodule_span_eq /-
@[simp]
theorem submodule_span_eq {s : Set α} : Submodule.span α s = Ideal.span s :=
  rfl
#align ideal.submodule_span_eq Ideal.submodule_span_eq
-/

/- warning: ideal.span_empty -> Ideal.span_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Bot.bot.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasBot.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Bot.bot.{u1} (Ideal.{u1} α _inst_1) (Submodule.instBotSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align ideal.span_empty Ideal.span_emptyₓ'. -/
@[simp]
theorem span_empty : span (∅ : Set α) = ⊥ :=
  Submodule.span_empty
#align ideal.span_empty Ideal.span_empty

/- warning: ideal.span_univ -> Ideal.span_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Set.univ.{u1} α)) (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Set.univ.{u1} α)) (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align ideal.span_univ Ideal.span_univₓ'. -/
@[simp]
theorem span_univ : span (Set.univ : Set α) = ⊤ :=
  Submodule.span_univ
#align ideal.span_univ Ideal.span_univ

/- warning: ideal.span_union -> Ideal.span_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Sup.sup.{u1} (Ideal.{u1} α _inst_1) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} α _inst_1) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) (Ideal.span.{u1} α _inst_1 s) (Ideal.span.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Sup.sup.{u1} (Ideal.{u1} α _inst_1) (SemilatticeSup.toSup.{u1} (Ideal.{u1} α _inst_1) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) (Ideal.span.{u1} α _inst_1 s) (Ideal.span.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align ideal.span_union Ideal.span_unionₓ'. -/
theorem span_union (s t : Set α) : span (s ∪ t) = span s ⊔ span t :=
  Submodule.span_union _ _
#align ideal.span_union Ideal.span_union

/- warning: ideal.span_Union -> Ideal.span_iUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {ι : Sort.{u2}} (s : ι -> (Set.{u1} α)), Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Set.iUnion.{u1, u2} α ι (fun (i : ι) => s i))) (iSup.{u1, u2} (Ideal.{u1} α _inst_1) (ConditionallyCompleteLattice.toHasSup.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) ι (fun (i : ι) => Ideal.span.{u1} α _inst_1 (s i)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : Semiring.{u2} α] {ι : Sort.{u1}} (s : ι -> (Set.{u2} α)), Eq.{succ u2} (Ideal.{u2} α _inst_1) (Ideal.span.{u2} α _inst_1 (Set.iUnion.{u2, u1} α ι (fun (i : ι) => s i))) (iSup.{u2, u1} (Ideal.{u2} α _inst_1) (ConditionallyCompleteLattice.toSupSet.{u2} (Ideal.{u2} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Ideal.{u2} α _inst_1) (Submodule.completeLattice.{u2, u2} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α _inst_1))) (Semiring.toModule.{u2} α _inst_1)))) ι (fun (i : ι) => Ideal.span.{u2} α _inst_1 (s i)))
Case conversion may be inaccurate. Consider using '#align ideal.span_Union Ideal.span_iUnionₓ'. -/
theorem span_iUnion {ι} (s : ι → Set α) : span (⋃ i, s i) = ⨆ i, span (s i) :=
  Submodule.span_iUnion _
#align ideal.span_Union Ideal.span_iUnion

#print Ideal.mem_span /-
theorem mem_span {s : Set α} (x) : x ∈ span s ↔ ∀ p : Ideal α, s ⊆ p → x ∈ p :=
  mem_iInter₂
#align ideal.mem_span Ideal.mem_span
-/

#print Ideal.subset_span /-
theorem subset_span {s : Set α} : s ⊆ span s :=
  Submodule.subset_span
#align ideal.subset_span Ideal.subset_span
-/

/- warning: ideal.span_le -> Ideal.span_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {s : Set.{u1} α} {I : Ideal.{u1} α _inst_1}, Iff (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))) (Ideal.span.{u1} α _inst_1 s) I) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ideal.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ideal.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ideal.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))) I))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {s : Set.{u1} α} {I : Ideal.{u1} α _inst_1}, Iff (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) (Ideal.span.{u1} α _inst_1 s) I) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (SetLike.coe.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)) I))
Case conversion may be inaccurate. Consider using '#align ideal.span_le Ideal.span_leₓ'. -/
theorem span_le {s : Set α} {I} : span s ≤ I ↔ s ⊆ I :=
  Submodule.span_le
#align ideal.span_le Ideal.span_le

/- warning: ideal.span_mono -> Ideal.span_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))) (Ideal.span.{u1} α _inst_1 s) (Ideal.span.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) (Ideal.span.{u1} α _inst_1 s) (Ideal.span.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align ideal.span_mono Ideal.span_monoₓ'. -/
theorem span_mono {s t : Set α} : s ⊆ t → span s ≤ span t :=
  Submodule.span_mono
#align ideal.span_mono Ideal.span_mono

#print Ideal.span_eq /-
@[simp]
theorem span_eq : span (I : Set α) = I :=
  Submodule.span_eq _
#align ideal.span_eq Ideal.span_eq
-/

/- warning: ideal.span_singleton_one -> Ideal.span_singleton_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))) (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_1))))) (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_one Ideal.span_singleton_oneₓ'. -/
@[simp]
theorem span_singleton_one : span ({1} : Set α) = ⊤ :=
  (eq_top_iff_one _).2 <| subset_span <| mem_singleton _
#align ideal.span_singleton_one Ideal.span_singleton_one

/- warning: ideal.mem_span_insert -> Ideal.mem_span_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, Iff (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x (Ideal.span.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) y s))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (z : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) z (Ideal.span.{u1} α _inst_1 s)) (fun (H : Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) z (Ideal.span.{u1} α _inst_1 s)) => Eq.{succ u1} α x (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a y) z)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, Iff (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x (Ideal.span.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) y s))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (z : α) => And (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) z (Ideal.span.{u1} α _inst_1 s)) (Eq.{succ u1} α x (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a y) z)))))
Case conversion may be inaccurate. Consider using '#align ideal.mem_span_insert Ideal.mem_span_insertₓ'. -/
theorem mem_span_insert {s : Set α} {x y} :
    x ∈ span (insert y s) ↔ ∃ a, ∃ z ∈ span s, x = a * y + z :=
  Submodule.mem_span_insert
#align ideal.mem_span_insert Ideal.mem_span_insert

/- warning: ideal.mem_span_singleton' -> Ideal.mem_span_singleton' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {x : α} {y : α}, Iff (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y))) (Exists.{succ u1} α (fun (a : α) => Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a y) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {x : α} {y : α}, Iff (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y))) (Exists.{succ u1} α (fun (a : α) => Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a y) x))
Case conversion may be inaccurate. Consider using '#align ideal.mem_span_singleton' Ideal.mem_span_singleton'ₓ'. -/
theorem mem_span_singleton' {x y : α} : x ∈ span ({y} : Set α) ↔ ∃ a, a * y = x :=
  Submodule.mem_span_singleton
#align ideal.mem_span_singleton' Ideal.mem_span_singleton'

/- warning: ideal.span_singleton_le_iff_mem -> Ideal.span_singleton_le_iff_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) {x : α}, Iff (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) I) (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1) {x : α}, Iff (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) I) (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I)
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_le_iff_mem Ideal.span_singleton_le_iff_memₓ'. -/
theorem span_singleton_le_iff_mem {x : α} : span {x} ≤ I ↔ x ∈ I :=
  Submodule.span_singleton_le_iff_mem _ _
#align ideal.span_singleton_le_iff_mem Ideal.span_singleton_le_iff_mem

/- warning: ideal.span_singleton_mul_left_unit -> Ideal.span_singleton_mul_left_unit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {a : α}, (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) a) -> (forall (x : α), Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a x))) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {a : α}, (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)) a) -> (forall (x : α), Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a x))) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_mul_left_unit Ideal.span_singleton_mul_left_unitₓ'. -/
theorem span_singleton_mul_left_unit {a : α} (h2 : IsUnit a) (x : α) :
    span ({a * x} : Set α) = span {x} :=
  by
  apply le_antisymm <;> rw [span_singleton_le_iff_mem, mem_span_singleton']
  exacts[⟨a, rfl⟩, ⟨_, h2.unit.inv_mul_cancel_left x⟩]
#align ideal.span_singleton_mul_left_unit Ideal.span_singleton_mul_left_unit

/- warning: ideal.span_insert -> Ideal.span_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (x : α) (s : Set.{u1} α), Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s)) (Sup.sup.{u1} (Ideal.{u1} α _inst_1) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} α _inst_1) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Ideal.span.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (x : α) (s : Set.{u1} α), Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x s)) (Sup.sup.{u1} (Ideal.{u1} α _inst_1) (SemilatticeSup.toSup.{u1} (Ideal.{u1} α _inst_1) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (Ideal.span.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align ideal.span_insert Ideal.span_insertₓ'. -/
theorem span_insert (x) (s : Set α) : span (insert x s) = span ({x} : Set α) ⊔ span s :=
  Submodule.span_insert x s
#align ideal.span_insert Ideal.span_insert

/- warning: ideal.span_eq_bot -> Ideal.span_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 s) (Bot.bot.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasBot.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {s : Set.{u1} α}, Iff (Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 s) (Bot.bot.{u1} (Ideal.{u1} α _inst_1) (Submodule.instBotSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align ideal.span_eq_bot Ideal.span_eq_botₓ'. -/
theorem span_eq_bot {s : Set α} : span s = ⊥ ↔ ∀ x ∈ s, (x : α) = 0 :=
  Submodule.span_eq_bot
#align ideal.span_eq_bot Ideal.span_eq_bot

/- warning: ideal.span_singleton_eq_bot -> Ideal.span_singleton_eq_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {x : α}, Iff (Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Bot.bot.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasBot.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {x : α}, Iff (Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (Bot.bot.{u1} (Ideal.{u1} α _inst_1) (Submodule.instBotSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_eq_bot Ideal.span_singleton_eq_botₓ'. -/
@[simp]
theorem span_singleton_eq_bot {x} : span ({x} : Set α) = ⊥ ↔ x = 0 :=
  Submodule.span_singleton_eq_bot
#align ideal.span_singleton_eq_bot Ideal.span_singleton_eq_bot

/- warning: ideal.span_singleton_ne_top -> Ideal.span_singleton_ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : CommSemiring.{u1} α] {x : α}, (Not (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2))) x)) -> (Ne.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Top.top.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)) (Submodule.hasTop.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : CommSemiring.{u1} α] {x : α}, (Not (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2))) x)) -> (Ne.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (Top.top.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)) (Submodule.instTopSubmodule.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_2)))))
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_ne_top Ideal.span_singleton_ne_topₓ'. -/
theorem span_singleton_ne_top {α : Type _} [CommSemiring α] {x : α} (hx : ¬IsUnit x) :
    Ideal.span ({x} : Set α) ≠ ⊤ :=
  (Ideal.ne_top_iff_one _).mpr fun h1 =>
    let ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h1
    hx ⟨⟨x, y, mul_comm y x ▸ hy, hy⟩, rfl⟩
#align ideal.span_singleton_ne_top Ideal.span_singleton_ne_top

/- warning: ideal.span_zero -> Ideal.span_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))) (Bot.bot.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasBot.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))))) (Bot.bot.{u1} (Ideal.{u1} α _inst_1) (Submodule.instBotSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align ideal.span_zero Ideal.span_zeroₓ'. -/
@[simp]
theorem span_zero : span (0 : Set α) = ⊥ := by rw [← Set.singleton_zero, span_singleton_eq_bot]
#align ideal.span_zero Ideal.span_zero

/- warning: ideal.span_one -> Ideal.span_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (OfNat.ofNat.{u1} (Set.{u1} α) 1 (OfNat.mk.{u1} (Set.{u1} α) 1 (One.one.{u1} (Set.{u1} α) (Set.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))) (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (OfNat.ofNat.{u1} (Set.{u1} α) 1 (One.toOfNat1.{u1} (Set.{u1} α) (Set.one.{u1} α (Semiring.toOne.{u1} α _inst_1))))) (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align ideal.span_one Ideal.span_oneₓ'. -/
@[simp]
theorem span_one : span (1 : Set α) = ⊤ := by rw [← Set.singleton_one, span_singleton_one]
#align ideal.span_one Ideal.span_one

/- warning: ideal.span_eq_top_iff_finite -> Ideal.span_eq_top_iff_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (s : Set.{u1} α), Iff (Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 s) (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Exists.{succ u1} (Finset.{u1} α) (fun (s' : Finset.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s') s) (Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s')) (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (s : Set.{u1} α), Iff (Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 s) (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Exists.{succ u1} (Finset.{u1} α) (fun (s' : Finset.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Finset.toSet.{u1} α s') s) (Eq.{succ u1} (Ideal.{u1} α _inst_1) (Ideal.span.{u1} α _inst_1 (Finset.toSet.{u1} α s')) (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align ideal.span_eq_top_iff_finite Ideal.span_eq_top_iff_finiteₓ'. -/
theorem span_eq_top_iff_finite (s : Set α) :
    span s = ⊤ ↔ ∃ s' : Finset α, ↑s' ⊆ s ∧ span (s' : Set α) = ⊤ :=
  by
  simp_rw [eq_top_iff_one]
  exact ⟨Submodule.mem_span_finite_of_mem_span, fun ⟨s', h₁, h₂⟩ => span_mono h₁ h₂⟩
#align ideal.span_eq_top_iff_finite Ideal.span_eq_top_iff_finite

/- warning: ideal.mem_span_singleton_sup -> Ideal.mem_span_singleton_sup is a dubious translation:
lean 3 declaration is
  forall {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] {x : S} {y : S} {I : Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)}, Iff (Membership.Mem.{u1, u1} S (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) S (Submodule.setLike.{u1, u1} S S (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (Semiring.toModule.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) x (Sup.sup.{u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (Submodule.completeLattice.{u1, u1} S S (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (Semiring.toModule.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))))) (Ideal.span.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2) (Singleton.singleton.{u1, u1} S (Set.{u1} S) (Set.hasSingleton.{u1} S) y)) I)) (Exists.{succ u1} S (fun (a : S) => Exists.{succ u1} S (fun (b : S) => Exists.{0} (Membership.Mem.{u1, u1} S (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) S (Submodule.setLike.{u1, u1} S S (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (Semiring.toModule.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) b I) (fun (H : Membership.Mem.{u1, u1} S (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) S (Submodule.setLike.{u1, u1} S S (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (Semiring.toModule.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) b I) => Eq.{succ u1} S (HAdd.hAdd.{u1, u1, u1} S S S (instHAdd.{u1} S (Distrib.toHasAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))))) (HMul.hMul.{u1, u1, u1} S S S (instHMul.{u1} S (Distrib.toHasMul.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))))) a y) b) x))))
but is expected to have type
  forall {S : Type.{u1}} [_inst_2 : CommSemiring.{u1} S] {x : S} {y : S} {I : Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)}, Iff (Membership.mem.{u1, u1} S (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) S (Submodule.setLike.{u1, u1} S S (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (Semiring.toModule.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) x (Sup.sup.{u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (SemilatticeSup.toSup.{u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (Submodule.completeLattice.{u1, u1} S S (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (Semiring.toModule.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))))) (Ideal.span.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2) (Singleton.singleton.{u1, u1} S (Set.{u1} S) (Set.instSingletonSet.{u1} S) y)) I)) (Exists.{succ u1} S (fun (a : S) => Exists.{succ u1} S (fun (b : S) => And (Membership.mem.{u1, u1} S (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)) S (Submodule.setLike.{u1, u1} S S (CommSemiring.toSemiring.{u1} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) (Semiring.toModule.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))) b I) (Eq.{succ u1} S (HAdd.hAdd.{u1, u1, u1} S S S (instHAdd.{u1} S (Distrib.toAdd.{u1} S (NonUnitalNonAssocSemiring.toDistrib.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2)))))) (HMul.hMul.{u1, u1, u1} S S S (instHMul.{u1} S (NonUnitalNonAssocSemiring.toMul.{u1} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} S (Semiring.toNonAssocSemiring.{u1} S (CommSemiring.toSemiring.{u1} S _inst_2))))) a y) b) x))))
Case conversion may be inaccurate. Consider using '#align ideal.mem_span_singleton_sup Ideal.mem_span_singleton_supₓ'. -/
theorem mem_span_singleton_sup {S : Type _} [CommSemiring S] {x y : S} {I : Ideal S} :
    x ∈ Ideal.span {y} ⊔ I ↔ ∃ a : S, ∃ b ∈ I, a * y + b = x :=
  by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨ya, hya, b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := mem_span_singleton'.mp hya
    exact ⟨a, b, hb, rfl⟩
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a * y, ideal.mem_span_singleton'.mpr ⟨a, rfl⟩, b, hb, rfl⟩
#align ideal.mem_span_singleton_sup Ideal.mem_span_singleton_sup

#print Ideal.ofRel /-
/-- The ideal generated by an arbitrary binary relation.
-/
def ofRel (r : α → α → Prop) : Ideal α :=
  Submodule.span α { x | ∃ (a b : _)(h : r a b), x + b = a }
#align ideal.of_rel Ideal.ofRel
-/

#print Ideal.IsPrime /-
/-- An ideal `P` of a ring `R` is prime if `P ≠ R` and `xy ∈ P → x ∈ P ∨ y ∈ P` -/
class IsPrime (I : Ideal α) : Prop where
  ne_top' : I ≠ ⊤
  mem_or_mem' : ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
#align ideal.is_prime Ideal.IsPrime
-/

/- warning: ideal.is_prime_iff -> Ideal.isPrime_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, Iff (Ideal.IsPrime.{u1} α _inst_1 I) (And (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (forall {x : α} {y : α}, (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) x y) I) -> (Or (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I) (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) y I))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, Iff (Ideal.IsPrime.{u1} α _inst_1 I) (And (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (forall {x : α} {y : α}, (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) x y) I) -> (Or (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I) (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) y I))))
Case conversion may be inaccurate. Consider using '#align ideal.is_prime_iff Ideal.isPrime_iffₓ'. -/
theorem isPrime_iff {I : Ideal α} : IsPrime I ↔ I ≠ ⊤ ∧ ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨fun h => ⟨h.1, fun _ _ => h.2⟩, fun h => ⟨h.1, fun _ _ => h.2⟩⟩
#align ideal.is_prime_iff Ideal.isPrime_iff

/- warning: ideal.is_prime.ne_top -> Ideal.IsPrime.ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ideal.IsPrime.{u1} α _inst_1 I) -> (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ideal.IsPrime.{u1} α _inst_1 I) -> (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align ideal.is_prime.ne_top Ideal.IsPrime.ne_topₓ'. -/
theorem IsPrime.ne_top {I : Ideal α} (hI : I.IsPrime) : I ≠ ⊤ :=
  hI.1
#align ideal.is_prime.ne_top Ideal.IsPrime.ne_top

/- warning: ideal.is_prime.mem_or_mem -> Ideal.IsPrime.mem_or_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ideal.IsPrime.{u1} α _inst_1 I) -> (forall {x : α} {y : α}, (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) x y) I) -> (Or (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I) (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) y I)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ideal.IsPrime.{u1} α _inst_1 I) -> (forall {x : α} {y : α}, (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) x y) I) -> (Or (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I) (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) y I)))
Case conversion may be inaccurate. Consider using '#align ideal.is_prime.mem_or_mem Ideal.IsPrime.mem_or_memₓ'. -/
theorem IsPrime.mem_or_mem {I : Ideal α} (hI : I.IsPrime) {x y : α} : x * y ∈ I → x ∈ I ∨ y ∈ I :=
  hI.2
#align ideal.is_prime.mem_or_mem Ideal.IsPrime.mem_or_mem

/- warning: ideal.is_prime.mem_or_mem_of_mul_eq_zero -> Ideal.IsPrime.mem_or_mem_of_mul_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ideal.IsPrime.{u1} α _inst_1 I) -> (forall {x : α} {y : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) x y) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))) -> (Or (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I) (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) y I)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ideal.IsPrime.{u1} α _inst_1 I) -> (forall {x : α} {y : α}, (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) x y) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1))))) -> (Or (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I) (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) y I)))
Case conversion may be inaccurate. Consider using '#align ideal.is_prime.mem_or_mem_of_mul_eq_zero Ideal.IsPrime.mem_or_mem_of_mul_eq_zeroₓ'. -/
theorem IsPrime.mem_or_mem_of_mul_eq_zero {I : Ideal α} (hI : I.IsPrime) {x y : α} (h : x * y = 0) :
    x ∈ I ∨ y ∈ I :=
  hI.mem_or_mem (h.symm ▸ I.zero_mem)
#align ideal.is_prime.mem_or_mem_of_mul_eq_zero Ideal.IsPrime.mem_or_mem_of_mul_eq_zero

#print Ideal.IsPrime.mem_of_pow_mem /-
theorem IsPrime.mem_of_pow_mem {I : Ideal α} (hI : I.IsPrime) {r : α} (n : ℕ) (H : r ^ n ∈ I) :
    r ∈ I := by
  induction' n with n ih
  · rw [pow_zero] at H
    exact (mt (eq_top_iff_one _).2 hI.1).elim H
  · rw [pow_succ] at H
    exact Or.cases_on (hI.mem_or_mem H) id ih
#align ideal.is_prime.mem_of_pow_mem Ideal.IsPrime.mem_of_pow_mem
-/

/- warning: ideal.not_is_prime_iff -> Ideal.not_isPrime_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, Iff (Not (Ideal.IsPrime.{u1} α _inst_1 I)) (Or (Eq.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Not (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I)) (fun (H : Not (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I)) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Not (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) y I)) (fun (H : Not (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) y I)) => Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) x y) I))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, Iff (Not (Ideal.IsPrime.{u1} α _inst_1 I)) (Or (Eq.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Not (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I)) (fun (H : Not (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I)) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Not (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) y I)) (fun (H : Not (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) y I)) => Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) x y) I))))))
Case conversion may be inaccurate. Consider using '#align ideal.not_is_prime_iff Ideal.not_isPrime_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » I) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ∉ » I) -/
theorem not_isPrime_iff {I : Ideal α} :
    ¬I.IsPrime ↔ I = ⊤ ∨ ∃ (x : _)(_ : x ∉ I)(y : _)(_ : y ∉ I), x * y ∈ I :=
  by
  simp_rw [Ideal.isPrime_iff, not_and_or, Ne.def, Classical.not_not, not_forall, not_or]
  exact
    or_congr Iff.rfl
      ⟨fun ⟨x, y, hxy, hx, hy⟩ => ⟨x, hx, y, hy, hxy⟩, fun ⟨x, hx, y, hy, hxy⟩ =>
        ⟨x, y, hxy, hx, hy⟩⟩
#align ideal.not_is_prime_iff Ideal.not_isPrime_iff

/- warning: ideal.zero_ne_one_of_proper -> Ideal.zero_ne_one_of_proper is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) -> (Ne.{succ u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) -> (Ne.{succ u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align ideal.zero_ne_one_of_proper Ideal.zero_ne_one_of_properₓ'. -/
theorem zero_ne_one_of_proper {I : Ideal α} (h : I ≠ ⊤) : (0 : α) ≠ 1 := fun hz =>
  I.ne_top_iff_one.1 h <| hz ▸ I.zero_mem
#align ideal.zero_ne_one_of_proper Ideal.zero_ne_one_of_proper

/- warning: ideal.bot_prime -> Ideal.bot_prime is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Ring.{u1} R] [_inst_3 : IsDomain.{u1} R (Ring.toSemiring.{u1} R _inst_2)], Ideal.IsPrime.{u1} R (Ring.toSemiring.{u1} R _inst_2) (Bot.bot.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Submodule.hasBot.{u1, u1} R R (Ring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_2))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : Ring.{u1} R] [_inst_3 : IsDomain.{u1} R (Ring.toSemiring.{u1} R _inst_2)], Ideal.IsPrime.{u1} R (Ring.toSemiring.{u1} R _inst_2) (Bot.bot.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R _inst_2)) (Submodule.instBotSubmodule.{u1, u1} R R (Ring.toSemiring.{u1} R _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R _inst_2)))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R _inst_2))))
Case conversion may be inaccurate. Consider using '#align ideal.bot_prime Ideal.bot_primeₓ'. -/
theorem bot_prime {R : Type _} [Ring R] [IsDomain R] : (⊥ : Ideal R).IsPrime :=
  ⟨fun h => one_ne_zero (by rwa [Ideal.eq_top_iff_one, Submodule.mem_bot] at h), fun x y h =>
    mul_eq_zero.mp (by simpa only [Submodule.mem_bot] using h)⟩
#align ideal.bot_prime Ideal.bot_prime

#print Ideal.IsMaximal /-
/-- An ideal is maximal if it is maximal in the collection of proper ideals. -/
class IsMaximal (I : Ideal α) : Prop where
  out : IsCoatom I
#align ideal.is_maximal Ideal.IsMaximal
-/

/- warning: ideal.is_maximal_def -> Ideal.isMaximal_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, Iff (Ideal.IsMaximal.{u1} α _inst_1 I) (IsCoatom.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) (Submodule.orderTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)) I)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, Iff (Ideal.IsMaximal.{u1} α _inst_1 I) (IsCoatom.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))) (Submodule.instOrderTopSubmoduleToLEToPreorderInstPartialOrderSetLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)) I)
Case conversion may be inaccurate. Consider using '#align ideal.is_maximal_def Ideal.isMaximal_defₓ'. -/
theorem isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoatom I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align ideal.is_maximal_def Ideal.isMaximal_def

/- warning: ideal.is_maximal.ne_top -> Ideal.IsMaximal.ne_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ideal.IsMaximal.{u1} α _inst_1 I) -> (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ideal.IsMaximal.{u1} α _inst_1 I) -> (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align ideal.is_maximal.ne_top Ideal.IsMaximal.ne_topₓ'. -/
theorem IsMaximal.ne_top {I : Ideal α} (h : I.IsMaximal) : I ≠ ⊤ :=
  (isMaximal_def.1 h).1
#align ideal.is_maximal.ne_top Ideal.IsMaximal.ne_top

/- warning: ideal.is_maximal_iff -> Ideal.isMaximal_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, Iff (Ideal.IsMaximal.{u1} α _inst_1 I) (And (Not (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) I)) (forall (J : Ideal.{u1} α _inst_1) (x : α), (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))) I J) -> (Not (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I)) -> (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x J) -> (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) J)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, Iff (Ideal.IsMaximal.{u1} α _inst_1 I) (And (Not (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_1))) I)) (forall (J : Ideal.{u1} α _inst_1) (x : α), (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) I J) -> (Not (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I)) -> (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x J) -> (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_1))) J)))
Case conversion may be inaccurate. Consider using '#align ideal.is_maximal_iff Ideal.isMaximal_iffₓ'. -/
theorem isMaximal_iff {I : Ideal α} :
    I.IsMaximal ↔ (1 : α) ∉ I ∧ ∀ (J : Ideal α) (x), I ≤ J → x ∉ I → x ∈ J → (1 : α) ∈ J :=
  isMaximal_def.trans <|
    and_congr I.ne_top_iff_one <|
      forall_congr' fun J => by
        rw [lt_iff_le_not_le] <;>
          exact
            ⟨fun H x h hx₁ hx₂ => J.eq_top_iff_one.1 <| H ⟨h, not_subset.2 ⟨_, hx₂, hx₁⟩⟩,
              fun H ⟨h₁, h₂⟩ =>
              let ⟨x, xJ, xI⟩ := not_subset.1 h₂
              J.eq_top_iff_one.2 <| H x h₁ xI xJ⟩
#align ideal.is_maximal_iff Ideal.isMaximal_iff

/- warning: ideal.is_maximal.eq_of_le -> Ideal.IsMaximal.eq_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1} {J : Ideal.{u1} α _inst_1}, (Ideal.IsMaximal.{u1} α _inst_1 I) -> (Ne.{succ u1} (Ideal.{u1} α _inst_1) J (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) -> (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))) I J) -> (Eq.{succ u1} (Ideal.{u1} α _inst_1) I J)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1} {J : Ideal.{u1} α _inst_1}, (Ideal.IsMaximal.{u1} α _inst_1 I) -> (Ne.{succ u1} (Ideal.{u1} α _inst_1) J (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) -> (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) I J) -> (Eq.{succ u1} (Ideal.{u1} α _inst_1) I J)
Case conversion may be inaccurate. Consider using '#align ideal.is_maximal.eq_of_le Ideal.IsMaximal.eq_of_leₓ'. -/
theorem IsMaximal.eq_of_le {I J : Ideal α} (hI : I.IsMaximal) (hJ : J ≠ ⊤) (IJ : I ≤ J) : I = J :=
  eq_iff_le_not_lt.2 ⟨IJ, fun h => hJ (hI.1.2 _ h)⟩
#align ideal.is_maximal.eq_of_le Ideal.IsMaximal.eq_of_le

instance : IsCoatomic (Ideal α) :=
  by
  apply CompleteLattice.coatomic_of_top_compact
  rw [← span_singleton_one]
  exact Submodule.singleton_span_isCompactElement 1

/- warning: ideal.is_maximal.coprime_of_ne -> Ideal.IsMaximal.coprime_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {M : Ideal.{u1} α _inst_1} {M' : Ideal.{u1} α _inst_1}, (Ideal.IsMaximal.{u1} α _inst_1 M) -> (Ideal.IsMaximal.{u1} α _inst_1 M') -> (Ne.{succ u1} (Ideal.{u1} α _inst_1) M M') -> (Eq.{succ u1} (Ideal.{u1} α _inst_1) (Sup.sup.{u1} (Ideal.{u1} α _inst_1) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} α _inst_1) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) M M') (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {M : Ideal.{u1} α _inst_1} {M' : Ideal.{u1} α _inst_1}, (Ideal.IsMaximal.{u1} α _inst_1 M) -> (Ideal.IsMaximal.{u1} α _inst_1 M') -> (Ne.{succ u1} (Ideal.{u1} α _inst_1) M M') -> (Eq.{succ u1} (Ideal.{u1} α _inst_1) (Sup.sup.{u1} (Ideal.{u1} α _inst_1) (SemilatticeSup.toSup.{u1} (Ideal.{u1} α _inst_1) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} α _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) M M') (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align ideal.is_maximal.coprime_of_ne Ideal.IsMaximal.coprime_of_neₓ'. -/
theorem IsMaximal.coprime_of_ne {M M' : Ideal α} (hM : M.IsMaximal) (hM' : M'.IsMaximal)
    (hne : M ≠ M') : M ⊔ M' = ⊤ := by
  contrapose! hne with h
  exact hM.eq_of_le hM'.ne_top (le_sup_left.trans_eq (hM'.eq_of_le h le_sup_right).symm)
#align ideal.is_maximal.coprime_of_ne Ideal.IsMaximal.coprime_of_ne

/- warning: ideal.exists_le_maximal -> Ideal.exists_le_maximal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1), (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) -> (Exists.{succ u1} (Ideal.{u1} α _inst_1) (fun (M : Ideal.{u1} α _inst_1) => And (Ideal.IsMaximal.{u1} α _inst_1 M) (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))) I M)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] (I : Ideal.{u1} α _inst_1), (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) -> (Exists.{succ u1} (Ideal.{u1} α _inst_1) (fun (M : Ideal.{u1} α _inst_1) => And (Ideal.IsMaximal.{u1} α _inst_1 M) (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) I M)))
Case conversion may be inaccurate. Consider using '#align ideal.exists_le_maximal Ideal.exists_le_maximalₓ'. -/
/-- **Krull's theorem**: if `I` is an ideal that is not the whole ring, then it is included in some
    maximal ideal. -/
theorem exists_le_maximal (I : Ideal α) (hI : I ≠ ⊤) : ∃ M : Ideal α, M.IsMaximal ∧ I ≤ M :=
  let ⟨m, hm⟩ := (eq_top_or_exists_le_coatom I).resolve_left hI
  ⟨m, ⟨⟨hm.1⟩, hm.2⟩⟩
#align ideal.exists_le_maximal Ideal.exists_le_maximal

variable (α)

#print Ideal.exists_maximal /-
/-- Krull's theorem: a nontrivial ring has a maximal ideal. -/
theorem exists_maximal [Nontrivial α] : ∃ M : Ideal α, M.IsMaximal :=
  let ⟨I, ⟨hI, _⟩⟩ := exists_le_maximal (⊥ : Ideal α) bot_ne_top
  ⟨I, hI⟩
#align ideal.exists_maximal Ideal.exists_maximal
-/

variable {α}

instance [Nontrivial α] : Nontrivial (Ideal α) :=
  by
  rcases@exists_maximal α _ _ with ⟨M, hM, _⟩
  exact nontrivial_of_ne M ⊤ hM

/- warning: ideal.maximal_of_no_maximal -> Ideal.maximal_of_no_maximal is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {P : Ideal.{u1} R _inst_2}, (forall (m : Ideal.{u1} R _inst_2), (LT.lt.{u1} (Ideal.{u1} R _inst_2) (Preorder.toLT.{u1} (Ideal.{u1} R _inst_2) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R _inst_2) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))))) P m) -> (Not (Ideal.IsMaximal.{u1} R _inst_2 m))) -> (forall (J : Ideal.{u1} R _inst_2), (LT.lt.{u1} (Ideal.{u1} R _inst_2) (Preorder.toLT.{u1} (Ideal.{u1} R _inst_2) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R _inst_2) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))))) P J) -> (Eq.{succ u1} (Ideal.{u1} R _inst_2) J (Top.top.{u1} (Ideal.{u1} R _inst_2) (Submodule.hasTop.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {P : Ideal.{u1} R _inst_2}, (forall (m : Ideal.{u1} R _inst_2), (LT.lt.{u1} (Ideal.{u1} R _inst_2) (Preorder.toLT.{u1} (Ideal.{u1} R _inst_2) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R _inst_2) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} R _inst_2) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} R _inst_2) (Submodule.completeLattice.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))))) P m) -> (Not (Ideal.IsMaximal.{u1} R _inst_2 m))) -> (forall (J : Ideal.{u1} R _inst_2), (LT.lt.{u1} (Ideal.{u1} R _inst_2) (Preorder.toLT.{u1} (Ideal.{u1} R _inst_2) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R _inst_2) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} R _inst_2) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} R _inst_2) (Submodule.completeLattice.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))))) P J) -> (Eq.{succ u1} (Ideal.{u1} R _inst_2) J (Top.top.{u1} (Ideal.{u1} R _inst_2) (Submodule.instTopSubmodule.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))))
Case conversion may be inaccurate. Consider using '#align ideal.maximal_of_no_maximal Ideal.maximal_of_no_maximalₓ'. -/
/-- If P is not properly contained in any maximal ideal then it is not properly contained
  in any proper ideal -/
theorem maximal_of_no_maximal {R : Type u} [Semiring R] {P : Ideal R}
    (hmax : ∀ m : Ideal R, P < m → ¬IsMaximal m) (J : Ideal R) (hPJ : P < J) : J = ⊤ :=
  by
  by_contra hnonmax
  rcases exists_le_maximal J hnonmax with ⟨M, hM1, hM2⟩
  exact hmax M (lt_of_lt_of_le hPJ hM2) hM1
#align ideal.maximal_of_no_maximal Ideal.maximal_of_no_maximal

#print Ideal.span_pair_comm /-
theorem span_pair_comm {x y : α} : (span {x, y} : Ideal α) = span {y, x} := by
  simp only [span_insert, sup_comm]
#align ideal.span_pair_comm Ideal.span_pair_comm
-/

/- warning: ideal.mem_span_pair -> Ideal.mem_span_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {x : α} {y : α} {z : α}, Iff (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) z (Ideal.span.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y)))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) a x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) b y)) z)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {x : α} {y : α} {z : α}, Iff (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) z (Ideal.span.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y)))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) b y)) z)))
Case conversion may be inaccurate. Consider using '#align ideal.mem_span_pair Ideal.mem_span_pairₓ'. -/
theorem mem_span_pair {x y z : α} : z ∈ span ({x, y} : Set α) ↔ ∃ a b, a * x + b * y = z :=
  Submodule.mem_span_pair
#align ideal.mem_span_pair Ideal.mem_span_pair

/- warning: ideal.span_pair_add_mul_left -> Ideal.span_pair_add_mul_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] {x : R} {y : R} (z : R), Eq.{succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Ideal.span.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2)) (Insert.insert.{u1, u1} R (Set.{u1} R) (Set.hasInsert.{u1} R) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_2)))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_2)))) y z)) (Singleton.singleton.{u1, u1} R (Set.{u1} R) (Set.hasSingleton.{u1} R) y))) (Ideal.span.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2)) (Insert.insert.{u1, u1} R (Set.{u1} R) (Set.hasInsert.{u1} R) x (Singleton.singleton.{u1, u1} R (Set.{u1} R) (Set.hasSingleton.{u1} R) y)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] {x : R} {y : R} (z : R), Eq.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2))) (Ideal.span.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2)) (Insert.insert.{u1, u1} R (Set.{u1} R) (Set.instInsertSet.{u1} R) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))))) x (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) y z)) (Singleton.singleton.{u1, u1} R (Set.{u1} R) (Set.instSingletonSet.{u1} R) y))) (Ideal.span.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2)) (Insert.insert.{u1, u1} R (Set.{u1} R) (Set.instInsertSet.{u1} R) x (Singleton.singleton.{u1, u1} R (Set.{u1} R) (Set.instSingletonSet.{u1} R) y)))
Case conversion may be inaccurate. Consider using '#align ideal.span_pair_add_mul_left Ideal.span_pair_add_mul_leftₓ'. -/
@[simp]
theorem span_pair_add_mul_left {R : Type u} [CommRing R] {x y : R} (z : R) :
    (span {x + y * z, y} : Ideal R) = span {x, y} :=
  by
  ext
  rw [mem_span_pair, mem_span_pair]
  exact
    ⟨fun ⟨a, b, h⟩ =>
      ⟨a, b + a * z, by
        rw [← h]
        ring1⟩,
      fun ⟨a, b, h⟩ =>
      ⟨a, b - a * z, by
        rw [← h]
        ring1⟩⟩
#align ideal.span_pair_add_mul_left Ideal.span_pair_add_mul_left

/- warning: ideal.span_pair_add_mul_right -> Ideal.span_pair_add_mul_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] {x : R} {y : R} (z : R), Eq.{succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2))) (Ideal.span.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2)) (Insert.insert.{u1, u1} R (Set.{u1} R) (Set.hasInsert.{u1} R) x (Singleton.singleton.{u1, u1} R (Set.{u1} R) (Set.hasSingleton.{u1} R) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_2)))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_2)))) x z))))) (Ideal.span.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_2)) (Insert.insert.{u1, u1} R (Set.{u1} R) (Set.hasInsert.{u1} R) x (Singleton.singleton.{u1, u1} R (Set.{u1} R) (Set.hasSingleton.{u1} R) y)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : CommRing.{u1} R] {x : R} {y : R} (z : R), Eq.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2))) (Ideal.span.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2)) (Insert.insert.{u1, u1} R (Set.{u1} R) (Set.instInsertSet.{u1} R) x (Singleton.singleton.{u1, u1} R (Set.{u1} R) (Set.instSingletonSet.{u1} R) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))))) y (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_2))))) x z))))) (Ideal.span.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_2)) (Insert.insert.{u1, u1} R (Set.{u1} R) (Set.instInsertSet.{u1} R) x (Singleton.singleton.{u1, u1} R (Set.{u1} R) (Set.instSingletonSet.{u1} R) y)))
Case conversion may be inaccurate. Consider using '#align ideal.span_pair_add_mul_right Ideal.span_pair_add_mul_rightₓ'. -/
@[simp]
theorem span_pair_add_mul_right {R : Type u} [CommRing R] {x y : R} (z : R) :
    (span {x, y + x * z} : Ideal R) = span {x, y} := by
  rw [span_pair_comm, span_pair_add_mul_left, span_pair_comm]
#align ideal.span_pair_add_mul_right Ideal.span_pair_add_mul_right

/- warning: ideal.is_maximal.exists_inv -> Ideal.IsMaximal.exists_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ideal.IsMaximal.{u1} α _inst_1 I) -> (forall {x : α}, (Not (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I)) -> (Exists.{succ u1} α (fun (y : α) => Exists.{succ u1} α (fun (i : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) i I) (fun (H : Membership.Mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) i I) => Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) y x) i) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ideal.IsMaximal.{u1} α _inst_1 I) -> (forall {x : α}, (Not (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) x I)) -> (Exists.{succ u1} α (fun (y : α) => Exists.{succ u1} α (fun (i : α) => And (Membership.mem.{u1, u1} α (Ideal.{u1} α _inst_1) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))) i I) (Eq.{succ u1} α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) y x) i) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align ideal.is_maximal.exists_inv Ideal.IsMaximal.exists_invₓ'. -/
theorem IsMaximal.exists_inv {I : Ideal α} (hI : I.IsMaximal) {x} (hx : x ∉ I) :
    ∃ y, ∃ i ∈ I, y * x + i = 1 :=
  by
  cases' is_maximal_iff.1 hI with H₁ H₂
  rcases mem_span_insert.1
      (H₂ (span (insert x I)) x (Set.Subset.trans (subset_insert _ _) subset_span) hx
        (subset_span (mem_insert _ _))) with
    ⟨y, z, hz, hy⟩
  refine' ⟨y, z, _, hy.symm⟩
  rwa [← span_eq I]
#align ideal.is_maximal.exists_inv Ideal.IsMaximal.exists_inv

section Lattice

variable {R : Type u} [Semiring R]

/- warning: ideal.mem_sup_left -> Ideal.mem_sup_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {S : Ideal.{u1} R _inst_2} {T : Ideal.{u1} R _inst_2} {x : R}, (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x S) -> (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (Sup.sup.{u1} (Ideal.{u1} R _inst_2) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} R _inst_2) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} R _inst_2) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} R _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} R _inst_2) (Submodule.completeLattice.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))))) S T))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {S : Ideal.{u1} R _inst_2} {T : Ideal.{u1} R _inst_2} {x : R}, (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x S) -> (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (Sup.sup.{u1} (Ideal.{u1} R _inst_2) (SemilatticeSup.toSup.{u1} (Ideal.{u1} R _inst_2) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} R _inst_2) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} R _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} R _inst_2) (Submodule.completeLattice.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))))) S T))
Case conversion may be inaccurate. Consider using '#align ideal.mem_sup_left Ideal.mem_sup_leftₓ'. -/
theorem mem_sup_left {S T : Ideal R} : ∀ {x : R}, x ∈ S → x ∈ S ⊔ T :=
  show S ≤ S ⊔ T from le_sup_left
#align ideal.mem_sup_left Ideal.mem_sup_left

/- warning: ideal.mem_sup_right -> Ideal.mem_sup_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {S : Ideal.{u1} R _inst_2} {T : Ideal.{u1} R _inst_2} {x : R}, (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x T) -> (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (Sup.sup.{u1} (Ideal.{u1} R _inst_2) (SemilatticeSup.toHasSup.{u1} (Ideal.{u1} R _inst_2) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} R _inst_2) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} R _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} R _inst_2) (Submodule.completeLattice.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))))) S T))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {S : Ideal.{u1} R _inst_2} {T : Ideal.{u1} R _inst_2} {x : R}, (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x T) -> (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (Sup.sup.{u1} (Ideal.{u1} R _inst_2) (SemilatticeSup.toSup.{u1} (Ideal.{u1} R _inst_2) (Lattice.toSemilatticeSup.{u1} (Ideal.{u1} R _inst_2) (ConditionallyCompleteLattice.toLattice.{u1} (Ideal.{u1} R _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} R _inst_2) (Submodule.completeLattice.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))))) S T))
Case conversion may be inaccurate. Consider using '#align ideal.mem_sup_right Ideal.mem_sup_rightₓ'. -/
theorem mem_sup_right {S T : Ideal R} : ∀ {x : R}, x ∈ T → x ∈ S ⊔ T :=
  show T ≤ S ⊔ T from le_sup_right
#align ideal.mem_sup_right Ideal.mem_sup_right

/- warning: ideal.mem_supr_of_mem -> Ideal.mem_iSup_of_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {ι : Sort.{u2}} {S : ι -> (Ideal.{u1} R _inst_2)} (i : ι) {x : R}, (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (S i)) -> (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (iSup.{u1, u2} (Ideal.{u1} R _inst_2) (ConditionallyCompleteLattice.toHasSup.{u1} (Ideal.{u1} R _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} R _inst_2) (Submodule.completeLattice.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))) ι S))
but is expected to have type
  forall {R : Type.{u2}} [_inst_2 : Semiring.{u2} R] {ι : Sort.{u1}} {S : ι -> (Ideal.{u2} R _inst_2)} (i : ι) {x : R}, (Membership.mem.{u2, u2} R (Ideal.{u2} R _inst_2) (SetLike.instMembership.{u2, u2} (Ideal.{u2} R _inst_2) R (Submodule.setLike.{u2, u2} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Semiring.toModule.{u2} R _inst_2))) x (S i)) -> (Membership.mem.{u2, u2} R (Ideal.{u2} R _inst_2) (SetLike.instMembership.{u2, u2} (Ideal.{u2} R _inst_2) R (Submodule.setLike.{u2, u2} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Semiring.toModule.{u2} R _inst_2))) x (iSup.{u2, u1} (Ideal.{u2} R _inst_2) (ConditionallyCompleteLattice.toSupSet.{u2} (Ideal.{u2} R _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Ideal.{u2} R _inst_2) (Submodule.completeLattice.{u2, u2} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Semiring.toModule.{u2} R _inst_2)))) ι S))
Case conversion may be inaccurate. Consider using '#align ideal.mem_supr_of_mem Ideal.mem_iSup_of_memₓ'. -/
theorem mem_iSup_of_mem {ι : Sort _} {S : ι → Ideal R} (i : ι) : ∀ {x : R}, x ∈ S i → x ∈ iSup S :=
  show S i ≤ iSup S from le_iSup _ _
#align ideal.mem_supr_of_mem Ideal.mem_iSup_of_mem

/- warning: ideal.mem_Sup_of_mem -> Ideal.mem_sSup_of_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {S : Set.{u1} (Ideal.{u1} R _inst_2)} {s : Ideal.{u1} R _inst_2}, (Membership.Mem.{u1, u1} (Ideal.{u1} R _inst_2) (Set.{u1} (Ideal.{u1} R _inst_2)) (Set.hasMem.{u1} (Ideal.{u1} R _inst_2)) s S) -> (forall {x : R}, (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x s) -> (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (SupSet.sSup.{u1} (Ideal.{u1} R _inst_2) (ConditionallyCompleteLattice.toHasSup.{u1} (Ideal.{u1} R _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} R _inst_2) (Submodule.completeLattice.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))) S)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {S : Set.{u1} (Ideal.{u1} R _inst_2)} {s : Ideal.{u1} R _inst_2}, (Membership.mem.{u1, u1} (Ideal.{u1} R _inst_2) (Set.{u1} (Ideal.{u1} R _inst_2)) (Set.instMembershipSet.{u1} (Ideal.{u1} R _inst_2)) s S) -> (forall {x : R}, (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x s) -> (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (SupSet.sSup.{u1} (Ideal.{u1} R _inst_2) (ConditionallyCompleteLattice.toSupSet.{u1} (Ideal.{u1} R _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} R _inst_2) (Submodule.completeLattice.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))) S)))
Case conversion may be inaccurate. Consider using '#align ideal.mem_Sup_of_mem Ideal.mem_sSup_of_memₓ'. -/
theorem mem_sSup_of_mem {S : Set (Ideal R)} {s : Ideal R} (hs : s ∈ S) :
    ∀ {x : R}, x ∈ s → x ∈ sSup S :=
  show s ≤ sSup S from le_sSup hs
#align ideal.mem_Sup_of_mem Ideal.mem_sSup_of_mem

/- warning: ideal.mem_Inf -> Ideal.mem_sInf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {s : Set.{u1} (Ideal.{u1} R _inst_2)} {x : R}, Iff (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (InfSet.sInf.{u1} (Ideal.{u1} R _inst_2) (Submodule.hasInf.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)) s)) (forall {{I : Ideal.{u1} R _inst_2}}, (Membership.Mem.{u1, u1} (Ideal.{u1} R _inst_2) (Set.{u1} (Ideal.{u1} R _inst_2)) (Set.hasMem.{u1} (Ideal.{u1} R _inst_2)) I s) -> (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x I))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {s : Set.{u1} (Ideal.{u1} R _inst_2)} {x : R}, Iff (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (InfSet.sInf.{u1} (Ideal.{u1} R _inst_2) (Submodule.instInfSetSubmodule.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)) s)) (forall {{I : Ideal.{u1} R _inst_2}}, (Membership.mem.{u1, u1} (Ideal.{u1} R _inst_2) (Set.{u1} (Ideal.{u1} R _inst_2)) (Set.instMembershipSet.{u1} (Ideal.{u1} R _inst_2)) I s) -> (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x I))
Case conversion may be inaccurate. Consider using '#align ideal.mem_Inf Ideal.mem_sInfₓ'. -/
theorem mem_sInf {s : Set (Ideal R)} {x : R} : x ∈ sInf s ↔ ∀ ⦃I⦄, I ∈ s → x ∈ I :=
  ⟨fun hx I his => hx I ⟨I, iInf_pos his⟩, fun H I ⟨J, hij⟩ => hij ▸ fun S ⟨hj, hS⟩ => hS ▸ H hj⟩
#align ideal.mem_Inf Ideal.mem_sInf

/- warning: ideal.mem_inf -> Ideal.mem_inf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {I : Ideal.{u1} R _inst_2} {J : Ideal.{u1} R _inst_2} {x : R}, Iff (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (Inf.inf.{u1} (Ideal.{u1} R _inst_2) (Submodule.hasInf.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)) I J)) (And (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x I) (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x J))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {I : Ideal.{u1} R _inst_2} {J : Ideal.{u1} R _inst_2} {x : R}, Iff (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (Inf.inf.{u1} (Ideal.{u1} R _inst_2) (Submodule.instInfSubmodule.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)) I J)) (And (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x I) (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x J))
Case conversion may be inaccurate. Consider using '#align ideal.mem_inf Ideal.mem_infₓ'. -/
@[simp]
theorem mem_inf {I J : Ideal R} {x : R} : x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl
#align ideal.mem_inf Ideal.mem_inf

/- warning: ideal.mem_infi -> Ideal.mem_iInf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {ι : Sort.{u2}} {I : ι -> (Ideal.{u1} R _inst_2)} {x : R}, Iff (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (iInf.{u1, u2} (Ideal.{u1} R _inst_2) (Submodule.hasInf.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)) ι I)) (forall (i : ι), Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (I i))
but is expected to have type
  forall {R : Type.{u2}} [_inst_2 : Semiring.{u2} R] {ι : Sort.{u1}} {I : ι -> (Ideal.{u2} R _inst_2)} {x : R}, Iff (Membership.mem.{u2, u2} R (Ideal.{u2} R _inst_2) (SetLike.instMembership.{u2, u2} (Ideal.{u2} R _inst_2) R (Submodule.setLike.{u2, u2} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Semiring.toModule.{u2} R _inst_2))) x (iInf.{u2, u1} (Ideal.{u2} R _inst_2) (Submodule.instInfSetSubmodule.{u2, u2} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Semiring.toModule.{u2} R _inst_2)) ι I)) (forall (i : ι), Membership.mem.{u2, u2} R (Ideal.{u2} R _inst_2) (SetLike.instMembership.{u2, u2} (Ideal.{u2} R _inst_2) R (Submodule.setLike.{u2, u2} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Semiring.toModule.{u2} R _inst_2))) x (I i))
Case conversion may be inaccurate. Consider using '#align ideal.mem_infi Ideal.mem_iInfₓ'. -/
@[simp]
theorem mem_iInf {ι : Sort _} {I : ι → Ideal R} {x : R} : x ∈ iInf I ↔ ∀ i, x ∈ I i :=
  Submodule.mem_iInf _
#align ideal.mem_infi Ideal.mem_iInf

/- warning: ideal.mem_bot -> Ideal.mem_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {x : R}, Iff (Membership.Mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (Bot.bot.{u1} (Ideal.{u1} R _inst_2) (Submodule.hasBot.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : Semiring.{u1} R] {x : R}, Iff (Membership.mem.{u1, u1} R (Ideal.{u1} R _inst_2) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R _inst_2) R (Submodule.setLike.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2))) x (Bot.bot.{u1} (Ideal.{u1} R _inst_2) (Submodule.instBotSubmodule.{u1, u1} R R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (Semiring.toModule.{u1} R _inst_2)))) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_2)))))
Case conversion may be inaccurate. Consider using '#align ideal.mem_bot Ideal.mem_botₓ'. -/
@[simp]
theorem mem_bot {x : R} : x ∈ (⊥ : Ideal R) ↔ x = 0 :=
  Submodule.mem_bot _
#align ideal.mem_bot Ideal.mem_bot

end Lattice

section Pi

variable (ι : Type v)

#print Ideal.pi /-
/-- `I^n` as an ideal of `R^n`. -/
def pi : Ideal (ι → α) where
  carrier := { x | ∀ i, x i ∈ I }
  zero_mem' i := I.zero_mem
  add_mem' a b ha hb i := I.add_mem (ha i) (hb i)
  smul_mem' a b hb i := I.mul_mem_left (a i) (hb i)
#align ideal.pi Ideal.pi
-/

#print Ideal.mem_pi /-
theorem mem_pi (x : ι → α) : x ∈ I.pi ι ↔ ∀ i, x i ∈ I :=
  Iff.rfl
#align ideal.mem_pi Ideal.mem_pi
-/

end Pi

/- warning: ideal.Inf_is_prime_of_is_chain -> Ideal.sInf_isPrime_of_isChain is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {s : Set.{u1} (Ideal.{u1} α _inst_1)}, (Set.Nonempty.{u1} (Ideal.{u1} α _inst_1) s) -> (IsChain.{u1} (Ideal.{u1} α _inst_1) (LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) s) -> (forall (p : Ideal.{u1} α _inst_1), (Membership.Mem.{u1, u1} (Ideal.{u1} α _inst_1) (Set.{u1} (Ideal.{u1} α _inst_1)) (Set.hasMem.{u1} (Ideal.{u1} α _inst_1)) p s) -> (Ideal.IsPrime.{u1} α _inst_1 p)) -> (Ideal.IsPrime.{u1} α _inst_1 (InfSet.sInf.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasInf.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {s : Set.{u1} (Ideal.{u1} α _inst_1)}, (Set.Nonempty.{u1} (Ideal.{u1} α _inst_1) s) -> (IsChain.{u1} (Ideal.{u1} α _inst_1) (fun (x._@.Mathlib.RingTheory.Ideal.Basic._hyg.4480 : Ideal.{u1} α _inst_1) (x._@.Mathlib.RingTheory.Ideal.Basic._hyg.4482 : Ideal.{u1} α _inst_1) => LE.le.{u1} (Ideal.{u1} α _inst_1) (Preorder.toLE.{u1} (Ideal.{u1} α _inst_1) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} α _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} α _inst_1) (Submodule.completeLattice.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))))) x._@.Mathlib.RingTheory.Ideal.Basic._hyg.4480 x._@.Mathlib.RingTheory.Ideal.Basic._hyg.4482) s) -> (forall (p : Ideal.{u1} α _inst_1), (Membership.mem.{u1, u1} (Ideal.{u1} α _inst_1) (Set.{u1} (Ideal.{u1} α _inst_1)) (Set.instMembershipSet.{u1} (Ideal.{u1} α _inst_1)) p s) -> (Ideal.IsPrime.{u1} α _inst_1 p)) -> (Ideal.IsPrime.{u1} α _inst_1 (InfSet.sInf.{u1} (Ideal.{u1} α _inst_1) (Submodule.instInfSetSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align ideal.Inf_is_prime_of_is_chain Ideal.sInf_isPrime_of_isChainₓ'. -/
theorem sInf_isPrime_of_isChain {s : Set (Ideal α)} (hs : s.Nonempty) (hs' : IsChain (· ≤ ·) s)
    (H : ∀ p ∈ s, Ideal.IsPrime p) : (sInf s).IsPrime :=
  ⟨fun e =>
    let ⟨x, hx⟩ := hs
    (H x hx).ne_top (eq_top_iff.mpr (e.symm.trans_le (sInf_le hx))),
    fun x y e =>
    or_iff_not_imp_left.mpr fun hx =>
      by
      rw [Ideal.mem_sInf] at hx e⊢
      push_neg  at hx
      obtain ⟨I, hI, hI'⟩ := hx
      intro J hJ
      cases hs'.total hI hJ
      · exact h (((H I hI).mem_or_mem (e hI)).resolve_left hI')
      · exact ((H J hJ).mem_or_mem (e hJ)).resolve_left fun x => hI' <| h x⟩
#align ideal.Inf_is_prime_of_is_chain Ideal.sInf_isPrime_of_isChain

end Ideal

end Semiring

section CommSemiring

variable {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace Ideal

variable [CommSemiring α] (I : Ideal α)

/- warning: ideal.mul_unit_mem_iff_mem -> Ideal.mul_unit_mem_iff_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] (I : Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) {x : α} {y : α}, (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))) y) -> (Iff (Membership.Mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) x y) I) (Membership.Mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) x I))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] (I : Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) {x : α} {y : α}, (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))) y) -> (Iff (Membership.mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) x y) I) (Membership.mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) x I))
Case conversion may be inaccurate. Consider using '#align ideal.mul_unit_mem_iff_mem Ideal.mul_unit_mem_iff_memₓ'. -/
@[simp]
theorem mul_unit_mem_iff_mem {x y : α} (hy : IsUnit y) : x * y ∈ I ↔ x ∈ I :=
  mul_comm y x ▸ unit_mul_mem_iff_mem I hy
#align ideal.mul_unit_mem_iff_mem Ideal.mul_unit_mem_iff_mem

#print Ideal.mem_span_singleton /-
theorem mem_span_singleton {x y : α} : x ∈ span ({y} : Set α) ↔ y ∣ x :=
  mem_span_singleton'.trans <| exists_congr fun _ => by rw [eq_comm, mul_comm]
#align ideal.mem_span_singleton Ideal.mem_span_singleton
-/

#print Ideal.mem_span_singleton_self /-
theorem mem_span_singleton_self (x : α) : x ∈ span ({x} : Set α) :=
  mem_span_singleton.mpr dvd_rfl
#align ideal.mem_span_singleton_self Ideal.mem_span_singleton_self
-/

/- warning: ideal.span_singleton_le_span_singleton -> Ideal.span_singleton_le_span_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {x : α} {y : α}, Iff (LE.le.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Preorder.toLE.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y))) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α (CommSemiring.toNonUnitalCommSemiring.{u1} α _inst_1))))) y x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {x : α} {y : α}, Iff (LE.le.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Preorder.toLE.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (PartialOrder.toPreorder.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Submodule.completeLattice.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))))) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y))) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α (CommSemiring.toNonUnitalCommSemiring.{u1} α _inst_1))))) y x)
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_le_span_singleton Ideal.span_singleton_le_span_singletonₓ'. -/
theorem span_singleton_le_span_singleton {x y : α} :
    span ({x} : Set α) ≤ span ({y} : Set α) ↔ y ∣ x :=
  span_le.trans <| singleton_subset_iff.trans mem_span_singleton
#align ideal.span_singleton_le_span_singleton Ideal.span_singleton_le_span_singleton

/- warning: ideal.span_singleton_eq_span_singleton -> Ideal.span_singleton_eq_span_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : CommRing.{u1} α] [_inst_3 : IsDomain.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_2))] {x : α} {y : α}, Iff (Eq.{succ u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_2))) (Ideal.span.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_2)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Ideal.span.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α _inst_2)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y))) (Associated.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α _inst_2)) x y)
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : CommRing.{u1} α] [_inst_3 : IsDomain.{u1} α (CommSemiring.toSemiring.{u1} α (CommRing.toCommSemiring.{u1} α _inst_2))] {x : α} {y : α}, Iff (Eq.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α (CommRing.toCommSemiring.{u1} α _inst_2))) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α (CommRing.toCommSemiring.{u1} α _inst_2)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α (CommRing.toCommSemiring.{u1} α _inst_2)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y))) (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α (CommRing.toCommSemiring.{u1} α _inst_2)))) x y)
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_eq_span_singleton Ideal.span_singleton_eq_span_singletonₓ'. -/
theorem span_singleton_eq_span_singleton {α : Type u} [CommRing α] [IsDomain α] {x y : α} :
    span ({x} : Set α) = span ({y} : Set α) ↔ Associated x y :=
  by
  rw [← dvd_dvd_iff_associated, le_antisymm_iff, and_comm']
  apply and_congr <;> rw [span_singleton_le_span_singleton]
#align ideal.span_singleton_eq_span_singleton Ideal.span_singleton_eq_span_singleton

/- warning: ideal.span_singleton_mul_right_unit -> Ideal.span_singleton_mul_right_unit is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {a : α}, (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))) a) -> (forall (x : α), Eq.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) x a))) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {a : α}, (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))) a) -> (forall (x : α), Eq.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) x a))) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_mul_right_unit Ideal.span_singleton_mul_right_unitₓ'. -/
theorem span_singleton_mul_right_unit {a : α} (h2 : IsUnit a) (x : α) :
    span ({x * a} : Set α) = span {x} := by rw [mul_comm, span_singleton_mul_left_unit h2]
#align ideal.span_singleton_mul_right_unit Ideal.span_singleton_mul_right_unit

/- warning: ideal.span_singleton_eq_top -> Ideal.span_singleton_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {x : α}, Iff (Eq.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Top.top.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Submodule.hasTop.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {x : α}, Iff (Eq.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (Top.top.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Submodule.instTopSubmodule.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))) x)
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_eq_top Ideal.span_singleton_eq_topₓ'. -/
theorem span_singleton_eq_top {x} : span ({x} : Set α) = ⊤ ↔ IsUnit x := by
  rw [isUnit_iff_dvd_one, ← span_singleton_le_span_singleton, span_singleton_one, eq_top_iff]
#align ideal.span_singleton_eq_top Ideal.span_singleton_eq_top

/- warning: ideal.span_singleton_prime -> Ideal.span_singleton_prime is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {p : α}, (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))))))) -> (Iff (Ideal.IsPrime.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) p))) (Prime.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α _inst_1) p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {p : α}, (Ne.{succ u1} α p (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α _inst_1))))) -> (Iff (Ideal.IsPrime.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) p))) (Prime.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α _inst_1) p))
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_prime Ideal.span_singleton_primeₓ'. -/
theorem span_singleton_prime {p : α} (hp : p ≠ 0) : IsPrime (span ({p} : Set α)) ↔ Prime p := by
  simp [is_prime_iff, Prime, span_singleton_eq_top, hp, mem_span_singleton]
#align ideal.span_singleton_prime Ideal.span_singleton_prime

#print Ideal.IsMaximal.isPrime /-
theorem IsMaximal.isPrime {I : Ideal α} (H : I.IsMaximal) : I.IsPrime :=
  ⟨H.1.1, fun x y hxy =>
    or_iff_not_imp_left.2 fun hx =>
      by
      let J : Ideal α := Submodule.span α (insert x ↑I)
      have IJ : I ≤ J := Set.Subset.trans (subset_insert _ _) subset_span
      have xJ : x ∈ J := Ideal.subset_span (Set.mem_insert x I)
      cases' is_maximal_iff.1 H with _ oJ
      specialize oJ J x IJ hx xJ
      rcases submodule.mem_span_insert.mp oJ with ⟨a, b, h, oe⟩
      obtain F : y * 1 = y * (a • x + b) := congr_arg (fun g : α => y * g) oe
      rw [← mul_one y, F, mul_add, mul_comm, smul_eq_mul, mul_assoc]
      refine' Submodule.add_mem I (I.mul_mem_left a hxy) (Submodule.smul_mem I y _)
      rwa [Submodule.span_eq] at h⟩
#align ideal.is_maximal.is_prime Ideal.IsMaximal.isPrime
-/

#print Ideal.IsMaximal.isPrime' /-
-- see Note [lower instance priority]
instance (priority := 100) IsMaximal.isPrime' (I : Ideal α) : ∀ [H : I.IsMaximal], I.IsPrime :=
  IsMaximal.isPrime
#align ideal.is_maximal.is_prime' Ideal.IsMaximal.isPrime'
-/

/- warning: ideal.span_singleton_lt_span_singleton -> Ideal.span_singleton_lt_span_singleton is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : CommRing.{u1} β] [_inst_3 : IsDomain.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))] {x : β} {y : β}, Iff (LT.lt.{u1} (Ideal.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))) (Preorder.toLT.{u1} (Ideal.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))) β (Submodule.setLike.{u1, u1} β β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))))) (Semiring.toModule.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))))))) (Ideal.span.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2)) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.hasSingleton.{u1} β) x)) (Ideal.span.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2)) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.hasSingleton.{u1} β) y))) (DvdNotUnit.{u1} β (CommSemiring.toCommMonoidWithZero.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2)) y x)
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : CommRing.{u1} β] [_inst_3 : IsDomain.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))] {x : β} {y : β}, Iff (LT.lt.{u1} (Ideal.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))) (Preorder.toLT.{u1} (Ideal.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))) (Submodule.completeLattice.{u1, u1} β β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))))) (Semiring.toModule.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2)))))))) (Ideal.span.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2)) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) x)) (Ideal.span.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2)) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) y))) (DvdNotUnit.{u1} β (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} β (IsDomain.toCancelCommMonoidWithZero.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2) _inst_3)) y x)
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_lt_span_singleton Ideal.span_singleton_lt_span_singletonₓ'. -/
theorem span_singleton_lt_span_singleton [CommRing β] [IsDomain β] {x y : β} :
    span ({x} : Set β) < span ({y} : Set β) ↔ DvdNotUnit y x := by
  rw [lt_iff_le_not_le, span_singleton_le_span_singleton, span_singleton_le_span_singleton,
    dvd_and_not_dvd_iff]
#align ideal.span_singleton_lt_span_singleton Ideal.span_singleton_lt_span_singleton

/- warning: ideal.factors_decreasing -> Ideal.factors_decreasing is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : CommRing.{u1} β] [_inst_3 : IsDomain.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))] (b₁ : β) (b₂ : β), (Ne.{succ u1} β b₁ (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β (CommRing.toRing.{u1} β _inst_2)))))))))) -> (Not (IsUnit.{u1} β (Ring.toMonoid.{u1} β (CommRing.toRing.{u1} β _inst_2)) b₂)) -> (LT.lt.{u1} (Ideal.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))) (Preorder.toLT.{u1} (Ideal.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))) β (Submodule.setLike.{u1, u1} β β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))))) (Semiring.toModule.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2))))))) (Ideal.span.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2)) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.hasSingleton.{u1} β) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (Distrib.toHasMul.{u1} β (Ring.toDistrib.{u1} β (CommRing.toRing.{u1} β _inst_2)))) b₁ b₂))) (Ideal.span.{u1} β (Ring.toSemiring.{u1} β (CommRing.toRing.{u1} β _inst_2)) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.hasSingleton.{u1} β) b₁)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : CommRing.{u1} β] [_inst_3 : IsDomain.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))] (b₁ : β) (b₂ : β), (Ne.{succ u1} β b₁ (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} β (IsDomain.toCancelCommMonoidWithZero.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2) _inst_3)))))) -> (Not (IsUnit.{u1} β (MonoidWithZero.toMonoid.{u1} β (Semiring.toMonoidWithZero.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2)))) b₂)) -> (LT.lt.{u1} (Ideal.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))) (Preorder.toLT.{u1} (Ideal.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))) (Submodule.completeLattice.{u1, u1} β β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2))))) (Semiring.toModule.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2)))))))) (Ideal.span.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2)) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (NonUnitalNonAssocRing.toMul.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β (CommRing.toRing.{u1} β _inst_2))))) b₁ b₂))) (Ideal.span.{u1} β (CommSemiring.toSemiring.{u1} β (CommRing.toCommSemiring.{u1} β _inst_2)) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b₁)))
Case conversion may be inaccurate. Consider using '#align ideal.factors_decreasing Ideal.factors_decreasingₓ'. -/
theorem factors_decreasing [CommRing β] [IsDomain β] (b₁ b₂ : β) (h₁ : b₁ ≠ 0) (h₂ : ¬IsUnit b₂) :
    span ({b₁ * b₂} : Set β) < span {b₁} :=
  lt_of_le_not_le
    (Ideal.span_le.2 <| singleton_subset_iff.2 <| Ideal.mem_span_singleton.2 ⟨b₂, rfl⟩) fun h =>
    h₂ <|
      isUnit_of_dvd_one _ <|
        (mul_dvd_mul_iff_left h₁).1 <| by rwa [mul_one, ← Ideal.span_singleton_le_span_singleton]
#align ideal.factors_decreasing Ideal.factors_decreasing

variable (b)

/- warning: ideal.mul_mem_right -> Ideal.mul_mem_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} (b : α) [_inst_1 : CommSemiring.{u1} α] (I : Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)), (Membership.Mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) a I) -> (Membership.Mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) a b) I)
but is expected to have type
  forall {α : Type.{u1}} {a : α} (b : α) [_inst_1 : CommSemiring.{u1} α] (I : Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)), (Membership.mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) a I) -> (Membership.mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) a b) I)
Case conversion may be inaccurate. Consider using '#align ideal.mul_mem_right Ideal.mul_mem_rightₓ'. -/
theorem mul_mem_right (h : a ∈ I) : a * b ∈ I :=
  mul_comm b a ▸ I.mul_mem_left b h
#align ideal.mul_mem_right Ideal.mul_mem_right

variable {b}

#print Ideal.pow_mem_of_mem /-
theorem pow_mem_of_mem (ha : a ∈ I) (n : ℕ) (hn : 0 < n) : a ^ n ∈ I :=
  Nat.casesOn n (Not.elim (by decide))
    (fun m hm => (pow_succ a m).symm ▸ I.mul_mem_right (a ^ m) ha) hn
#align ideal.pow_mem_of_mem Ideal.pow_mem_of_mem
-/

/- warning: ideal.is_prime.mul_mem_iff_mem_or_mem -> Ideal.IsPrime.mul_mem_iff_mem_or_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {I : Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)}, (Ideal.IsPrime.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) I) -> (forall {x : α} {y : α}, Iff (Membership.Mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))) x y) I) (Or (Membership.Mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) x I) (Membership.Mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) y I)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {I : Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)}, (Ideal.IsPrime.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) I) -> (forall {x : α} {y : α}, Iff (Membership.mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) x y) I) (Or (Membership.mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) x I) (Membership.mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) y I)))
Case conversion may be inaccurate. Consider using '#align ideal.is_prime.mul_mem_iff_mem_or_mem Ideal.IsPrime.mul_mem_iff_mem_or_memₓ'. -/
theorem IsPrime.mul_mem_iff_mem_or_mem {I : Ideal α} (hI : I.IsPrime) :
    ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ I := fun x y =>
  ⟨hI.mem_or_mem, by
    rintro (h | h)
    exacts[I.mul_mem_right y h, I.mul_mem_left x h]⟩
#align ideal.is_prime.mul_mem_iff_mem_or_mem Ideal.IsPrime.mul_mem_iff_mem_or_mem

#print Ideal.IsPrime.pow_mem_iff_mem /-
theorem IsPrime.pow_mem_iff_mem {I : Ideal α} (hI : I.IsPrime) {r : α} (n : ℕ) (hn : 0 < n) :
    r ^ n ∈ I ↔ r ∈ I :=
  ⟨hI.mem_of_pow_mem n, fun hr => I.pow_mem_of_mem hr n hn⟩
#align ideal.is_prime.pow_mem_iff_mem Ideal.IsPrime.pow_mem_iff_mem
-/

/- warning: ideal.pow_multiset_sum_mem_span_pow -> Ideal.pow_multiset_sum_mem_span_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] (s : Multiset.{u1} α) (n : Nat), Membership.Mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (Multiset.sum.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => Classical.propDecidable (Eq.{succ u1} α a b)) (Multiset.map.{u1, u1} α α (fun (x : α) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) x (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] (s : Multiset.{u1} α) (n : Nat), Membership.mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) α (instHPow.{u1, 0} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (Multiset.sum.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) s) (HAdd.hAdd.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) (instHAdd.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) instAddNat) (HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) Nat ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) (instHMul.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) instMulNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) n) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) 1 (instOfNatNat 1)))) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Finset.toSet.{u1} α (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => Classical.propDecidable (Eq.{succ u1} α a b)) (Multiset.map.{u1, u1} α α (fun (x : α) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) x (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) s))))
Case conversion may be inaccurate. Consider using '#align ideal.pow_multiset_sum_mem_span_pow Ideal.pow_multiset_sum_mem_span_powₓ'. -/
theorem pow_multiset_sum_mem_span_pow (s : Multiset α) (n : ℕ) :
    s.Sum ^ (s.card * n + 1) ∈ span ((s.map fun x => x ^ (n + 1)).toFinset : Set α) :=
  by
  induction' s using Multiset.induction_on with a s hs
  · simp
  simp only [Finset.coe_insert, Multiset.map_cons, Multiset.toFinset_cons, Multiset.sum_cons,
    Multiset.card_cons, add_pow]
  refine' Submodule.sum_mem _ _
  intro c hc
  rw [mem_span_insert]
  by_cases h : n + 1 ≤ c
  · refine'
      ⟨a ^ (c - (n + 1)) * s.sum ^ ((s.card + 1) * n + 1 - c) * ((s.card + 1) * n + 1).choose c, 0,
        Submodule.zero_mem _, _⟩
    rw [mul_comm _ (a ^ (n + 1))]
    simp_rw [← mul_assoc]
    rw [← pow_add, add_zero, add_tsub_cancel_of_le h]
  · use 0
    simp_rw [MulZeroClass.zero_mul, zero_add]
    refine' ⟨_, _, rfl⟩
    replace h : c ≤ n := nat.lt_succ_iff.mp (not_le.mp h)
    have : (s.card + 1) * n + 1 - c = s.card * n + 1 + (n - c) := by
      rw [add_mul, one_mul, add_assoc, add_comm n 1, ← add_assoc, add_tsub_assoc_of_le h]
    rw [this, pow_add]
    simp_rw [mul_assoc, mul_comm (s.sum ^ (s.card * n + 1)), ← mul_assoc]
    exact mul_mem_left _ _ hs
#align ideal.pow_multiset_sum_mem_span_pow Ideal.pow_multiset_sum_mem_span_pow

/- warning: ideal.sum_pow_mem_span_pow -> Ideal.sum_pow_mem_span_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] {ι : Type.{u2}} (s : Finset.{u2} ι) (f : ι -> α) (n : Nat), Membership.Mem.{u1, u1} α (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (Finset.sum.{u1, u2} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) s (fun (i : ι) => f i)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u2} ι s) n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Set.image.{u2, u1} ι α (fun (i : ι) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) (f i) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : CommSemiring.{u2} α] {ι : Type.{u1}} (s : Finset.{u1} ι) (f : ι -> α) (n : Nat), Membership.mem.{u2, u2} α (Ideal.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) (SetLike.instMembership.{u2, u2} (Ideal.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)) α (Submodule.setLike.{u2, u2} α α (CommSemiring.toSemiring.{u2} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)))) (Semiring.toModule.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)))) (HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (MonoidWithZero.toMonoid.{u2} α (Semiring.toMonoidWithZero.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1))))) (Finset.sum.{u2, u1} α ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} α (Semiring.toNonAssocSemiring.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1)))) s (fun (i : ι) => f i)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u1} ι s) n) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Ideal.span.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1) (Set.image.{u1, u2} ι α (fun (i : ι) => HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (MonoidWithZero.toMonoid.{u2} α (Semiring.toMonoidWithZero.{u2} α (CommSemiring.toSemiring.{u2} α _inst_1))))) (f i) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Finset.toSet.{u1} ι s)))
Case conversion may be inaccurate. Consider using '#align ideal.sum_pow_mem_span_pow Ideal.sum_pow_mem_span_powₓ'. -/
theorem sum_pow_mem_span_pow {ι} (s : Finset ι) (f : ι → α) (n : ℕ) :
    (∑ i in s, f i) ^ (s.card * n + 1) ∈ span ((fun i => f i ^ (n + 1)) '' s) :=
  by
  convert pow_multiset_sum_mem_span_pow (s.1.map f) n
  · rw [Multiset.card_map]
    rfl
  rw [Multiset.map_map, Multiset.toFinset_map, Finset.val_toFinset, Finset.coe_image]
#align ideal.sum_pow_mem_span_pow Ideal.sum_pow_mem_span_pow

/- warning: ideal.span_pow_eq_top -> Ideal.span_pow_eq_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] (s : Set.{u1} α), (Eq.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) s) (Top.top.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Submodule.hasTop.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) -> (forall (n : Nat), Eq.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Set.image.{u1, u1} α α (fun (x : α) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) x n) s)) (Top.top.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Submodule.hasTop.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommSemiring.{u1} α] (s : Set.{u1} α), (Eq.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) s) (Top.top.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Submodule.instTopSubmodule.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) -> (forall (n : Nat), Eq.{succ u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Ideal.span.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1) (Set.image.{u1, u1} α α (fun (x : α) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1))))) x n) s)) (Top.top.{u1} (Ideal.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)) (Submodule.instTopSubmodule.{u1, u1} α α (CommSemiring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (CommSemiring.toSemiring.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ideal.span_pow_eq_top Ideal.span_pow_eq_topₓ'. -/
theorem span_pow_eq_top (s : Set α) (hs : span s = ⊤) (n : ℕ) : span ((fun x => x ^ n) '' s) = ⊤ :=
  by
  rw [eq_top_iff_one]
  cases n
  · obtain rfl | ⟨x, hx⟩ := eq_empty_or_nonempty s
    · rw [Set.image_empty, hs]
      trivial
    · exact subset_span ⟨_, hx, pow_zero _⟩
  rw [eq_top_iff_one, span, Finsupp.mem_span_iff_total] at hs
  rcases hs with ⟨f, hf⟩
  change (f.support.sum fun a => f a * a) = 1 at hf
  have := sum_pow_mem_span_pow f.support (fun a => f a * a) n
  rw [hf, one_pow] at this
  refine' span_le.mpr _ this
  rintro _ hx
  simp_rw [Finset.mem_coe, Set.mem_image] at hx
  rcases hx with ⟨x, hx, rfl⟩
  have : span ({x ^ (n + 1)} : Set α) ≤ span ((fun x : α => x ^ (n + 1)) '' s) :=
    by
    rw [span_le, Set.singleton_subset_iff]
    exact subset_span ⟨x, x.prop, rfl⟩
  refine' this _
  rw [mul_pow, mem_span_singleton]
  exact ⟨f x ^ (n + 1), mul_comm _ _⟩
#align ideal.span_pow_eq_top Ideal.span_pow_eq_top

end Ideal

end CommSemiring

section Ring

namespace Ideal

variable [Ring α] (I : Ideal α) {a b : α}

/- warning: ideal.neg_mem_iff -> Ideal.neg_mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (I : Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) {a : α}, Iff (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1))))) a) I) (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) a I)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (I : Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) {a : α}, Iff (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Neg.neg.{u1} α (Ring.toNeg.{u1} α _inst_1) a) I) (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) a I)
Case conversion may be inaccurate. Consider using '#align ideal.neg_mem_iff Ideal.neg_mem_iffₓ'. -/
protected theorem neg_mem_iff : -a ∈ I ↔ a ∈ I :=
  neg_mem_iff
#align ideal.neg_mem_iff Ideal.neg_mem_iff

/- warning: ideal.add_mem_iff_left -> Ideal.add_mem_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (I : Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) b I) -> (Iff (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a b) I) (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) a I))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (I : Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) {a : α} {b : α}, (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) b I) -> (Iff (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a b) I) (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) a I))
Case conversion may be inaccurate. Consider using '#align ideal.add_mem_iff_left Ideal.add_mem_iff_leftₓ'. -/
protected theorem add_mem_iff_left : b ∈ I → (a + b ∈ I ↔ a ∈ I) :=
  I.add_mem_iff_left
#align ideal.add_mem_iff_left Ideal.add_mem_iff_left

/- warning: ideal.add_mem_iff_right -> Ideal.add_mem_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (I : Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) a I) -> (Iff (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a b) I) (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) b I))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (I : Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) {a : α} {b : α}, (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) a I) -> (Iff (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a b) I) (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) b I))
Case conversion may be inaccurate. Consider using '#align ideal.add_mem_iff_right Ideal.add_mem_iff_rightₓ'. -/
protected theorem add_mem_iff_right : a ∈ I → (a + b ∈ I ↔ b ∈ I) :=
  I.add_mem_iff_right
#align ideal.add_mem_iff_right Ideal.add_mem_iff_right

/- warning: ideal.sub_mem -> Ideal.sub_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (I : Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) {a : α} {b : α}, (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) a I) -> (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) b I) -> (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1)))))) a b) I)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (I : Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) {a : α} {b : α}, (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) a I) -> (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) b I) -> (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (Ring.toSub.{u1} α _inst_1)) a b) I)
Case conversion may be inaccurate. Consider using '#align ideal.sub_mem Ideal.sub_memₓ'. -/
protected theorem sub_mem : a ∈ I → b ∈ I → a - b ∈ I :=
  sub_mem
#align ideal.sub_mem Ideal.sub_mem

/- warning: ideal.mem_span_insert' -> Ideal.mem_span_insert' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, Iff (Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) x (Ideal.span.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) y s))) (Exists.{succ u1} α (fun (a : α) => Membership.Mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.hasMem.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a y)) (Ideal.span.{u1} α (Ring.toSemiring.{u1} α _inst_1) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {s : Set.{u1} α} {x : α} {y : α}, Iff (Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) x (Ideal.span.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) y s))) (Exists.{succ u1} α (fun (a : α) => Membership.mem.{u1, u1} α (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (SetLike.instMembership.{u1, u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) α (Submodule.setLike.{u1, u1} α α (Ring.toSemiring.{u1} α _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (Semiring.toModule.{u1} α (Ring.toSemiring.{u1} α _inst_1)))) (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))) a y)) (Ideal.span.{u1} α (Ring.toSemiring.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align ideal.mem_span_insert' Ideal.mem_span_insert'ₓ'. -/
theorem mem_span_insert' {s : Set α} {x y} : x ∈ span (insert y s) ↔ ∃ a, x + a * y ∈ span s :=
  Submodule.mem_span_insert'
#align ideal.mem_span_insert' Ideal.mem_span_insert'

/- warning: ideal.span_singleton_neg -> Ideal.span_singleton_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (x : α), Eq.{succ u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (Ideal.span.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1))))) x))) (Ideal.span.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] (x : α), Eq.{succ u1} (Ideal.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (Ideal.span.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Neg.neg.{u1} α (Ring.toNeg.{u1} α _inst_1) x))) (Ideal.span.{u1} α (Ring.toSemiring.{u1} α _inst_1) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x))
Case conversion may be inaccurate. Consider using '#align ideal.span_singleton_neg Ideal.span_singleton_negₓ'. -/
@[simp]
theorem span_singleton_neg (x : α) : (span {-x} : Ideal α) = span {x} :=
  by
  ext
  simp only [mem_span_singleton']
  exact ⟨fun ⟨y, h⟩ => ⟨-y, h ▸ neg_mul_comm y x⟩, fun ⟨y, h⟩ => ⟨-y, h ▸ neg_mul_neg y x⟩⟩
#align ideal.span_singleton_neg Ideal.span_singleton_neg

end Ideal

end Ring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

/- warning: ideal.eq_bot_or_top -> Ideal.eq_bot_or_top is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionSemiring.{u1} K] (I : Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)), Or (Eq.{succ u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) I (Bot.bot.{u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) (Submodule.hasBot.{u1, u1} K K (DivisionSemiring.toSemiring.{u1} K _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)))) (Semiring.toModule.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1))))) (Eq.{succ u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) I (Top.top.{u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) (Submodule.hasTop.{u1, u1} K K (DivisionSemiring.toSemiring.{u1} K _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)))) (Semiring.toModule.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionSemiring.{u1} K] (I : Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)), Or (Eq.{succ u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) I (Bot.bot.{u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) (Submodule.instBotSubmodule.{u1, u1} K K (DivisionSemiring.toSemiring.{u1} K _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)))) (Semiring.toModule.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1))))) (Eq.{succ u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) I (Top.top.{u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) (Submodule.instTopSubmodule.{u1, u1} K K (DivisionSemiring.toSemiring.{u1} K _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)))) (Semiring.toModule.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ideal.eq_bot_or_top Ideal.eq_bot_or_topₓ'. -/
/-- All ideals in a division (semi)ring are trivial. -/
theorem eq_bot_or_top : I = ⊥ ∨ I = ⊤ :=
  by
  rw [or_iff_not_imp_right]
  change _ ≠ _ → _
  rw [Ideal.ne_top_iff_one]
  intro h1
  rw [eq_bot_iff]
  intro r hr
  by_cases H : r = 0; · simpa
  simpa [H, h1] using I.mul_mem_left r⁻¹ hr
#align ideal.eq_bot_or_top Ideal.eq_bot_or_top

/-- Ideals of a `division_semiring` are a simple order. Thanks to the way abbreviations work,
this automatically gives a `is_simple_module K` instance. -/
instance : IsSimpleOrder (Ideal K) :=
  ⟨eq_bot_or_top⟩

/- warning: ideal.eq_bot_of_prime -> Ideal.eq_bot_of_prime is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionSemiring.{u1} K] (I : Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) [h : Ideal.IsPrime.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1) I], Eq.{succ u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) I (Bot.bot.{u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) (Submodule.hasBot.{u1, u1} K K (DivisionSemiring.toSemiring.{u1} K _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)))) (Semiring.toModule.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionSemiring.{u1} K] (I : Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) [h : Ideal.IsPrime.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1) I], Eq.{succ u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) I (Bot.bot.{u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) (Submodule.instBotSubmodule.{u1, u1} K K (DivisionSemiring.toSemiring.{u1} K _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)))) (Semiring.toModule.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1))))
Case conversion may be inaccurate. Consider using '#align ideal.eq_bot_of_prime Ideal.eq_bot_of_primeₓ'. -/
theorem eq_bot_of_prime [h : I.IsPrime] : I = ⊥ :=
  or_iff_not_imp_right.mp I.eq_bot_or_top h.1
#align ideal.eq_bot_of_prime Ideal.eq_bot_of_prime

/- warning: ideal.bot_is_maximal -> Ideal.bot_isMaximal is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionSemiring.{u1} K], Ideal.IsMaximal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1) (Bot.bot.{u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) (Submodule.hasBot.{u1, u1} K K (DivisionSemiring.toSemiring.{u1} K _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)))) (Semiring.toModule.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionSemiring.{u1} K], Ideal.IsMaximal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1) (Bot.bot.{u1} (Ideal.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)) (Submodule.instBotSubmodule.{u1, u1} K K (DivisionSemiring.toSemiring.{u1} K _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} K (Semiring.toNonAssocSemiring.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1)))) (Semiring.toModule.{u1} K (DivisionSemiring.toSemiring.{u1} K _inst_1))))
Case conversion may be inaccurate. Consider using '#align ideal.bot_is_maximal Ideal.bot_isMaximalₓ'. -/
theorem bot_isMaximal : IsMaximal (⊥ : Ideal K) :=
  ⟨⟨fun h => absurd ((eq_top_iff_one (⊤ : Ideal K)).mp rfl) (by rw [← h] <;> simp), fun I hI =>
      or_iff_not_imp_left.mp (eq_bot_or_top I) (ne_of_gt hI)⟩⟩
#align ideal.bot_is_maximal Ideal.bot_isMaximal

end Ideal

end DivisionSemiring

section CommRing

namespace Ideal

/- warning: ideal.mul_sub_mul_mem -> Ideal.mul_sub_mul_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) {a : R} {b : R} {c : R} {d : R}, (Membership.Mem.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) a b) I) -> (Membership.Mem.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) c d) I) -> (Membership.Mem.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) a c) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (CommRing.toRing.{u1} R _inst_1)))) b d)) I)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (I : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) {a : R} {b : R} {c : R} {d : R}, (Membership.mem.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_1))) a b) I) -> (Membership.mem.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_1))) c d) I) -> (Membership.mem.{u1, u1} R (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (CommRing.toRing.{u1} R _inst_1))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) a c) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))) b d)) I)
Case conversion may be inaccurate. Consider using '#align ideal.mul_sub_mul_mem Ideal.mul_sub_mul_memₓ'. -/
theorem mul_sub_mul_mem {R : Type _} [CommRing R] (I : Ideal R) {a b c d : R} (h1 : a - b ∈ I)
    (h2 : c - d ∈ I) : a * c - b * d ∈ I :=
  by
  rw [show a * c - b * d = (a - b) * c + b * (c - d)
      by
      rw [sub_mul, mul_sub]
      abel]
  exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)
#align ideal.mul_sub_mul_mem Ideal.mul_sub_mul_mem

end Ideal

end CommRing

-- TODO: consider moving the lemmas below out of the `ring` namespace since they are
-- about `comm_semiring`s.
namespace Ring

variable {R : Type _} [CommSemiring R]

/- warning: ring.exists_not_is_unit_of_not_is_field -> Ring.exists_not_isUnit_of_not_isField is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], (Not (IsField.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) -> (Exists.{succ u1} R (fun (x : R) => Exists.{0} (Ne.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))) (fun (H : Ne.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))))) => Not (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], (Not (IsField.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) -> (Exists.{succ u1} R (fun (x : R) => Exists.{0} (Ne.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1))))) (fun (H : Ne.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R _inst_1))))) => Not (IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) x))))
Case conversion may be inaccurate. Consider using '#align ring.exists_not_is_unit_of_not_is_field Ring.exists_not_isUnit_of_not_isFieldₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ≠ » (0 : R)) -/
theorem exists_not_isUnit_of_not_isField [Nontrivial R] (hf : ¬IsField R) :
    ∃ (x : _)(_ : x ≠ (0 : R)), ¬IsUnit x :=
  by
  have : ¬_ := fun h => hf ⟨exists_pair_ne R, mul_comm, h⟩
  simp_rw [isUnit_iff_exists_inv]
  push_neg  at this⊢
  obtain ⟨x, hx, not_unit⟩ := this
  exact ⟨x, hx, not_unit⟩
#align ring.exists_not_is_unit_of_not_is_field Ring.exists_not_isUnit_of_not_isField

/- warning: ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top -> Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Iff (Not (IsField.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Exists.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (fun (I : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) => And (LT.lt.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Preorder.toLT.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (Bot.bot.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.hasBot.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) I) (LT.lt.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Preorder.toLT.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) I (Top.top.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.hasTop.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Iff (Not (IsField.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Exists.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (fun (I : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) => And (LT.lt.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Preorder.toLT.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))) (Bot.bot.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.instBotSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) I) (LT.lt.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Preorder.toLT.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))) I (Top.top.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.instTopSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_topₓ'. -/
theorem not_isField_iff_exists_ideal_bot_lt_and_lt_top [Nontrivial R] :
    ¬IsField R ↔ ∃ I : Ideal R, ⊥ < I ∧ I < ⊤ :=
  by
  constructor
  · intro h
    obtain ⟨x, nz, nu⟩ := exists_not_is_unit_of_not_is_field h
    use Ideal.span {x}
    rw [bot_lt_iff_ne_bot, lt_top_iff_ne_top]
    exact ⟨mt ideal.span_singleton_eq_bot.mp nz, mt ideal.span_singleton_eq_top.mp nu⟩
  · rintro ⟨I, bot_lt, lt_top⟩ hf
    obtain ⟨x, mem, ne_zero⟩ := SetLike.exists_of_lt bot_lt
    rw [Submodule.mem_bot] at ne_zero
    obtain ⟨y, hy⟩ := hf.mul_inv_cancel NeZero
    rw [lt_top_iff_ne_top, Ne.def, Ideal.eq_top_iff_one, ← hy] at lt_top
    exact lt_top (I.mul_mem_right _ mem)
#align ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top

/- warning: ring.not_is_field_iff_exists_prime -> Ring.not_isField_iff_exists_prime is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Iff (Not (IsField.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Exists.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (fun (p : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) => And (Ne.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) p (Bot.bot.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.hasBot.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Ideal.IsPrime.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) p)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R], Iff (Not (IsField.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Exists.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (fun (p : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) => And (Ne.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) p (Bot.bot.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.instBotSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Ideal.IsPrime.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) p)))
Case conversion may be inaccurate. Consider using '#align ring.not_is_field_iff_exists_prime Ring.not_isField_iff_exists_primeₓ'. -/
theorem not_isField_iff_exists_prime [Nontrivial R] :
    ¬IsField R ↔ ∃ p : Ideal R, p ≠ ⊥ ∧ p.IsPrime :=
  not_isField_iff_exists_ideal_bot_lt_and_lt_top.trans
    ⟨fun ⟨I, bot_lt, lt_top⟩ =>
      let ⟨p, hp, le_p⟩ := I.exists_le_maximal (lt_top_iff_ne_top.mp lt_top)
      ⟨p, bot_lt_iff_ne_bot.mp (lt_of_lt_of_le bot_lt le_p), hp.IsPrime⟩,
      fun ⟨p, ne_bot, Prime⟩ => ⟨p, bot_lt_iff_ne_bot.mpr ne_bot, lt_top_iff_ne_top.mpr Prime.1⟩⟩
#align ring.not_is_field_iff_exists_prime Ring.not_isField_iff_exists_prime

/- warning: ring.is_field_iff_is_simple_order_ideal -> Ring.isField_iff_isSimpleOrder_ideal is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R], Iff (IsField.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (IsSimpleOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Preorder.toLE.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) R (Submodule.setLike.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (CompleteLattice.toBoundedOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R], Iff (IsField.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (IsSimpleOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Preorder.toLE.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))))) (CompleteLattice.toBoundedOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ring.is_field_iff_is_simple_order_ideal Ring.isField_iff_isSimpleOrder_idealₓ'. -/
/-- Also see `ideal.is_simple_order` for the forward direction as an instance when `R` is a
division (semi)ring. 

This result actually holds for all division semirings, but we lack the predicate to state it. -/
theorem isField_iff_isSimpleOrder_ideal : IsField R ↔ IsSimpleOrder (Ideal R) :=
  by
  cases subsingleton_or_nontrivial R
  ·
    exact
      ⟨fun h => (not_isField_of_subsingleton _ h).elim, fun h =>
        (false_of_nontrivial_of_subsingleton <| Ideal R).elim⟩
  rw [← not_iff_not, Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top, ← not_iff_not]
  push_neg
  simp_rw [lt_top_iff_ne_top, bot_lt_iff_ne_bot, ← or_iff_not_imp_left, not_ne_iff]
  exact ⟨fun h => ⟨h⟩, fun h => h.2⟩
#align ring.is_field_iff_is_simple_order_ideal Ring.isField_iff_isSimpleOrder_ideal

/- warning: ring.ne_bot_of_is_maximal_of_not_is_field -> Ring.ne_bot_of_isMaximal_of_not_isField is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] {M : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)}, (Ideal.IsMaximal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) M) -> (Not (IsField.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) -> (Ne.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) M (Bot.bot.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.hasBot.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] {M : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)}, (Ideal.IsMaximal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1) M) -> (Not (IsField.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) -> (Ne.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) M (Bot.bot.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.instBotSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ring.ne_bot_of_is_maximal_of_not_is_field Ring.ne_bot_of_isMaximal_of_not_isFieldₓ'. -/
/-- When a ring is not a field, the maximal ideals are nontrivial. -/
theorem ne_bot_of_isMaximal_of_not_isField [Nontrivial R] {M : Ideal R} (max : M.IsMaximal)
    (not_field : ¬IsField R) : M ≠ ⊥ := by
  rintro h
  rw [h] at max
  rcases max with ⟨⟨h1, h2⟩⟩
  obtain ⟨I, hIbot, hItop⟩ := not_is_field_iff_exists_ideal_bot_lt_and_lt_top.mp not_field
  exact ne_of_lt hItop (h2 I hIbot)
#align ring.ne_bot_of_is_maximal_of_not_is_field Ring.ne_bot_of_isMaximal_of_not_isField

end Ring

namespace Ideal

variable {R : Type u} [CommRing R] [Nontrivial R]

/- warning: ideal.bot_lt_of_maximal -> Ideal.bot_lt_of_maximal is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Nontrivial.{u1} R] (M : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) [hm : Ideal.IsMaximal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) M], (Not (IsField.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) -> (LT.lt.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Preorder.toLT.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (Bot.bot.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Submodule.hasBot.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) M)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : Nontrivial.{u1} R] (M : Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) [hm : Ideal.IsMaximal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) M], (Not (IsField.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) -> (LT.lt.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Preorder.toLT.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))))) (Bot.bot.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Submodule.instBotSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) M)
Case conversion may be inaccurate. Consider using '#align ideal.bot_lt_of_maximal Ideal.bot_lt_of_maximalₓ'. -/
theorem bot_lt_of_maximal (M : Ideal R) [hm : M.IsMaximal] (non_field : ¬IsField R) : ⊥ < M :=
  by
  rcases Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.1 non_field with ⟨I, Ibot, Itop⟩
  constructor; · simp
  intro mle
  apply @irrefl _ (· < ·) _ (⊤ : Ideal R)
  have : M = ⊥ := eq_bot_iff.mpr mle
  rw [this] at *
  rwa [hm.1.2 I Ibot] at Itop
#align ideal.bot_lt_of_maximal Ideal.bot_lt_of_maximal

end Ideal

variable {a b : α}

#print nonunits /-
/-- The set of non-invertible elements of a monoid. -/
def nonunits (α : Type u) [Monoid α] : Set α :=
  { a | ¬IsUnit a }
#align nonunits nonunits
-/

#print mem_nonunits_iff /-
@[simp]
theorem mem_nonunits_iff [Monoid α] : a ∈ nonunits α ↔ ¬IsUnit a :=
  Iff.rfl
#align mem_nonunits_iff mem_nonunits_iff
-/

/- warning: mul_mem_nonunits_right -> mul_mem_nonunits_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {b : α} [_inst_1 : CommMonoid.{u1} α], (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b (nonunits.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (nonunits.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {b : α} [_inst_1 : CommMonoid.{u1} α], (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b (nonunits.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (nonunits.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align mul_mem_nonunits_right mul_mem_nonunits_rightₓ'. -/
theorem mul_mem_nonunits_right [CommMonoid α] : b ∈ nonunits α → a * b ∈ nonunits α :=
  mt isUnit_of_mul_isUnit_right
#align mul_mem_nonunits_right mul_mem_nonunits_right

/- warning: mul_mem_nonunits_left -> mul_mem_nonunits_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {b : α} [_inst_1 : CommMonoid.{u1} α], (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (nonunits.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (nonunits.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {b : α} [_inst_1 : CommMonoid.{u1} α], (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (nonunits.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (nonunits.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align mul_mem_nonunits_left mul_mem_nonunits_leftₓ'. -/
theorem mul_mem_nonunits_left [CommMonoid α] : a ∈ nonunits α → a * b ∈ nonunits α :=
  mt isUnit_of_mul_isUnit_left
#align mul_mem_nonunits_left mul_mem_nonunits_left

/- warning: zero_mem_nonunits -> zero_mem_nonunits is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) (nonunits.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))) (Ne.{succ u1} α (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α], Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))) (nonunits.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))) (Ne.{succ u1} α (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align zero_mem_nonunits zero_mem_nonunitsₓ'. -/
theorem zero_mem_nonunits [Semiring α] : 0 ∈ nonunits α ↔ (0 : α) ≠ 1 :=
  not_congr isUnit_zero_iff
#align zero_mem_nonunits zero_mem_nonunits

/- warning: one_not_mem_nonunits -> one_not_mem_nonunits is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))) (nonunits.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))) (nonunits.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align one_not_mem_nonunits one_not_mem_nonunitsₓ'. -/
@[simp]
theorem one_not_mem_nonunits [Monoid α] : (1 : α) ∉ nonunits α :=
  not_not_intro isUnit_one
#align one_not_mem_nonunits one_not_mem_nonunits

/- warning: coe_subset_nonunits -> coe_subset_nonunits is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.hasTop.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ideal.{u1} α _inst_1) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Ideal.{u1} α _inst_1) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Ideal.{u1} α _inst_1) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1))))) I) (nonunits.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {I : Ideal.{u1} α _inst_1}, (Ne.{succ u1} (Ideal.{u1} α _inst_1) I (Top.top.{u1} (Ideal.{u1} α _inst_1) (Submodule.instTopSubmodule.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SetLike.coe.{u1, u1} (Ideal.{u1} α _inst_1) α (Submodule.setLike.{u1, u1} α α _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1))) (Semiring.toModule.{u1} α _inst_1)) I) (nonunits.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align coe_subset_nonunits coe_subset_nonunitsₓ'. -/
theorem coe_subset_nonunits [Semiring α] {I : Ideal α} (h : I ≠ ⊤) : (I : Set α) ⊆ nonunits α :=
  fun x hx hu => h <| I.eq_top_of_isUnit_mem hx hu
#align coe_subset_nonunits coe_subset_nonunits

#print exists_max_ideal_of_mem_nonunits /-
theorem exists_max_ideal_of_mem_nonunits [CommSemiring α] (h : a ∈ nonunits α) :
    ∃ I : Ideal α, I.IsMaximal ∧ a ∈ I :=
  by
  have : Ideal.span ({a} : Set α) ≠ ⊤ := by
    intro H
    rw [Ideal.span_singleton_eq_top] at H
    contradiction
  rcases Ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩
  use I, Imax
  apply H
  apply Ideal.subset_span
  exact Set.mem_singleton a
#align exists_max_ideal_of_mem_nonunits exists_max_ideal_of_mem_nonunits
-/

