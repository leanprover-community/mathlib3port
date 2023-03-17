/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module algebra.monoid_algebra.no_zero_divisors
! leanprover-community/mathlib commit 3e067975886cf5801e597925328c335609511b1a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.MonoidAlgebra.Support

/-!
# Variations on non-zero divisors in `add_monoid_algebra`s

This file studies the interaction between typeclass assumptions on two Types `R` and `A` and
whether `add_monoid_algebra R A` has non-zero zero-divisors.  For some background on related
questions, see [Kaplansky's Conjectures](https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures),
especially the *zero divisor conjecture*.

_Conjecture._
Let `K` be a field, and `G` a torsion-free group. The group ring `K[G]` does not contain
nontrivial zero divisors, that is, it is a domain.

We formalize in this file the well-known result that if `R` is a field and `A` is a left-ordered
group, then `R[A]` contains no non-zero zero-divisors.  Some of these assumptions can be trivially
weakened: below we mention what assumptions are sufficient for the proofs in this file.

##  Main results

* `no_zero_divisors.of_left_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add right cancel semigroup with strictly monotone
  left addition, then `add_monoid_algebra R A` has no non-zero zero-divisors.
* `no_zero_divisors.of_right_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add left cancel semigroup with strictly monotone
  right addition, then `add_monoid_algebra R A` has no non-zero zero-divisors.

The conditions on `A` imposed in `no_zero_divisors.of_left_ordered` are sometimes referred to as
`left-ordered`.
The conditions on `A` imposed in `no_zero_divisors.of_right_ordered` are sometimes referred to as
`right-ordered`.

These conditions are sufficient, but not necessary.  As mentioned above, *Kaplansky's Conjecture*
asserts that `A` being torsion-free may be enough.
-/


namespace AddMonoidAlgebra

open Finsupp

variable {R A : Type _} [Semiring R]

/- warning: add_monoid_algebra.mul_apply_add_eq_mul_of_forall_ne -> AddMonoidAlgebra.mul_apply_add_eq_mul_of_forall_ne is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Add.{u2} A] {f : AddMonoidAlgebra.{u1, u2} R A _inst_1} {g : AddMonoidAlgebra.{u1, u2} R A _inst_1} {a0 : A} {b0 : A}, (forall {a : A} {b : A}, (Membership.Mem.{u2, u2} A (Finset.{u2} A) (Finset.hasMem.{u2} A) a (Finsupp.support.{u2, u1} A R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) f)) -> (Membership.Mem.{u2, u2} A (Finset.{u2} A) (Finset.hasMem.{u2} A) b (Finsupp.support.{u2, u1} A R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) g)) -> (Or (Ne.{succ u2} A a a0) (Ne.{succ u2} A b b0)) -> (Ne.{succ u2} A (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) a b) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) a0 b0))) -> (Eq.{succ u1} R (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (fun (_x : AddMonoidAlgebra.{u1, u2} R A _inst_1) => A -> R) (AddMonoidAlgebra.coeFun.{u1, u2} R A _inst_1) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (instHMul.{max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.hasMul.{u1, u2} R A _inst_1 _inst_2)) f g) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) a0 b0)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (fun (_x : AddMonoidAlgebra.{u1, u2} R A _inst_1) => A -> R) (AddMonoidAlgebra.coeFun.{u1, u2} R A _inst_1) f a0) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (fun (_x : AddMonoidAlgebra.{u1, u2} R A _inst_1) => A -> R) (AddMonoidAlgebra.coeFun.{u1, u2} R A _inst_1) g b0)))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Add.{u2} A] {f : AddMonoidAlgebra.{u1, u2} R A _inst_1} {g : AddMonoidAlgebra.{u1, u2} R A _inst_1} {a0 : A} {b0 : A}, (forall {a : A} {b : A}, (Membership.mem.{u2, u2} A (Finset.{u2} A) (Finset.instMembershipFinset.{u2} A) a (Finsupp.support.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) f)) -> (Membership.mem.{u2, u2} A (Finset.{u2} A) (Finset.instMembershipFinset.{u2} A) b (Finsupp.support.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) g)) -> (Or (Ne.{succ u2} A a a0) (Ne.{succ u2} A b b0)) -> (Ne.{succ u2} A (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) a b) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) a0 b0))) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) a0 b0)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) A (fun (_x : A) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) _x) (Finsupp.funLike.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (instHMul.{max u1 u2} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.hasMul.{u1, u2} R A _inst_1 _inst_2)) f g) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A _inst_2) a0 b0)) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) a0) ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) b0) ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) a0) (instHMul.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) a0) (NonUnitalNonAssocSemiring.toMul.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) a0) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) a0) (Semiring.toNonAssocSemiring.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) a0) _inst_1)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) A (fun (_x : A) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) _x) (Finsupp.funLike.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) f a0) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) A (fun (_x : A) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : A) => R) _x) (Finsupp.funLike.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) g b0)))
Case conversion may be inaccurate. Consider using '#align add_monoid_algebra.mul_apply_add_eq_mul_of_forall_ne AddMonoidAlgebra.mul_apply_add_eq_mul_of_forall_neₓ'. -/
/-- The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
theorem mul_apply_add_eq_mul_of_forall_ne [Add A] {f g : AddMonoidAlgebra R A} {a0 b0 : A}
    (h : ∀ {a b : A}, a ∈ f.support → b ∈ g.support → a ≠ a0 ∨ b ≠ b0 → a + b ≠ a0 + b0) :
    (f * g) (a0 + b0) = f a0 * g b0 := by
  classical
    rw [mul_apply]
    refine' (Finset.sum_eq_single a0 _ _).trans _
    · exact fun b H hb => Finset.sum_eq_zero fun x H1 => if_neg (h H H1 (Or.inl hb))
    · exact fun af0 => by simp [not_mem_support_iff.mp af0]
    · refine' (Finset.sum_eq_single b0 (fun b bg b0 => _) _).trans (if_pos rfl)
      · by_cases af : a0 ∈ f.support
        · exact if_neg (h af bg (Or.inr b0))
        · simp only [not_mem_support_iff.mp af, MulZeroClass.zero_mul, if_t_t]
      · exact fun bf0 => by simp [not_mem_support_iff.mp bf0]
#align add_monoid_algebra.mul_apply_add_eq_mul_of_forall_ne AddMonoidAlgebra.mul_apply_add_eq_mul_of_forall_ne

section LeftOrRightOrderability

/- warning: add_monoid_algebra.left.exists_add_of_mem_support_single_mul -> AddMonoidAlgebra.Left.exists_add_of_mem_support_single_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddLeftCancelSemigroup.{u2} A] {g : AddMonoidAlgebra.{u1, u2} R A _inst_1} (a : A) (x : A), (Membership.Mem.{u2, u2} A (Finset.{u2} A) (Finset.hasMem.{u2} A) x (Finsupp.support.{u2, u1} A R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (instHMul.{max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.hasMul.{u1, u2} R A _inst_1 (AddSemigroup.toHasAdd.{u2} A (AddLeftCancelSemigroup.toAddSemigroup.{u2} A _inst_2)))) (Finsupp.single.{u2, u1} A R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) a (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))))) g))) -> (Exists.{succ u2} A (fun (b : A) => Exists.{0} (Membership.Mem.{u2, u2} A (Finset.{u2} A) (Finset.hasMem.{u2} A) b (Finsupp.support.{u2, u1} A R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) g)) (fun (H : Membership.Mem.{u2, u2} A (Finset.{u2} A) (Finset.hasMem.{u2} A) b (Finsupp.support.{u2, u1} A R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) g)) => Eq.{succ u2} A (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddSemigroup.toHasAdd.{u2} A (AddLeftCancelSemigroup.toAddSemigroup.{u2} A _inst_2))) a b) x)))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddLeftCancelSemigroup.{u2} A] {g : AddMonoidAlgebra.{u1, u2} R A _inst_1} (a : A) (x : A), (Membership.mem.{u2, u2} A (Finset.{u2} A) (Finset.instMembershipFinset.{u2} A) x (Finsupp.support.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (HMul.hMul.{max u2 u1, max u1 u2, max u1 u2} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (instHMul.{max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.hasMul.{u1, u2} R A _inst_1 (AddSemigroup.toAdd.{u2} A (AddLeftCancelSemigroup.toAddSemigroup.{u2} A _inst_2)))) (AddMonoidAlgebra.single.{u1, u2} R A _inst_1 a (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_1)))) g))) -> (Exists.{succ u2} A (fun (b : A) => And (Membership.mem.{u2, u2} A (Finset.{u2} A) (Finset.instMembershipFinset.{u2} A) b (Finsupp.support.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) g)) (Eq.{succ u2} A (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddSemigroup.toAdd.{u2} A (AddLeftCancelSemigroup.toAddSemigroup.{u2} A _inst_2))) a b) x)))
Case conversion may be inaccurate. Consider using '#align add_monoid_algebra.left.exists_add_of_mem_support_single_mul AddMonoidAlgebra.Left.exists_add_of_mem_support_single_mulₓ'. -/
theorem Left.exists_add_of_mem_support_single_mul [AddLeftCancelSemigroup A]
    {g : AddMonoidAlgebra R A} (a x : A)
    (hx : x ∈ (single a 1 * g : AddMonoidAlgebra R A).support) : ∃ b ∈ g.support, a + b = x := by
  rwa [support_single_mul _ _ (fun y => by rw [one_mul] : ∀ y : R, 1 * y = 0 ↔ _),
    Finset.mem_map] at hx
#align add_monoid_algebra.left.exists_add_of_mem_support_single_mul AddMonoidAlgebra.Left.exists_add_of_mem_support_single_mul

/- warning: add_monoid_algebra.right.exists_add_of_mem_support_single_mul -> AddMonoidAlgebra.Right.exists_add_of_mem_support_single_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddRightCancelSemigroup.{u2} A] {f : AddMonoidAlgebra.{u1, u2} R A _inst_1} (b : A) (x : A), (Membership.Mem.{u2, u2} A (Finset.{u2} A) (Finset.hasMem.{u2} A) x (Finsupp.support.{u2, u1} A R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (instHMul.{max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.hasMul.{u1, u2} R A _inst_1 (AddSemigroup.toHasAdd.{u2} A (AddRightCancelSemigroup.toAddSemigroup.{u2} A _inst_2)))) f (Finsupp.single.{u2, u1} A R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) b (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))))) -> (Exists.{succ u2} A (fun (a : A) => Exists.{0} (Membership.Mem.{u2, u2} A (Finset.{u2} A) (Finset.hasMem.{u2} A) a (Finsupp.support.{u2, u1} A R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) f)) (fun (H : Membership.Mem.{u2, u2} A (Finset.{u2} A) (Finset.hasMem.{u2} A) a (Finsupp.support.{u2, u1} A R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) f)) => Eq.{succ u2} A (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddSemigroup.toHasAdd.{u2} A (AddRightCancelSemigroup.toAddSemigroup.{u2} A _inst_2))) a b) x)))
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddRightCancelSemigroup.{u2} A] {f : AddMonoidAlgebra.{u1, u2} R A _inst_1} (b : A) (x : A), (Membership.mem.{u2, u2} A (Finset.{u2} A) (Finset.instMembershipFinset.{u2} A) x (Finsupp.support.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (HMul.hMul.{max u1 u2, max u2 u1, max u1 u2} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.{u1, u2} R A _inst_1) (instHMul.{max u1 u2} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.hasMul.{u1, u2} R A _inst_1 (AddSemigroup.toAdd.{u2} A (AddRightCancelSemigroup.toAddSemigroup.{u2} A _inst_2)))) f (AddMonoidAlgebra.single.{u1, u2} R A _inst_1 b (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_1))))))) -> (Exists.{succ u2} A (fun (a : A) => And (Membership.mem.{u2, u2} A (Finset.{u2} A) (Finset.instMembershipFinset.{u2} A) a (Finsupp.support.{u2, u1} A R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) f)) (Eq.{succ u2} A (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddSemigroup.toAdd.{u2} A (AddRightCancelSemigroup.toAddSemigroup.{u2} A _inst_2))) a b) x)))
Case conversion may be inaccurate. Consider using '#align add_monoid_algebra.right.exists_add_of_mem_support_single_mul AddMonoidAlgebra.Right.exists_add_of_mem_support_single_mulₓ'. -/
theorem Right.exists_add_of_mem_support_single_mul [AddRightCancelSemigroup A]
    {f : AddMonoidAlgebra R A} (b x : A)
    (hx : x ∈ (f * single b 1 : AddMonoidAlgebra R A).support) : ∃ a ∈ f.support, a + b = x := by
  rwa [support_mul_single _ _ (fun y => by rw [mul_one] : ∀ y : R, y * 1 = 0 ↔ _),
    Finset.mem_map] at hx
#align add_monoid_algebra.right.exists_add_of_mem_support_single_mul AddMonoidAlgebra.Right.exists_add_of_mem_support_single_mul

/- warning: add_monoid_algebra.no_zero_divisors.of_left_ordered -> AddMonoidAlgebra.NoZeroDivisors.of_left_ordered is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))] [_inst_3 : AddRightCancelSemigroup.{u2} A] [_inst_4 : LinearOrder.{u2} A] [_inst_5 : CovariantClass.{u2, u2} A A (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddSemigroup.toHasAdd.{u2} A (AddRightCancelSemigroup.toAddSemigroup.{u2} A _inst_3)))) (LT.lt.{u2} A (Preorder.toLT.{u2} A (PartialOrder.toPreorder.{u2} A (SemilatticeInf.toPartialOrder.{u2} A (Lattice.toSemilatticeInf.{u2} A (LinearOrder.toLattice.{u2} A _inst_4))))))], NoZeroDivisors.{max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.hasMul.{u1, u2} R A _inst_1 (AddSemigroup.toHasAdd.{u2} A (AddRightCancelSemigroup.toAddSemigroup.{u2} A _inst_3))) (MulZeroClass.toHasZero.{max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (NonUnitalNonAssocSemiring.toMulZeroClass.{max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.nonUnitalNonAssocSemiring.{u1, u2} R A _inst_1 (AddSemigroup.toHasAdd.{u2} A (AddRightCancelSemigroup.toAddSemigroup.{u2} A _inst_3)))))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : NoZeroDivisors.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1))] [_inst_3 : AddRightCancelSemigroup.{u1} A] [_inst_4 : LinearOrder.{u1} A] [_inst_5 : CovariantClass.{u1, u1} A A (fun (x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.587 : A) (x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.589 : A) => HAdd.hAdd.{u1, u1, u1} A A A (instHAdd.{u1} A (AddSemigroup.toAdd.{u1} A (AddRightCancelSemigroup.toAddSemigroup.{u1} A _inst_3))) x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.587 x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.589) (fun (x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.602 : A) (x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.604 : A) => LT.lt.{u1} A (Preorder.toLT.{u1} A (PartialOrder.toPreorder.{u1} A (SemilatticeInf.toPartialOrder.{u1} A (Lattice.toSemilatticeInf.{u1} A (DistribLattice.toLattice.{u1} A (instDistribLattice.{u1} A _inst_4)))))) x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.602 x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.604)], NoZeroDivisors.{max u1 u2} (AddMonoidAlgebra.{u2, u1} R A _inst_1) (AddMonoidAlgebra.hasMul.{u2, u1} R A _inst_1 (AddSemigroup.toAdd.{u1} A (AddRightCancelSemigroup.toAddSemigroup.{u1} A _inst_3))) (SemigroupWithZero.toZero.{max u2 u1} (AddMonoidAlgebra.{u2, u1} R A _inst_1) (NonUnitalSemiring.toSemigroupWithZero.{max u2 u1} (AddMonoidAlgebra.{u2, u1} R A _inst_1) (AddMonoidAlgebra.nonUnitalSemiring.{u2, u1} R A _inst_1 (AddRightCancelSemigroup.toAddSemigroup.{u1} A _inst_3))))
Case conversion may be inaccurate. Consider using '#align add_monoid_algebra.no_zero_divisors.of_left_ordered AddMonoidAlgebra.NoZeroDivisors.of_left_orderedₓ'. -/
/-- If `R` is a semiring with no non-trivial zero-divisors and `A` is a left-ordered add right
cancel semigroup, then `add_monoid_algebra R A` also contains no non-zero zero-divisors. -/
theorem NoZeroDivisors.of_left_ordered [NoZeroDivisors R] [AddRightCancelSemigroup A]
    [LinearOrder A] [CovariantClass A A (· + ·) (· < ·)] : NoZeroDivisors (AddMonoidAlgebra R A) :=
  ⟨fun f g fg => by
    contrapose! fg
    let gmin : A := g.support.min' (support_nonempty_iff.mpr fg.2)
    refine' support_nonempty_iff.mp _
    obtain ⟨a, ha, H⟩ :=
      right.exists_add_of_mem_support_single_mul gmin
        ((f * single gmin 1 : AddMonoidAlgebra R A).support.min'
          (by rw [support_mul_single] <;> simp [support_nonempty_iff.mpr fg.1]))
        (Finset.min'_mem _ _)
    refine' ⟨a + gmin, mem_support_iff.mpr _⟩
    rw [mul_apply_add_eq_mul_of_forall_ne _]
    · refine' mul_ne_zero _ _
      exacts[mem_support_iff.mp ha, mem_support_iff.mp (Finset.min'_mem _ _)]
    · rw [H]
      rintro b c bf cg (hb | hc) <;> refine' ne_of_gt _
      · refine' lt_of_lt_of_le (_ : _ < b + gmin) _
        · apply Finset.min'_lt_of_mem_erase_min'
          rw [← H]
          apply Finset.mem_erase_of_ne_of_mem
          · simpa only [Ne.def, add_left_inj]
          · rw [support_mul_single _ _ (fun y => by rw [mul_one] : ∀ y : R, y * 1 = 0 ↔ _)]
            simpa only [Finset.mem_map, addRightEmbedding_apply, add_left_inj, exists_prop,
              exists_eq_right]
        · haveI : CovariantClass A A (· + ·) (· ≤ ·) := Add.to_covariantClass_left A
          exact add_le_add_left (Finset.min'_le _ _ cg) _
      · refine' lt_of_le_of_lt (_ : _ ≤ b + gmin) _
        · apply Finset.min'_le
          rw [support_mul_single _ _ (fun y => by rw [mul_one] : ∀ y : R, y * 1 = 0 ↔ _)]
          simp only [bf, Finset.mem_map, addRightEmbedding_apply, add_left_inj, exists_prop,
            exists_eq_right]
        · refine' add_lt_add_left _ _
          exact Finset.min'_lt_of_mem_erase_min' _ _ (finset.mem_erase.mpr ⟨hc, cg⟩)⟩
#align add_monoid_algebra.no_zero_divisors.of_left_ordered AddMonoidAlgebra.NoZeroDivisors.of_left_ordered

/- warning: add_monoid_algebra.no_zero_divisors.of_right_ordered -> AddMonoidAlgebra.NoZeroDivisors.of_right_ordered is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))] [_inst_3 : AddLeftCancelSemigroup.{u2} A] [_inst_4 : LinearOrder.{u2} A] [_inst_5 : CovariantClass.{u2, u2} A A (Function.swap.{succ u2, succ u2, succ u2} A A (fun (ᾰ : A) (ᾰ : A) => A) (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddSemigroup.toHasAdd.{u2} A (AddLeftCancelSemigroup.toAddSemigroup.{u2} A _inst_3))))) (LT.lt.{u2} A (Preorder.toLT.{u2} A (PartialOrder.toPreorder.{u2} A (SemilatticeInf.toPartialOrder.{u2} A (Lattice.toSemilatticeInf.{u2} A (LinearOrder.toLattice.{u2} A _inst_4))))))], NoZeroDivisors.{max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.hasMul.{u1, u2} R A _inst_1 (AddSemigroup.toHasAdd.{u2} A (AddLeftCancelSemigroup.toAddSemigroup.{u2} A _inst_3))) (MulZeroClass.toHasZero.{max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (NonUnitalNonAssocSemiring.toMulZeroClass.{max u2 u1} (AddMonoidAlgebra.{u1, u2} R A _inst_1) (AddMonoidAlgebra.nonUnitalNonAssocSemiring.{u1, u2} R A _inst_1 (AddSemigroup.toHasAdd.{u2} A (AddLeftCancelSemigroup.toAddSemigroup.{u2} A _inst_3)))))
but is expected to have type
  forall {R : Type.{u2}} {A : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : NoZeroDivisors.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1))] [_inst_3 : AddLeftCancelSemigroup.{u1} A] [_inst_4 : LinearOrder.{u1} A] [_inst_5 : CovariantClass.{u1, u1} A A (Function.swap.{succ u1, succ u1, succ u1} A A (fun (ᾰ : A) (ᾰ : A) => A) (fun (x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.1204 : A) (x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.1206 : A) => HAdd.hAdd.{u1, u1, u1} A A A (instHAdd.{u1} A (AddSemigroup.toAdd.{u1} A (AddLeftCancelSemigroup.toAddSemigroup.{u1} A _inst_3))) x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.1204 x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.1206)) (fun (x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.1219 : A) (x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.1221 : A) => LT.lt.{u1} A (Preorder.toLT.{u1} A (PartialOrder.toPreorder.{u1} A (SemilatticeInf.toPartialOrder.{u1} A (Lattice.toSemilatticeInf.{u1} A (DistribLattice.toLattice.{u1} A (instDistribLattice.{u1} A _inst_4)))))) x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.1219 x._@.Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors._hyg.1221)], NoZeroDivisors.{max u1 u2} (AddMonoidAlgebra.{u2, u1} R A _inst_1) (AddMonoidAlgebra.hasMul.{u2, u1} R A _inst_1 (AddSemigroup.toAdd.{u1} A (AddLeftCancelSemigroup.toAddSemigroup.{u1} A _inst_3))) (SemigroupWithZero.toZero.{max u2 u1} (AddMonoidAlgebra.{u2, u1} R A _inst_1) (NonUnitalSemiring.toSemigroupWithZero.{max u2 u1} (AddMonoidAlgebra.{u2, u1} R A _inst_1) (AddMonoidAlgebra.nonUnitalSemiring.{u2, u1} R A _inst_1 (AddLeftCancelSemigroup.toAddSemigroup.{u1} A _inst_3))))
Case conversion may be inaccurate. Consider using '#align add_monoid_algebra.no_zero_divisors.of_right_ordered AddMonoidAlgebra.NoZeroDivisors.of_right_orderedₓ'. -/
/-- If `R` is a semiring with no non-trivial zero-divisors and `A` is a right-ordered add left
cancel semigroup, then `add_monoid_algebra R A` also contains no non-zero zero-divisors. -/
theorem NoZeroDivisors.of_right_ordered [NoZeroDivisors R] [AddLeftCancelSemigroup A]
    [LinearOrder A] [CovariantClass A A (Function.swap (· + ·)) (· < ·)] :
    NoZeroDivisors (AddMonoidAlgebra R A) :=
  ⟨fun f g fg => by
    contrapose! fg
    let fmin : A := f.support.min' (support_nonempty_iff.mpr fg.1)
    refine' support_nonempty_iff.mp _
    obtain ⟨a, ha, H⟩ :=
      left.exists_add_of_mem_support_single_mul fmin
        ((single fmin 1 * g : AddMonoidAlgebra R A).support.min'
          (by rw [support_single_mul] <;> simp [support_nonempty_iff.mpr fg.2]))
        (Finset.min'_mem _ _)
    refine' ⟨fmin + a, mem_support_iff.mpr _⟩
    rw [mul_apply_add_eq_mul_of_forall_ne _]
    · refine' mul_ne_zero _ _
      exacts[mem_support_iff.mp (Finset.min'_mem _ _), mem_support_iff.mp ha]
    · rw [H]
      rintro b c bf cg (hb | hc) <;> refine' ne_of_gt _
      · refine' lt_of_le_of_lt (_ : _ ≤ fmin + c) _
        · apply Finset.min'_le
          rw [support_single_mul _ _ (fun y => by rw [one_mul] : ∀ y : R, 1 * y = 0 ↔ _)]
          simp only [cg, Finset.mem_map, addLeftEmbedding_apply, add_right_inj, exists_prop,
            exists_eq_right]
        · refine' add_lt_add_right _ _
          exact Finset.min'_lt_of_mem_erase_min' _ _ (finset.mem_erase.mpr ⟨hb, bf⟩)
      · refine' lt_of_lt_of_le (_ : _ < fmin + c) _
        · apply Finset.min'_lt_of_mem_erase_min'
          rw [← H]
          apply Finset.mem_erase_of_ne_of_mem
          · simpa only [Ne.def, add_right_inj]
          · rw [support_single_mul _ _ (fun y => by rw [one_mul] : ∀ y : R, 1 * y = 0 ↔ _)]
            simpa only [Finset.mem_map, addLeftEmbedding_apply, add_right_inj, exists_prop,
              exists_eq_right]
        · haveI : CovariantClass A A (Function.swap (· + ·)) (· ≤ ·) :=
            Add.to_covariantClass_right A
          exact add_le_add_right (Finset.min'_le _ _ bf) _⟩
#align add_monoid_algebra.no_zero_divisors.of_right_ordered AddMonoidAlgebra.NoZeroDivisors.of_right_ordered

end LeftOrRightOrderability

end AddMonoidAlgebra

