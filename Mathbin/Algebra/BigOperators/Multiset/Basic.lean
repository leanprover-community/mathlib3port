/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module algebra.big_operators.multiset.basic
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.BigOperators.Basic
import Mathbin.Data.Multiset.Basic

/-!
# Sums and products over multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define products and sums indexed by multisets. This is later used to define products
and sums indexed by finite sets.

## Main declarations

* `multiset.prod`: `s.prod f` is the product of `f i` over all `i ∈ s`. Not to be mistaken with
  the cartesian product `multiset.product`.
* `multiset.sum`: `s.sum f` is the sum of `f i` over all `i ∈ s`.

## Implementation notes

Nov 2022: To speed the Lean 4 port, lemmas requiring extra algebra imports
(`data.list.big_operators.lemmas` rather than `.basic`) have been moved to a separate file,
`algebra.big_operators.multiset.lemmas`.  This split does not need to be permanent.
-/


variable {ι α β γ : Type _}

namespace Multiset

section CommMonoid

variable [CommMonoid α] {s t : Multiset α} {a : α} {m : Multiset ι} {f g : ι → α}

#print Multiset.prod /-
/-- Product of a multiset given a commutative monoid structure on `α`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive
      "Sum of a multiset given a commutative additive monoid structure on `α`.\n  `sum {a, b, c} = a + b + c`"]
def prod : Multiset α → α :=
  foldr (· * ·) (fun x y z => by simp [mul_left_comm]) 1
#align multiset.prod Multiset.prod
#align multiset.sum Multiset.sum
-/

/- warning: multiset.prod_eq_foldr -> Multiset.prod_eq_foldr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 s) (Multiset.foldr.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) (fun (x : α) (y : α) (z : α) => Eq.mpr.{0} (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x z))) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x z))) True) (Eq.trans.{1} Prop (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x z))) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z))) True ((fun (a : α) (a_1 : α) (e_1 : Eq.{succ u1} α a a_1) (ᾰ : α) (ᾰ_1 : α) (e_2 : Eq.{succ u1} α ᾰ ᾰ_1) => congr.{succ u1, 1} α Prop (Eq.{succ u1} α a) (Eq.{succ u1} α a_1) ᾰ ᾰ_1 (congr_arg.{succ u1, succ u1} α (α -> Prop) a a_1 (Eq.{succ u1} α) e_1) e_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (rfl.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (mul_left_comm.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1) y x z)) (propext (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z))) True (eq_self_iff_true.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)))))) trivial) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 s) (Multiset.foldr.{u1, u1} α α (fun (x._@.Mathlib.Algebra.BigOperators.Multiset.Basic._hyg.128 : α) (x._@.Mathlib.Algebra.BigOperators.Multiset.Basic._hyg.130 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.BigOperators.Multiset.Basic._hyg.128 x._@.Mathlib.Algebra.BigOperators.Multiset.Basic._hyg.130) (fun (x : α) (y : α) (z : α) => of_eq_true (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) y (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) x z))) (Eq.trans.{1} Prop (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) y (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) x z))) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) y z))) True (congrArg.{succ u1, 1} α Prop (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) y (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) x z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) y z)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z))) (mul_left_comm.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1) y x z)) (eq_self.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) y z))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) s)
Case conversion may be inaccurate. Consider using '#align multiset.prod_eq_foldr Multiset.prod_eq_foldrₓ'. -/
@[to_additive]
theorem prod_eq_foldr (s : Multiset α) :
    prod s = foldr (· * ·) (fun x y z => by simp [mul_left_comm]) 1 s :=
  rfl
#align multiset.prod_eq_foldr Multiset.prod_eq_foldr
#align multiset.sum_eq_foldr Multiset.sum_eq_foldr

/- warning: multiset.prod_eq_foldl -> Multiset.prod_eq_foldl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 s) (Multiset.foldl.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) (fun (x : α) (y : α) (z : α) => Eq.mpr.{0} (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x z) y)) True (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x z) y)) True) (Eq.trans.{1} Prop (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x z) y)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z)) True ((fun (a : α) (a_1 : α) (e_1 : Eq.{succ u1} α a a_1) (ᾰ : α) (ᾰ_1 : α) (e_2 : Eq.{succ u1} α ᾰ ᾰ_1) => congr.{succ u1, 1} α Prop (Eq.{succ u1} α a) (Eq.{succ u1} α a_1) ᾰ ᾰ_1 (congr_arg.{succ u1, succ u1} α (α -> Prop) a a_1 (Eq.{succ u1} α) e_1) e_2) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (rfl.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x z) y) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (mul_right_comm.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1) x z y)) (propext (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z)) True (eq_self_iff_true.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z))))) trivial) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 s) (Multiset.foldl.{u1, u1} α α (fun (x._@.Mathlib.Algebra.BigOperators.Multiset.Basic._hyg.187 : α) (x._@.Mathlib.Algebra.BigOperators.Multiset.Basic._hyg.189 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.BigOperators.Multiset.Basic._hyg.187 x._@.Mathlib.Algebra.BigOperators.Multiset.Basic._hyg.189) (fun (x : α) (y : α) (z : α) => of_eq_true (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) x z) y)) (Eq.trans.{1} Prop (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) x z) y)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) x y) z)) True (congrArg.{succ u1, 1} α Prop (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) x z) y) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1)))) x y) z) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z)) (mul_right_comm.{u1} α (CommMonoid.toCommSemigroup.{u1} α _inst_1) x z y)) (eq_self.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) x y) z)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) s)
Case conversion may be inaccurate. Consider using '#align multiset.prod_eq_foldl Multiset.prod_eq_foldlₓ'. -/
@[to_additive]
theorem prod_eq_foldl (s : Multiset α) :
    prod s = foldl (· * ·) (fun x y z => by simp [mul_right_comm]) 1 s :=
  (foldr_swap _ _ _ _).trans (by simp [mul_comm])
#align multiset.prod_eq_foldl Multiset.prod_eq_foldl
#align multiset.sum_eq_foldl Multiset.sum_eq_foldl

/- warning: multiset.coe_prod -> Multiset.coe_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (l : List.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) l)) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) l)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (l : List.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (Multiset.ofList.{u1} α l)) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) l)
Case conversion may be inaccurate. Consider using '#align multiset.coe_prod Multiset.coe_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_prod (l : List α) : prod ↑l = l.Prod :=
  prod_eq_foldl _
#align multiset.coe_prod Multiset.coe_prod
#align multiset.coe_sum Multiset.coe_sum

/- warning: multiset.prod_to_list -> Multiset.prod_toList is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (s : Multiset.{u1} α), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Multiset.toList.{u1} α s)) (Multiset.prod.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (s : Multiset.{u1} α), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Multiset.toList.{u1} α s)) (Multiset.prod.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align multiset.prod_to_list Multiset.prod_toListₓ'. -/
@[simp, to_additive]
theorem prod_toList (s : Multiset α) : s.toList.Prod = s.Prod :=
  by
  conv_rhs => rw [← coe_to_list s]
  rw [coe_prod]
#align multiset.prod_to_list Multiset.prod_toList
#align multiset.sum_to_list Multiset.sum_toList

/- warning: multiset.prod_zero -> Multiset.prod_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α], Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (OfNat.mk.{u1} (Multiset.{u1} α) 0 (Zero.zero.{u1} (Multiset.{u1} α) (Multiset.hasZero.{u1} α))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α], Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (OfNat.ofNat.{u1} (Multiset.{u1} α) 0 (Zero.toOfNat0.{u1} (Multiset.{u1} α) (Multiset.instZeroMultiset.{u1} α)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align multiset.prod_zero Multiset.prod_zeroₓ'. -/
@[simp, to_additive]
theorem prod_zero : @prod α _ 0 = 1 :=
  rfl
#align multiset.prod_zero Multiset.prod_zero
#align multiset.sum_zero Multiset.sum_zero

/- warning: multiset.prod_cons -> Multiset.prod_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (Multiset.cons.{u1} α a s)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a (Multiset.prod.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (Multiset.cons.{u1} α a s)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a (Multiset.prod.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align multiset.prod_cons Multiset.prod_consₓ'. -/
@[simp, to_additive]
theorem prod_cons (a : α) (s) : prod (a ::ₘ s) = a * prod s :=
  foldr_cons _ _ _ _ _
#align multiset.prod_cons Multiset.prod_cons
#align multiset.sum_cons Multiset.sum_cons

/- warning: multiset.prod_erase -> Multiset.prod_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {s : Multiset.{u1} α} {a : α} [_inst_2 : DecidableEq.{succ u1} α], (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a (Multiset.prod.{u1} α _inst_1 (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s a))) (Multiset.prod.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {s : Multiset.{u1} α} {a : α} [_inst_2 : DecidableEq.{succ u1} α], (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a (Multiset.prod.{u1} α _inst_1 (Multiset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s a))) (Multiset.prod.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align multiset.prod_erase Multiset.prod_eraseₓ'. -/
@[simp, to_additive]
theorem prod_erase [DecidableEq α] (h : a ∈ s) : a * (s.erase a).Prod = s.Prod := by
  rw [← s.coe_to_list, coe_erase, coe_prod, coe_prod, List.prod_erase (mem_to_list.2 h)]
#align multiset.prod_erase Multiset.prod_erase
#align multiset.sum_erase Multiset.sum_erase

/- warning: multiset.prod_map_erase -> Multiset.prod_map_erase is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] {m : Multiset.{u1} ι} {f : ι -> α} [_inst_2 : DecidableEq.{succ u1} ι] {a : ι}, (Membership.Mem.{u1, u1} ι (Multiset.{u1} ι) (Multiset.hasMem.{u1} ι) a m) -> (Eq.{succ u2} α (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (f a) (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α f (Multiset.erase.{u1} ι (fun (a : ι) (b : ι) => _inst_2 a b) m a)))) (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α f m)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {m : Multiset.{u2} ι} {f : ι -> α} [_inst_2 : DecidableEq.{succ u2} ι] {a : ι}, (Membership.mem.{u2, u2} ι (Multiset.{u2} ι) (Multiset.instMembershipMultiset.{u2} ι) a m) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (f a) (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u2, u1} ι α f (Multiset.erase.{u2} ι (fun (a : ι) (b : ι) => _inst_2 a b) m a)))) (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u2, u1} ι α f m)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_erase Multiset.prod_map_eraseₓ'. -/
@[simp, to_additive]
theorem prod_map_erase [DecidableEq ι] {a : ι} (h : a ∈ m) :
    f a * ((m.erase a).map f).Prod = (m.map f).Prod := by
  rw [← m.coe_to_list, coe_erase, coe_map, coe_map, coe_prod, coe_prod,
    List.prod_map_erase f (mem_to_list.2 h)]
#align multiset.prod_map_erase Multiset.prod_map_erase
#align multiset.sum_map_erase Multiset.sum_map_erase

#print Multiset.prod_singleton /-
@[simp, to_additive]
theorem prod_singleton (a : α) : prod {a} = a := by
  simp only [mul_one, prod_cons, ← cons_zero, eq_self_iff_true, prod_zero]
#align multiset.prod_singleton Multiset.prod_singleton
#align multiset.sum_singleton Multiset.sum_singleton
-/

/- warning: multiset.prod_pair -> Multiset.prod_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.hasInsert.{u1} α) a (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) b))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (Insert.insert.{u1, u1} α (Multiset.{u1} α) (Multiset.instInsertMultiset.{u1} α) a (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) b))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b)
Case conversion may be inaccurate. Consider using '#align multiset.prod_pair Multiset.prod_pairₓ'. -/
@[to_additive]
theorem prod_pair (a b : α) : ({a, b} : Multiset α).Prod = a * b := by
  rw [insert_eq_cons, prod_cons, prod_singleton]
#align multiset.prod_pair Multiset.prod_pair
#align multiset.sum_pair Multiset.sum_pair

/- warning: multiset.prod_add -> Multiset.prod_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) s t)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Multiset.prod.{u1} α _inst_1 s) (Multiset.prod.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (s : Multiset.{u1} α) (t : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) s t)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Multiset.prod.{u1} α _inst_1 s) (Multiset.prod.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align multiset.prod_add Multiset.prod_addₓ'. -/
@[simp, to_additive]
theorem prod_add (s t : Multiset α) : prod (s + t) = prod s * prod t :=
  Quotient.induction_on₂ s t fun l₁ l₂ => by simp
#align multiset.prod_add Multiset.prod_add
#align multiset.sum_add Multiset.sum_add

/- warning: multiset.prod_nsmul -> Multiset.prod_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (m : Multiset.{u1} α) (n : Nat), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n m)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Multiset.prod.{u1} α _inst_1 m) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (m : Multiset.{u1} α) (n : Nat), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n m)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Multiset.prod.{u1} α _inst_1 m) n)
Case conversion may be inaccurate. Consider using '#align multiset.prod_nsmul Multiset.prod_nsmulₓ'. -/
theorem prod_nsmul (m : Multiset α) : ∀ n : ℕ, (n • m).Prod = m.Prod ^ n
  | 0 => by
    rw [zero_nsmul, pow_zero]
    rfl
  | n + 1 => by rw [add_nsmul, one_nsmul, pow_add, pow_one, prod_add, prod_nsmul n]
#align multiset.prod_nsmul Multiset.prod_nsmul

#print Multiset.prod_replicate /-
@[simp, to_additive]
theorem prod_replicate (n : ℕ) (a : α) : (replicate n a).Prod = a ^ n := by
  simp [replicate, List.prod_replicate]
#align multiset.prod_replicate Multiset.prod_replicate
#align multiset.sum_replicate Multiset.sum_replicate
-/

/- warning: multiset.prod_map_eq_pow_single -> Multiset.prod_map_eq_pow_single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] {m : Multiset.{u1} ι} {f : ι -> α} [_inst_2 : DecidableEq.{succ u1} ι] (i : ι), (forall (i' : ι), (Ne.{succ u1} ι i' i) -> (Membership.Mem.{u1, u1} ι (Multiset.{u1} ι) (Multiset.hasMem.{u1} ι) i' m) -> (Eq.{succ u2} α (f i') (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))))))) -> (Eq.{succ u2} α (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α f m)) (HPow.hPow.{u2, 0, u2} α Nat α (instHPow.{u2, 0} α Nat (Monoid.Pow.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (f i) (Multiset.count.{u1} ι (fun (a : ι) (b : ι) => _inst_2 a b) i m)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {m : Multiset.{u2} ι} {f : ι -> α} [_inst_2 : DecidableEq.{succ u2} ι] (i : ι), (forall (i' : ι), (Ne.{succ u2} ι i' i) -> (Membership.mem.{u2, u2} ι (Multiset.{u2} ι) (Multiset.instMembershipMultiset.{u2} ι) i' m) -> (Eq.{succ u1} α (f i') (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u2, u1} ι α f m)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (f i) (Multiset.count.{u2} ι (fun (a : ι) (b : ι) => _inst_2 a b) i m)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_eq_pow_single Multiset.prod_map_eq_pow_singleₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (i' «expr ≠ » i) -/
@[to_additive]
theorem prod_map_eq_pow_single [DecidableEq ι] (i : ι)
    (hf : ∀ (i') (_ : i' ≠ i), i' ∈ m → f i' = 1) : (m.map f).Prod = f i ^ m.count i :=
  by
  induction' m using Quotient.inductionOn with l
  simp [List.prod_map_eq_pow_single i f hf]
#align multiset.prod_map_eq_pow_single Multiset.prod_map_eq_pow_single

/- warning: multiset.prod_eq_pow_single -> Multiset.prod_eq_pow_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {s : Multiset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] (a : α), (forall (a' : α), (Ne.{succ u1} α a' a) -> (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a' s) -> (Eq.{succ u1} α a' (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 s) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {s : Multiset.{u1} α} [_inst_2 : DecidableEq.{succ u1} α] (a : α), (forall (a' : α), (Ne.{succ u1} α a' a) -> (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a' s) -> (Eq.{succ u1} α a' (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 s) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a s)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_eq_pow_single Multiset.prod_eq_pow_singleₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a' «expr ≠ » a) -/
@[to_additive]
theorem prod_eq_pow_single [DecidableEq α] (a : α) (h : ∀ (a') (_ : a' ≠ a), a' ∈ s → a' = 1) :
    s.Prod = a ^ s.count a :=
  by
  induction' s using Quotient.inductionOn with l
  simp [List.prod_eq_pow_single a h]
#align multiset.prod_eq_pow_single Multiset.prod_eq_pow_single

#print Multiset.pow_count /-
@[to_additive]
theorem pow_count [DecidableEq α] (a : α) : a ^ s.count a = (s.filter (Eq a)).Prod := by
  rw [filter_eq, prod_replicate]
#align multiset.pow_count Multiset.pow_count
-/

/- warning: multiset.prod_hom -> Multiset.prod_hom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : CommMonoid.{u2} β] (s : Multiset.{u1} α) {F : Type.{u3}} [_inst_3 : MonoidHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))] (f : F), Eq.{succ u2} β (Multiset.prod.{u2} β _inst_2 (Multiset.map.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} F α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3))) f) s)) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} F α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3))) f (Multiset.prod.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u3} β] (s : Multiset.{u2} α) {F : Type.{u1}} [_inst_3 : MonoidHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))] (f : F), Eq.{succ u3} β (Multiset.prod.{u3} β _inst_2 (Multiset.map.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2)) _inst_3)) f) s)) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2)) _inst_3)) f (Multiset.prod.{u2} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align multiset.prod_hom Multiset.prod_homₓ'. -/
@[to_additive]
theorem prod_hom [CommMonoid β] (s : Multiset α) {F : Type _} [MonoidHomClass F α β] (f : F) :
    (s.map f).Prod = f s.Prod :=
  Quotient.inductionOn s fun l => by simp only [l.prod_hom f, quot_mk_to_coe, coe_map, coe_prod]
#align multiset.prod_hom Multiset.prod_hom
#align multiset.sum_hom Multiset.sum_hom

/- warning: multiset.prod_hom' -> Multiset.prod_hom' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u3} β] (s : Multiset.{u1} ι) {F : Type.{u4}} [_inst_3 : MonoidHomClass.{u4, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))] (f : F) (g : ι -> α), Eq.{succ u3} β (Multiset.prod.{u3} β _inst_2 (Multiset.map.{u1, u3} ι β (fun (i : ι) => coeFn.{succ u4, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u4, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))) (MonoidHomClass.toMulHomClass.{u4, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2)) _inst_3))) f (g i)) s)) (coeFn.{succ u4, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u4, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))) (MonoidHomClass.toMulHomClass.{u4, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2)) _inst_3))) f (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α g s)))
but is expected to have type
  forall {ι : Type.{u3}} {α : Type.{u1}} {β : Type.{u4}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : CommMonoid.{u4} β] (s : Multiset.{u3} ι) {F : Type.{u2}} [_inst_3 : MonoidHomClass.{u2, u1, u4} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u4} β (CommMonoid.toMonoid.{u4} β _inst_2))] (f : F) (g : ι -> α), Eq.{succ u4} β (Multiset.prod.{u4} β _inst_2 (Multiset.map.{u3, u4} ι β (fun (i : ι) => FunLike.coe.{succ u2, succ u1, succ u4} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{u2, u1, u4} F α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toMul.{u4} β (Monoid.toMulOneClass.{u4} β (CommMonoid.toMonoid.{u4} β _inst_2))) (MonoidHomClass.toMulHomClass.{u2, u1, u4} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u4} β (CommMonoid.toMonoid.{u4} β _inst_2)) _inst_3)) f (g i)) s)) (FunLike.coe.{succ u2, succ u1, succ u4} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{u2, u1, u4} F α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toMul.{u4} β (Monoid.toMulOneClass.{u4} β (CommMonoid.toMonoid.{u4} β _inst_2))) (MonoidHomClass.toMulHomClass.{u2, u1, u4} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u4} β (CommMonoid.toMonoid.{u4} β _inst_2)) _inst_3)) f (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u3, u1} ι α g s)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_hom' Multiset.prod_hom'ₓ'. -/
@[to_additive]
theorem prod_hom' [CommMonoid β] (s : Multiset ι) {F : Type _} [MonoidHomClass F α β] (f : F)
    (g : ι → α) : (s.map fun i => f <| g i).Prod = f (s.map g).Prod :=
  by
  convert (s.map g).prod_hom f
  exact (map_map _ _ _).symm
#align multiset.prod_hom' Multiset.prod_hom'
#align multiset.sum_hom' Multiset.sum_hom'

/- warning: multiset.prod_hom₂ -> Multiset.prod_hom₂ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u3} β] [_inst_3 : CommMonoid.{u4} γ] (s : Multiset.{u1} ι) (f : α -> β -> γ), (forall (a : α) (b : α) (c : β) (d : β), Eq.{succ u4} γ (f (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) a b) (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2)))) c d)) (HMul.hMul.{u4, u4, u4} γ γ γ (instHMul.{u4} γ (MulOneClass.toHasMul.{u4} γ (Monoid.toMulOneClass.{u4} γ (CommMonoid.toMonoid.{u4} γ _inst_3)))) (f a c) (f b d))) -> (Eq.{succ u4} γ (f (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))))) (OfNat.ofNat.{u3} β 1 (OfNat.mk.{u3} β 1 (One.one.{u3} β (MulOneClass.toHasOne.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))))))) (OfNat.ofNat.{u4} γ 1 (OfNat.mk.{u4} γ 1 (One.one.{u4} γ (MulOneClass.toHasOne.{u4} γ (Monoid.toMulOneClass.{u4} γ (CommMonoid.toMonoid.{u4} γ _inst_3))))))) -> (forall (f₁ : ι -> α) (f₂ : ι -> β), Eq.{succ u4} γ (Multiset.prod.{u4} γ _inst_3 (Multiset.map.{u1, u4} ι γ (fun (i : ι) => f (f₁ i) (f₂ i)) s)) (f (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α f₁ s)) (Multiset.prod.{u3} β _inst_2 (Multiset.map.{u1, u3} ι β f₂ s))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {β : Type.{u4}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : CommMonoid.{u4} β] [_inst_3 : CommMonoid.{u3} γ] (s : Multiset.{u2} ι) (f : α -> β -> γ), (forall (a : α) (b : α) (c : β) (d : β), Eq.{succ u3} γ (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b) (HMul.hMul.{u4, u4, u4} β β β (instHMul.{u4} β (MulOneClass.toMul.{u4} β (Monoid.toMulOneClass.{u4} β (CommMonoid.toMonoid.{u4} β _inst_2)))) c d)) (HMul.hMul.{u3, u3, u3} γ γ γ (instHMul.{u3} γ (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_3)))) (f a c) (f b d))) -> (Eq.{succ u3} γ (f (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u4} β 1 (One.toOfNat1.{u4} β (Monoid.toOne.{u4} β (CommMonoid.toMonoid.{u4} β _inst_2))))) (OfNat.ofNat.{u3} γ 1 (One.toOfNat1.{u3} γ (Monoid.toOne.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_3))))) -> (forall (f₁ : ι -> α) (f₂ : ι -> β), Eq.{succ u3} γ (Multiset.prod.{u3} γ _inst_3 (Multiset.map.{u2, u3} ι γ (fun (i : ι) => f (f₁ i) (f₂ i)) s)) (f (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u2, u1} ι α f₁ s)) (Multiset.prod.{u4} β _inst_2 (Multiset.map.{u2, u4} ι β f₂ s))))
Case conversion may be inaccurate. Consider using '#align multiset.prod_hom₂ Multiset.prod_hom₂ₓ'. -/
@[to_additive]
theorem prod_hom₂ [CommMonoid β] [CommMonoid γ] (s : Multiset ι) (f : α → β → γ)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → α)
    (f₂ : ι → β) : (s.map fun i => f (f₁ i) (f₂ i)).Prod = f (s.map f₁).Prod (s.map f₂).Prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, coe_map, coe_prod]
#align multiset.prod_hom₂ Multiset.prod_hom₂
#align multiset.sum_hom₂ Multiset.sum_hom₂

/- warning: multiset.prod_hom_rel -> Multiset.prod_hom_rel is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u3} β] (s : Multiset.{u1} ι) {r : α -> β -> Prop} {f : ι -> α} {g : ι -> β}, (r (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))))) (OfNat.ofNat.{u3} β 1 (OfNat.mk.{u3} β 1 (One.one.{u3} β (MulOneClass.toHasOne.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))))))) -> (forall {{a : ι}} {{b : α}} {{c : β}}, (r b c) -> (r (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (f a) b) (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2)))) (g a) c))) -> (r (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α f s)) (Multiset.prod.{u3} β _inst_2 (Multiset.map.{u1, u3} ι β g s)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : CommMonoid.{u3} β] (s : Multiset.{u2} ι) {r : α -> β -> Prop} {f : ι -> α} {g : ι -> β}, (r (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u3} β 1 (One.toOfNat1.{u3} β (Monoid.toOne.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))))) -> (forall {{a : ι}} {{b : α}} {{c : β}}, (r b c) -> (r (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (f a) b) (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2)))) (g a) c))) -> (r (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u2, u1} ι α f s)) (Multiset.prod.{u3} β _inst_2 (Multiset.map.{u2, u3} ι β g s)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_hom_rel Multiset.prod_hom_relₓ'. -/
@[to_additive]
theorem prod_hom_rel [CommMonoid β] (s : Multiset ι) {r : α → β → Prop} {f : ι → α} {g : ι → β}
    (h₁ : r 1 1) (h₂ : ∀ ⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
    r (s.map f).Prod (s.map g).Prod :=
  Quotient.inductionOn s fun l => by
    simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, coe_map, coe_prod]
#align multiset.prod_hom_rel Multiset.prod_hom_rel
#align multiset.sum_hom_rel Multiset.sum_hom_rel

/- warning: multiset.prod_map_one -> Multiset.prod_map_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] {m : Multiset.{u1} ι}, Eq.{succ u2} α (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α (fun (i : ι) => OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))))) m)) (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] {m : Multiset.{u1} ι}, Eq.{succ u2} α (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α (fun (i : ι) => OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (Monoid.toOne.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) m)) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (Monoid.toOne.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_one Multiset.prod_map_oneₓ'. -/
@[to_additive]
theorem prod_map_one : prod (m.map fun i => (1 : α)) = 1 := by
  rw [map_const, prod_replicate, one_pow]
#align multiset.prod_map_one Multiset.prod_map_one
#align multiset.sum_map_zero Multiset.sum_map_zero

/- warning: multiset.prod_map_mul -> Multiset.prod_map_mul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] {m : Multiset.{u1} ι} {f : ι -> α} {g : ι -> α}, Eq.{succ u2} α (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (f i) (g i)) m)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α f m)) (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α g m)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] {m : Multiset.{u1} ι} {f : ι -> α} {g : ι -> α}, Eq.{succ u2} α (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (f i) (g i)) m)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α f m)) (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α g m)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_mul Multiset.prod_map_mulₓ'. -/
@[simp, to_additive]
theorem prod_map_mul : (m.map fun i => f i * g i).Prod = (m.map f).Prod * (m.map g).Prod :=
  m.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _
#align multiset.prod_map_mul Multiset.prod_map_mul
#align multiset.sum_map_add Multiset.sum_map_add

/- warning: multiset.prod_map_neg -> Multiset.prod_map_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))] (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u1, u1} α α (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) _inst_2))) s)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) _inst_2)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)) (Multiset.prod.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))] (s : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u1, u1} α α (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) _inst_2))) s)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (HPow.hPow.{u1, 0, u1} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) α (instHPow.{u1, 0} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) _inst_2)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)) (Multiset.prod.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_neg Multiset.prod_map_negₓ'. -/
@[simp]
theorem prod_map_neg [HasDistribNeg α] (s : Multiset α) :
    (s.map Neg.neg).Prod = (-1) ^ s.card * s.Prod :=
  by
  refine' Quotient.ind _ s
  simp
#align multiset.prod_map_neg Multiset.prod_map_neg

#print Multiset.prod_map_pow /-
@[to_additive]
theorem prod_map_pow {n : ℕ} : (m.map fun i => f i ^ n).Prod = (m.map f).Prod ^ n :=
  m.prod_hom' (powMonoidHom n : α →* α) f
#align multiset.prod_map_pow Multiset.prod_map_pow
-/

/- warning: multiset.prod_map_prod_map -> Multiset.prod_map_prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} α] (m : Multiset.{u2} β) (n : Multiset.{u3} γ) {f : β -> γ -> α}, Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u2, u1} β α (fun (a : β) => Multiset.prod.{u1} α _inst_1 (Multiset.map.{u3, u1} γ α (fun (b : γ) => f a b) n)) m)) (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u3, u1} γ α (fun (b : γ) => Multiset.prod.{u1} α _inst_1 (Multiset.map.{u2, u1} β α (fun (a : β) => f a b) m)) n))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] (m : Multiset.{u3} β) (n : Multiset.{u2} γ) {f : β -> γ -> α}, Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u3, u1} β α (fun (a : β) => Multiset.prod.{u1} α _inst_1 (Multiset.map.{u2, u1} γ α (fun (b : γ) => f a b) n)) m)) (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u2, u1} γ α (fun (b : γ) => Multiset.prod.{u1} α _inst_1 (Multiset.map.{u3, u1} β α (fun (a : β) => f a b) m)) n))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_prod_map Multiset.prod_map_prod_mapₓ'. -/
@[to_additive]
theorem prod_map_prod_map (m : Multiset β) (n : Multiset γ) {f : β → γ → α} :
    prod (m.map fun a => Prod <| n.map fun b => f a b) =
      prod (n.map fun b => Prod <| m.map fun a => f a b) :=
  Multiset.induction_on m (by simp) fun a m ih => by simp [ih]
#align multiset.prod_map_prod_map Multiset.prod_map_prod_map
#align multiset.sum_map_sum_map Multiset.sum_map_sum_map

/- warning: multiset.prod_induction -> Multiset.prod_induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (p : α -> Prop) (s : Multiset.{u1} α), (forall (a : α) (b : α), (p a) -> (p b) -> (p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b))) -> (p (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)) -> (p (Multiset.prod.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (p : α -> Prop) (s : Multiset.{u1} α), (forall (a : α) (b : α), (p a) -> (p b) -> (p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b))) -> (p (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) -> (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (p a)) -> (p (Multiset.prod.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align multiset.prod_induction Multiset.prod_inductionₓ'. -/
@[to_additive]
theorem prod_induction (p : α → Prop) (s : Multiset α) (p_mul : ∀ a b, p a → p b → p (a * b))
    (p_one : p 1) (p_s : ∀ a ∈ s, p a) : p s.Prod :=
  by
  rw [prod_eq_foldr]
  exact foldr_induction (· * ·) (fun x y z => by simp [mul_left_comm]) 1 p s p_mul p_one p_s
#align multiset.prod_induction Multiset.prod_induction
#align multiset.sum_induction Multiset.sum_induction

/- warning: multiset.prod_induction_nonempty -> Multiset.prod_induction_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {s : Multiset.{u1} α} (p : α -> Prop), (forall (a : α) (b : α), (p a) -> (p b) -> (p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b))) -> (Ne.{succ u1} (Multiset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Multiset.{u1} α) (Multiset.hasEmptyc.{u1} α))) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)) -> (p (Multiset.prod.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {s : Multiset.{u1} α} (p : α -> Prop), (forall (a : α) (b : α), (p a) -> (p b) -> (p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b))) -> (Ne.{succ u1} (Multiset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Multiset.{u1} α) (Multiset.instEmptyCollectionMultiset.{u1} α))) -> (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (p a)) -> (p (Multiset.prod.{u1} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align multiset.prod_induction_nonempty Multiset.prod_induction_nonemptyₓ'. -/
@[to_additive]
theorem prod_induction_nonempty (p : α → Prop) (p_mul : ∀ a b, p a → p b → p (a * b)) (hs : s ≠ ∅)
    (p_s : ∀ a ∈ s, p a) : p s.Prod := by
  revert s
  refine' Multiset.induction _ _
  · intro h
    exfalso
    simpa using h
  intro a s hs hsa hpsa
  rw [prod_cons]
  by_cases hs_empty : s = ∅
  · simp [hs_empty, hpsa a]
  have hps : ∀ x, x ∈ s → p x := fun x hxs => hpsa x (mem_cons_of_mem hxs)
  exact p_mul a s.prod (hpsa a (mem_cons_self a s)) (hs hs_empty hps)
#align multiset.prod_induction_nonempty Multiset.prod_induction_nonempty
#align multiset.sum_induction_nonempty Multiset.sum_induction_nonempty

/- warning: multiset.prod_dvd_prod_of_le -> Multiset.prod_dvd_prod_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) s t) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Multiset.prod.{u1} α _inst_1 s) (Multiset.prod.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {s : Multiset.{u1} α} {t : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) s t) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Multiset.prod.{u1} α _inst_1 s) (Multiset.prod.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align multiset.prod_dvd_prod_of_le Multiset.prod_dvd_prod_of_leₓ'. -/
theorem prod_dvd_prod_of_le (h : s ≤ t) : s.Prod ∣ t.Prod :=
  by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  simp only [prod_add, dvd_mul_right]
#align multiset.prod_dvd_prod_of_le Multiset.prod_dvd_prod_of_le

end CommMonoid

#print Multiset.prod_dvd_prod_of_dvd /-
theorem prod_dvd_prod_of_dvd [CommMonoid β] {S : Multiset α} (g1 g2 : α → β)
    (h : ∀ a ∈ S, g1 a ∣ g2 a) : (Multiset.map g1 S).Prod ∣ (Multiset.map g2 S).Prod :=
  by
  apply Multiset.induction_on' S; · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]
#align multiset.prod_dvd_prod_of_dvd Multiset.prod_dvd_prod_of_dvd
-/

section AddCommMonoid

variable [AddCommMonoid α]

/- warning: multiset.sum_add_monoid_hom -> Multiset.sumAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α], AddMonoidHom.{u1, u1} (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α], AddMonoidHom.{u1, u1} (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align multiset.sum_add_monoid_hom Multiset.sumAddMonoidHomₓ'. -/
/-- `multiset.sum`, the sum of the elements of a multiset, promoted to a morphism of
`add_comm_monoid`s. -/
def sumAddMonoidHom : Multiset α →+ α where
  toFun := sum
  map_zero' := sum_zero
  map_add' := sum_add
#align multiset.sum_add_monoid_hom Multiset.sumAddMonoidHom

/- warning: multiset.coe_sum_add_monoid_hom -> Multiset.coe_sumAddMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α], Eq.{succ u1} ((fun (_x : AddMonoidHom.{u1, u1} (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) => (Multiset.{u1} α) -> α) (Multiset.sumAddMonoidHom.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, u1} (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (fun (_x : AddMonoidHom.{u1, u1} (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) => (Multiset.{u1} α) -> α) (AddMonoidHom.hasCoeToFun.{u1, u1} (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (Multiset.sumAddMonoidHom.{u1} α _inst_1)) (Multiset.sum.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α], Eq.{succ u1} (forall (a : Multiset.{u1} α), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (AddMonoidHom.{u1, u1} (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => α) _x) (AddHomClass.toFunLike.{u1, u1, u1} (AddMonoidHom.{u1, u1} (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (Multiset.{u1} α) α (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (AddMonoidHom.{u1, u1} (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))) (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1)) (AddMonoidHom.addMonoidHomClass.{u1, u1} (Multiset.{u1} α) α (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_1))))) (Multiset.sumAddMonoidHom.{u1} α _inst_1)) (Multiset.sum.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align multiset.coe_sum_add_monoid_hom Multiset.coe_sumAddMonoidHomₓ'. -/
@[simp]
theorem coe_sumAddMonoidHom : (sumAddMonoidHom : Multiset α → α) = Sum :=
  rfl
#align multiset.coe_sum_add_monoid_hom Multiset.coe_sumAddMonoidHom

end AddCommMonoid

section CommMonoidWithZero

variable [CommMonoidWithZero α]

/- warning: multiset.prod_eq_zero -> Multiset.prod_eq_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {s : Multiset.{u1} α}, (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))) s) -> (Eq.{succ u1} α (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) s) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {s : Multiset.{u1} α}, (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α _inst_1))) s) -> (Eq.{succ u1} α (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) s) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align multiset.prod_eq_zero Multiset.prod_eq_zeroₓ'. -/
theorem prod_eq_zero {s : Multiset α} (h : (0 : α) ∈ s) : s.Prod = 0 :=
  by
  rcases Multiset.exists_cons_of_mem h with ⟨s', hs'⟩
  simp [hs', Multiset.prod_cons]
#align multiset.prod_eq_zero Multiset.prod_eq_zero

variable [NoZeroDivisors α] [Nontrivial α] {s : Multiset α}

/- warning: multiset.prod_eq_zero_iff -> Multiset.prod_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))] [_inst_3 : Nontrivial.{u1} α] {s : Multiset.{u1} α}, Iff (Eq.{succ u1} α (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) s) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (CommMonoidWithZero.toZero.{u1} α _inst_1)] [_inst_3 : Nontrivial.{u1} α] {s : Multiset.{u1} α}, Iff (Eq.{succ u1} α (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) s) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α _inst_1)))) (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α _inst_1))) s)
Case conversion may be inaccurate. Consider using '#align multiset.prod_eq_zero_iff Multiset.prod_eq_zero_iffₓ'. -/
theorem prod_eq_zero_iff : s.Prod = 0 ↔ (0 : α) ∈ s :=
  Quotient.inductionOn s fun l => by
    rw [quot_mk_to_coe, coe_prod]
    exact List.prod_eq_zero_iff
#align multiset.prod_eq_zero_iff Multiset.prod_eq_zero_iff

/- warning: multiset.prod_ne_zero -> Multiset.prod_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))] [_inst_3 : Nontrivial.{u1} α] {s : Multiset.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))) s)) -> (Ne.{succ u1} α (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) s) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] [_inst_2 : NoZeroDivisors.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) (CommMonoidWithZero.toZero.{u1} α _inst_1)] [_inst_3 : Nontrivial.{u1} α] {s : Multiset.{u1} α}, (Not (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α _inst_1))) s)) -> (Ne.{succ u1} α (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) s) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align multiset.prod_ne_zero Multiset.prod_ne_zeroₓ'. -/
theorem prod_ne_zero (h : (0 : α) ∉ s) : s.Prod ≠ 0 :=
  mt prod_eq_zero_iff.1 h
#align multiset.prod_ne_zero Multiset.prod_ne_zero

end CommMonoidWithZero

section DivisionCommMonoid

variable [DivisionCommMonoid α] {m : Multiset ι} {f g : ι → α}

/- warning: multiset.prod_map_inv' -> Multiset.prod_map_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (m : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α (DivisionCommMonoid.toCommMonoid.{u1} α _inst_1) (Multiset.map.{u1, u1} α α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) m)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))) (Multiset.prod.{u1} α (DivisionCommMonoid.toCommMonoid.{u1} α _inst_1) m))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionCommMonoid.{u1} α] (m : Multiset.{u1} α), Eq.{succ u1} α (Multiset.prod.{u1} α (DivisionCommMonoid.toCommMonoid.{u1} α _inst_1) (Multiset.map.{u1, u1} α α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1))))) m)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α _inst_1)))) (Multiset.prod.{u1} α (DivisionCommMonoid.toCommMonoid.{u1} α _inst_1) m))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_inv' Multiset.prod_map_inv'ₓ'. -/
@[to_additive]
theorem prod_map_inv' (m : Multiset α) : (m.map Inv.inv).Prod = m.Prod⁻¹ :=
  m.prod_hom (invMonoidHom : α →* α)
#align multiset.prod_map_inv' Multiset.prod_map_inv'
#align multiset.sum_map_neg' Multiset.sum_map_neg'

/- warning: multiset.prod_map_inv -> Multiset.prod_map_inv is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionCommMonoid.{u2} α] {m : Multiset.{u1} ι} {f : ι -> α}, Eq.{succ u2} α (Multiset.prod.{u2} α (DivisionCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α (fun (i : ι) => Inv.inv.{u2} α (DivInvMonoid.toHasInv.{u2} α (DivisionMonoid.toDivInvMonoid.{u2} α (DivisionCommMonoid.toDivisionMonoid.{u2} α _inst_1))) (f i)) m)) (Inv.inv.{u2} α (DivInvMonoid.toHasInv.{u2} α (DivisionMonoid.toDivInvMonoid.{u2} α (DivisionCommMonoid.toDivisionMonoid.{u2} α _inst_1))) (Multiset.prod.{u2} α (DivisionCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α f m)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionCommMonoid.{u2} α] {m : Multiset.{u1} ι} {f : ι -> α}, Eq.{succ u2} α (Multiset.prod.{u2} α (DivisionCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α (fun (i : ι) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (DivisionCommMonoid.toDivisionMonoid.{u2} α _inst_1)))) (f i)) m)) (Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (DivisionCommMonoid.toDivisionMonoid.{u2} α _inst_1)))) (Multiset.prod.{u2} α (DivisionCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α f m)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_inv Multiset.prod_map_invₓ'. -/
@[simp, to_additive]
theorem prod_map_inv : (m.map fun i => (f i)⁻¹).Prod = (m.map f).Prod⁻¹ :=
  by
  convert (m.map f).prod_map_inv'
  rw [map_map]
#align multiset.prod_map_inv Multiset.prod_map_inv
#align multiset.sum_map_neg Multiset.sum_map_neg

/- warning: multiset.prod_map_div -> Multiset.prod_map_div is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionCommMonoid.{u2} α] {m : Multiset.{u1} ι} {f : ι -> α} {g : ι -> α}, Eq.{succ u2} α (Multiset.prod.{u2} α (DivisionCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (DivisionMonoid.toDivInvMonoid.{u2} α (DivisionCommMonoid.toDivisionMonoid.{u2} α _inst_1)))) (f i) (g i)) m)) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (DivisionMonoid.toDivInvMonoid.{u2} α (DivisionCommMonoid.toDivisionMonoid.{u2} α _inst_1)))) (Multiset.prod.{u2} α (DivisionCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α f m)) (Multiset.prod.{u2} α (DivisionCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α g m)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DivisionCommMonoid.{u2} α] {m : Multiset.{u1} ι} {f : ι -> α} {g : ι -> α}, Eq.{succ u2} α (Multiset.prod.{u2} α (DivisionCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (DivisionMonoid.toDivInvMonoid.{u2} α (DivisionCommMonoid.toDivisionMonoid.{u2} α _inst_1)))) (f i) (g i)) m)) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (DivisionMonoid.toDivInvMonoid.{u2} α (DivisionCommMonoid.toDivisionMonoid.{u2} α _inst_1)))) (Multiset.prod.{u2} α (DivisionCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α f m)) (Multiset.prod.{u2} α (DivisionCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α g m)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_div Multiset.prod_map_divₓ'. -/
@[simp, to_additive]
theorem prod_map_div : (m.map fun i => f i / g i).Prod = (m.map f).Prod / (m.map g).Prod :=
  m.prod_hom₂ (· / ·) mul_div_mul_comm (div_one _) _ _
#align multiset.prod_map_div Multiset.prod_map_div
#align multiset.sum_map_sub Multiset.sum_map_sub

#print Multiset.prod_map_zpow /-
@[to_additive]
theorem prod_map_zpow {n : ℤ} : (m.map fun i => f i ^ n).Prod = (m.map f).Prod ^ n :=
  by
  convert (m.map f).prod_hom (zpowGroupHom _ : α →* α)
  rw [map_map]
  rfl
#align multiset.prod_map_zpow Multiset.prod_map_zpow
#align multiset.sum_map_zsmul Multiset.sum_map_zsmul
-/

end DivisionCommMonoid

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] {a : α} {s : Multiset ι} {f : ι → α}

/- warning: multiset.sum_map_mul_left -> Multiset.sum_map_mul_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] {a : α} {s : Multiset.{u1} ι} {f : ι -> α}, Eq.{succ u2} α (Multiset.sum.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) a (f i)) s)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) a (Multiset.sum.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α f s)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] {a : α} {s : Multiset.{u1} ι} {f : ι -> α}, Eq.{succ u2} α (Multiset.sum.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) a (f i)) s)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) a (Multiset.sum.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α f s)))
Case conversion may be inaccurate. Consider using '#align multiset.sum_map_mul_left Multiset.sum_map_mul_leftₓ'. -/
theorem sum_map_mul_left : sum (s.map fun i => a * f i) = a * sum (s.map f) :=
  Multiset.induction_on s (by simp) fun i s ih => by simp [ih, mul_add]
#align multiset.sum_map_mul_left Multiset.sum_map_mul_left

/- warning: multiset.sum_map_mul_right -> Multiset.sum_map_mul_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] {a : α} {s : Multiset.{u1} ι} {f : ι -> α}, Eq.{succ u2} α (Multiset.sum.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) (f i) a) s)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (Distrib.toHasMul.{u2} α (NonUnitalNonAssocSemiring.toDistrib.{u2} α _inst_1))) (Multiset.sum.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α f s)) a)
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} α] {a : α} {s : Multiset.{u1} ι} {f : ι -> α}, Eq.{succ u2} α (Multiset.sum.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α (fun (i : ι) => HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) (f i) a) s)) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocSemiring.toMul.{u2} α _inst_1)) (Multiset.sum.{u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α f s)) a)
Case conversion may be inaccurate. Consider using '#align multiset.sum_map_mul_right Multiset.sum_map_mul_rightₓ'. -/
theorem sum_map_mul_right : sum (s.map fun i => f i * a) = sum (s.map f) * a :=
  Multiset.induction_on s (by simp) fun a s ih => by simp [ih, add_mul]
#align multiset.sum_map_mul_right Multiset.sum_map_mul_right

end NonUnitalNonAssocSemiring

section Semiring

variable [Semiring α]

#print Multiset.dvd_sum /-
theorem dvd_sum {a : α} {s : Multiset α} : (∀ x ∈ s, a ∣ x) → a ∣ s.Sum :=
  Multiset.induction_on s (fun _ => dvd_zero _) fun x s ih h =>
    by
    rw [sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun y hy => h _ <| mem_cons.2 <| Or.inr hy)
#align multiset.dvd_sum Multiset.dvd_sum
-/

end Semiring

/-! ### Order -/


section OrderedCommMonoid

variable [OrderedCommMonoid α] {s t : Multiset α} {a : α}

/- warning: multiset.one_le_prod_of_one_le -> Multiset.one_le_prod_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Multiset.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))))) x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))))) (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Multiset.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))) x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))) (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align multiset.one_le_prod_of_one_le Multiset.one_le_prod_of_one_leₓ'. -/
@[to_additive sum_nonneg]
theorem one_le_prod_of_one_le : (∀ x ∈ s, (1 : α) ≤ x) → 1 ≤ s.Prod :=
  Quotient.inductionOn s fun l hl => by simpa using List.one_le_prod_of_one_le hl
#align multiset.one_le_prod_of_one_le Multiset.one_le_prod_of_one_le
#align multiset.sum_nonneg Multiset.sum_nonneg

/- warning: multiset.single_le_prod -> Multiset.single_le_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Multiset.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))))) x)) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) x (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Multiset.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))) x)) -> (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) x (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align multiset.single_le_prod Multiset.single_le_prodₓ'. -/
@[to_additive]
theorem single_le_prod : (∀ x ∈ s, (1 : α) ≤ x) → ∀ x ∈ s, x ≤ s.Prod :=
  Quotient.inductionOn s fun l hl x hx => by simpa using List.single_le_prod hl x hx
#align multiset.single_le_prod Multiset.single_le_prod
#align multiset.single_le_sum Multiset.single_le_sum

/- warning: multiset.prod_le_pow_card -> Multiset.prod_le_pow_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] (s : Multiset.{u1} α) (n : α), (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) x n)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) s) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))) n (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] (s : Multiset.{u1} α) (n : α), (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) x n)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) s) (HPow.hPow.{u1, 0, u1} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) α (instHPow.{u1, 0} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))) n (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_le_pow_card Multiset.prod_le_pow_cardₓ'. -/
@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card (s : Multiset α) (n : α) (h : ∀ x ∈ s, x ≤ n) : s.Prod ≤ n ^ s.card :=
  by
  induction s using Quotient.inductionOn
  simpa using List.prod_le_pow_card _ _ h
#align multiset.prod_le_pow_card Multiset.prod_le_pow_card
#align multiset.sum_le_card_nsmul Multiset.sum_le_card_nsmul

/- warning: multiset.all_one_of_le_one_le_of_prod_eq_one -> Multiset.all_one_of_le_one_le_of_prod_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Multiset.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))))) x)) -> (Eq.{succ u1} α (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) s) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))))) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Multiset.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))) x)) -> (Eq.{succ u1} α (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) s) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))) -> (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align multiset.all_one_of_le_one_le_of_prod_eq_one Multiset.all_one_of_le_one_le_of_prod_eq_oneₓ'. -/
@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
theorem all_one_of_le_one_le_of_prod_eq_one :
    (∀ x ∈ s, (1 : α) ≤ x) → s.Prod = 1 → ∀ x ∈ s, x = (1 : α) :=
  by
  apply Quotient.inductionOn s
  simp only [quot_mk_to_coe, coe_prod, mem_coe]
  exact fun l => List.all_one_of_le_one_le_of_prod_eq_one
#align multiset.all_one_of_le_one_le_of_prod_eq_one Multiset.all_one_of_le_one_le_of_prod_eq_one
#align multiset.all_zero_of_le_zero_le_of_sum_eq_zero Multiset.all_zero_of_le_zero_le_of_sum_eq_zero

#print Multiset.prod_le_prod_of_rel_le /-
@[to_additive]
theorem prod_le_prod_of_rel_le (h : s.Rel (· ≤ ·) t) : s.Prod ≤ t.Prod :=
  by
  induction' h with _ _ _ _ rh _ rt
  · rfl
  · rw [prod_cons, prod_cons]
    exact mul_le_mul' rh rt
#align multiset.prod_le_prod_of_rel_le Multiset.prod_le_prod_of_rel_le
#align multiset.sum_le_sum_of_rel_le Multiset.sum_le_sum_of_rel_le
-/

/- warning: multiset.prod_map_le_prod_map -> Multiset.prod_map_le_prod_map is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : OrderedCommMonoid.{u2} α] {s : Multiset.{u1} ι} (f : ι -> α) (g : ι -> α), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Multiset.{u1} ι) (Multiset.hasMem.{u1} ι) i s) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedCommMonoid.toPartialOrder.{u2} α _inst_1))) (f i) (g i))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedCommMonoid.toPartialOrder.{u2} α _inst_1))) (Multiset.prod.{u2} α (OrderedCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α f s)) (Multiset.prod.{u2} α (OrderedCommMonoid.toCommMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι α g s)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Multiset.{u2} ι} (f : ι -> α) (g : ι -> α), (forall (i : ι), (Membership.mem.{u2, u2} ι (Multiset.{u2} ι) (Multiset.instMembershipMultiset.{u2} ι) i s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (f i) (g i))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) (Multiset.map.{u2, u1} ι α f s)) (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) (Multiset.map.{u2, u1} ι α g s)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_map_le_prod_map Multiset.prod_map_le_prod_mapₓ'. -/
@[to_additive]
theorem prod_map_le_prod_map {s : Multiset ι} (f : ι → α) (g : ι → α) (h : ∀ i, i ∈ s → f i ≤ g i) :
    (s.map f).Prod ≤ (s.map g).Prod :=
  prod_le_prod_of_rel_le <| rel_map.2 <| rel_refl_of_refl_on h
#align multiset.prod_map_le_prod_map Multiset.prod_map_le_prod_map
#align multiset.sum_map_le_sum_map Multiset.sum_map_le_sum_map

#print Multiset.prod_map_le_prod /-
@[to_additive]
theorem prod_map_le_prod (f : α → α) (h : ∀ x, x ∈ s → f x ≤ x) : (s.map f).Prod ≤ s.Prod :=
  prod_le_prod_of_rel_le <| rel_map_left.2 <| rel_refl_of_refl_on h
#align multiset.prod_map_le_prod Multiset.prod_map_le_prod
#align multiset.sum_map_le_sum Multiset.sum_map_le_sum
-/

#print Multiset.prod_le_prod_map /-
@[to_additive]
theorem prod_le_prod_map (f : α → α) (h : ∀ x, x ∈ s → x ≤ f x) : s.Prod ≤ (s.map f).Prod :=
  @prod_map_le_prod αᵒᵈ _ _ f h
#align multiset.prod_le_prod_map Multiset.prod_le_prod_map
#align multiset.sum_le_sum_map Multiset.sum_le_sum_map
-/

/- warning: multiset.pow_card_le_prod -> Multiset.pow_card_le_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Multiset.{u1} α} {a : α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) a x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))) a (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toCancelAddMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)) (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Multiset.{u1} α} {a : α}, (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) a x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (HPow.hPow.{u1, 0, u1} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) α (instHPow.{u1, 0} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) s) (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))) a (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)) (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align multiset.pow_card_le_prod Multiset.pow_card_le_prodₓ'. -/
@[to_additive card_nsmul_le_sum]
theorem pow_card_le_prod (h : ∀ x ∈ s, a ≤ x) : a ^ s.card ≤ s.Prod :=
  by
  rw [← Multiset.prod_replicate, ← Multiset.map_const]
  exact prod_map_le_prod _ h
#align multiset.pow_card_le_prod Multiset.pow_card_le_prod
#align multiset.card_nsmul_le_sum Multiset.card_nsmul_le_sum

end OrderedCommMonoid

/- warning: multiset.prod_nonneg -> Multiset.prod_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommSemiring.{u1} α] {m : Multiset.{u1} α}, (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α _inst_1))))))))) a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (OrderedSemiring.toOrderedAddCommMonoid.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (OrderedSemiring.toSemiring.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α _inst_1))))))))) (Multiset.prod.{u1} α (CommSemiring.toCommMonoid.{u1} α (OrderedCommSemiring.toCommSemiring.{u1} α _inst_1)) m))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommSemiring.{u1} α] {m : Multiset.{u1} α}, (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a m) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (OrderedCommSemiring.toCommSemiring.{u1} α _inst_1))))) a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α (OrderedCommSemiring.toOrderedSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CommSemiring.toCommMonoidWithZero.{u1} α (OrderedCommSemiring.toCommSemiring.{u1} α _inst_1))))) (Multiset.prod.{u1} α (CommSemiring.toCommMonoid.{u1} α (OrderedCommSemiring.toCommSemiring.{u1} α _inst_1)) m))
Case conversion may be inaccurate. Consider using '#align multiset.prod_nonneg Multiset.prod_nonnegₓ'. -/
theorem prod_nonneg [OrderedCommSemiring α] {m : Multiset α} (h : ∀ a ∈ m, (0 : α) ≤ a) :
    0 ≤ m.Prod := by
  revert h
  refine' m.induction_on _ _
  · rintro -
    rw [prod_zero]
    exact zero_le_one
  intro a s hs ih
  rw [prod_cons]
  exact mul_nonneg (ih _ <| mem_cons_self _ _) (hs fun a ha => ih _ <| mem_cons_of_mem ha)
#align multiset.prod_nonneg Multiset.prod_nonneg

/- warning: multiset.prod_eq_one -> Multiset.prod_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {m : Multiset.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))))) -> (Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 m) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {m : Multiset.{u1} α}, (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))) -> (Eq.{succ u1} α (Multiset.prod.{u1} α _inst_1 m) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align multiset.prod_eq_one Multiset.prod_eq_oneₓ'. -/
/-- Slightly more general version of `multiset.prod_eq_one_iff` for a non-ordered `monoid` -/
@[to_additive
      "Slightly more general version of `multiset.sum_eq_zero_iff`\n  for a non-ordered `add_monoid`"]
theorem prod_eq_one [CommMonoid α] {m : Multiset α} (h : ∀ x ∈ m, x = (1 : α)) : m.Prod = 1 :=
  by
  induction' m using Quotient.inductionOn with l
  simp [List.prod_eq_one h]
#align multiset.prod_eq_one Multiset.prod_eq_one
#align multiset.sum_eq_zero Multiset.sum_eq_zero

#print Multiset.le_prod_of_mem /-
@[to_additive]
theorem le_prod_of_mem [CanonicallyOrderedMonoid α] {m : Multiset α} {a : α} (h : a ∈ m) :
    a ≤ m.Prod := by
  obtain ⟨m', rfl⟩ := exists_cons_of_mem h
  rw [prod_cons]
  exact _root_.le_mul_right (le_refl a)
#align multiset.le_prod_of_mem Multiset.le_prod_of_mem
#align multiset.le_sum_of_mem Multiset.le_sum_of_mem
-/

/- warning: multiset.le_prod_of_submultiplicative_on_pred -> Multiset.le_prod_of_submultiplicative_on_pred is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : OrderedCommMonoid.{u2} β] (f : α -> β) (p : α -> Prop), (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β (OrderedCommMonoid.toCommMonoid.{u2} β _inst_2)))))))) -> (p (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))) -> (forall (a : α) (b : α), (p a) -> (p b) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedCommMonoid.toPartialOrder.{u2} β _inst_2))) (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β (OrderedCommMonoid.toCommMonoid.{u2} β _inst_2))))) (f a) (f b)))) -> (forall (a : α) (b : α), (p a) -> (p b) -> (p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b))) -> (forall (s : Multiset.{u1} α), (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedCommMonoid.toPartialOrder.{u2} β _inst_2))) (f (Multiset.prod.{u1} α _inst_1 s)) (Multiset.prod.{u2} β (OrderedCommMonoid.toCommMonoid.{u2} β _inst_2) (Multiset.map.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : OrderedCommMonoid.{u1} β] (f : α -> β) (p : α -> Prop), (Eq.{succ u1} β (f (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (Monoid.toOne.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β (OrderedCommMonoid.toCommMonoid.{u1} β _inst_2)))))) -> (p (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (Monoid.toOne.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))))) -> (forall (a : α) (b : α), (p a) -> (p b) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (OrderedCommMonoid.toPartialOrder.{u1} β _inst_2))) (f (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) a b)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β (OrderedCommMonoid.toCommMonoid.{u1} β _inst_2))))) (f a) (f b)))) -> (forall (a : α) (b : α), (p a) -> (p b) -> (p (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) a b))) -> (forall (s : Multiset.{u2} α), (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (p a)) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (OrderedCommMonoid.toPartialOrder.{u1} β _inst_2))) (f (Multiset.prod.{u2} α _inst_1 s)) (Multiset.prod.{u1} β (OrderedCommMonoid.toCommMonoid.{u1} β _inst_2) (Multiset.map.{u2, u1} α β f s))))
Case conversion may be inaccurate. Consider using '#align multiset.le_prod_of_submultiplicative_on_pred Multiset.le_prod_of_submultiplicative_on_predₓ'. -/
@[to_additive le_sum_of_subadditive_on_pred]
theorem le_prod_of_submultiplicative_on_pred [CommMonoid α] [OrderedCommMonoid β] (f : α → β)
    (p : α → Prop) (h_one : f 1 = 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hps : ∀ a, a ∈ s → p a) : f s.Prod ≤ (s.map f).Prod :=
  by
  revert s
  refine' Multiset.induction _ _
  · simp [le_of_eq h_one]
  intro a s hs hpsa
  have hps : ∀ x, x ∈ s → p x := fun x hx => hpsa x (mem_cons_of_mem hx)
  have hp_prod : p s.prod := prod_induction p s hp_mul hp_one hps
  rw [prod_cons, map_cons, prod_cons]
  exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans (mul_le_mul_left' (hs hps) _)
#align multiset.le_prod_of_submultiplicative_on_pred Multiset.le_prod_of_submultiplicative_on_pred
#align multiset.le_sum_of_subadditive_on_pred Multiset.le_sum_of_subadditive_on_pred

/- warning: multiset.le_prod_of_submultiplicative -> Multiset.le_prod_of_submultiplicative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : OrderedCommMonoid.{u2} β] (f : α -> β), (Eq.{succ u2} β (f (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β (OrderedCommMonoid.toCommMonoid.{u2} β _inst_2)))))))) -> (forall (a : α) (b : α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedCommMonoid.toPartialOrder.{u2} β _inst_2))) (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β (OrderedCommMonoid.toCommMonoid.{u2} β _inst_2))))) (f a) (f b))) -> (forall (s : Multiset.{u1} α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedCommMonoid.toPartialOrder.{u2} β _inst_2))) (f (Multiset.prod.{u1} α _inst_1 s)) (Multiset.prod.{u2} β (OrderedCommMonoid.toCommMonoid.{u2} β _inst_2) (Multiset.map.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : OrderedCommMonoid.{u1} β] (f : α -> β), (Eq.{succ u1} β (f (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (Monoid.toOne.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β (OrderedCommMonoid.toCommMonoid.{u1} β _inst_2)))))) -> (forall (a : α) (b : α), LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (OrderedCommMonoid.toPartialOrder.{u1} β _inst_2))) (f (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) a b)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β (OrderedCommMonoid.toCommMonoid.{u1} β _inst_2))))) (f a) (f b))) -> (forall (s : Multiset.{u2} α), LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (OrderedCommMonoid.toPartialOrder.{u1} β _inst_2))) (f (Multiset.prod.{u2} α _inst_1 s)) (Multiset.prod.{u1} β (OrderedCommMonoid.toCommMonoid.{u1} β _inst_2) (Multiset.map.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align multiset.le_prod_of_submultiplicative Multiset.le_prod_of_submultiplicativeₓ'. -/
@[to_additive le_sum_of_subadditive]
theorem le_prod_of_submultiplicative [CommMonoid α] [OrderedCommMonoid β] (f : α → β)
    (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) :
    f s.Prod ≤ (s.map f).Prod :=
  le_prod_of_submultiplicative_on_pred f (fun i => True) h_one trivial (fun x y _ _ => h_mul x y)
    (by simp) s (by simp)
#align multiset.le_prod_of_submultiplicative Multiset.le_prod_of_submultiplicative
#align multiset.le_sum_of_subadditive Multiset.le_sum_of_subadditive

/- warning: multiset.le_prod_nonempty_of_submultiplicative_on_pred -> Multiset.le_prod_nonempty_of_submultiplicative_on_pred is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : OrderedCommMonoid.{u2} β] (f : α -> β) (p : α -> Prop), (forall (a : α) (b : α), (p a) -> (p b) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedCommMonoid.toPartialOrder.{u2} β _inst_2))) (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β (OrderedCommMonoid.toCommMonoid.{u2} β _inst_2))))) (f a) (f b)))) -> (forall (a : α) (b : α), (p a) -> (p b) -> (p (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b))) -> (forall (s : Multiset.{u1} α), (Ne.{succ u1} (Multiset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Multiset.{u1} α) (Multiset.hasEmptyc.{u1} α))) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (p a)) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedCommMonoid.toPartialOrder.{u2} β _inst_2))) (f (Multiset.prod.{u1} α _inst_1 s)) (Multiset.prod.{u2} β (OrderedCommMonoid.toCommMonoid.{u2} β _inst_2) (Multiset.map.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : OrderedCommMonoid.{u1} β] (f : α -> β) (p : α -> Prop), (forall (a : α) (b : α), (p a) -> (p b) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (OrderedCommMonoid.toPartialOrder.{u1} β _inst_2))) (f (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) a b)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β (OrderedCommMonoid.toCommMonoid.{u1} β _inst_2))))) (f a) (f b)))) -> (forall (a : α) (b : α), (p a) -> (p b) -> (p (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) a b))) -> (forall (s : Multiset.{u2} α), (Ne.{succ u2} (Multiset.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Multiset.{u2} α) (Multiset.instEmptyCollectionMultiset.{u2} α))) -> (forall (a : α), (Membership.mem.{u2, u2} α (Multiset.{u2} α) (Multiset.instMembershipMultiset.{u2} α) a s) -> (p a)) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (OrderedCommMonoid.toPartialOrder.{u1} β _inst_2))) (f (Multiset.prod.{u2} α _inst_1 s)) (Multiset.prod.{u1} β (OrderedCommMonoid.toCommMonoid.{u1} β _inst_2) (Multiset.map.{u2, u1} α β f s))))
Case conversion may be inaccurate. Consider using '#align multiset.le_prod_nonempty_of_submultiplicative_on_pred Multiset.le_prod_nonempty_of_submultiplicative_on_predₓ'. -/
@[to_additive le_sum_nonempty_of_subadditive_on_pred]
theorem le_prod_nonempty_of_submultiplicative_on_pred [CommMonoid α] [OrderedCommMonoid β]
    (f : α → β) (p : α → Prop) (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b)
    (hp_mul : ∀ a b, p a → p b → p (a * b)) (s : Multiset α) (hs_nonempty : s ≠ ∅)
    (hs : ∀ a, a ∈ s → p a) : f s.Prod ≤ (s.map f).Prod :=
  by
  revert s
  refine' Multiset.induction _ _
  · intro h
    exfalso
    exact h rfl
  rintro a s hs hsa_nonempty hsa_prop
  rw [prod_cons, map_cons, prod_cons]
  by_cases hs_empty : s = ∅
  · simp [hs_empty]
  have hsa_restrict : ∀ x, x ∈ s → p x := fun x hx => hsa_prop x (mem_cons_of_mem hx)
  have hp_sup : p s.prod := prod_induction_nonempty p hp_mul hs_empty hsa_restrict
  have hp_a : p a := hsa_prop a (mem_cons_self a s)
  exact (h_mul a _ hp_a hp_sup).trans (mul_le_mul_left' (hs hs_empty hsa_restrict) _)
#align multiset.le_prod_nonempty_of_submultiplicative_on_pred Multiset.le_prod_nonempty_of_submultiplicative_on_pred
#align multiset.le_sum_nonempty_of_subadditive_on_pred Multiset.le_sum_nonempty_of_subadditive_on_pred

/- warning: multiset.le_prod_nonempty_of_submultiplicative -> Multiset.le_prod_nonempty_of_submultiplicative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : OrderedCommMonoid.{u2} β] (f : α -> β), (forall (a : α) (b : α), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedCommMonoid.toPartialOrder.{u2} β _inst_2))) (f (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) a b)) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β (OrderedCommMonoid.toCommMonoid.{u2} β _inst_2))))) (f a) (f b))) -> (forall (s : Multiset.{u1} α), (Ne.{succ u1} (Multiset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Multiset.{u1} α) (Multiset.hasEmptyc.{u1} α))) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedCommMonoid.toPartialOrder.{u2} β _inst_2))) (f (Multiset.prod.{u1} α _inst_1 s)) (Multiset.prod.{u2} β (OrderedCommMonoid.toCommMonoid.{u2} β _inst_2) (Multiset.map.{u1, u2} α β f s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : OrderedCommMonoid.{u1} β] (f : α -> β), (forall (a : α) (b : α), LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (OrderedCommMonoid.toPartialOrder.{u1} β _inst_2))) (f (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) a b)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β (OrderedCommMonoid.toCommMonoid.{u1} β _inst_2))))) (f a) (f b))) -> (forall (s : Multiset.{u2} α), (Ne.{succ u2} (Multiset.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Multiset.{u2} α) (Multiset.instEmptyCollectionMultiset.{u2} α))) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (OrderedCommMonoid.toPartialOrder.{u1} β _inst_2))) (f (Multiset.prod.{u2} α _inst_1 s)) (Multiset.prod.{u1} β (OrderedCommMonoid.toCommMonoid.{u1} β _inst_2) (Multiset.map.{u2, u1} α β f s))))
Case conversion may be inaccurate. Consider using '#align multiset.le_prod_nonempty_of_submultiplicative Multiset.le_prod_nonempty_of_submultiplicativeₓ'. -/
@[to_additive le_sum_nonempty_of_subadditive]
theorem le_prod_nonempty_of_submultiplicative [CommMonoid α] [OrderedCommMonoid β] (f : α → β)
    (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) (hs_nonempty : s ≠ ∅) :
    f s.Prod ≤ (s.map f).Prod :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun i => True) (by simp [h_mul]) (by simp) s
    hs_nonempty (by simp)
#align multiset.le_prod_nonempty_of_submultiplicative Multiset.le_prod_nonempty_of_submultiplicative
#align multiset.le_sum_nonempty_of_subadditive Multiset.le_sum_nonempty_of_subadditive

/- warning: multiset.sum_map_singleton -> Multiset.sum_map_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.sum.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)) (Multiset.map.{u1, u1} α (Multiset.{u1} α) (fun (a : α) => Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a) s)) s
but is expected to have type
  forall {α : Type.{u1}} (s : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Multiset.sum.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)) (Multiset.map.{u1, u1} α (Multiset.{u1} α) (fun (a : α) => Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a) s)) s
Case conversion may be inaccurate. Consider using '#align multiset.sum_map_singleton Multiset.sum_map_singletonₓ'. -/
@[simp]
theorem sum_map_singleton (s : Multiset α) : (s.map fun a => ({a} : Multiset α)).Sum = s :=
  Multiset.induction_on s (by simp) (by simp)
#align multiset.sum_map_singleton Multiset.sum_map_singleton

/- warning: multiset.abs_sum_le_sum_abs -> Multiset.abs_sum_le_sum_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedAddCommGroup.{u1} α] {s : Multiset.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommGroup.toLinearOrder.{u1} α _inst_1))))) (Multiset.sum.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) s)) (Multiset.sum.{u1} α (AddCommGroup.toAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))) (Multiset.map.{u1, u1} α α (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommGroup.toLinearOrder.{u1} α _inst_1)))))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedAddCommGroup.{u1} α] {s : Multiset.{u1} α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1)))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedAddCommGroup.toLinearOrder.{u1} α _inst_1)))))) (Multiset.sum.{u1} α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u1} α _inst_1))) s)) (Multiset.sum.{u1} α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} α (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u1} α _inst_1))) (Multiset.map.{u1, u1} α α (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α (LinearOrderedAddCommGroup.toLinearOrder.{u1} α _inst_1))))))) s))
Case conversion may be inaccurate. Consider using '#align multiset.abs_sum_le_sum_abs Multiset.abs_sum_le_sum_absₓ'. -/
theorem abs_sum_le_sum_abs [LinearOrderedAddCommGroup α] {s : Multiset α} :
    abs s.Sum ≤ (s.map abs).Sum :=
  le_sum_of_subadditive _ abs_zero abs_add s
#align multiset.abs_sum_le_sum_abs Multiset.abs_sum_le_sum_abs

end Multiset

/- warning: map_multiset_prod -> map_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : CommMonoid.{u2} β] {F : Type.{u3}} [_inst_3 : MonoidHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))] (f : F) (s : Multiset.{u1} α), Eq.{succ u2} β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} F α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3))) f (Multiset.prod.{u1} α _inst_1 s)) (Multiset.prod.{u2} β _inst_2 (Multiset.map.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} F α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3))) f) s))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u3} α] [_inst_2 : CommMonoid.{u2} β] {F : Type.{u1}} [_inst_3 : MonoidHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))] (f : F) (s : Multiset.{u3} α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) (Multiset.prod.{u3} α _inst_1 s)) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3)) f (Multiset.prod.{u3} α _inst_1 s)) (Multiset.prod.{u2} β _inst_2 (Multiset.map.{u3, u2} α β (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3)) f) s))
Case conversion may be inaccurate. Consider using '#align map_multiset_prod map_multiset_prodₓ'. -/
@[to_additive]
theorem map_multiset_prod [CommMonoid α] [CommMonoid β] {F : Type _} [MonoidHomClass F α β] (f : F)
    (s : Multiset α) : f s.Prod = (s.map f).Prod :=
  (s.prod_hom f).symm
#align map_multiset_prod map_multiset_prod
#align map_multiset_sum map_multiset_sum

/- warning: monoid_hom.map_multiset_prod -> MonoidHom.map_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : CommMonoid.{u2} β] (f : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (s : Multiset.{u1} α), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) f (Multiset.prod.{u1} α _inst_1 s)) (Multiset.prod.{u2} β _inst_2 (Multiset.map.{u1, u2} α β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (fun (_x : MonoidHom.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) => α -> β) (MonoidHom.hasCoeToFun.{u1, u2} α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) f) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u1} β] (f : MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) (s : Multiset.{u2} α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) (Multiset.prod.{u2} α _inst_1 s)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2)) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))))) f (Multiset.prod.{u2} α _inst_1 s)) (Multiset.prod.{u1} β _inst_2 (Multiset.map.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))) α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2)) (MonoidHom.monoidHomClass.{u2, u1} α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2))))) f) s))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_multiset_prod MonoidHom.map_multiset_prodₓ'. -/
@[to_additive]
protected theorem MonoidHom.map_multiset_prod [CommMonoid α] [CommMonoid β] (f : α →* β)
    (s : Multiset α) : f s.Prod = (s.map f).Prod :=
  (s.prod_hom f).symm
#align monoid_hom.map_multiset_prod MonoidHom.map_multiset_prod
#align add_monoid_hom.map_multiset_sum AddMonoidHom.map_multiset_sum

