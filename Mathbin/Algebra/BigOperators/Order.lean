/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module algebra.big_operators.order
! leanprover-community/mathlib commit 824f9ae93a4f5174d2ea948e2d75843dd83447bb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Algebra.Order.Ring.WithTop
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Fintype.Card

/-!
# Results about big operators with values in an ordered algebraic structure.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Mostly monotonicity results for the `∏` and `∑` operations.

-/


open Function

open BigOperators

variable {ι α β M N G k R : Type _}

namespace Finset

section OrderedCommMonoid

variable [CommMonoid M] [OrderedCommMonoid N]

/- warning: finset.le_prod_nonempty_of_submultiplicative_on_pred -> Finset.le_prod_nonempty_of_submultiplicative_on_pred is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : OrderedCommMonoid.{u3} N] (f : M -> N) (p : M -> Prop), (forall (x : M) (y : M), (p x) -> (p y) -> (LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y)) (HMul.hMul.{u3, u3, u3} N N N (instHMul.{u3} N (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2))))) (f x) (f y)))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y))) -> (forall (g : ι -> M) (s : Finset.{u1} ι), (Finset.Nonempty.{u1} ι s) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (p (g i))) -> (LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (Finset.prod.{u2, u1} M ι _inst_1 s (fun (i : ι) => g i))) (Finset.prod.{u3, u1} N ι (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2) s (fun (i : ι) => f (g i)))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : OrderedCommMonoid.{u3} N] (f : M -> N) (p : M -> Prop), (forall (x : M) (y : M), (p x) -> (p y) -> (LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y)) (HMul.hMul.{u3, u3, u3} N N N (instHMul.{u3} N (MulOneClass.toMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2))))) (f x) (f y)))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y))) -> (forall (g : ι -> M) (s : Finset.{u1} ι), (Finset.Nonempty.{u1} ι s) -> (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (p (g i))) -> (LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (Finset.prod.{u2, u1} M ι _inst_1 s (fun (i : ι) => g i))) (Finset.prod.{u3, u1} N ι (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2) s (fun (i : ι) => f (g i)))))
Case conversion may be inaccurate. Consider using '#align finset.le_prod_nonempty_of_submultiplicative_on_pred Finset.le_prod_nonempty_of_submultiplicative_on_predₓ'. -/
/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
submultiplicative on `{x | p x}`, i.e., `p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be
a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∏ x in s, g x) ≤ ∏ x in s, f (g x)`. -/
@[to_additive le_sum_nonempty_of_subadditive_on_pred]
theorem le_prod_nonempty_of_submultiplicative_on_pred (f : M → N) (p : M → Prop)
    (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y) (hp_mul : ∀ x y, p x → p y → p (x * y))
    (g : ι → M) (s : Finset ι) (hs_nonempty : s.Nonempty) (hs : ∀ i ∈ s, p (g i)) :
    f (∏ i in s, g i) ≤ ∏ i in s, f (g i) :=
  by
  refine' le_trans (Multiset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul _ _ _) _
  · simp [hs_nonempty.ne_empty]
  · exact multiset.forall_mem_map_iff.mpr hs
  rw [Multiset.map_map]
  rfl
#align finset.le_prod_nonempty_of_submultiplicative_on_pred Finset.le_prod_nonempty_of_submultiplicative_on_pred
#align finset.le_sum_nonempty_of_subadditive_on_pred Finset.le_sum_nonempty_of_subadditive_on_pred

/-- Let `{x | p x}` be an additive subsemigroup of an additive commutative monoid `M`. Let
`f : M → N` be a map subadditive on `{x | p x}`, i.e., `p x → p y → f (x + y) ≤ f x + f y`. Let
`g i`, `i ∈ s`, be a nonempty finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ i in s, g i) ≤ ∑ i in s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive_on_pred

/- warning: finset.le_prod_nonempty_of_submultiplicative -> Finset.le_prod_nonempty_of_submultiplicative is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : OrderedCommMonoid.{u3} N] (f : M -> N), (forall (x : M) (y : M), LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y)) (HMul.hMul.{u3, u3, u3} N N N (instHMul.{u3} N (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2))))) (f x) (f y))) -> (forall {s : Finset.{u1} ι}, (Finset.Nonempty.{u1} ι s) -> (forall (g : ι -> M), LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (Finset.prod.{u2, u1} M ι _inst_1 s (fun (i : ι) => g i))) (Finset.prod.{u3, u1} N ι (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2) s (fun (i : ι) => f (g i)))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : OrderedCommMonoid.{u3} N] (f : M -> N), (forall (x : M) (y : M), LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y)) (HMul.hMul.{u3, u3, u3} N N N (instHMul.{u3} N (MulOneClass.toMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2))))) (f x) (f y))) -> (forall {s : Finset.{u1} ι}, (Finset.Nonempty.{u1} ι s) -> (forall (g : ι -> M), LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (Finset.prod.{u2, u1} M ι _inst_1 s (fun (i : ι) => g i))) (Finset.prod.{u3, u1} N ι (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2) s (fun (i : ι) => f (g i)))))
Case conversion may be inaccurate. Consider using '#align finset.le_prod_nonempty_of_submultiplicative Finset.le_prod_nonempty_of_submultiplicativeₓ'. -/
/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∏ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
@[to_additive le_sum_nonempty_of_subadditive]
theorem le_prod_nonempty_of_submultiplicative (f : M → N) (h_mul : ∀ x y, f (x * y) ≤ f x * f y)
    {s : Finset ι} (hs : s.Nonempty) (g : ι → M) : f (∏ i in s, g i) ≤ ∏ i in s, f (g i) :=
  le_prod_nonempty_of_submultiplicative_on_pred f (fun i => True) (fun x y _ _ => h_mul x y)
    (fun _ _ _ _ => trivial) g s hs fun _ _ => trivial
#align finset.le_prod_nonempty_of_submultiplicative Finset.le_prod_nonempty_of_submultiplicative
#align finset.le_sum_nonempty_of_subadditive Finset.le_sum_nonempty_of_subadditive

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y` and `g i`, `i ∈ s`, is a
nonempty finite family of elements of `M`, then `f (∑ i in s, g i) ≤ ∑ i in s, f (g i)`. -/
add_decl_doc le_sum_nonempty_of_subadditive

/- warning: finset.le_prod_of_submultiplicative_on_pred -> Finset.le_prod_of_submultiplicative_on_pred is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : OrderedCommMonoid.{u3} N] (f : M -> N) (p : M -> Prop), (Eq.{succ u3} N (f (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) (OfNat.ofNat.{u3} N 1 (OfNat.mk.{u3} N 1 (One.one.{u3} N (MulOneClass.toHasOne.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2)))))))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y)) (HMul.hMul.{u3, u3, u3} N N N (instHMul.{u3} N (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2))))) (f x) (f y)))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y))) -> (forall (g : ι -> M) {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (p (g i))) -> (LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (Finset.prod.{u2, u1} M ι _inst_1 s (fun (i : ι) => g i))) (Finset.prod.{u3, u1} N ι (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2) s (fun (i : ι) => f (g i)))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : OrderedCommMonoid.{u3} N] (f : M -> N) (p : M -> Prop), (Eq.{succ u3} N (f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) (OfNat.ofNat.{u3} N 1 (One.toOfNat1.{u3} N (Monoid.toOne.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2)))))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y)) (HMul.hMul.{u3, u3, u3} N N N (instHMul.{u3} N (MulOneClass.toMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2))))) (f x) (f y)))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y))) -> (forall (g : ι -> M) {s : Finset.{u1} ι}, (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (p (g i))) -> (LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (Finset.prod.{u2, u1} M ι _inst_1 s (fun (i : ι) => g i))) (Finset.prod.{u3, u1} N ι (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2) s (fun (i : ι) => f (g i)))))
Case conversion may be inaccurate. Consider using '#align finset.le_prod_of_submultiplicative_on_pred Finset.le_prod_of_submultiplicative_on_predₓ'. -/
/-- Let `{x | p x}` be a subsemigroup of a commutative monoid `M`. Let `f : M → N` be a map
such that `f 1 = 1` and `f` is submultiplicative on `{x | p x}`, i.e.,
`p x → p y → f (x * y) ≤ f x * f y`. Let `g i`, `i ∈ s`, be a finite family of elements of `M` such
that `∀ i ∈ s, p (g i)`. Then `f (∏ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
@[to_additive le_sum_of_subadditive_on_pred]
theorem le_prod_of_submultiplicative_on_pred (f : M → N) (p : M → Prop) (h_one : f 1 = 1)
    (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y) (hp_mul : ∀ x y, p x → p y → p (x * y))
    (g : ι → M) {s : Finset ι} (hs : ∀ i ∈ s, p (g i)) : f (∏ i in s, g i) ≤ ∏ i in s, f (g i) :=
  by
  rcases eq_empty_or_nonempty s with (rfl | hs_nonempty)
  · simp [h_one]
  · exact le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul g s hs_nonempty hs
#align finset.le_prod_of_submultiplicative_on_pred Finset.le_prod_of_submultiplicative_on_pred
#align finset.le_sum_of_subadditive_on_pred Finset.le_sum_of_subadditive_on_pred

/-- Let `{x | p x}` be a subsemigroup of a commutative additive monoid `M`. Let `f : M → N` be a map
such that `f 0 = 0` and `f` is subadditive on `{x | p x}`, i.e. `p x → p y → f (x + y) ≤ f x + f y`.
Let `g i`, `i ∈ s`, be a finite family of elements of `M` such that `∀ i ∈ s, p (g i)`. Then
`f (∑ x in s, g x) ≤ ∑ x in s, f (g x)`. -/
add_decl_doc le_sum_of_subadditive_on_pred

/- warning: finset.le_prod_of_submultiplicative -> Finset.le_prod_of_submultiplicative is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : OrderedCommMonoid.{u3} N] (f : M -> N), (Eq.{succ u3} N (f (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))))) (OfNat.ofNat.{u3} N 1 (OfNat.mk.{u3} N 1 (One.one.{u3} N (MulOneClass.toHasOne.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2)))))))) -> (forall (x : M) (y : M), LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y)) (HMul.hMul.{u3, u3, u3} N N N (instHMul.{u3} N (MulOneClass.toHasMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2))))) (f x) (f y))) -> (forall (s : Finset.{u1} ι) (g : ι -> M), LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (Finset.prod.{u2, u1} M ι _inst_1 s (fun (i : ι) => g i))) (Finset.prod.{u3, u1} N ι (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2) s (fun (i : ι) => f (g i))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : OrderedCommMonoid.{u3} N] (f : M -> N), (Eq.{succ u3} N (f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) (OfNat.ofNat.{u3} N 1 (One.toOfNat1.{u3} N (Monoid.toOne.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2)))))) -> (forall (x : M) (y : M), LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) x y)) (HMul.hMul.{u3, u3, u3} N N N (instHMul.{u3} N (MulOneClass.toMul.{u3} N (Monoid.toMulOneClass.{u3} N (CommMonoid.toMonoid.{u3} N (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2))))) (f x) (f y))) -> (forall (s : Finset.{u1} ι) (g : ι -> M), LE.le.{u3} N (Preorder.toLE.{u3} N (PartialOrder.toPreorder.{u3} N (OrderedCommMonoid.toPartialOrder.{u3} N _inst_2))) (f (Finset.prod.{u2, u1} M ι _inst_1 s (fun (i : ι) => g i))) (Finset.prod.{u3, u1} N ι (OrderedCommMonoid.toCommMonoid.{u3} N _inst_2) s (fun (i : ι) => f (g i))))
Case conversion may be inaccurate. Consider using '#align finset.le_prod_of_submultiplicative Finset.le_prod_of_submultiplicativeₓ'. -/
/-- If `f : M → N` is a submultiplicative function, `f (x * y) ≤ f x * f y`, `f 1 = 1`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∏ i in s, g i) ≤ ∏ i in s, f (g i)`. -/
@[to_additive le_sum_of_subadditive]
theorem le_prod_of_submultiplicative (f : M → N) (h_one : f 1 = 1)
    (h_mul : ∀ x y, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (∏ i in s, g i) ≤ ∏ i in s, f (g i) :=
  by
  refine' le_trans (Multiset.le_prod_of_submultiplicative f h_one h_mul _) _
  rw [Multiset.map_map]
  rfl
#align finset.le_prod_of_submultiplicative Finset.le_prod_of_submultiplicative
#align finset.le_sum_of_subadditive Finset.le_sum_of_subadditive

/-- If `f : M → N` is a subadditive function, `f (x + y) ≤ f x + f y`, `f 0 = 0`, and `g i`,
`i ∈ s`, is a finite family of elements of `M`, then `f (∑ i in s, g i) ≤ ∑ i in s, f (g i)`. -/
add_decl_doc le_sum_of_subadditive

variable {f g : ι → N} {s t : Finset ι}

/- warning: finset.prod_le_prod' -> Finset.prod_le_prod' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N} {g : ι -> N} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (f i) (g i))) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (i : ι) => f i)) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (i : ι) => g i)))
but is expected to have type
  forall {ι : Type.{u2}} {N : Type.{u1}} [_inst_2 : OrderedCommMonoid.{u1} N] {f : ι -> N} {g : ι -> N} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (f i) (g i))) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s (fun (i : ι) => f i)) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_le_prod' Finset.prod_le_prod'ₓ'. -/
/-- In an ordered commutative monoid, if each factor `f i` of one finite product is less than or
equal to the corresponding factor `g i` of another finite product, then
`∏ i in s, f i ≤ ∏ i in s, g i`. -/
@[to_additive sum_le_sum]
theorem prod_le_prod' (h : ∀ i ∈ s, f i ≤ g i) : (∏ i in s, f i) ≤ ∏ i in s, g i :=
  Multiset.prod_map_le_prod_map f g h
#align finset.prod_le_prod' Finset.prod_le_prod'
#align finset.sum_le_sum Finset.sum_le_sum

/-- In an ordered additive commutative monoid, if each summand `f i` of one finite sum is less than
or equal to the corresponding summand `g i` of another finite sum, then
`∑ i in s, f i ≤ ∑ i in s, g i`. -/
add_decl_doc sum_le_sum

/- warning: finset.one_le_prod' -> Finset.one_le_prod' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) (f i))) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {N : Type.{u1}} [_inst_2 : OrderedCommMonoid.{u1} N] {f : ι -> N} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))) (f i))) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.one_le_prod' Finset.one_le_prod'ₓ'. -/
@[to_additive sum_nonneg]
theorem one_le_prod' (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i in s, f i :=
  le_trans (by rw [prod_const_one]) (prod_le_prod' h)
#align finset.one_le_prod' Finset.one_le_prod'
#align finset.sum_nonneg Finset.sum_nonneg

/- warning: finset.one_le_prod'' -> Finset.one_le_prod'' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N} {s : Finset.{u1} ι}, (forall (i : ι), LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) (f i)) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N} {s : Finset.{u1} ι}, (forall (i : ι), LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (One.toOfNat1.{u2} N (Monoid.toOne.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))) (f i)) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (One.toOfNat1.{u2} N (Monoid.toOne.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.one_le_prod'' Finset.one_le_prod''ₓ'. -/
@[to_additive Finset.sum_nonneg']
theorem one_le_prod'' (h : ∀ i : ι, 1 ≤ f i) : 1 ≤ ∏ i : ι in s, f i :=
  Finset.one_le_prod' fun i hi => h i
#align finset.one_le_prod'' Finset.one_le_prod''
#align finset.sum_nonneg' Finset.sum_nonneg'

/- warning: finset.prod_le_one' -> Finset.prod_le_one' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (f i) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))))) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (i : ι) => f i)) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))))
but is expected to have type
  forall {ι : Type.{u2}} {N : Type.{u1}} [_inst_2 : OrderedCommMonoid.{u1} N] {f : ι -> N} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (f i) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))))) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s (fun (i : ι) => f i)) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_le_one' Finset.prod_le_one'ₓ'. -/
@[to_additive sum_nonpos]
theorem prod_le_one' (h : ∀ i ∈ s, f i ≤ 1) : (∏ i in s, f i) ≤ 1 :=
  (prod_le_prod' h).trans_eq (by rw [prod_const_one])
#align finset.prod_le_one' Finset.prod_le_one'
#align finset.sum_nonpos Finset.sum_nonpos

/- warning: finset.prod_le_prod_of_subset_of_one_le' -> Finset.prod_le_prod_of_subset_of_one_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N} {s : Finset.{u1} ι} {t : Finset.{u1} ι}, (HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.hasSubset.{u1} ι) s t) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i t) -> (Not (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s)) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) (f i))) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (i : ι) => f i)) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) t (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {N : Type.{u1}} [_inst_2 : OrderedCommMonoid.{u1} N] {f : ι -> N} {s : Finset.{u2} ι} {t : Finset.{u2} ι}, (HasSubset.Subset.{u2} (Finset.{u2} ι) (Finset.instHasSubsetFinset.{u2} ι) s t) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i t) -> (Not (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s)) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))) (f i))) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s (fun (i : ι) => f i)) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) t (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_le_prod_of_subset_of_one_le' Finset.prod_le_prod_of_subset_of_one_le'ₓ'. -/
@[to_additive sum_le_sum_of_subset_of_nonneg]
theorem prod_le_prod_of_subset_of_one_le' (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) :
    (∏ i in s, f i) ≤ ∏ i in t, f i := by
  classical calc
      (∏ i in s, f i) ≤ (∏ i in t \ s, f i) * ∏ i in s, f i :=
        le_mul_of_one_le_left' <| one_le_prod' <| by simpa only [mem_sdiff, and_imp]
      _ = ∏ i in t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i in t, f i := by rw [sdiff_union_of_subset h]
      
#align finset.prod_le_prod_of_subset_of_one_le' Finset.prod_le_prod_of_subset_of_one_le'
#align finset.sum_le_sum_of_subset_of_nonneg Finset.sum_le_sum_of_subset_of_nonneg

/- warning: finset.prod_mono_set_of_one_le' -> Finset.prod_mono_set_of_one_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N}, (forall (x : ι), LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) (f x)) -> (Monotone.{u1, u2} (Finset.{u1} ι) N (PartialOrder.toPreorder.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι)) (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2)) (fun (s : Finset.{u1} ι) => Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (x : ι) => f x)))
but is expected to have type
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N}, (forall (x : ι), LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (One.toOfNat1.{u2} N (Monoid.toOne.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))) (f x)) -> (Monotone.{u1, u2} (Finset.{u1} ι) N (PartialOrder.toPreorder.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι)) (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2)) (fun (s : Finset.{u1} ι) => Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (x : ι) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_mono_set_of_one_le' Finset.prod_mono_set_of_one_le'ₓ'. -/
@[to_additive sum_mono_set_of_nonneg]
theorem prod_mono_set_of_one_le' (hf : ∀ x, 1 ≤ f x) : Monotone fun s => ∏ x in s, f x :=
  fun s t hst => prod_le_prod_of_subset_of_one_le' hst fun x _ _ => hf x
#align finset.prod_mono_set_of_one_le' Finset.prod_mono_set_of_one_le'
#align finset.sum_mono_set_of_nonneg Finset.sum_mono_set_of_nonneg

/- warning: finset.prod_le_univ_prod_of_one_le' -> Finset.prod_le_univ_prod_of_one_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N} [_inst_3 : Fintype.{u1} ι] {s : Finset.{u1} ι}, (forall (x : ι), LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) (f x)) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (x : ι) => f x)) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) (Finset.univ.{u1} ι _inst_3) (fun (x : ι) => f x)))
but is expected to have type
  forall {ι : Type.{u2}} {N : Type.{u1}} [_inst_2 : OrderedCommMonoid.{u1} N] {f : ι -> N} [_inst_3 : Fintype.{u2} ι] {s : Finset.{u2} ι}, (forall (x : ι), LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))) (f x)) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s (fun (x : ι) => f x)) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) (Finset.univ.{u2} ι _inst_3) (fun (x : ι) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_le_univ_prod_of_one_le' Finset.prod_le_univ_prod_of_one_le'ₓ'. -/
@[to_additive sum_le_univ_sum_of_nonneg]
theorem prod_le_univ_prod_of_one_le' [Fintype ι] {s : Finset ι} (w : ∀ x, 1 ≤ f x) :
    (∏ x in s, f x) ≤ ∏ x, f x :=
  prod_le_prod_of_subset_of_one_le' (subset_univ s) fun a _ _ => w a
#align finset.prod_le_univ_prod_of_one_le' Finset.prod_le_univ_prod_of_one_le'
#align finset.sum_le_univ_sum_of_nonneg Finset.sum_le_univ_sum_of_nonneg

/- warning: finset.prod_eq_one_iff_of_one_le' -> Finset.prod_eq_one_iff_of_one_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) (f i))) -> (Iff (Eq.{succ u2} N (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (i : ι) => f i)) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2)))))))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Eq.{succ u2} N (f i) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))))))
but is expected to have type
  forall {ι : Type.{u2}} {N : Type.{u1}} [_inst_2 : OrderedCommMonoid.{u1} N] {f : ι -> N} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))) (f i))) -> (Iff (Eq.{succ u1} N (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s (fun (i : ι) => f i)) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2)))))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Eq.{succ u1} N (f i) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_one_iff_of_one_le' Finset.prod_eq_one_iff_of_one_le'ₓ'. -/
@[to_additive sum_eq_zero_iff_of_nonneg]
theorem prod_eq_one_iff_of_one_le' :
    (∀ i ∈ s, 1 ≤ f i) → ((∏ i in s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) := by
  classical
    apply Finset.induction_on s
    exact fun _ => ⟨fun _ _ => False.elim, fun _ => rfl⟩
    intro a s ha ih H
    have : ∀ i ∈ s, 1 ≤ f i := fun _ => H _ ∘ mem_insert_of_mem
    rw [prod_insert ha, mul_eq_one_iff' (H _ <| mem_insert_self _ _) (one_le_prod' this),
      forall_mem_insert, ih this]
#align finset.prod_eq_one_iff_of_one_le' Finset.prod_eq_one_iff_of_one_le'
#align finset.sum_eq_zero_iff_of_nonneg Finset.sum_eq_zero_iff_of_nonneg

/- warning: finset.prod_eq_one_iff_of_le_one' -> Finset.prod_eq_one_iff_of_le_one' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (f i) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))))) -> (Iff (Eq.{succ u2} N (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (i : ι) => f i)) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2)))))))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Eq.{succ u2} N (f i) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))))))
but is expected to have type
  forall {ι : Type.{u2}} {N : Type.{u1}} [_inst_2 : OrderedCommMonoid.{u1} N] {f : ι -> N} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (f i) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))))) -> (Iff (Eq.{succ u1} N (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s (fun (i : ι) => f i)) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2)))))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Eq.{succ u1} N (f i) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_one_iff_of_le_one' Finset.prod_eq_one_iff_of_le_one'ₓ'. -/
@[to_additive sum_eq_zero_iff_of_nonneg]
theorem prod_eq_one_iff_of_le_one' :
    (∀ i ∈ s, f i ≤ 1) → ((∏ i in s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) :=
  @prod_eq_one_iff_of_one_le' _ Nᵒᵈ _ _ _
#align finset.prod_eq_one_iff_of_le_one' Finset.prod_eq_one_iff_of_le_one'
#align finset.sum_eq_zero_iff_of_nonneg Finset.sum_eq_zero_iff_of_nonneg

/- warning: finset.single_le_prod' -> Finset.single_le_prod' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {f : ι -> N} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) (f i))) -> (forall {a : ι}, (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) a s) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (f a) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (x : ι) => f x))))
but is expected to have type
  forall {ι : Type.{u2}} {N : Type.{u1}} [_inst_2 : OrderedCommMonoid.{u1} N] {f : ι -> N} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2))))) (f i))) -> (forall {a : ι}, (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) a s) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (f a) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s (fun (x : ι) => f x))))
Case conversion may be inaccurate. Consider using '#align finset.single_le_prod' Finset.single_le_prod'ₓ'. -/
@[to_additive single_le_sum]
theorem single_le_prod' (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s) : f a ≤ ∏ x in s, f x :=
  calc
    f a = ∏ i in {a}, f i := prod_singleton.symm
    _ ≤ ∏ i in s, f i :=
      prod_le_prod_of_subset_of_one_le' (singleton_subset_iff.2 h) fun i hi _ => hf i hi
    
#align finset.single_le_prod' Finset.single_le_prod'
#align finset.single_le_sum Finset.single_le_sum

/- warning: finset.prod_le_pow_card -> Finset.prod_le_pow_card is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] (s : Finset.{u1} ι) (f : ι -> N) (n : N), (forall (x : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x s) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (f x) n)) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s f) (HPow.hPow.{u2, 0, u2} N Nat N (instHPow.{u2, 0} N Nat (Monoid.Pow.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2)))) n (Finset.card.{u1} ι s)))
but is expected to have type
  forall {ι : Type.{u2}} {N : Type.{u1}} [_inst_2 : OrderedCommMonoid.{u1} N] (s : Finset.{u2} ι) (f : ι -> N) (n : N), (forall (x : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (f x) n)) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s f) (HPow.hPow.{u1, 0, u1} N Nat N (instHPow.{u1, 0} N Nat (Monoid.Pow.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2)))) n (Finset.card.{u2} ι s)))
Case conversion may be inaccurate. Consider using '#align finset.prod_le_pow_card Finset.prod_le_pow_cardₓ'. -/
@[to_additive sum_le_card_nsmul]
theorem prod_le_pow_card (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, f x ≤ n) :
    s.Prod f ≤ n ^ s.card :=
  by
  refine' (Multiset.prod_le_pow_card (s.val.map f) n _).trans _
  · simpa using h
  · simpa
#align finset.prod_le_pow_card Finset.prod_le_pow_card
#align finset.sum_le_card_nsmul Finset.sum_le_card_nsmul

/- warning: finset.pow_card_le_prod -> Finset.pow_card_le_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] (s : Finset.{u1} ι) (f : ι -> N) (n : N), (forall (x : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x s) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) n (f x))) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (HPow.hPow.{u2, 0, u2} N Nat N (instHPow.{u2, 0} N Nat (Monoid.Pow.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2)))) n (Finset.card.{u1} ι s)) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s f))
but is expected to have type
  forall {ι : Type.{u2}} {N : Type.{u1}} [_inst_2 : OrderedCommMonoid.{u1} N] (s : Finset.{u2} ι) (f : ι -> N) (n : N), (forall (x : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) n (f x))) -> (LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N (OrderedCommMonoid.toPartialOrder.{u1} N _inst_2))) (HPow.hPow.{u1, 0, u1} N Nat N (instHPow.{u1, 0} N Nat (Monoid.Pow.{u1} N (CommMonoid.toMonoid.{u1} N (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2)))) n (Finset.card.{u2} ι s)) (Finset.prod.{u1, u2} N ι (OrderedCommMonoid.toCommMonoid.{u1} N _inst_2) s f))
Case conversion may be inaccurate. Consider using '#align finset.pow_card_le_prod Finset.pow_card_le_prodₓ'. -/
@[to_additive card_nsmul_le_sum]
theorem pow_card_le_prod (s : Finset ι) (f : ι → N) (n : N) (h : ∀ x ∈ s, n ≤ f x) :
    n ^ s.card ≤ s.Prod f :=
  @Finset.prod_le_pow_card _ Nᵒᵈ _ _ _ _ h
#align finset.pow_card_le_prod Finset.pow_card_le_prod
#align finset.card_nsmul_le_sum Finset.card_nsmul_le_sum

#print Finset.card_bunionᵢ_le_card_mul /-
theorem card_bunionᵢ_le_card_mul [DecidableEq β] (s : Finset ι) (f : ι → Finset β) (n : ℕ)
    (h : ∀ a ∈ s, (f a).card ≤ n) : (s.bunionᵢ f).card ≤ s.card * n :=
  card_bunionᵢ_le.trans <| sum_le_card_nsmul _ _ _ h
#align finset.card_bUnion_le_card_mul Finset.card_bunionᵢ_le_card_mul
-/

variable {ι' : Type _} [DecidableEq ι']

/- warning: finset.prod_fiberwise_le_prod_of_one_le_prod_fiber' -> Finset.prod_fiberwise_le_prod_of_one_le_prod_fiber' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {s : Finset.{u1} ι} {ι' : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} ι'] {t : Finset.{u3} ι'} {g : ι -> ι'} {f : ι -> N}, (forall (y : ι'), (Not (Membership.Mem.{u3, u3} ι' (Finset.{u3} ι') (Finset.hasMem.{u3} ι') y t)) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) (Finset.filter.{u1} ι (fun (x : ι) => Eq.{succ u3} ι' (g x) y) (fun (a : ι) => _inst_3 (g a) y) s) (fun (x : ι) => f x)))) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u3} N ι' (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) t (fun (y : ι') => Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) (Finset.filter.{u1} ι (fun (x : ι) => Eq.{succ u3} ι' (g x) y) (fun (a : ι) => _inst_3 (g a) y) s) (fun (x : ι) => f x))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (x : ι) => f x)))
but is expected to have type
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {s : Finset.{u1} ι} {ι' : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} ι'] {t : Finset.{u3} ι'} {g : ι -> ι'} {f : ι -> N}, (forall (y : ι'), (Not (Membership.mem.{u3, u3} ι' (Finset.{u3} ι') (Finset.instMembershipFinset.{u3} ι') y t)) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (OfNat.ofNat.{u2} N 1 (One.toOfNat1.{u2} N (Monoid.toOne.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) (Finset.filter.{u1} ι (fun (x : ι) => Eq.{succ u3} ι' (g x) y) (fun (a : ι) => _inst_3 (g a) y) s) (fun (x : ι) => f x)))) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u3} N ι' (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) t (fun (y : ι') => Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) (Finset.filter.{u1} ι (fun (x : ι) => Eq.{succ u3} ι' (g x) y) (fun (a : ι) => _inst_3 (g a) y) s) (fun (x : ι) => f x))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (x : ι) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_fiberwise_le_prod_of_one_le_prod_fiber' Finset.prod_fiberwise_le_prod_of_one_le_prod_fiber'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ∉ » t) -/
@[to_additive sum_fiberwise_le_sum_of_sum_fiber_nonneg]
theorem prod_fiberwise_le_prod_of_one_le_prod_fiber' {t : Finset ι'} {g : ι → ι'} {f : ι → N}
    (h : ∀ (y) (_ : y ∉ t), (1 : N) ≤ ∏ x in s.filterₓ fun x => g x = y, f x) :
    (∏ y in t, ∏ x in s.filterₓ fun x => g x = y, f x) ≤ ∏ x in s, f x :=
  calc
    (∏ y in t, ∏ x in s.filterₓ fun x => g x = y, f x) ≤
        ∏ y in t ∪ s.image g, ∏ x in s.filterₓ fun x => g x = y, f x :=
      prod_le_prod_of_subset_of_one_le' (subset_union_left _ _) fun y hyts => h y
    _ = ∏ x in s, f x :=
      prod_fiberwise_of_maps_to (fun x hx => mem_union.2 <| Or.inr <| mem_image_of_mem _ hx) _
    
#align finset.prod_fiberwise_le_prod_of_one_le_prod_fiber' Finset.prod_fiberwise_le_prod_of_one_le_prod_fiber'
#align finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg Finset.sum_fiberwise_le_sum_of_sum_fiber_nonneg

/- warning: finset.prod_le_prod_fiberwise_of_prod_fiber_le_one' -> Finset.prod_le_prod_fiberwise_of_prod_fiber_le_one' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {s : Finset.{u1} ι} {ι' : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} ι'] {t : Finset.{u3} ι'} {g : ι -> ι'} {f : ι -> N}, (forall (y : ι'), (Not (Membership.Mem.{u3, u3} ι' (Finset.{u3} ι') (Finset.hasMem.{u3} ι') y t)) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) (Finset.filter.{u1} ι (fun (x : ι) => Eq.{succ u3} ι' (g x) y) (fun (a : ι) => _inst_3 (g a) y) s) (fun (x : ι) => f x)) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))))) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (x : ι) => f x)) (Finset.prod.{u2, u3} N ι' (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) t (fun (y : ι') => Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) (Finset.filter.{u1} ι (fun (x : ι) => Eq.{succ u3} ι' (g x) y) (fun (a : ι) => _inst_3 (g a) y) s) (fun (x : ι) => f x))))
but is expected to have type
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_2 : OrderedCommMonoid.{u2} N] {s : Finset.{u1} ι} {ι' : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} ι'] {t : Finset.{u3} ι'} {g : ι -> ι'} {f : ι -> N}, (forall (y : ι'), (Not (Membership.mem.{u3, u3} ι' (Finset.{u3} ι') (Finset.instMembershipFinset.{u3} ι') y t)) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) (Finset.filter.{u1} ι (fun (x : ι) => Eq.{succ u3} ι' (g x) y) (fun (a : ι) => _inst_3 (g a) y) s) (fun (x : ι) => f x)) (OfNat.ofNat.{u2} N 1 (One.toOfNat1.{u2} N (Monoid.toOne.{u2} N (CommMonoid.toMonoid.{u2} N (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2))))))) -> (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N (OrderedCommMonoid.toPartialOrder.{u2} N _inst_2))) (Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) s (fun (x : ι) => f x)) (Finset.prod.{u2, u3} N ι' (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) t (fun (y : ι') => Finset.prod.{u2, u1} N ι (OrderedCommMonoid.toCommMonoid.{u2} N _inst_2) (Finset.filter.{u1} ι (fun (x : ι) => Eq.{succ u3} ι' (g x) y) (fun (a : ι) => _inst_3 (g a) y) s) (fun (x : ι) => f x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_le_prod_fiberwise_of_prod_fiber_le_one' Finset.prod_le_prod_fiberwise_of_prod_fiber_le_one'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ∉ » t) -/
@[to_additive sum_le_sum_fiberwise_of_sum_fiber_nonpos]
theorem prod_le_prod_fiberwise_of_prod_fiber_le_one' {t : Finset ι'} {g : ι → ι'} {f : ι → N}
    (h : ∀ (y) (_ : y ∉ t), (∏ x in s.filterₓ fun x => g x = y, f x) ≤ 1) :
    (∏ x in s, f x) ≤ ∏ y in t, ∏ x in s.filterₓ fun x => g x = y, f x :=
  @prod_fiberwise_le_prod_of_one_le_prod_fiber' _ Nᵒᵈ _ _ _ _ _ _ _ h
#align finset.prod_le_prod_fiberwise_of_prod_fiber_le_one' Finset.prod_le_prod_fiberwise_of_prod_fiber_le_one'
#align finset.sum_le_sum_fiberwise_of_sum_fiber_nonpos Finset.sum_le_sum_fiberwise_of_sum_fiber_nonpos

end OrderedCommMonoid

/- warning: finset.abs_sum_le_sum_abs -> Finset.abs_sum_le_sum_abs is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} G] (f : ι -> G) (s : Finset.{u1} ι), LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1)))) (Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_1))))) (Finset.sum.{u2, u1} G ι (AddCommGroup.toAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))) s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} G ι (AddCommGroup.toAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))) s (fun (i : ι) => Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_1))))) (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} G] (f : ι -> G) (s : Finset.{u1} ι), LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1)))) (Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (NegZeroClass.toNeg.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (SubtractionCommMonoid.toSubtractionMonoid.{u2} G (AddCommGroup.toDivisionAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))))))) (SemilatticeSup.toSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (DistribLattice.toLattice.{u2} G (instDistribLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_1)))))) (Finset.sum.{u2, u1} G ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} G (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} G (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} G _inst_1))) s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} G ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} G (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} G (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} G _inst_1))) s (fun (i : ι) => Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (NegZeroClass.toNeg.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (SubtractionCommMonoid.toSubtractionMonoid.{u2} G (AddCommGroup.toDivisionAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))))))) (SemilatticeSup.toSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (DistribLattice.toLattice.{u2} G (instDistribLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_1)))))) (f i)))
Case conversion may be inaccurate. Consider using '#align finset.abs_sum_le_sum_abs Finset.abs_sum_le_sum_absₓ'. -/
theorem abs_sum_le_sum_abs {G : Type _} [LinearOrderedAddCommGroup G] (f : ι → G) (s : Finset ι) :
    |∑ i in s, f i| ≤ ∑ i in s, |f i| :=
  le_sum_of_subadditive _ abs_zero abs_add s f
#align finset.abs_sum_le_sum_abs Finset.abs_sum_le_sum_abs

/- warning: finset.abs_sum_of_nonneg -> Finset.abs_sum_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} G] {f : ι -> G} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1)))) (OfNat.ofNat.{u2} G 0 (OfNat.mk.{u2} G 0 (Zero.zero.{u2} G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1)))))))))) (f i))) -> (Eq.{succ u2} G (Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_1))))) (Finset.sum.{u2, u1} G ι (AddCommGroup.toAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))) s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} G ι (AddCommGroup.toAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} G] {f : ι -> G} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1)))) (OfNat.ofNat.{u2} G 0 (Zero.toOfNat0.{u2} G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (SubtractionCommMonoid.toSubtractionMonoid.{u2} G (AddCommGroup.toDivisionAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))))))))) (f i))) -> (Eq.{succ u2} G (Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (NegZeroClass.toNeg.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (SubtractionCommMonoid.toSubtractionMonoid.{u2} G (AddCommGroup.toDivisionAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))))))) (SemilatticeSup.toSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (DistribLattice.toLattice.{u2} G (instDistribLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_1)))))) (Finset.sum.{u2, u1} G ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} G (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} G (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} G _inst_1))) s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} G ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} G (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} G (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} G _inst_1))) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.abs_sum_of_nonneg Finset.abs_sum_of_nonnegₓ'. -/
theorem abs_sum_of_nonneg {G : Type _} [LinearOrderedAddCommGroup G] {f : ι → G} {s : Finset ι}
    (hf : ∀ i ∈ s, 0 ≤ f i) : |∑ i : ι in s, f i| = ∑ i : ι in s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg hf)]
#align finset.abs_sum_of_nonneg Finset.abs_sum_of_nonneg

/- warning: finset.abs_sum_of_nonneg' -> Finset.abs_sum_of_nonneg' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} G] {f : ι -> G} {s : Finset.{u1} ι}, (forall (i : ι), LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1)))) (OfNat.ofNat.{u2} G 0 (OfNat.mk.{u2} G 0 (Zero.zero.{u2} G (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1)))))))))) (f i)) -> (Eq.{succ u2} G (Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (SubNegMonoid.toHasNeg.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))))) (SemilatticeSup.toHasSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (LinearOrder.toLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_1))))) (Finset.sum.{u2, u1} G ι (AddCommGroup.toAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))) s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} G ι (AddCommGroup.toAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u2} G] {f : ι -> G} {s : Finset.{u1} ι}, (forall (i : ι), LE.le.{u2} G (Preorder.toLE.{u2} G (PartialOrder.toPreorder.{u2} G (OrderedAddCommGroup.toPartialOrder.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1)))) (OfNat.ofNat.{u2} G 0 (Zero.toOfNat0.{u2} G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (SubtractionCommMonoid.toSubtractionMonoid.{u2} G (AddCommGroup.toDivisionAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))))))))) (f i)) -> (Eq.{succ u2} G (Abs.abs.{u2} G (Neg.toHasAbs.{u2} G (NegZeroClass.toNeg.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (SubtractionCommMonoid.toSubtractionMonoid.{u2} G (AddCommGroup.toDivisionAddCommMonoid.{u2} G (OrderedAddCommGroup.toAddCommGroup.{u2} G (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} G _inst_1))))))) (SemilatticeSup.toSup.{u2} G (Lattice.toSemilatticeSup.{u2} G (DistribLattice.toLattice.{u2} G (instDistribLattice.{u2} G (LinearOrderedAddCommGroup.toLinearOrder.{u2} G _inst_1)))))) (Finset.sum.{u2, u1} G ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} G (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} G (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} G _inst_1))) s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} G ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} G (LinearOrderedCancelAddCommMonoid.toOrderedCancelAddCommMonoid.{u2} G (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} G _inst_1))) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.abs_sum_of_nonneg' Finset.abs_sum_of_nonneg'ₓ'. -/
theorem abs_sum_of_nonneg' {G : Type _} [LinearOrderedAddCommGroup G] {f : ι → G} {s : Finset ι}
    (hf : ∀ i, 0 ≤ f i) : |∑ i : ι in s, f i| = ∑ i : ι in s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg' hf)]
#align finset.abs_sum_of_nonneg' Finset.abs_sum_of_nonneg'

/- warning: finset.abs_prod -> Finset.abs_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : LinearOrderedCommRing.{u2} R] {f : ι -> R} {s : Finset.{u1} ι}, Eq.{succ u2} R (Abs.abs.{u2} R (Neg.toHasAbs.{u2} R (SubNegMonoid.toHasNeg.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R _inst_1)))))))) (SemilatticeSup.toHasSup.{u2} R (Lattice.toSemilatticeSup.{u2} R (LinearOrder.toLattice.{u2} R (LinearOrderedRing.toLinearOrder.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R _inst_1)))))) (Finset.prod.{u2, u1} R ι (LinearOrderedCommRing.toCommMonoid.{u2} R _inst_1) s (fun (x : ι) => f x))) (Finset.prod.{u2, u1} R ι (LinearOrderedCommRing.toCommMonoid.{u2} R _inst_1) s (fun (x : ι) => Abs.abs.{u2} R (Neg.toHasAbs.{u2} R (SubNegMonoid.toHasNeg.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R _inst_1)))))))) (SemilatticeSup.toHasSup.{u2} R (Lattice.toSemilatticeSup.{u2} R (LinearOrder.toLattice.{u2} R (LinearOrderedRing.toLinearOrder.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R _inst_1)))))) (f x)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : LinearOrderedCommRing.{u2} R] {f : ι -> R} {s : Finset.{u1} ι}, Eq.{succ u2} R (Abs.abs.{u2} R (Neg.toHasAbs.{u2} R (Ring.toNeg.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R _inst_1)))) (SemilatticeSup.toSup.{u2} R (Lattice.toSemilatticeSup.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R (LinearOrderedRing.toLinearOrder.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R _inst_1))))))) (Finset.prod.{u2, u1} R ι (LinearOrderedCommRing.toCommMonoid.{u2} R _inst_1) s (fun (x : ι) => f x))) (Finset.prod.{u2, u1} R ι (LinearOrderedCommRing.toCommMonoid.{u2} R _inst_1) s (fun (x : ι) => Abs.abs.{u2} R (Neg.toHasAbs.{u2} R (Ring.toNeg.{u2} R (StrictOrderedRing.toRing.{u2} R (LinearOrderedRing.toStrictOrderedRing.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R _inst_1)))) (SemilatticeSup.toSup.{u2} R (Lattice.toSemilatticeSup.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R (LinearOrderedRing.toLinearOrder.{u2} R (LinearOrderedCommRing.toLinearOrderedRing.{u2} R _inst_1))))))) (f x)))
Case conversion may be inaccurate. Consider using '#align finset.abs_prod Finset.abs_prodₓ'. -/
theorem abs_prod {R : Type _} [LinearOrderedCommRing R] {f : ι → R} {s : Finset ι} :
    |∏ x in s, f x| = ∏ x in s, |f x| :=
  (absHom.toMonoidHom : R →* R).map_prod _ _
#align finset.abs_prod Finset.abs_prod

section Pigeonhole

variable [DecidableEq β]

/- warning: finset.card_le_mul_card_image_of_maps_to -> Finset.card_le_mul_card_image_of_maps_to is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} {s : Finset.{u1} α} {t : Finset.{u2} β}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (f a) t)) -> (forall (n : Nat), (forall (a : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a t) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α (Finset.filter.{u1} α (fun (x : α) => Eq.{succ u2} β (f x) a) (fun (a_1 : α) => _inst_1 (f a_1) a) s)) n)) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α s) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n (Finset.card.{u2} β t))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} {s : Finset.{u2} α} {t : Finset.{u1} β}, (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (f a) t)) -> (forall (n : Nat), (forall (a : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) a t) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} α (Finset.filter.{u2} α (fun (x : α) => Eq.{succ u1} β (f x) a) (fun (a_1 : α) => _inst_1 (f a_1) a) s)) n)) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} α s) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n (Finset.card.{u1} β t))))
Case conversion may be inaccurate. Consider using '#align finset.card_le_mul_card_image_of_maps_to Finset.card_le_mul_card_image_of_maps_toₓ'. -/
theorem card_le_mul_card_image_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ a ∈ t, (s.filterₓ fun x => f x = a).card ≤ n) :
    s.card ≤ n * t.card :=
  calc
    s.card = ∑ a in t, (s.filterₓ fun x => f x = a).card := card_eq_sum_card_fiberwise Hf
    _ ≤ ∑ _ in t, n := (sum_le_sum hn)
    _ = _ := by simp [mul_comm]
    
#align finset.card_le_mul_card_image_of_maps_to Finset.card_le_mul_card_image_of_maps_to

/- warning: finset.card_le_mul_card_image -> Finset.card_le_mul_card_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} (s : Finset.{u1} α) (n : Nat), (forall (a : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α (Finset.filter.{u1} α (fun (x : α) => Eq.{succ u2} β (f x) a) (fun (a_1 : α) => _inst_1 (f a_1) a) s)) n)) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α s) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n (Finset.card.{u2} β (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} (s : Finset.{u2} α) (n : Nat), (forall (a : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) a (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} α (Finset.filter.{u2} α (fun (x : α) => Eq.{succ u1} β (f x) a) (fun (a_1 : α) => _inst_1 (f a_1) a) s)) n)) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} α s) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n (Finset.card.{u1} β (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s))))
Case conversion may be inaccurate. Consider using '#align finset.card_le_mul_card_image Finset.card_le_mul_card_imageₓ'. -/
theorem card_le_mul_card_image {f : α → β} (s : Finset α) (n : ℕ)
    (hn : ∀ a ∈ s.image f, (s.filterₓ fun x => f x = a).card ≤ n) : s.card ≤ n * (s.image f).card :=
  card_le_mul_card_image_of_maps_to (fun x => mem_image_of_mem _) n hn
#align finset.card_le_mul_card_image Finset.card_le_mul_card_image

/- warning: finset.mul_card_image_le_card_of_maps_to -> Finset.mul_card_image_le_card_of_maps_to is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} {s : Finset.{u1} α} {t : Finset.{u2} β}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (f a) t)) -> (forall (n : Nat), (forall (a : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a t) -> (LE.le.{0} Nat Nat.hasLe n (Finset.card.{u1} α (Finset.filter.{u1} α (fun (x : α) => Eq.{succ u2} β (f x) a) (fun (a_1 : α) => _inst_1 (f a_1) a) s)))) -> (LE.le.{0} Nat Nat.hasLe (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n (Finset.card.{u2} β t)) (Finset.card.{u1} α s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} {s : Finset.{u2} α} {t : Finset.{u1} β}, (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (f a) t)) -> (forall (n : Nat), (forall (a : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) a t) -> (LE.le.{0} Nat instLENat n (Finset.card.{u2} α (Finset.filter.{u2} α (fun (x : α) => Eq.{succ u1} β (f x) a) (fun (a_1 : α) => _inst_1 (f a_1) a) s)))) -> (LE.le.{0} Nat instLENat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n (Finset.card.{u1} β t)) (Finset.card.{u2} α s)))
Case conversion may be inaccurate. Consider using '#align finset.mul_card_image_le_card_of_maps_to Finset.mul_card_image_le_card_of_maps_toₓ'. -/
theorem mul_card_image_le_card_of_maps_to {f : α → β} {s : Finset α} {t : Finset β}
    (Hf : ∀ a ∈ s, f a ∈ t) (n : ℕ) (hn : ∀ a ∈ t, n ≤ (s.filterₓ fun x => f x = a).card) :
    n * t.card ≤ s.card :=
  calc
    n * t.card = ∑ _ in t, n := by simp [mul_comm]
    _ ≤ ∑ a in t, (s.filterₓ fun x => f x = a).card := (sum_le_sum hn)
    _ = s.card := by rw [← card_eq_sum_card_fiberwise Hf]
    
#align finset.mul_card_image_le_card_of_maps_to Finset.mul_card_image_le_card_of_maps_to

/- warning: finset.mul_card_image_le_card -> Finset.mul_card_image_le_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} (s : Finset.{u1} α) (n : Nat), (forall (a : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) -> (LE.le.{0} Nat Nat.hasLe n (Finset.card.{u1} α (Finset.filter.{u1} α (fun (x : α) => Eq.{succ u2} β (f x) a) (fun (a_1 : α) => _inst_1 (f a_1) a) s)))) -> (LE.le.{0} Nat Nat.hasLe (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) n (Finset.card.{u2} β (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s))) (Finset.card.{u1} α s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} (s : Finset.{u2} α) (n : Nat), (forall (a : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) a (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) -> (LE.le.{0} Nat instLENat n (Finset.card.{u2} α (Finset.filter.{u2} α (fun (x : α) => Eq.{succ u1} β (f x) a) (fun (a_1 : α) => _inst_1 (f a_1) a) s)))) -> (LE.le.{0} Nat instLENat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) n (Finset.card.{u1} β (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s))) (Finset.card.{u2} α s))
Case conversion may be inaccurate. Consider using '#align finset.mul_card_image_le_card Finset.mul_card_image_le_cardₓ'. -/
theorem mul_card_image_le_card {f : α → β} (s : Finset α) (n : ℕ)
    (hn : ∀ a ∈ s.image f, n ≤ (s.filterₓ fun x => f x = a).card) : n * (s.image f).card ≤ s.card :=
  mul_card_image_le_card_of_maps_to (fun x => mem_image_of_mem _) n hn
#align finset.mul_card_image_le_card Finset.mul_card_image_le_card

end Pigeonhole

section DoubleCounting

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

#print Finset.sum_card_inter_le /-
/-- If every element belongs to at most `n` finsets, then the sum of their sizes is at most `n`
times how many they are. -/
theorem sum_card_inter_le (h : ∀ a ∈ s, (B.filterₓ <| (· ∈ ·) a).card ≤ n) :
    (∑ t in B, (s ∩ t).card) ≤ s.card * n :=
  by
  refine' le_trans _ (s.sum_le_card_nsmul _ _ h)
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le
#align finset.sum_card_inter_le Finset.sum_card_inter_le
-/

#print Finset.sum_card_le /-
/-- If every element belongs to at most `n` finsets, then the sum of their sizes is at most `n`
times how many they are. -/
theorem sum_card_le [Fintype α] (h : ∀ a, (B.filterₓ <| (· ∈ ·) a).card ≤ n) :
    (∑ s in B, s.card) ≤ Fintype.card α * n :=
  calc
    (∑ s in B, s.card) = ∑ s in B, (univ ∩ s).card := by simp_rw [univ_inter]
    _ ≤ Fintype.card α * n := sum_card_inter_le fun a _ => h a
    
#align finset.sum_card_le Finset.sum_card_le
-/

#print Finset.le_sum_card_inter /-
/-- If every element belongs to at least `n` finsets, then the sum of their sizes is at least `n`
times how many they are. -/
theorem le_sum_card_inter (h : ∀ a ∈ s, n ≤ (B.filterₓ <| (· ∈ ·) a).card) :
    s.card * n ≤ ∑ t in B, (s ∩ t).card :=
  by
  apply (s.card_nsmul_le_sum _ _ h).trans
  simp_rw [← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm.le
#align finset.le_sum_card_inter Finset.le_sum_card_inter
-/

#print Finset.le_sum_card /-
/-- If every element belongs to at least `n` finsets, then the sum of their sizes is at least `n`
times how many they are. -/
theorem le_sum_card [Fintype α] (h : ∀ a, n ≤ (B.filterₓ <| (· ∈ ·) a).card) :
    Fintype.card α * n ≤ ∑ s in B, s.card :=
  calc
    Fintype.card α * n ≤ ∑ s in B, (univ ∩ s).card := le_sum_card_inter fun a _ => h a
    _ = ∑ s in B, s.card := by simp_rw [univ_inter]
    
#align finset.le_sum_card Finset.le_sum_card
-/

#print Finset.sum_card_inter /-
/-- If every element belongs to exactly `n` finsets, then the sum of their sizes is `n` times how
many they are. -/
theorem sum_card_inter (h : ∀ a ∈ s, (B.filterₓ <| (· ∈ ·) a).card = n) :
    (∑ t in B, (s ∩ t).card) = s.card * n :=
  (sum_card_inter_le fun a ha => (h a ha).le).antisymm (le_sum_card_inter fun a ha => (h a ha).ge)
#align finset.sum_card_inter Finset.sum_card_inter
-/

#print Finset.sum_card /-
/-- If every element belongs to exactly `n` finsets, then the sum of their sizes is `n` times how
many they are. -/
theorem sum_card [Fintype α] (h : ∀ a, (B.filterₓ <| (· ∈ ·) a).card = n) :
    (∑ s in B, s.card) = Fintype.card α * n := by
  simp_rw [Fintype.card, ← sum_card_inter fun a _ => h a, univ_inter]
#align finset.sum_card Finset.sum_card
-/

/- warning: finset.card_le_card_bUnion -> Finset.card_le_card_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {s : Finset.{u1} ι} {f : ι -> (Finset.{u2} α)}, (Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} α) ι (Finset.partialOrder.{u2} α) (Finset.orderBot.{u2} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) s) f) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Finset.Nonempty.{u2} α (f i))) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} ι s) (Finset.card.{u2} α (Finset.bunionᵢ.{u1, u2} ι α (fun (a : α) (b : α) => _inst_1 a b) s f)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u2} ι} {f : ι -> (Finset.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} α) ι (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.toSet.{u2} ι s) f) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Finset.Nonempty.{u1} α (f i))) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} ι s) (Finset.card.{u1} α (Finset.bunionᵢ.{u2, u1} ι α (fun (a : α) (b : α) => _inst_1 a b) s f)))
Case conversion may be inaccurate. Consider using '#align finset.card_le_card_bUnion Finset.card_le_card_bunionᵢₓ'. -/
theorem card_le_card_bunionᵢ {s : Finset ι} {f : ι → Finset α} (hs : (s : Set ι).PairwiseDisjoint f)
    (hf : ∀ i ∈ s, (f i).Nonempty) : s.card ≤ (s.bunionᵢ f).card :=
  by
  rw [card_bUnion hs, card_eq_sum_ones]
  exact sum_le_sum fun i hi => (hf i hi).card_pos
#align finset.card_le_card_bUnion Finset.card_le_card_bunionᵢ

/- warning: finset.card_le_card_bUnion_add_card_fiber -> Finset.card_le_card_bunionᵢ_add_card_fiber is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {s : Finset.{u1} ι} {f : ι -> (Finset.{u2} α)}, (Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} α) ι (Finset.partialOrder.{u2} α) (Finset.orderBot.{u2} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) s) f) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} ι s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u2} α (Finset.bunionᵢ.{u1, u2} ι α (fun (a : α) (b : α) => _inst_1 a b) s f)) (Finset.card.{u1} ι (Finset.filter.{u1} ι (fun (i : ι) => Eq.{succ u2} (Finset.{u2} α) (f i) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.hasEmptyc.{u2} α))) (fun (a : ι) => Finset.decidableEq.{u2} α (fun (a : α) (b : α) => _inst_1 a b) (f a) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.hasEmptyc.{u2} α))) s))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u2} ι} {f : ι -> (Finset.{u1} α)}, (Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} α) ι (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.toSet.{u2} ι s) f) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} ι s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} α (Finset.bunionᵢ.{u2, u1} ι α (fun (a : α) (b : α) => _inst_1 a b) s f)) (Finset.card.{u2} ι (Finset.filter.{u2} ι (fun (i : ι) => Eq.{succ u1} (Finset.{u1} α) (f i) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) (fun (a : ι) => Finset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (f a) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) s))))
Case conversion may be inaccurate. Consider using '#align finset.card_le_card_bUnion_add_card_fiber Finset.card_le_card_bunionᵢ_add_card_fiberₓ'. -/
theorem card_le_card_bunionᵢ_add_card_fiber {s : Finset ι} {f : ι → Finset α}
    (hs : (s : Set ι).PairwiseDisjoint f) :
    s.card ≤ (s.bunionᵢ f).card + (s.filterₓ fun i => f i = ∅).card :=
  by
  rw [← Finset.filter_card_add_filter_neg_card_eq_card fun i => f i = ∅, add_comm]
  exact
    add_le_add_right
      ((card_le_card_bUnion (hs.subset <| filter_subset _ _) fun i hi =>
            nonempty_of_ne_empty <| (mem_filter.1 hi).2).trans <|
        card_le_of_subset <| bUnion_subset_bUnion_of_subset_left _ <| filter_subset _ _)
      _
#align finset.card_le_card_bUnion_add_card_fiber Finset.card_le_card_bunionᵢ_add_card_fiber

/- warning: finset.card_le_card_bUnion_add_one -> Finset.card_le_card_bunionᵢ_add_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {s : Finset.{u1} ι} {f : ι -> (Finset.{u2} α)}, (Function.Injective.{succ u1, succ u2} ι (Finset.{u2} α) f) -> (Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} α) ι (Finset.partialOrder.{u2} α) (Finset.orderBot.{u2} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) s) f) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} ι s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u2} α (Finset.bunionᵢ.{u1, u2} ι α (fun (a : α) (b : α) => _inst_1 a b) s f)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u2} ι} {f : ι -> (Finset.{u1} α)}, (Function.Injective.{succ u2, succ u1} ι (Finset.{u1} α) f) -> (Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} α) ι (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.toSet.{u2} ι s) f) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} ι s) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} α (Finset.bunionᵢ.{u2, u1} ι α (fun (a : α) (b : α) => _inst_1 a b) s f)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))
Case conversion may be inaccurate. Consider using '#align finset.card_le_card_bUnion_add_one Finset.card_le_card_bunionᵢ_add_oneₓ'. -/
theorem card_le_card_bunionᵢ_add_one {s : Finset ι} {f : ι → Finset α} (hf : Injective f)
    (hs : (s : Set ι).PairwiseDisjoint f) : s.card ≤ (s.bunionᵢ f).card + 1 :=
  (card_le_card_bunionᵢ_add_card_fiber hs).trans <|
    add_le_add_left
      (card_le_one.2 fun i hi j hj => hf <| (mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm) _
#align finset.card_le_card_bUnion_add_one Finset.card_le_card_bunionᵢ_add_one

end DoubleCounting

section CanonicallyOrderedMonoid

variable [CanonicallyOrderedMonoid M] {f : ι → M} {s t : Finset ι}

/- warning: finset.prod_eq_one_iff' -> Finset.prod_eq_one_iff' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : CanonicallyOrderedMonoid.{u2} M] {f : ι -> M} {s : Finset.{u1} ι}, Iff (Eq.{succ u2} M (Finset.prod.{u2, u1} M ι (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)) s (fun (x : ι) => f x)) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))))))))) (forall (x : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x s) -> (Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))))))))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : CanonicallyOrderedMonoid.{u2} M] {f : ι -> M} {s : Finset.{u1} ι}, Iff (Eq.{succ u2} M (Finset.prod.{u2, u1} M ι (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)) s (fun (x : ι) => f x)) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))))))) (forall (x : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s) -> (Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_one_iff' Finset.prod_eq_one_iff'ₓ'. -/
@[simp, to_additive sum_eq_zero_iff]
theorem prod_eq_one_iff' : (∏ x in s, f x) = 1 ↔ ∀ x ∈ s, f x = 1 :=
  prod_eq_one_iff_of_one_le' fun x hx => one_le (f x)
#align finset.prod_eq_one_iff' Finset.prod_eq_one_iff'
#align finset.sum_eq_zero_iff Finset.sum_eq_zero_iff

/- warning: finset.prod_le_prod_of_subset' -> Finset.prod_le_prod_of_subset' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : CanonicallyOrderedMonoid.{u2} M] {f : ι -> M} {s : Finset.{u1} ι} {t : Finset.{u1} ι}, (HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.hasSubset.{u1} ι) s t) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)))) (Finset.prod.{u2, u1} M ι (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)) s (fun (x : ι) => f x)) (Finset.prod.{u2, u1} M ι (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)) t (fun (x : ι) => f x)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} M] {f : ι -> M} {s : Finset.{u2} ι} {t : Finset.{u2} ι}, (HasSubset.Subset.{u2} (Finset.{u2} ι) (Finset.instHasSubsetFinset.{u2} ι) s t) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)))) (Finset.prod.{u1, u2} M ι (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)) s (fun (x : ι) => f x)) (Finset.prod.{u1, u2} M ι (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)) t (fun (x : ι) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_le_prod_of_subset' Finset.prod_le_prod_of_subset'ₓ'. -/
@[to_additive sum_le_sum_of_subset]
theorem prod_le_prod_of_subset' (h : s ⊆ t) : (∏ x in s, f x) ≤ ∏ x in t, f x :=
  prod_le_prod_of_subset_of_one_le' h fun x h₁ h₂ => one_le _
#align finset.prod_le_prod_of_subset' Finset.prod_le_prod_of_subset'
#align finset.sum_le_sum_of_subset Finset.sum_le_sum_of_subset

/- warning: finset.prod_mono_set' -> Finset.prod_mono_set' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : CanonicallyOrderedMonoid.{u2} M] (f : ι -> M), Monotone.{u1, u2} (Finset.{u1} ι) M (PartialOrder.toPreorder.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι)) (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))) (fun (s : Finset.{u1} ι) => Finset.prod.{u2, u1} M ι (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)) s (fun (x : ι) => f x))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} M] (f : ι -> M), Monotone.{u2, u1} (Finset.{u2} ι) M (PartialOrder.toPreorder.{u2} (Finset.{u2} ι) (Finset.partialOrder.{u2} ι)) (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))) (fun (s : Finset.{u2} ι) => Finset.prod.{u1, u2} M ι (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)) s (fun (x : ι) => f x))
Case conversion may be inaccurate. Consider using '#align finset.prod_mono_set' Finset.prod_mono_set'ₓ'. -/
@[to_additive sum_mono_set]
theorem prod_mono_set' (f : ι → M) : Monotone fun s => ∏ x in s, f x := fun s₁ s₂ hs =>
  prod_le_prod_of_subset' hs
#align finset.prod_mono_set' Finset.prod_mono_set'
#align finset.sum_mono_set Finset.sum_mono_set

/- warning: finset.prod_le_prod_of_ne_one' -> Finset.prod_le_prod_of_ne_one' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : CanonicallyOrderedMonoid.{u2} M] {f : ι -> M} {s : Finset.{u1} ι} {t : Finset.{u1} ι}, (forall (x : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x s) -> (Ne.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1))))))))) -> (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x t)) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCommMonoid.toPartialOrder.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)))) (Finset.prod.{u2, u1} M ι (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)) s (fun (x : ι) => f x)) (Finset.prod.{u2, u1} M ι (OrderedCommMonoid.toCommMonoid.{u2} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u2} M _inst_1)) t (fun (x : ι) => f x)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} M] {f : ι -> M} {s : Finset.{u2} ι} {t : Finset.{u2} ι}, (forall (x : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x s) -> (Ne.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))))) -> (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) x t)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)))) (Finset.prod.{u1, u2} M ι (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)) s (fun (x : ι) => f x)) (Finset.prod.{u1, u2} M ι (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)) t (fun (x : ι) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_le_prod_of_ne_one' Finset.prod_le_prod_of_ne_one'ₓ'. -/
@[to_additive sum_le_sum_of_ne_zero]
theorem prod_le_prod_of_ne_one' (h : ∀ x ∈ s, f x ≠ 1 → x ∈ t) : (∏ x in s, f x) ≤ ∏ x in t, f x :=
  by
  classical calc
      (∏ x in s, f x) =
          (∏ x in s.filter fun x => f x = 1, f x) * ∏ x in s.filter fun x => f x ≠ 1, f x :=
        by
        rw [← prod_union, filter_union_filter_neg_eq] <;>
          exact disjoint_filter.2 fun _ _ h n_h => n_h h
      _ ≤ ∏ x in t, f x :=
        mul_le_of_le_one_of_le
          (prod_le_one' <| by simp only [mem_filter, and_imp] <;> exact fun _ _ => le_of_eq)
          (prod_le_prod_of_subset' <| by simpa only [subset_iff, mem_filter, and_imp] )
      
#align finset.prod_le_prod_of_ne_one' Finset.prod_le_prod_of_ne_one'
#align finset.sum_le_sum_of_ne_zero Finset.sum_le_sum_of_ne_zero

end CanonicallyOrderedMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid M] {f g : ι → M} {s t : Finset ι}

/- warning: finset.prod_lt_prod' -> Finset.prod_lt_prod' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : OrderedCancelCommMonoid.{u2} M] {f : ι -> M} {g : ι -> M} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (f i) (g i))) -> (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (f i) (g i)))) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (i : ι) => g i)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} M] {f : ι -> M} {g : ι -> M} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (f i) (g i))) -> (Exists.{succ u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (f i) (g i)))) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (i : ι) => f i)) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_lt_prod' Finset.prod_lt_prod'ₓ'. -/
@[to_additive sum_lt_sum]
theorem prod_lt_prod' (Hle : ∀ i ∈ s, f i ≤ g i) (Hlt : ∃ i ∈ s, f i < g i) :
    (∏ i in s, f i) < ∏ i in s, g i := by
  classical
    rcases Hlt with ⟨i, hi, hlt⟩
    rw [← insert_erase hi, prod_insert (not_mem_erase _ _), prod_insert (not_mem_erase _ _)]
    exact mul_lt_mul_of_lt_of_le hlt (prod_le_prod' fun j hj => Hle j <| mem_of_mem_erase hj)
#align finset.prod_lt_prod' Finset.prod_lt_prod'
#align finset.sum_lt_sum Finset.sum_lt_sum

/- warning: finset.prod_lt_prod_of_nonempty' -> Finset.prod_lt_prod_of_nonempty' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : OrderedCancelCommMonoid.{u2} M] {f : ι -> M} {g : ι -> M} {s : Finset.{u1} ι}, (Finset.Nonempty.{u1} ι s) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (f i) (g i))) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (i : ι) => g i)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} M] {f : ι -> M} {g : ι -> M} {s : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι s) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (f i) (g i))) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (i : ι) => f i)) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_lt_prod_of_nonempty' Finset.prod_lt_prod_of_nonempty'ₓ'. -/
@[to_additive sum_lt_sum_of_nonempty]
theorem prod_lt_prod_of_nonempty' (hs : s.Nonempty) (Hlt : ∀ i ∈ s, f i < g i) :
    (∏ i in s, f i) < ∏ i in s, g i := by
  apply prod_lt_prod'
  · intro i hi
    apply le_of_lt (Hlt i hi)
  cases' hs with i hi
  exact ⟨i, hi, Hlt i hi⟩
#align finset.prod_lt_prod_of_nonempty' Finset.prod_lt_prod_of_nonempty'
#align finset.sum_lt_sum_of_nonempty Finset.sum_lt_sum_of_nonempty

/- warning: finset.prod_lt_prod_of_subset' -> Finset.prod_lt_prod_of_subset' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : OrderedCancelCommMonoid.{u2} M] {f : ι -> M} {s : Finset.{u1} ι} {t : Finset.{u1} ι}, (HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.hasSubset.{u1} ι) s t) -> (forall {i : ι}, (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i t) -> (Not (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s)) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))) (f i)) -> (forall (j : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) j t) -> (Not (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) j s)) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))) (f j))) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (j : ι) => f j)) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) t (fun (j : ι) => f j))))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} M] {f : ι -> M} {s : Finset.{u2} ι} {t : Finset.{u2} ι}, (HasSubset.Subset.{u2} (Finset.{u2} ι) (Finset.instHasSubsetFinset.{u2} ι) s t) -> (forall {i : ι}, (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i t) -> (Not (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s)) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))) (f i)) -> (forall (j : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) j t) -> (Not (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) j s)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))) (f j))) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (j : ι) => f j)) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) t (fun (j : ι) => f j))))
Case conversion may be inaccurate. Consider using '#align finset.prod_lt_prod_of_subset' Finset.prod_lt_prod_of_subset'ₓ'. -/
@[to_additive sum_lt_sum_of_subset]
theorem prod_lt_prod_of_subset' (h : s ⊆ t) {i : ι} (ht : i ∈ t) (hs : i ∉ s) (hlt : 1 < f i)
    (hle : ∀ j ∈ t, j ∉ s → 1 ≤ f j) : (∏ j in s, f j) < ∏ j in t, f j := by
  classical calc
      (∏ j in s, f j) < ∏ j in insert i s, f j :=
        by
        rw [prod_insert hs]
        exact lt_mul_of_one_lt_left' (∏ j in s, f j) hlt
      _ ≤ ∏ j in t, f j := by
        apply prod_le_prod_of_subset_of_one_le'
        · simp [Finset.insert_subset, h, ht]
        · intro x hx h'x
          simp only [mem_insert, not_or] at h'x
          exact hle x hx h'x.2
      
#align finset.prod_lt_prod_of_subset' Finset.prod_lt_prod_of_subset'
#align finset.sum_lt_sum_of_subset Finset.sum_lt_sum_of_subset

/- warning: finset.single_lt_prod' -> Finset.single_lt_prod' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : OrderedCancelCommMonoid.{u2} M] {f : ι -> M} {s : Finset.{u1} ι} {i : ι} {j : ι}, (Ne.{succ u1} ι j i) -> (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) j s) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))) (f j)) -> (forall (k : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) k s) -> (Ne.{succ u1} ι k i) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))) (f k))) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (f i) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (k : ι) => f k)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} M] {f : ι -> M} {s : Finset.{u2} ι} {i : ι} {j : ι}, (Ne.{succ u2} ι j i) -> (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) j s) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))) (f j)) -> (forall (k : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) k s) -> (Ne.{succ u2} ι k i) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))) (f k))) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (f i) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (k : ι) => f k)))
Case conversion may be inaccurate. Consider using '#align finset.single_lt_prod' Finset.single_lt_prod'ₓ'. -/
@[to_additive single_lt_sum]
theorem single_lt_prod' {i j : ι} (hij : j ≠ i) (hi : i ∈ s) (hj : j ∈ s) (hlt : 1 < f j)
    (hle : ∀ k ∈ s, k ≠ i → 1 ≤ f k) : f i < ∏ k in s, f k :=
  calc
    f i = ∏ k in {i}, f k := prod_singleton.symm
    _ < ∏ k in s, f k :=
      prod_lt_prod_of_subset' (singleton_subset_iff.2 hi) hj (mt mem_singleton.1 hij) hlt
        fun k hks hki => hle k hks (mt mem_singleton.2 hki)
    
#align finset.single_lt_prod' Finset.single_lt_prod'
#align finset.single_lt_sum Finset.single_lt_sum

/- warning: finset.one_lt_prod -> Finset.one_lt_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : OrderedCancelCommMonoid.{u2} M] {f : ι -> M} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))) (f i))) -> (Finset.Nonempty.{u1} ι s) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} M] {f : ι -> M} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))) (f i))) -> (Finset.Nonempty.{u2} ι s) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.one_lt_prod Finset.one_lt_prodₓ'. -/
@[to_additive sum_pos]
theorem one_lt_prod (h : ∀ i ∈ s, 1 < f i) (hs : s.Nonempty) : 1 < ∏ i in s, f i :=
  lt_of_le_of_lt (by rw [prod_const_one]) <| prod_lt_prod_of_nonempty' hs h
#align finset.one_lt_prod Finset.one_lt_prod
#align finset.sum_pos Finset.sum_pos

/- warning: finset.prod_lt_one -> Finset.prod_lt_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : OrderedCancelCommMonoid.{u2} M] {f : ι -> M} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (f i) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))))) -> (Finset.Nonempty.{u1} ι s) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} M] {f : ι -> M} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (f i) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))))) -> (Finset.Nonempty.{u2} ι s) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (i : ι) => f i)) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_lt_one Finset.prod_lt_oneₓ'. -/
@[to_additive]
theorem prod_lt_one (h : ∀ i ∈ s, f i < 1) (hs : s.Nonempty) : (∏ i in s, f i) < 1 :=
  (prod_lt_prod_of_nonempty' hs h).trans_le (by rw [prod_const_one])
#align finset.prod_lt_one Finset.prod_lt_one
#align finset.sum_neg Finset.sum_neg

/- warning: finset.one_lt_prod' -> Finset.one_lt_prod' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : OrderedCancelCommMonoid.{u2} M] {f : ι -> M} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))) (f i))) -> (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))) (f i)))) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} M] {f : ι -> M} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))) (f i))) -> (Exists.{succ u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))) (f i)))) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.one_lt_prod' Finset.one_lt_prod'ₓ'. -/
@[to_additive sum_pos']
theorem one_lt_prod' (h : ∀ i ∈ s, 1 ≤ f i) (hs : ∃ i ∈ s, 1 < f i) : 1 < ∏ i in s, f i :=
  prod_const_one.symm.trans_lt <| prod_lt_prod' h hs
#align finset.one_lt_prod' Finset.one_lt_prod'
#align finset.sum_pos' Finset.sum_pos'

/- warning: finset.prod_lt_one' -> Finset.prod_lt_one' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : OrderedCancelCommMonoid.{u2} M] {f : ι -> M} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (f i) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))))) -> (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (f i) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1)))))))))))) -> (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M _inst_1))))))))))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} M] {f : ι -> M} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (f i) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))))) -> (Exists.{succ u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (f i) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1))))))))) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (i : ι) => f i)) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (RightCancelMonoid.toOne.{u1} M (CancelMonoid.toRightCancelMonoid.{u1} M (CancelCommMonoid.toCancelMonoid.{u1} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} M _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_lt_one' Finset.prod_lt_one'ₓ'. -/
@[to_additive]
theorem prod_lt_one' (h : ∀ i ∈ s, f i ≤ 1) (hs : ∃ i ∈ s, f i < 1) : (∏ i in s, f i) < 1 :=
  prod_const_one.le.trans_lt' <| prod_lt_prod' h hs
#align finset.prod_lt_one' Finset.prod_lt_one'
#align finset.sum_neg' Finset.sum_neg'

/- warning: finset.prod_eq_prod_iff_of_le -> Finset.prod_eq_prod_iff_of_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : OrderedCancelCommMonoid.{u2} M] {s : Finset.{u1} ι} {f : ι -> M} {g : ι -> M}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M _inst_1))) (f i) (g i))) -> (Iff (Eq.{succ u2} M (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M _inst_1) s (fun (i : ι) => g i))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Eq.{succ u2} M (f i) (g i))))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} M] {s : Finset.{u2} ι} {f : ι -> M} {g : ι -> M}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M _inst_1))) (f i) (g i))) -> (Iff (Eq.{succ u1} M (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (i : ι) => f i)) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M _inst_1) s (fun (i : ι) => g i))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Eq.{succ u1} M (f i) (g i))))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_prod_iff_of_le Finset.prod_eq_prod_iff_of_leₓ'. -/
@[to_additive]
theorem prod_eq_prod_iff_of_le {f g : ι → M} (h : ∀ i ∈ s, f i ≤ g i) :
    ((∏ i in s, f i) = ∏ i in s, g i) ↔ ∀ i ∈ s, f i = g i := by
  classical
    revert h
    refine'
      Finset.induction_on s (fun _ => ⟨fun _ _ => False.elim, fun _ => rfl⟩) fun a s ha ih H => _
    specialize ih fun i => H i ∘ Finset.mem_insert_of_mem
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.forall_mem_insert, ← ih]
    exact
      mul_eq_mul_iff_eq_and_eq (H a (s.mem_insert_self a))
        (Finset.prod_le_prod' fun i => H i ∘ Finset.mem_insert_of_mem)
#align finset.prod_eq_prod_iff_of_le Finset.prod_eq_prod_iff_of_le
#align finset.sum_eq_sum_iff_of_le Finset.sum_eq_sum_iff_of_le

end OrderedCancelCommMonoid

section LinearOrderedCancelCommMonoid

variable [LinearOrderedCancelCommMonoid M] {f g : ι → M} {s t : Finset ι}

/- warning: finset.exists_lt_of_prod_lt' -> Finset.exists_lt_of_prod_lt' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : LinearOrderedCancelCommMonoid.{u2} M] {f : ι -> M} {g : ι -> M} {s : Finset.{u1} ι}, (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)) s (fun (i : ι) => f i)) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)) s (fun (i : ι) => g i))) -> (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))) (f i) (g i))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : LinearOrderedCancelCommMonoid.{u2} M] {f : ι -> M} {g : ι -> M} {s : Finset.{u1} ι}, (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)) s (fun (i : ι) => f i)) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)) s (fun (i : ι) => g i))) -> (Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))) (f i) (g i))))
Case conversion may be inaccurate. Consider using '#align finset.exists_lt_of_prod_lt' Finset.exists_lt_of_prod_lt'ₓ'. -/
@[to_additive exists_lt_of_sum_lt]
theorem exists_lt_of_prod_lt' (Hlt : (∏ i in s, f i) < ∏ i in s, g i) : ∃ i ∈ s, f i < g i :=
  by
  contrapose! Hlt with Hle
  exact prod_le_prod' Hle
#align finset.exists_lt_of_prod_lt' Finset.exists_lt_of_prod_lt'
#align finset.exists_lt_of_sum_lt Finset.exists_lt_of_sum_lt

/- warning: finset.exists_le_of_prod_le' -> Finset.exists_le_of_prod_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : LinearOrderedCancelCommMonoid.{u2} M] {f : ι -> M} {g : ι -> M} {s : Finset.{u1} ι}, (Finset.Nonempty.{u1} ι s) -> (LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)) s (fun (i : ι) => f i)) (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)) s (fun (i : ι) => g i))) -> (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => LE.le.{u2} M (Preorder.toLE.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))) (f i) (g i))))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_1 : LinearOrderedCancelCommMonoid.{u1} M] {f : ι -> M} {g : ι -> M} {s : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι s) -> (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_1)))) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_1)) s (fun (i : ι) => f i)) (Finset.prod.{u1, u2} M ι (OrderedCancelCommMonoid.toCommMonoid.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_1)) s (fun (i : ι) => g i))) -> (Exists.{succ u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (LE.le.{u1} M (Preorder.toLE.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedCancelCommMonoid.toPartialOrder.{u1} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} M _inst_1)))) (f i) (g i))))
Case conversion may be inaccurate. Consider using '#align finset.exists_le_of_prod_le' Finset.exists_le_of_prod_le'ₓ'. -/
@[to_additive exists_le_of_sum_le]
theorem exists_le_of_prod_le' (hs : s.Nonempty) (Hle : (∏ i in s, f i) ≤ ∏ i in s, g i) :
    ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle with Hlt
  exact prod_lt_prod_of_nonempty' hs Hlt
#align finset.exists_le_of_prod_le' Finset.exists_le_of_prod_le'
#align finset.exists_le_of_sum_le Finset.exists_le_of_sum_le

/- warning: finset.exists_one_lt_of_prod_one_of_exists_ne_one' -> Finset.exists_one_lt_of_prod_one_of_exists_ne_one' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : LinearOrderedCancelCommMonoid.{u2} M] {s : Finset.{u1} ι} (f : ι -> M), (Eq.{succ u2} M (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)) s (fun (i : ι) => f i)) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1))))))))))) -> (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => Ne.{succ u2} M (f i) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1))))))))))))) -> (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (RightCancelMonoid.toMonoid.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))))))))) (f i))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : LinearOrderedCancelCommMonoid.{u2} M] {s : Finset.{u1} ι} (f : ι -> M), (Eq.{succ u2} M (Finset.prod.{u2, u1} M ι (OrderedCancelCommMonoid.toCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)) s (fun (i : ι) => f i)) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (RightCancelMonoid.toOne.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))))))) -> (Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (Ne.{succ u2} M (f i) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (RightCancelMonoid.toOne.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))))))))) -> (Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (LT.lt.{u2} M (Preorder.toLT.{u2} M (PartialOrder.toPreorder.{u2} M (OrderedCancelCommMonoid.toPartialOrder.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1)))) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (RightCancelMonoid.toOne.{u2} M (CancelMonoid.toRightCancelMonoid.{u2} M (CancelCommMonoid.toCancelMonoid.{u2} M (OrderedCancelCommMonoid.toCancelCommMonoid.{u2} M (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u2} M _inst_1))))))) (f i))))
Case conversion may be inaccurate. Consider using '#align finset.exists_one_lt_of_prod_one_of_exists_ne_one' Finset.exists_one_lt_of_prod_one_of_exists_ne_one'ₓ'. -/
@[to_additive exists_pos_of_sum_zero_of_exists_nonzero]
theorem exists_one_lt_of_prod_one_of_exists_ne_one' (f : ι → M) (h₁ : (∏ i in s, f i) = 1)
    (h₂ : ∃ i ∈ s, f i ≠ 1) : ∃ i ∈ s, 1 < f i :=
  by
  contrapose! h₁
  obtain ⟨i, m, i_ne⟩ : ∃ i ∈ s, f i ≠ 1 := h₂
  apply ne_of_lt
  calc
    (∏ j in s, f j) < ∏ j in s, 1 := prod_lt_prod' h₁ ⟨i, m, (h₁ i m).lt_of_ne i_ne⟩
    _ = 1 := prod_const_one
    
#align finset.exists_one_lt_of_prod_one_of_exists_ne_one' Finset.exists_one_lt_of_prod_one_of_exists_ne_one'
#align finset.exists_pos_of_sum_zero_of_exists_nonzero Finset.exists_pos_of_sum_zero_of_exists_nonzero

end LinearOrderedCancelCommMonoid

section OrderedCommSemiring

variable [OrderedCommSemiring R] {f g : ι → R} {s t : Finset ι}

open Classical

/- warning: finset.prod_nonneg -> Finset.prod_nonneg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : OrderedCommSemiring.{u2} R] {f : ι -> R} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))))))) (f i))) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))))))) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_1)) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_1 : OrderedCommSemiring.{u1} R] {f : ι -> R} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1))))) (f i))) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1))))) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1)) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_nonneg Finset.prod_nonnegₓ'. -/
-- this is also true for a ordered commutative multiplicative monoid with zero
theorem prod_nonneg (h0 : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i in s, f i :=
  prod_induction f (fun i => 0 ≤ i) (fun _ _ ha hb => mul_nonneg ha hb) zero_le_one h0
#align finset.prod_nonneg Finset.prod_nonneg

/- warning: finset.prod_le_prod -> Finset.prod_le_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : OrderedCommSemiring.{u2} R] {f : ι -> R} {g : ι -> R} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))))))) (f i))) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (f i) (g i))) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_1)) s (fun (i : ι) => f i)) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_1)) s (fun (i : ι) => g i)))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_1 : OrderedCommSemiring.{u1} R] {f : ι -> R} {g : ι -> R} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1))))) (f i))) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (f i) (g i))) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1)) s (fun (i : ι) => f i)) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1)) s (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_le_prod Finset.prod_le_prodₓ'. -/
/-- If all `f i`, `i ∈ s`, are nonnegative and each `f i` is less than or equal to `g i`, then the
product of `f i` is less than or equal to the product of `g i`. See also `finset.prod_le_prod'` for
the case of an ordered commutative multiplicative monoid. -/
theorem prod_le_prod (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    (∏ i in s, f i) ≤ ∏ i in s, g i :=
  by
  induction' s using Finset.induction with a s has ih h
  · simp
  · simp only [prod_insert has]
    apply mul_le_mul
    · exact h1 a (mem_insert_self a s)
    · apply ih (fun x H => h0 _ _) fun x H => h1 _ _ <;> exact mem_insert_of_mem H
    · apply prod_nonneg fun x H => h0 x (mem_insert_of_mem H)
    · apply le_trans (h0 a (mem_insert_self a s)) (h1 a (mem_insert_self a s))
#align finset.prod_le_prod Finset.prod_le_prod

/- warning: finset.prod_le_one -> Finset.prod_le_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : OrderedCommSemiring.{u2} R] {f : ι -> R} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))))))) (f i))) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (f i) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R (AddMonoidWithOne.toOne.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))))))))) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_1)) s (fun (i : ι) => f i)) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R (AddMonoidWithOne.toOne.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))))))))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_1 : OrderedCommSemiring.{u1} R] {f : ι -> R} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1))))) (f i))) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (f i) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1))))))) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1)) s (fun (i : ι) => f i)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_le_one Finset.prod_le_oneₓ'. -/
/-- If each `f i`, `i ∈ s` belongs to `[0, 1]`, then their product is less than or equal to one.
See also `finset.prod_le_one'` for the case of an ordered commutative multiplicative monoid. -/
theorem prod_le_one (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) : (∏ i in s, f i) ≤ 1 :=
  by
  convert ← prod_le_prod h0 h1
  exact Finset.prod_const_one
#align finset.prod_le_one Finset.prod_le_one

/- warning: finset.prod_add_prod_le -> Finset.prod_add_prod_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : OrderedCommSemiring.{u2} R] {s : Finset.{u1} ι} {i : ι} {f : ι -> R} {g : ι -> R} {h : ι -> R}, (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))))) (g i) (h i)) (f i)) -> (forall (j : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) j s) -> (Ne.{succ u1} ι j i) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (g j) (f j))) -> (forall (j : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) j s) -> (Ne.{succ u1} ι j i) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (h j) (f j))) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))))))) (g i))) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))))))) (h i))) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))) (HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R _inst_1))))))) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_1)) s (fun (i : ι) => g i)) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_1)) s (fun (i : ι) => h i))) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R (OrderedCommSemiring.toCommSemiring.{u2} R _inst_1)) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_1 : OrderedCommSemiring.{u1} R] {s : Finset.{u2} ι} {i : ι} {f : ι -> R} {g : ι -> R} {h : ι -> R}, (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1))))))) (g i) (h i)) (f i)) -> (forall (j : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) j s) -> (Ne.{succ u2} ι j i) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (g j) (f j))) -> (forall (j : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) j s) -> (Ne.{succ u2} ι j i) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (h j) (f j))) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1))))) (g i))) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1))))) (h i))) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1)))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R _inst_1))))))) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1)) s (fun (i : ι) => g i)) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1)) s (fun (i : ι) => h i))) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R (OrderedCommSemiring.toCommSemiring.{u1} R _inst_1)) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_add_prod_le Finset.prod_add_prod_leₓ'. -/
/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `ordered_comm_semiring`. -/
theorem prod_add_prod_le {i : ι} {f g h : ι → R} (hi : i ∈ s) (h2i : g i + h i ≤ f i)
    (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j) (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hh : ∀ i ∈ s, 0 ≤ h i) : ((∏ i in s, g i) + ∏ i in s, h i) ≤ ∏ i in s, f i :=
  by
  simp_rw [prod_eq_mul_prod_diff_singleton hi]
  refine' le_trans _ (mul_le_mul_of_nonneg_right h2i _)
  · rw [right_distrib]
    apply add_le_add <;> apply mul_le_mul_of_nonneg_left <;> try apply_assumption <;> assumption <;>
        apply prod_le_prod <;>
      simp (config := { contextual := true }) [*]
  · apply prod_nonneg
    simp only [and_imp, mem_sdiff, mem_singleton]
    intro j h1j h2j
    exact le_trans (hg j h1j) (hgf j h1j h2j)
#align finset.prod_add_prod_le Finset.prod_add_prod_le

end OrderedCommSemiring

section StrictOrderedCommSemiring

variable [StrictOrderedCommSemiring R] [Nontrivial R] {f : ι → R} {s : Finset ι}

/- warning: finset.prod_pos -> Finset.prod_pos is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : StrictOrderedCommSemiring.{u2} R] [_inst_2 : Nontrivial.{u2} R] {f : ι -> R} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))))))) (f i))) -> (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedCancelAddCommMonoid.toPartialOrder.{u2} R (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (StrictOrderedSemiring.toSemiring.{u2} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u2} R _inst_1))))))))) (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R (StrictOrderedCommSemiring.toCommSemiring.{u2} R _inst_1)) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_1 : StrictOrderedCommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] {f : ι -> R} {s : Finset.{u2} ι}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedSemiring.toPartialOrder.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (StrictOrderedCommSemiring.toCommSemiring.{u1} R _inst_1))))) (f i))) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (StrictOrderedSemiring.toPartialOrder.{u1} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (StrictOrderedCommSemiring.toCommSemiring.{u1} R _inst_1))))) (Finset.prod.{u1, u2} R ι (CommSemiring.toCommMonoid.{u1} R (StrictOrderedCommSemiring.toCommSemiring.{u1} R _inst_1)) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_pos Finset.prod_posₓ'. -/
-- This is also true for a ordered commutative multiplicative monoid with zero
theorem prod_pos (h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i in s, f i :=
  prod_induction f (fun x => 0 < x) (fun _ _ ha hb => mul_pos ha hb) zero_lt_one h0
#align finset.prod_pos Finset.prod_pos

end StrictOrderedCommSemiring

section CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring R] {f g h : ι → R} {s : Finset ι} {i : ι}

/- warning: canonically_ordered_comm_semiring.multiset_prod_pos -> CanonicallyOrderedCommSemiring.multiset_prod_pos is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CanonicallyOrderedCommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] {m : Multiset.{u1} R}, Iff (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommMonoid.toPartialOrder.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1)))))))))) (Multiset.prod.{u1} R (OrderedCommMonoid.toCommMonoid.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{u1} R _inst_1)) m)) (forall (x : R), (Membership.Mem.{u1, u1} R (Multiset.{u1} R) (Multiset.hasMem.{u1} R) x m) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedAddCommMonoid.toPartialOrder.{u1} R (OrderedSemiring.toOrderedAddCommMonoid.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1)))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1)))))))))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CanonicallyOrderedCommSemiring.{u1} R] [_inst_2 : Nontrivial.{u1} R] {m : Multiset.{u1} R}, Iff (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CanonicallyOrderedCommSemiring.toCommSemiring.{u1} R _inst_1))))) (Multiset.prod.{u1} R (OrderedCommMonoid.toCommMonoid.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{u1} R _inst_1)) m)) (forall (x : R), (Membership.mem.{u1, u1} R (Multiset.{u1} R) (Multiset.instMembershipMultiset.{u1} R) x m) -> (LT.lt.{u1} R (Preorder.toLT.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1))))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CanonicallyOrderedCommSemiring.toCommSemiring.{u1} R _inst_1))))) x))
Case conversion may be inaccurate. Consider using '#align canonically_ordered_comm_semiring.multiset_prod_pos CanonicallyOrderedCommSemiring.multiset_prod_posₓ'. -/
@[simp]
theorem CanonicallyOrderedCommSemiring.multiset_prod_pos [Nontrivial R] {m : Multiset R} :
    0 < m.Prod ↔ ∀ x ∈ m, (0 : R) < x :=
  by
  induction m using Quotient.inductionOn
  rw [Multiset.quot_mk_to_coe, Multiset.coe_prod]
  exact CanonicallyOrderedCommSemiring.list_prod_pos
#align canonically_ordered_comm_semiring.multiset_prod_pos CanonicallyOrderedCommSemiring.multiset_prod_pos

/- warning: canonically_ordered_comm_semiring.prod_pos -> CanonicallyOrderedCommSemiring.prod_pos is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CanonicallyOrderedCommSemiring.{u2} R] {f : ι -> R} {s : Finset.{u1} ι} [_inst_2 : Nontrivial.{u2} R], Iff (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1)))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1)))))))))) (Finset.prod.{u2, u1} R ι (OrderedCommMonoid.toCommMonoid.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{u2} R _inst_1)) s (fun (i : ι) => f i))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1)))))) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1)))))))))) (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CanonicallyOrderedCommSemiring.{u2} R] {f : ι -> R} {s : Finset.{u1} ι} [_inst_2 : Nontrivial.{u2} R], Iff (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedSemiring.toPartialOrder.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (CanonicallyOrderedCommSemiring.toCommSemiring.{u2} R _inst_1))))) (Finset.prod.{u2, u1} R ι (OrderedCommMonoid.toCommMonoid.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{u2} R _inst_1)) s (fun (i : ι) => f i))) (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LT.lt.{u2} R (Preorder.toLT.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedSemiring.toPartialOrder.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1))))) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (CommMonoidWithZero.toZero.{u2} R (CommSemiring.toCommMonoidWithZero.{u2} R (CanonicallyOrderedCommSemiring.toCommSemiring.{u2} R _inst_1))))) (f i)))
Case conversion may be inaccurate. Consider using '#align canonically_ordered_comm_semiring.prod_pos CanonicallyOrderedCommSemiring.prod_posₓ'. -/
/-- Note that the name is to match `canonically_ordered_comm_semiring.mul_pos`. -/
@[simp]
theorem CanonicallyOrderedCommSemiring.prod_pos [Nontrivial R] :
    (0 < ∏ i in s, f i) ↔ ∀ i ∈ s, (0 : R) < f i :=
  CanonicallyOrderedCommSemiring.multiset_prod_pos.trans <| by simp
#align canonically_ordered_comm_semiring.prod_pos CanonicallyOrderedCommSemiring.prod_pos

/- warning: finset.prod_add_prod_le' -> Finset.prod_add_prod_le' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CanonicallyOrderedCommSemiring.{u2} R] {f : ι -> R} {g : ι -> R} {h : ι -> R} {s : Finset.{u1} ι} {i : ι}, (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1)))))) (HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1)))))))) (g i) (h i)) (f i)) -> (forall (j : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) j s) -> (Ne.{succ u1} ι j i) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1)))))) (g j) (f j))) -> (forall (j : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) j s) -> (Ne.{succ u1} ι j i) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1)))))) (h j) (f j))) -> (LE.le.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (OrderedAddCommMonoid.toPartialOrder.{u2} R (OrderedSemiring.toOrderedAddCommMonoid.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1)))))) (HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (OrderedSemiring.toSemiring.{u2} R (OrderedCommSemiring.toOrderedSemiring.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u2} R _inst_1)))))))) (Finset.prod.{u2, u1} R ι (OrderedCommMonoid.toCommMonoid.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{u2} R _inst_1)) s (fun (i : ι) => g i)) (Finset.prod.{u2, u1} R ι (OrderedCommMonoid.toCommMonoid.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{u2} R _inst_1)) s (fun (i : ι) => h i))) (Finset.prod.{u2, u1} R ι (OrderedCommMonoid.toCommMonoid.{u2} R (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{u2} R _inst_1)) s (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_1 : CanonicallyOrderedCommSemiring.{u1} R] {f : ι -> R} {g : ι -> R} {h : ι -> R} {s : Finset.{u2} ι} {i : ι}, (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1)))))))) (g i) (h i)) (f i)) -> (forall (j : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) j s) -> (Ne.{succ u2} ι j i) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1))))) (g j) (f j))) -> (forall (j : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) j s) -> (Ne.{succ u2} ι j i) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1))))) (h j) (f j))) -> (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (OrderedSemiring.toPartialOrder.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (OrderedSemiring.toSemiring.{u1} R (OrderedCommSemiring.toOrderedSemiring.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{u1} R _inst_1)))))))) (Finset.prod.{u1, u2} R ι (OrderedCommMonoid.toCommMonoid.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{u1} R _inst_1)) s (fun (i : ι) => g i)) (Finset.prod.{u1, u2} R ι (OrderedCommMonoid.toCommMonoid.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{u1} R _inst_1)) s (fun (i : ι) => h i))) (Finset.prod.{u1, u2} R ι (OrderedCommMonoid.toCommMonoid.{u1} R (CanonicallyOrderedCommSemiring.toOrderedCommMonoid.{u1} R _inst_1)) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_add_prod_le' Finset.prod_add_prod_le'ₓ'. -/
/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `canonically_ordered_comm_semiring`.
-/
theorem prod_add_prod_le' (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
    (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) : ((∏ i in s, g i) + ∏ i in s, h i) ≤ ∏ i in s, f i := by
  classical
    simp_rw [prod_eq_mul_prod_diff_singleton hi]
    refine' le_trans _ (mul_le_mul_right' h2i _)
    rw [right_distrib]
    apply add_le_add <;> apply mul_le_mul_left' <;> apply prod_le_prod' <;>
            simp only [and_imp, mem_sdiff, mem_singleton] <;>
          intros <;>
        apply_assumption <;>
      assumption
#align finset.prod_add_prod_le' Finset.prod_add_prod_le'

end CanonicallyOrderedCommSemiring

end Finset

namespace Fintype

variable [Fintype ι]

#print Fintype.prod_mono' /-
@[to_additive sum_mono, mono]
theorem prod_mono' [OrderedCommMonoid M] : Monotone fun f : ι → M => ∏ i, f i := fun f g hfg =>
  Finset.prod_le_prod' fun x _ => hfg x
#align fintype.prod_mono' Fintype.prod_mono'
#align fintype.sum_mono Fintype.sum_mono
-/

attribute [mono] sum_mono

#print Fintype.prod_strict_mono' /-
@[to_additive sum_strict_mono]
theorem prod_strict_mono' [OrderedCancelCommMonoid M] : StrictMono fun f : ι → M => ∏ x, f x :=
  fun f g hfg =>
  let ⟨hle, i, hlt⟩ := Pi.lt_def.mp hfg
  Finset.prod_lt_prod' (fun i _ => hle i) ⟨i, Finset.mem_univ i, hlt⟩
#align fintype.prod_strict_mono' Fintype.prod_strict_mono'
#align fintype.sum_strict_mono Fintype.sum_strict_mono
-/

end Fintype

namespace WithTop

open Finset

/- warning: with_top.prod_lt_top -> WithTop.prod_lt_top is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u2} R] [_inst_2 : NoZeroDivisors.{u2} R (MulZeroClass.toHasMul.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (CommMonoidWithZero.toMonoidWithZero.{u2} R _inst_1)))) (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (CommMonoidWithZero.toMonoidWithZero.{u2} R _inst_1))))] [_inst_3 : Nontrivial.{u2} R] [_inst_4 : DecidableEq.{succ u2} R] [_inst_5 : LT.{u2} R] {s : Finset.{u1} ι} {f : ι -> (WithTop.{u2} R)}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Ne.{succ u2} (WithTop.{u2} R) (f i) (Top.top.{u2} (WithTop.{u2} R) (WithTop.hasTop.{u2} R)))) -> (LT.lt.{u2} (WithTop.{u2} R) (WithTop.hasLt.{u2} R _inst_5) (Finset.prod.{u2, u1} (WithTop.{u2} R) ι (CommMonoidWithZero.toCommMonoid.{u2} (WithTop.{u2} R) (WithTop.commMonoidWithZero.{u2} R (fun (a : R) (b : R) => _inst_4 a b) _inst_1 _inst_2 _inst_3)) s (fun (i : ι) => f i)) (Top.top.{u2} (WithTop.{u2} R) (WithTop.hasTop.{u2} R)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u2} R] [_inst_2 : NoZeroDivisors.{u2} R (MulZeroClass.toMul.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (CommMonoidWithZero.toMonoidWithZero.{u2} R _inst_1)))) (CommMonoidWithZero.toZero.{u2} R _inst_1)] [_inst_3 : Nontrivial.{u2} R] [_inst_4 : DecidableEq.{succ u2} R] [_inst_5 : LT.{u2} R] {s : Finset.{u1} ι} {f : ι -> (WithTop.{u2} R)}, (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Ne.{succ u2} (WithTop.{u2} R) (f i) (Top.top.{u2} (WithTop.{u2} R) (WithTop.top.{u2} R)))) -> (LT.lt.{u2} (WithTop.{u2} R) (WithTop.lt.{u2} R _inst_5) (Finset.prod.{u2, u1} (WithTop.{u2} R) ι (CommMonoidWithZero.toCommMonoid.{u2} (WithTop.{u2} R) (WithTop.commMonoidWithZero.{u2} R (fun (a : R) (b : R) => _inst_4 a b) _inst_1 _inst_2 _inst_3)) s (fun (i : ι) => f i)) (Top.top.{u2} (WithTop.{u2} R) (WithTop.top.{u2} R)))
Case conversion may be inaccurate. Consider using '#align with_top.prod_lt_top WithTop.prod_lt_topₓ'. -/
/-- A product of finite numbers is still finite -/
theorem prod_lt_top [CommMonoidWithZero R] [NoZeroDivisors R] [Nontrivial R] [DecidableEq R] [LT R]
    {s : Finset ι} {f : ι → WithTop R} (h : ∀ i ∈ s, f i ≠ ⊤) : (∏ i in s, f i) < ⊤ :=
  prod_induction f (fun a => a < ⊤) (fun a b h₁ h₂ => mul_lt_top' h₁ h₂) (coe_lt_top 1) fun a ha =>
    WithTop.lt_top_iff_ne_top.2 (h a ha)
#align with_top.prod_lt_top WithTop.prod_lt_top

/- warning: with_top.sum_eq_top_iff -> WithTop.sum_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {s : Finset.{u1} ι} {f : ι -> (WithTop.{u2} M)}, Iff (Eq.{succ u2} (WithTop.{u2} M) (Finset.sum.{u2, u1} (WithTop.{u2} M) ι (WithTop.addCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (Top.top.{u2} (WithTop.{u2} M) (WithTop.hasTop.{u2} M))) (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => Eq.{succ u2} (WithTop.{u2} M) (f i) (Top.top.{u2} (WithTop.{u2} M) (WithTop.hasTop.{u2} M)))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] {s : Finset.{u1} ι} {f : ι -> (WithTop.{u2} M)}, Iff (Eq.{succ u2} (WithTop.{u2} M) (Finset.sum.{u2, u1} (WithTop.{u2} M) ι (WithTop.addCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (Top.top.{u2} (WithTop.{u2} M) (WithTop.top.{u2} M))) (Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (Eq.{succ u2} (WithTop.{u2} M) (f i) (Top.top.{u2} (WithTop.{u2} M) (WithTop.top.{u2} M)))))
Case conversion may be inaccurate. Consider using '#align with_top.sum_eq_top_iff WithTop.sum_eq_top_iffₓ'. -/
/-- A sum of numbers is infinite iff one of them is infinite -/
theorem sum_eq_top_iff [AddCommMonoid M] {s : Finset ι} {f : ι → WithTop M} :
    (∑ i in s, f i) = ⊤ ↔ ∃ i ∈ s, f i = ⊤ := by
  induction s using Finset.cons_induction <;> simp [*, or_and_right, exists_or]
#align with_top.sum_eq_top_iff WithTop.sum_eq_top_iff

/- warning: with_top.sum_lt_top_iff -> WithTop.sum_lt_top_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] [_inst_2 : LT.{u2} M] {s : Finset.{u1} ι} {f : ι -> (WithTop.{u2} M)}, Iff (LT.lt.{u2} (WithTop.{u2} M) (WithTop.hasLt.{u2} M _inst_2) (Finset.sum.{u2, u1} (WithTop.{u2} M) ι (WithTop.addCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (Top.top.{u2} (WithTop.{u2} M) (WithTop.hasTop.{u2} M))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LT.lt.{u2} (WithTop.{u2} M) (WithTop.hasLt.{u2} M _inst_2) (f i) (Top.top.{u2} (WithTop.{u2} M) (WithTop.hasTop.{u2} M))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] [_inst_2 : LT.{u2} M] {s : Finset.{u1} ι} {f : ι -> (WithTop.{u2} M)}, Iff (LT.lt.{u2} (WithTop.{u2} M) (WithTop.lt.{u2} M _inst_2) (Finset.sum.{u2, u1} (WithTop.{u2} M) ι (WithTop.addCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (Top.top.{u2} (WithTop.{u2} M) (WithTop.top.{u2} M))) (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LT.lt.{u2} (WithTop.{u2} M) (WithTop.lt.{u2} M _inst_2) (f i) (Top.top.{u2} (WithTop.{u2} M) (WithTop.top.{u2} M))))
Case conversion may be inaccurate. Consider using '#align with_top.sum_lt_top_iff WithTop.sum_lt_top_iffₓ'. -/
/-- A sum of finite numbers is still finite -/
theorem sum_lt_top_iff [AddCommMonoid M] [LT M] {s : Finset ι} {f : ι → WithTop M} :
    (∑ i in s, f i) < ⊤ ↔ ∀ i ∈ s, f i < ⊤ := by
  simp only [WithTop.lt_top_iff_ne_top, Ne.def, sum_eq_top_iff, not_exists]
#align with_top.sum_lt_top_iff WithTop.sum_lt_top_iff

/- warning: with_top.sum_lt_top -> WithTop.sum_lt_top is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] [_inst_2 : LT.{u2} M] {s : Finset.{u1} ι} {f : ι -> (WithTop.{u2} M)}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Ne.{succ u2} (WithTop.{u2} M) (f i) (Top.top.{u2} (WithTop.{u2} M) (WithTop.hasTop.{u2} M)))) -> (LT.lt.{u2} (WithTop.{u2} M) (WithTop.hasLt.{u2} M _inst_2) (Finset.sum.{u2, u1} (WithTop.{u2} M) ι (WithTop.addCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (Top.top.{u2} (WithTop.{u2} M) (WithTop.hasTop.{u2} M)))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] [_inst_2 : LT.{u2} M] {s : Finset.{u1} ι} {f : ι -> (WithTop.{u2} M)}, (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Ne.{succ u2} (WithTop.{u2} M) (f i) (Top.top.{u2} (WithTop.{u2} M) (WithTop.top.{u2} M)))) -> (LT.lt.{u2} (WithTop.{u2} M) (WithTop.lt.{u2} M _inst_2) (Finset.sum.{u2, u1} (WithTop.{u2} M) ι (WithTop.addCommMonoid.{u2} M _inst_1) s (fun (i : ι) => f i)) (Top.top.{u2} (WithTop.{u2} M) (WithTop.top.{u2} M)))
Case conversion may be inaccurate. Consider using '#align with_top.sum_lt_top WithTop.sum_lt_topₓ'. -/
/-- A sum of finite numbers is still finite -/
theorem sum_lt_top [AddCommMonoid M] [LT M] {s : Finset ι} {f : ι → WithTop M}
    (h : ∀ i ∈ s, f i ≠ ⊤) : (∑ i in s, f i) < ⊤ :=
  sum_lt_top_iff.2 fun i hi => WithTop.lt_top_iff_ne_top.2 (h i hi)
#align with_top.sum_lt_top WithTop.sum_lt_top

end WithTop

section AbsoluteValue

variable {S : Type _}

/- warning: absolute_value.sum_le -> AbsoluteValue.sum_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : OrderedSemiring.{u3} S] (abv : AbsoluteValue.{u2, u3} R S _inst_1 _inst_2) (s : Finset.{u1} ι) (f : ι -> R), LE.le.{u3} S (Preorder.toLE.{u3} S (PartialOrder.toPreorder.{u3} S (OrderedAddCommMonoid.toPartialOrder.{u3} S (OrderedSemiring.toOrderedAddCommMonoid.{u3} S _inst_2)))) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (AbsoluteValue.{u2, u3} R S _inst_1 _inst_2) (fun (f : AbsoluteValue.{u2, u3} R S _inst_1 _inst_2) => R -> S) (AbsoluteValue.hasCoeToFun.{u2, u3} R S _inst_1 _inst_2) abv (Finset.sum.{u2, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) s (fun (i : ι) => f i))) (Finset.sum.{u3, u1} S ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} S (OrderedSemiring.toOrderedAddCommMonoid.{u3} S _inst_2)) s (fun (i : ι) => coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (AbsoluteValue.{u2, u3} R S _inst_1 _inst_2) (fun (f : AbsoluteValue.{u2, u3} R S _inst_1 _inst_2) => R -> S) (AbsoluteValue.hasCoeToFun.{u2, u3} R S _inst_1 _inst_2) abv (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} [_inst_1 : Semiring.{u3} R] [_inst_2 : OrderedSemiring.{u2} S] (abv : AbsoluteValue.{u3, u2} R S _inst_1 _inst_2) (s : Finset.{u1} ι) (f : ι -> R), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => S) (Finset.sum.{u3, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) s (fun (i : ι) => f i))) (Preorder.toLE.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => S) (Finset.sum.{u3, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) s (fun (i : ι) => f i))) (PartialOrder.toPreorder.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => S) (Finset.sum.{u3, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) s (fun (i : ι) => f i))) (OrderedSemiring.toPartialOrder.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => S) (Finset.sum.{u3, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) s (fun (i : ι) => f i))) _inst_2))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (AbsoluteValue.{u3, u2} R S _inst_1 _inst_2) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u3 u2, u3, u2} (AbsoluteValue.{u3, u2} R S _inst_1 _inst_2) R S (Distrib.toAdd.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Distrib.toAdd.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S _inst_2))))) (Preorder.toLE.{u2} S (PartialOrder.toPreorder.{u2} S (OrderedSemiring.toPartialOrder.{u2} S _inst_2))) (AbsoluteValue.subadditiveHomClass.{u3, u2} R S _inst_1 _inst_2)) abv (Finset.sum.{u3, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} S ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} S (OrderedSemiring.toOrderedAddCommMonoid.{u2} S _inst_2)) s (fun (i : ι) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (AbsoluteValue.{u3, u2} R S _inst_1 _inst_2) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u3 u2, u3, u2} (AbsoluteValue.{u3, u2} R S _inst_1 _inst_2) R S (Distrib.toAdd.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Distrib.toAdd.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S _inst_2))))) (Preorder.toLE.{u2} S (PartialOrder.toPreorder.{u2} S (OrderedSemiring.toPartialOrder.{u2} S _inst_2))) (AbsoluteValue.subadditiveHomClass.{u3, u2} R S _inst_1 _inst_2)) abv (f i)))
Case conversion may be inaccurate. Consider using '#align absolute_value.sum_le AbsoluteValue.sum_leₓ'. -/
theorem AbsoluteValue.sum_le [Semiring R] [OrderedSemiring S] (abv : AbsoluteValue R S)
    (s : Finset ι) (f : ι → R) : abv (∑ i in s, f i) ≤ ∑ i in s, abv (f i) :=
  Finset.le_sum_of_subadditive abv (map_zero _) abv.add_le _ _
#align absolute_value.sum_le AbsoluteValue.sum_le

/- warning: is_absolute_value.abv_sum -> IsAbsoluteValue.abv_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : OrderedSemiring.{u3} S] (abv : R -> S) [_inst_3 : IsAbsoluteValue.{u3, u2} S _inst_2 R _inst_1 abv] (f : ι -> R) (s : Finset.{u1} ι), LE.le.{u3} S (Preorder.toLE.{u3} S (PartialOrder.toPreorder.{u3} S (OrderedAddCommMonoid.toPartialOrder.{u3} S (OrderedSemiring.toOrderedAddCommMonoid.{u3} S _inst_2)))) (abv (Finset.sum.{u2, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) s (fun (i : ι) => f i))) (Finset.sum.{u3, u1} S ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} S (OrderedSemiring.toOrderedAddCommMonoid.{u3} S _inst_2)) s (fun (i : ι) => abv (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} [_inst_1 : Semiring.{u3} R] [_inst_2 : OrderedSemiring.{u2} S] (abv : R -> S) [_inst_3 : IsAbsoluteValue.{u2, u3} S _inst_2 R _inst_1 abv] (f : ι -> R) (s : Finset.{u1} ι), LE.le.{u2} S (Preorder.toLE.{u2} S (PartialOrder.toPreorder.{u2} S (OrderedSemiring.toPartialOrder.{u2} S _inst_2))) (abv (Finset.sum.{u3, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} S ι (OrderedAddCommMonoid.toAddCommMonoid.{u2} S (OrderedSemiring.toOrderedAddCommMonoid.{u2} S _inst_2)) s (fun (i : ι) => abv (f i)))
Case conversion may be inaccurate. Consider using '#align is_absolute_value.abv_sum IsAbsoluteValue.abv_sumₓ'. -/
theorem IsAbsoluteValue.abv_sum [Semiring R] [OrderedSemiring S] (abv : R → S) [IsAbsoluteValue abv]
    (f : ι → R) (s : Finset ι) : abv (∑ i in s, f i) ≤ ∑ i in s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).sum_le _ _
#align is_absolute_value.abv_sum IsAbsoluteValue.abv_sum

/- warning: absolute_value.map_prod -> AbsoluteValue.map_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Nontrivial.{u2} R] [_inst_3 : LinearOrderedCommRing.{u3} S] (abv : AbsoluteValue.{u2, u3} R S (CommSemiring.toSemiring.{u2} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u3} S (StrictOrderedRing.toStrictOrderedSemiring.{u3} S (LinearOrderedRing.toStrictOrderedRing.{u3} S (LinearOrderedCommRing.toLinearOrderedRing.{u3} S _inst_3))))) (f : ι -> R) (s : Finset.{u1} ι), Eq.{succ u3} S (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (AbsoluteValue.{u2, u3} R S (CommSemiring.toSemiring.{u2} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u3} S (StrictOrderedRing.toStrictOrderedSemiring.{u3} S (LinearOrderedRing.toStrictOrderedRing.{u3} S (LinearOrderedCommRing.toLinearOrderedRing.{u3} S _inst_3))))) (fun (f : AbsoluteValue.{u2, u3} R S (CommSemiring.toSemiring.{u2} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u3} S (StrictOrderedRing.toStrictOrderedSemiring.{u3} S (LinearOrderedRing.toStrictOrderedRing.{u3} S (LinearOrderedCommRing.toLinearOrderedRing.{u3} S _inst_3))))) => R -> S) (AbsoluteValue.hasCoeToFun.{u2, u3} R S (CommSemiring.toSemiring.{u2} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u3} S (StrictOrderedRing.toStrictOrderedSemiring.{u3} S (LinearOrderedRing.toStrictOrderedRing.{u3} S (LinearOrderedCommRing.toLinearOrderedRing.{u3} S _inst_3))))) abv (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R _inst_1) s (fun (i : ι) => f i))) (Finset.prod.{u3, u1} S ι (LinearOrderedCommRing.toCommMonoid.{u3} S _inst_3) s (fun (i : ι) => coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (AbsoluteValue.{u2, u3} R S (CommSemiring.toSemiring.{u2} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u3} S (StrictOrderedRing.toStrictOrderedSemiring.{u3} S (LinearOrderedRing.toStrictOrderedRing.{u3} S (LinearOrderedCommRing.toLinearOrderedRing.{u3} S _inst_3))))) (fun (f : AbsoluteValue.{u2, u3} R S (CommSemiring.toSemiring.{u2} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u3} S (StrictOrderedRing.toStrictOrderedSemiring.{u3} S (LinearOrderedRing.toStrictOrderedRing.{u3} S (LinearOrderedCommRing.toLinearOrderedRing.{u3} S _inst_3))))) => R -> S) (AbsoluteValue.hasCoeToFun.{u2, u3} R S (CommSemiring.toSemiring.{u2} R _inst_1) (StrictOrderedSemiring.toOrderedSemiring.{u3} S (StrictOrderedRing.toStrictOrderedSemiring.{u3} S (LinearOrderedRing.toStrictOrderedRing.{u3} S (LinearOrderedCommRing.toLinearOrderedRing.{u3} S _inst_3))))) abv (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : Nontrivial.{u3} R] [_inst_3 : LinearOrderedCommRing.{u2} S] (abv : AbsoluteValue.{u3, u2} R S (CommSemiring.toSemiring.{u3} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3))))) (f : ι -> R) (s : Finset.{u1} ι), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => S) (Finset.prod.{u3, u1} R ι (CommSemiring.toCommMonoid.{u3} R _inst_1) s (fun (i : ι) => f i))) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (AbsoluteValue.{u3, u2} R S (CommSemiring.toSemiring.{u3} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3))))) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u3 u2, u3, u2} (AbsoluteValue.{u3, u2} R S (CommSemiring.toSemiring.{u3} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3))))) R S (Distrib.toAdd.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (Distrib.toAdd.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3))))))))) (Preorder.toLE.{u2} S (PartialOrder.toPreorder.{u2} S (OrderedSemiring.toPartialOrder.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3))))))) (AbsoluteValue.subadditiveHomClass.{u3, u2} R S (CommSemiring.toSemiring.{u3} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3)))))) abv (Finset.prod.{u3, u1} R ι (CommSemiring.toCommMonoid.{u3} R _inst_1) s (fun (i : ι) => f i))) (Finset.prod.{u2, u1} S ι (LinearOrderedCommRing.toCommMonoid.{u2} S _inst_3) s (fun (i : ι) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (AbsoluteValue.{u3, u2} R S (CommSemiring.toSemiring.{u3} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3))))) R (fun (f : R) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : R) => S) f) (SubadditiveHomClass.toFunLike.{max u3 u2, u3, u2} (AbsoluteValue.{u3, u2} R S (CommSemiring.toSemiring.{u3} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3))))) R S (Distrib.toAdd.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_1))))) (Distrib.toAdd.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (OrderedSemiring.toSemiring.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3))))))))) (Preorder.toLE.{u2} S (PartialOrder.toPreorder.{u2} S (OrderedSemiring.toPartialOrder.{u2} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3))))))) (AbsoluteValue.subadditiveHomClass.{u3, u2} R S (CommSemiring.toSemiring.{u3} R _inst_1) (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3)))))) abv (f i)))
Case conversion may be inaccurate. Consider using '#align absolute_value.map_prod AbsoluteValue.map_prodₓ'. -/
theorem AbsoluteValue.map_prod [CommSemiring R] [Nontrivial R] [LinearOrderedCommRing S]
    (abv : AbsoluteValue R S) (f : ι → R) (s : Finset ι) :
    abv (∏ i in s, f i) = ∏ i in s, abv (f i) :=
  abv.toMonoidHom.map_prod f s
#align absolute_value.map_prod AbsoluteValue.map_prod

/- warning: is_absolute_value.map_prod -> IsAbsoluteValue.map_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Nontrivial.{u2} R] [_inst_3 : LinearOrderedCommRing.{u3} S] (abv : R -> S) [_inst_4 : IsAbsoluteValue.{u3, u2} S (StrictOrderedSemiring.toOrderedSemiring.{u3} S (StrictOrderedRing.toStrictOrderedSemiring.{u3} S (LinearOrderedRing.toStrictOrderedRing.{u3} S (LinearOrderedCommRing.toLinearOrderedRing.{u3} S _inst_3)))) R (CommSemiring.toSemiring.{u2} R _inst_1) abv] (f : ι -> R) (s : Finset.{u1} ι), Eq.{succ u3} S (abv (Finset.prod.{u2, u1} R ι (CommSemiring.toCommMonoid.{u2} R _inst_1) s (fun (i : ι) => f i))) (Finset.prod.{u3, u1} S ι (LinearOrderedCommRing.toCommMonoid.{u3} S _inst_3) s (fun (i : ι) => abv (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : Nontrivial.{u3} R] [_inst_3 : LinearOrderedCommRing.{u2} S] (abv : R -> S) [_inst_4 : IsAbsoluteValue.{u2, u3} S (OrderedCommSemiring.toOrderedSemiring.{u2} S (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} S (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} S (LinearOrderedCommRing.toLinearOrderedCommSemiring.{u2} S _inst_3)))) R (CommSemiring.toSemiring.{u3} R _inst_1) abv] (f : ι -> R) (s : Finset.{u1} ι), Eq.{succ u2} S (abv (Finset.prod.{u3, u1} R ι (CommSemiring.toCommMonoid.{u3} R _inst_1) s (fun (i : ι) => f i))) (Finset.prod.{u2, u1} S ι (LinearOrderedCommRing.toCommMonoid.{u2} S _inst_3) s (fun (i : ι) => abv (f i)))
Case conversion may be inaccurate. Consider using '#align is_absolute_value.map_prod IsAbsoluteValue.map_prodₓ'. -/
theorem IsAbsoluteValue.map_prod [CommSemiring R] [Nontrivial R] [LinearOrderedCommRing S]
    (abv : R → S) [IsAbsoluteValue abv] (f : ι → R) (s : Finset ι) :
    abv (∏ i in s, f i) = ∏ i in s, abv (f i) :=
  (IsAbsoluteValue.toAbsoluteValue abv).map_prod _ _
#align is_absolute_value.map_prod IsAbsoluteValue.map_prod

end AbsoluteValue

