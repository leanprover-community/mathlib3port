/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module algebra.big_operators.basic
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Multiset.Lemmas
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Ring.Opposite
import Mathbin.Data.Finset.Sum
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Finset.Sigma
import Mathbin.Data.Multiset.Powerset
import Mathbin.Data.Set.Pairwise

/-!
# Big operators

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define products and sums indexed by finite sets (specifically, `finset`).

## Notation

We introduce the following notation, localized in `big_operators`.
To enable the notation, use `open_locale big_operators`.

Let `s` be a `finset α`, and `f : α → β` a function.

* `∏ x in s, f x` is notation for `finset.prod s f` (assuming `β` is a `comm_monoid`)
* `∑ x in s, f x` is notation for `finset.sum s f` (assuming `β` is an `add_comm_monoid`)
* `∏ x, f x` is notation for `finset.prod finset.univ f`
  (assuming `α` is a `fintype` and `β` is a `comm_monoid`)
* `∑ x, f x` is notation for `finset.sum finset.univ f`
  (assuming `α` is a `fintype` and `β` is an `add_comm_monoid`)

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/


universe u v w

variable {ι : Type _} {β : Type u} {α : Type v} {γ : Type w}

open Fin

namespace Finset

#print Finset.prod /-
/-- `∏ x in s, f x` is the product of `f x`
as `x` ranges over the elements of the finite set `s`.
-/
@[to_additive
      "`∑ x in s, f x` is the sum of `f x` as `x` ranges over the elements\nof the finite set `s`."]
protected def prod [CommMonoid β] (s : Finset α) (f : α → β) : β :=
  (s.1.map f).Prod
#align finset.prod Finset.prod
#align finset.sum Finset.sum
-/

#print Finset.prod_mk /-
@[simp, to_additive]
theorem prod_mk [CommMonoid β] (s : Multiset α) (hs : s.Nodup) (f : α → β) :
    (⟨s, hs⟩ : Finset α).Prod f = (s.map f).Prod :=
  rfl
#align finset.prod_mk Finset.prod_mk
#align finset.sum_mk Finset.sum_mk
-/

#print Finset.prod_val /-
@[simp, to_additive]
theorem prod_val [CommMonoid α] (s : Finset α) : s.1.Prod = s.Prod id := by
  rw [Finset.prod, Multiset.map_id]
#align finset.prod_val Finset.prod_val
#align finset.sum_val Finset.sum_val
-/

end Finset

library_note "operator precedence of big operators"/--
There is no established mathematical convention
for the operator precedence of big operators like `∏` and `∑`.
We will have to make a choice.

Online discussions, such as https://math.stackexchange.com/q/185538/30839
seem to suggest that `∏` and `∑` should have the same precedence,
and that this should be somewhere between `*` and `+`.
The latter have precedence levels `70` and `65` respectively,
and we therefore choose the level `67`.

In practice, this means that parentheses should be placed as follows:
```lean
∑ k in K, (a k + b k) = ∑ k in K, a k + ∑ k in K, b k →
  ∏ k in K, a k * b k = (∏ k in K, a k) * (∏ k in K, b k)
```
(Example taken from page 490 of Knuth's *Concrete Mathematics*.)
-/


-- mathport name: finset.sum_univ
scoped[BigOperators] notation3"∑ "(...)", "r:(scoped f => Finset.sum Finset.univ f) => r

-- mathport name: finset.prod_univ
scoped[BigOperators] notation3"∏ "(...)", "r:(scoped f => Finset.prod Finset.univ f) => r

-- mathport name: finset.sum
scoped[BigOperators] notation3"∑ "(...)" in "s", "r:(scoped f => Finset.sum s f) => r

-- mathport name: finset.prod
scoped[BigOperators] notation3"∏ "(...)" in "s", "r:(scoped f => Finset.prod s f) => r

open BigOperators

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

#print Finset.prod_eq_multiset_prod /-
@[to_additive]
theorem prod_eq_multiset_prod [CommMonoid β] (s : Finset α) (f : α → β) :
    (∏ x in s, f x) = (s.1.map f).Prod :=
  rfl
#align finset.prod_eq_multiset_prod Finset.prod_eq_multiset_prod
#align finset.sum_eq_multiset_sum Finset.sum_eq_multiset_sum
-/

/- warning: finset.prod_eq_fold -> Finset.prod_eq_fold is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (Finset.fold.{u2, u1} α β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) (CommSemigroup.to_isCommutative.{u1} β (CommMonoid.toCommSemigroup.{u1} β _inst_1)) (Semigroup.to_isAssociative.{u1} β (Monoid.toSemigroup.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) f s)
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (Finset.fold.{u2, u1} α β (fun (x._@.Mathlib.Algebra.BigOperators.Basic._hyg.3175 : β) (x._@.Mathlib.Algebra.BigOperators.Basic._hyg.3177 : β) => HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) x._@.Mathlib.Algebra.BigOperators.Basic._hyg.3175 x._@.Mathlib.Algebra.BigOperators.Basic._hyg.3177) (CommSemigroup.to_isCommutative.{u1} β (CommMonoid.toCommSemigroup.{u1} β _inst_1)) (Semigroup.to_isAssociative.{u1} β (Monoid.toSemigroup.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) f s)
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_fold Finset.prod_eq_foldₓ'. -/
@[to_additive]
theorem prod_eq_fold [CommMonoid β] (s : Finset α) (f : α → β) :
    (∏ x in s, f x) = s.fold (· * ·) 1 f :=
  rfl
#align finset.prod_eq_fold Finset.prod_eq_fold
#align finset.sum_eq_fold Finset.sum_eq_fold

/- warning: finset.sum_multiset_singleton -> Finset.sum_multiset_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Finset.sum.{u1, u1} (Multiset.{u1} α) α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)) s (fun (x : α) => Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) x)) (Finset.val.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Finset.sum.{u1, u1} (Multiset.{u1} α) α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)) s (fun (x : α) => Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) x)) (Finset.val.{u1} α s)
Case conversion may be inaccurate. Consider using '#align finset.sum_multiset_singleton Finset.sum_multiset_singletonₓ'. -/
@[simp]
theorem sum_multiset_singleton (s : Finset α) : (s.Sum fun x => {x}) = s.val := by
  simp only [sum_eq_multiset_sum, Multiset.sum_map_singleton]
#align finset.sum_multiset_singleton Finset.sum_multiset_singleton

end Finset

/- warning: map_prod -> map_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : CommMonoid.{u3} γ] {G : Type.{u4}} [_inst_3 : MonoidHomClass.{u4, u1, u3} G β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))] (g : G) (f : α -> β) (s : Finset.{u2} α), Eq.{succ u3} γ (coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => β -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G β (fun (_x : β) => γ) (MulHomClass.toFunLike.{u4, u1, u3} G β γ (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (MonoidHomClass.toMulHomClass.{u4, u1, u3} G β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) _inst_3))) g (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))) (Finset.prod.{u3, u2} γ α _inst_2 s (fun (x : α) => coeFn.{succ u4, max (succ u1) (succ u3)} G (fun (_x : G) => β -> γ) (FunLike.hasCoeToFun.{succ u4, succ u1, succ u3} G β (fun (_x : β) => γ) (MulHomClass.toFunLike.{u4, u1, u3} G β γ (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (MonoidHomClass.toMulHomClass.{u4, u1, u3} G β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) _inst_3))) g (f x)))
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u3}} {γ : Type.{u4}} [_inst_1 : CommMonoid.{u2} β] [_inst_2 : CommMonoid.{u4} γ] {G : Type.{u1}} [_inst_3 : MonoidHomClass.{u1, u2, u4} G β γ (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_1)) (Monoid.toMulOneClass.{u4} γ (CommMonoid.toMonoid.{u4} γ _inst_2))] (g : G) (f : α -> β) (s : Finset.{u3} α), Eq.{succ u4} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) (Finset.prod.{u2, u3} β α _inst_1 s (fun (x : α) => f x))) (FunLike.coe.{succ u1, succ u2, succ u4} G β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{u1, u2, u4} G β γ (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_1))) (MulOneClass.toMul.{u4} γ (Monoid.toMulOneClass.{u4} γ (CommMonoid.toMonoid.{u4} γ _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u2, u4} G β γ (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_1)) (Monoid.toMulOneClass.{u4} γ (CommMonoid.toMonoid.{u4} γ _inst_2)) _inst_3)) g (Finset.prod.{u2, u3} β α _inst_1 s (fun (x : α) => f x))) (Finset.prod.{u4, u3} γ α _inst_2 s (fun (x : α) => FunLike.coe.{succ u1, succ u2, succ u4} G β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{u1, u2, u4} G β γ (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_1))) (MulOneClass.toMul.{u4} γ (Monoid.toMulOneClass.{u4} γ (CommMonoid.toMonoid.{u4} γ _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u2, u4} G β γ (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_1)) (Monoid.toMulOneClass.{u4} γ (CommMonoid.toMonoid.{u4} γ _inst_2)) _inst_3)) g (f x)))
Case conversion may be inaccurate. Consider using '#align map_prod map_prodₓ'. -/
@[to_additive]
theorem map_prod [CommMonoid β] [CommMonoid γ] {G : Type _} [MonoidHomClass G β γ] (g : G)
    (f : α → β) (s : Finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) := by
  simp only [Finset.prod_eq_multiset_prod, map_multiset_prod, Multiset.map_map]
#align map_prod map_prod
#align map_sum map_sum

section Deprecated

/- warning: monoid_hom.map_prod -> MonoidHom.map_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : CommMonoid.{u3} γ] (g : MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (f : α -> β) (s : Finset.{u2} α), Eq.{succ u3} γ (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (fun (_x : MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) => β -> γ) (MonoidHom.hasCoeToFun.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) g (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))) (Finset.prod.{u3, u2} γ α _inst_2 s (fun (x : α) => coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (fun (_x : MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) => β -> γ) (MonoidHom.hasCoeToFun.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) g (f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : CommMonoid.{u3} γ] (g : MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (f : α -> β) (s : Finset.{u2} α), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) (MonoidHom.monoidHomClass.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))))) g (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))) (Finset.prod.{u3, u2} γ α _inst_2 s (fun (x : α) => FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) (MonoidHom.monoidHomClass.{u1, u3} β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))))) g (f x)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.map_prod MonoidHom.map_prodₓ'. -/
/-- Deprecated: use `_root_.map_prod` instead. -/
@[to_additive "Deprecated: use `_root_.map_sum` instead."]
protected theorem MonoidHom.map_prod [CommMonoid β] [CommMonoid γ] (g : β →* γ) (f : α → β)
    (s : Finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  map_prod g f s
#align monoid_hom.map_prod MonoidHom.map_prod
#align add_monoid_hom.map_sum AddMonoidHom.map_sum

/- warning: mul_equiv.map_prod -> MulEquiv.map_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : CommMonoid.{u3} γ] (g : MulEquiv.{u1, u3} β γ (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) (f : α -> β) (s : Finset.{u2} α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MulEquiv.{u1, u3} β γ (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) (fun (_x : MulEquiv.{u1, u3} β γ (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) => β -> γ) (MulEquiv.hasCoeToFun.{u1, u3} β γ (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) g (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))) (Finset.prod.{u3, u2} γ α _inst_2 s (fun (x : α) => coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MulEquiv.{u1, u3} β γ (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) (fun (_x : MulEquiv.{u1, u3} β γ (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) => β -> γ) (MulEquiv.hasCoeToFun.{u1, u3} β γ (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) g (f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : CommMonoid.{u3} γ] (g : MulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) (f : α -> β) (s : Finset.{u2} α), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) (MulEquivClass.instMonoidHomClass.{max u1 u3, u1, u3} (MulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) (MulEquiv.instMulEquivClassMulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))))))) g (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))) (Finset.prod.{u3, u2} γ α _inst_2 s (fun (x : α) => FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) (MulEquivClass.instMonoidHomClass.{max u1 u3, u1, u3} (MulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) β γ (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) (MulEquiv.instMulEquivClassMulEquiv.{u1, u3} β γ (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))))))) g (f x)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.map_prod MulEquiv.map_prodₓ'. -/
/-- Deprecated: use `_root_.map_prod` instead. -/
@[to_additive "Deprecated: use `_root_.map_sum` instead."]
protected theorem MulEquiv.map_prod [CommMonoid β] [CommMonoid γ] (g : β ≃* γ) (f : α → β)
    (s : Finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  map_prod g f s
#align mul_equiv.map_prod MulEquiv.map_prod
#align add_equiv.map_sum AddEquiv.map_sum

/- warning: ring_hom.map_list_prod -> RingHom.map_list_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : Semiring.{u1} β] [_inst_2 : Semiring.{u2} γ] (f : RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) (l : List.{u1} β), Eq.{succ u2} γ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) (fun (_x : RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) => β -> γ) (RingHom.hasCoeToFun.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) f (List.prod.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)))) (AddMonoidWithOne.toOne.{u1} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} β (NonAssocSemiring.toAddCommMonoidWithOne.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)))) l)) (List.prod.{u2} γ (Distrib.toHasMul.{u2} γ (NonUnitalNonAssocSemiring.toDistrib.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)))) (AddMonoidWithOne.toOne.{u2} γ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} γ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)))) (List.map.{u1, u2} β γ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) (fun (_x : RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) => β -> γ) (RingHom.hasCoeToFun.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) f) l))
but is expected to have type
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : Semiring.{u1} β] [_inst_2 : Semiring.{u2} γ] (f : RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) (l : List.{u1} β), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) (List.prod.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1))) (Semiring.toOne.{u1} β _inst_1) l)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2))))) f (List.prod.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1))) (Semiring.toOne.{u1} β _inst_1) l)) (List.prod.{u2} γ (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) (Semiring.toOne.{u2} γ _inst_2) (List.map.{u1, u2} β γ (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β _inst_1) (Semiring.toNonAssocSemiring.{u2} γ _inst_2))))) f) l))
Case conversion may be inaccurate. Consider using '#align ring_hom.map_list_prod RingHom.map_list_prodₓ'. -/
/-- Deprecated: use `_root_.map_list_prod` instead. -/
protected theorem RingHom.map_list_prod [Semiring β] [Semiring γ] (f : β →+* γ) (l : List β) :
    f l.Prod = (l.map f).Prod :=
  map_list_prod f l
#align ring_hom.map_list_prod RingHom.map_list_prod

/- warning: ring_hom.map_list_sum -> RingHom.map_list_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} β] [_inst_2 : NonAssocSemiring.{u2} γ] (f : RingHom.{u1, u2} β γ _inst_1 _inst_2) (l : List.{u1} β), Eq.{succ u2} γ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} β γ _inst_1 _inst_2) (fun (_x : RingHom.{u1, u2} β γ _inst_1 _inst_2) => β -> γ) (RingHom.hasCoeToFun.{u1, u2} β γ _inst_1 _inst_2) f (List.sum.{u1} β (Distrib.toHasAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1))) (MulZeroClass.toHasZero.{u1} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1))) l)) (List.sum.{u2} γ (Distrib.toHasAdd.{u2} γ (NonUnitalNonAssocSemiring.toDistrib.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2))) (MulZeroClass.toHasZero.{u2} γ (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2))) (List.map.{u1, u2} β γ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} β γ _inst_1 _inst_2) (fun (_x : RingHom.{u1, u2} β γ _inst_1 _inst_2) => β -> γ) (RingHom.hasCoeToFun.{u1, u2} β γ _inst_1 _inst_2) f) l))
but is expected to have type
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} β] [_inst_2 : NonAssocSemiring.{u2} γ] (f : RingHom.{u1, u2} β γ _inst_1 _inst_2) (l : List.{u1} β), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) (List.sum.{u1} β (Distrib.toAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1))) (MulZeroOneClass.toZero.{u1} β (NonAssocSemiring.toMulZeroOneClass.{u1} β _inst_1)) l)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ _inst_1 _inst_2 (RingHom.instRingHomClassRingHom.{u1, u2} β γ _inst_1 _inst_2)))) f (List.sum.{u1} β (Distrib.toAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1))) (MulZeroOneClass.toZero.{u1} β (NonAssocSemiring.toMulZeroOneClass.{u1} β _inst_1)) l)) (List.sum.{u2} γ (Distrib.toAdd.{u2} γ (NonUnitalNonAssocSemiring.toDistrib.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2))) (MulZeroOneClass.toZero.{u2} γ (NonAssocSemiring.toMulZeroOneClass.{u2} γ _inst_2)) (List.map.{u1, u2} β γ (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ _inst_1 _inst_2 (RingHom.instRingHomClassRingHom.{u1, u2} β γ _inst_1 _inst_2)))) f) l))
Case conversion may be inaccurate. Consider using '#align ring_hom.map_list_sum RingHom.map_list_sumₓ'. -/
/-- Deprecated: use `_root_.map_list_sum` instead. -/
protected theorem RingHom.map_list_sum [NonAssocSemiring β] [NonAssocSemiring γ] (f : β →+* γ)
    (l : List β) : f l.Sum = (l.map f).Sum :=
  map_list_sum f l
#align ring_hom.map_list_sum RingHom.map_list_sum

/- warning: ring_hom.unop_map_list_prod -> RingHom.unop_map_list_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : Semiring.{u1} β] [_inst_2 : Semiring.{u2} γ] (f : RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.nonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) (l : List.{u1} β), Eq.{succ u2} γ (MulOpposite.unop.{u2} γ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.nonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) (fun (_x : RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.nonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) => β -> (MulOpposite.{u2} γ)) (RingHom.hasCoeToFun.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.nonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) f (List.prod.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)))) (AddMonoidWithOne.toOne.{u1} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} β (NonAssocSemiring.toAddCommMonoidWithOne.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)))) l))) (List.prod.{u2} γ (Distrib.toHasMul.{u2} γ (NonUnitalNonAssocSemiring.toDistrib.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)))) (AddMonoidWithOne.toOne.{u2} γ (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} γ (NonAssocSemiring.toAddCommMonoidWithOne.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)))) (List.reverse.{u2} γ (List.map.{u1, u2} β γ (Function.comp.{succ u1, succ u2, succ u2} β (MulOpposite.{u2} γ) γ (MulOpposite.unop.{u2} γ) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.nonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) (fun (_x : RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.nonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) => β -> (MulOpposite.{u2} γ)) (RingHom.hasCoeToFun.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.nonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) f)) l)))
but is expected to have type
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : Semiring.{u1} β] [_inst_2 : Semiring.{u2} γ] (f : RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) (l : List.{u1} β), Eq.{succ u2} γ (MulOpposite.unop.{u2} γ (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => MulOpposite.{u2} γ) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) β (MulOpposite.{u2} γ) (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} (MulOpposite.{u2} γ) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (MulOpposite.{u2} γ) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) β (MulOpposite.{u2} γ) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (MulOpposite.{u2} γ) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)))))) f (List.prod.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1))) (Semiring.toOne.{u1} β _inst_1) l))) (List.prod.{u2} γ (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) (Semiring.toOne.{u2} γ _inst_2) (List.reverse.{u2} γ (List.map.{u1, u2} β γ (Function.comp.{succ u1, succ u2, succ u2} β (MulOpposite.{u2} γ) γ (MulOpposite.unop.{u2} γ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => MulOpposite.{u2} γ) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) β (MulOpposite.{u2} γ) (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} (MulOpposite.{u2} γ) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (MulOpposite.{u2} γ) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) β (MulOpposite.{u2} γ) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (MulOpposite.{u2} γ) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2))) β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} β (MulOpposite.{u2} γ) (Semiring.toNonAssocSemiring.{u1} β _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ _inst_2)))))) f)) l)))
Case conversion may be inaccurate. Consider using '#align ring_hom.unop_map_list_prod RingHom.unop_map_list_prodₓ'. -/
/-- A morphism into the opposite ring acts on the product by acting on the reversed elements.

Deprecated: use `_root_.unop_map_list_prod` instead.
-/
protected theorem RingHom.unop_map_list_prod [Semiring β] [Semiring γ] (f : β →+* γᵐᵒᵖ)
    (l : List β) : MulOpposite.unop (f l.Prod) = (l.map (MulOpposite.unop ∘ f)).reverse.Prod :=
  unop_map_list_prod f l
#align ring_hom.unop_map_list_prod RingHom.unop_map_list_prod

/- warning: ring_hom.map_multiset_prod -> RingHom.map_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : CommSemiring.{u1} β] [_inst_2 : CommSemiring.{u2} γ] (f : RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) (s : Multiset.{u1} β), Eq.{succ u2} γ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) (fun (_x : RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) => β -> γ) (RingHom.hasCoeToFun.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) f (Multiset.prod.{u1} β (CommSemiring.toCommMonoid.{u1} β _inst_1) s)) (Multiset.prod.{u2} γ (CommSemiring.toCommMonoid.{u2} γ _inst_2) (Multiset.map.{u1, u2} β γ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) (fun (_x : RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) => β -> γ) (RingHom.hasCoeToFun.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) f) s))
but is expected to have type
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : CommSemiring.{u1} β] [_inst_2 : CommSemiring.{u2} γ] (f : RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) (s : Multiset.{u1} β), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) (Multiset.prod.{u1} β (CommSemiring.toCommMonoid.{u1} β _inst_1) s)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2)))))) f (Multiset.prod.{u1} β (CommSemiring.toCommMonoid.{u1} β _inst_1) s)) (Multiset.prod.{u2} γ (CommSemiring.toCommMonoid.{u2} γ _inst_2) (Multiset.map.{u1, u2} β γ (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2))) β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u2} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u2} γ (CommSemiring.toSemiring.{u2} γ _inst_2)))))) f) s))
Case conversion may be inaccurate. Consider using '#align ring_hom.map_multiset_prod RingHom.map_multiset_prodₓ'. -/
/-- Deprecated: use `_root_.map_multiset_prod` instead. -/
protected theorem RingHom.map_multiset_prod [CommSemiring β] [CommSemiring γ] (f : β →+* γ)
    (s : Multiset β) : f s.Prod = (s.map f).Prod :=
  map_multiset_prod f s
#align ring_hom.map_multiset_prod RingHom.map_multiset_prod

/- warning: ring_hom.map_multiset_sum -> RingHom.map_multiset_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} β] [_inst_2 : NonAssocSemiring.{u2} γ] (f : RingHom.{u1, u2} β γ _inst_1 _inst_2) (s : Multiset.{u1} β), Eq.{succ u2} γ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} β γ _inst_1 _inst_2) (fun (_x : RingHom.{u1, u2} β γ _inst_1 _inst_2) => β -> γ) (RingHom.hasCoeToFun.{u1, u2} β γ _inst_1 _inst_2) f (Multiset.sum.{u1} β (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) s)) (Multiset.sum.{u2} γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2)) (Multiset.map.{u1, u2} β γ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} β γ _inst_1 _inst_2) (fun (_x : RingHom.{u1, u2} β γ _inst_1 _inst_2) => β -> γ) (RingHom.hasCoeToFun.{u1, u2} β γ _inst_1 _inst_2) f) s))
but is expected to have type
  forall {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} β] [_inst_2 : NonAssocSemiring.{u2} γ] (f : RingHom.{u1, u2} β γ _inst_1 _inst_2) (s : Multiset.{u1} β), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) (Multiset.sum.{u1} β (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) s)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ _inst_1 _inst_2 (RingHom.instRingHomClassRingHom.{u1, u2} β γ _inst_1 _inst_2)))) f (Multiset.sum.{u1} β (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) s)) (Multiset.sum.{u2} γ (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2)) (Multiset.map.{u1, u2} β γ (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u2} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} γ _inst_2) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} β γ _inst_1 _inst_2) β γ _inst_1 _inst_2 (RingHom.instRingHomClassRingHom.{u1, u2} β γ _inst_1 _inst_2)))) f) s))
Case conversion may be inaccurate. Consider using '#align ring_hom.map_multiset_sum RingHom.map_multiset_sumₓ'. -/
/-- Deprecated: use `_root_.map_multiset_sum` instead. -/
protected theorem RingHom.map_multiset_sum [NonAssocSemiring β] [NonAssocSemiring γ] (f : β →+* γ)
    (s : Multiset β) : f s.Sum = (s.map f).Sum :=
  map_multiset_sum f s
#align ring_hom.map_multiset_sum RingHom.map_multiset_sum

/- warning: ring_hom.map_prod -> RingHom.map_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommSemiring.{u1} β] [_inst_2 : CommSemiring.{u3} γ] (g : RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) (f : α -> β) (s : Finset.{u2} α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) (fun (_x : RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) => β -> γ) (RingHom.hasCoeToFun.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) g (Finset.prod.{u1, u2} β α (CommSemiring.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x))) (Finset.prod.{u3, u2} γ α (CommSemiring.toCommMonoid.{u3} γ _inst_2) s (fun (x : α) => coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) (fun (_x : RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) => β -> γ) (RingHom.hasCoeToFun.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) g (f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommSemiring.{u1} β] [_inst_2 : CommSemiring.{u3} γ] (g : RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) (f : α -> β) (s : Finset.{u2} α), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) (Finset.prod.{u1, u2} β α (CommSemiring.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x))) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2)))))) g (Finset.prod.{u1, u2} β α (CommSemiring.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x))) (Finset.prod.{u3, u2} γ α (CommSemiring.toCommMonoid.{u3} γ _inst_2) s (fun (x : α) => FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2))) β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2)) (RingHom.instRingHomClassRingHom.{u1, u3} β γ (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)) (Semiring.toNonAssocSemiring.{u3} γ (CommSemiring.toSemiring.{u3} γ _inst_2)))))) g (f x)))
Case conversion may be inaccurate. Consider using '#align ring_hom.map_prod RingHom.map_prodₓ'. -/
/-- Deprecated: use `_root_.map_prod` instead. -/
protected theorem RingHom.map_prod [CommSemiring β] [CommSemiring γ] (g : β →+* γ) (f : α → β)
    (s : Finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) :=
  map_prod g f s
#align ring_hom.map_prod RingHom.map_prod

/- warning: ring_hom.map_sum -> RingHom.map_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : NonAssocSemiring.{u1} β] [_inst_2 : NonAssocSemiring.{u3} γ] (g : RingHom.{u1, u3} β γ _inst_1 _inst_2) (f : α -> β) (s : Finset.{u2} α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (RingHom.{u1, u3} β γ _inst_1 _inst_2) (fun (_x : RingHom.{u1, u3} β γ _inst_1 _inst_2) => β -> γ) (RingHom.hasCoeToFun.{u1, u3} β γ _inst_1 _inst_2) g (Finset.sum.{u1, u2} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) s (fun (x : α) => f x))) (Finset.sum.{u3, u2} γ α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ _inst_2)) s (fun (x : α) => coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (RingHom.{u1, u3} β γ _inst_1 _inst_2) (fun (_x : RingHom.{u1, u3} β γ _inst_1 _inst_2) => β -> γ) (RingHom.hasCoeToFun.{u1, u3} β γ _inst_1 _inst_2) g (f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : NonAssocSemiring.{u1} β] [_inst_2 : NonAssocSemiring.{u3} γ] (g : RingHom.{u1, u3} β γ _inst_1 _inst_2) (f : α -> β) (s : Finset.{u2} α), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) (Finset.sum.{u1, u2} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) s (fun (x : α) => f x))) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (RingHom.{u1, u3} β γ _inst_1 _inst_2) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ _inst_1 _inst_2) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ _inst_1 _inst_2) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ _inst_2) (RingHomClass.toNonUnitalRingHomClass.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ _inst_1 _inst_2) β γ _inst_1 _inst_2 (RingHom.instRingHomClassRingHom.{u1, u3} β γ _inst_1 _inst_2)))) g (Finset.sum.{u1, u2} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) s (fun (x : α) => f x))) (Finset.sum.{u3, u2} γ α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ _inst_2)) s (fun (x : α) => FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (RingHom.{u1, u3} β γ _inst_1 _inst_2) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ _inst_1 _inst_2) β γ (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) (NonUnitalNonAssocSemiring.toMul.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ _inst_2)) (NonUnitalRingHomClass.toMulHomClass.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ _inst_1 _inst_2) β γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ _inst_2) (RingHomClass.toNonUnitalRingHomClass.{max u1 u3, u1, u3} (RingHom.{u1, u3} β γ _inst_1 _inst_2) β γ _inst_1 _inst_2 (RingHom.instRingHomClassRingHom.{u1, u3} β γ _inst_1 _inst_2)))) g (f x)))
Case conversion may be inaccurate. Consider using '#align ring_hom.map_sum RingHom.map_sumₓ'. -/
/-- Deprecated: use `_root_.map_sum` instead. -/
protected theorem RingHom.map_sum [NonAssocSemiring β] [NonAssocSemiring γ] (g : β →+* γ)
    (f : α → β) (s : Finset α) : g (∑ x in s, f x) = ∑ x in s, g (f x) :=
  map_sum g f s
#align ring_hom.map_sum RingHom.map_sum

end Deprecated

/- warning: monoid_hom.coe_finset_prod -> MonoidHom.coe_finset_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MulOneClass.{u1} β] [_inst_2 : CommMonoid.{u3} γ] (f : α -> (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) (s : Finset.{u2} α), Eq.{max (succ u1) (succ u3)} (β -> γ) (coeFn.{succ (max u3 u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (fun (_x : MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) => β -> γ) (MonoidHom.hasCoeToFun.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (Finset.prod.{max u3 u1, u2} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) α (MonoidHom.commMonoid.{u1, u3} β γ _inst_1 _inst_2) s (fun (x : α) => f x))) (Finset.prod.{max u1 u3, u2} (β -> γ) α (Pi.commMonoid.{u1, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_2)) s (fun (x : α) => coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (fun (_x : MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) => β -> γ) (MonoidHom.hasCoeToFun.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MulOneClass.{u1} β] [_inst_2 : CommMonoid.{u3} γ] (f : α -> (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) (s : Finset.{u2} α), Eq.{max (succ u1) (succ u3)} (forall (ᾰ : β), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ (MulOneClass.toMul.{u1} β _inst_1) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) (MonoidHom.monoidHomClass.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))))) (Finset.prod.{max u1 u3, u2} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) α (MonoidHom.commMonoid.{u1, u3} β γ _inst_1 _inst_2) s (fun (x : α) => f x))) (Finset.prod.{max u1 u3, u2} (forall (ᾰ : β), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) ᾰ) α (Pi.commMonoid.{u1, u3} β (fun (ᾰ : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) ᾰ) (fun (i : β) => _inst_2)) s (fun (x : α) => FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ (MulOneClass.toMul.{u1} β _inst_1) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) (MonoidHom.monoidHomClass.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))))) (f x)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_finset_prod MonoidHom.coe_finset_prodₓ'. -/
@[to_additive]
theorem MonoidHom.coe_finset_prod [MulOneClass β] [CommMonoid γ] (f : α → β →* γ) (s : Finset α) :
    ⇑(∏ x in s, f x) = ∏ x in s, f x :=
  (MonoidHom.coeFn β γ).map_prod _ _
#align monoid_hom.coe_finset_prod MonoidHom.coe_finset_prod
#align add_monoid_hom.coe_finset_sum AddMonoidHom.coe_finset_sum

/- warning: monoid_hom.finset_prod_apply -> MonoidHom.finset_prod_apply is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MulOneClass.{u1} β] [_inst_2 : CommMonoid.{u3} γ] (f : α -> (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) (s : Finset.{u2} α) (b : β), Eq.{succ u3} γ (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (fun (_x : MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) => β -> γ) (MonoidHom.hasCoeToFun.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (Finset.prod.{max u3 u1, u2} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) α (MonoidHom.commMonoid.{u1, u3} β γ _inst_1 _inst_2) s (fun (x : α) => f x)) b) (Finset.prod.{u3, u2} γ α _inst_2 s (fun (x : α) => coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (fun (_x : MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) => β -> γ) (MonoidHom.hasCoeToFun.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (f x) b))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MulOneClass.{u1} β] [_inst_2 : CommMonoid.{u3} γ] (f : α -> (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) (s : Finset.{u2} α) (b : β), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) b) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ (MulOneClass.toMul.{u1} β _inst_1) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) (MonoidHom.monoidHomClass.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))))) (Finset.prod.{max u1 u3, u2} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) α (MonoidHom.commMonoid.{u1, u3} β γ _inst_1 _inst_2) s (fun (x : α) => f x)) b) (Finset.prod.{u3, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) b) α _inst_2 s (fun (x : α) => FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β (fun (_x : β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : β) => γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ (MulOneClass.toMul.{u1} β _inst_1) (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))) β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)) (MonoidHom.monoidHomClass.{u1, u3} β γ _inst_1 (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))))) (f x) b))
Case conversion may be inaccurate. Consider using '#align monoid_hom.finset_prod_apply MonoidHom.finset_prod_applyₓ'. -/
-- See also `finset.prod_apply`, with the same conclusion
-- but with the weaker hypothesis `f : α → β → γ`.
@[simp, to_additive]
theorem MonoidHom.finset_prod_apply [MulOneClass β] [CommMonoid γ] (f : α → β →* γ) (s : Finset α)
    (b : β) : (∏ x in s, f x) b = ∏ x in s, f x b :=
  (MonoidHom.eval b).map_prod _ _
#align monoid_hom.finset_prod_apply MonoidHom.finset_prod_apply
#align add_monoid_hom.finset_sum_apply AddMonoidHom.finset_sum_apply

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoid

variable [CommMonoid β]

/- warning: finset.prod_empty -> Finset.prod_empty is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {f : α -> β} [_inst_1 : CommMonoid.{u1} β], Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.hasEmptyc.{u2} α)) (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {f : α -> β} [_inst_1 : CommMonoid.{u1} β], Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α)) (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))
Case conversion may be inaccurate. Consider using '#align finset.prod_empty Finset.prod_emptyₓ'. -/
@[simp, to_additive]
theorem prod_empty : (∏ x in ∅, f x) = 1 :=
  rfl
#align finset.prod_empty Finset.prod_empty
#align finset.sum_empty Finset.sum_empty

/- warning: finset.prod_of_empty -> Finset.prod_of_empty is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : IsEmpty.{succ u2} α] (s : Finset.{u2} α), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => f i)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : IsEmpty.{succ u2} α] (s : Finset.{u2} α), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => f i)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))
Case conversion may be inaccurate. Consider using '#align finset.prod_of_empty Finset.prod_of_emptyₓ'. -/
@[to_additive]
theorem prod_of_empty [IsEmpty α] (s : Finset α) : (∏ i in s, f i) = 1 := by
  rw [eq_empty_of_is_empty s, prod_empty]
#align finset.prod_of_empty Finset.prod_of_empty
#align finset.sum_of_empty Finset.sum_of_empty

/- warning: finset.prod_cons -> Finset.prod_cons is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {a : α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] (h : Not (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s)), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.cons.{u2} α a s h) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {a : α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] (h : Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.cons.{u2} α a s h) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_cons Finset.prod_consₓ'. -/
@[simp, to_additive]
theorem prod_cons (h : a ∉ s) : (∏ x in cons a s h, f x) = f a * ∏ x in s, f x :=
  fold_cons h
#align finset.prod_cons Finset.prod_cons
#align finset.sum_cons Finset.sum_cons

/- warning: finset.prod_insert -> Finset.prod_insert is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {a : α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (Not (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s)) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.hasInsert.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {a : α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_insert Finset.prod_insertₓ'. -/
@[simp, to_additive]
theorem prod_insert [DecidableEq α] : a ∉ s → (∏ x in insert a s, f x) = f a * ∏ x in s, f x :=
  fold_insert
#align finset.prod_insert Finset.prod_insert
#align finset.sum_insert Finset.sum_insert

/- warning: finset.prod_insert_of_eq_one_if_not_mem -> Finset.prod_insert_of_eq_one_if_not_mem is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {a : α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], ((Not (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s)) -> (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.hasInsert.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {a : α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], ((Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) -> (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_insert_of_eq_one_if_not_mem Finset.prod_insert_of_eq_one_if_not_memₓ'. -/
/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `a` is in `s` or `f a = 1`.
-/
@[simp,
  to_additive
      "The sum of `f` over `insert a s` is the same as\nthe sum over `s`, as long as `a` is in `s` or `f a = 0`."]
theorem prod_insert_of_eq_one_if_not_mem [DecidableEq α] (h : a ∉ s → f a = 1) :
    (∏ x in insert a s, f x) = ∏ x in s, f x :=
  by
  by_cases hm : a ∈ s
  · simp_rw [insert_eq_of_mem hm]
  · rw [prod_insert hm, h hm, one_mul]
#align finset.prod_insert_of_eq_one_if_not_mem Finset.prod_insert_of_eq_one_if_not_mem
#align finset.sum_insert_of_eq_zero_if_not_mem Finset.sum_insert_of_eq_zero_if_not_mem

/- warning: finset.prod_insert_one -> Finset.prod_insert_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {a : α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.hasInsert.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {a : α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_insert_one Finset.prod_insert_oneₓ'. -/
/-- The product of `f` over `insert a s` is the same as the product over `s`, as long as `f a = 1`.
-/
@[simp,
  to_additive
      "The sum of `f` over `insert a s` is the same as\nthe sum over `s`, as long as `f a = 0`."]
theorem prod_insert_one [DecidableEq α] (h : f a = 1) : (∏ x in insert a s, f x) = ∏ x in s, f x :=
  prod_insert_of_eq_one_if_not_mem fun _ => h
#align finset.prod_insert_one Finset.prod_insert_one
#align finset.sum_insert_zero Finset.sum_insert_zero

#print Finset.prod_singleton /-
@[simp, to_additive]
theorem prod_singleton : (∏ x in singleton a, f x) = f a :=
  Eq.trans fold_singleton <| mul_one _
#align finset.prod_singleton Finset.prod_singleton
#align finset.sum_singleton Finset.sum_singleton
-/

/- warning: finset.prod_pair -> Finset.prod_pair is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {a : α} {b : α}, (Ne.{succ u2} α a b) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.hasInsert.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.hasSingleton.{u2} α) b)) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (f b)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {a : α} {b : α}, (Ne.{succ u2} α a b) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) b)) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align finset.prod_pair Finset.prod_pairₓ'. -/
@[to_additive]
theorem prod_pair [DecidableEq α] {a b : α} (h : a ≠ b) :
    (∏ x in ({a, b} : Finset α), f x) = f a * f b := by
  rw [prod_insert (not_mem_singleton.2 h), prod_singleton]
#align finset.prod_pair Finset.prod_pair
#align finset.sum_pair Finset.sum_pair

/- warning: finset.prod_const_one -> Finset.prod_const_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} [_inst_1 : CommMonoid.{u1} β], Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} [_inst_1 : CommMonoid.{u1} β], Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))
Case conversion may be inaccurate. Consider using '#align finset.prod_const_one Finset.prod_const_oneₓ'. -/
@[simp, to_additive]
theorem prod_const_one : (∏ x in s, (1 : β)) = 1 := by
  simp only [Finset.prod, Multiset.map_const, Multiset.prod_replicate, one_pow]
#align finset.prod_const_one Finset.prod_const_one
#align finset.sum_const_zero Finset.sum_const_zero

#print Finset.prod_image /-
@[simp, to_additive]
theorem prod_image [DecidableEq α] {s : Finset γ} {g : γ → α} :
    (∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) → (∏ x in s.image g, f x) = ∏ x in s, f (g x) :=
  fold_image
#align finset.prod_image Finset.prod_image
#align finset.sum_image Finset.sum_image
-/

#print Finset.prod_map /-
@[simp, to_additive]
theorem prod_map (s : Finset α) (e : α ↪ γ) (f : γ → β) :
    (∏ x in s.map e, f x) = ∏ x in s, f (e x) := by
  rw [Finset.prod, Finset.map_val, Multiset.map_map] <;> rfl
#align finset.prod_map Finset.prod_map
#align finset.sum_map Finset.sum_map
-/

#print Finset.prod_congr /-
@[congr, to_additive]
theorem prod_congr (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.Prod f = s₂.Prod g := by
  rw [h] <;> exact fold_congr
#align finset.prod_congr Finset.prod_congr
#align finset.sum_congr Finset.sum_congr
-/

attribute [congr] Finset.sum_congr

/- warning: finset.prod_disj_union -> Finset.prod_disjUnion is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] (h : Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.orderBot.{u2} α) s₁ s₂), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.disjUnion.{u2} α s₁ s₂ h) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] (h : Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s₁ s₂), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.disjUnion.{u2} α s₁ s₂ h) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_disj_union Finset.prod_disjUnionₓ'. -/
@[to_additive]
theorem prod_disjUnion (h) : (∏ x in s₁.disjUnion s₂ h, f x) = (∏ x in s₁, f x) * ∏ x in s₂, f x :=
  by
  refine' Eq.trans _ (fold_disj_union h)
  rw [one_mul]
  rfl
#align finset.prod_disj_union Finset.prod_disjUnion
#align finset.sum_disj_union Finset.sum_disjUnion

/- warning: finset.prod_disj_Union -> Finset.prod_disjUnionᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u3}} {β : Type.{u1}} {α : Type.{u2}} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u3} ι) (t : ι -> (Finset.{u2} α)) (h : Set.PairwiseDisjoint.{u2, u3} (Finset.{u2} α) ι (Finset.partialOrder.{u2} α) (Finset.orderBot.{u2} α) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} ι) (Set.{u3} ι) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} ι) (Set.{u3} ι) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} ι) (Set.{u3} ι) (Finset.Set.hasCoeT.{u3} ι))) s) t), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.disjUnionₓ.{u3, u2} ι α s t h) (fun (x : α) => f x)) (Finset.prod.{u1, u3} β ι _inst_1 s (fun (i : ι) => Finset.prod.{u1, u2} β α _inst_1 (t i) (fun (x : α) => f x)))
but is expected to have type
  forall {ι : Type.{u1}} {β : Type.{u2}} {α : Type.{u3}} {f : α -> β} [_inst_1 : CommMonoid.{u2} β] (s : Finset.{u1} ι) (t : ι -> (Finset.{u3} α)) (h : Set.PairwiseDisjoint.{u3, u1} (Finset.{u3} α) ι (Finset.partialOrder.{u3} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u3} α) (Finset.toSet.{u1} ι s) t), Eq.{succ u2} β (Finset.prod.{u2, u3} β α _inst_1 (Finset.disjUnionᵢ.{u1, u3} ι α s t h) (fun (x : α) => f x)) (Finset.prod.{u2, u1} β ι _inst_1 s (fun (i : ι) => Finset.prod.{u2, u3} β α _inst_1 (t i) (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_disj_Union Finset.prod_disjUnionᵢₓ'. -/
@[to_additive]
theorem prod_disjUnionᵢ (s : Finset ι) (t : ι → Finset α) (h) :
    (∏ x in s.disjUnion t h, f x) = ∏ i in s, ∏ x in t i, f x :=
  by
  refine' Eq.trans _ (fold_disj_Union h)
  dsimp [Finset.prod, Multiset.prod, Multiset.fold, Finset.disjUnion, Finset.fold]
  congr
  exact prod_const_one.symm
#align finset.prod_disj_Union Finset.prod_disjUnionᵢ
#align finset.sum_disj_Union Finset.sum_disjUnionᵢ

/- warning: finset.prod_union_inter -> Finset.prod_union_inter is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Union.union.{u2} (Finset.{u2} α) (Finset.hasUnion.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 (Inter.inter.{u2} (Finset.{u2} α) (Finset.hasInter.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂) (fun (x : α) => f x))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂) (fun (x : α) => f x))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_union_inter Finset.prod_union_interₓ'. -/
@[to_additive]
theorem prod_union_inter [DecidableEq α] :
    ((∏ x in s₁ ∪ s₂, f x) * ∏ x in s₁ ∩ s₂, f x) = (∏ x in s₁, f x) * ∏ x in s₂, f x :=
  fold_union_inter
#align finset.prod_union_inter Finset.prod_union_inter
#align finset.sum_union_inter Finset.sum_union_inter

/- warning: finset.prod_union -> Finset.prod_union is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.orderBot.{u2} α) s₁ s₂) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Union.union.{u2} (Finset.{u2} α) (Finset.hasUnion.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (x : α) => f x))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s₁ s₂) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (x : α) => f x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_union Finset.prod_unionₓ'. -/
@[to_additive]
theorem prod_union [DecidableEq α] (h : Disjoint s₁ s₂) :
    (∏ x in s₁ ∪ s₂, f x) = (∏ x in s₁, f x) * ∏ x in s₂, f x := by
  rw [← prod_union_inter, disjoint_iff_inter_eq_empty.mp h] <;> exact (mul_one _).symm
#align finset.prod_union Finset.prod_union
#align finset.sum_union Finset.sum_union

/- warning: finset.prod_filter_mul_prod_filter_not -> Finset.prod_filter_mul_prod_filter_not is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u2} α) (p : α -> Prop) [_inst_2 : DecidablePred.{succ u2} α p] [_inst_3 : DecidablePred.{succ u2} α (fun (x : α) => Not (p x))] (f : α -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α p (fun (a : α) => _inst_2 a) s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_3 a) s) (fun (x : α) => f x))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u2} α) (p : α -> Prop) [_inst_2 : DecidablePred.{succ u2} α p] [_inst_3 : forall (x : α), Decidable (Not (p x))] (f : α -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α p (fun (a : α) => _inst_2 a) s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_3 a) s) (fun (x : α) => f x))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))
Case conversion may be inaccurate. Consider using '#align finset.prod_filter_mul_prod_filter_not Finset.prod_filter_mul_prod_filter_notₓ'. -/
@[to_additive]
theorem prod_filter_mul_prod_filter_not (s : Finset α) (p : α → Prop) [DecidablePred p]
    [DecidablePred fun x => ¬p x] (f : α → β) :
    ((∏ x in s.filter p, f x) * ∏ x in s.filter fun x => ¬p x, f x) = ∏ x in s, f x :=
  by
  haveI := Classical.decEq α
  rw [← prod_union (disjoint_filter_filter_neg _ _ p), filter_union_filter_neg_eq]
#align finset.prod_filter_mul_prod_filter_not Finset.prod_filter_mul_prod_filter_not
#align finset.sum_filter_add_sum_filter_not Finset.sum_filter_add_sum_filter_not

section ToList

/- warning: finset.prod_to_list -> Finset.prod_to_list is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (List.prod.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (List.map.{u2, u1} α β f (Finset.toList.{u2} α s))) (Finset.prod.{u1, u2} β α _inst_1 s f)
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (List.prod.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)) (List.map.{u2, u1} α β f (Finset.toList.{u2} α s))) (Finset.prod.{u1, u2} β α _inst_1 s f)
Case conversion may be inaccurate. Consider using '#align finset.prod_to_list Finset.prod_to_listₓ'. -/
@[simp, to_additive]
theorem prod_to_list (s : Finset α) (f : α → β) : (s.toList.map f).Prod = s.Prod f := by
  rw [Finset.prod, ← Multiset.coe_prod, ← Multiset.coe_map, Finset.coe_toList]
#align finset.prod_to_list Finset.prod_to_list
#align finset.sum_to_list Finset.sum_to_list

end ToList

#print Equiv.Perm.prod_comp /-
@[to_additive]
theorem Equiv.Perm.prod_comp (σ : Equiv.Perm α) (s : Finset α) (f : α → β)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x in s, f (σ x)) = ∏ x in s, f x :=
  by
  convert (Prod_map _ σ.to_embedding _).symm
  exact (map_perm hs).symm
#align equiv.perm.prod_comp Equiv.Perm.prod_comp
#align equiv.perm.sum_comp Equiv.Perm.sum_comp
-/

#print Equiv.Perm.prod_comp' /-
@[to_additive]
theorem Equiv.Perm.prod_comp' (σ : Equiv.Perm α) (s : Finset α) (f : α → α → β)
    (hs : { a | σ a ≠ a } ⊆ s) : (∏ x in s, f (σ x) x) = ∏ x in s, f x (σ.symm x) :=
  by
  convert σ.prod_comp s (fun x => f x (σ.symm x)) hs
  ext
  rw [Equiv.symm_apply_apply]
#align equiv.perm.prod_comp' Equiv.Perm.prod_comp'
#align equiv.perm.sum_comp' Equiv.Perm.sum_comp'
-/

end CommMonoid

end Finset

section

open Finset

variable [Fintype α] [CommMonoid β]

/- warning: is_compl.prod_mul_prod -> IsCompl.prod_mul_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u2} α] [_inst_2 : CommMonoid.{u1} β] {s : Finset.{u2} α} {t : Finset.{u2} α}, (IsCompl.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.boundedOrder.{u2} α _inst_1) s t) -> (forall (f : α -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2)))) (Finset.prod.{u1, u2} β α _inst_2 s (fun (i : α) => f i)) (Finset.prod.{u1, u2} β α _inst_2 t (fun (i : α) => f i))) (Finset.prod.{u1, u2} β α _inst_2 (Finset.univ.{u2} α _inst_1) (fun (i : α) => f i)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : Fintype.{u2} α] [_inst_2 : CommMonoid.{u1} β] {s : Finset.{u2} α} {t : Finset.{u2} α}, (IsCompl.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instBoundedOrderFinsetToLEToPreorderPartialOrder.{u2} α _inst_1) s t) -> (forall (f : α -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2)))) (Finset.prod.{u1, u2} β α _inst_2 s (fun (i : α) => f i)) (Finset.prod.{u1, u2} β α _inst_2 t (fun (i : α) => f i))) (Finset.prod.{u1, u2} β α _inst_2 (Finset.univ.{u2} α _inst_1) (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align is_compl.prod_mul_prod IsCompl.prod_mul_prodₓ'. -/
@[to_additive]
theorem IsCompl.prod_mul_prod {s t : Finset α} (h : IsCompl s t) (f : α → β) :
    ((∏ i in s, f i) * ∏ i in t, f i) = ∏ i, f i :=
  (Finset.prod_disjUnion h.Disjoint).symm.trans <| by
    classical rw [Finset.disjUnion_eq_union, ← Finset.sup_eq_union, h.sup_eq_top] <;> rfl
#align is_compl.prod_mul_prod IsCompl.prod_mul_prod
#align is_compl.sum_add_sum IsCompl.sum_add_sum

end

namespace Finset

section CommMonoid

variable [CommMonoid β]

/- warning: finset.prod_mul_prod_compl -> Finset.prod_mul_prod_compl is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : Fintype.{u2} α] [_inst_3 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => f i)) (Finset.prod.{u1, u2} β α _inst_1 (HasCompl.compl.{u2} (Finset.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} α) (Finset.booleanAlgebra.{u2} α _inst_2 (fun (a : α) (b : α) => _inst_3 a b))) s) (fun (i : α) => f i))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_2) (fun (i : α) => f i))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : Fintype.{u2} α] [_inst_3 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => f i)) (Finset.prod.{u1, u2} β α _inst_1 (HasCompl.compl.{u2} (Finset.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} α) (Finset.instBooleanAlgebraFinset.{u2} α _inst_2 (fun (a : α) (b : α) => _inst_3 a b))) s) (fun (i : α) => f i))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_2) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finset.prod_mul_prod_compl Finset.prod_mul_prod_complₓ'. -/
/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `fintype.prod_subtype_mul_prod_subtype`. -/
@[to_additive
      "Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.\nFor a version expressed with subtypes, see `fintype.sum_subtype_add_sum_subtype`. "]
theorem prod_mul_prod_compl [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    ((∏ i in s, f i) * ∏ i in sᶜ, f i) = ∏ i, f i :=
  IsCompl.prod_mul_prod isCompl_compl f
#align finset.prod_mul_prod_compl Finset.prod_mul_prod_compl
#align finset.sum_add_sum_compl Finset.sum_add_sum_compl

/- warning: finset.prod_compl_mul_prod -> Finset.prod_compl_mul_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : Fintype.{u2} α] [_inst_3 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (HasCompl.compl.{u2} (Finset.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} α) (Finset.booleanAlgebra.{u2} α _inst_2 (fun (a : α) (b : α) => _inst_3 a b))) s) (fun (i : α) => f i)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => f i))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_2) (fun (i : α) => f i))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : Fintype.{u2} α] [_inst_3 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (HasCompl.compl.{u2} (Finset.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} α) (Finset.instBooleanAlgebraFinset.{u2} α _inst_2 (fun (a : α) (b : α) => _inst_3 a b))) s) (fun (i : α) => f i)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => f i))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_2) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finset.prod_compl_mul_prod Finset.prod_compl_mul_prodₓ'. -/
@[to_additive]
theorem prod_compl_mul_prod [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    ((∏ i in sᶜ, f i) * ∏ i in s, f i) = ∏ i, f i :=
  (@isCompl_compl _ s _).symm.prod_mul_prod f
#align finset.prod_compl_mul_prod Finset.prod_compl_mul_prod
#align finset.sum_compl_add_sum Finset.sum_compl_add_sum

/- warning: finset.prod_sdiff -> Finset.prod_sdiff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.hasSubset.{u2} α) s₁ s₂) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.hasSdiff.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₂ s₁) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (x : α) => f x))) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₁ s₂) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.instSDiffFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₂ s₁) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (x : α) => f x))) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_sdiff Finset.prod_sdiffₓ'. -/
@[to_additive]
theorem prod_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) :
    ((∏ x in s₂ \ s₁, f x) * ∏ x in s₁, f x) = ∏ x in s₂, f x := by
  rw [← prod_union sdiff_disjoint, sdiff_union_of_subset h]
#align finset.prod_sdiff Finset.prod_sdiff
#align finset.sum_sdiff Finset.sum_sdiff

/- warning: finset.prod_disj_sum -> Finset.prod_disj_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u2} α) (t : Finset.{u3} γ) (f : (Sum.{u2, u3} α γ) -> β), Eq.{succ u1} β (Finset.prod.{u1, max u2 u3} β (Sum.{u2, u3} α γ) _inst_1 (Finset.disjSum.{u2, u3} α γ s t) (fun (x : Sum.{u2, u3} α γ) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f (Sum.inl.{u2, u3} α γ x))) (Finset.prod.{u1, u3} β γ _inst_1 t (fun (x : γ) => f (Sum.inr.{u2, u3} α γ x))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u2} α) (t : Finset.{u3} γ) (f : (Sum.{u2, u3} α γ) -> β), Eq.{succ u1} β (Finset.prod.{u1, max u2 u3} β (Sum.{u2, u3} α γ) _inst_1 (Finset.disjSum.{u2, u3} α γ s t) (fun (x : Sum.{u2, u3} α γ) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f (Sum.inl.{u2, u3} α γ x))) (Finset.prod.{u1, u3} β γ _inst_1 t (fun (x : γ) => f (Sum.inr.{u2, u3} α γ x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_disj_sum Finset.prod_disj_sumₓ'. -/
@[simp, to_additive]
theorem prod_disj_sum (s : Finset α) (t : Finset γ) (f : Sum α γ → β) :
    (∏ x in s.disjSum t, f x) = (∏ x in s, f (Sum.inl x)) * ∏ x in t, f (Sum.inr x) :=
  by
  rw [← map_inl_disj_union_map_inr, prod_disj_union, Prod_map, Prod_map]
  rfl
#align finset.prod_disj_sum Finset.prod_disj_sum
#align finset.sum_disj_sum Finset.sum_disj_sum

/- warning: finset.prod_sum_elim -> Finset.prod_sum_elim is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u2} α) (t : Finset.{u3} γ) (f : α -> β) (g : γ -> β), Eq.{succ u1} β (Finset.prod.{u1, max u2 u3} β (Sum.{u2, u3} α γ) _inst_1 (Finset.disjSum.{u2, u3} α γ s t) (fun (x : Sum.{u2, u3} α γ) => Sum.elim.{u2, u3, succ u1} α γ β f g x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (Finset.prod.{u1, u3} β γ _inst_1 t (fun (x : γ) => g x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] (s : Finset.{u2} α) (t : Finset.{u3} γ) (f : α -> β) (g : γ -> β), Eq.{succ u1} β (Finset.prod.{u1, max u2 u3} β (Sum.{u2, u3} α γ) _inst_1 (Finset.disjSum.{u2, u3} α γ s t) (fun (x : Sum.{u2, u3} α γ) => Sum.elim.{u2, u3, succ u1} α γ β f g x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (Finset.prod.{u1, u3} β γ _inst_1 t (fun (x : γ) => g x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_sum_elim Finset.prod_sum_elimₓ'. -/
@[to_additive]
theorem prod_sum_elim (s : Finset α) (t : Finset γ) (f : α → β) (g : γ → β) :
    (∏ x in s.disjSum t, Sum.elim f g x) = (∏ x in s, f x) * ∏ x in t, g x := by simp
#align finset.prod_sum_elim Finset.prod_sum_elim
#align finset.sum_sum_elim Finset.sum_sum_elim

/- warning: finset.prod_bUnion -> Finset.prod_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u3} γ} {t : γ -> (Finset.{u2} α)}, (Set.PairwiseDisjoint.{u2, u3} (Finset.{u2} α) γ (Finset.partialOrder.{u2} α) (Finset.orderBot.{u2} α) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} γ) (Set.{u3} γ) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (Finset.Set.hasCoeT.{u3} γ))) s) t) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.bunionᵢ.{u3, u2} γ α (fun (a : α) (b : α) => _inst_2 a b) s t) (fun (x : α) => f x)) (Finset.prod.{u1, u3} β γ _inst_1 s (fun (x : γ) => Finset.prod.{u1, u2} β α _inst_1 (t x) (fun (i : α) => f i))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u3} γ} {t : γ -> (Finset.{u2} α)}, (Set.PairwiseDisjoint.{u2, u3} (Finset.{u2} α) γ (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) (Finset.toSet.{u3} γ s) t) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.bunionᵢ.{u3, u2} γ α (fun (a : α) (b : α) => _inst_2 a b) s t) (fun (x : α) => f x)) (Finset.prod.{u1, u3} β γ _inst_1 s (fun (x : γ) => Finset.prod.{u1, u2} β α _inst_1 (t x) (fun (i : α) => f i))))
Case conversion may be inaccurate. Consider using '#align finset.prod_bUnion Finset.prod_bunionᵢₓ'. -/
@[to_additive]
theorem prod_bunionᵢ [DecidableEq α] {s : Finset γ} {t : γ → Finset α}
    (hs : Set.PairwiseDisjoint (↑s) t) : (∏ x in s.bUnion t, f x) = ∏ x in s, ∏ i in t x, f i := by
  rw [← disj_Union_eq_bUnion _ _ hs, prod_disj_Union]
#align finset.prod_bUnion Finset.prod_bunionᵢ
#align finset.sum_bUnion Finset.sum_bunionᵢ

/- warning: finset.prod_sigma -> Finset.prod_sigma is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {σ : α -> Type.{u3}} (s : Finset.{u2} α) (t : forall (a : α), Finset.{u3} (σ a)) (f : (Sigma.{u2, u3} α σ) -> β), Eq.{succ u1} β (Finset.prod.{u1, max u2 u3} β (Sigma.{u2, u3} α (fun (i : α) => σ i)) _inst_1 (Finset.sigma.{u2, u3} α (fun (a : α) => σ a) s t) (fun (x : Sigma.{u2, u3} α (fun (i : α) => σ i)) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (a : α) => Finset.prod.{u1, u3} β (σ a) _inst_1 (t a) (fun (s : σ a) => f (Sigma.mk.{u2, u3} α σ a s))))
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u3}} [_inst_1 : CommMonoid.{u2} β] {σ : α -> Type.{u1}} (s : Finset.{u3} α) (t : forall (a : α), Finset.{u1} (σ a)) (f : (Sigma.{u3, u1} α σ) -> β), Eq.{succ u2} β (Finset.prod.{u2, max u3 u1} β (Sigma.{u3, u1} α (fun (i : α) => σ i)) _inst_1 (Finset.sigma.{u3, u1} α (fun (a : α) => σ a) s t) (fun (x : Sigma.{u3, u1} α (fun (i : α) => σ i)) => f x)) (Finset.prod.{u2, u3} β α _inst_1 s (fun (a : α) => Finset.prod.{u2, u1} β (σ a) _inst_1 (t a) (fun (s : σ a) => f (Sigma.mk.{u3, u1} α σ a s))))
Case conversion may be inaccurate. Consider using '#align finset.prod_sigma Finset.prod_sigmaₓ'. -/
/-- Product over a sigma type equals the product of fiberwise products. For rewriting
in the reverse direction, use `finset.prod_sigma'`.  -/
@[to_additive
      "Sum over a sigma type equals the sum of fiberwise sums. For rewriting\nin the reverse direction, use `finset.sum_sigma'`"]
theorem prod_sigma {σ : α → Type _} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : Sigma σ → β) :
    (∏ x in s.Sigma t, f x) = ∏ a in s, ∏ s in t a, f ⟨a, s⟩ := by
  simp_rw [← disj_Union_map_sigma_mk, prod_disj_Union, Prod_map, Function.Embedding.sigmaMk_apply]
#align finset.prod_sigma Finset.prod_sigma
#align finset.sum_sigma Finset.sum_sigma

/- warning: finset.prod_sigma' -> Finset.prod_sigma' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {σ : α -> Type.{u3}} (s : Finset.{u2} α) (t : forall (a : α), Finset.{u3} (σ a)) (f : forall (a : α), (σ a) -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (a : α) => Finset.prod.{u1, u3} β (σ a) _inst_1 (t a) (fun (s : σ a) => f a s))) (Finset.prod.{u1, max u2 u3} β (Sigma.{u2, u3} α (fun (i : α) => σ i)) _inst_1 (Finset.sigma.{u2, u3} α (fun (a : α) => σ a) s t) (fun (x : Sigma.{u2, u3} α (fun (i : α) => σ i)) => f (Sigma.fst.{u2, u3} α (fun (i : α) => σ i) x) (Sigma.snd.{u2, u3} α (fun (i : α) => σ i) x)))
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u3}} [_inst_1 : CommMonoid.{u2} β] {σ : α -> Type.{u1}} (s : Finset.{u3} α) (t : forall (a : α), Finset.{u1} (σ a)) (f : forall (a : α), (σ a) -> β), Eq.{succ u2} β (Finset.prod.{u2, u3} β α _inst_1 s (fun (a : α) => Finset.prod.{u2, u1} β (σ a) _inst_1 (t a) (fun (s : σ a) => f a s))) (Finset.prod.{u2, max u3 u1} β (Sigma.{u3, u1} α (fun (i : α) => σ i)) _inst_1 (Finset.sigma.{u3, u1} α (fun (a : α) => σ a) s t) (fun (x : Sigma.{u3, u1} α (fun (i : α) => σ i)) => f (Sigma.fst.{u3, u1} α (fun (i : α) => σ i) x) (Sigma.snd.{u3, u1} α (fun (i : α) => σ i) x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_sigma' Finset.prod_sigma'ₓ'. -/
@[to_additive]
theorem prod_sigma' {σ : α → Type _} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : ∀ a, σ a → β) :
    (∏ a in s, ∏ s in t a, f a s) = ∏ x in s.Sigma t, f x.1 x.2 :=
  Eq.symm <| prod_sigma s t fun x => f x.1 x.2
#align finset.prod_sigma' Finset.prod_sigma'
#align finset.sum_sigma' Finset.sum_sigma'

#print Finset.prod_bij /-
/-- Reorder a product.

  The difference with `prod_bij'` is that the bijection is specified as a surjective injection,
  rather than by an inverse function.
-/
@[to_additive
      "\n  Reorder a sum.\n\n  The difference with `sum_bij'` is that the bijection is specified as a surjective injection,\n  rather than by an inverse function.\n"]
theorem prod_bij {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a ∈ s, γ)
    (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) : (∏ x in s, f x) = ∏ x in t, g x :=
  congr_arg Multiset.prod (Multiset.map_eq_map_of_bij_of_nodup f g s.2 t.2 i hi h i_inj i_surj)
#align finset.prod_bij Finset.prod_bij
#align finset.sum_bij Finset.sum_bij
-/

#print Finset.prod_bij' /-
/-- Reorder a product.

  The difference with `prod_bij` is that the bijection is specified with an inverse, rather than
  as a surjective injection.
-/
@[to_additive
      "\n  Reorder a sum.\n\n  The difference with `sum_bij` is that the bijection is specified with an inverse, rather than\n  as a surjective injection.\n"]
theorem prod_bij' {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β} (i : ∀ a ∈ s, γ)
    (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha)) (j : ∀ a ∈ t, α)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) : (∏ x in s, f x) = ∏ x in t, g x :=
  by
  refine' prod_bij i hi h _ _
  · intro a1 a2 h1 h2 eq
    rw [← left_inv a1 h1, ← left_inv a2 h2]
    cc
  · intro b hb
    use j b hb
    use hj b hb
    exact (right_inv b hb).symm
#align finset.prod_bij' Finset.prod_bij'
#align finset.sum_bij' Finset.sum_bij'
-/

/- warning: finset.equiv.prod_comp_finset -> Finset.Equiv.prod_comp_finset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {ι' : Type.{u3}} [_inst_2 : DecidableEq.{succ u2} ι] (e : Equiv.{succ u2, succ u3} ι ι') (f : ι' -> β) {s' : Finset.{u3} ι'} {s : Finset.{u2} ι}, (Eq.{succ u2} (Finset.{u2} ι) s (Finset.image.{u3, u2} ι' ι (fun (a : ι) (b : ι) => _inst_2 a b) (coeFn.{max 1 (max (succ u3) (succ u2)) (succ u2) (succ u3), max (succ u3) (succ u2)} (Equiv.{succ u3, succ u2} ι' ι) (fun (_x : Equiv.{succ u3, succ u2} ι' ι) => ι' -> ι) (Equiv.hasCoeToFun.{succ u3, succ u2} ι' ι) (Equiv.symm.{succ u2, succ u3} ι ι' e)) s')) -> (Eq.{succ u1} β (Finset.prod.{u1, u3} β ι' _inst_1 s' (fun (i' : ι') => f i')) (Finset.prod.{u1, u2} β ι _inst_1 s (fun (i : ι) => f (coeFn.{max 1 (max (succ u2) (succ u3)) (succ u3) (succ u2), max (succ u2) (succ u3)} (Equiv.{succ u2, succ u3} ι ι') (fun (_x : Equiv.{succ u2, succ u3} ι ι') => ι -> ι') (Equiv.hasCoeToFun.{succ u2, succ u3} ι ι') e i))))
but is expected to have type
  forall {ι : Type.{u1}} {β : Type.{u3}} [_inst_1 : CommMonoid.{u3} β] {ι' : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} ι] (e : Equiv.{succ u1, succ u2} ι ι') (f : ι' -> β) {s' : Finset.{u2} ι'} {s : Finset.{u1} ι}, (Eq.{succ u1} (Finset.{u1} ι) s (Finset.image.{u2, u1} ι' ι (fun (a : ι) (b : ι) => _inst_2 a b) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : ι') => ι) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} ι' ι) ι' ι (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} ι' ι) ι' ι (Equiv.instEquivLikeEquiv.{succ u2, succ u1} ι' ι))) (Equiv.symm.{succ u1, succ u2} ι ι' e)) s')) -> (Eq.{succ u3} β (Finset.prod.{u3, u2} β ι' _inst_1 s' (fun (i' : ι') => f i')) (Finset.prod.{u3, u1} β ι _inst_1 s (fun (i : ι) => f (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Equiv.{succ u1, succ u2} ι ι') ι (fun (_x : ι) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : ι) => ι') _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Equiv.{succ u1, succ u2} ι ι') ι ι' (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Equiv.{succ u1, succ u2} ι ι') ι ι' (Equiv.instEquivLikeEquiv.{succ u1, succ u2} ι ι'))) e i))))
Case conversion may be inaccurate. Consider using '#align finset.equiv.prod_comp_finset Finset.Equiv.prod_comp_finsetₓ'. -/
/-- Reindexing a product over a finset along an equivalence.
See `equiv.prod_comp` for the version where `s` and `s'` are `univ`. -/
@[to_additive
      " Reindexing a sum over a finset along an equivalence.\nSee `equiv.sum_comp` for the version where `s` and `s'` are `univ`. "]
theorem Equiv.prod_comp_finset {ι'} [DecidableEq ι] (e : ι ≃ ι') (f : ι' → β) {s' : Finset ι'}
    {s : Finset ι} (h : s = s'.image e.symm) : (∏ i' in s', f i') = ∏ i in s, f (e i) :=
  by
  rw [h]
  refine'
    Finset.prod_bij' (fun i' hi' => e.symm i') (fun a ha => Finset.mem_image_of_mem _ ha)
      (fun a ha => by simp_rw [e.apply_symm_apply]) (fun i hi => e i) (fun a ha => _)
      (fun a ha => e.apply_symm_apply a) fun a ha => e.symm_apply_apply a
  rcases finset.mem_image.mp ha with ⟨i', hi', rfl⟩
  rwa [e.apply_symm_apply]
#align finset.equiv.prod_comp_finset Finset.Equiv.prod_comp_finset
#align finset.equiv.sum_comp_finset Finset.Equiv.sum_comp_finset

#print Finset.prod_finset_product /-
@[to_additive]
theorem prod_finset_product (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ × α → β} :
    (∏ p in r, f p) = ∏ c in s, ∏ a in t c, f (c, a) :=
  by
  refine' Eq.trans _ (prod_sigma s t fun p => f (p.1, p.2))
  exact
    prod_bij' (fun p hp => ⟨p.1, p.2⟩) (fun p => mem_sigma.mpr ∘ (h p).mp)
      (fun p hp => congr_arg f prod.mk.eta.symm) (fun p hp => (p.1, p.2))
      (fun p => (h (p.1, p.2)).mpr ∘ mem_sigma.mp) (fun p hp => Prod.mk.eta) fun p hp => p.eta
#align finset.prod_finset_product Finset.prod_finset_product
#align finset.sum_finset_product Finset.sum_finset_product
-/

#print Finset.prod_finset_product' /-
@[to_additive]
theorem prod_finset_product' (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ → α → β} :
    (∏ p in r, f p.1 p.2) = ∏ c in s, ∏ a in t c, f c a :=
  prod_finset_product r s t h
#align finset.prod_finset_product' Finset.prod_finset_product'
#align finset.sum_finset_product' Finset.sum_finset_product'
-/

#print Finset.prod_finset_product_right /-
@[to_additive]
theorem prod_finset_product_right (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α × γ → β} :
    (∏ p in r, f p) = ∏ c in s, ∏ a in t c, f (a, c) :=
  by
  refine' Eq.trans _ (prod_sigma s t fun p => f (p.2, p.1))
  exact
    prod_bij' (fun p hp => ⟨p.2, p.1⟩) (fun p => mem_sigma.mpr ∘ (h p).mp)
      (fun p hp => congr_arg f prod.mk.eta.symm) (fun p hp => (p.2, p.1))
      (fun p => (h (p.2, p.1)).mpr ∘ mem_sigma.mp) (fun p hp => Prod.mk.eta) fun p hp => p.eta
#align finset.prod_finset_product_right Finset.prod_finset_product_right
#align finset.sum_finset_product_right Finset.sum_finset_product_right
-/

#print Finset.prod_finset_product_right' /-
@[to_additive]
theorem prod_finset_product_right' (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α → γ → β} :
    (∏ p in r, f p.1 p.2) = ∏ c in s, ∏ a in t c, f a c :=
  prod_finset_product_right r s t h
#align finset.prod_finset_product_right' Finset.prod_finset_product_right'
#align finset.sum_finset_product_right' Finset.sum_finset_product_right'
-/

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { occs := occurrences.pos[occurrences.pos] «expr[ ,]»([2]) } -/
#print Finset.prod_fiberwise_of_maps_to /-
@[to_additive]
theorem prod_fiberwise_of_maps_to [DecidableEq γ] {s : Finset α} {t : Finset γ} {g : α → γ}
    (h : ∀ x ∈ s, g x ∈ t) (f : α → β) :
    (∏ y in t, ∏ x in s.filter fun x => g x = y, f x) = ∏ x in s, f x :=
  by
  rw [← disj_Union_filter_eq_of_maps_to h]
  rw [prod_disj_Union]
#align finset.prod_fiberwise_of_maps_to Finset.prod_fiberwise_of_maps_to
#align finset.sum_fiberwise_of_maps_to Finset.sum_fiberwise_of_maps_to
-/

#print Finset.prod_image' /-
@[to_additive]
theorem prod_image' [DecidableEq α] {s : Finset γ} {g : γ → α} (h : γ → β)
    (eq : ∀ c ∈ s, f (g c) = ∏ x in s.filter fun c' => g c' = g c, h x) :
    (∏ x in s.image g, f x) = ∏ x in s, h x :=
  calc
    (∏ x in s.image g, f x) = ∏ x in s.image g, ∏ x in s.filter fun c' => g c' = x, h x :=
      prod_congr rfl fun x hx =>
        let ⟨c, hcs, hc⟩ := mem_image.1 hx
        hc ▸ Eq c hcs
    _ = ∏ x in s, h x := prod_fiberwise_of_maps_to (fun x => mem_image_of_mem g) _
    
#align finset.prod_image' Finset.prod_image'
#align finset.sum_image' Finset.sum_image'
-/

/- warning: finset.prod_mul_distrib -> Finset.prod_mul_distrib is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} {g : α -> β} [_inst_1 : CommMonoid.{u1} β], Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f x) (g x))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => g x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} {g : α -> β} [_inst_1 : CommMonoid.{u1} β], Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f x) (g x))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_mul_distrib Finset.prod_mul_distribₓ'. -/
@[to_additive]
theorem prod_mul_distrib : (∏ x in s, f x * g x) = (∏ x in s, f x) * ∏ x in s, g x :=
  Eq.trans (by rw [one_mul] <;> rfl) fold_op_distrib
#align finset.prod_mul_distrib Finset.prod_mul_distrib
#align finset.sum_add_distrib Finset.sum_add_distrib

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.prod_product /-
@[to_additive]
theorem prod_product {s : Finset γ} {t : Finset α} {f : γ × α → β} :
    (∏ x in s ×ˢ t, f x) = ∏ x in s, ∏ y in t, f (x, y) :=
  prod_finset_product (s ×ˢ t) s (fun a => t) fun p => mem_product
#align finset.prod_product Finset.prod_product
#align finset.sum_product Finset.sum_product
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.prod_product' /-
/-- An uncurried version of `finset.prod_product`. -/
@[to_additive "An uncurried version of `finset.sum_product`"]
theorem prod_product' {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x in s ×ˢ t, f x.1 x.2) = ∏ x in s, ∏ y in t, f x y :=
  prod_product
#align finset.prod_product' Finset.prod_product'
#align finset.sum_product' Finset.sum_product'
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.prod_product_right /-
@[to_additive]
theorem prod_product_right {s : Finset γ} {t : Finset α} {f : γ × α → β} :
    (∏ x in s ×ˢ t, f x) = ∏ y in t, ∏ x in s, f (x, y) :=
  prod_finset_product_right (s ×ˢ t) t (fun a => s) fun p => mem_product.trans and_comm
#align finset.prod_product_right Finset.prod_product_right
#align finset.sum_product_right Finset.sum_product_right
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.prod_product_right' /-
/-- An uncurried version of `finset.prod_product_right`. -/
@[to_additive "An uncurried version of `finset.prod_product_right`"]
theorem prod_product_right' {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x in s ×ˢ t, f x.1 x.2) = ∏ y in t, ∏ x in s, f x y :=
  prod_product_right
#align finset.prod_product_right' Finset.prod_product_right'
#align finset.sum_product_right' Finset.sum_product_right'
-/

#print Finset.prod_comm' /-
/-- Generalization of `finset.prod_comm` to the case when the inner `finset`s depend on the outer
variable. -/
@[to_additive
      "Generalization of `finset.sum_comm` to the case when the inner `finset`s depend on\nthe outer variable."]
theorem prod_comm' {s : Finset γ} {t : γ → Finset α} {t' : Finset α} {s' : α → Finset γ}
    (h : ∀ x y, x ∈ s ∧ y ∈ t x ↔ x ∈ s' y ∧ y ∈ t') {f : γ → α → β} :
    (∏ x in s, ∏ y in t x, f x y) = ∏ y in t', ∏ x in s' y, f x y := by
  classical
    have :
      ∀ z : γ × α,
        (z ∈ s.bUnion fun x => (t x).map <| Function.Embedding.sectr x _) ↔ z.1 ∈ s ∧ z.2 ∈ t z.1 :=
      by
      rintro ⟨x, y⟩
      simp
    exact
      (prod_finset_product' _ _ _ this).symm.trans
        (prod_finset_product_right' _ _ _ fun ⟨x, y⟩ => (this _).trans ((h x y).trans and_comm))
#align finset.prod_comm' Finset.prod_comm'
#align finset.sum_comm' Finset.sum_comm'
-/

#print Finset.prod_comm /-
@[to_additive]
theorem prod_comm {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y :=
  prod_comm' fun _ _ => Iff.rfl
#align finset.prod_comm Finset.prod_comm
#align finset.sum_comm Finset.sum_comm
-/

/- warning: finset.prod_hom_rel -> Finset.prod_hom_rel is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : CommMonoid.{u3} γ] {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ} {s : Finset.{u2} α}, (r (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) (OfNat.ofNat.{u3} γ 1 (OfNat.mk.{u3} γ 1 (One.one.{u3} γ (MulOneClass.toHasOne.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))))))) -> (forall (a : α) (b : β) (c : γ), (r b c) -> (r (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) b) (HMul.hMul.{u3, u3, u3} γ γ γ (instHMul.{u3} γ (MulOneClass.toHasMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) (g a) c))) -> (r (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (Finset.prod.{u3, u2} γ α _inst_2 s (fun (x : α) => g x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : CommMonoid.{u3} γ] {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ} {s : Finset.{u2} α}, (r (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (OfNat.ofNat.{u3} γ 1 (One.toOfNat1.{u3} γ (Monoid.toOne.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2))))) -> (forall (a : α) (b : β) (c : γ), (r b c) -> (r (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) b) (HMul.hMul.{u3, u3, u3} γ γ γ (instHMul.{u3} γ (MulOneClass.toMul.{u3} γ (Monoid.toMulOneClass.{u3} γ (CommMonoid.toMonoid.{u3} γ _inst_2)))) (g a) c))) -> (r (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (Finset.prod.{u3, u2} γ α _inst_2 s (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_hom_rel Finset.prod_hom_relₓ'. -/
@[to_additive]
theorem prod_hom_rel [CommMonoid γ] {r : β → γ → Prop} {f : α → β} {g : α → γ} {s : Finset α}
    (h₁ : r 1 1) (h₂ : ∀ a b c, r b c → r (f a * b) (g a * c)) :
    r (∏ x in s, f x) (∏ x in s, g x) := by
  delta Finset.prod
  apply Multiset.prod_hom_rel <;> assumption
#align finset.prod_hom_rel Finset.prod_hom_rel
#align finset.sum_hom_rel Finset.sum_hom_rel

/- warning: finset.prod_eq_one -> Finset.prod_eq_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {f : α -> β} {s : Finset.{u2} α}, (forall (x : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {f : α -> β} {s : Finset.{u2} α}, (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_one Finset.prod_eq_oneₓ'. -/
@[to_additive]
theorem prod_eq_one {f : α → β} {s : Finset α} (h : ∀ x ∈ s, f x = 1) : (∏ x in s, f x) = 1 :=
  calc
    (∏ x in s, f x) = ∏ x in s, 1 := Finset.prod_congr rfl h
    _ = 1 := Finset.prod_const_one
    
#align finset.prod_eq_one Finset.prod_eq_one
#align finset.sum_eq_zero Finset.sum_eq_zero

/- warning: finset.prod_subset_one_on_sdiff -> Finset.prod_subset_one_on_sdiff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} {g : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.hasSubset.{u2} α) s₁ s₂) -> (forall (x : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.hasSdiff.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₂ s₁)) -> (Eq.{succ u1} β (g x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (forall (x : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s₁) -> (Eq.{succ u1} β (f x) (g x))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (i : α) => f i)) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (i : α) => g i)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} {g : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₁ s₂) -> (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.instSDiffFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₂ s₁)) -> (Eq.{succ u1} β (g x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s₁) -> (Eq.{succ u1} β (f x) (g x))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (i : α) => f i)) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (i : α) => g i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_subset_one_on_sdiff Finset.prod_subset_one_on_sdiffₓ'. -/
@[to_additive]
theorem prod_subset_one_on_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) (hg : ∀ x ∈ s₂ \ s₁, g x = 1)
    (hfg : ∀ x ∈ s₁, f x = g x) : (∏ i in s₁, f i) = ∏ i in s₂, g i :=
  by
  rw [← prod_sdiff h, prod_eq_one hg, one_mul]
  exact prod_congr rfl hfg
#align finset.prod_subset_one_on_sdiff Finset.prod_subset_one_on_sdiff
#align finset.sum_subset_zero_on_sdiff Finset.sum_subset_zero_on_sdiff

/- warning: finset.prod_subset -> Finset.prod_subset is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β], (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.hasSubset.{u2} α) s₁ s₂) -> (forall (x : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s₂) -> (Not (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s₁)) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β], (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₁ s₂) -> (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s₂) -> (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s₁)) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s₁ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s₂ (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_subset Finset.prod_subsetₓ'. -/
@[to_additive]
theorem prod_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
    (∏ x in s₁, f x) = ∏ x in s₂, f x :=
  haveI := Classical.decEq α
  prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl
#align finset.prod_subset Finset.prod_subset
#align finset.sum_subset Finset.sum_subset

/- warning: finset.prod_filter_of_ne -> Finset.prod_filter_of_ne is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] {p : α -> Prop} [_inst_2 : DecidablePred.{succ u2} α p], (forall (x : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s) -> (Ne.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> (p x)) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α p (fun (a : α) => _inst_2 a) s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] {p : α -> Prop} [_inst_2 : DecidablePred.{succ u2} α p], (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Ne.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> (p x)) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α p (fun (a : α) => _inst_2 a) s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_filter_of_ne Finset.prod_filter_of_neₓ'. -/
@[to_additive]
theorem prod_filter_of_ne {p : α → Prop} [DecidablePred p] (hp : ∀ x ∈ s, f x ≠ 1 → p x) :
    (∏ x in s.filter p, f x) = ∏ x in s, f x :=
  prod_subset (filter_subset _ _) fun x => by
    classical
      rw [not_imp_comm, mem_filter]
      exact fun h₁ h₂ => ⟨h₁, hp _ h₁ h₂⟩
#align finset.prod_filter_of_ne Finset.prod_filter_of_ne
#align finset.sum_filter_of_ne Finset.sum_filter_of_ne

/- warning: finset.prod_filter_ne_one -> Finset.prod_filter_ne_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : forall (x : α), Decidable (Ne.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))], Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α (fun (x : α) => Ne.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) (fun (a : α) => _inst_2 a) s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : forall (x : α), Decidable (Ne.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))], Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α (fun (x : α) => Ne.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) (fun (a : α) => _inst_2 a) s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))
Case conversion may be inaccurate. Consider using '#align finset.prod_filter_ne_one Finset.prod_filter_ne_oneₓ'. -/
-- If we use `[decidable_eq β]` here, some rewrites fail because they find a wrong `decidable`
-- instance first; `{∀ x, decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`
@[to_additive]
theorem prod_filter_ne_one [∀ x, Decidable (f x ≠ 1)] :
    (∏ x in s.filter fun x => f x ≠ 1, f x) = ∏ x in s, f x :=
  prod_filter_of_ne fun _ _ => id
#align finset.prod_filter_ne_one Finset.prod_filter_ne_one
#align finset.sum_filter_ne_zero Finset.sum_filter_ne_zero

/- warning: finset.prod_filter -> Finset.prod_filter is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} [_inst_1 : CommMonoid.{u1} β] (p : α -> Prop) [_inst_2 : DecidablePred.{succ u2} α p] (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α p (fun (a : α) => _inst_2 a) s) (fun (a : α) => f a)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (a : α) => ite.{succ u1} β (p a) (_inst_2 a) (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} [_inst_1 : CommMonoid.{u1} β] (p : α -> Prop) [_inst_2 : DecidablePred.{succ u2} α p] (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α p (fun (a : α) => _inst_2 a) s) (fun (a : α) => f a)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (a : α) => ite.{succ u1} β (p a) (_inst_2 a) (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_filter Finset.prod_filterₓ'. -/
@[to_additive]
theorem prod_filter (p : α → Prop) [DecidablePred p] (f : α → β) :
    (∏ a in s.filter p, f a) = ∏ a in s, if p a then f a else 1 :=
  calc
    (∏ a in s.filter p, f a) = ∏ a in s.filter p, if p a then f a else 1 :=
      prod_congr rfl fun a h => by rw [if_pos (mem_filter.1 h).2]
    _ = ∏ a in s, if p a then f a else 1 :=
      by
      refine' prod_subset (filter_subset _ s) fun x hs h => _
      rw [mem_filter, not_and] at h
      exact if_neg (h hs)
    
#align finset.prod_filter Finset.prod_filter
#align finset.sum_filter Finset.sum_filter

/- warning: finset.prod_eq_single_of_mem -> Finset.prod_eq_single_of_mem is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} (a : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) -> (forall (b : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) b s) -> (Ne.{succ u2} α b a) -> (Eq.{succ u1} β (f b) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (f a))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (forall (b : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) b s) -> (Ne.{succ u2} α b a) -> (Eq.{succ u1} β (f b) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (f a))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_single_of_mem Finset.prod_eq_single_of_memₓ'. -/
@[to_additive]
theorem prod_eq_single_of_mem {s : Finset α} {f : α → β} (a : α) (h : a ∈ s)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) : (∏ x in s, f x) = f a :=
  by
  haveI := Classical.decEq α
  calc
    (∏ x in s, f x) = ∏ x in {a}, f x :=
      by
      refine' (prod_subset _ _).symm
      · intro _ H
        rwa [mem_singleton.1 H]
      · simpa only [mem_singleton]
    _ = f a := prod_singleton
    
#align finset.prod_eq_single_of_mem Finset.prod_eq_single_of_mem
#align finset.sum_eq_single_of_mem Finset.sum_eq_single_of_mem

/- warning: finset.prod_eq_single -> Finset.prod_eq_single is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} (a : α), (forall (b : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) b s) -> (Ne.{succ u2} α b a) -> (Eq.{succ u1} β (f b) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> ((Not (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s)) -> (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (f a))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} (a : α), (forall (b : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) b s) -> (Ne.{succ u2} α b a) -> (Eq.{succ u1} β (f b) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> ((Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) -> (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (f a))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_single Finset.prod_eq_singleₓ'. -/
@[to_additive]
theorem prod_eq_single {s : Finset α} {f : α → β} (a : α) (h₀ : ∀ b ∈ s, b ≠ a → f b = 1)
    (h₁ : a ∉ s → f a = 1) : (∏ x in s, f x) = f a :=
  haveI := Classical.decEq α
  by_cases (fun this : a ∈ s => prod_eq_single_of_mem a this h₀) fun this : a ∉ s =>
    (prod_congr rfl fun b hb => h₀ b hb <| by rintro rfl <;> cc).trans <|
      prod_const_one.trans (h₁ this).symm
#align finset.prod_eq_single Finset.prod_eq_single
#align finset.sum_eq_single Finset.sum_eq_single

/- warning: finset.prod_eq_mul_of_mem -> Finset.prod_eq_mul_of_mem is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} (a : α) (b : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) -> (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) b s) -> (Ne.{succ u2} α a b) -> (forall (c : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) c s) -> (And (Ne.{succ u2} α c a) (Ne.{succ u2} α c b)) -> (Eq.{succ u1} β (f c) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (f b)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} (a : α) (b : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) b s) -> (Ne.{succ u2} α a b) -> (forall (c : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) c s) -> (And (Ne.{succ u2} α c a) (Ne.{succ u2} α c b)) -> (Eq.{succ u1} β (f c) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_mul_of_mem Finset.prod_eq_mul_of_memₓ'. -/
@[to_additive]
theorem prod_eq_mul_of_mem {s : Finset α} {f : α → β} (a b : α) (ha : a ∈ s) (hb : b ∈ s)
    (hn : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : (∏ x in s, f x) = f a * f b :=
  by
  haveI := Classical.decEq α <;> let s' := ({a, b} : Finset α)
  have hu : s' ⊆ s := by
    refine' insert_subset.mpr _
    apply And.intro ha
    apply singleton_subset_iff.mpr hb
  have hf : ∀ c ∈ s, c ∉ s' → f c = 1 := by
    intro c hc hcs
    apply h₀ c hc
    apply not_or_distrib.mp
    intro hab
    apply hcs
    apply mem_insert.mpr
    rw [mem_singleton]
    exact hab
  rw [← prod_subset hu hf]
  exact Finset.prod_pair hn
#align finset.prod_eq_mul_of_mem Finset.prod_eq_mul_of_mem
#align finset.sum_eq_add_of_mem Finset.sum_eq_add_of_mem

/- warning: finset.prod_eq_mul -> Finset.prod_eq_mul is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} (a : α) (b : α), (Ne.{succ u2} α a b) -> (forall (c : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) c s) -> (And (Ne.{succ u2} α c a) (Ne.{succ u2} α c b)) -> (Eq.{succ u1} β (f c) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> ((Not (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s)) -> (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> ((Not (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) b s)) -> (Eq.{succ u1} β (f b) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (f b)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} (a : α) (b : α), (Ne.{succ u2} α a b) -> (forall (c : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) c s) -> (And (Ne.{succ u2} α c a) (Ne.{succ u2} α c b)) -> (Eq.{succ u1} β (f c) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> ((Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) -> (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> ((Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) b s)) -> (Eq.{succ u1} β (f b) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_mul Finset.prod_eq_mulₓ'. -/
@[to_additive]
theorem prod_eq_mul {s : Finset α} {f : α → β} (a b : α) (hn : a ≠ b)
    (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) (ha : a ∉ s → f a = 1) (hb : b ∉ s → f b = 1) :
    (∏ x in s, f x) = f a * f b :=
  by
  haveI := Classical.decEq α <;> by_cases h₁ : a ∈ s <;> by_cases h₂ : b ∈ s
  · exact prod_eq_mul_of_mem a b h₁ h₂ hn h₀
  · rw [hb h₂, mul_one]
    apply prod_eq_single_of_mem a h₁
    exact fun c hc hca => h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩
  · rw [ha h₁, one_mul]
    apply prod_eq_single_of_mem b h₂
    exact fun c hc hcb => h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, hcb⟩
  · rw [ha h₁, hb h₂, mul_one]
    exact
      trans
        (prod_congr rfl fun c hc =>
          h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, ne_of_mem_of_not_mem hc h₂⟩)
        prod_const_one
#align finset.prod_eq_mul Finset.prod_eq_mul
#align finset.sum_eq_add Finset.sum_eq_add

#print Finset.prod_attach /-
@[to_additive]
theorem prod_attach {f : α → β} : (∏ x in s.attach, f x) = ∏ x in s, f x :=
  haveI := Classical.decEq α
  calc
    (∏ x in s.attach, f x.val) = ∏ x in s.attach.image Subtype.val, f x := by
      rw [prod_image] <;> exact fun x _ y _ => Subtype.eq
    _ = _ := by rw [attach_image_val]
    
#align finset.prod_attach Finset.prod_attach
#align finset.sum_attach Finset.sum_attach
-/

#print Finset.prod_subtype_eq_prod_filter /-
/-- A product over `s.subtype p` equals one over `s.filter p`. -/
@[simp, to_additive "A sum over `s.subtype p` equals one over `s.filter p`."]
theorem prod_subtype_eq_prod_filter (f : α → β) {p : α → Prop} [DecidablePred p] :
    (∏ x in s.Subtype p, f x) = ∏ x in s.filter p, f x :=
  by
  conv_lhs => erw [← Prod_map (s.subtype p) (Function.Embedding.subtype _) f]
  exact prod_congr (subtype_map _) fun x hx => rfl
#align finset.prod_subtype_eq_prod_filter Finset.prod_subtype_eq_prod_filter
#align finset.sum_subtype_eq_sum_filter Finset.sum_subtype_eq_sum_filter
-/

#print Finset.prod_subtype_of_mem /-
/-- If all elements of a `finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
@[to_additive
      "If all elements of a `finset` satisfy the predicate `p`, a sum\nover `s.subtype p` equals that sum over `s`."]
theorem prod_subtype_of_mem (f : α → β) {p : α → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) :
    (∏ x in s.Subtype p, f x) = ∏ x in s, f x := by
  simp_rw [prod_subtype_eq_prod_filter, filter_true_of_mem h]
#align finset.prod_subtype_of_mem Finset.prod_subtype_of_mem
#align finset.sum_subtype_of_mem Finset.sum_subtype_of_mem
-/

#print Finset.prod_subtype_map_embedding /-
/-- A product of a function over a `finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `finset`. -/
@[to_additive
      "A sum of a function over a `finset` in a subtype equals a\nsum in the main type of a function that agrees with the first\nfunction on that `finset`."]
theorem prod_subtype_map_embedding {p : α → Prop} {s : Finset { x // p x }} {f : { x // p x } → β}
    {g : α → β} (h : ∀ x : { x // p x }, x ∈ s → g x = f x) :
    (∏ x in s.map (Function.Embedding.subtype _), g x) = ∏ x in s, f x :=
  by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h
#align finset.prod_subtype_map_embedding Finset.prod_subtype_map_embedding
#align finset.sum_subtype_map_embedding Finset.sum_subtype_map_embedding
-/

variable (f s)

#print Finset.prod_coe_sort_eq_attach /-
@[to_additive]
theorem prod_coe_sort_eq_attach (f : s → β) : (∏ i : s, f i) = ∏ i in s.attach, f i :=
  rfl
#align finset.prod_coe_sort_eq_attach Finset.prod_coe_sort_eq_attach
#align finset.sum_coe_sort_eq_attach Finset.sum_coe_sort_eq_attach
-/

#print Finset.prod_coe_sort /-
@[to_additive]
theorem prod_coe_sort : (∏ i : s, f i) = ∏ i in s, f i :=
  prod_attach
#align finset.prod_coe_sort Finset.prod_coe_sort
#align finset.sum_coe_sort Finset.sum_coe_sort
-/

#print Finset.prod_finset_coe /-
@[to_additive]
theorem prod_finset_coe (f : α → β) (s : Finset α) : (∏ i : (s : Set α), f i) = ∏ i in s, f i :=
  prod_coe_sort s f
#align finset.prod_finset_coe Finset.prod_finset_coe
#align finset.sum_finset_coe Finset.sum_finset_coe
-/

variable {f s}

#print Finset.prod_subtype /-
@[to_additive]
theorem prod_subtype {p : α → Prop} {F : Fintype (Subtype p)} (s : Finset α) (h : ∀ x, x ∈ s ↔ p x)
    (f : α → β) : (∏ a in s, f a) = ∏ a : Subtype p, f a :=
  by
  have : (· ∈ s) = p := Set.ext h
  subst p
  rw [← prod_coe_sort]
  congr
#align finset.prod_subtype Finset.prod_subtype
#align finset.sum_subtype Finset.sum_subtype
-/

/- warning: finset.prod_congr_set -> Finset.prod_congr_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : CommMonoid.{u1} α] {β : Type.{u2}} [_inst_3 : Fintype.{u2} β] (s : Set.{u2} β) [_inst_4 : DecidablePred.{succ u2} β (fun (_x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) _x s)] (f : β -> α) (g : (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) -> α), (forall (x : β) (h : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s), Eq.{succ u1} α (f x) (g (Subtype.mk.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) x h))) -> (forall (x : β), (Not (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s)) -> (Eq.{succ u1} α (f x) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_2)))))))) -> (Eq.{succ u1} α (Finset.prod.{u1, u2} α β _inst_2 (Finset.univ.{u2} β _inst_3) f) (Finset.prod.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) _inst_2 (Finset.univ.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) s) (Subtype.fintype.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (fun (a : β) => _inst_4 a) _inst_3)) g))
but is expected to have type
  forall {α : Type.{u2}} [_inst_2 : CommMonoid.{u2} α] {β : Type.{u1}} [_inst_3 : Fintype.{u1} β] (s : Set.{u1} β) [_inst_4 : DecidablePred.{succ u1} β (fun (_x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) _x s)] (f : β -> α) (g : (Set.Elem.{u1} β s) -> α), (forall (x : β) (h : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s), Eq.{succ u2} α (f x) (g (Subtype.mk.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s) x h))) -> (forall (x : β), (Not (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s)) -> (Eq.{succ u2} α (f x) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (Monoid.toOne.{u2} α (CommMonoid.toMonoid.{u2} α _inst_2)))))) -> (Eq.{succ u2} α (Finset.prod.{u2, u1} α β _inst_2 (Finset.univ.{u1} β _inst_3) f) (Finset.prod.{u2, u1} α (Set.Elem.{u1} β s) _inst_2 (Finset.univ.{u1} (Set.Elem.{u1} β s) (Subtype.fintype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s) (fun (a : β) => _inst_4 a) _inst_3)) g))
Case conversion may be inaccurate. Consider using '#align finset.prod_congr_set Finset.prod_congr_setₓ'. -/
/-- The product of a function `g` defined only on a set `s` is equal to
the product of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 1` off `s`. -/
@[to_additive
      "The sum of a function `g` defined only on a set `s` is equal to\nthe sum of a function `f` defined everywhere,\nas long as `f` and `g` agree on `s`, and `f = 0` off `s`."]
theorem prod_congr_set {α : Type _} [CommMonoid α] {β : Type _} [Fintype β] (s : Set β)
    [DecidablePred (· ∈ s)] (f : β → α) (g : s → α) (w : ∀ (x : β) (h : x ∈ s), f x = g ⟨x, h⟩)
    (w' : ∀ x : β, x ∉ s → f x = 1) : Finset.univ.Prod f = Finset.univ.Prod g :=
  by
  rw [← @Finset.prod_subset _ _ s.to_finset Finset.univ f _ (by simp)]
  · rw [Finset.prod_subtype]
    · apply Finset.prod_congr rfl
      exact fun ⟨x, h⟩ _ => w x h
    · simp
  · rintro x _ h
    exact w' x (by simpa using h)
#align finset.prod_congr_set Finset.prod_congr_set
#align finset.sum_congr_set Finset.sum_congr_set

/- warning: finset.prod_apply_dite -> Finset.prod_apply_dite is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {p : α -> Prop} {hp : DecidablePred.{succ u2} α p} [_inst_2 : DecidablePred.{succ u2} α (fun (x : α) => Not (p x))] (f : forall (x : α), (p x) -> γ) (g : forall (x : α), (Not (p x)) -> γ) (h : γ -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => h (dite.{succ u3} γ (p x) (hp x) (fun (hx : p x) => f x hx) (fun (hx : Not (p x)) => g x hx)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s))) _inst_1 (Finset.attach.{u2} α (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s))) => h (f (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) (And.right (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) s) (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x)) (Iff.mp (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) (And (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) s) (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x))) (Finset.mem_filter.{u2} α p (fun (a : α) => hp a) s (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x)) (Subtype.property.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x)))))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s))) _inst_1 (Finset.attach.{u2} α (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s))) => h (g (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x) (And.right (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x) s) (Not (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x))) (Iff.mp (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x) (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) (And (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x) s) (Not (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x)))) (Finset.mem_filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x)) (Subtype.property.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x)))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {p : α -> Prop} {hp : DecidablePred.{succ u2} α p} [_inst_2 : DecidablePred.{succ u2} α (fun (x : α) => Not (p x))] (f : forall (x : α), (p x) -> γ) (g : forall (x : α), (Not (p x)) -> γ) (h : γ -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => h (dite.{succ u3} γ (p x) (hp x) (fun (hx : p x) => f x hx) (fun (hx : Not (p x)) => g x hx)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s))) _inst_1 (Finset.attach.{u2} α (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s))) => h (f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) (And.right (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) s) (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x)) (Iff.mp (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) (And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) s) (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x))) (Finset.mem_filter.{u2} α p (fun (a : α) => hp a) s (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x)) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x)))))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s))) _inst_1 (Finset.attach.{u2} α (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s))) => h (g (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x) (And.right (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x) s) (Not (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x))) (Iff.mp (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x) (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) (And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x) s) (Not (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x)))) (Finset.mem_filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x)) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => _inst_2 a) s)) x)))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_apply_dite Finset.prod_apply_diteₓ'. -/
@[to_additive]
theorem prod_apply_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p}
    [DecidablePred fun x => ¬p x] (f : ∀ x : α, p x → γ) (g : ∀ x : α, ¬p x → γ) (h : γ → β) :
    (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
      (∏ x in (s.filter p).attach, h (f x.1 (mem_filter.mp x.2).2)) *
        ∏ x in (s.filter fun x => ¬p x).attach, h (g x.1 (mem_filter.mp x.2).2) :=
  calc
    (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
        (∏ x in s.filter p, h (if hx : p x then f x hx else g x hx)) *
          ∏ x in s.filter fun x => ¬p x, h (if hx : p x then f x hx else g x hx) :=
      (prod_filter_mul_prod_filter_not s p _).symm
    _ =
        (∏ x in (s.filter p).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) *
          ∏ x in (s.filter fun x => ¬p x).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx) :=
      congr_arg₂ _ prod_attach.symm prod_attach.symm
    _ =
        (∏ x in (s.filter p).attach, h (f x.1 (mem_filter.mp x.2).2)) *
          ∏ x in (s.filter fun x => ¬p x).attach, h (g x.1 (mem_filter.mp x.2).2) :=
      congr_arg₂ _ (prod_congr rfl fun x hx => congr_arg h (dif_pos (mem_filter.mp x.2).2))
        (prod_congr rfl fun x hx => congr_arg h (dif_neg (mem_filter.mp x.2).2))
    
#align finset.prod_apply_dite Finset.prod_apply_dite
#align finset.sum_apply_dite Finset.sum_apply_dite

/- warning: finset.prod_apply_ite -> Finset.prod_apply_ite is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {p : α -> Prop} {hp : DecidablePred.{succ u2} α p} (f : α -> γ) (g : α -> γ) (h : γ -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => h (ite.{succ u3} γ (p x) (hp x) (f x) (g x)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α p (fun (a : α) => hp a) s) (fun (x : α) => h (f x))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s) (fun (x : α) => h (g x))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {p : α -> Prop} {hp : DecidablePred.{succ u2} α p} (f : α -> γ) (g : α -> γ) (h : γ -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => h (ite.{succ u3} γ (p x) (hp x) (f x) (g x)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α p (fun (a : α) => hp a) s) (fun (x : α) => h (f x))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s) (fun (x : α) => h (g x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_apply_ite Finset.prod_apply_iteₓ'. -/
@[to_additive]
theorem prod_apply_ite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f g : α → γ)
    (h : γ → β) :
    (∏ x in s, h (if p x then f x else g x)) =
      (∏ x in s.filter p, h (f x)) * ∏ x in s.filter fun x => ¬p x, h (g x) :=
  trans (prod_apply_dite _ _ _)
    (congr_arg₂ _ (@prod_attach _ _ _ _ (h ∘ f)) (@prod_attach _ _ _ _ (h ∘ g)))
#align finset.prod_apply_ite Finset.prod_apply_ite
#align finset.sum_apply_ite Finset.sum_apply_ite

/- warning: finset.prod_dite -> Finset.prod_dite is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {p : α -> Prop} {hp : DecidablePred.{succ u2} α p} (f : forall (x : α), (p x) -> β) (g : forall (x : α), (Not (p x)) -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => dite.{succ u1} β (p x) (hp x) (fun (hx : p x) => f x hx) (fun (hx : Not (p x)) => g x hx))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s))) _inst_1 (Finset.attach.{u2} α (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s))) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) (And.right (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) s) (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x)) (Iff.mp (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) (And (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) s) (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x))) (Finset.mem_filter.{u2} α p (fun (a : α) => hp a) s (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x)) (Subtype.property.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x))))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s))) _inst_1 (Finset.attach.{u2} α (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s)) (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s))) => g (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s)) x) (And.right (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s)) x) s) (Not (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s)) x))) (Iff.mp (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s)) x) (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s)) (And (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s)) x) s) (Not (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s)) x)))) (Finset.mem_filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s)) x)) (Subtype.property.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s)) x))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {p : α -> Prop} {hp : DecidablePred.{succ u2} α p} (f : forall (x : α), (p x) -> β) (g : forall (x : α), (Not (p x)) -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => dite.{succ u1} β (p x) (hp x) (fun (hx : p x) => f x hx) (fun (hx : Not (p x)) => g x hx))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s))) _inst_1 (Finset.attach.{u2} α (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s))) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) (And.right (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) s) (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x)) (Iff.mp (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) (And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x) s) (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x))) (Finset.mem_filter.{u2} α p (fun (a : α) => hp a) s (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x)) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α p (fun (a : α) => hp a) s)) x))))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s))) _inst_1 (Finset.attach.{u2} α (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s)) (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s))) => g (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s)) x) (And.right (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s)) x) s) (Not (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s)) x))) (Iff.mp (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s)) x) (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s)) (And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s)) x) s) (Not (p (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s)) x)))) (Finset.mem_filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s)) x)) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s)) x))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_dite Finset.prod_diteₓ'. -/
@[to_additive]
theorem prod_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f : ∀ x : α, p x → β)
    (g : ∀ x : α, ¬p x → β) :
    (∏ x in s, if hx : p x then f x hx else g x hx) =
      (∏ x in (s.filter p).attach, f x.1 (mem_filter.mp x.2).2) *
        ∏ x in (s.filter fun x => ¬p x).attach, g x.1 (mem_filter.mp x.2).2 :=
  by simp [prod_apply_dite _ _ fun x => x]
#align finset.prod_dite Finset.prod_dite
#align finset.sum_dite Finset.sum_dite

/- warning: finset.prod_ite -> Finset.prod_ite is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {p : α -> Prop} {hp : DecidablePred.{succ u2} α p} (f : α -> β) (g : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => ite.{succ u1} β (p x) (hp x) (f x) (g x))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α p (fun (a : α) => hp a) s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (hp a)) s) (fun (x : α) => g x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {p : α -> Prop} {hp : DecidablePred.{succ u2} α p} (f : α -> β) (g : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => ite.{succ u1} β (p x) (hp x) (f x) (g x))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α p (fun (a : α) => hp a) s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (hp a)) s) (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_ite Finset.prod_iteₓ'. -/
@[to_additive]
theorem prod_ite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f g : α → β) :
    (∏ x in s, if p x then f x else g x) =
      (∏ x in s.filter p, f x) * ∏ x in s.filter fun x => ¬p x, g x :=
  by simp [prod_apply_ite _ _ fun x => x]
#align finset.prod_ite Finset.prod_ite
#align finset.sum_ite Finset.sum_ite

#print Finset.prod_ite_of_false /-
@[to_additive]
theorem prod_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → β) (h : ∀ x ∈ s, ¬p x) :
    (∏ x in s, if p x then f x else g x) = ∏ x in s, g x :=
  by
  rw [prod_ite]
  simp [filter_false_of_mem h, filter_true_of_mem h]
#align finset.prod_ite_of_false Finset.prod_ite_of_false
#align finset.sum_ite_of_false Finset.sum_ite_of_false
-/

#print Finset.prod_ite_of_true /-
@[to_additive]
theorem prod_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → β) (h : ∀ x ∈ s, p x) :
    (∏ x in s, if p x then f x else g x) = ∏ x in s, f x :=
  by
  simp_rw [← ite_not (p _)]
  apply prod_ite_of_false
  simpa
#align finset.prod_ite_of_true Finset.prod_ite_of_true
#align finset.sum_ite_of_true Finset.sum_ite_of_true
-/

#print Finset.prod_apply_ite_of_false /-
@[to_additive]
theorem prod_apply_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
    (h : ∀ x ∈ s, ¬p x) : (∏ x in s, k (if p x then f x else g x)) = ∏ x in s, k (g x) :=
  by
  simp_rw [apply_ite k]
  exact prod_ite_of_false _ _ h
#align finset.prod_apply_ite_of_false Finset.prod_apply_ite_of_false
#align finset.sum_apply_ite_of_false Finset.sum_apply_ite_of_false
-/

#print Finset.prod_apply_ite_of_true /-
@[to_additive]
theorem prod_apply_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
    (h : ∀ x ∈ s, p x) : (∏ x in s, k (if p x then f x else g x)) = ∏ x in s, k (f x) :=
  by
  simp_rw [apply_ite k]
  exact prod_ite_of_true _ _ h
#align finset.prod_apply_ite_of_true Finset.prod_apply_ite_of_true
#align finset.sum_apply_ite_of_true Finset.sum_apply_ite_of_true
-/

/- warning: finset.prod_extend_by_one -> Finset.prod_extend_by_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => ite.{succ u1} β (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) i s) (f i) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => f i))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => ite.{succ u1} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) i s) (f i) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finset.prod_extend_by_one Finset.prod_extend_by_oneₓ'. -/
@[to_additive]
theorem prod_extend_by_one [DecidableEq α] (s : Finset α) (f : α → β) :
    (∏ i in s, if i ∈ s then f i else 1) = ∏ i in s, f i :=
  prod_congr rfl fun i hi => if_pos hi
#align finset.prod_extend_by_one Finset.prod_extend_by_one
#align finset.sum_extend_by_zero Finset.sum_extend_by_zero

/- warning: finset.prod_ite_mem -> Finset.prod_ite_mem is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (t : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => ite.{succ u1} β (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i t) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) i t) (f i) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) (Finset.prod.{u1, u2} β α _inst_1 (Inter.inter.{u2} (Finset.{u2} α) (Finset.hasInter.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (fun (i : α) => f i))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (t : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => ite.{succ u1} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) i t) (f i) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) (Finset.prod.{u1, u2} β α _inst_1 (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align finset.prod_ite_mem Finset.prod_ite_memₓ'. -/
@[simp, to_additive]
theorem prod_ite_mem [DecidableEq α] (s t : Finset α) (f : α → β) :
    (∏ i in s, if i ∈ t then f i else 1) = ∏ i in s ∩ t, f i := by
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter]
#align finset.prod_ite_mem Finset.prod_ite_mem
#align finset.sum_ite_mem Finset.sum_ite_mem

/- warning: finset.prod_dite_eq -> Finset.prod_dite_eq is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (b : forall (x : α), (Eq.{succ u2} α a x) -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => dite.{succ u1} β (Eq.{succ u2} α a x) (_inst_2 a x) (fun (h : Eq.{succ u2} α a x) => b x h) (fun (h : Not (Eq.{succ u2} α a x)) => OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) (ite.{succ u1} β (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a s) (b a (rfl.{succ u2} α a)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (b : forall (x : α), (Eq.{succ u2} α a x) -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => dite.{succ u1} β (Eq.{succ u2} α a x) (_inst_2 a x) (fun (h : Eq.{succ u2} α a x) => b x h) (fun (h : Not (Eq.{succ u2} α a x)) => OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) (ite.{succ u1} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a s) (b a (rfl.{succ u2} α a)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_dite_eq Finset.prod_dite_eqₓ'. -/
@[simp, to_additive]
theorem prod_dite_eq [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, a = x → β) :
    (∏ x in s, if h : a = x then b x h else 1) = ite (a ∈ s) (b a rfl) 1 :=
  by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros
      rw [dif_neg]
      cc
    · cc
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    intro
    cc
#align finset.prod_dite_eq Finset.prod_dite_eq
#align finset.sum_dite_eq Finset.sum_dite_eq

/- warning: finset.prod_dite_eq' -> Finset.prod_dite_eq' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (b : forall (x : α), (Eq.{succ u2} α x a) -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => dite.{succ u1} β (Eq.{succ u2} α x a) (_inst_2 x a) (fun (h : Eq.{succ u2} α x a) => b x h) (fun (h : Not (Eq.{succ u2} α x a)) => OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) (ite.{succ u1} β (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a s) (b a (rfl.{succ u2} α a)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (b : forall (x : α), (Eq.{succ u2} α x a) -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => dite.{succ u1} β (Eq.{succ u2} α x a) (_inst_2 x a) (fun (h : Eq.{succ u2} α x a) => b x h) (fun (h : Not (Eq.{succ u2} α x a)) => OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) (ite.{succ u1} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a s) (b a (rfl.{succ u2} α a)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_dite_eq' Finset.prod_dite_eq'ₓ'. -/
@[simp, to_additive]
theorem prod_dite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, x = a → β) :
    (∏ x in s, if h : x = a then b x h else 1) = ite (a ∈ s) (b a rfl) 1 :=
  by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros
      rw [dif_neg]
      cc
    · cc
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    intro
    cc
#align finset.prod_dite_eq' Finset.prod_dite_eq'
#align finset.sum_dite_eq' Finset.sum_dite_eq'

/- warning: finset.prod_ite_eq -> Finset.prod_ite_eq is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (b : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => ite.{succ u1} β (Eq.{succ u2} α a x) (_inst_2 a x) (b x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) (ite.{succ u1} β (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a s) (b a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (b : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => ite.{succ u1} β (Eq.{succ u2} α a x) (_inst_2 a x) (b x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) (ite.{succ u1} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a s) (b a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_ite_eq Finset.prod_ite_eqₓ'. -/
@[simp, to_additive]
theorem prod_ite_eq [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x in s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x
#align finset.prod_ite_eq Finset.prod_ite_eq
#align finset.sum_ite_eq Finset.sum_ite_eq

/- warning: finset.prod_ite_eq' -> Finset.prod_ite_eq' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (b : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => ite.{succ u1} β (Eq.{succ u2} α x a) (_inst_2 x a) (b x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) (ite.{succ u1} β (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a s) (b a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (a : α) (b : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => ite.{succ u1} β (Eq.{succ u2} α x a) (_inst_2 x a) (b x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) (ite.{succ u1} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a s) (b a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_ite_eq' Finset.prod_ite_eq'ₓ'. -/
/-- A product taken over a conditional whose condition is an equality test on the index and whose
alternative is `1` has value either the term at that index or `1`.

The difference with `finset.prod_ite_eq` is that the arguments to `eq` are swapped. -/
@[simp,
  to_additive
      "A sum taken over a conditional whose condition is an equality test on the index\nand whose alternative is `0` has value either the term at that index or `0`.\n\nThe difference with `finset.sum_ite_eq` is that the arguments to `eq` are swapped."]
theorem prod_ite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x in s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x
#align finset.prod_ite_eq' Finset.prod_ite_eq'
#align finset.sum_ite_eq' Finset.sum_ite_eq'

#print Finset.prod_ite_index /-
@[to_additive]
theorem prod_ite_index (p : Prop) [Decidable p] (s t : Finset α) (f : α → β) :
    (∏ x in if p then s else t, f x) = if p then ∏ x in s, f x else ∏ x in t, f x :=
  apply_ite (fun s => ∏ x in s, f x) _ _ _
#align finset.prod_ite_index Finset.prod_ite_index
#align finset.sum_ite_index Finset.sum_ite_index
-/

#print Finset.prod_ite_irrel /-
@[simp, to_additive]
theorem prod_ite_irrel (p : Prop) [Decidable p] (s : Finset α) (f g : α → β) :
    (∏ x in s, if p then f x else g x) = if p then ∏ x in s, f x else ∏ x in s, g x := by
  split_ifs with h <;> rfl
#align finset.prod_ite_irrel Finset.prod_ite_irrel
#align finset.sum_ite_irrel Finset.sum_ite_irrel
-/

#print Finset.prod_dite_irrel /-
@[simp, to_additive]
theorem prod_dite_irrel (p : Prop) [Decidable p] (s : Finset α) (f : p → α → β) (g : ¬p → α → β) :
    (∏ x in s, if h : p then f h x else g h x) =
      if h : p then ∏ x in s, f h x else ∏ x in s, g h x :=
  by split_ifs with h <;> rfl
#align finset.prod_dite_irrel Finset.prod_dite_irrel
#align finset.sum_dite_irrel Finset.sum_dite_irrel
-/

/- warning: finset.sum_pi_single' -> Finset.sum_pi_single' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : AddCommMonoid.{u2} M] (i : ι) (x : M) (s : Finset.{u1} ι), Eq.{succ u2} M (Finset.sum.{u2, u1} M ι _inst_3 s (fun (j : ι) => Pi.single.{u1, u2} ι (fun (i : ι) => M) (fun (a : ι) (b : ι) => _inst_2 a b) (fun (i : ι) => AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_3))) i x j)) (ite.{succ u2} M (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (Finset.decidableMem.{u1} ι (fun (a : ι) (b : ι) => _inst_2 a b) i s) x (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_3)))))))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : AddCommMonoid.{u1} M] (i : ι) (x : M) (s : Finset.{u2} ι), Eq.{succ u1} M (Finset.sum.{u1, u2} M ι _inst_3 s (fun (j : ι) => Pi.single.{u2, u1} ι (fun (i : ι) => M) (fun (a : ι) (b : ι) => _inst_2 a b) (fun (i : ι) => AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_3)) i x j)) (ite.{succ u1} M (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (Finset.decidableMem.{u2} ι (fun (a : ι) (b : ι) => _inst_2 a b) i s) x (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_3)))))
Case conversion may be inaccurate. Consider using '#align finset.sum_pi_single' Finset.sum_pi_single'ₓ'. -/
@[simp]
theorem sum_pi_single' {ι M : Type _} [DecidableEq ι] [AddCommMonoid M] (i : ι) (x : M)
    (s : Finset ι) : (∑ j in s, Pi.single i x j) = if i ∈ s then x else 0 :=
  sum_dite_eq' _ _ _
#align finset.sum_pi_single' Finset.sum_pi_single'

/- warning: finset.sum_pi_single -> Finset.sum_pi_single is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : ι -> Type.{u2}} [_inst_2 : DecidableEq.{succ u1} ι] [_inst_3 : forall (i : ι), AddCommMonoid.{u2} (M i)] (i : ι) (f : forall (i : ι), M i) (s : Finset.{u1} ι), Eq.{succ u2} (M i) (Finset.sum.{u2, u1} (M i) ι (_inst_3 i) s (fun (j : ι) => Pi.single.{u1, u2} ι (fun (j : ι) => M j) (fun (a : ι) (b : ι) => _inst_2 a b) (fun (i : ι) => AddZeroClass.toHasZero.{u2} (M i) (AddMonoid.toAddZeroClass.{u2} (M i) (AddCommMonoid.toAddMonoid.{u2} (M i) (_inst_3 i)))) j (f j) i)) (ite.{succ u2} (M i) (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (Finset.decidableMem.{u1} ι (fun (a : ι) (b : ι) => _inst_2 a b) i s) (f i) (OfNat.ofNat.{u2} (M i) 0 (OfNat.mk.{u2} (M i) 0 (Zero.zero.{u2} (M i) (AddZeroClass.toHasZero.{u2} (M i) (AddMonoid.toAddZeroClass.{u2} (M i) (AddCommMonoid.toAddMonoid.{u2} (M i) (_inst_3 i))))))))
but is expected to have type
  forall {ι : Type.{u2}} {M : ι -> Type.{u1}} [_inst_2 : DecidableEq.{succ u2} ι] [_inst_3 : forall (i : ι), AddCommMonoid.{u1} (M i)] (i : ι) (f : forall (i : ι), M i) (s : Finset.{u2} ι), Eq.{succ u1} (M i) (Finset.sum.{u1, u2} (M i) ι (_inst_3 i) s (fun (j : ι) => Pi.single.{u2, u1} ι M (fun (a : ι) (b : ι) => _inst_2 a b) (fun (i : ι) => AddMonoid.toZero.{u1} (M i) (AddCommMonoid.toAddMonoid.{u1} (M i) (_inst_3 i))) j (f j) i)) (ite.{succ u1} (M i) (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (Finset.decidableMem.{u2} ι (fun (a : ι) (b : ι) => _inst_2 a b) i s) (f i) (OfNat.ofNat.{u1} (M i) 0 (Zero.toOfNat0.{u1} (M i) (AddMonoid.toZero.{u1} (M i) (AddCommMonoid.toAddMonoid.{u1} (M i) (_inst_3 i))))))
Case conversion may be inaccurate. Consider using '#align finset.sum_pi_single Finset.sum_pi_singleₓ'. -/
@[simp]
theorem sum_pi_single {ι : Type _} {M : ι → Type _} [DecidableEq ι] [∀ i, AddCommMonoid (M i)]
    (i : ι) (f : ∀ i, M i) (s : Finset ι) :
    (∑ j in s, Pi.single j (f j) i) = if i ∈ s then f i else 0 :=
  sum_dite_eq _ _ _
#align finset.sum_pi_single Finset.sum_pi_single

/- warning: finset.prod_bij_ne_one -> Finset.prod_bij_ne_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {t : Finset.{u3} γ} {f : α -> β} {g : γ -> β} (i : forall (a : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) -> (Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> γ), (forall (a : α) (h₁ : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (h₂ : Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))), Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (i a h₁ h₂) t) -> (forall (a₁ : α) (a₂ : α) (h₁₁ : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a₁ s) (h₁₂ : Ne.{succ u1} β (f a₁) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) (h₂₁ : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a₂ s) (h₂₂ : Ne.{succ u1} β (f a₂) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))), (Eq.{succ u3} γ (i a₁ h₁₁ h₁₂) (i a₂ h₂₁ h₂₂)) -> (Eq.{succ u2} α a₁ a₂)) -> (forall (b : γ), (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) b t) -> (Ne.{succ u1} β (g b) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> (Exists.{succ u2} α (fun (a : α) => Exists.{0} (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (fun (h₁ : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) => Exists.{0} (Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) (fun (h₂ : Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) => Eq.{succ u3} γ b (i a h₁ h₂)))))) -> (forall (a : α) (h₁ : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (h₂ : Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))), Eq.{succ u1} β (f a) (g (i a h₁ h₂))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (Finset.prod.{u1, u3} β γ _inst_1 t (fun (x : γ) => g x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {t : Finset.{u3} γ} {f : α -> β} {g : γ -> β} (i : forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> γ), (forall (a : α) (h₁ : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (h₂ : Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))), Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) (i a h₁ h₂) t) -> (forall (a₁ : α) (a₂ : α) (h₁₁ : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a₁ s) (h₁₂ : Ne.{succ u1} β (f a₁) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) (h₂₁ : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a₂ s) (h₂₂ : Ne.{succ u1} β (f a₂) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))), (Eq.{succ u3} γ (i a₁ h₁₁ h₁₂) (i a₂ h₂₁ h₂₂)) -> (Eq.{succ u2} α a₁ a₂)) -> (forall (b : γ), (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) b t) -> (Ne.{succ u1} β (g b) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> (Exists.{succ u2} α (fun (a : α) => Exists.{0} (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (fun (h₁ : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) => Exists.{0} (Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) (fun (h₂ : Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) => Eq.{succ u3} γ b (i a h₁ h₂)))))) -> (forall (a : α) (h₁ : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (h₂ : Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))), Eq.{succ u1} β (f a) (g (i a h₁ h₂))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (Finset.prod.{u1, u3} β γ _inst_1 t (fun (x : γ) => g x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_bij_ne_one Finset.prod_bij_ne_oneₓ'. -/
@[to_additive]
theorem prod_bij_ne_one {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β}
    (i : ∀ a ∈ s, f a ≠ 1 → γ) (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ t)
    (i_inj : ∀ a₁ a₂ h₁₁ h₁₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, g b ≠ 1 → ∃ a h₁ h₂, b = i a h₁ h₂) (h : ∀ a h₁ h₂, f a = g (i a h₁ h₂)) :
    (∏ x in s, f x) = ∏ x in t, g x := by
  classical exact
      calc
        (∏ x in s, f x) = ∏ x in s.filter fun x => f x ≠ 1, f x := prod_filter_ne_one.symm
        _ = ∏ x in t.filter fun x => g x ≠ 1, g x :=
          prod_bij (fun a ha => i a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
            (fun a ha =>
              (mem_filter.mp ha).elim fun h₁ h₂ =>
                mem_filter.mpr ⟨hi a h₁ h₂, fun hg => h₂ (hg ▸ h a h₁ h₂)⟩)
            (fun a ha => (mem_filter.mp ha).elim <| h a)
            (fun a₁ a₂ ha₁ ha₂ =>
              (mem_filter.mp ha₁).elim fun ha₁₁ ha₁₂ =>
                (mem_filter.mp ha₂).elim fun ha₂₁ ha₂₂ => i_inj a₁ a₂ _ _ _ _)
            fun b hb =>
            (mem_filter.mp hb).elim fun h₁ h₂ =>
              let ⟨a, ha₁, ha₂, Eq⟩ := i_surj b h₁ h₂
              ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, Eq⟩
        _ = ∏ x in t, g x := prod_filter_ne_one
        
#align finset.prod_bij_ne_one Finset.prod_bij_ne_one
#align finset.sum_bij_ne_zero Finset.sum_bij_ne_zero

#print Finset.prod_dite_of_false /-
@[to_additive]
theorem prod_dite_of_false {p : α → Prop} {hp : DecidablePred p} (h : ∀ x ∈ s, ¬p x)
    (f : ∀ x : α, p x → β) (g : ∀ x : α, ¬p x → β) :
    (∏ x in s, if hx : p x then f x hx else g x hx) = ∏ x : s, g x.val (h x.val x.property) :=
  prod_bij (fun x hx => ⟨x, hx⟩) (fun x hx => by simp)
    (fun a ha => by
      dsimp
      rw [dif_neg])
    (fun a₁ a₂ h₁ h₂ hh => congr_arg coe hh) fun b hb => ⟨b.1, b.2, by simp⟩
#align finset.prod_dite_of_false Finset.prod_dite_of_false
#align finset.sum_dite_of_false Finset.sum_dite_of_false
-/

#print Finset.prod_dite_of_true /-
@[to_additive]
theorem prod_dite_of_true {p : α → Prop} {hp : DecidablePred p} (h : ∀ x ∈ s, p x)
    (f : ∀ x : α, p x → β) (g : ∀ x : α, ¬p x → β) :
    (∏ x in s, if hx : p x then f x hx else g x hx) = ∏ x : s, f x.val (h x.val x.property) :=
  prod_bij (fun x hx => ⟨x, hx⟩) (fun x hx => by simp)
    (fun a ha => by
      dsimp
      rw [dif_pos])
    (fun a₁ a₂ h₁ h₂ hh => congr_arg coe hh) fun b hb => ⟨b.1, b.2, by simp⟩
#align finset.prod_dite_of_true Finset.prod_dite_of_true
#align finset.sum_dite_of_true Finset.sum_dite_of_true
-/

/- warning: finset.nonempty_of_prod_ne_one -> Finset.nonempty_of_prod_ne_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β], (Ne.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> (Finset.Nonempty.{u2} α s)
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β], (Ne.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> (Finset.Nonempty.{u2} α s)
Case conversion may be inaccurate. Consider using '#align finset.nonempty_of_prod_ne_one Finset.nonempty_of_prod_ne_oneₓ'. -/
@[to_additive]
theorem nonempty_of_prod_ne_one (h : (∏ x in s, f x) ≠ 1) : s.Nonempty :=
  s.eq_empty_or_nonempty.elim (fun H => False.elim <| h <| H.symm ▸ prod_empty) id
#align finset.nonempty_of_prod_ne_one Finset.nonempty_of_prod_ne_one
#align finset.nonempty_of_sum_ne_zero Finset.nonempty_of_sum_ne_zero

/- warning: finset.exists_ne_one_of_prod_ne_one -> Finset.exists_ne_one_of_prod_ne_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β], (Ne.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> (Exists.{succ u2} α (fun (a : α) => Exists.{0} (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (fun (H : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) => Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β], (Ne.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align finset.exists_ne_one_of_prod_ne_one Finset.exists_ne_one_of_prod_ne_oneₓ'. -/
@[to_additive]
theorem exists_ne_one_of_prod_ne_one (h : (∏ x in s, f x) ≠ 1) : ∃ a ∈ s, f a ≠ 1 := by
  classical
    rw [← prod_filter_ne_one] at h
    rcases nonempty_of_prod_ne_one h with ⟨x, hx⟩
    exact ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
#align finset.exists_ne_one_of_prod_ne_one Finset.exists_ne_one_of_prod_ne_one
#align finset.exists_ne_zero_of_sum_ne_zero Finset.exists_ne_zero_of_sum_ne_zero

/- warning: finset.prod_range_succ_comm -> Finset.prod_range_succ_comm is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) (n : Nat), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (x : Nat) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f n) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (x : Nat) => f x)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) (n : Nat), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x : Nat) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f n) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (x : Nat) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_succ_comm Finset.prod_range_succ_commₓ'. -/
@[to_additive]
theorem prod_range_succ_comm (f : ℕ → β) (n : ℕ) :
    (∏ x in range (n + 1), f x) = f n * ∏ x in range n, f x := by
  rw [range_succ, prod_insert not_mem_range_self]
#align finset.prod_range_succ_comm Finset.prod_range_succ_comm
#align finset.sum_range_succ_comm Finset.sum_range_succ_comm

/- warning: finset.prod_range_succ -> Finset.prod_range_succ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) (n : Nat), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (x : Nat) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (x : Nat) => f x)) (f n))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) (n : Nat), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x : Nat) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (x : Nat) => f x)) (f n))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_succ Finset.prod_range_succₓ'. -/
@[to_additive]
theorem prod_range_succ (f : ℕ → β) (n : ℕ) :
    (∏ x in range (n + 1), f x) = (∏ x in range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]
#align finset.prod_range_succ Finset.prod_range_succ
#align finset.sum_range_succ Finset.sum_range_succ

/- warning: finset.prod_range_succ' -> Finset.prod_range_succ' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) (n : Nat), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => f k)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) (n : Nat), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => f k)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_succ' Finset.prod_range_succ'ₓ'. -/
@[to_additive]
theorem prod_range_succ' (f : ℕ → β) :
    ∀ n : ℕ, (∏ k in range (n + 1), f k) = (∏ k in range n, f (k + 1)) * f 0
  | 0 => prod_range_succ _ _
  | n + 1 => by rw [prod_range_succ _ n, mul_right_comm, ← prod_range_succ', prod_range_succ]
#align finset.prod_range_succ' Finset.prod_range_succ'
#align finset.sum_range_succ' Finset.sum_range_succ'

/- warning: finset.eventually_constant_prod -> Finset.eventually_constant_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {u : Nat -> β} {N : Nat}, (forall (n : Nat), (GE.ge.{0} Nat Nat.hasLe n N) -> (Eq.{succ u1} β (u n) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (forall {n : Nat}, (LE.le.{0} Nat Nat.hasLe N n) -> (Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => u k)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) N (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => u k))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {u : Nat -> β} {N : Nat}, (forall (n : Nat), (GE.ge.{0} Nat instLENat n N) -> (Eq.{succ u1} β (u n) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (forall {n : Nat}, (LE.le.{0} Nat instLENat N n) -> (Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => u k)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) N (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => u k))))
Case conversion may be inaccurate. Consider using '#align finset.eventually_constant_prod Finset.eventually_constant_prodₓ'. -/
@[to_additive]
theorem eventually_constant_prod {u : ℕ → β} {N : ℕ} (hu : ∀ n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
    (∏ k in range (n + 1), u k) = ∏ k in range (N + 1), u k :=
  by
  obtain ⟨m, rfl : n = N + m⟩ := le_iff_exists_add.mp hn
  clear hn
  induction' m with m hm
  · simp
  erw [prod_range_succ, hm]
  simp [hu, @zero_le' ℕ]
#align finset.eventually_constant_prod Finset.eventually_constant_prod
#align finset.eventually_constant_sum Finset.eventually_constant_sum

/- warning: finset.prod_range_add -> Finset.prod_range_add is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) (n : Nat) (m : Nat), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n m)) (fun (x : Nat) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (x : Nat) => f x)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range m) (fun (x : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n x))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) (n : Nat) (m : Nat), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n m)) (fun (x : Nat) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (x : Nat) => f x)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range m) (fun (x : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_add Finset.prod_range_addₓ'. -/
@[to_additive]
theorem prod_range_add (f : ℕ → β) (n m : ℕ) :
    (∏ x in range (n + m), f x) = (∏ x in range n, f x) * ∏ x in range m, f (n + x) :=
  by
  induction' m with m hm
  · simp
  · rw [Nat.add_succ, prod_range_succ, hm, prod_range_succ, mul_assoc]
#align finset.prod_range_add Finset.prod_range_add
#align finset.sum_range_add Finset.sum_range_add

/- warning: finset.prod_range_add_div_prod_range -> Finset.prod_range_add_div_prod_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : CommGroup.{u1} α] (f : Nat -> α) (n : Nat) (m : Nat), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n m)) (fun (k : Nat) => f k)) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.range n) (fun (k : Nat) => f k))) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.range m) (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : CommGroup.{u1} α] (f : Nat -> α) (n : Nat) (m : Nat), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n m)) (fun (k : Nat) => f k)) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.range n) (fun (k : Nat) => f k))) (Finset.prod.{u1, 0} α Nat (CommGroup.toCommMonoid.{u1} α _inst_2) (Finset.range m) (fun (k : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k)))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_add_div_prod_range Finset.prod_range_add_div_prod_rangeₓ'. -/
@[to_additive]
theorem prod_range_add_div_prod_range {α : Type _} [CommGroup α] (f : ℕ → α) (n m : ℕ) :
    ((∏ k in range (n + m), f k) / ∏ k in range n, f k) = ∏ k in Finset.range m, f (n + k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)
#align finset.prod_range_add_div_prod_range Finset.prod_range_add_div_prod_range
#align finset.sum_range_add_sub_sum_range Finset.sum_range_add_sub_sum_range

/- warning: finset.prod_range_zero -> Finset.prod_range_zero is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (fun (k : Nat) => f k)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (fun (k : Nat) => f k)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_zero Finset.prod_range_zeroₓ'. -/
@[to_additive]
theorem prod_range_zero (f : ℕ → β) : (∏ k in range 0, f k) = 1 := by rw [range_zero, prod_empty]
#align finset.prod_range_zero Finset.prod_range_zero
#align finset.sum_range_zero Finset.sum_range_zero

#print Finset.prod_range_one /-
@[to_additive sum_range_one]
theorem prod_range_one (f : ℕ → β) : (∏ k in range 1, f k) = f 0 :=
  by
  rw [range_one]
  apply @prod_singleton β ℕ 0 f
#align finset.prod_range_one Finset.prod_range_one
#align finset.sum_range_one Finset.sum_range_one
-/

open List

/- warning: finset.prod_list_map_count -> Finset.prod_list_map_count is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] (l : List.{u1} α) {M : Type.{u2}} [_inst_3 : CommMonoid.{u2} M] (f : α -> M), Eq.{succ u2} M (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_3))) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_3))) (List.map.{u1, u2} α M f l)) (Finset.prod.{u2, u1} M α _inst_3 (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b) l) (fun (m : α) => HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M (CommMonoid.toMonoid.{u2} M _inst_3))) (f m) (List.count.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m l)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} α] (l : List.{u2} α) {M : Type.{u1}} [_inst_3 : CommMonoid.{u1} M] (f : α -> M), Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)) (List.map.{u2, u1} α M f l)) (Finset.prod.{u1, u2} M α _inst_3 (List.toFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b) l) (fun (m : α) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) (f m) (List.count.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) m l)))
Case conversion may be inaccurate. Consider using '#align finset.prod_list_map_count Finset.prod_list_map_countₓ'. -/
@[to_additive]
theorem prod_list_map_count [DecidableEq α] (l : List α) {M : Type _} [CommMonoid M] (f : α → M) :
    (l.map f).Prod = ∏ m in l.toFinset, f m ^ l.count m :=
  by
  induction' l with a s IH; · simp only [map_nil, prod_nil, count_nil, pow_zero, prod_const_one]
  simp only [List.map, List.prod_cons, to_finset_cons, IH]
  by_cases has : a ∈ s.to_finset
  · rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (not_mem_erase _ _),
      prod_insert (not_mem_erase _ _), ← mul_assoc, count_cons_self, pow_succ]
    congr 1
    refine' prod_congr rfl fun x hx => _
    rw [count_cons_of_ne (ne_of_mem_erase hx)]
  rw [prod_insert has, count_cons_self, count_eq_zero_of_not_mem (mt mem_to_finset.2 has), pow_one]
  congr 1
  refine' prod_congr rfl fun x hx => _
  rw [count_cons_of_ne]
  rintro rfl
  exact has hx
#align finset.prod_list_map_count Finset.prod_list_map_count
#align finset.sum_list_map_count Finset.sum_list_map_count

/- warning: finset.prod_list_count -> Finset.prod_list_count is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : CommMonoid.{u1} α] (s : List.{u1} α), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3))) s) (Finset.prod.{u1, u1} α α _inst_3 (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s) (fun (m : α) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3))) m (List.count.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : CommMonoid.{u1} α] (s : List.{u1} α), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3)) s) (Finset.prod.{u1, u1} α α _inst_3 (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s) (fun (m : α) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3))) m (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) m s)))
Case conversion may be inaccurate. Consider using '#align finset.prod_list_count Finset.prod_list_countₓ'. -/
@[to_additive]
theorem prod_list_count [DecidableEq α] [CommMonoid α] (s : List α) :
    s.Prod = ∏ m in s.toFinset, m ^ s.count m := by simpa using prod_list_map_count s id
#align finset.prod_list_count Finset.prod_list_count
#align finset.sum_list_count Finset.sum_list_count

/- warning: finset.prod_list_count_of_subset -> Finset.prod_list_count_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : CommMonoid.{u1} α] (m : List.{u1} α) (s : Finset.{u1} α), (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m) s) -> (Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3))) m) (Finset.prod.{u1, u1} α α _inst_3 s (fun (i : α) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3))) i (List.count.{u1} α (fun (a : α) (b : α) => _inst_2 a b) i m))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : CommMonoid.{u1} α] (m : List.{u1} α) (s : Finset.{u1} α), (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m) s) -> (Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3)) m) (Finset.prod.{u1, u1} α α _inst_3 s (fun (i : α) => HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3))) i (List.count.{u1} α (instBEq.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) i m))))
Case conversion may be inaccurate. Consider using '#align finset.prod_list_count_of_subset Finset.prod_list_count_of_subsetₓ'. -/
@[to_additive]
theorem prod_list_count_of_subset [DecidableEq α] [CommMonoid α] (m : List α) (s : Finset α)
    (hs : m.toFinset ⊆ s) : m.Prod = ∏ i in s, i ^ m.count i :=
  by
  rw [prod_list_count]
  refine' prod_subset hs fun x _ hx => _
  rw [mem_to_finset] at hx
  rw [count_eq_zero_of_not_mem hx, pow_zero]
#align finset.prod_list_count_of_subset Finset.prod_list_count_of_subset
#align finset.sum_list_count_of_subset Finset.sum_list_count_of_subset

#print Finset.sum_filter_count_eq_countp /-
theorem sum_filter_count_eq_countp [DecidableEq α] (p : α → Prop) [DecidablePred p] (l : List α) :
    (∑ x in l.toFinset.filter p, l.count x) = l.countp p := by
  simp [Finset.sum, sum_map_count_dedup_filter_eq_countp p l]
#align finset.sum_filter_count_eq_countp Finset.sum_filter_count_eq_countp
-/

open Multiset

/- warning: finset.prod_multiset_map_count -> Finset.prod_multiset_map_count is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) {M : Type.{u2}} [_inst_3 : CommMonoid.{u2} M] (f : α -> M), Eq.{succ u2} M (Multiset.prod.{u2} M _inst_3 (Multiset.map.{u1, u2} α M f s)) (Finset.prod.{u2, u1} M α _inst_3 (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s) (fun (m : α) => HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M (CommMonoid.toMonoid.{u2} M _inst_3))) (f m) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m s)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} α] (s : Multiset.{u2} α) {M : Type.{u1}} [_inst_3 : CommMonoid.{u1} M] (f : α -> M), Eq.{succ u1} M (Multiset.prod.{u1} M _inst_3 (Multiset.map.{u2, u1} α M f s)) (Finset.prod.{u1, u2} M α _inst_3 (Multiset.toFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s) (fun (m : α) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) (f m) (Multiset.count.{u2} α (fun (a : α) (b : α) => _inst_2 a b) m s)))
Case conversion may be inaccurate. Consider using '#align finset.prod_multiset_map_count Finset.prod_multiset_map_countₓ'. -/
@[to_additive]
theorem prod_multiset_map_count [DecidableEq α] (s : Multiset α) {M : Type _} [CommMonoid M]
    (f : α → M) : (s.map f).Prod = ∏ m in s.toFinset, f m ^ s.count m :=
  by
  refine' Quot.inductionOn s fun l => _
  simp [prod_list_map_count l f]
#align finset.prod_multiset_map_count Finset.prod_multiset_map_count
#align finset.sum_multiset_map_count Finset.sum_multiset_map_count

#print Finset.prod_multiset_count /-
@[to_additive]
theorem prod_multiset_count [DecidableEq α] [CommMonoid α] (s : Multiset α) :
    s.Prod = ∏ m in s.toFinset, m ^ s.count m :=
  by
  convert prod_multiset_map_count s id
  rw [Multiset.map_id]
#align finset.prod_multiset_count Finset.prod_multiset_count
#align finset.sum_multiset_count Finset.sum_multiset_count
-/

#print Finset.prod_multiset_count_of_subset /-
@[to_additive]
theorem prod_multiset_count_of_subset [DecidableEq α] [CommMonoid α] (m : Multiset α) (s : Finset α)
    (hs : m.toFinset ⊆ s) : m.Prod = ∏ i in s, i ^ m.count i :=
  by
  revert hs
  refine' Quot.inductionOn m fun l => _
  simp only [quot_mk_to_coe'', coe_prod, coe_count]
  apply prod_list_count_of_subset l s
#align finset.prod_multiset_count_of_subset Finset.prod_multiset_count_of_subset
#align finset.sum_multiset_count_of_subset Finset.sum_multiset_count_of_subset
-/

#print Finset.prod_mem_multiset /-
@[to_additive]
theorem prod_mem_multiset [DecidableEq α] (m : Multiset α) (f : { x // x ∈ m } → β) (g : α → β)
    (hfg : ∀ x, f x = g x) : (∏ x : { x // x ∈ m }, f x) = ∏ x in m.toFinset, g x :=
  prod_bij (fun x _ => x.1) (fun x _ => Multiset.mem_toFinset.mpr x.2) (fun _ _ => hfg _)
    (fun _ _ _ _ h => by
      ext
      assumption)
    fun y hy => ⟨⟨y, Multiset.mem_toFinset.mp hy⟩, Finset.mem_univ _, rfl⟩
#align finset.prod_mem_multiset Finset.prod_mem_multiset
#align finset.sum_mem_multiset Finset.sum_mem_multiset
-/

/- warning: finset.prod_induction -> Finset.prod_induction is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {M : Type.{u2}} [_inst_2 : CommMonoid.{u2} M] (f : α -> M) (p : M -> Prop), (forall (a : M) (b : M), (p a) -> (p b) -> (p (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))) a b))) -> (p (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))))))) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (p (f x))) -> (p (Finset.prod.{u2, u1} M α _inst_2 s (fun (x : α) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {s : Finset.{u2} α} {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] (f : α -> M) (p : M -> Prop), (forall (a : M) (b : M), (p a) -> (p b) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) a b))) -> (p (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))))) -> (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (p (f x))) -> (p (Finset.prod.{u1, u2} M α _inst_2 s (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_induction Finset.prod_inductionₓ'. -/
/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors.
-/
@[to_additive
      "To prove a property of a sum, it suffices to prove that\nthe property is additive and holds on summands."]
theorem prod_induction {M : Type _} [CommMonoid M] (f : α → M) (p : M → Prop)
    (p_mul : ∀ a b, p a → p b → p (a * b)) (p_one : p 1) (p_s : ∀ x ∈ s, p <| f x) :
    p <| ∏ x in s, f x :=
  Multiset.prod_induction _ _ p_mul p_one (Multiset.forall_mem_map_iff.mpr p_s)
#align finset.prod_induction Finset.prod_induction
#align finset.sum_induction Finset.sum_induction

/- warning: finset.prod_induction_nonempty -> Finset.prod_induction_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {M : Type.{u2}} [_inst_2 : CommMonoid.{u2} M] (f : α -> M) (p : M -> Prop), (forall (a : M) (b : M), (p a) -> (p b) -> (p (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))) a b))) -> (Finset.Nonempty.{u1} α s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (p (f x))) -> (p (Finset.prod.{u2, u1} M α _inst_2 s (fun (x : α) => f x)))
but is expected to have type
  forall {α : Type.{u2}} {s : Finset.{u2} α} {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] (f : α -> M) (p : M -> Prop), (forall (a : M) (b : M), (p a) -> (p b) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) a b))) -> (Finset.Nonempty.{u2} α s) -> (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (p (f x))) -> (p (Finset.prod.{u1, u2} M α _inst_2 s (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_induction_nonempty Finset.prod_induction_nonemptyₓ'. -/
/-- To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors.
-/
@[to_additive
      "To prove a property of a sum, it suffices to prove that\nthe property is additive and holds on summands."]
theorem prod_induction_nonempty {M : Type _} [CommMonoid M] (f : α → M) (p : M → Prop)
    (p_mul : ∀ a b, p a → p b → p (a * b)) (hs_nonempty : s.Nonempty) (p_s : ∀ x ∈ s, p <| f x) :
    p <| ∏ x in s, f x :=
  Multiset.prod_induction_nonempty p p_mul (by simp [nonempty_iff_ne_empty.mp hs_nonempty])
    (Multiset.forall_mem_map_iff.mpr p_s)
#align finset.prod_induction_nonempty Finset.prod_induction_nonempty
#align finset.sum_induction_nonempty Finset.sum_induction_nonempty

/- warning: finset.prod_range_induction -> Finset.prod_range_induction is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) (s : Nat -> β), (Eq.{succ u1} β (s (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> (forall (n : Nat), Eq.{succ u1} β (s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (s n) (f n))) -> (forall (n : Nat), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (k : Nat) => f k)) (s n))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] (f : Nat -> β) (s : Nat -> β), (Eq.{succ u1} β (s (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> (forall (n : Nat), Eq.{succ u1} β (s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (s n) (f n))) -> (forall (n : Nat), Eq.{succ u1} β (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (k : Nat) => f k)) (s n))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_induction Finset.prod_range_inductionₓ'. -/
/-- For any product along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can verify
that it's equal to a different function just by checking ratios of adjacent terms.

This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
@[to_additive
      "For any sum along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can\nverify that it's equal to a different function just by checking differences of adjacent terms.\n\nThis is a discrete analogue of the fundamental theorem of calculus."]
theorem prod_range_induction (f s : ℕ → β) (h0 : s 0 = 1) (h : ∀ n, s (n + 1) = s n * f n) (n : ℕ) :
    (∏ k in Finset.range n, f k) = s n :=
  by
  induction' n with k hk
  · simp only [h0, Finset.prod_range_zero]
  · simp only [hk, Finset.prod_range_succ, h, mul_comm]
#align finset.prod_range_induction Finset.prod_range_induction
#align finset.sum_range_induction Finset.sum_range_induction

/- warning: finset.prod_range_div -> Finset.prod_range_div is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : CommGroup.{u1} M] (f : Nat -> M) (n : Nat), Eq.{succ u1} M (Finset.prod.{u1, 0} M Nat (CommGroup.toCommMonoid.{u1} M _inst_2) (Finset.range n) (fun (i : Nat) => HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (f i))) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f n) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : CommGroup.{u1} M] (f : Nat -> M) (n : Nat), Eq.{succ u1} M (Finset.prod.{u1, 0} M Nat (CommGroup.toCommMonoid.{u1} M _inst_2) (Finset.range n) (fun (i : Nat) => HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (f i))) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f n) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_div Finset.prod_range_divₓ'. -/
/-- A telescoping product along `{0, ..., n - 1}` of a commutative group valued function reduces to
the ratio of the last and first factors. -/
@[to_additive
      "A telescoping sum along `{0, ..., n - 1}` of an additive commutative group valued\nfunction reduces to the difference of the last and first terms."]
theorem prod_range_div {M : Type _} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i in range n, f (i + 1) / f i) = f n / f 0 := by apply prod_range_induction <;> simp
#align finset.prod_range_div Finset.prod_range_div
#align finset.sum_range_sub Finset.sum_range_sub

/- warning: finset.prod_range_div' -> Finset.prod_range_div' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : CommGroup.{u1} M] (f : Nat -> M) (n : Nat), Eq.{succ u1} M (Finset.prod.{u1, 0} M Nat (CommGroup.toCommMonoid.{u1} M _inst_2) (Finset.range n) (fun (i : Nat) => HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f i) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (f n))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : CommGroup.{u1} M] (f : Nat -> M) (n : Nat), Eq.{succ u1} M (Finset.prod.{u1, 0} M Nat (CommGroup.toCommMonoid.{u1} M _inst_2) (Finset.range n) (fun (i : Nat) => HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f i) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f n))
Case conversion may be inaccurate. Consider using '#align finset.prod_range_div' Finset.prod_range_div'ₓ'. -/
@[to_additive]
theorem prod_range_div' {M : Type _} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i in range n, f i / f (i + 1)) = f 0 / f n := by apply prod_range_induction <;> simp
#align finset.prod_range_div' Finset.prod_range_div'
#align finset.sum_range_sub' Finset.sum_range_sub'

/- warning: finset.eq_prod_range_div -> Finset.eq_prod_range_div is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : CommGroup.{u1} M] (f : Nat -> M) (n : Nat), Eq.{succ u1} M (f n) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))))) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Finset.prod.{u1, 0} M Nat (CommGroup.toCommMonoid.{u1} M _inst_2) (Finset.range n) (fun (i : Nat) => HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (f i))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : CommGroup.{u1} M] (f : Nat -> M) (n : Nat), Eq.{succ u1} M (f n) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (DivInvMonoid.toMonoid.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))))) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Finset.prod.{u1, 0} M Nat (CommGroup.toCommMonoid.{u1} M _inst_2) (Finset.range n) (fun (i : Nat) => HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (f i))))
Case conversion may be inaccurate. Consider using '#align finset.eq_prod_range_div Finset.eq_prod_range_divₓ'. -/
@[to_additive]
theorem eq_prod_range_div {M : Type _} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = f 0 * ∏ i in range n, f (i + 1) / f i := by rw [prod_range_div, mul_div_cancel'_right]
#align finset.eq_prod_range_div Finset.eq_prod_range_div
#align finset.eq_sum_range_sub Finset.eq_sum_range_sub

/- warning: finset.eq_prod_range_div' -> Finset.eq_prod_range_div' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : CommGroup.{u1} M] (f : Nat -> M) (n : Nat), Eq.{succ u1} M (f n) (Finset.prod.{u1, 0} M Nat (CommGroup.toCommMonoid.{u1} M _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (i : Nat) => ite.{succ u1} M (Eq.{1} Nat i (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Nat.decidableEq i (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toHasDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f i) (f (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : CommGroup.{u1} M] (f : Nat -> M) (n : Nat), Eq.{succ u1} M (f n) (Finset.prod.{u1, 0} M Nat (CommGroup.toCommMonoid.{u1} M _inst_2) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (i : Nat) => ite.{succ u1} M (Eq.{1} Nat i (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (instDecidableEqNat i (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (HDiv.hDiv.{u1, u1, u1} M M M (instHDiv.{u1} M (DivInvMonoid.toDiv.{u1} M (Group.toDivInvMonoid.{u1} M (CommGroup.toGroup.{u1} M _inst_2)))) (f i) (f (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align finset.eq_prod_range_div' Finset.eq_prod_range_div'ₓ'. -/
@[to_additive]
theorem eq_prod_range_div' {M : Type _} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = ∏ i in range (n + 1), if i = 0 then f 0 else f i / f (i - 1) :=
  by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]
#align finset.eq_prod_range_div' Finset.eq_prod_range_div'
#align finset.eq_sum_range_sub' Finset.eq_sum_range_sub'

/- warning: finset.sum_range_tsub -> Finset.sum_range_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : CanonicallyOrderedAddMonoid.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2)))) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2))))) _inst_3] [_inst_5 : ContravariantClass.{u1, u1} α α (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2)))))] {f : Nat -> α}, (Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2))) f) -> (forall (n : Nat), Eq.{succ u1} α (Finset.sum.{u1, 0} α Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2)) (Finset.range n) (fun (i : Nat) => HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (f i))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (f n) (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : CanonicallyOrderedAddMonoid.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2)))) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2))))) _inst_3] [_inst_5 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.BigOperators.Basic._hyg.18850 : α) (x._@.Mathlib.Algebra.BigOperators.Basic._hyg.18852 : α) => HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.BigOperators.Basic._hyg.18850 x._@.Mathlib.Algebra.BigOperators.Basic._hyg.18852) (fun (x._@.Mathlib.Algebra.BigOperators.Basic._hyg.18865 : α) (x._@.Mathlib.Algebra.BigOperators.Basic._hyg.18867 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2)))) x._@.Mathlib.Algebra.BigOperators.Basic._hyg.18865 x._@.Mathlib.Algebra.BigOperators.Basic._hyg.18867)] {f : Nat -> α}, (Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{u1} α (OrderedAddCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2))) f) -> (forall (n : Nat), Eq.{succ u1} α (Finset.sum.{u1, 0} α Nat (OrderedAddCommMonoid.toAddCommMonoid.{u1} α (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} α _inst_2)) (Finset.range n) (fun (i : Nat) => HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (f i))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) (f n) (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align finset.sum_range_tsub Finset.sum_range_tsubₓ'. -/
/-- A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function
reduces to the difference of the last and first terms
when the function we are summing is monotone.
-/
theorem sum_range_tsub [CanonicallyOrderedAddMonoid α] [Sub α] [OrderedSub α]
    [ContravariantClass α α (· + ·) (· ≤ ·)] {f : ℕ → α} (h : Monotone f) (n : ℕ) :
    (∑ i in range n, f (i + 1) - f i) = f n - f 0 :=
  by
  refine' sum_range_induction _ _ (tsub_self _) (fun n => _) _
  have h₁ : f n ≤ f (n + 1) := h (Nat.le_succ _)
  have h₂ : f 0 ≤ f n := h (Nat.zero_le _)
  rw [tsub_add_eq_add_tsub h₂, add_tsub_cancel_of_le h₁]
#align finset.sum_range_tsub Finset.sum_range_tsub

#print Finset.prod_const /-
@[simp, to_additive]
theorem prod_const (b : β) : (∏ x in s, b) = b ^ s.card :=
  (congr_arg _ <| s.val.mapConst b).trans <| Multiset.prod_replicate s.card b
#align finset.prod_const Finset.prod_const
#align finset.sum_const Finset.sum_const
-/

#print Finset.pow_eq_prod_const /-
@[to_additive]
theorem pow_eq_prod_const (b : β) : ∀ n, b ^ n = ∏ k in range n, b := by simp
#align finset.pow_eq_prod_const Finset.pow_eq_prod_const
#align finset.nsmul_eq_sum_const Finset.nsmul_eq_sum_const
-/

#print Finset.prod_pow /-
@[to_additive]
theorem prod_pow (s : Finset α) (n : ℕ) (f : α → β) : (∏ x in s, f x ^ n) = (∏ x in s, f x) ^ n :=
  Multiset.prod_map_pow
#align finset.prod_pow Finset.prod_pow
#align finset.sum_nsmul Finset.sum_nsmul
-/

#print Finset.prod_flip /-
@[to_additive]
theorem prod_flip {n : ℕ} (f : ℕ → β) :
    (∏ r in range (n + 1), f (n - r)) = ∏ k in range (n + 1), f k :=
  by
  induction' n with n ih
  · rw [prod_range_one, prod_range_one]
  · rw [prod_range_succ', prod_range_succ _ (Nat.succ n)]
    simp [← ih]
#align finset.prod_flip Finset.prod_flip
#align finset.sum_flip Finset.sum_flip
-/

/- warning: finset.prod_involution -> Finset.prod_involution is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} (g : forall (a : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) -> α), (forall (a : α) (ha : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (f (g a ha))) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> (forall (a : α) (ha : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s), (Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> (Ne.{succ u2} α (g a ha) a)) -> (forall (g_mem : forall (a : α) (ha : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s), Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) (g a ha) s), (forall (a : α) (ha : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s), Eq.{succ u2} α (g (g a ha) (g_mem a ha)) a) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} (g : forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> α), (forall (a : α) (ha : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (f (g a ha))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> (forall (a : α) (ha : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s), (Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> (Ne.{succ u2} α (g a ha) a)) -> (forall (g_mem : forall (a : α) (ha : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s), Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (g a ha) s), (forall (a : α) (ha : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s), Eq.{succ u2} α (g (g a ha) (g_mem a ha)) a) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_involution Finset.prod_involutionₓ'. -/
@[to_additive]
theorem prod_involution {s : Finset α} {f : α → β} :
    ∀ (g : ∀ a ∈ s, α) (h : ∀ a ha, f a * f (g a ha) = 1) (g_ne : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
      (g_mem : ∀ a ha, g a ha ∈ s) (g_inv : ∀ a ha, g (g a ha) (g_mem a ha) = a),
      (∏ x in s, f x) = 1 :=
  by
  haveI := Classical.decEq α <;> haveI := Classical.decEq β <;>
    exact
      Finset.strongInductionOn s fun s ih g h g_ne g_mem g_inv =>
        s.eq_empty_or_nonempty.elim (fun hs => hs.symm ▸ rfl) fun ⟨x, hx⟩ =>
          have hmem : ∀ y ∈ (s.erase x).erase (g x hx), y ∈ s := fun y hy =>
            mem_of_mem_erase (mem_of_mem_erase hy)
          have g_inj : ∀ {x hx y hy}, g x hx = g y hy → x = y := fun x hx y hy h => by
            rw [← g_inv x hx, ← g_inv y hy] <;> simp [h]
          have ih' : (∏ y in erase (erase s x) (g x hx), f y) = (1 : β) :=
            ih ((s.erase x).erase (g x hx))
              ⟨subset.trans (erase_subset _ _) (erase_subset _ _), fun h =>
                not_mem_erase (g x hx) (s.erase x) (h (g_mem x hx))⟩
              (fun y hy => g y (hmem y hy)) (fun y hy => h y (hmem y hy))
              (fun y hy => g_ne y (hmem y hy))
              (fun y hy =>
                mem_erase.2
                  ⟨fun h : g y _ = g x hx => by simpa [g_inj h] using hy,
                    mem_erase.2
                      ⟨fun h : g y _ = x =>
                        by
                        have : y = g x hx := g_inv y (hmem y hy) ▸ by simp [h]
                        simpa [this] using hy, g_mem y (hmem y hy)⟩⟩)
              fun y hy => g_inv y (hmem y hy)
          if hx1 : f x = 1 then
            ih' ▸
              Eq.symm
                (prod_subset hmem fun y hy hy₁ =>
                  have : y = x ∨ y = g x hx := by simpa [hy, not_and_or, or_comm'] using hy₁
                  this.elim (fun hy => hy.symm ▸ hx1) fun hy =>
                    h x hx ▸ hy ▸ hx1.symm ▸ (one_mul _).symm)
          else by
            rw [← insert_erase hx, prod_insert (not_mem_erase _ _), ←
              insert_erase (mem_erase.2 ⟨g_ne x hx hx1, g_mem x hx⟩),
              prod_insert (not_mem_erase _ _), ih', mul_one, h x hx]
#align finset.prod_involution Finset.prod_involution
#align finset.sum_involution Finset.sum_involution

#print Finset.prod_comp /-
/-- The product of the composition of functions `f` and `g`, is the product over `b ∈ s.image g` of
`f b` to the power of the cardinality of the fibre of `b`. See also `finset.prod_image`. -/
@[to_additive
      "The sum of the composition of functions `f` and `g`, is the sum over `b ∈ s.image g`\nof `f b` times of the cardinality of the fibre of `b`. See also `finset.sum_image`."]
theorem prod_comp [DecidableEq γ] (f : γ → β) (g : α → γ) :
    (∏ a in s, f (g a)) = ∏ b in s.image g, f b ^ (s.filter fun a => g a = b).card :=
  calc
    (∏ a in s, f (g a)) =
        ∏ x in (s.image g).Sigma fun b : γ => s.filter fun a => g a = b, f (g x.2) :=
      prod_bij (fun a ha => ⟨g a, a⟩) (by simp <;> tauto) (fun _ _ => rfl) (by simp)
        (-- `(by finish)` closes this
        by
          rintro ⟨b_fst, b_snd⟩ H
          simp only [mem_image, exists_prop, mem_filter, mem_sigma] at H
          tauto)
    _ = ∏ b in s.image g, ∏ a in s.filter fun a => g a = b, f (g a) := prod_sigma _ _ _
    _ = ∏ b in s.image g, ∏ a in s.filter fun a => g a = b, f b :=
      prod_congr rfl fun b hb => prod_congr rfl (by simp (config := { contextual := true }))
    _ = ∏ b in s.image g, f b ^ (s.filter fun a => g a = b).card :=
      prod_congr rfl fun _ _ => prod_const _
    
#align finset.prod_comp Finset.prod_comp
#align finset.sum_comp Finset.sum_comp
-/

/- warning: finset.prod_piecewise -> Finset.prod_piecewise is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (t : Finset.{u2} α) (f : α -> β) (g : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => Finset.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) t f g (fun (j : α) => Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) j t) x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Inter.inter.{u2} (Finset.{u2} α) (Finset.hasInter.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.hasSdiff.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (fun (x : α) => g x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (t : Finset.{u2} α) (f : α -> β) (g : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => Finset.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) t f g (fun (j : α) => Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) j t) x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.instSDiffFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_piecewise Finset.prod_piecewiseₓ'. -/
@[to_additive]
theorem prod_piecewise [DecidableEq α] (s t : Finset α) (f g : α → β) :
    (∏ x in s, (t.piecewise f g) x) = (∏ x in s ∩ t, f x) * ∏ x in s \ t, g x := by
  rw [piecewise, prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter]
#align finset.prod_piecewise Finset.prod_piecewise
#align finset.sum_piecewise Finset.sum_piecewise

/- warning: finset.prod_inter_mul_prod_diff -> Finset.prod_inter_mul_prod_diff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (t : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Inter.inter.{u2} (Finset.{u2} α) (Finset.hasInter.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.hasSdiff.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (fun (x : α) => f x))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (t : Finset.{u2} α) (f : α -> β), Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.instSDiffFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (fun (x : α) => f x))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x))
Case conversion may be inaccurate. Consider using '#align finset.prod_inter_mul_prod_diff Finset.prod_inter_mul_prod_diffₓ'. -/
@[to_additive]
theorem prod_inter_mul_prod_diff [DecidableEq α] (s t : Finset α) (f : α → β) :
    ((∏ x in s ∩ t, f x) * ∏ x in s \ t, f x) = ∏ x in s, f x :=
  by
  convert (s.prod_piecewise t f f).symm
  simp [Finset.piecewise]
#align finset.prod_inter_mul_prod_diff Finset.prod_inter_mul_prod_diff
#align finset.sum_inter_add_sum_diff Finset.sum_inter_add_sum_diff

/- warning: finset.prod_eq_mul_prod_diff_singleton -> Finset.prod_eq_mul_prod_diff_singleton is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} {i : α}, (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) -> (forall (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f i) (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.hasSdiff.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.hasSingleton.{u2} α) i)) (fun (x : α) => f x))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} {i : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (forall (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f i) (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.instSDiffFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) i)) (fun (x : α) => f x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_mul_prod_diff_singleton Finset.prod_eq_mul_prod_diff_singletonₓ'. -/
@[to_additive]
theorem prod_eq_mul_prod_diff_singleton [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s)
    (f : α → β) : (∏ x in s, f x) = f i * ∏ x in s \ {i}, f x :=
  by
  convert (s.prod_inter_mul_prod_diff {i} f).symm
  simp [h]
#align finset.prod_eq_mul_prod_diff_singleton Finset.prod_eq_mul_prod_diff_singleton
#align finset.sum_eq_add_sum_diff_singleton Finset.sum_eq_add_sum_diff_singleton

/- warning: finset.prod_eq_prod_diff_singleton_mul -> Finset.prod_eq_prod_diff_singleton_mul is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} {i : α}, (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) -> (forall (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.hasSdiff.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.hasSingleton.{u2} α) i)) (fun (x : α) => f x)) (f i)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} {i : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (forall (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.instSDiffFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) i)) (fun (x : α) => f x)) (f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_prod_diff_singleton_mul Finset.prod_eq_prod_diff_singleton_mulₓ'. -/
@[to_additive]
theorem prod_eq_prod_diff_singleton_mul [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s)
    (f : α → β) : (∏ x in s, f x) = (∏ x in s \ {i}, f x) * f i := by
  rw [prod_eq_mul_prod_diff_singleton h, mul_comm]
#align finset.prod_eq_prod_diff_singleton_mul Finset.prod_eq_prod_diff_singleton_mul
#align finset.sum_eq_sum_diff_singleton_add Finset.sum_eq_sum_diff_singleton_add

/- warning: fintype.prod_eq_mul_prod_compl -> Fintype.prod_eq_mul_prod_compl is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : Fintype.{u2} α] (a : α) (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_3) (fun (i : α) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (Finset.prod.{u1, u2} β α _inst_1 (HasCompl.compl.{u2} (Finset.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} α) (Finset.booleanAlgebra.{u2} α _inst_3 (fun (a : α) (b : α) => _inst_2 a b))) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.hasSingleton.{u2} α) a)) (fun (i : α) => f i)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : Fintype.{u2} α] (a : α) (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_3) (fun (i : α) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (Finset.prod.{u1, u2} β α _inst_1 (HasCompl.compl.{u2} (Finset.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} α) (Finset.instBooleanAlgebraFinset.{u2} α _inst_3 (fun (a : α) (b : α) => _inst_2 a b))) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a)) (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align fintype.prod_eq_mul_prod_compl Fintype.prod_eq_mul_prod_complₓ'. -/
@[to_additive]
theorem Fintype.prod_eq_mul_prod_compl [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    (∏ i, f i) = f a * ∏ i in {a}ᶜ, f i :=
  prod_eq_mul_prod_diff_singleton (mem_univ a) f
#align fintype.prod_eq_mul_prod_compl Fintype.prod_eq_mul_prod_compl
#align fintype.sum_eq_add_sum_compl Fintype.sum_eq_add_sum_compl

/- warning: fintype.prod_eq_prod_compl_mul -> Fintype.prod_eq_prod_compl_mul is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : Fintype.{u2} α] (a : α) (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_3) (fun (i : α) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (HasCompl.compl.{u2} (Finset.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} α) (Finset.booleanAlgebra.{u2} α _inst_3 (fun (a : α) (b : α) => _inst_2 a b))) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.hasSingleton.{u2} α) a)) (fun (i : α) => f i)) (f a))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : Fintype.{u2} α] (a : α) (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_3) (fun (i : α) => f i)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (HasCompl.compl.{u2} (Finset.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} α) (Finset.instBooleanAlgebraFinset.{u2} α _inst_3 (fun (a : α) (b : α) => _inst_2 a b))) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a)) (fun (i : α) => f i)) (f a))
Case conversion may be inaccurate. Consider using '#align fintype.prod_eq_prod_compl_mul Fintype.prod_eq_prod_compl_mulₓ'. -/
@[to_additive]
theorem Fintype.prod_eq_prod_compl_mul [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    (∏ i, f i) = (∏ i in {a}ᶜ, f i) * f a :=
  prod_eq_prod_diff_singleton_mul (mem_univ a) f
#align fintype.prod_eq_prod_compl_mul Fintype.prod_eq_prod_compl_mul
#align fintype.sum_eq_sum_compl_add Fintype.sum_eq_sum_compl_add

#print Finset.dvd_prod_of_mem /-
theorem dvd_prod_of_mem (f : α → β) {a : α} {s : Finset α} (ha : a ∈ s) : f a ∣ ∏ i in s, f i := by
  classical
    rw [Finset.prod_eq_mul_prod_diff_singleton ha]
    exact dvd_mul_right _ _
#align finset.dvd_prod_of_mem Finset.dvd_prod_of_mem
-/

#print Finset.prod_partition /-
/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
@[to_additive "A sum can be partitioned into a sum of sums, each equivalent under a setoid."]
theorem prod_partition (R : Setoid α) [DecidableRel R.R] :
    (∏ x in s, f x) = ∏ xbar in s.image Quotient.mk', ∏ y in s.filter fun y => ⟦y⟧ = xbar, f y :=
  by
  refine' (Finset.prod_image' f fun x hx => _).symm
  rfl
#align finset.prod_partition Finset.prod_partition
#align finset.sum_partition Finset.sum_partition
-/

/- warning: finset.prod_cancels_of_partition_cancels -> Finset.prod_cancels_of_partition_cancels is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] (R : Setoid.{succ u2} α) [_inst_2 : DecidableRel.{succ u2} α (Setoid.r.{succ u2} α R)], (forall (x : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α (fun (y : α) => HasEquivₓ.Equiv.{succ u2} α (setoidHasEquiv.{succ u2} α R) y x) (fun (a : α) => _inst_2 a x) s) (fun (a : α) => f a)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoid.{u1} β] (R : Setoid.{succ u2} α) [_inst_2 : DecidableRel.{succ u2} α (Setoid.r.{succ u2} α R)], (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.filter.{u2} α (fun (y : α) => HasEquiv.Equiv.{succ u2, 0} α (instHasEquiv.{succ u2} α R) y x) (fun (a : α) => _inst_2 a x) s) (fun (a : α) => f a)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_cancels_of_partition_cancels Finset.prod_cancels_of_partition_cancelsₓ'. -/
/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[to_additive "If we can partition a sum into subsets that cancel out, then the whole sum cancels."]
theorem prod_cancels_of_partition_cancels (R : Setoid α) [DecidableRel R.R]
    (h : ∀ x ∈ s, (∏ a in s.filter fun y => y ≈ x, f a) = 1) : (∏ x in s, f x) = 1 :=
  by
  rw [prod_partition R, ← Finset.prod_eq_one]
  intro xbar xbar_in_s
  obtain ⟨x, x_in_s, xbar_eq_x⟩ := mem_image.mp xbar_in_s
  rw [← xbar_eq_x, filter_congr fun y _ => @Quotient.eq' _ R y x]
  apply h x x_in_s
#align finset.prod_cancels_of_partition_cancels Finset.prod_cancels_of_partition_cancels
#align finset.sum_cancels_of_partition_cancels Finset.sum_cancels_of_partition_cancels

#print Finset.prod_update_of_not_mem /-
@[to_additive]
theorem prod_update_of_not_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∉ s) (f : α → β)
    (b : β) : (∏ x in s, Function.update f i b x) = ∏ x in s, f x :=
  by
  apply prod_congr rfl fun j hj => _
  have : j ≠ i := by
    intro eq
    rw [Eq] at hj
    exact h hj
  simp [this]
#align finset.prod_update_of_not_mem Finset.prod_update_of_not_mem
#align finset.sum_update_of_not_mem Finset.sum_update_of_not_mem
-/

/- warning: finset.prod_update_of_mem -> Finset.prod_update_of_mem is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} {i : α}, (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) -> (forall (f : α -> β) (b : β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_2 a b) f i b x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) b (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.hasSdiff.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.hasSingleton.{u2} α) i)) (fun (x : α) => f x))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} {i : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (forall (f : α -> β) (b : β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => Function.update.{succ u2, succ u1} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_2 a b) f i b x)) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) b (Finset.prod.{u1, u2} β α _inst_1 (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.instSDiffFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) i)) (fun (x : α) => f x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_update_of_mem Finset.prod_update_of_memₓ'. -/
@[to_additive]
theorem prod_update_of_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) :
    (∏ x in s, Function.update f i b x) = b * ∏ x in s \ singleton i, f x :=
  by
  rw [update_eq_piecewise, prod_piecewise]
  simp [h]
#align finset.prod_update_of_mem Finset.prod_update_of_mem
#align finset.sum_update_of_mem Finset.sum_update_of_mem

#print Finset.eq_of_card_le_one_of_prod_eq /-
/-- If a product of a `finset` of size at most 1 has a given value, so
do the terms in that product. -/
@[to_additive eq_of_card_le_one_of_sum_eq
      "If a sum of a `finset` of size at most 1 has a given\nvalue, so do the terms in that sum."]
theorem eq_of_card_le_one_of_prod_eq {s : Finset α} (hc : s.card ≤ 1) {f : α → β} {b : β}
    (h : (∏ x in s, f x) = b) : ∀ x ∈ s, f x = b :=
  by
  intro x hx
  by_cases hc0 : s.card = 0
  · exact False.elim (card_ne_zero_of_mem hx hc0)
  · have h1 : s.card = 1 := le_antisymm hc (Nat.one_le_of_lt (Nat.pos_of_ne_zero hc0))
    rw [card_eq_one] at h1
    cases' h1 with x2 hx2
    rw [hx2, mem_singleton] at hx
    simp_rw [hx2] at h
    rw [hx]
    rw [prod_singleton] at h
    exact h
#align finset.eq_of_card_le_one_of_prod_eq Finset.eq_of_card_le_one_of_prod_eq
#align finset.eq_of_card_le_one_of_sum_eq Finset.eq_of_card_le_one_of_sum_eq
-/

/- warning: finset.mul_prod_erase -> Finset.mul_prod_erase is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β) {a : α}, (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (Finset.prod.{u1, u2} β α _inst_1 (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a) (fun (x : α) => f x))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β) {a : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (f a) (Finset.prod.{u1, u2} β α _inst_1 (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a) (fun (x : α) => f x))) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.mul_prod_erase Finset.mul_prod_eraseₓ'. -/
/-- Taking a product over `s : finset α` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`.

See `multiset.prod_map_erase` for the `multiset` version. -/
@[to_additive
      "Taking a sum over `s : finset α` is the same as adding the value on a single element\n`f a` to the sum over `s.erase a`.\n\nSee `multiset.sum_map_erase` for the `multiset` version."]
theorem mul_prod_erase [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x := by
  rw [← prod_insert (not_mem_erase a s), insert_erase h]
#align finset.mul_prod_erase Finset.mul_prod_erase
#align finset.add_sum_erase Finset.add_sum_erase

/- warning: finset.prod_erase_mul -> Finset.prod_erase_mul is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β) {a : α}, (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toHasMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a) (fun (x : α) => f x)) (f a)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β) {a : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α _inst_1 (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a) (fun (x : α) => f x)) (f a)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_erase_mul Finset.prod_erase_mulₓ'. -/
/-- A variant of `finset.mul_prod_erase` with the multiplication swapped. -/
@[to_additive "A variant of `finset.add_sum_erase` with the addition swapped."]
theorem prod_erase_mul [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    (∏ x in s.erase a, f x) * f a = ∏ x in s, f x := by rw [mul_comm, mul_prod_erase s f h]
#align finset.prod_erase_mul Finset.prod_erase_mul
#align finset.sum_erase_add Finset.sum_erase_add

/- warning: finset.prod_erase -> Finset.prod_erase is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) {f : α -> β} {a : α}, (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) {f : α -> β} {a : α}, (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_erase Finset.prod_eraseₓ'. -/
/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `finset`. -/
@[to_additive
      "If a function applied at a point is 0, a sum is unchanged by\nremoving that point, if present, from a `finset`."]
theorem prod_erase [DecidableEq α] (s : Finset α) {f : α → β} {a : α} (h : f a = 1) :
    (∏ x in s.erase a, f x) = ∏ x in s, f x :=
  by
  rw [← sdiff_singleton_eq_erase]
  refine' prod_subset (sdiff_subset _ _) fun x hx hnx => _
  rw [sdiff_singleton_eq_erase] at hnx
  rwa [eq_of_mem_of_not_mem_erase hx hnx]
#align finset.prod_erase Finset.prod_erase
#align finset.sum_erase Finset.sum_erase

/- warning: finset.prod_ite_one -> Finset.prod_ite_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} [_inst_1 : CommMonoid.{u1} β] {f : α -> Prop} [_inst_2 : DecidablePred.{succ u2} α f], (Set.PairwiseDisjoint.{0, u2} Prop α Prop.partialOrder (GeneralizedBooleanAlgebra.toOrderBot.{0} Prop (BooleanAlgebra.toGeneralizedBooleanAlgebra.{0} Prop Prop.booleanAlgebra)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} α) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (Finset.Set.hasCoeT.{u2} α))) s) f) -> (forall (a : β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => ite.{succ u1} β (f i) (_inst_2 i) a (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) (ite.{succ u1} β (Exists.{succ u2} α (fun (i : α) => Exists.{0} (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) (fun (H : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) => f i))) (Finset.decidableDexistsFinset.{u2} α s (fun (i : α) (H : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) => f i) (fun (a : α) (h : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) => _inst_2 a)) a (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} [_inst_1 : CommMonoid.{u1} β] {f : α -> Prop} [_inst_2 : DecidablePred.{succ u2} α f], (Set.PairwiseDisjoint.{0, u2} Prop α Prop.partialOrder (BoundedOrder.toOrderBot.{0} Prop (Preorder.toLE.{0} Prop (PartialOrder.toPreorder.{0} Prop Prop.partialOrder)) Prop.boundedOrder) (Finset.toSet.{u2} α s) f) -> (forall (a : β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (i : α) => ite.{succ u1} β (f i) (_inst_2 i) a (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) (ite.{succ u1} β (Exists.{succ u2} α (fun (i : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) (f i))) (Finset.decidableExistsAndFinset.{u2} α s (fun (i : α) => f i) (fun (a : α) => _inst_2 a)) a (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_ite_one Finset.prod_ite_oneₓ'. -/
/-- See also `finset.prod_boole`. -/
@[to_additive "See also `finset.sum_boole`."]
theorem prod_ite_one {f : α → Prop} [DecidablePred f] (hf : (s : Set α).PairwiseDisjoint f)
    (a : β) : (∏ i in s, ite (f i) a 1) = ite (∃ i ∈ s, f i) a 1 :=
  by
  split_ifs
  · obtain ⟨i, hi, hfi⟩ := h
    rw [prod_eq_single_of_mem _ hi, if_pos hfi]
    exact fun j hj h => if_neg fun hfj => (hf hj hi h).le_bot ⟨hfj, hfi⟩
  · push_neg  at h
    rw [prod_eq_one]
    exact fun i hi => if_neg (h i hi)
#align finset.prod_ite_one Finset.prod_ite_one
#align finset.sum_ite_zero Finset.sum_ite_zero

/- warning: finset.sum_erase_lt_of_pos -> Finset.sum_erase_lt_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : OrderedAddCommMonoid.{u2} γ] [_inst_4 : CovariantClass.{u2, u2} γ γ (HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ _inst_3)))))) (LT.lt.{u2} γ (Preorder.toLT.{u2} γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ _inst_3))))] {s : Finset.{u1} α} {d : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) d s) -> (forall {f : α -> γ}, (LT.lt.{u2} γ (Preorder.toLT.{u2} γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ _inst_3))) (OfNat.ofNat.{u2} γ 0 (OfNat.mk.{u2} γ 0 (Zero.zero.{u2} γ (AddZeroClass.toHasZero.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ _inst_3))))))) (f d)) -> (LT.lt.{u2} γ (Preorder.toLT.{u2} γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ _inst_3))) (Finset.sum.{u2, u1} γ α (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ _inst_3) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s d) (fun (m : α) => f m)) (Finset.sum.{u2, u1} γ α (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ _inst_3) s (fun (m : α) => f m))))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : OrderedAddCommMonoid.{u1} γ] [_inst_4 : CovariantClass.{u1, u1} γ γ (fun (x._@.Mathlib.Algebra.BigOperators.Basic._hyg.22608 : γ) (x._@.Mathlib.Algebra.BigOperators.Basic._hyg.22610 : γ) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (OrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) x._@.Mathlib.Algebra.BigOperators.Basic._hyg.22608 x._@.Mathlib.Algebra.BigOperators.Basic._hyg.22610) (fun (x._@.Mathlib.Algebra.BigOperators.Basic._hyg.22623 : γ) (x._@.Mathlib.Algebra.BigOperators.Basic._hyg.22625 : γ) => LT.lt.{u1} γ (Preorder.toLT.{u1} γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ _inst_3))) x._@.Mathlib.Algebra.BigOperators.Basic._hyg.22623 x._@.Mathlib.Algebra.BigOperators.Basic._hyg.22625)] {s : Finset.{u2} α} {d : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) d s) -> (forall {f : α -> γ}, (LT.lt.{u1} γ (Preorder.toLT.{u1} γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ _inst_3))) (OfNat.ofNat.{u1} γ 0 (Zero.toOfNat0.{u1} γ (AddMonoid.toZero.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (OrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f d)) -> (LT.lt.{u1} γ (Preorder.toLT.{u1} γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ _inst_3))) (Finset.sum.{u1, u2} γ α (OrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3) (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s d) (fun (m : α) => f m)) (Finset.sum.{u1, u2} γ α (OrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3) s (fun (m : α) => f m))))
Case conversion may be inaccurate. Consider using '#align finset.sum_erase_lt_of_pos Finset.sum_erase_lt_of_posₓ'. -/
theorem sum_erase_lt_of_pos {γ : Type _} [DecidableEq α] [OrderedAddCommMonoid γ]
    [CovariantClass γ γ (· + ·) (· < ·)] {s : Finset α} {d : α} (hd : d ∈ s) {f : α → γ}
    (hdf : 0 < f d) : (∑ m : α in s.erase d, f m) < ∑ m : α in s, f m :=
  by
  nth_rw_rhs 1 [← Finset.insert_erase hd]
  rw [Finset.sum_insert (Finset.not_mem_erase d s)]
  exact lt_add_of_pos_left _ hdf
#align finset.sum_erase_lt_of_pos Finset.sum_erase_lt_of_pos

/- warning: finset.eq_one_of_prod_eq_one -> Finset.eq_one_of_prod_eq_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} {a : α}, (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))) -> (forall (x : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s) -> (Ne.{succ u2} α x a) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))) -> (forall (x : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] {s : Finset.{u2} α} {f : α -> β} {a : α}, (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))) -> (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Ne.{succ u2} α x a) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))) -> (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))
Case conversion may be inaccurate. Consider using '#align finset.eq_one_of_prod_eq_one Finset.eq_one_of_prod_eq_oneₓ'. -/
/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `finset`. -/
@[to_additive
      "If a sum is 0 and the function is 0 except possibly at one\npoint, it is 0 everywhere on the `finset`."]
theorem eq_one_of_prod_eq_one {s : Finset α} {f : α → β} {a : α} (hp : (∏ x in s, f x) = 1)
    (h1 : ∀ x ∈ s, x ≠ a → f x = 1) : ∀ x ∈ s, f x = 1 :=
  by
  intro x hx
  classical
    by_cases h : x = a
    · rw [h]
      rw [h] at hx
      rw [← prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (not_mem_singleton.1 ha),
        prod_singleton] at hp
      exact hp
    · exact h1 x hx h
#align finset.eq_one_of_prod_eq_one Finset.eq_one_of_prod_eq_one
#align finset.eq_zero_of_sum_eq_zero Finset.eq_zero_of_sum_eq_zero

/- warning: finset.prod_pow_boole -> Finset.prod_pow_boole is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β) (a : α), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => HPow.hPow.{u1, 0, u1} β Nat β (instHPow.{u1, 0} β Nat (Monoid.Pow.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (f x) (ite.{1} Nat (Eq.{succ u2} α a x) (_inst_2 a x) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))) (ite.{succ u1} β (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a s) (f a) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u2} α) (f : α -> β) (a : α), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => HPow.hPow.{u1, 0, u1} β Nat β (instHPow.{u1, 0} β Nat (Monoid.Pow.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))) (f x) (ite.{1} Nat (Eq.{succ u2} α a x) (_inst_2 a x) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (ite.{succ u1} β (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) a s) (f a) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_pow_boole Finset.prod_pow_booleₓ'. -/
theorem prod_pow_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∏ x in s, f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1 := by simp
#align finset.prod_pow_boole Finset.prod_pow_boole

#print Finset.prod_dvd_prod_of_dvd /-
theorem prod_dvd_prod_of_dvd {S : Finset α} (g1 g2 : α → β) (h : ∀ a ∈ S, g1 a ∣ g2 a) :
    S.Prod g1 ∣ S.Prod g2 := by
  classical
    apply Finset.induction_on' S
    · simp
    intro a T haS _ haT IH
    repeat' rw [Finset.prod_insert haT]
    exact mul_dvd_mul (h a haS) IH
#align finset.prod_dvd_prod_of_dvd Finset.prod_dvd_prod_of_dvd
-/

/- warning: finset.prod_dvd_prod_of_subset -> Finset.prod_dvd_prod_of_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_2 : CommMonoid.{u2} M] (s : Finset.{u1} ι) (t : Finset.{u1} ι) (f : ι -> M), (HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.hasSubset.{u1} ι) s t) -> (Dvd.Dvd.{u2} M (semigroupDvd.{u2} M (Monoid.toSemigroup.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) (Finset.prod.{u2, u1} M ι _inst_2 s (fun (i : ι) => f i)) (Finset.prod.{u2, u1} M ι _inst_2 t (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] (s : Finset.{u2} ι) (t : Finset.{u2} ι) (f : ι -> M), (HasSubset.Subset.{u2} (Finset.{u2} ι) (Finset.instHasSubsetFinset.{u2} ι) s t) -> (Dvd.dvd.{u1} M (semigroupDvd.{u1} M (Monoid.toSemigroup.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (Finset.prod.{u1, u2} M ι _inst_2 s (fun (i : ι) => f i)) (Finset.prod.{u1, u2} M ι _inst_2 t (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_dvd_prod_of_subset Finset.prod_dvd_prod_of_subsetₓ'. -/
theorem prod_dvd_prod_of_subset {ι M : Type _} [CommMonoid M] (s t : Finset ι) (f : ι → M)
    (h : s ⊆ t) : (∏ i in s, f i) ∣ ∏ i in t, f i :=
  Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| by simpa
#align finset.prod_dvd_prod_of_subset Finset.prod_dvd_prod_of_subset

end CommMonoid

/- warning: finset.prod_add_prod_eq -> Finset.prod_add_prod_eq is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommSemiring.{u1} β] {s : Finset.{u2} α} {i : α} {f : α -> β} {g : α -> β} {h : α -> β}, (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) -> (Eq.{succ u1} β (HAdd.hAdd.{u1, u1, u1} β β β (instHAdd.{u1} β (Distrib.toHasAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)))))) (g i) (h i)) (f i)) -> (forall (j : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) j s) -> (Ne.{succ u2} α j i) -> (Eq.{succ u1} β (g j) (f j))) -> (forall (j : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) j s) -> (Ne.{succ u2} α j i) -> (Eq.{succ u1} β (h j) (f j))) -> (Eq.{succ u1} β (HAdd.hAdd.{u1, u1, u1} β β β (instHAdd.{u1} β (Distrib.toHasAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)))))) (Finset.prod.{u1, u2} β α (CommSemiring.toCommMonoid.{u1} β _inst_1) s (fun (i : α) => g i)) (Finset.prod.{u1, u2} β α (CommSemiring.toCommMonoid.{u1} β _inst_1) s (fun (i : α) => h i))) (Finset.prod.{u1, u2} β α (CommSemiring.toCommMonoid.{u1} β _inst_1) s (fun (i : α) => f i)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommSemiring.{u1} β] {s : Finset.{u2} α} {i : α} {f : α -> β} {g : α -> β} {h : α -> β}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (Eq.{succ u1} β (HAdd.hAdd.{u1, u1, u1} β β β (instHAdd.{u1} β (Distrib.toAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)))))) (g i) (h i)) (f i)) -> (forall (j : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s) -> (Ne.{succ u2} α j i) -> (Eq.{succ u1} β (g j) (f j))) -> (forall (j : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s) -> (Ne.{succ u2} α j i) -> (Eq.{succ u1} β (h j) (f j))) -> (Eq.{succ u1} β (HAdd.hAdd.{u1, u1, u1} β β β (instHAdd.{u1} β (Distrib.toAdd.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β (CommSemiring.toSemiring.{u1} β _inst_1)))))) (Finset.prod.{u1, u2} β α (CommSemiring.toCommMonoid.{u1} β _inst_1) s (fun (i : α) => g i)) (Finset.prod.{u1, u2} β α (CommSemiring.toCommMonoid.{u1} β _inst_1) s (fun (i : α) => h i))) (Finset.prod.{u1, u2} β α (CommSemiring.toCommMonoid.{u1} β _inst_1) s (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.prod_add_prod_eq Finset.prod_add_prod_eqₓ'. -/
/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
theorem prod_add_prod_eq [CommSemiring β] {s : Finset α} {i : α} {f g h : α → β} (hi : i ∈ s)
    (h1 : g i + h i = f i) (h2 : ∀ j ∈ s, j ≠ i → g j = f j) (h3 : ∀ j ∈ s, j ≠ i → h j = f j) :
    ((∏ i in s, g i) + ∏ i in s, h i) = ∏ i in s, f i := by
  classical
    simp_rw [prod_eq_mul_prod_diff_singleton hi, ← h1, right_distrib]
    congr 2 <;> apply prod_congr rfl <;> simpa
#align finset.prod_add_prod_eq Finset.prod_add_prod_eq

#print Finset.card_eq_sum_ones /-
theorem card_eq_sum_ones (s : Finset α) : s.card = ∑ _ in s, 1 := by simp
#align finset.card_eq_sum_ones Finset.card_eq_sum_ones
-/

#print Finset.sum_const_nat /-
theorem sum_const_nat {m : ℕ} {f : α → ℕ} (h₁ : ∀ x ∈ s, f x = m) : (∑ x in s, f x) = card s * m :=
  by
  rw [← Nat.nsmul_eq_mul, ← sum_const]
  apply sum_congr rfl h₁
#align finset.sum_const_nat Finset.sum_const_nat
-/

/- warning: finset.sum_boole -> Finset.sum_boole is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {p : α -> Prop} [_inst_1 : NonAssocSemiring.{u1} β] {hp : DecidablePred.{succ u2} α p}, Eq.{succ u1} β (Finset.sum.{u1, u2} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) s (fun (x : α) => ite.{succ u1} β (p x) (hp x) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (AddMonoidWithOne.toOne.{u1} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} β (NonAssocSemiring.toAddCommMonoidWithOne.{u1} β _inst_1)))))) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat β (HasLiftT.mk.{1, succ u1} Nat β (CoeTCₓ.coe.{1, succ u1} Nat β (Nat.castCoe.{u1} β (AddMonoidWithOne.toNatCast.{u1} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} β (NonAssocSemiring.toAddCommMonoidWithOne.{u1} β _inst_1)))))) (Finset.card.{u2} α (Finset.filter.{u2} α p (fun (a : α) => hp a) s)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {p : α -> Prop} [_inst_1 : NonAssocSemiring.{u1} β] {hp : DecidablePred.{succ u2} α p}, Eq.{succ u1} β (Finset.sum.{u1, u2} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β _inst_1)) s (fun (x : α) => ite.{succ u1} β (p x) (hp x) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (NonAssocSemiring.toOne.{u1} β _inst_1))) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (MulZeroOneClass.toZero.{u1} β (NonAssocSemiring.toMulZeroOneClass.{u1} β _inst_1)))))) (Nat.cast.{u1} β (NonAssocSemiring.toNatCast.{u1} β _inst_1) (Finset.card.{u2} α (Finset.filter.{u2} α p (fun (a : α) => hp a) s)))
Case conversion may be inaccurate. Consider using '#align finset.sum_boole Finset.sum_booleₓ'. -/
@[simp]
theorem sum_boole {s : Finset α} {p : α → Prop} [NonAssocSemiring β] {hp : DecidablePred p} :
    (∑ x in s, if p x then (1 : β) else (0 : β)) = (s.filter p).card := by
  simp only [add_zero, mul_one, Finset.sum_const, nsmul_eq_mul, eq_self_iff_true,
    Finset.sum_const_zero, Finset.sum_ite]
#align finset.sum_boole Finset.sum_boole

/- warning: commute.sum_right -> Commute.sum_right is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} β] (s : Finset.{u2} α) (f : α -> β) (b : β), (forall (i : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) -> (Commute.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1)) b (f i))) -> (Commute.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1)) b (Finset.sum.{u1, u2} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) s (fun (i : α) => f i)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} β] (s : Finset.{u2} α) (f : α -> β) (b : β), (forall (i : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (Commute.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β _inst_1) b (f i))) -> (Commute.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β _inst_1) b (Finset.sum.{u1, u2} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) s (fun (i : α) => f i)))
Case conversion may be inaccurate. Consider using '#align commute.sum_right Commute.sum_rightₓ'. -/
theorem Commute.sum_right [NonUnitalNonAssocSemiring β] (s : Finset α) (f : α → β) (b : β)
    (h : ∀ i ∈ s, Commute b (f i)) : Commute b (∑ i in s, f i) :=
  Commute.multiset_sum_right _ _ fun b hb =>
    by
    obtain ⟨i, hi, rfl⟩ := multiset.mem_map.mp hb
    exact h _ hi
#align commute.sum_right Commute.sum_right

/- warning: commute.sum_left -> Commute.sum_left is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} β] (s : Finset.{u2} α) (f : α -> β) (b : β), (forall (i : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) -> (Commute.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1)) (f i) b)) -> (Commute.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β _inst_1)) (Finset.sum.{u1, u2} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) s (fun (i : α) => f i)) b)
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} β] (s : Finset.{u2} α) (f : α -> β) (b : β), (forall (i : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (Commute.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β _inst_1) (f i) b)) -> (Commute.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β _inst_1) (Finset.sum.{u1, u2} β α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} β _inst_1) s (fun (i : α) => f i)) b)
Case conversion may be inaccurate. Consider using '#align commute.sum_left Commute.sum_leftₓ'. -/
theorem Commute.sum_left [NonUnitalNonAssocSemiring β] (s : Finset α) (f : α → β) (b : β)
    (h : ∀ i ∈ s, Commute (f i) b) : Commute (∑ i in s, f i) b :=
  (Commute.sum_right _ _ _ fun i hi => (h _ hi).symm).symm
#align commute.sum_left Commute.sum_left

section Opposite

open MulOpposite

/- warning: finset.op_sum -> Finset.op_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} β] {s : Finset.{u2} α} (f : α -> β), Eq.{succ u1} (MulOpposite.{u1} β) (MulOpposite.op.{u1} β (Finset.sum.{u1, u2} β α _inst_1 s (fun (x : α) => f x))) (Finset.sum.{u1, u2} (MulOpposite.{u1} β) α (MulOpposite.addCommMonoid.{u1} β _inst_1) s (fun (x : α) => MulOpposite.op.{u1} β (f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} β] {s : Finset.{u2} α} (f : α -> β), Eq.{succ u1} (MulOpposite.{u1} β) (MulOpposite.op.{u1} β (Finset.sum.{u1, u2} β α _inst_1 s (fun (x : α) => f x))) (Finset.sum.{u1, u2} (MulOpposite.{u1} β) α (MulOpposite.instAddCommMonoidMulOpposite.{u1} β _inst_1) s (fun (x : α) => MulOpposite.op.{u1} β (f x)))
Case conversion may be inaccurate. Consider using '#align finset.op_sum Finset.op_sumₓ'. -/
/-- Moving to the opposite additive commutative monoid commutes with summing. -/
@[simp]
theorem op_sum [AddCommMonoid β] {s : Finset α} (f : α → β) :
    op (∑ x in s, f x) = ∑ x in s, op (f x) :=
  (opAddEquiv : β ≃+ βᵐᵒᵖ).map_sum _ _
#align finset.op_sum Finset.op_sum

/- warning: finset.unop_sum -> Finset.unop_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} β] {s : Finset.{u2} α} (f : α -> (MulOpposite.{u1} β)), Eq.{succ u1} β (MulOpposite.unop.{u1} β (Finset.sum.{u1, u2} (MulOpposite.{u1} β) α (MulOpposite.addCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x))) (Finset.sum.{u1, u2} β α _inst_1 s (fun (x : α) => MulOpposite.unop.{u1} β (f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} β] {s : Finset.{u2} α} (f : α -> (MulOpposite.{u1} β)), Eq.{succ u1} β (MulOpposite.unop.{u1} β (Finset.sum.{u1, u2} (MulOpposite.{u1} β) α (MulOpposite.instAddCommMonoidMulOpposite.{u1} β _inst_1) s (fun (x : α) => f x))) (Finset.sum.{u1, u2} β α _inst_1 s (fun (x : α) => MulOpposite.unop.{u1} β (f x)))
Case conversion may be inaccurate. Consider using '#align finset.unop_sum Finset.unop_sumₓ'. -/
@[simp]
theorem unop_sum [AddCommMonoid β] {s : Finset α} (f : α → βᵐᵒᵖ) :
    unop (∑ x in s, f x) = ∑ x in s, unop (f x) :=
  (opAddEquiv : β ≃+ βᵐᵒᵖ).symm.map_sum _ _
#align finset.unop_sum Finset.unop_sum

end Opposite

section DivisionCommMonoid

variable [DivisionCommMonoid β]

/- warning: finset.prod_inv_distrib -> Finset.prod_inv_distrib is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : DivisionCommMonoid.{u1} β], Eq.{succ u1} β (Finset.prod.{u1, u2} β α (DivisionCommMonoid.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => Inv.inv.{u1} β (DivInvMonoid.toHasInv.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β _inst_1))) (f x))) (Inv.inv.{u1} β (DivInvMonoid.toHasInv.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β _inst_1))) (Finset.prod.{u1, u2} β α (DivisionCommMonoid.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : DivisionCommMonoid.{u1} β], Eq.{succ u1} β (Finset.prod.{u1, u2} β α (DivisionCommMonoid.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => Inv.inv.{u1} β (InvOneClass.toInv.{u1} β (DivInvOneMonoid.toInvOneClass.{u1} β (DivisionMonoid.toDivInvOneMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β _inst_1)))) (f x))) (Inv.inv.{u1} β (InvOneClass.toInv.{u1} β (DivInvOneMonoid.toInvOneClass.{u1} β (DivisionMonoid.toDivInvOneMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (DivisionCommMonoid.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_inv_distrib Finset.prod_inv_distribₓ'. -/
@[simp, to_additive]
theorem prod_inv_distrib : (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹ :=
  Multiset.prod_map_inv
#align finset.prod_inv_distrib Finset.prod_inv_distrib
#align finset.sum_neg_distrib Finset.sum_neg_distrib

/- warning: finset.prod_div_distrib -> Finset.prod_div_distrib is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} {g : α -> β} [_inst_1 : DivisionCommMonoid.{u1} β], Eq.{succ u1} β (Finset.prod.{u1, u2} β α (DivisionCommMonoid.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toHasDiv.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β _inst_1)))) (f x) (g x))) (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toHasDiv.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (DivisionCommMonoid.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α (DivisionCommMonoid.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => g x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} {g : α -> β} [_inst_1 : DivisionCommMonoid.{u1} β], Eq.{succ u1} β (Finset.prod.{u1, u2} β α (DivisionCommMonoid.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toDiv.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β _inst_1)))) (f x) (g x))) (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toDiv.{u1} β (DivisionMonoid.toDivInvMonoid.{u1} β (DivisionCommMonoid.toDivisionMonoid.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (DivisionCommMonoid.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α (DivisionCommMonoid.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => g x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_div_distrib Finset.prod_div_distribₓ'. -/
@[simp, to_additive]
theorem prod_div_distrib : (∏ x in s, f x / g x) = (∏ x in s, f x) / ∏ x in s, g x :=
  Multiset.prod_map_div
#align finset.prod_div_distrib Finset.prod_div_distrib
#align finset.sum_sub_distrib Finset.sum_sub_distrib

#print Finset.prod_zpow /-
@[to_additive]
theorem prod_zpow (f : α → β) (s : Finset α) (n : ℤ) : (∏ a in s, f a ^ n) = (∏ a in s, f a) ^ n :=
  Multiset.prod_map_zpow
#align finset.prod_zpow Finset.prod_zpow
#align finset.sum_zsmul Finset.sum_zsmul
-/

end DivisionCommMonoid

section CommGroup

variable [CommGroup β] [DecidableEq α]

/- warning: finset.prod_sdiff_eq_div -> Finset.prod_sdiff_eq_div is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommGroup.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.hasSubset.{u2} α) s₁ s₂) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.hasSdiff.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₂ s₁) (fun (x : α) => f x)) (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toHasDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) s₂ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) s₁ (fun (x : α) => f x))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommGroup.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₁ s₂) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.instSDiffFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₂ s₁) (fun (x : α) => f x)) (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) s₂ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) s₁ (fun (x : α) => f x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_sdiff_eq_div Finset.prod_sdiff_eq_divₓ'. -/
@[simp, to_additive]
theorem prod_sdiff_eq_div (h : s₁ ⊆ s₂) :
    (∏ x in s₂ \ s₁, f x) = (∏ x in s₂, f x) / ∏ x in s₁, f x := by
  rw [eq_div_iff_mul_eq', prod_sdiff h]
#align finset.prod_sdiff_eq_div Finset.prod_sdiff_eq_div
#align finset.sum_sdiff_eq_sub Finset.sum_sdiff_eq_sub

/- warning: finset.prod_sdiff_div_prod_sdiff -> Finset.prod_sdiff_div_prod_sdiff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommGroup.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], Eq.{succ u1} β (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toHasDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.hasSdiff.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₂ s₁) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.hasSdiff.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂) (fun (x : α) => f x))) (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toHasDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) s₂ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) s₁ (fun (x : α) => f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {f : α -> β} [_inst_1 : CommGroup.{u1} β] [_inst_2 : DecidableEq.{succ u2} α], Eq.{succ u1} β (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.instSDiffFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₂ s₁) (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) (SDiff.sdiff.{u2} (Finset.{u2} α) (Finset.instSDiffFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂) (fun (x : α) => f x))) (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) s₂ (fun (x : α) => f x)) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) s₁ (fun (x : α) => f x)))
Case conversion may be inaccurate. Consider using '#align finset.prod_sdiff_div_prod_sdiff Finset.prod_sdiff_div_prod_sdiffₓ'. -/
@[to_additive]
theorem prod_sdiff_div_prod_sdiff :
    ((∏ x in s₂ \ s₁, f x) / ∏ x in s₁ \ s₂, f x) = (∏ x in s₂, f x) / ∏ x in s₁, f x := by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]
#align finset.prod_sdiff_div_prod_sdiff Finset.prod_sdiff_div_prod_sdiff
#align finset.sum_sdiff_sub_sum_sdiff Finset.sum_sdiff_sub_sum_sdiff

/- warning: finset.prod_erase_eq_div -> Finset.prod_erase_eq_div is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommGroup.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {a : α}, (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a) (fun (x : α) => f x)) (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toHasDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)) (f a)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommGroup.{u1} β] [_inst_2 : DecidableEq.{succ u2} α] {a : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a) (fun (x : α) => f x)) (HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (DivInvMonoid.toDiv.{u1} β (Group.toDivInvMonoid.{u1} β (CommGroup.toGroup.{u1} β _inst_1)))) (Finset.prod.{u1, u2} β α (CommGroup.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)) (f a)))
Case conversion may be inaccurate. Consider using '#align finset.prod_erase_eq_div Finset.prod_erase_eq_divₓ'. -/
@[simp, to_additive]
theorem prod_erase_eq_div {a : α} (h : a ∈ s) : (∏ x in s.erase a, f x) = (∏ x in s, f x) / f a :=
  by rw [eq_div_iff_mul_eq', prod_erase_mul _ _ h]
#align finset.prod_erase_eq_div Finset.prod_erase_eq_div
#align finset.sum_erase_eq_sub Finset.sum_erase_eq_sub

end CommGroup

/- warning: finset.card_sigma -> Finset.card_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {σ : α -> Type.{u2}} (s : Finset.{u1} α) (t : forall (a : α), Finset.{u2} (σ a)), Eq.{1} Nat (Finset.card.{max u1 u2} (Sigma.{u1, u2} α (fun (i : α) => σ i)) (Finset.sigma.{u1, u2} α (fun (a : α) => σ a) s t)) (Finset.sum.{0, u1} Nat α Nat.addCommMonoid s (fun (a : α) => Finset.card.{u2} (σ a) (t a)))
but is expected to have type
  forall {α : Type.{u2}} {σ : α -> Type.{u1}} (s : Finset.{u2} α) (t : forall (a : α), Finset.{u1} (σ a)), Eq.{1} Nat (Finset.card.{max u2 u1} (Sigma.{u2, u1} α (fun (i : α) => σ i)) (Finset.sigma.{u2, u1} α (fun (a : α) => σ a) s t)) (Finset.sum.{0, u2} Nat α Nat.addCommMonoid s (fun (a : α) => Finset.card.{u1} (σ a) (t a)))
Case conversion may be inaccurate. Consider using '#align finset.card_sigma Finset.card_sigmaₓ'. -/
@[simp]
theorem card_sigma {σ : α → Type _} (s : Finset α) (t : ∀ a, Finset (σ a)) :
    card (s.Sigma t) = ∑ a in s, card (t a) :=
  Multiset.card_sigma _ _
#align finset.card_sigma Finset.card_sigma

/- warning: finset.card_disj_Union -> Finset.card_disjUnionᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} (s : Finset.{u2} α) (t : α -> (Finset.{u1} β)) (h : Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} β) α (Finset.partialOrder.{u1} β) (Finset.orderBot.{u1} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} α) (Set.{u2} α) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} α) (Set.{u2} α) (Finset.Set.hasCoeT.{u2} α))) s) t), Eq.{1} Nat (Finset.card.{u1} β (Finset.disjUnionₓ.{u2, u1} α β s t h)) (Finset.sum.{0, u2} Nat α Nat.addCommMonoid s (fun (i : α) => Finset.card.{u1} β (t i)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} (s : Finset.{u2} α) (t : α -> (Finset.{u1} β)) (h : Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} β) α (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.toSet.{u2} α s) t), Eq.{1} Nat (Finset.card.{u1} β (Finset.disjUnionᵢ.{u2, u1} α β s t h)) (Finset.sum.{0, u2} Nat α Nat.addCommMonoid s (fun (i : α) => Finset.card.{u1} β (t i)))
Case conversion may be inaccurate. Consider using '#align finset.card_disj_Union Finset.card_disjUnionᵢₓ'. -/
@[simp]
theorem card_disjUnionᵢ (s : Finset α) (t : α → Finset β) (h) :
    (s.disjUnion t h).card = s.Sum fun i => (t i).card :=
  Multiset.card_bind _ _
#align finset.card_disj_Union Finset.card_disjUnionᵢ

/- warning: finset.card_bUnion -> Finset.card_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {t : α -> (Finset.{u1} β)}, (forall (x : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s) -> (forall (y : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) y s) -> (Ne.{succ u2} α x y) -> (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.orderBot.{u1} β) (t x) (t y)))) -> (Eq.{1} Nat (Finset.card.{u1} β (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s t)) (Finset.sum.{0, u2} Nat α Nat.addCommMonoid s (fun (u : α) => Finset.card.{u1} β (t u))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {t : α -> (Finset.{u1} β)}, (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (forall (y : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) y s) -> (Ne.{succ u2} α x y) -> (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (t x) (t y)))) -> (Eq.{1} Nat (Finset.card.{u1} β (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s t)) (Finset.sum.{0, u2} Nat α Nat.addCommMonoid s (fun (u : α) => Finset.card.{u1} β (t u))))
Case conversion may be inaccurate. Consider using '#align finset.card_bUnion Finset.card_bunionᵢₓ'. -/
theorem card_bunionᵢ [DecidableEq β] {s : Finset α} {t : α → Finset β}
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (t x) (t y)) :
    (s.bUnion t).card = ∑ u in s, card (t u) :=
  calc
    (s.bUnion t).card = ∑ i in s.bUnion t, 1 := by simp
    _ = ∑ a in s, ∑ i in t a, 1 := Finset.sum_bunionᵢ h
    _ = ∑ u in s, card (t u) := by simp
    
#align finset.card_bUnion Finset.card_bunionᵢ

#print Finset.card_bunionᵢ_le /-
theorem card_bunionᵢ_le [DecidableEq β] {s : Finset α} {t : α → Finset β} :
    (s.bUnion t).card ≤ ∑ a in s, (t a).card :=
  haveI := Classical.decEq α
  Finset.induction_on s (by simp) fun a s has ih =>
    calc
      ((insert a s).bUnion t).card ≤ (t a).card + (s.bUnion t).card := by
        rw [bUnion_insert] <;> exact Finset.card_union_le _ _
      _ ≤ ∑ a in insert a s, card (t a) := by rw [sum_insert has] <;> exact add_le_add_left ih _
      
#align finset.card_bUnion_le Finset.card_bunionᵢ_le
-/

#print Finset.card_eq_sum_card_fiberwise /-
theorem card_eq_sum_card_fiberwise [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
    (H : ∀ x ∈ s, f x ∈ t) : s.card = ∑ a in t, (s.filter fun x => f x = a).card := by
  simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]
#align finset.card_eq_sum_card_fiberwise Finset.card_eq_sum_card_fiberwise
-/

#print Finset.card_eq_sum_card_image /-
theorem card_eq_sum_card_image [DecidableEq β] (f : α → β) (s : Finset α) :
    s.card = ∑ a in s.image f, (s.filter fun x => f x = a).card :=
  card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _
#align finset.card_eq_sum_card_image Finset.card_eq_sum_card_image
-/

/- warning: finset.mem_sum -> Finset.mem_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {f : α -> (Multiset.{u1} β)} (s : Finset.{u2} α) (b : β), Iff (Membership.Mem.{u1, u1} β (Multiset.{u1} β) (Multiset.hasMem.{u1} β) b (Finset.sum.{u1, u2} (Multiset.{u1} β) α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.orderedCancelAddCommMonoid.{u1} β)) s (fun (x : α) => f x))) (Exists.{succ u2} α (fun (a : α) => Exists.{0} (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (fun (H : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) => Membership.Mem.{u1, u1} β (Multiset.{u1} β) (Multiset.hasMem.{u1} β) b (f a))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {f : α -> (Multiset.{u1} β)} (s : Finset.{u2} α) (b : β), Iff (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b (Finset.sum.{u1, u2} (Multiset.{u1} β) α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} β) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} β)) s (fun (x : α) => f x))) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Membership.mem.{u1, u1} β (Multiset.{u1} β) (Multiset.instMembershipMultiset.{u1} β) b (f a))))
Case conversion may be inaccurate. Consider using '#align finset.mem_sum Finset.mem_sumₓ'. -/
theorem mem_sum {f : α → Multiset β} (s : Finset α) (b : β) :
    (b ∈ ∑ x in s, f x) ↔ ∃ a ∈ s, b ∈ f a := by
  classical
    refine' s.induction_on (by simp) _
    · intro a t hi ih
      simp [sum_insert hi, ih, or_and_right, exists_or]
#align finset.mem_sum Finset.mem_sum

section ProdEqZero

variable [CommMonoidWithZero β]

/- warning: finset.prod_eq_zero -> Finset.prod_eq_zero is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {a : α} {f : α -> β} [_inst_1 : CommMonoidWithZero.{u1} β], (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) -> (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1)))))))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1))))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {a : α} {f : α -> β} [_inst_1 : CommMonoidWithZero.{u1} β], (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β _inst_1)))) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β _inst_1))))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_zero Finset.prod_eq_zeroₓ'. -/
theorem prod_eq_zero (ha : a ∈ s) (h : f a = 0) : (∏ x in s, f x) = 0 :=
  by
  haveI := Classical.decEq α
  rw [← prod_erase_mul _ _ ha, h, mul_zero]
#align finset.prod_eq_zero Finset.prod_eq_zero

/- warning: finset.prod_boole -> Finset.prod_boole is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u1} β] {s : Finset.{u2} α} {p : α -> Prop} [_inst_2 : DecidablePred.{succ u2} α p], Eq.{succ u1} β (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β _inst_1) s (fun (i : α) => ite.{succ u1} β (p i) (_inst_2 i) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (MulZeroOneClass.toMulOneClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1))))))) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1))))))))) (ite.{succ u1} β (forall (i : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) -> (p i)) (Finset.decidableDforallFinset.{u2} α s (fun (i : α) (H : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) i s) => p i) (fun (a : α) (h : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) => _inst_2 a)) (OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (MulZeroOneClass.toMulOneClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1))))))) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1))))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u1} β] {s : Finset.{u2} α} {p : α -> Prop} [_inst_2 : DecidablePred.{succ u2} α p], Eq.{succ u1} β (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β _inst_1) s (fun (i : α) => ite.{succ u1} β (p i) (_inst_2 i) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (MonoidWithZero.toMonoid.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1))))) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β _inst_1))))) (ite.{succ u1} β (forall (i : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (p i)) (Finset.decidableDforallFinset.{u2} α s (fun (i : α) (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) => p i) (fun (a : α) (h : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) => (fun (a : α) => _inst_2 a) a)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (MonoidWithZero.toMonoid.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1))))) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β _inst_1))))
Case conversion may be inaccurate. Consider using '#align finset.prod_boole Finset.prod_booleₓ'. -/
theorem prod_boole {s : Finset α} {p : α → Prop} [DecidablePred p] :
    (∏ i in s, ite (p i) (1 : β) (0 : β)) = ite (∀ i ∈ s, p i) 1 0 :=
  by
  split_ifs
  · apply prod_eq_one
    intro i hi
    rw [if_pos (h i hi)]
  · push_neg  at h
    rcases h with ⟨i, hi, hq⟩
    apply prod_eq_zero hi
    rw [if_neg hq]
#align finset.prod_boole Finset.prod_boole

variable [Nontrivial β] [NoZeroDivisors β]

/- warning: finset.prod_eq_zero_iff -> Finset.prod_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoidWithZero.{u1} β] [_inst_2 : Nontrivial.{u1} β] [_inst_3 : NoZeroDivisors.{u1} β (MulZeroClass.toHasMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1)))) (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1))))], Iff (Eq.{succ u1} β (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1)))))))) (Exists.{succ u2} α (fun (a : α) => Exists.{0} (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) (fun (H : Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) => Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1))))))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoidWithZero.{u1} β] [_inst_2 : Nontrivial.{u1} β] [_inst_3 : NoZeroDivisors.{u1} β (MulZeroClass.toMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1)))) (CommMonoidWithZero.toZero.{u1} β _inst_1)], Iff (Eq.{succ u1} β (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β _inst_1)))) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Eq.{succ u1} β (f a) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β _inst_1))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_eq_zero_iff Finset.prod_eq_zero_iffₓ'. -/
theorem prod_eq_zero_iff : (∏ x in s, f x) = 0 ↔ ∃ a ∈ s, f a = 0 := by
  classical
    apply Finset.induction_on s
    exact ⟨Not.elim one_neZero, fun ⟨_, H, _⟩ => H.elim⟩
    intro a s ha ih
    rw [prod_insert ha, mul_eq_zero, bex_def, exists_mem_insert, ih, ← bex_def]
#align finset.prod_eq_zero_iff Finset.prod_eq_zero_iff

/- warning: finset.prod_ne_zero_iff -> Finset.prod_ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoidWithZero.{u1} β] [_inst_2 : Nontrivial.{u1} β] [_inst_3 : NoZeroDivisors.{u1} β (MulZeroClass.toHasMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1)))) (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1))))], Iff (Ne.{succ u1} β (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1)))))))) (forall (a : α), (Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) a s) -> (Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1)))))))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} {s : Finset.{u2} α} {f : α -> β} [_inst_1 : CommMonoidWithZero.{u1} β] [_inst_2 : Nontrivial.{u1} β] [_inst_3 : NoZeroDivisors.{u1} β (MulZeroClass.toMul.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (CommMonoidWithZero.toMonoidWithZero.{u1} β _inst_1)))) (CommMonoidWithZero.toZero.{u1} β _inst_1)], Iff (Ne.{succ u1} β (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β _inst_1) s (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β _inst_1)))) (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Ne.{succ u1} β (f a) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β _inst_1)))))
Case conversion may be inaccurate. Consider using '#align finset.prod_ne_zero_iff Finset.prod_ne_zero_iffₓ'. -/
theorem prod_ne_zero_iff : (∏ x in s, f x) ≠ 0 ↔ ∀ a ∈ s, f a ≠ 0 :=
  by
  rw [Ne, prod_eq_zero_iff]
  push_neg
#align finset.prod_ne_zero_iff Finset.prod_ne_zero_iff

end ProdEqZero

/- warning: finset.prod_unique_nonempty -> Finset.prod_unique_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u2} β] [_inst_2 : Unique.{succ u1} α] (s : Finset.{u1} α) (f : α -> β), (Finset.Nonempty.{u1} α s) -> (Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_1 s (fun (x : α) => f x)) (f (Inhabited.default.{succ u1} α (Unique.inhabited.{succ u1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : Unique.{succ u2} α] (s : Finset.{u2} α) (f : α -> β), (Finset.Nonempty.{u2} α s) -> (Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 s (fun (x : α) => f x)) (f (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2))))
Case conversion may be inaccurate. Consider using '#align finset.prod_unique_nonempty Finset.prod_unique_nonemptyₓ'. -/
@[to_additive]
theorem prod_unique_nonempty {α β : Type _} [CommMonoid β] [Unique α] (s : Finset α) (f : α → β)
    (h : s.Nonempty) : (∏ x in s, f x) = f default := by
  rw [h.eq_singleton_default, Finset.prod_singleton]
#align finset.prod_unique_nonempty Finset.prod_unique_nonempty
#align finset.sum_unique_nonempty Finset.sum_unique_nonempty

end Finset

namespace Fintype

open Finset

/- warning: fintype.prod_bijective -> Fintype.prod_bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u3} M] (e : α -> β), (Function.Bijective.{succ u1, succ u2} α β e) -> (forall (f : α -> M) (g : β -> M), (forall (x : α), Eq.{succ u3} M (f x) (g (e x))) -> (Eq.{succ u3} M (Finset.prod.{u3, u1} M α _inst_3 (Finset.univ.{u1} α _inst_1) (fun (x : α) => f x)) (Finset.prod.{u3, u2} M β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (x : β) => g x))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Fintype.{u3} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u1} M] (e : α -> β), (Function.Bijective.{succ u3, succ u2} α β e) -> (forall (f : α -> M) (g : β -> M), (forall (x : α), Eq.{succ u1} M (f x) (g (e x))) -> (Eq.{succ u1} M (Finset.prod.{u1, u3} M α _inst_3 (Finset.univ.{u3} α _inst_1) (fun (x : α) => f x)) (Finset.prod.{u1, u2} M β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (x : β) => g x))))
Case conversion may be inaccurate. Consider using '#align fintype.prod_bijective Fintype.prod_bijectiveₓ'. -/
/-- `fintype.prod_bijective` is a variant of `finset.prod_bij` that accepts `function.bijective`.

See `function.bijective.prod_comp` for a version without `h`. -/
@[to_additive
      "`fintype.sum_equiv` is a variant of `finset.sum_bij` that accepts\n`function.bijective`.\n\nSee `function.bijective.sum_comp` for a version without `h`. "]
theorem prod_bijective {α β M : Type _} [Fintype α] [Fintype β] [CommMonoid M] (e : α → β)
    (he : Function.Bijective e) (f : α → M) (g : β → M) (h : ∀ x, f x = g (e x)) :
    (∏ x : α, f x) = ∏ x : β, g x :=
  prod_bij (fun x _ => e x) (fun x _ => mem_univ (e x)) (fun x _ => h x)
    (fun x x' _ _ h => he.Injective h) fun y _ =>
    (he.Surjective y).imp fun a h => ⟨mem_univ _, h.symm⟩
#align fintype.prod_bijective Fintype.prod_bijective
#align fintype.sum_bijective Fintype.sum_bijective

/- warning: fintype.prod_equiv -> Fintype.prod_equiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {M : Type.{u3}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u3} M] (e : Equiv.{succ u1, succ u2} α β) (f : α -> M) (g : β -> M), (forall (x : α), Eq.{succ u3} M (f x) (g (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e x))) -> (Eq.{succ u3} M (Finset.prod.{u3, u1} M α _inst_3 (Finset.univ.{u1} α _inst_1) (fun (x : α) => f x)) (Finset.prod.{u3, u2} M β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (x : β) => g x)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {M : Type.{u1}} [_inst_1 : Fintype.{u3} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u1} M] (e : Equiv.{succ u3, succ u2} α β) (f : α -> M) (g : β -> M), (forall (x : α), Eq.{succ u1} M (f x) (g (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Equiv.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Equiv.{succ u3, succ u2} α β) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Equiv.{succ u3, succ u2} α β) α β (Equiv.instEquivLikeEquiv.{succ u3, succ u2} α β))) e x))) -> (Eq.{succ u1} M (Finset.prod.{u1, u3} M α _inst_3 (Finset.univ.{u3} α _inst_1) (fun (x : α) => f x)) (Finset.prod.{u1, u2} M β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (x : β) => g x)))
Case conversion may be inaccurate. Consider using '#align fintype.prod_equiv Fintype.prod_equivₓ'. -/
/-- `fintype.prod_equiv` is a specialization of `finset.prod_bij` that
automatically fills in most arguments.

See `equiv.prod_comp` for a version without `h`.
-/
@[to_additive
      "`fintype.sum_equiv` is a specialization of `finset.sum_bij` that\nautomatically fills in most arguments.\n\nSee `equiv.sum_comp` for a version without `h`.\n"]
theorem prod_equiv {α β M : Type _} [Fintype α] [Fintype β] [CommMonoid M] (e : α ≃ β) (f : α → M)
    (g : β → M) (h : ∀ x, f x = g (e x)) : (∏ x : α, f x) = ∏ x : β, g x :=
  prod_bijective e e.Bijective f g h
#align fintype.prod_equiv Fintype.prod_equiv
#align fintype.sum_equiv Fintype.sum_equiv

variable {f s}

/- warning: fintype.prod_unique -> Fintype.prod_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u2} β] [_inst_2 : Unique.{succ u1} α] [_inst_3 : Fintype.{u1} α] (f : α -> β), Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_1 (Finset.univ.{u1} α _inst_3) (fun (x : α) => f x)) (f (Inhabited.default.{succ u1} α (Unique.inhabited.{succ u1} α _inst_2)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : Unique.{succ u2} α] [_inst_3 : Fintype.{u2} α] (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_3) (fun (x : α) => f x)) (f (Inhabited.default.{succ u2} α (Unique.instInhabited.{succ u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align fintype.prod_unique Fintype.prod_uniqueₓ'. -/
@[to_additive]
theorem prod_unique {α β : Type _} [CommMonoid β] [Unique α] [Fintype α] (f : α → β) :
    (∏ x : α, f x) = f default := by rw [univ_unique, prod_singleton]
#align fintype.prod_unique Fintype.prod_unique
#align fintype.sum_unique Fintype.sum_unique

/- warning: fintype.prod_empty -> Fintype.prod_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u2} β] [_inst_2 : IsEmpty.{succ u1} α] [_inst_3 : Fintype.{u1} α] (f : α -> β), Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_1 (Finset.univ.{u1} α _inst_3) (fun (x : α) => f x)) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_1))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : IsEmpty.{succ u2} α] [_inst_3 : Fintype.{u2} α] (f : α -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_3) (fun (x : α) => f x)) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))
Case conversion may be inaccurate. Consider using '#align fintype.prod_empty Fintype.prod_emptyₓ'. -/
@[to_additive]
theorem prod_empty {α β : Type _} [CommMonoid β] [IsEmpty α] [Fintype α] (f : α → β) :
    (∏ x : α, f x) = 1 :=
  Finset.prod_of_empty _
#align fintype.prod_empty Fintype.prod_empty
#align fintype.sum_empty Fintype.sum_empty

/- warning: fintype.prod_subsingleton -> Fintype.prod_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u2} β] [_inst_2 : Subsingleton.{succ u1} α] [_inst_3 : Fintype.{u1} α] (f : α -> β) (a : α), Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_1 (Finset.univ.{u1} α _inst_3) (fun (x : α) => f x)) (f a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] [_inst_2 : Subsingleton.{succ u2} α] [_inst_3 : Fintype.{u2} α] (f : α -> β) (a : α), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_1 (Finset.univ.{u2} α _inst_3) (fun (x : α) => f x)) (f a)
Case conversion may be inaccurate. Consider using '#align fintype.prod_subsingleton Fintype.prod_subsingletonₓ'. -/
@[to_additive]
theorem prod_subsingleton {α β : Type _} [CommMonoid β] [Subsingleton α] [Fintype α] (f : α → β)
    (a : α) : (∏ x : α, f x) = f a :=
  by
  haveI : Unique α := uniqueOfSubsingleton a
  convert prod_unique f
#align fintype.prod_subsingleton Fintype.prod_subsingleton
#align fintype.sum_subsingleton Fintype.sum_subsingleton

/- warning: fintype.prod_subtype_mul_prod_subtype -> Fintype.prod_subtype_mul_prod_subtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CommMonoid.{u2} β] (p : α -> Prop) (f : α -> β) [_inst_3 : DecidablePred.{succ u1} α p], Eq.{succ u2} β (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)))) (Finset.prod.{u2, u1} β (Subtype.{succ u1} α (fun (x : α) => p x)) _inst_2 (Finset.univ.{u1} (Subtype.{succ u1} α (fun (x : α) => p x)) (Subtype.fintype.{u1} α (fun (x : α) => p x) (fun (a : α) => _inst_3 a) _inst_1)) (fun (i : Subtype.{succ u1} α (fun (x : α) => p x)) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => p x)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => p x)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => p x)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => p x)) α (coeSubtype.{succ u1} α (fun (x : α) => p x))))) i))) (Finset.prod.{u2, u1} β (Subtype.{succ u1} α (fun (x : α) => Not (p x))) _inst_2 (Finset.univ.{u1} (Subtype.{succ u1} α (fun (x : α) => Not (p x))) (Subtype.fintype.{u1} α (fun (x : α) => Not (p x)) (fun (a : α) => Not.decidable (p a) (_inst_3 a)) _inst_1)) (fun (i : Subtype.{succ u1} α (fun (x : α) => Not (p x))) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Not (p x))) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Not (p x))) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Not (p x))) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Not (p x))) α (coeSubtype.{succ u1} α (fun (x : α) => Not (p x)))))) i)))) (Finset.prod.{u2, u1} β α _inst_2 (Finset.univ.{u1} α _inst_1) (fun (i : α) => f i))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : CommMonoid.{u1} β] (p : α -> Prop) (f : α -> β) [_inst_3 : DecidablePred.{succ u2} α p], Eq.{succ u1} β (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_2)))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => p x)) _inst_2 (Finset.univ.{u2} (Subtype.{succ u2} α (fun (x : α) => p x)) (Subtype.fintype.{u2} α (fun (x : α) => p x) (fun (a : α) => _inst_3 a) _inst_1)) (fun (i : Subtype.{succ u2} α (fun (x : α) => p x)) => f (Subtype.val.{succ u2} α (fun (x : α) => p x) i))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => Not (p x))) _inst_2 (Finset.univ.{u2} (Subtype.{succ u2} α (fun (x : α) => Not (p x))) (Subtype.fintype.{u2} α (fun (x : α) => Not (p x)) (fun (a : α) => instDecidableNot (p a) (_inst_3 a)) _inst_1)) (fun (i : Subtype.{succ u2} α (fun (x : α) => Not (p x))) => f (Subtype.val.{succ u2} α (fun (x : α) => Not (p x)) i)))) (Finset.prod.{u1, u2} β α _inst_2 (Finset.univ.{u2} α _inst_1) (fun (i : α) => f i))
Case conversion may be inaccurate. Consider using '#align fintype.prod_subtype_mul_prod_subtype Fintype.prod_subtype_mul_prod_subtypeₓ'. -/
@[to_additive]
theorem prod_subtype_mul_prod_subtype {α β : Type _} [Fintype α] [CommMonoid β] (p : α → Prop)
    (f : α → β) [DecidablePred p] :
    ((∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i) = ∏ i, f i := by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s, ← Finset.prod_subtype (sᶜ)]
    · exact Finset.prod_mul_prod_compl _ _
    · simp
    · simp
#align fintype.prod_subtype_mul_prod_subtype Fintype.prod_subtype_mul_prod_subtype
#align fintype.sum_subtype_add_sum_subtype Fintype.sum_subtype_add_sum_subtype

end Fintype

namespace List

/- warning: list.prod_to_finset -> List.prod_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommMonoid.{u2} M] (f : α -> M) {l : List.{u1} α}, (List.Nodup.{u1} α l) -> (Eq.{succ u2} M (Finset.prod.{u2, u1} M α _inst_2 (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l) f) (List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) (List.map.{u1, u2} α M f l)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : CommMonoid.{u1} M] (f : α -> M) {l : List.{u2} α}, (List.Nodup.{u2} α l) -> (Eq.{succ u1} M (Finset.prod.{u1, u2} M α _inst_2 (List.toFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b) l) f) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) (List.map.{u2, u1} α M f l)))
Case conversion may be inaccurate. Consider using '#align list.prod_to_finset List.prod_toFinsetₓ'. -/
@[to_additive]
theorem prod_toFinset {M : Type _} [DecidableEq α] [CommMonoid M] (f : α → M) :
    ∀ {l : List α} (hl : l.Nodup), l.toFinset.Prod f = (l.map f).Prod
  | [], _ => by simp
  | a :: l, hl => by
    let ⟨not_mem, hl⟩ := List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt list.mem_to_finset.mp not_mem), prod_to_finset hl]
#align list.prod_to_finset List.prod_toFinset
#align list.sum_to_finset List.sum_toFinset

end List

namespace Multiset

#print Multiset.disjoint_list_sum_left /-
theorem disjoint_list_sum_left {a : Multiset α} {l : List (Multiset α)} :
    Multiset.Disjoint l.Sum a ↔ ∀ b ∈ l, Multiset.Disjoint b a :=
  by
  induction' l with b bs ih
  · simp only [zero_disjoint, List.not_mem_nil, IsEmpty.forall_iff, forall_const, List.sum_nil]
  · simp_rw [List.sum_cons, disjoint_add_left, List.mem_cons, forall_eq_or_imp]
    simp [and_congr_left_iff, iff_self_iff, ih]
#align multiset.disjoint_list_sum_left Multiset.disjoint_list_sum_left
-/

#print Multiset.disjoint_list_sum_right /-
theorem disjoint_list_sum_right {a : Multiset α} {l : List (Multiset α)} :
    Multiset.Disjoint a l.Sum ↔ ∀ b ∈ l, Multiset.Disjoint a b := by
  simpa only [disjoint_comm] using disjoint_list_sum_left
#align multiset.disjoint_list_sum_right Multiset.disjoint_list_sum_right
-/

/- warning: multiset.disjoint_sum_left -> Multiset.disjoint_sum_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : Multiset.{u1} α} {i : Multiset.{u1} (Multiset.{u1} α)}, Iff (Multiset.Disjoint.{u1} α (Multiset.sum.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)) i) a) (forall (b : Multiset.{u1} α), (Membership.Mem.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} (Multiset.{u1} α)) (Multiset.hasMem.{u1} (Multiset.{u1} α)) b i) -> (Multiset.Disjoint.{u1} α b a))
but is expected to have type
  forall {α : Type.{u1}} {a : Multiset.{u1} α} {i : Multiset.{u1} (Multiset.{u1} α)}, Iff (Multiset.Disjoint.{u1} α (Multiset.sum.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)) i) a) (forall (b : Multiset.{u1} α), (Membership.mem.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instMembershipMultiset.{u1} (Multiset.{u1} α)) b i) -> (Multiset.Disjoint.{u1} α b a))
Case conversion may be inaccurate. Consider using '#align multiset.disjoint_sum_left Multiset.disjoint_sum_leftₓ'. -/
theorem disjoint_sum_left {a : Multiset α} {i : Multiset (Multiset α)} :
    Multiset.Disjoint i.Sum a ↔ ∀ b ∈ i, Multiset.Disjoint b a :=
  Quotient.inductionOn i fun l =>
    by
    rw [quot_mk_to_coe, Multiset.coe_sum]
    exact disjoint_list_sum_left
#align multiset.disjoint_sum_left Multiset.disjoint_sum_left

/- warning: multiset.disjoint_sum_right -> Multiset.disjoint_sum_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : Multiset.{u1} α} {i : Multiset.{u1} (Multiset.{u1} α)}, Iff (Multiset.Disjoint.{u1} α a (Multiset.sum.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)) i)) (forall (b : Multiset.{u1} α), (Membership.Mem.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} (Multiset.{u1} α)) (Multiset.hasMem.{u1} (Multiset.{u1} α)) b i) -> (Multiset.Disjoint.{u1} α a b))
but is expected to have type
  forall {α : Type.{u1}} {a : Multiset.{u1} α} {i : Multiset.{u1} (Multiset.{u1} α)}, Iff (Multiset.Disjoint.{u1} α a (Multiset.sum.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)) i)) (forall (b : Multiset.{u1} α), (Membership.mem.{u1, u1} (Multiset.{u1} α) (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instMembershipMultiset.{u1} (Multiset.{u1} α)) b i) -> (Multiset.Disjoint.{u1} α a b))
Case conversion may be inaccurate. Consider using '#align multiset.disjoint_sum_right Multiset.disjoint_sum_rightₓ'. -/
theorem disjoint_sum_right {a : Multiset α} {i : Multiset (Multiset α)} :
    Multiset.Disjoint a i.Sum ↔ ∀ b ∈ i, Multiset.Disjoint a b := by
  simpa only [disjoint_comm] using disjoint_sum_left
#align multiset.disjoint_sum_right Multiset.disjoint_sum_right

/- warning: multiset.disjoint_finset_sum_left -> Multiset.disjoint_finset_sum_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {i : Finset.{u2} β} {f : β -> (Multiset.{u1} α)} {a : Multiset.{u1} α}, Iff (Multiset.Disjoint.{u1} α (Finset.sum.{u1, u2} (Multiset.{u1} α) β (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)) i f) a) (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b i) -> (Multiset.Disjoint.{u1} α (f b) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {i : Finset.{u1} β} {f : β -> (Multiset.{u2} α)} {a : Multiset.{u2} α}, Iff (Multiset.Disjoint.{u2} α (Finset.sum.{u2, u1} (Multiset.{u2} α) β (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)) i f) a) (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b i) -> (Multiset.Disjoint.{u2} α (f b) a))
Case conversion may be inaccurate. Consider using '#align multiset.disjoint_finset_sum_left Multiset.disjoint_finset_sum_leftₓ'. -/
theorem disjoint_finset_sum_left {β : Type _} {i : Finset β} {f : β → Multiset α} {a : Multiset α} :
    Multiset.Disjoint (i.Sum f) a ↔ ∀ b ∈ i, Multiset.Disjoint (f b) a :=
  by
  convert (@disjoint_sum_left _ a) (map f i.val)
  simp [and_congr_left_iff, iff_self_iff]
#align multiset.disjoint_finset_sum_left Multiset.disjoint_finset_sum_left

/- warning: multiset.disjoint_finset_sum_right -> Multiset.disjoint_finset_sum_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {i : Finset.{u2} β} {f : β -> (Multiset.{u1} α)} {a : Multiset.{u1} α}, Iff (Multiset.Disjoint.{u1} α a (Finset.sum.{u1, u2} (Multiset.{u1} α) β (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)) i f)) (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b i) -> (Multiset.Disjoint.{u1} α a (f b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {i : Finset.{u1} β} {f : β -> (Multiset.{u2} α)} {a : Multiset.{u2} α}, Iff (Multiset.Disjoint.{u2} α a (Finset.sum.{u2, u1} (Multiset.{u2} α) β (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)) i f)) (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b i) -> (Multiset.Disjoint.{u2} α a (f b)))
Case conversion may be inaccurate. Consider using '#align multiset.disjoint_finset_sum_right Multiset.disjoint_finset_sum_rightₓ'. -/
theorem disjoint_finset_sum_right {β : Type _} {i : Finset β} {f : β → Multiset α}
    {a : Multiset α} : Multiset.Disjoint a (i.Sum f) ↔ ∀ b ∈ i, Multiset.Disjoint a (f b) := by
  simpa only [disjoint_comm] using disjoint_finset_sum_left
#align multiset.disjoint_finset_sum_right Multiset.disjoint_finset_sum_right

variable [DecidableEq α]

/- warning: multiset.add_eq_union_left_of_le -> Multiset.add_eq_union_left_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {x : Multiset.{u1} α} {y : Multiset.{u1} α} {z : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) y x) -> (Iff (Eq.{succ u1} (Multiset.{u1} α) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) z x) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) z y)) (And (Multiset.Disjoint.{u1} α z x) (Eq.{succ u1} (Multiset.{u1} α) x y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {x : Multiset.{u1} α} {y : Multiset.{u1} α} {z : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) y x) -> (Iff (Eq.{succ u1} (Multiset.{u1} α) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) z x) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) z y)) (And (Multiset.Disjoint.{u1} α z x) (Eq.{succ u1} (Multiset.{u1} α) x y)))
Case conversion may be inaccurate. Consider using '#align multiset.add_eq_union_left_of_le Multiset.add_eq_union_left_of_leₓ'. -/
theorem add_eq_union_left_of_le {x y z : Multiset α} (h : y ≤ x) :
    z + x = z ∪ y ↔ z.Disjoint x ∧ x = y :=
  by
  rw [← add_eq_union_iff_disjoint]
  constructor
  · intro h0
    rw [and_iff_right_of_imp]
    · exact (le_of_add_le_add_left <| h0.trans_le <| union_le_add z y).antisymm h
    · rintro rfl
      exact h0
  · rintro ⟨h0, rfl⟩
    exact h0
#align multiset.add_eq_union_left_of_le Multiset.add_eq_union_left_of_le

/- warning: multiset.add_eq_union_right_of_le -> Multiset.add_eq_union_right_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {x : Multiset.{u1} α} {y : Multiset.{u1} α} {z : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) z y) -> (Iff (Eq.{succ u1} (Multiset.{u1} α) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.hasAdd.{u1} α)) x y) (Union.union.{u1} (Multiset.{u1} α) (Multiset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x z)) (And (Eq.{succ u1} (Multiset.{u1} α) y z) (Multiset.Disjoint.{u1} α x y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {x : Multiset.{u1} α} {y : Multiset.{u1} α} {z : Multiset.{u1} α}, (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) z y) -> (Iff (Eq.{succ u1} (Multiset.{u1} α) (HAdd.hAdd.{u1, u1, u1} (Multiset.{u1} α) (Multiset.{u1} α) (Multiset.{u1} α) (instHAdd.{u1} (Multiset.{u1} α) (Multiset.instAddMultiset.{u1} α)) x y) (Union.union.{u1} (Multiset.{u1} α) (Multiset.instUnionMultiset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) x z)) (And (Eq.{succ u1} (Multiset.{u1} α) y z) (Multiset.Disjoint.{u1} α x y)))
Case conversion may be inaccurate. Consider using '#align multiset.add_eq_union_right_of_le Multiset.add_eq_union_right_of_leₓ'. -/
theorem add_eq_union_right_of_le {x y z : Multiset α} (h : z ≤ y) :
    x + y = x ∪ z ↔ y = z ∧ x.Disjoint y := by
  simpa only [and_comm'] using add_eq_union_left_of_le h
#align multiset.add_eq_union_right_of_le Multiset.add_eq_union_right_of_le

/- warning: multiset.finset_sum_eq_sup_iff_disjoint -> Multiset.finset_sum_eq_sup_iff_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {β : Type.{u2}} {i : Finset.{u2} β} {f : β -> (Multiset.{u1} α)}, Iff (Eq.{succ u1} (Multiset.{u1} α) (Finset.sum.{u1, u2} (Multiset.{u1} α) β (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)) i f) (Finset.sup.{u1, u2} (Multiset.{u1} α) β (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} α) (Multiset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Multiset.orderBot.{u1} α) i f)) (forall (x : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x i) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y i) -> (Ne.{succ u2} β x y) -> (Multiset.Disjoint.{u1} α (f x) (f y))))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {β : Type.{u1}} {i : Finset.{u1} β} {f : β -> (Multiset.{u2} α)}, Iff (Eq.{succ u2} (Multiset.{u2} α) (Finset.sum.{u2, u1} (Multiset.{u2} α) β (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)) i f) (Finset.sup.{u2, u1} (Multiset.{u2} α) β (Lattice.toSemilatticeSup.{u2} (Multiset.{u2} α) (Multiset.instLatticeMultiset.{u2} α (fun (a : α) (b : α) => _inst_1 a b))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u2} α) i f)) (forall (x : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x i) -> (forall (y : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y i) -> (Ne.{succ u1} β x y) -> (Multiset.Disjoint.{u2} α (f x) (f y))))
Case conversion may be inaccurate. Consider using '#align multiset.finset_sum_eq_sup_iff_disjoint Multiset.finset_sum_eq_sup_iff_disjointₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ∈ » i) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » i) -/
theorem finset_sum_eq_sup_iff_disjoint {β : Type _} {i : Finset β} {f : β → Multiset α} :
    i.Sum f = i.sup f ↔ ∀ (x) (_ : x ∈ i) (y) (_ : y ∈ i), x ≠ y → Multiset.Disjoint (f x) (f y) :=
  by
  induction' i using Finset.cons_induction_on with z i hz hr
  ·
    simp only [Finset.not_mem_empty, IsEmpty.forall_iff, imp_true_iff, Finset.sum_empty,
      Finset.sup_empty, bot_eq_zero, eq_self_iff_true]
  · simp_rw [Finset.sum_cons hz, Finset.sup_cons, Finset.mem_cons, Multiset.sup_eq_union,
      forall_eq_or_imp, Ne.def, eq_self_iff_true, not_true, IsEmpty.forall_iff, true_and_iff,
      imp_and, forall_and, ← hr, @eq_comm _ z]
    have := fun x (_ : x ∈ i) => ne_of_mem_of_not_mem H hz
    simp (config := { contextual := true }) only [this, not_false_iff, true_imp_iff]
    simp_rw [← disjoint_finset_sum_left, ← disjoint_finset_sum_right, disjoint_comm, ← and_assoc',
      and_self_iff]
    exact add_eq_union_left_of_le (Finset.sup_le fun x hx => le_sum_of_mem (mem_map_of_mem f hx))
#align multiset.finset_sum_eq_sup_iff_disjoint Multiset.finset_sum_eq_sup_iff_disjoint

/- warning: multiset.sup_powerset_len -> Multiset.sup_powerset_len is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] (x : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} (Multiset.{u1} α)) (Finset.sup.{u1, 0} (Multiset.{u1} (Multiset.{u1} α)) Nat (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.lattice.{u1} (Multiset.{u1} α) (fun (a : Multiset.{u1} α) (b : Multiset.{u1} α) => Multiset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a b))) (Multiset.orderBot.{u1} (Multiset.{u1} α)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) x) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => Multiset.powersetLen.{u1} α k x)) (Multiset.powerset.{u1} α x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] (x : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} (Multiset.{u1} α)) (Finset.sup.{u1, 0} (Multiset.{u1} (Multiset.{u1} α)) Nat (Lattice.toSemilatticeSup.{u1} (Multiset.{u1} (Multiset.{u1} α)) (Multiset.instLatticeMultiset.{u1} (Multiset.{u1} α) (fun (a : Multiset.{u1} α) (b : Multiset.{u1} α) => Multiset.decidableEq.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a b))) (Multiset.instOrderBotMultisetToLEToPreorderInstPartialOrderMultiset.{u1} (Multiset.{u1} α)) (Finset.range (HAdd.hAdd.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) x) Nat ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) x) (instHAdd.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) x) instAddNat) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) x) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => Multiset.powersetLen.{u1} α k x)) (Multiset.powerset.{u1} α x)
Case conversion may be inaccurate. Consider using '#align multiset.sup_powerset_len Multiset.sup_powerset_lenₓ'. -/
theorem sup_powerset_len {α : Type _} [DecidableEq α] (x : Multiset α) :
    (Finset.sup (Finset.range (x.card + 1)) fun k => x.powersetLen k) = x.powerset :=
  by
  convert bind_powerset_len x
  rw [Multiset.bind, Multiset.join, ← Finset.range_val, ← Finset.sum_eq_multiset_sum]
  exact
    Eq.symm (finset_sum_eq_sup_iff_disjoint.mpr fun _ _ _ _ h => pairwise_disjoint_powerset_len x h)
#align multiset.sup_powerset_len Multiset.sup_powerset_len

/- warning: multiset.to_finset_sum_count_eq -> Multiset.toFinset_sum_count_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α), Eq.{1} Nat (Finset.sum.{0, u1} Nat α Nat.addCommMonoid (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (fun (a : α) => Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s)) (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α), Eq.{1} Nat (Finset.sum.{0, u1} Nat α Nat.addCommMonoid (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (fun (a : α) => Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s)) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s)
Case conversion may be inaccurate. Consider using '#align multiset.to_finset_sum_count_eq Multiset.toFinset_sum_count_eqₓ'. -/
@[simp]
theorem toFinset_sum_count_eq (s : Multiset α) : (∑ a in s.toFinset, s.count a) = s.card :=
  calc
    (∑ a in s.toFinset, s.count a) = ∑ a in s.toFinset, s.count a • 1 := by
      simp only [smul_eq_mul, mul_one]
    _ = (s.map fun _ => 1).Sum := (Finset.sum_multiset_map_count _ _).symm
    _ = s.card := by simp
    
#align multiset.to_finset_sum_count_eq Multiset.toFinset_sum_count_eq

/- warning: multiset.count_sum' -> Multiset.count_sum' is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {a : α} {f : β -> (Multiset.{u2} α)}, Eq.{1} Nat (Multiset.count.{u2} α (fun (a : α) (b : α) => _inst_1 a b) a (Finset.sum.{u2, u1} (Multiset.{u2} α) β (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.orderedCancelAddCommMonoid.{u2} α)) s (fun (x : β) => f x))) (Finset.sum.{0, u1} Nat β Nat.addCommMonoid s (fun (x : β) => Multiset.count.{u2} α (fun (a : α) (b : α) => _inst_1 a b) a (f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {a : α} {f : β -> (Multiset.{u2} α)}, Eq.{1} Nat (Multiset.count.{u2} α (fun (a : α) (b : α) => _inst_1 a b) a (Finset.sum.{u2, u1} (Multiset.{u2} α) β (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)) s (fun (x : β) => f x))) (Finset.sum.{0, u1} Nat β Nat.addCommMonoid s (fun (x : β) => Multiset.count.{u2} α (fun (a : α) (b : α) => _inst_1 a b) a (f x)))
Case conversion may be inaccurate. Consider using '#align multiset.count_sum' Multiset.count_sum'ₓ'. -/
theorem count_sum' {s : Finset β} {a : α} {f : β → Multiset α} :
    count a (∑ x in s, f x) = ∑ x in s, count a (f x) :=
  by
  dsimp only [Finset.sum]
  rw [count_sum]
#align multiset.count_sum' Multiset.count_sum'

/- warning: multiset.to_finset_sum_count_nsmul_eq -> Multiset.toFinset_sum_count_nsmul_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Finset.sum.{u1, u1} (Multiset.{u1} α) α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (fun (a : α) => SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α) a))) s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α), Eq.{succ u1} (Multiset.{u1} α) (Finset.sum.{u1, u1} (Multiset.{u1} α) α (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (fun (a : α) => HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α) a))) s
Case conversion may be inaccurate. Consider using '#align multiset.to_finset_sum_count_nsmul_eq Multiset.toFinset_sum_count_nsmul_eqₓ'. -/
@[simp]
theorem toFinset_sum_count_nsmul_eq (s : Multiset α) : (∑ a in s.toFinset, s.count a • {a}) = s :=
  by rw [← Finset.sum_multiset_map_count, Multiset.sum_map_singleton]
#align multiset.to_finset_sum_count_nsmul_eq Multiset.toFinset_sum_count_nsmul_eq

/- warning: multiset.exists_smul_of_dvd_count -> Multiset.exists_smul_of_dvd_count is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) {k : Nat}, (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (Dvd.Dvd.{0} Nat Nat.hasDvd k (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s))) -> (Exists.{succ u1} (Multiset.{u1} α) (fun (u : Multiset.{u1} α) => Eq.{succ u1} (Multiset.{u1} α) s (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) k u)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) {k : Nat}, (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (Dvd.dvd.{0} Nat Nat.instDvdNat k (Multiset.count.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a s))) -> (Exists.{succ u1} (Multiset.{u1} α) (fun (u : Multiset.{u1} α) => Eq.{succ u1} (Multiset.{u1} α) s (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) k u)))
Case conversion may be inaccurate. Consider using '#align multiset.exists_smul_of_dvd_count Multiset.exists_smul_of_dvd_countₓ'. -/
theorem exists_smul_of_dvd_count (s : Multiset α) {k : ℕ}
    (h : ∀ a : α, a ∈ s → k ∣ Multiset.count a s) : ∃ u : Multiset α, s = k • u :=
  by
  use ∑ a in s.to_finset, (s.count a / k) • {a}
  have h₂ :
    (∑ x : α in s.to_finset, k • (count x s / k) • ({x} : Multiset α)) =
      ∑ x : α in s.to_finset, count x s • {x} :=
    by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul', Nat.mul_div_cancel' (h x (mem_to_finset.mp hx))]
  rw [← Finset.sum_nsmul, h₂, to_finset_sum_count_nsmul_eq]
#align multiset.exists_smul_of_dvd_count Multiset.exists_smul_of_dvd_count

#print Multiset.toFinset_prod_dvd_prod /-
theorem toFinset_prod_dvd_prod [CommMonoid α] (S : Multiset α) : S.toFinset.Prod id ∣ S.Prod :=
  by
  rw [Finset.prod_eq_multiset_prod]
  refine' Multiset.prod_dvd_prod_of_le _
  simp [Multiset.dedup_le S]
#align multiset.to_finset_prod_dvd_prod Multiset.toFinset_prod_dvd_prod
-/

/- warning: multiset.prod_sum -> Multiset.prod_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_2 : CommMonoid.{u1} α] (f : ι -> (Multiset.{u1} α)) (s : Finset.{u2} ι), Eq.{succ u1} α (Multiset.prod.{u1} α _inst_2 (Finset.sum.{u1, u2} (Multiset.{u1} α) ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)) s (fun (x : ι) => f x))) (Finset.prod.{u1, u2} α ι _inst_2 s (fun (x : ι) => Multiset.prod.{u1} α _inst_2 (f x)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_2 : CommMonoid.{u2} α] (f : ι -> (Multiset.{u2} α)) (s : Finset.{u1} ι), Eq.{succ u2} α (Multiset.prod.{u2} α _inst_2 (Finset.sum.{u2, u1} (Multiset.{u2} α) ι (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} (Multiset.{u2} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u2} α)) s (fun (x : ι) => f x))) (Finset.prod.{u2, u1} α ι _inst_2 s (fun (x : ι) => Multiset.prod.{u2} α _inst_2 (f x)))
Case conversion may be inaccurate. Consider using '#align multiset.prod_sum Multiset.prod_sumₓ'. -/
@[to_additive]
theorem prod_sum {α : Type _} {ι : Type _} [CommMonoid α] (f : ι → Multiset α) (s : Finset ι) :
    (∑ x in s, f x).Prod = ∏ x in s, (f x).Prod := by
  classical
    induction' s using Finset.induction_on with a t hat ih
    · rw [Finset.sum_empty, Finset.prod_empty, Multiset.prod_zero]
    · rw [Finset.sum_insert hat, Finset.prod_insert hat, Multiset.prod_add, ih]
#align multiset.prod_sum Multiset.prod_sum
#align multiset.sum_sum Multiset.sum_sum

end Multiset

namespace Nat

/- warning: nat.cast_list_sum -> Nat.cast_list_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} β] (s : List.{0} Nat), Eq.{succ u1} β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat β (HasLiftT.mk.{1, succ u1} Nat β (CoeTCₓ.coe.{1, succ u1} Nat β (Nat.castCoe.{u1} β (AddMonoidWithOne.toNatCast.{u1} β _inst_1)))) (List.sum.{0} Nat Nat.hasAdd Nat.hasZero s)) (List.sum.{u1} β (AddZeroClass.toHasAdd.{u1} β (AddMonoid.toAddZeroClass.{u1} β (AddMonoidWithOne.toAddMonoid.{u1} β _inst_1))) (AddZeroClass.toHasZero.{u1} β (AddMonoid.toAddZeroClass.{u1} β (AddMonoidWithOne.toAddMonoid.{u1} β _inst_1))) (List.map.{0, u1} Nat β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat β (HasLiftT.mk.{1, succ u1} Nat β (CoeTCₓ.coe.{1, succ u1} Nat β (Nat.castCoe.{u1} β (AddMonoidWithOne.toNatCast.{u1} β _inst_1))))) s))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : AddMonoidWithOne.{u1} β] (s : List.{0} Nat), Eq.{succ u1} β (Nat.cast.{u1} β (AddMonoidWithOne.toNatCast.{u1} β _inst_1) (List.sum.{0} Nat instAddNat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) s)) (List.sum.{u1} β (AddZeroClass.toAdd.{u1} β (AddMonoid.toAddZeroClass.{u1} β (AddMonoidWithOne.toAddMonoid.{u1} β _inst_1))) (AddMonoid.toZero.{u1} β (AddMonoidWithOne.toAddMonoid.{u1} β _inst_1)) (List.map.{0, u1} Nat β (Nat.cast.{u1} β (AddMonoidWithOne.toNatCast.{u1} β _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align nat.cast_list_sum Nat.cast_list_sumₓ'. -/
@[simp, norm_cast]
theorem cast_list_sum [AddMonoidWithOne β] (s : List ℕ) : (↑s.Sum : β) = (s.map coe).Sum :=
  map_list_sum (castAddMonoidHom β) _
#align nat.cast_list_sum Nat.cast_list_sum

/- warning: nat.cast_list_prod -> Nat.cast_list_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : Semiring.{u1} β] (s : List.{0} Nat), Eq.{succ u1} β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat β (HasLiftT.mk.{1, succ u1} Nat β (CoeTCₓ.coe.{1, succ u1} Nat β (Nat.castCoe.{u1} β (AddMonoidWithOne.toNatCast.{u1} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} β (NonAssocSemiring.toAddCommMonoidWithOne.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1))))))) (List.prod.{0} Nat Nat.hasMul Nat.hasOne s)) (List.prod.{u1} β (Distrib.toHasMul.{u1} β (NonUnitalNonAssocSemiring.toDistrib.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)))) (AddMonoidWithOne.toOne.{u1} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} β (NonAssocSemiring.toAddCommMonoidWithOne.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)))) (List.map.{0, u1} Nat β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat β (HasLiftT.mk.{1, succ u1} Nat β (CoeTCₓ.coe.{1, succ u1} Nat β (Nat.castCoe.{u1} β (AddMonoidWithOne.toNatCast.{u1} β (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} β (NonAssocSemiring.toAddCommMonoidWithOne.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1)))))))) s))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : Semiring.{u1} β] (s : List.{0} Nat), Eq.{succ u1} β (Nat.cast.{u1} β (Semiring.toNatCast.{u1} β _inst_1) (List.prod.{0} Nat instMulNat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) s)) (List.prod.{u1} β (NonUnitalNonAssocSemiring.toMul.{u1} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} β (Semiring.toNonAssocSemiring.{u1} β _inst_1))) (Semiring.toOne.{u1} β _inst_1) (List.map.{0, u1} Nat β (Nat.cast.{u1} β (Semiring.toNatCast.{u1} β _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align nat.cast_list_prod Nat.cast_list_prodₓ'. -/
@[simp, norm_cast]
theorem cast_list_prod [Semiring β] (s : List ℕ) : (↑s.Prod : β) = (s.map coe).Prod :=
  map_list_prod (castRingHom β) _
#align nat.cast_list_prod Nat.cast_list_prod

#print Nat.cast_multiset_sum /-
@[simp, norm_cast]
theorem cast_multiset_sum [AddCommMonoidWithOne β] (s : Multiset ℕ) :
    (↑s.Sum : β) = (s.map coe).Sum :=
  map_multiset_sum (castAddMonoidHom β) _
#align nat.cast_multiset_sum Nat.cast_multiset_sum
-/

#print Nat.cast_multiset_prod /-
@[simp, norm_cast]
theorem cast_multiset_prod [CommSemiring β] (s : Multiset ℕ) : (↑s.Prod : β) = (s.map coe).Prod :=
  map_multiset_prod (castRingHom β) _
#align nat.cast_multiset_prod Nat.cast_multiset_prod
-/

#print Nat.cast_sum /-
@[simp, norm_cast]
theorem cast_sum [AddCommMonoidWithOne β] (s : Finset α) (f : α → ℕ) :
    ↑(∑ x in s, f x : ℕ) = ∑ x in s, (f x : β) :=
  map_sum (castAddMonoidHom β) _ _
#align nat.cast_sum Nat.cast_sum
-/

#print Nat.cast_prod /-
@[simp, norm_cast]
theorem cast_prod [CommSemiring β] (f : α → ℕ) (s : Finset α) :
    (↑(∏ i in s, f i) : β) = ∏ i in s, f i :=
  map_prod (castRingHom β) _ _
#align nat.cast_prod Nat.cast_prod
-/

end Nat

namespace Int

/- warning: int.cast_list_sum -> Int.cast_list_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} β] (s : List.{0} Int), Eq.{succ u1} β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int β (HasLiftT.mk.{1, succ u1} Int β (CoeTCₓ.coe.{1, succ u1} Int β (Int.castCoe.{u1} β (AddGroupWithOne.toHasIntCast.{u1} β _inst_1)))) (List.sum.{0} Int Int.hasAdd Int.hasZero s)) (List.sum.{u1} β (AddZeroClass.toHasAdd.{u1} β (AddMonoid.toAddZeroClass.{u1} β (AddMonoidWithOne.toAddMonoid.{u1} β (AddGroupWithOne.toAddMonoidWithOne.{u1} β _inst_1)))) (AddZeroClass.toHasZero.{u1} β (AddMonoid.toAddZeroClass.{u1} β (AddMonoidWithOne.toAddMonoid.{u1} β (AddGroupWithOne.toAddMonoidWithOne.{u1} β _inst_1)))) (List.map.{0, u1} Int β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int β (HasLiftT.mk.{1, succ u1} Int β (CoeTCₓ.coe.{1, succ u1} Int β (Int.castCoe.{u1} β (AddGroupWithOne.toHasIntCast.{u1} β _inst_1))))) s))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : AddGroupWithOne.{u1} β] (s : List.{0} Int), Eq.{succ u1} β (Int.cast.{u1} β (AddGroupWithOne.toIntCast.{u1} β _inst_1) (List.sum.{0} Int Int.instAddInt (CommMonoidWithZero.toZero.{0} Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.instCommSemiringInt)) s)) (List.sum.{u1} β (AddZeroClass.toAdd.{u1} β (AddMonoid.toAddZeroClass.{u1} β (AddMonoidWithOne.toAddMonoid.{u1} β (AddGroupWithOne.toAddMonoidWithOne.{u1} β _inst_1)))) (NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (AddGroup.toSubtractionMonoid.{u1} β (AddGroupWithOne.toAddGroup.{u1} β _inst_1))))) (List.map.{0, u1} Int β (Int.cast.{u1} β (AddGroupWithOne.toIntCast.{u1} β _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align int.cast_list_sum Int.cast_list_sumₓ'. -/
@[simp, norm_cast]
theorem cast_list_sum [AddGroupWithOne β] (s : List ℤ) : (↑s.Sum : β) = (s.map coe).Sum :=
  map_list_sum (castAddHom β) _
#align int.cast_list_sum Int.cast_list_sum

/- warning: int.cast_list_prod -> Int.cast_list_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : Ring.{u1} β] (s : List.{0} Int), Eq.{succ u1} β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int β (HasLiftT.mk.{1, succ u1} Int β (CoeTCₓ.coe.{1, succ u1} Int β (Int.castCoe.{u1} β (AddGroupWithOne.toHasIntCast.{u1} β (NonAssocRing.toAddGroupWithOne.{u1} β (Ring.toNonAssocRing.{u1} β _inst_1)))))) (List.prod.{0} Int Int.hasMul Int.hasOne s)) (List.prod.{u1} β (Distrib.toHasMul.{u1} β (Ring.toDistrib.{u1} β _inst_1)) (AddMonoidWithOne.toOne.{u1} β (AddGroupWithOne.toAddMonoidWithOne.{u1} β (NonAssocRing.toAddGroupWithOne.{u1} β (Ring.toNonAssocRing.{u1} β _inst_1)))) (List.map.{0, u1} Int β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int β (HasLiftT.mk.{1, succ u1} Int β (CoeTCₓ.coe.{1, succ u1} Int β (Int.castCoe.{u1} β (AddGroupWithOne.toHasIntCast.{u1} β (NonAssocRing.toAddGroupWithOne.{u1} β (Ring.toNonAssocRing.{u1} β _inst_1))))))) s))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : Ring.{u1} β] (s : List.{0} Int), Eq.{succ u1} β (Int.cast.{u1} β (Ring.toIntCast.{u1} β _inst_1) (List.prod.{0} Int Int.instMulInt (NonAssocRing.toOne.{0} Int (Ring.toNonAssocRing.{0} Int Int.instRingInt)) s)) (List.prod.{u1} β (NonUnitalNonAssocRing.toMul.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β _inst_1))) (NonAssocRing.toOne.{u1} β (Ring.toNonAssocRing.{u1} β _inst_1)) (List.map.{0, u1} Int β (Int.cast.{u1} β (Ring.toIntCast.{u1} β _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align int.cast_list_prod Int.cast_list_prodₓ'. -/
@[simp, norm_cast]
theorem cast_list_prod [Ring β] (s : List ℤ) : (↑s.Prod : β) = (s.map coe).Prod :=
  map_list_prod (castRingHom β) _
#align int.cast_list_prod Int.cast_list_prod

/- warning: int.cast_multiset_sum -> Int.cast_multiset_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : AddCommGroupWithOne.{u1} β] (s : Multiset.{0} Int), Eq.{succ u1} β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int β (HasLiftT.mk.{1, succ u1} Int β (CoeTCₓ.coe.{1, succ u1} Int β (Int.castCoe.{u1} β (AddGroupWithOne.toHasIntCast.{u1} β (AddCommGroupWithOne.toAddGroupWithOne.{u1} β _inst_1))))) (Multiset.sum.{0} Int Int.addCommMonoid s)) (Multiset.sum.{u1} β (AddCommGroup.toAddCommMonoid.{u1} β (AddCommGroupWithOne.toAddCommGroup.{u1} β _inst_1)) (Multiset.map.{0, u1} Int β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int β (HasLiftT.mk.{1, succ u1} Int β (CoeTCₓ.coe.{1, succ u1} Int β (Int.castCoe.{u1} β (AddGroupWithOne.toHasIntCast.{u1} β (AddCommGroupWithOne.toAddGroupWithOne.{u1} β _inst_1)))))) s))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : AddCommGroupWithOne.{u1} β] (s : Multiset.{0} Int), Eq.{succ u1} β (Int.cast.{u1} β (AddCommGroupWithOne.toIntCast.{u1} β _inst_1) (Multiset.sum.{0} Int Int.instAddCommMonoidInt s)) (Multiset.sum.{u1} β (AddCommGroup.toAddCommMonoid.{u1} β (AddCommGroupWithOne.toAddCommGroup.{u1} β _inst_1)) (Multiset.map.{0, u1} Int β (Int.cast.{u1} β (AddCommGroupWithOne.toIntCast.{u1} β _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align int.cast_multiset_sum Int.cast_multiset_sumₓ'. -/
@[simp, norm_cast]
theorem cast_multiset_sum [AddCommGroupWithOne β] (s : Multiset ℤ) :
    (↑s.Sum : β) = (s.map coe).Sum :=
  map_multiset_sum (castAddHom β) _
#align int.cast_multiset_sum Int.cast_multiset_sum

/- warning: int.cast_multiset_prod -> Int.cast_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (s : Multiset.{0} Int), Eq.{succ u1} R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) (Multiset.prod.{0} Int Int.commMonoid s)) (Multiset.prod.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) (Multiset.map.{0, u1} Int R ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int R (HasLiftT.mk.{1, succ u1} Int R (CoeTCₓ.coe.{1, succ u1} Int R (Int.castCoe.{u1} R (AddGroupWithOne.toHasIntCast.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) s))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (s : Multiset.{0} Int), Eq.{succ u1} R (Int.cast.{u1} R (Ring.toIntCast.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Multiset.prod.{0} Int Int.instCommMonoidInt s)) (Multiset.prod.{u1} R (CommRing.toCommMonoid.{u1} R _inst_1) (Multiset.map.{0, u1} Int R (Int.cast.{u1} R (Ring.toIntCast.{u1} R (CommRing.toRing.{u1} R _inst_1))) s))
Case conversion may be inaccurate. Consider using '#align int.cast_multiset_prod Int.cast_multiset_prodₓ'. -/
@[simp, norm_cast]
theorem cast_multiset_prod {R : Type _} [CommRing R] (s : Multiset ℤ) :
    (↑s.Prod : R) = (s.map coe).Prod :=
  map_multiset_prod (castRingHom R) _
#align int.cast_multiset_prod Int.cast_multiset_prod

/- warning: int.cast_sum -> Int.cast_sum is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddCommGroupWithOne.{u1} β] (s : Finset.{u2} α) (f : α -> Int), Eq.{succ u1} β ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int β (HasLiftT.mk.{1, succ u1} Int β (CoeTCₓ.coe.{1, succ u1} Int β (Int.castCoe.{u1} β (AddGroupWithOne.toHasIntCast.{u1} β (AddCommGroupWithOne.toAddGroupWithOne.{u1} β _inst_1))))) (Finset.sum.{0, u2} Int α Int.addCommMonoid s (fun (x : α) => f x))) (Finset.sum.{u1, u2} β α (AddCommGroup.toAddCommMonoid.{u1} β (AddCommGroupWithOne.toAddCommGroup.{u1} β _inst_1)) s (fun (x : α) => (fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int β (HasLiftT.mk.{1, succ u1} Int β (CoeTCₓ.coe.{1, succ u1} Int β (Int.castCoe.{u1} β (AddGroupWithOne.toHasIntCast.{u1} β (AddCommGroupWithOne.toAddGroupWithOne.{u1} β _inst_1))))) (f x)))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddCommGroupWithOne.{u1} β] (s : Finset.{u2} α) (f : α -> Int), Eq.{succ u1} β (Int.cast.{u1} β (AddCommGroupWithOne.toIntCast.{u1} β _inst_1) (Finset.sum.{0, u2} Int α Int.instAddCommMonoidInt s (fun (x : α) => f x))) (Finset.sum.{u1, u2} β α (AddCommGroup.toAddCommMonoid.{u1} β (AddCommGroupWithOne.toAddCommGroup.{u1} β _inst_1)) s (fun (x : α) => Int.cast.{u1} β (AddCommGroupWithOne.toIntCast.{u1} β _inst_1) (f x)))
Case conversion may be inaccurate. Consider using '#align int.cast_sum Int.cast_sumₓ'. -/
@[simp, norm_cast]
theorem cast_sum [AddCommGroupWithOne β] (s : Finset α) (f : α → ℤ) :
    ↑(∑ x in s, f x : ℤ) = ∑ x in s, (f x : β) :=
  map_sum (castAddHom β) _ _
#align int.cast_sum Int.cast_sum

/- warning: int.cast_prod -> Int.cast_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommRing.{u2} R] (f : α -> Int) (s : Finset.{u1} α), Eq.{succ u2} R ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int R (HasLiftT.mk.{1, succ u2} Int R (CoeTCₓ.coe.{1, succ u2} Int R (Int.castCoe.{u2} R (AddGroupWithOne.toHasIntCast.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_1))))))) (Finset.prod.{0, u1} Int α Int.commMonoid s (fun (i : α) => f i))) (Finset.prod.{u2, u1} R α (CommRing.toCommMonoid.{u2} R _inst_1) s (fun (i : α) => (fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int R (HasLiftT.mk.{1, succ u2} Int R (CoeTCₓ.coe.{1, succ u2} Int R (Int.castCoe.{u2} R (AddGroupWithOne.toHasIntCast.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_1))))))) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (f : α -> Int) (s : Finset.{u2} α), Eq.{succ u1} R (Int.cast.{u1} R (Ring.toIntCast.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Finset.prod.{0, u2} Int α Int.instCommMonoidInt s (fun (i : α) => f i))) (Finset.prod.{u1, u2} R α (CommRing.toCommMonoid.{u1} R _inst_1) s (fun (i : α) => Int.cast.{u1} R (Ring.toIntCast.{u1} R (CommRing.toRing.{u1} R _inst_1)) (f i)))
Case conversion may be inaccurate. Consider using '#align int.cast_prod Int.cast_prodₓ'. -/
@[simp, norm_cast]
theorem cast_prod {R : Type _} [CommRing R] (f : α → ℤ) (s : Finset α) :
    (↑(∏ i in s, f i) : R) = ∏ i in s, f i :=
  (Int.castRingHom R).map_prod _ _
#align int.cast_prod Int.cast_prod

end Int

/- warning: units.coe_prod -> Units.coe_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))) (s : Finset.{u1} α), Eq.{succ u2} M ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) M (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) M (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) M (coeBase.{succ u2, succ u2} (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) M (Units.hasCoe.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) (Finset.prod.{u2, u1} (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) α (CommGroup.toCommMonoid.{u2} (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) (Units.instCommGroupUnitsToMonoid.{u2} M _inst_1)) s (fun (i : α) => f i))) (Finset.prod.{u2, u1} M α _inst_1 s (fun (i : α) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) M (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) M (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) M (coeBase.{succ u2, succ u2} (Units.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)) M (Units.hasCoe.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1))))) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> (Units.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (s : Finset.{u2} α), Eq.{succ u1} M (Units.val.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1) (Finset.prod.{u1, u2} (Units.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) α (CommGroup.toCommMonoid.{u1} (Units.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) (Units.instCommGroupUnitsToMonoid.{u1} M _inst_1)) s (fun (i : α) => f i))) (Finset.prod.{u1, u2} M α _inst_1 s (fun (i : α) => Units.val.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1) (f i)))
Case conversion may be inaccurate. Consider using '#align units.coe_prod Units.coe_prodₓ'. -/
@[simp, norm_cast]
theorem Units.coe_prod {M : Type _} [CommMonoid M] (f : α → Mˣ) (s : Finset α) :
    (↑(∏ i in s, f i) : M) = ∏ i in s, f i :=
  (Units.coeHom M).map_prod _ _
#align units.coe_prod Units.coe_prod

/- warning: units.mk0_prod -> Units.mk0_prod is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommGroupWithZero.{u1} β] (s : Finset.{u2} α) (f : α -> β) (h : Ne.{succ u1} β (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β (CommGroupWithZero.toCommMonoidWithZero.{u1} β _inst_1)) s (fun (b : α) => f b)) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1))))))))), Eq.{succ u1} (Units.{u1} β (MonoidWithZero.toMonoid.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1)))) (Units.mk0.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1) (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β (CommGroupWithZero.toCommMonoidWithZero.{u1} β _inst_1)) s (fun (b : α) => f b)) h) (Finset.prod.{u1, u2} (Units.{u1} β (MonoidWithZero.toMonoid.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1)))) (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s)) (CommGroup.toCommMonoid.{u1} (Units.{u1} β (MonoidWithZero.toMonoid.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1)))) (Units.instCommGroupUnitsToMonoid.{u1} β (CommMonoidWithZero.toCommMonoid.{u1} β (CommGroupWithZero.toCommMonoidWithZero.{u1} β _inst_1)))) (Finset.attach.{u2} α s) (fun (b : Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s)) => Units.mk0.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1) (f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s)) α (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s)) α (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s)) α (coeBase.{succ u2, succ u2} (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s)) α (coeSubtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s))))) b)) (fun (hh : Eq.{succ u1} β (f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s)) α (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s)) α (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s)) α (coeBase.{succ u2, succ u2} (Subtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s)) α (coeSubtype.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s))))) b)) (OfNat.ofNat.{u1} β 0 (OfNat.mk.{u1} β 0 (Zero.zero.{u1} β (MulZeroClass.toHasZero.{u1} β (MulZeroOneClass.toMulZeroClass.{u1} β (MonoidWithZero.toMulZeroOneClass.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1))))))))) => h (Finset.prod_eq_zero.{u1, u2} β α s (Subtype.val.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s) b) (fun (b : α) => f b) (CommGroupWithZero.toCommMonoidWithZero.{u1} β _inst_1) (Subtype.property.{succ u2} α (fun (x : α) => Membership.Mem.{u2, u2} α (Finset.{u2} α) (Finset.hasMem.{u2} α) x s) b) hh))))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommGroupWithZero.{u1} β] (s : Finset.{u2} α) (f : α -> β) (h : Ne.{succ u1} β (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β (CommGroupWithZero.toCommMonoidWithZero.{u1} β _inst_1)) s (fun (b : α) => f b)) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1)))))), Eq.{succ u1} (Units.{u1} β (MonoidWithZero.toMonoid.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1)))) (Units.mk0.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1) (Finset.prod.{u1, u2} β α (CommMonoidWithZero.toCommMonoid.{u1} β (CommGroupWithZero.toCommMonoidWithZero.{u1} β _inst_1)) s (fun (b : α) => f b)) h) (Finset.prod.{u1, u2} (Units.{u1} β (MonoidWithZero.toMonoid.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1)))) (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)) (CommGroup.toCommMonoid.{u1} (Units.{u1} β (MonoidWithZero.toMonoid.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1)))) (Units.instCommGroupUnitsToMonoid.{u1} β (CommMonoidWithZero.toCommMonoid.{u1} β (CommGroupWithZero.toCommMonoidWithZero.{u1} β _inst_1)))) (Finset.attach.{u2} α s) (fun (b : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)) => Units.mk0.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1) (f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) b)) (fun (hh : Eq.{succ u1} β (f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) b)) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (MonoidWithZero.toZero.{u1} β (GroupWithZero.toMonoidWithZero.{u1} β (CommGroupWithZero.toGroupWithZero.{u1} β _inst_1)))))) => h (Finset.prod_eq_zero.{u1, u2} β α s (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) b) (fun (b : α) => f b) (CommGroupWithZero.toCommMonoidWithZero.{u1} β _inst_1) (Subtype.property.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) b) hh))))
Case conversion may be inaccurate. Consider using '#align units.mk0_prod Units.mk0_prodₓ'. -/
theorem Units.mk0_prod [CommGroupWithZero β] (s : Finset α) (f : α → β) (h) :
    Units.mk0 (∏ b in s, f b) h =
      ∏ b in s.attach, Units.mk0 (f b) fun hh => h (Finset.prod_eq_zero b.2 hh) :=
  by classical induction s using Finset.induction_on <;> simp [*]
#align units.mk0_prod Units.mk0_prod

/- warning: nat_abs_sum_le -> nat_abs_sum_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (s : Finset.{u1} ι) (f : ι -> Int), LE.le.{0} Nat Nat.hasLe (Int.natAbs (Finset.sum.{0, u1} Int ι Int.addCommMonoid s (fun (i : ι) => f i))) (Finset.sum.{0, u1} Nat ι Nat.addCommMonoid s (fun (i : ι) => Int.natAbs (f i)))
but is expected to have type
  forall {ι : Type.{u1}} (s : Finset.{u1} ι) (f : ι -> Int), LE.le.{0} Nat instLENat (Int.natAbs (Finset.sum.{0, u1} Int ι Int.instAddCommMonoidInt s (fun (i : ι) => f i))) (Finset.sum.{0, u1} Nat ι Nat.addCommMonoid s (fun (i : ι) => Int.natAbs (f i)))
Case conversion may be inaccurate. Consider using '#align nat_abs_sum_le nat_abs_sum_leₓ'. -/
theorem nat_abs_sum_le {ι : Type _} (s : Finset ι) (f : ι → ℤ) :
    (∑ i in s, f i).natAbs ≤ ∑ i in s, (f i).natAbs := by
  classical
    apply Finset.induction_on s
    · simp only [Finset.sum_empty, Int.natAbs_zero]
    · intro i s his IH
      simp only [his, Finset.sum_insert, not_false_iff]
      exact (Int.natAbs_add_le _ _).trans (add_le_add le_rfl IH)
#align nat_abs_sum_le nat_abs_sum_le

/-! ### `additive`, `multiplicative` -/


open Additive Multiplicative

section Monoid

variable [Monoid α]

#print ofMul_list_prod /-
@[simp]
theorem ofMul_list_prod (s : List α) : ofMul s.Prod = (s.map ofMul).Sum := by simpa [of_mul]
#align of_mul_list_prod ofMul_list_prod
-/

#print toMul_list_sum /-
@[simp]
theorem toMul_list_sum (s : List (Additive α)) : toMul s.Sum = (s.map toMul).Prod := by
  simpa [to_mul, of_mul]
#align to_mul_list_sum toMul_list_sum
-/

end Monoid

section AddMonoid

variable [AddMonoid α]

#print ofAdd_list_prod /-
@[simp]
theorem ofAdd_list_prod (s : List α) : ofAdd s.Sum = (s.map ofAdd).Prod := by simpa [of_add]
#align of_add_list_prod ofAdd_list_prod
-/

#print toAdd_list_sum /-
@[simp]
theorem toAdd_list_sum (s : List (Multiplicative α)) : toAdd s.Prod = (s.map toAdd).Sum := by
  simpa [to_add, of_add]
#align to_add_list_sum toAdd_list_sum
-/

end AddMonoid

section CommMonoid

variable [CommMonoid α]

#print ofMul_multiset_prod /-
@[simp]
theorem ofMul_multiset_prod (s : Multiset α) : ofMul s.Prod = (s.map ofMul).Sum := by simpa [of_mul]
#align of_mul_multiset_prod ofMul_multiset_prod
-/

#print toMul_multiset_sum /-
@[simp]
theorem toMul_multiset_sum (s : Multiset (Additive α)) : toMul s.Sum = (s.map toMul).Prod := by
  simpa [to_mul, of_mul]
#align to_mul_multiset_sum toMul_multiset_sum
-/

/- warning: of_mul_prod -> ofMul_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (s : Finset.{u2} ι) (f : ι -> α), Eq.{succ u1} (Additive.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Additive.{u1} α)) => α -> (Additive.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) (Finset.prod.{u1, u2} α ι _inst_1 s (fun (i : ι) => f i))) (Finset.sum.{u1, u2} (Additive.{u1} α) ι (Additive.addCommMonoid.{u1} α _inst_1) s (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Additive.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Additive.{u1} α)) => α -> (Additive.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Additive.{u1} α)) (Additive.ofMul.{u1} α) (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] (s : Finset.{u1} ι) (f : ι -> α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Additive.{u2} α) (Finset.prod.{u2, u1} α ι _inst_1 s (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Additive.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Additive.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Additive.{u2} α)) α (Additive.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Additive.{u2} α)) α (Additive.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (Additive.{u2} α)))) (Additive.ofMul.{u2} α) (Finset.prod.{u2, u1} α ι _inst_1 s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} (Additive.{u2} α) ι (Additive.addCommMonoid.{u2} α _inst_1) s (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Additive.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Additive.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Additive.{u2} α)) α (Additive.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Additive.{u2} α)) α (Additive.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (Additive.{u2} α)))) (Additive.ofMul.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align of_mul_prod ofMul_prodₓ'. -/
@[simp]
theorem ofMul_prod (s : Finset ι) (f : ι → α) : ofMul (∏ i in s, f i) = ∑ i in s, ofMul (f i) :=
  rfl
#align of_mul_prod ofMul_prod

/- warning: to_mul_sum -> toMul_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (s : Finset.{u2} ι) (f : ι -> (Additive.{u1} α)), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Additive.{u1} α) α) => (Additive.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) (Finset.sum.{u1, u2} (Additive.{u1} α) ι (Additive.addCommMonoid.{u1} α _inst_1) s (fun (i : ι) => f i))) (Finset.prod.{u1, u2} α ι _inst_1 s (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Additive.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Additive.{u1} α) α) => (Additive.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Additive.{u1} α) α) (Additive.toMul.{u1} α) (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] (s : Finset.{u1} ι) (f : ι -> (Additive.{u2} α)), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Additive.{u2} α) => α) (Finset.sum.{u2, u1} (Additive.{u2} α) ι (Additive.addCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Additive.{u2} α) α) (Additive.{u2} α) (fun (_x : Additive.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Additive.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Additive.{u2} α) α) (Additive.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Additive.{u2} α) α) (Additive.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (Additive.{u2} α) α))) (Additive.toMul.{u2} α) (Finset.sum.{u2, u1} (Additive.{u2} α) ι (Additive.addCommMonoid.{u2} α _inst_1) s (fun (i : ι) => f i))) (Finset.prod.{u2, u1} α ι _inst_1 s (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Additive.{u2} α) α) (Additive.{u2} α) (fun (_x : Additive.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Additive.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Additive.{u2} α) α) (Additive.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Additive.{u2} α) α) (Additive.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (Additive.{u2} α) α))) (Additive.toMul.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align to_mul_sum toMul_sumₓ'. -/
@[simp]
theorem toMul_sum (s : Finset ι) (f : ι → Additive α) :
    toMul (∑ i in s, f i) = ∏ i in s, toMul (f i) :=
  rfl
#align to_mul_sum toMul_sum

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid α]

#print ofAdd_multiset_prod /-
@[simp]
theorem ofAdd_multiset_prod (s : Multiset α) : ofAdd s.Sum = (s.map ofAdd).Prod := by simpa [of_add]
#align of_add_multiset_prod ofAdd_multiset_prod
-/

#print toAdd_multiset_sum /-
@[simp]
theorem toAdd_multiset_sum (s : Multiset (Multiplicative α)) : toAdd s.Prod = (s.map toAdd).Sum :=
  by simpa [to_add, of_add]
#align to_add_multiset_sum toAdd_multiset_sum
-/

/- warning: of_add_sum -> ofAdd_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] (s : Finset.{u2} ι) (f : ι -> α), Eq.{succ u1} (Multiplicative.{u1} α) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) => α -> (Multiplicative.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) (Finset.sum.{u1, u2} α ι _inst_1 s (fun (i : ι) => f i))) (Finset.prod.{u1, u2} (Multiplicative.{u1} α) ι (Multiplicative.commMonoid.{u1} α _inst_1) s (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (Multiplicative.{u1} α)) => α -> (Multiplicative.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (Multiplicative.{u1} α)) (Multiplicative.ofAdd.{u1} α) (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} α] (s : Finset.{u1} ι) (f : ι -> α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Multiplicative.{u2} α) (Finset.sum.{u2, u1} α ι _inst_1 s (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Multiplicative.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Multiplicative.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Multiplicative.{u2} α)) α (Multiplicative.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Multiplicative.{u2} α)) α (Multiplicative.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (Multiplicative.{u2} α)))) (Multiplicative.ofAdd.{u2} α) (Finset.sum.{u2, u1} α ι _inst_1 s (fun (i : ι) => f i))) (Finset.prod.{u2, u1} (Multiplicative.{u2} α) ι (Multiplicative.commMonoid.{u2} α _inst_1) s (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Multiplicative.{u2} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Multiplicative.{u2} α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Multiplicative.{u2} α)) α (Multiplicative.{u2} α) (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} α (Multiplicative.{u2} α)) α (Multiplicative.{u2} α) (Equiv.instEquivLikeEquiv.{succ u2, succ u2} α (Multiplicative.{u2} α)))) (Multiplicative.ofAdd.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align of_add_sum ofAdd_sumₓ'. -/
@[simp]
theorem ofAdd_sum (s : Finset ι) (f : ι → α) : ofAdd (∑ i in s, f i) = ∏ i in s, ofAdd (f i) :=
  rfl
#align of_add_sum ofAdd_sum

/- warning: to_add_prod -> toAdd_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} α] (s : Finset.{u2} ι) (f : ι -> (Multiplicative.{u1} α)), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) => (Multiplicative.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) (Finset.prod.{u1, u2} (Multiplicative.{u1} α) ι (Multiplicative.commMonoid.{u1} α _inst_1) s (fun (i : ι) => f i))) (Finset.sum.{u1, u2} α ι _inst_1 s (fun (i : ι) => coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (Multiplicative.{u1} α) α) => (Multiplicative.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (Multiplicative.{u1} α) α) (Multiplicative.toAdd.{u1} α) (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} α] (s : Finset.{u1} ι) (f : ι -> (Multiplicative.{u2} α)), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Multiplicative.{u2} α) => α) (Finset.prod.{u2, u1} (Multiplicative.{u2} α) ι (Multiplicative.commMonoid.{u2} α _inst_1) s (fun (i : ι) => f i))) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Multiplicative.{u2} α) α) (Multiplicative.{u2} α) (fun (_x : Multiplicative.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Multiplicative.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Multiplicative.{u2} α) α) (Multiplicative.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Multiplicative.{u2} α) α) (Multiplicative.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (Multiplicative.{u2} α) α))) (Multiplicative.toAdd.{u2} α) (Finset.prod.{u2, u1} (Multiplicative.{u2} α) ι (Multiplicative.commMonoid.{u2} α _inst_1) s (fun (i : ι) => f i))) (Finset.sum.{u2, u1} α ι _inst_1 s (fun (i : ι) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Multiplicative.{u2} α) α) (Multiplicative.{u2} α) (fun (_x : Multiplicative.{u2} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Multiplicative.{u2} α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Multiplicative.{u2} α) α) (Multiplicative.{u2} α) α (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Multiplicative.{u2} α) α) (Multiplicative.{u2} α) α (Equiv.instEquivLikeEquiv.{succ u2, succ u2} (Multiplicative.{u2} α) α))) (Multiplicative.toAdd.{u2} α) (f i)))
Case conversion may be inaccurate. Consider using '#align to_add_prod toAdd_prodₓ'. -/
@[simp]
theorem toAdd_prod (s : Finset ι) (f : ι → Multiplicative α) :
    toAdd (∏ i in s, f i) = ∑ i in s, toAdd (f i) :=
  rfl
#align to_add_prod toAdd_prod

end AddCommMonoid

