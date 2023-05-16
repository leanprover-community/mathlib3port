/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module algebra.big_operators.option
! leanprover-community/mathlib commit 327c3c0d9232d80e250dc8f65e7835b82b266ea5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Finset.Option

/-!
# Lemmas about products and sums over finite sets in `option α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove formulas for products and sums over `finset.insert_none s` and
`finset.erase_none s`.
-/


open BigOperators

open Function

namespace Finset

variable {α M : Type _} [CommMonoid M]

/- warning: finset.prod_insert_none -> Finset.prod_insertNone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : (Option.{u1} α) -> M) (s : Finset.{u1} α), Eq.{succ u2} M (Finset.prod.{u2, u1} M (Option.{u1} α) _inst_1 (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Preorder.toHasLe.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Preorder.toHasLe.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))))) (fun (_x : RelEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toHasLe.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toHasLe.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) => (Finset.{u1} α) -> (Finset.{u1} (Option.{u1} α))) (RelEmbedding.hasCoeToFun.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toHasLe.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toHasLe.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) (Finset.insertNone.{u1} α) s) (fun (x : Option.{u1} α) => f x)) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))) (f (Option.none.{u1} α)) (Finset.prod.{u2, u1} M α _inst_1 s (fun (x : α) => f (Option.some.{u1} α x))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : (Option.{u2} α) -> M) (s : Finset.{u2} α), Eq.{succ u1} M (Finset.prod.{u1, u2} M (Option.{u2} α) _inst_1 (FunLike.coe.{succ u2, succ u2, succ u2} (OrderEmbedding.{u2, u2} (Finset.{u2} α) (Finset.{u2} (Option.{u2} α)) (Preorder.toLE.{u2} (Finset.{u2} α) (PartialOrder.toPreorder.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α))) (Preorder.toLE.{u2} (Finset.{u2} (Option.{u2} α)) (PartialOrder.toPreorder.{u2} (Finset.{u2} (Option.{u2} α)) (Finset.partialOrder.{u2} (Option.{u2} α))))) (Finset.{u2} α) (fun (_x : Finset.{u2} α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Finset.{u2} α) => Finset.{u2} (Option.{u2} α)) _x) (RelHomClass.toFunLike.{u2, u2, u2} (OrderEmbedding.{u2, u2} (Finset.{u2} α) (Finset.{u2} (Option.{u2} α)) (Preorder.toLE.{u2} (Finset.{u2} α) (PartialOrder.toPreorder.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α))) (Preorder.toLE.{u2} (Finset.{u2} (Option.{u2} α)) (PartialOrder.toPreorder.{u2} (Finset.{u2} (Option.{u2} α)) (Finset.partialOrder.{u2} (Option.{u2} α))))) (Finset.{u2} α) (Finset.{u2} (Option.{u2} α)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u2} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u2} α) => LE.le.{u2} (Finset.{u2} α) (Preorder.toLE.{u2} (Finset.{u2} α) (PartialOrder.toPreorder.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Finset.{u2} (Option.{u2} α)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Finset.{u2} (Option.{u2} α)) => LE.le.{u2} (Finset.{u2} (Option.{u2} α)) (Preorder.toLE.{u2} (Finset.{u2} (Option.{u2} α)) (PartialOrder.toPreorder.{u2} (Finset.{u2} (Option.{u2} α)) (Finset.partialOrder.{u2} (Option.{u2} α)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{u2, u2} (Finset.{u2} α) (Finset.{u2} (Option.{u2} α)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u2} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u2} α) => LE.le.{u2} (Finset.{u2} α) (Preorder.toLE.{u2} (Finset.{u2} α) (PartialOrder.toPreorder.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Finset.{u2} (Option.{u2} α)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Finset.{u2} (Option.{u2} α)) => LE.le.{u2} (Finset.{u2} (Option.{u2} α)) (Preorder.toLE.{u2} (Finset.{u2} (Option.{u2} α)) (PartialOrder.toPreorder.{u2} (Finset.{u2} (Option.{u2} α)) (Finset.partialOrder.{u2} (Option.{u2} α)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (Finset.insertNone.{u2} α) s) (fun (x : Option.{u2} α) => f x)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f (Option.none.{u2} α)) (Finset.prod.{u1, u2} M α _inst_1 s (fun (x : α) => f (Option.some.{u2} α x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_insert_none Finset.prod_insertNoneₓ'. -/
@[simp, to_additive]
theorem prod_insertNone (f : Option α → M) (s : Finset α) :
    (∏ x in s.insertNone, f x) = f none * ∏ x in s, f (some x) := by simp [insert_none]
#align finset.prod_insert_none Finset.prod_insertNone
#align finset.sum_insert_none Finset.sum_insertNone

/- warning: finset.prod_erase_none -> Finset.prod_eraseNone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoid.{u2} M] (f : α -> M) (s : Finset.{u1} (Option.{u1} α)), Eq.{succ u2} M (Finset.prod.{u2, u1} M α _inst_1 (coeFn.{succ u1, succ u1} (OrderHom.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (fun (_x : OrderHom.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) => (Finset.{u1} (Option.{u1} α)) -> (Finset.{u1} α)) (OrderHom.hasCoeToFun.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.eraseNone.{u1} α) s) (fun (x : α) => f x)) (Finset.prod.{u2, u1} M (Option.{u1} α) _inst_1 s (fun (x : Option.{u1} α) => Option.elim'.{u1, u2} α M (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))))) f x))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] (f : α -> M) (s : Finset.{u2} (Option.{u2} α)), Eq.{succ u1} M (Finset.prod.{u1, u2} M α _inst_1 (OrderHom.toFun.{u2, u2} (Finset.{u2} (Option.{u2} α)) (Finset.{u2} α) (PartialOrder.toPreorder.{u2} (Finset.{u2} (Option.{u2} α)) (Finset.partialOrder.{u2} (Option.{u2} α))) (PartialOrder.toPreorder.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α)) (Finset.eraseNone.{u2} α) s) (fun (x : α) => f x)) (Finset.prod.{u1, u2} M (Option.{u2} α) _inst_1 s (fun (x : Option.{u2} α) => Option.elim'.{u2, u1} α M (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) f x))
Case conversion may be inaccurate. Consider using '#align finset.prod_erase_none Finset.prod_eraseNoneₓ'. -/
@[to_additive]
theorem prod_eraseNone (f : α → M) (s : Finset (Option α)) :
    (∏ x in s.eraseNone, f x) = ∏ x in s, Option.elim' 1 f x := by
  classical calc
      (∏ x in s.erase_none, f x) = ∏ x in s.erase_none.map embedding.some, Option.elim' 1 f x :=
        (Prod_map s.erase_none embedding.some <| Option.elim' 1 f).symm
      _ = ∏ x in s.erase none, Option.elim' 1 f x := by rw [map_some_erase_none]
      _ = ∏ x in s, Option.elim' 1 f x := prod_erase _ rfl
      
#align finset.prod_erase_none Finset.prod_eraseNone
#align finset.sum_erase_none Finset.sum_eraseNone

end Finset

