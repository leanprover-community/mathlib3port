/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module algebra.order.sub.basic
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Ring.Basic
import Mathbin.Algebra.Order.Sub.Defs

/-!
# Additional results about ordered Subtraction

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α β : Type _}

section Add

variable [Preorder α] [Add α] [Sub α] [OrderedSub α] {a b c d : α}

#print AddHom.le_map_tsub /-
theorem AddHom.le_map_tsub [Preorder β] [Add β] [Sub β] [OrderedSub β] (f : AddHom α β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) :=
  by
  rw [tsub_le_iff_right, ← f.map_add]
  exact hf le_tsub_add
#align add_hom.le_map_tsub AddHom.le_map_tsub
-/

/- warning: le_mul_tsub -> le_mul_tsub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_5 : Distrib.{u1} R] [_inst_6 : Preorder.{u1} R] [_inst_7 : Sub.{u1} R] [_inst_8 : OrderedSub.{u1} R (Preorder.toLE.{u1} R _inst_6) (Distrib.toHasAdd.{u1} R _inst_5) _inst_7] [_inst_9 : CovariantClass.{u1, u1} R R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R _inst_5))) (LE.le.{u1} R (Preorder.toLE.{u1} R _inst_6))] {a : R} {b : R} {c : R}, LE.le.{u1} R (Preorder.toLE.{u1} R _inst_6) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R _inst_7) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R _inst_5)) a b) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R _inst_5)) a c)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R _inst_5)) a (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R _inst_7) b c))
but is expected to have type
  forall {R : Type.{u1}} [_inst_5 : Distrib.{u1} R] [_inst_6 : Preorder.{u1} R] [_inst_7 : Sub.{u1} R] [_inst_8 : OrderedSub.{u1} R (Preorder.toLE.{u1} R _inst_6) (Distrib.toAdd.{u1} R _inst_5) _inst_7] [_inst_9 : CovariantClass.{u1, u1} R R (fun (x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.170 : R) (x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.172 : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toMul.{u1} R _inst_5)) x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.170 x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.172) (fun (x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.185 : R) (x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.187 : R) => LE.le.{u1} R (Preorder.toLE.{u1} R _inst_6) x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.185 x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.187)] {a : R} {b : R} {c : R}, LE.le.{u1} R (Preorder.toLE.{u1} R _inst_6) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R _inst_7) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toMul.{u1} R _inst_5)) a b) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toMul.{u1} R _inst_5)) a c)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toMul.{u1} R _inst_5)) a (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R _inst_7) b c))
Case conversion may be inaccurate. Consider using '#align le_mul_tsub le_mul_tsubₓ'. -/
theorem le_mul_tsub {R : Type _} [Distrib R] [Preorder R] [Sub R] [OrderedSub R]
    [CovariantClass R R (· * ·) (· ≤ ·)] {a b c : R} : a * b - a * c ≤ a * (b - c) :=
  (AddHom.mulLeft a).le_map_tsub (monotone_id.const_mul' a) _ _
#align le_mul_tsub le_mul_tsub

/- warning: le_tsub_mul -> le_tsub_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_5 : CommSemiring.{u1} R] [_inst_6 : Preorder.{u1} R] [_inst_7 : Sub.{u1} R] [_inst_8 : OrderedSub.{u1} R (Preorder.toLE.{u1} R _inst_6) (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_5))))) _inst_7] [_inst_9 : CovariantClass.{u1, u1} R R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_5))))))) (LE.le.{u1} R (Preorder.toLE.{u1} R _inst_6))] {a : R} {b : R} {c : R}, LE.le.{u1} R (Preorder.toLE.{u1} R _inst_6) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R _inst_7) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_5)))))) a c) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_5)))))) b c)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_5)))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R _inst_7) a b) c)
but is expected to have type
  forall {R : Type.{u1}} [_inst_5 : CommSemiring.{u1} R] [_inst_6 : Preorder.{u1} R] [_inst_7 : Sub.{u1} R] [_inst_8 : OrderedSub.{u1} R (Preorder.toLE.{u1} R _inst_6) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_5))))) _inst_7] [_inst_9 : CovariantClass.{u1, u1} R R (fun (x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.266 : R) (x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.268 : R) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_5))))) x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.266 x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.268) (fun (x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.281 : R) (x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.283 : R) => LE.le.{u1} R (Preorder.toLE.{u1} R _inst_6) x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.281 x._@.Mathlib.Algebra.Order.Sub.Basic._hyg.283)] {a : R} {b : R} {c : R}, LE.le.{u1} R (Preorder.toLE.{u1} R _inst_6) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R _inst_7) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_5))))) a c) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_5))))) b c)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_5))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R _inst_7) a b) c)
Case conversion may be inaccurate. Consider using '#align le_tsub_mul le_tsub_mulₓ'. -/
theorem le_tsub_mul {R : Type _} [CommSemiring R] [Preorder R] [Sub R] [OrderedSub R]
    [CovariantClass R R (· * ·) (· ≤ ·)] {a b c : R} : a * c - b * c ≤ (a - b) * c := by
  simpa only [mul_comm _ c] using le_mul_tsub
#align le_tsub_mul le_tsub_mul

end Add

/- warning: order_iso.map_tsub -> OrderIso.map_tsub is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Preorder.{u1} M] [_inst_2 : Add.{u1} M] [_inst_3 : Sub.{u1} M] [_inst_4 : OrderedSub.{u1} M (Preorder.toLE.{u1} M _inst_1) _inst_2 _inst_3] [_inst_5 : PartialOrder.{u2} N] [_inst_6 : Add.{u2} N] [_inst_7 : Sub.{u2} N] [_inst_8 : OrderedSub.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)) _inst_6 _inst_7] (e : OrderIso.{u1, u2} M N (Preorder.toLE.{u1} M _inst_1) (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5))), (forall (a : M) (b : M), Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} M N (Preorder.toLE.{u1} M _inst_1) (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5))) (fun (_x : RelIso.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) => M -> N) (RelIso.hasCoeToFun.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) e (HAdd.hAdd.{u1, u1, u1} M M M (instHAdd.{u1} M _inst_2) a b)) (HAdd.hAdd.{u2, u2, u2} N N N (instHAdd.{u2} N _inst_6) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} M N (Preorder.toLE.{u1} M _inst_1) (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5))) (fun (_x : RelIso.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) => M -> N) (RelIso.hasCoeToFun.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) e a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} M N (Preorder.toLE.{u1} M _inst_1) (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5))) (fun (_x : RelIso.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) => M -> N) (RelIso.hasCoeToFun.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) e b))) -> (forall (a : M) (b : M), Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} M N (Preorder.toLE.{u1} M _inst_1) (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5))) (fun (_x : RelIso.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) => M -> N) (RelIso.hasCoeToFun.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) e (HSub.hSub.{u1, u1, u1} M M M (instHSub.{u1} M _inst_3) a b)) (HSub.hSub.{u2, u2, u2} N N N (instHSub.{u2} N _inst_7) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} M N (Preorder.toLE.{u1} M _inst_1) (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5))) (fun (_x : RelIso.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) => M -> N) (RelIso.hasCoeToFun.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) e a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} M N (Preorder.toLE.{u1} M _inst_1) (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5))) (fun (_x : RelIso.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) => M -> N) (RelIso.hasCoeToFun.{u1, u2} M N (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_1)) (LE.le.{u2} N (Preorder.toLE.{u2} N (PartialOrder.toPreorder.{u2} N _inst_5)))) e b)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Preorder.{u2} M] [_inst_2 : Add.{u2} M] [_inst_3 : Sub.{u2} M] [_inst_4 : OrderedSub.{u2} M (Preorder.toLE.{u2} M _inst_1) _inst_2 _inst_3] [_inst_5 : PartialOrder.{u1} N] [_inst_6 : Add.{u1} N] [_inst_7 : Sub.{u1} N] [_inst_8 : OrderedSub.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) _inst_6 _inst_7] (e : OrderIso.{u2, u1} M N (Preorder.toLE.{u2} M _inst_1) (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5))), (forall (a : M) (b : M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M _inst_2) a b)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M N (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} M N)) (RelEmbedding.toEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e)) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M _inst_2) a b)) (HAdd.hAdd.{u1, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) b) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (instHAdd.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) _inst_6) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M N (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} M N)) (RelEmbedding.toEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e)) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M N (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} M N)) (RelEmbedding.toEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e)) b))) -> (forall (a : M) (b : M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M _inst_3) a b)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M N (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} M N)) (RelEmbedding.toEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e)) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M _inst_3) a b)) (HSub.hSub.{u1, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) b) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (instHSub.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) _inst_7) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M N (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} M N)) (RelEmbedding.toEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e)) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} M N) M N (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} M N)) (RelEmbedding.toEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} M N (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : M) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : M) => LE.le.{u2} M (Preorder.toLE.{u2} M _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : N) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : N) => LE.le.{u1} N (Preorder.toLE.{u1} N (PartialOrder.toPreorder.{u1} N _inst_5)) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) e)) b)))
Case conversion may be inaccurate. Consider using '#align order_iso.map_tsub OrderIso.map_tsubₓ'. -/
/-- An order isomorphism between types with ordered subtraction preserves subtraction provided that
it preserves addition. -/
theorem OrderIso.map_tsub {M N : Type _} [Preorder M] [Add M] [Sub M] [OrderedSub M]
    [PartialOrder N] [Add N] [Sub N] [OrderedSub N] (e : M ≃o N)
    (h_add : ∀ a b, e (a + b) = e a + e b) (a b : M) : e (a - b) = e a - e b :=
  by
  set e_add : M ≃+ N := { e with map_add' := h_add }
  refine' le_antisymm _ (e_add.to_add_hom.le_map_tsub e.monotone a b)
  suffices e (e.symm (e a) - e.symm (e b)) ≤ e (e.symm (e a - e b)) by simpa
  exact e.monotone (e_add.symm.to_add_hom.le_map_tsub e.symm.monotone _ _)
#align order_iso.map_tsub OrderIso.map_tsub

/-! ### Preorder -/


section Preorder

variable [Preorder α]

variable [AddCommMonoid α] [Sub α] [OrderedSub α] {a b c d : α}

/- warning: add_monoid_hom.le_map_tsub -> AddMonoidHom.le_map_tsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) _inst_3] [_inst_5 : Preorder.{u2} β] [_inst_6 : AddCommMonoid.{u2} β] [_inst_7 : Sub.{u2} β] [_inst_8 : OrderedSub.{u2} β (Preorder.toLE.{u2} β _inst_5) (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) _inst_7] (f : AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))), (Monotone.{u1, u2} α β _inst_1 _inst_5 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) (fun (_x : AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) => α -> β) (AddMonoidHom.hasCoeToFun.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) f)) -> (forall (a : α) (b : α), LE.le.{u2} β (Preorder.toLE.{u2} β _inst_5) (HSub.hSub.{u2, u2, u2} β β β (instHSub.{u2} β _inst_7) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) (fun (_x : AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) => α -> β) (AddMonoidHom.hasCoeToFun.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) f a) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) (fun (_x : AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) => α -> β) (AddMonoidHom.hasCoeToFun.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) f b)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) (fun (_x : AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) => α -> β) (AddMonoidHom.hasCoeToFun.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) f (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : AddCommMonoid.{u1} α] [_inst_3 : Sub.{u1} α] [_inst_4 : OrderedSub.{u1} α (Preorder.toLE.{u1} α _inst_1) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) _inst_3] [_inst_5 : Preorder.{u2} β] [_inst_6 : AddCommMonoid.{u2} β] [_inst_7 : Sub.{u2} β] [_inst_8 : OrderedSub.{u2} β (Preorder.toLE.{u2} β _inst_5) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) _inst_7] (f : AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))), (Monotone.{u1, u2} α β _inst_1 _inst_5 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α β (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) (AddMonoidHomClass.toAddHomClass.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6)) (AddMonoidHom.addMonoidHomClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))))) f)) -> (forall (a : α) (b : α), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) a) (Preorder.toLE.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) a) _inst_5) (HSub.hSub.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) a) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) b) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) a) (instHSub.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) a) _inst_7) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α β (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) (AddMonoidHomClass.toAddHomClass.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6)) (AddMonoidHom.addMonoidHomClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))))) f a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α β (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) (AddMonoidHomClass.toAddHomClass.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6)) (AddMonoidHom.addMonoidHomClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))))) f b)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.398 : α) => β) _x) (AddHomClass.toFunLike.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α β (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2))) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) (AddMonoidHomClass.toAddHomClass.{max u1 u2, u1, u2} (AddMonoidHom.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))) α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6)) (AddMonoidHom.addMonoidHomClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u1} α (AddCommMonoid.toAddMonoid.{u1} α _inst_2)) (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β _inst_6))))) f (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_3) a b)))
Case conversion may be inaccurate. Consider using '#align add_monoid_hom.le_map_tsub AddMonoidHom.le_map_tsubₓ'. -/
theorem AddMonoidHom.le_map_tsub [Preorder β] [AddCommMonoid β] [Sub β] [OrderedSub β] (f : α →+ β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) :=
  f.toAddHom.le_map_tsub hf a b
#align add_monoid_hom.le_map_tsub AddMonoidHom.le_map_tsub

end Preorder

