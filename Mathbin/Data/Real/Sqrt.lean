/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Yury Kudryashov

! This file was ported from Lean 3 source module data.real.sqrt
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Order.MonotoneContinuity
import Mathbin.Topology.Instances.Nnreal
import Mathbin.Tactic.Positivity

/-!
# Square root of a real number

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define

* `nnreal.sqrt` to be the square root of a nonnegative real number.
* `real.sqrt` to be the square root of a real number, defined to be zero on negative numbers.

Then we prove some basic properties of these functions.

## Implementation notes

We define `nnreal.sqrt` as the noncomputable inverse to the function `x ↦ x * x`. We use general
theory of inverses of strictly monotone functions to prove that `nnreal.sqrt x` exists. As a side
effect, `nnreal.sqrt` is a bundled `order_iso`, so for `nnreal` numbers we get continuity as well as
theorems like `sqrt x ≤ y ↔ x ≤ y * y` for free.

Then we define `real.sqrt x` to be `nnreal.sqrt (real.to_nnreal x)`. We also define a Cauchy
sequence `real.sqrt_aux (f : cau_seq ℚ abs)` which converges to `sqrt (mk f)` but do not prove (yet)
that this sequence actually converges to `sqrt (mk f)`.

## Tags

square root
-/


open Set Filter

open Filter NNReal Topology

namespace NNReal

variable {x y : ℝ≥0}

#print NNReal.sqrt /-
/-- Square root of a nonnegative real number. -/
@[pp_nodot]
noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
  OrderIso.symm <| powOrderIso 2 two_ne_zero
#align nnreal.sqrt NNReal.sqrt
-/

/- warning: nnreal.sqrt_le_sqrt_iff -> NNReal.sqrt_le_sqrt_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal}, Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt y)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x y)
but is expected to have type
  forall {x : NNReal} {y : NNReal}, Iff (LE.le.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (Preorder.toLE.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (PartialOrder.toPreorder.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (StrictOrderedSemiring.toPartialOrder.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) instNNRealStrictOrderedSemiring))) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) y)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x y)
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_le_sqrt_iff NNReal.sqrt_le_sqrt_iffₓ'. -/
theorem sqrt_le_sqrt_iff : sqrt x ≤ sqrt y ↔ x ≤ y :=
  sqrt.le_iff_le
#align nnreal.sqrt_le_sqrt_iff NNReal.sqrt_le_sqrt_iff

/- warning: nnreal.sqrt_lt_sqrt_iff -> NNReal.sqrt_lt_sqrt_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal}, Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt y)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x y)
but is expected to have type
  forall {x : NNReal} {y : NNReal}, Iff (LT.lt.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (Preorder.toLT.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (PartialOrder.toPreorder.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (StrictOrderedSemiring.toPartialOrder.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) instNNRealStrictOrderedSemiring))) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) y)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x y)
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_lt_sqrt_iff NNReal.sqrt_lt_sqrt_iffₓ'. -/
theorem sqrt_lt_sqrt_iff : sqrt x < sqrt y ↔ x < y :=
  sqrt.lt_iff_lt
#align nnreal.sqrt_lt_sqrt_iff NNReal.sqrt_lt_sqrt_iff

/- warning: nnreal.sqrt_eq_iff_sq_eq -> NNReal.sqrt_eq_iff_sq_eq is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal}, Iff (Eq.{1} NNReal (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x) y) (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) x)
but is expected to have type
  forall {x : NNReal} {y : NNReal}, Iff (Eq.{1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x) y) (Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) x)
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_eq_iff_sq_eq NNReal.sqrt_eq_iff_sq_eqₓ'. -/
theorem sqrt_eq_iff_sq_eq : sqrt x = y ↔ y ^ 2 = x :=
  sqrt.toEquiv.apply_eq_iff_eq_symm_apply.trans eq_comm
#align nnreal.sqrt_eq_iff_sq_eq NNReal.sqrt_eq_iff_sq_eq

/- warning: nnreal.sqrt_le_iff -> NNReal.sqrt_le_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal}, Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x) y) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {x : NNReal} {y : NNReal}, Iff (LE.le.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (Preorder.toLE.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (PartialOrder.toPreorder.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (StrictOrderedSemiring.toPartialOrder.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) instNNRealStrictOrderedSemiring))) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x) y) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_le_iff NNReal.sqrt_le_iffₓ'. -/
theorem sqrt_le_iff : sqrt x ≤ y ↔ x ≤ y ^ 2 :=
  sqrt.to_galoisConnection _ _
#align nnreal.sqrt_le_iff NNReal.sqrt_le_iff

/- warning: nnreal.le_sqrt_iff -> NNReal.le_sqrt_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal}, Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt y)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y)
but is expected to have type
  forall {x : NNReal} {y : NNReal}, Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) y)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y)
Case conversion may be inaccurate. Consider using '#align nnreal.le_sqrt_iff NNReal.le_sqrt_iffₓ'. -/
theorem le_sqrt_iff : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
  (sqrt.symm.to_galoisConnection _ _).symm
#align nnreal.le_sqrt_iff NNReal.le_sqrt_iff

/- warning: nnreal.sqrt_eq_zero -> NNReal.sqrt_eq_zero is a dubious translation:
lean 3 declaration is
  forall {x : NNReal}, Iff (Eq.{1} NNReal (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (Eq.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {x : NNReal}, Iff (Eq.{1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) instNNRealZero))) (Eq.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)))
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_eq_zero NNReal.sqrt_eq_zeroₓ'. -/
@[simp]
theorem sqrt_eq_zero : sqrt x = 0 ↔ x = 0 :=
  sqrt_eq_iff_sq_eq.trans <| by rw [eq_comm, sq, MulZeroClass.zero_mul]
#align nnreal.sqrt_eq_zero NNReal.sqrt_eq_zero

/- warning: nnreal.sqrt_zero -> NNReal.sqrt_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} NNReal (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  Eq.{1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) instNNRealZero))
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_zero NNReal.sqrt_zeroₓ'. -/
@[simp]
theorem sqrt_zero : sqrt 0 = 0 :=
  sqrt_eq_zero.2 rfl
#align nnreal.sqrt_zero NNReal.sqrt_zero

/- warning: nnreal.sqrt_one -> NNReal.sqrt_one is a dubious translation:
lean 3 declaration is
  Eq.{1} NNReal (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  Eq.{1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) 1 (One.toOfNat1.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) instNNRealOne))
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_one NNReal.sqrt_oneₓ'. -/
@[simp]
theorem sqrt_one : sqrt 1 = 1 :=
  sqrt_eq_iff_sq_eq.2 <| one_pow _
#align nnreal.sqrt_one NNReal.sqrt_one

/- warning: nnreal.sq_sqrt -> NNReal.sq_sqrt is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} NNReal (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) x
but is expected to have type
  forall (x : NNReal), Eq.{1} NNReal (HPow.hPow.{0, 0, 0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) Nat NNReal (instHPow.{0, 0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) Nat (Monoid.Pow.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (MonoidWithZero.toMonoid.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (Semiring.toMonoidWithZero.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) instNNRealSemiring)))) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) x
Case conversion may be inaccurate. Consider using '#align nnreal.sq_sqrt NNReal.sq_sqrtₓ'. -/
@[simp]
theorem sq_sqrt (x : ℝ≥0) : sqrt x ^ 2 = x :=
  sqrt.symm_apply_apply x
#align nnreal.sq_sqrt NNReal.sq_sqrt

/- warning: nnreal.mul_self_sqrt -> NNReal.mul_self_sqrt is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x)) x
but is expected to have type
  forall (x : NNReal), Eq.{1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (instHMul.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (CanonicallyOrderedCommSemiring.toMul.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) instNNRealCanonicallyOrderedCommSemiring)) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x)) x
Case conversion may be inaccurate. Consider using '#align nnreal.mul_self_sqrt NNReal.mul_self_sqrtₓ'. -/
@[simp]
theorem mul_self_sqrt (x : ℝ≥0) : sqrt x * sqrt x = x := by rw [← sq, sq_sqrt]
#align nnreal.mul_self_sqrt NNReal.mul_self_sqrt

/- warning: nnreal.sqrt_sq -> NNReal.sqrt_sq is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} NNReal (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) x
but is expected to have type
  forall (x : NNReal), Eq.{1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) x
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_sq NNReal.sqrt_sqₓ'. -/
@[simp]
theorem sqrt_sq (x : ℝ≥0) : sqrt (x ^ 2) = x :=
  sqrt.apply_symm_apply x
#align nnreal.sqrt_sq NNReal.sqrt_sq

/- warning: nnreal.sqrt_mul_self -> NNReal.sqrt_mul_self is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} NNReal (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) x x)) x
but is expected to have type
  forall (x : NNReal), Eq.{1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) x x)) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) x x)) x
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_mul_self NNReal.sqrt_mul_selfₓ'. -/
@[simp]
theorem sqrt_mul_self (x : ℝ≥0) : sqrt (x * x) = x := by rw [← sq, sqrt_sq x]
#align nnreal.sqrt_mul_self NNReal.sqrt_mul_self

/- warning: nnreal.sqrt_mul -> NNReal.sqrt_mul is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) (y : NNReal), Eq.{1} NNReal (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) x y)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt y))
but is expected to have type
  forall (x : NNReal) (y : NNReal), Eq.{1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) x y)) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) x y)) (HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) y) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (instHMul.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (CanonicallyOrderedCommSemiring.toMul.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) instNNRealCanonicallyOrderedCommSemiring)) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) y))
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_mul NNReal.sqrt_mulₓ'. -/
theorem sqrt_mul (x y : ℝ≥0) : sqrt (x * y) = sqrt x * sqrt y := by
  rw [sqrt_eq_iff_sq_eq, mul_pow, sq_sqrt, sq_sqrt]
#align nnreal.sqrt_mul NNReal.sqrt_mul

#print NNReal.sqrtHom /-
/-- `nnreal.sqrt` as a `monoid_with_zero_hom`. -/
noncomputable def sqrtHom : ℝ≥0 →*₀ ℝ≥0 :=
  ⟨sqrt, sqrt_zero, sqrt_one, sqrt_mul⟩
#align nnreal.sqrt_hom NNReal.sqrtHom
-/

/- warning: nnreal.sqrt_inv -> NNReal.sqrt_inv is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} NNReal (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) x)) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x))
but is expected to have type
  forall (x : NNReal), Eq.{1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) x)) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) x)) (Inv.inv.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (CanonicallyLinearOrderedSemifield.toInv.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) NNReal.instCanonicallyLinearOrderedSemifieldNNReal) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x))
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_inv NNReal.sqrt_invₓ'. -/
theorem sqrt_inv (x : ℝ≥0) : sqrt x⁻¹ = (sqrt x)⁻¹ :=
  map_inv₀ sqrtHom x
#align nnreal.sqrt_inv NNReal.sqrt_inv

/- warning: nnreal.sqrt_div -> NNReal.sqrt_div is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) (y : NNReal), Eq.{1} NNReal (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) x y)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt y))
but is expected to have type
  forall (x : NNReal) (y : NNReal), Eq.{1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) x y)) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) x y)) (HDiv.hDiv.{0, 0, 0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) y) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (instHDiv.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) (CanonicallyLinearOrderedSemifield.toDiv.{0} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) x) NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) y))
Case conversion may be inaccurate. Consider using '#align nnreal.sqrt_div NNReal.sqrt_divₓ'. -/
theorem sqrt_div (x y : ℝ≥0) : sqrt (x / y) = sqrt x / sqrt y :=
  map_div₀ sqrtHom x y
#align nnreal.sqrt_div NNReal.sqrt_div

/- warning: nnreal.continuous_sqrt -> NNReal.continuous_sqrt is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} NNReal NNReal NNReal.topologicalSpace NNReal.topologicalSpace (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt)
but is expected to have type
  Continuous.{0, 0} NNReal NNReal NNReal.instTopologicalSpaceNNReal NNReal.instTopologicalSpaceNNReal (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)))
Case conversion may be inaccurate. Consider using '#align nnreal.continuous_sqrt NNReal.continuous_sqrtₓ'. -/
theorem continuous_sqrt : Continuous sqrt :=
  sqrt.Continuous
#align nnreal.continuous_sqrt NNReal.continuous_sqrt

end NNReal

namespace Real

/- warning: real.sqrt_aux -> Real.sqrtAux is a dubious translation:
lean 3 declaration is
  (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) -> Nat -> Rat
but is expected to have type
  (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instSupRat))) -> Nat -> Rat
Case conversion may be inaccurate. Consider using '#align real.sqrt_aux Real.sqrtAuxₓ'. -/
/-- An auxiliary sequence of rational numbers that converges to `real.sqrt (mk f)`.
Currently this sequence is not used in `mathlib`.  -/
def sqrtAux (f : CauSeq ℚ abs) : ℕ → ℚ
  | 0 => mkRat (f 0).num.toNat.sqrt (f 0).den.sqrt
  | n + 1 =>
    let s := sqrt_aux n
    max 0 <| (s + f (n + 1) / s) / 2
#align real.sqrt_aux Real.sqrtAux

/- warning: real.sqrt_aux_nonneg -> Real.sqrtAux_nonneg is a dubious translation:
lean 3 declaration is
  forall (f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (i : Nat), LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) (Real.sqrtAux f i)
but is expected to have type
  forall (f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instSupRat))) (i : Nat), LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) (Real.sqrtAux f i)
Case conversion may be inaccurate. Consider using '#align real.sqrt_aux_nonneg Real.sqrtAux_nonnegₓ'. -/
theorem sqrtAux_nonneg (f : CauSeq ℚ abs) : ∀ i : ℕ, 0 ≤ sqrtAux f i
  | 0 => by
    rw [sqrt_aux, Rat.mkRat_eq, Rat.divInt_eq_div] <;> apply div_nonneg <;>
      exact Int.cast_nonneg.2 (Int.ofNat_nonneg _)
  | n + 1 => le_max_left _ _
#align real.sqrt_aux_nonneg Real.sqrtAux_nonneg

#print Real.sqrt /-
/- TODO(Mario): finish the proof
theorem sqrt_aux_converges (f : cau_seq ℚ abs) : ∃ h x, 0 ≤ x ∧ x * x = max 0 (mk f) ∧
  mk ⟨sqrt_aux f, h⟩ = x :=
begin
  rcases sqrt_exists (le_max_left 0 (mk f)) with ⟨x, x0, hx⟩,
  suffices : ∃ h, mk ⟨sqrt_aux f, h⟩ = x,
  { exact this.imp (λ h e, ⟨x, x0, hx, e⟩) },
  apply of_near,

  rsuffices ⟨δ, δ0, hδ⟩ : ∃ δ > 0, ∀ i, abs (↑(sqrt_aux f i) - x) < δ / 2 ^ i,
  { intros }
end -/
/-- The square root of a real number. This returns 0 for negative inputs. -/
@[pp_nodot]
noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)
#align real.sqrt Real.sqrt
-/

/-quotient.lift_on x
  (λ f, mk ⟨sqrt_aux f, (sqrt_aux_converges f).fst⟩)
  (λ f g e, begin
    rcases sqrt_aux_converges f with ⟨hf, x, x0, xf, xs⟩,
    rcases sqrt_aux_converges g with ⟨hg, y, y0, yg, ys⟩,
    refine xs.trans (eq.trans _ ys.symm),
    rw [← @mul_self_inj_of_nonneg ℝ _ x y x0 y0, xf, yg],
    congr' 1, exact quotient.sound e
  end)-/
variable {x y : ℝ}

/- warning: real.coe_sqrt -> Real.coe_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : NNReal}, Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (coeFn.{1, 1} (OrderIso.{0, 0} NNReal NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (fun (_x : RelIso.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) => NNReal -> NNReal) (RelIso.hasCoeToFun.{0, 0} NNReal NNReal (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))) NNReal.sqrt x)) (Real.sqrt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x))
but is expected to have type
  forall {x : NNReal}, Eq.{1} Real (NNReal.toReal (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : NNReal) => NNReal) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} NNReal NNReal) NNReal NNReal (Function.instEmbeddingLikeEmbedding.{1, 1} NNReal NNReal)) (RelEmbedding.toEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : NNReal) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) NNReal.sqrt)) x)) (Real.sqrt (NNReal.toReal x))
Case conversion may be inaccurate. Consider using '#align real.coe_sqrt Real.coe_sqrtₓ'. -/
@[simp, norm_cast]
theorem coe_sqrt {x : ℝ≥0} : (NNReal.sqrt x : ℝ) = Real.sqrt x := by
  rw [Real.sqrt, Real.toNNReal_coe]
#align real.coe_sqrt Real.coe_sqrt

#print Real.continuous_sqrt /-
@[continuity]
theorem continuous_sqrt : Continuous sqrt :=
  NNReal.continuous_coe.comp <| NNReal.sqrt.Continuous.comp continuous_real_toNNReal
#align real.continuous_sqrt Real.continuous_sqrt
-/

/- warning: real.sqrt_eq_zero_of_nonpos -> Real.sqrt_eq_zero_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.sqrt_eq_zero_of_nonpos Real.sqrt_eq_zero_of_nonposₓ'. -/
theorem sqrt_eq_zero_of_nonpos (h : x ≤ 0) : sqrt x = 0 := by simp [sqrt, Real.toNNReal_eq_zero.2 h]
#align real.sqrt_eq_zero_of_nonpos Real.sqrt_eq_zero_of_nonpos

/- warning: real.sqrt_nonneg -> Real.sqrt_nonneg is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sqrt x)
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sqrt x)
Case conversion may be inaccurate. Consider using '#align real.sqrt_nonneg Real.sqrt_nonnegₓ'. -/
theorem sqrt_nonneg (x : ℝ) : 0 ≤ sqrt x :=
  NNReal.coe_nonneg _
#align real.sqrt_nonneg Real.sqrt_nonneg

/- warning: real.mul_self_sqrt -> Real.mul_self_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.sqrt x) (Real.sqrt x)) x)
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.sqrt x) (Real.sqrt x)) x)
Case conversion may be inaccurate. Consider using '#align real.mul_self_sqrt Real.mul_self_sqrtₓ'. -/
@[simp]
theorem mul_self_sqrt (h : 0 ≤ x) : sqrt x * sqrt x = x := by
  rw [sqrt, ← NNReal.coe_mul, NNReal.mul_self_sqrt, Real.coe_toNNReal _ h]
#align real.mul_self_sqrt Real.mul_self_sqrt

/- warning: real.sqrt_mul_self -> Real.sqrt_mul_self is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.sqrt (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x x)) x)
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.sqrt (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x x)) x)
Case conversion may be inaccurate. Consider using '#align real.sqrt_mul_self Real.sqrt_mul_selfₓ'. -/
@[simp]
theorem sqrt_mul_self (h : 0 ≤ x) : sqrt (x * x) = x :=
  (mul_self_inj_of_nonneg (sqrt_nonneg _) h).1 (mul_self_sqrt (mul_self_nonneg _))
#align real.sqrt_mul_self Real.sqrt_mul_self

/- warning: real.sqrt_eq_cases -> Real.sqrt_eq_cases is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, Iff (Eq.{1} Real (Real.sqrt x) y) (Or (And (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) y y) x) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y)) (And (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))
but is expected to have type
  forall {x : Real} {y : Real}, Iff (Eq.{1} Real (Real.sqrt x) y) (Or (And (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) y y) x) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y)) (And (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_eq_cases Real.sqrt_eq_casesₓ'. -/
theorem sqrt_eq_cases : sqrt x = y ↔ y * y = x ∧ 0 ≤ y ∨ x < 0 ∧ y = 0 :=
  by
  constructor
  · rintro rfl
    cases' le_or_lt 0 x with hle hlt
    · exact Or.inl ⟨mul_self_sqrt hle, sqrt_nonneg x⟩
    · exact Or.inr ⟨hlt, sqrt_eq_zero_of_nonpos hlt.le⟩
  · rintro (⟨rfl, hy⟩ | ⟨hx, rfl⟩)
    exacts[sqrt_mul_self hy, sqrt_eq_zero_of_nonpos hx.le]
#align real.sqrt_eq_cases Real.sqrt_eq_cases

/- warning: real.sqrt_eq_iff_mul_self_eq -> Real.sqrt_eq_iff_mul_self_eq is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (Eq.{1} Real (Real.sqrt x) y) (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) y y) x))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (Eq.{1} Real (Real.sqrt x) y) (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) y y) x))
Case conversion may be inaccurate. Consider using '#align real.sqrt_eq_iff_mul_self_eq Real.sqrt_eq_iff_mul_self_eqₓ'. -/
theorem sqrt_eq_iff_mul_self_eq (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = y ↔ y * y = x :=
  ⟨fun h => by rw [← h, mul_self_sqrt hx], fun h => by rw [← h, sqrt_mul_self hy]⟩
#align real.sqrt_eq_iff_mul_self_eq Real.sqrt_eq_iff_mul_self_eq

/- warning: real.sqrt_eq_iff_mul_self_eq_of_pos -> Real.sqrt_eq_iff_mul_self_eq_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (Eq.{1} Real (Real.sqrt x) y) (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) y y) x))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (Eq.{1} Real (Real.sqrt x) y) (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) y y) x))
Case conversion may be inaccurate. Consider using '#align real.sqrt_eq_iff_mul_self_eq_of_pos Real.sqrt_eq_iff_mul_self_eq_of_posₓ'. -/
theorem sqrt_eq_iff_mul_self_eq_of_pos (h : 0 < y) : sqrt x = y ↔ y * y = x := by
  simp [sqrt_eq_cases, h.ne', h.le]
#align real.sqrt_eq_iff_mul_self_eq_of_pos Real.sqrt_eq_iff_mul_self_eq_of_pos

/- warning: real.sqrt_eq_one -> Real.sqrt_eq_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.sqrt_eq_one Real.sqrt_eq_oneₓ'. -/
@[simp]
theorem sqrt_eq_one : sqrt x = 1 ↔ x = 1 :=
  calc
    sqrt x = 1 ↔ 1 * 1 = x := sqrt_eq_iff_mul_self_eq_of_pos zero_lt_one
    _ ↔ x = 1 := by rw [eq_comm, mul_one]
    
#align real.sqrt_eq_one Real.sqrt_eq_one

/- warning: real.sq_sqrt -> Real.sq_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sqrt x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) x)
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sqrt x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) x)
Case conversion may be inaccurate. Consider using '#align real.sq_sqrt Real.sq_sqrtₓ'. -/
@[simp]
theorem sq_sqrt (h : 0 ≤ x) : sqrt x ^ 2 = x := by rw [sq, mul_self_sqrt h]
#align real.sq_sqrt Real.sq_sqrt

/- warning: real.sqrt_sq -> Real.sqrt_sq is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.sqrt (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) x)
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.sqrt (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) x)
Case conversion may be inaccurate. Consider using '#align real.sqrt_sq Real.sqrt_sqₓ'. -/
@[simp]
theorem sqrt_sq (h : 0 ≤ x) : sqrt (x ^ 2) = x := by rw [sq, sqrt_mul_self h]
#align real.sqrt_sq Real.sqrt_sq

/- warning: real.sqrt_eq_iff_sq_eq -> Real.sqrt_eq_iff_sq_eq is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (Eq.{1} Real (Real.sqrt x) y) (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) x))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (Eq.{1} Real (Real.sqrt x) y) (Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) x))
Case conversion may be inaccurate. Consider using '#align real.sqrt_eq_iff_sq_eq Real.sqrt_eq_iff_sq_eqₓ'. -/
theorem sqrt_eq_iff_sq_eq (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = y ↔ y ^ 2 = x := by
  rw [sq, sqrt_eq_iff_mul_self_eq hx hy]
#align real.sqrt_eq_iff_sq_eq Real.sqrt_eq_iff_sq_eq

/- warning: real.sqrt_mul_self_eq_abs -> Real.sqrt_mul_self_eq_abs is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.sqrt (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x x)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.sqrt (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x x)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x)
Case conversion may be inaccurate. Consider using '#align real.sqrt_mul_self_eq_abs Real.sqrt_mul_self_eq_absₓ'. -/
theorem sqrt_mul_self_eq_abs (x : ℝ) : sqrt (x * x) = |x| := by
  rw [← abs_mul_abs_self x, sqrt_mul_self (abs_nonneg _)]
#align real.sqrt_mul_self_eq_abs Real.sqrt_mul_self_eq_abs

/- warning: real.sqrt_sq_eq_abs -> Real.sqrt_sq_eq_abs is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.sqrt (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.sqrt (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x)
Case conversion may be inaccurate. Consider using '#align real.sqrt_sq_eq_abs Real.sqrt_sq_eq_absₓ'. -/
theorem sqrt_sq_eq_abs (x : ℝ) : sqrt (x ^ 2) = |x| := by rw [sq, sqrt_mul_self_eq_abs]
#align real.sqrt_sq_eq_abs Real.sqrt_sq_eq_abs

/- warning: real.sqrt_zero -> Real.sqrt_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.sqrt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Real.sqrt (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.sqrt_zero Real.sqrt_zeroₓ'. -/
@[simp]
theorem sqrt_zero : sqrt 0 = 0 := by simp [sqrt]
#align real.sqrt_zero Real.sqrt_zero

/- warning: real.sqrt_one -> Real.sqrt_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.sqrt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (Real.sqrt (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.sqrt_one Real.sqrt_oneₓ'. -/
@[simp]
theorem sqrt_one : sqrt 1 = 1 := by simp [sqrt]
#align real.sqrt_one Real.sqrt_one

/- warning: real.sqrt_le_sqrt_iff -> Real.sqrt_le_sqrt_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe (Real.sqrt x) (Real.sqrt y)) (LE.le.{0} Real Real.hasLe x y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.sqrt x) (Real.sqrt y)) (LE.le.{0} Real Real.instLEReal x y))
Case conversion may be inaccurate. Consider using '#align real.sqrt_le_sqrt_iff Real.sqrt_le_sqrt_iffₓ'. -/
@[simp]
theorem sqrt_le_sqrt_iff (hy : 0 ≤ y) : sqrt x ≤ sqrt y ↔ x ≤ y := by
  rw [sqrt, sqrt, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt_iff, Real.toNNReal_le_toNNReal_iff hy]
#align real.sqrt_le_sqrt_iff Real.sqrt_le_sqrt_iff

/- warning: real.sqrt_lt_sqrt_iff -> Real.sqrt_lt_sqrt_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.sqrt x) (Real.sqrt y)) (LT.lt.{0} Real Real.hasLt x y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.sqrt x) (Real.sqrt y)) (LT.lt.{0} Real Real.instLTReal x y))
Case conversion may be inaccurate. Consider using '#align real.sqrt_lt_sqrt_iff Real.sqrt_lt_sqrt_iffₓ'. -/
@[simp]
theorem sqrt_lt_sqrt_iff (hx : 0 ≤ x) : sqrt x < sqrt y ↔ x < y :=
  lt_iff_lt_of_le_iff_le (sqrt_le_sqrt_iff hx)
#align real.sqrt_lt_sqrt_iff Real.sqrt_lt_sqrt_iff

/- warning: real.sqrt_lt_sqrt_iff_of_pos -> Real.sqrt_lt_sqrt_iff_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.sqrt x) (Real.sqrt y)) (LT.lt.{0} Real Real.hasLt x y))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.sqrt x) (Real.sqrt y)) (LT.lt.{0} Real Real.instLTReal x y))
Case conversion may be inaccurate. Consider using '#align real.sqrt_lt_sqrt_iff_of_pos Real.sqrt_lt_sqrt_iff_of_posₓ'. -/
theorem sqrt_lt_sqrt_iff_of_pos (hy : 0 < y) : sqrt x < sqrt y ↔ x < y := by
  rw [sqrt, sqrt, NNReal.coe_lt_coe, NNReal.sqrt_lt_sqrt_iff, to_nnreal_lt_to_nnreal_iff hy]
#align real.sqrt_lt_sqrt_iff_of_pos Real.sqrt_lt_sqrt_iff_of_pos

/- warning: real.sqrt_le_sqrt -> Real.sqrt_le_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe x y) -> (LE.le.{0} Real Real.hasLe (Real.sqrt x) (Real.sqrt y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal x y) -> (LE.le.{0} Real Real.instLEReal (Real.sqrt x) (Real.sqrt y))
Case conversion may be inaccurate. Consider using '#align real.sqrt_le_sqrt Real.sqrt_le_sqrtₓ'. -/
theorem sqrt_le_sqrt (h : x ≤ y) : sqrt x ≤ sqrt y :=
  by
  rw [sqrt, sqrt, NNReal.coe_le_coe, NNReal.sqrt_le_sqrt_iff]
  exact to_nnreal_le_to_nnreal h
#align real.sqrt_le_sqrt Real.sqrt_le_sqrt

/- warning: real.sqrt_lt_sqrt -> Real.sqrt_lt_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (Real.sqrt x) (Real.sqrt y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (Real.sqrt x) (Real.sqrt y))
Case conversion may be inaccurate. Consider using '#align real.sqrt_lt_sqrt Real.sqrt_lt_sqrtₓ'. -/
theorem sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y) : sqrt x < sqrt y :=
  (sqrt_lt_sqrt_iff hx).2 h
#align real.sqrt_lt_sqrt Real.sqrt_lt_sqrt

/- warning: real.sqrt_le_left -> Real.sqrt_le_left is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe (Real.sqrt x) y) (LE.le.{0} Real Real.hasLe x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.sqrt x) y) (LE.le.{0} Real Real.instLEReal x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_le_left Real.sqrt_le_leftₓ'. -/
theorem sqrt_le_left (hy : 0 ≤ y) : sqrt x ≤ y ↔ x ≤ y ^ 2 := by
  rw [sqrt, ← Real.le_toNNReal_iff_coe_le hy, NNReal.sqrt_le_iff, sq, ← Real.toNNReal_mul hy,
    Real.toNNReal_le_toNNReal_iff (mul_self_nonneg y), sq]
#align real.sqrt_le_left Real.sqrt_le_left

/- warning: real.sqrt_le_iff -> Real.sqrt_le_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, Iff (LE.le.{0} Real Real.hasLe (Real.sqrt x) y) (And (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) (LE.le.{0} Real Real.hasLe x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {x : Real} {y : Real}, Iff (LE.le.{0} Real Real.instLEReal (Real.sqrt x) y) (And (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) (LE.le.{0} Real Real.instLEReal x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_le_iff Real.sqrt_le_iffₓ'. -/
theorem sqrt_le_iff : sqrt x ≤ y ↔ 0 ≤ y ∧ x ≤ y ^ 2 :=
  by
  rw [← and_iff_right_of_imp fun h => (sqrt_nonneg x).trans h, and_congr_right_iff]
  exact sqrt_le_left
#align real.sqrt_le_iff Real.sqrt_le_iff

/- warning: real.sqrt_lt -> Real.sqrt_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.sqrt x) y) (LT.lt.{0} Real Real.hasLt x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.sqrt x) y) (LT.lt.{0} Real Real.instLTReal x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_lt Real.sqrt_ltₓ'. -/
theorem sqrt_lt (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff hx, sqrt_sq hy]
#align real.sqrt_lt Real.sqrt_lt

/- warning: real.sqrt_lt' -> Real.sqrt_lt' is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.sqrt x) y) (LT.lt.{0} Real Real.hasLt x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.sqrt x) y) (LT.lt.{0} Real Real.instLTReal x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_lt' Real.sqrt_lt'ₓ'. -/
theorem sqrt_lt' (hy : 0 < y) : sqrt x < y ↔ x < y ^ 2 := by
  rw [← sqrt_lt_sqrt_iff_of_pos (pow_pos hy _), sqrt_sq hy.le]
#align real.sqrt_lt' Real.sqrt_lt'

/- warning: real.le_sqrt -> Real.le_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe x (Real.sqrt y)) (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal x (Real.sqrt y)) (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y))
Case conversion may be inaccurate. Consider using '#align real.le_sqrt Real.le_sqrtₓ'. -/
/- note: if you want to conclude `x ≤ sqrt y`, then use `le_sqrt_of_sq_le`.
   if you have `x > 0`, consider using `le_sqrt'` -/
theorem le_sqrt (hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| sqrt_lt hy hx
#align real.le_sqrt Real.le_sqrt

/- warning: real.le_sqrt' -> Real.le_sqrt' is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe x (Real.sqrt y)) (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal x (Real.sqrt y)) (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y))
Case conversion may be inaccurate. Consider using '#align real.le_sqrt' Real.le_sqrt'ₓ'. -/
theorem le_sqrt' (hx : 0 < x) : x ≤ sqrt y ↔ x ^ 2 ≤ y :=
  le_iff_le_iff_lt_iff_lt.2 <| sqrt_lt' hx
#align real.le_sqrt' Real.le_sqrt'

/- warning: real.abs_le_sqrt -> Real.abs_le_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (Real.sqrt y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (Real.sqrt y))
Case conversion may be inaccurate. Consider using '#align real.abs_le_sqrt Real.abs_le_sqrtₓ'. -/
theorem abs_le_sqrt (h : x ^ 2 ≤ y) : |x| ≤ sqrt y := by
  rw [← sqrt_sq_eq_abs] <;> exact sqrt_le_sqrt h
#align real.abs_le_sqrt Real.abs_le_sqrt

/- warning: real.sq_le -> Real.sq_le is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y) (And (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (Real.sqrt y)) x) (LE.le.{0} Real Real.hasLe x (Real.sqrt y))))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y) (And (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (Real.sqrt y)) x) (LE.le.{0} Real Real.instLEReal x (Real.sqrt y))))
Case conversion may be inaccurate. Consider using '#align real.sq_le Real.sq_leₓ'. -/
theorem sq_le (h : 0 ≤ y) : x ^ 2 ≤ y ↔ -sqrt y ≤ x ∧ x ≤ sqrt y :=
  by
  constructor
  · simpa only [abs_le] using abs_le_sqrt
  · rw [← abs_le, ← sq_abs]
    exact (le_sqrt (abs_nonneg x) h).mp
#align real.sq_le Real.sq_le

/- warning: real.neg_sqrt_le_of_sq_le -> Real.neg_sqrt_le_of_sq_le is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y) -> (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (Real.sqrt y)) x)
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y) -> (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (Real.sqrt y)) x)
Case conversion may be inaccurate. Consider using '#align real.neg_sqrt_le_of_sq_le Real.neg_sqrt_le_of_sq_leₓ'. -/
theorem neg_sqrt_le_of_sq_le (h : x ^ 2 ≤ y) : -sqrt y ≤ x :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).1
#align real.neg_sqrt_le_of_sq_le Real.neg_sqrt_le_of_sq_le

/- warning: real.le_sqrt_of_sq_le -> Real.le_sqrt_of_sq_le is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y) -> (LE.le.{0} Real Real.hasLe x (Real.sqrt y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y) -> (LE.le.{0} Real Real.instLEReal x (Real.sqrt y))
Case conversion may be inaccurate. Consider using '#align real.le_sqrt_of_sq_le Real.le_sqrt_of_sq_leₓ'. -/
theorem le_sqrt_of_sq_le (h : x ^ 2 ≤ y) : x ≤ sqrt y :=
  ((sq_le ((sq_nonneg x).trans h)).mp h).2
#align real.le_sqrt_of_sq_le Real.le_sqrt_of_sq_le

/- warning: real.sqrt_inj -> Real.sqrt_inj is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (Eq.{1} Real (Real.sqrt x) (Real.sqrt y)) (Eq.{1} Real x y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (Eq.{1} Real (Real.sqrt x) (Real.sqrt y)) (Eq.{1} Real x y))
Case conversion may be inaccurate. Consider using '#align real.sqrt_inj Real.sqrt_injₓ'. -/
@[simp]
theorem sqrt_inj (hx : 0 ≤ x) (hy : 0 ≤ y) : sqrt x = sqrt y ↔ x = y := by
  simp [le_antisymm_iff, hx, hy]
#align real.sqrt_inj Real.sqrt_inj

/- warning: real.sqrt_eq_zero -> Real.sqrt_eq_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (Eq.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (Eq.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_eq_zero Real.sqrt_eq_zeroₓ'. -/
@[simp]
theorem sqrt_eq_zero (h : 0 ≤ x) : sqrt x = 0 ↔ x = 0 := by simpa using sqrt_inj h le_rfl
#align real.sqrt_eq_zero Real.sqrt_eq_zero

/- warning: real.sqrt_eq_zero' -> Real.sqrt_eq_zero' is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.sqrt_eq_zero' Real.sqrt_eq_zero'ₓ'. -/
theorem sqrt_eq_zero' : sqrt x = 0 ↔ x ≤ 0 := by
  rw [sqrt, NNReal.coe_eq_zero, NNReal.sqrt_eq_zero, Real.toNNReal_eq_zero]
#align real.sqrt_eq_zero' Real.sqrt_eq_zero'

/- warning: real.sqrt_ne_zero -> Real.sqrt_ne_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (Ne.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (Ne.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_ne_zero Real.sqrt_ne_zeroₓ'. -/
theorem sqrt_ne_zero (h : 0 ≤ x) : sqrt x ≠ 0 ↔ x ≠ 0 := by rw [not_iff_not, sqrt_eq_zero h]
#align real.sqrt_ne_zero Real.sqrt_ne_zero

/- warning: real.sqrt_ne_zero' -> Real.sqrt_ne_zero' is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Ne.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (Ne.{1} Real (Real.sqrt x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align real.sqrt_ne_zero' Real.sqrt_ne_zero'ₓ'. -/
theorem sqrt_ne_zero' : sqrt x ≠ 0 ↔ 0 < x := by rw [← not_le, not_iff_not, sqrt_eq_zero']
#align real.sqrt_ne_zero' Real.sqrt_ne_zero'

/- warning: real.sqrt_pos -> Real.sqrt_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sqrt x)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sqrt x)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align real.sqrt_pos Real.sqrt_posₓ'. -/
@[simp]
theorem sqrt_pos : 0 < sqrt x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le (Iff.trans (by simp [le_antisymm_iff, sqrt_nonneg]) sqrt_eq_zero')
#align real.sqrt_pos Real.sqrt_pos

/- warning: real.sqrt_pos_of_pos -> Real.sqrt_pos_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sqrt x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sqrt x))
Case conversion may be inaccurate. Consider using '#align real.sqrt_pos_of_pos Real.sqrt_pos_of_posₓ'. -/
alias sqrt_pos ↔ _ sqrt_pos_of_pos
#align real.sqrt_pos_of_pos Real.sqrt_pos_of_pos

section

open Tactic Tactic.Positivity

/-- Extension for the `positivity` tactic: a square root is nonnegative, and is strictly positive if
its input is. -/
@[positivity]
unsafe def _root_.tactic.positivity_sqrt : expr → tactic strictness
  | q(Real.sqrt $(a)) => do
    (-- if can prove `0 < a`, report positivity
        do
          let positive pa ← core a
          positive <$> mk_app `` sqrt_pos_of_pos [pa]) <|>
        nonnegative <$> mk_app `` sqrt_nonneg [a]
  |-- else report nonnegativity
    _ =>
    failed
#align tactic.positivity_sqrt tactic.positivity_sqrt

end

/- warning: real.sqrt_mul -> Real.sqrt_mul is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real), Eq.{1} Real (Real.sqrt (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.sqrt x) (Real.sqrt y)))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real), Eq.{1} Real (Real.sqrt (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.sqrt x) (Real.sqrt y)))
Case conversion may be inaccurate. Consider using '#align real.sqrt_mul Real.sqrt_mulₓ'. -/
@[simp]
theorem sqrt_mul (hx : 0 ≤ x) (y : ℝ) : sqrt (x * y) = sqrt x * sqrt y := by
  simp_rw [sqrt, ← NNReal.coe_mul, NNReal.coe_eq, Real.toNNReal_mul hx, NNReal.sqrt_mul]
#align real.sqrt_mul Real.sqrt_mul

/- warning: real.sqrt_mul' -> Real.sqrt_mul' is a dubious translation:
lean 3 declaration is
  forall (x : Real) {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Eq.{1} Real (Real.sqrt (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.sqrt x) (Real.sqrt y)))
but is expected to have type
  forall (x : Real) {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Eq.{1} Real (Real.sqrt (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.sqrt x) (Real.sqrt y)))
Case conversion may be inaccurate. Consider using '#align real.sqrt_mul' Real.sqrt_mul'ₓ'. -/
@[simp]
theorem sqrt_mul' (x) {y : ℝ} (hy : 0 ≤ y) : sqrt (x * y) = sqrt x * sqrt y := by
  rw [mul_comm, sqrt_mul hy, mul_comm]
#align real.sqrt_mul' Real.sqrt_mul'

/- warning: real.sqrt_inv -> Real.sqrt_inv is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.sqrt (Inv.inv.{0} Real Real.hasInv x)) (Inv.inv.{0} Real Real.hasInv (Real.sqrt x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.sqrt (Inv.inv.{0} Real Real.instInvReal x)) (Inv.inv.{0} Real Real.instInvReal (Real.sqrt x))
Case conversion may be inaccurate. Consider using '#align real.sqrt_inv Real.sqrt_invₓ'. -/
@[simp]
theorem sqrt_inv (x : ℝ) : sqrt x⁻¹ = (sqrt x)⁻¹ := by
  rw [sqrt, Real.toNNReal_inv, NNReal.sqrt_inv, NNReal.coe_inv, sqrt]
#align real.sqrt_inv Real.sqrt_inv

/- warning: real.sqrt_div -> Real.sqrt_div is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (y : Real), Eq.{1} Real (Real.sqrt (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x y)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sqrt x) (Real.sqrt y)))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (y : Real), Eq.{1} Real (Real.sqrt (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x y)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sqrt x) (Real.sqrt y)))
Case conversion may be inaccurate. Consider using '#align real.sqrt_div Real.sqrt_divₓ'. -/
@[simp]
theorem sqrt_div (hx : 0 ≤ x) (y : ℝ) : sqrt (x / y) = sqrt x / sqrt y := by
  rw [division_def, sqrt_mul hx, sqrt_inv, division_def]
#align real.sqrt_div Real.sqrt_div

/- warning: real.sqrt_div' -> Real.sqrt_div' is a dubious translation:
lean 3 declaration is
  forall (x : Real) {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Eq.{1} Real (Real.sqrt (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x y)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sqrt x) (Real.sqrt y)))
but is expected to have type
  forall (x : Real) {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Eq.{1} Real (Real.sqrt (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x y)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sqrt x) (Real.sqrt y)))
Case conversion may be inaccurate. Consider using '#align real.sqrt_div' Real.sqrt_div'ₓ'. -/
@[simp]
theorem sqrt_div' (x) {y : ℝ} (hy : 0 ≤ y) : sqrt (x / y) = sqrt x / sqrt y := by
  rw [division_def, sqrt_mul' x (inv_nonneg.2 hy), sqrt_inv, division_def]
#align real.sqrt_div' Real.sqrt_div'

/- warning: real.div_sqrt -> Real.div_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x (Real.sqrt x)) (Real.sqrt x)
but is expected to have type
  forall {x : Real}, Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Real.sqrt x)) (Real.sqrt x)
Case conversion may be inaccurate. Consider using '#align real.div_sqrt Real.div_sqrtₓ'. -/
@[simp]
theorem div_sqrt : x / sqrt x = sqrt x :=
  by
  cases le_or_lt x 0
  · rw [sqrt_eq_zero'.mpr h, div_zero]
  · rw [div_eq_iff (sqrt_ne_zero'.mpr h), mul_self_sqrt h.le]
#align real.div_sqrt Real.div_sqrt

/- warning: real.sqrt_div_self' -> Real.sqrt_div_self' is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sqrt x) x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Real.sqrt x))
but is expected to have type
  forall {x : Real}, Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sqrt x) x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Real.sqrt x))
Case conversion may be inaccurate. Consider using '#align real.sqrt_div_self' Real.sqrt_div_self'ₓ'. -/
theorem sqrt_div_self' : sqrt x / x = 1 / sqrt x := by rw [← div_sqrt, one_div_div, div_sqrt]
#align real.sqrt_div_self' Real.sqrt_div_self'

/- warning: real.sqrt_div_self -> Real.sqrt_div_self is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sqrt x) x) (Inv.inv.{0} Real Real.hasInv (Real.sqrt x))
but is expected to have type
  forall {x : Real}, Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sqrt x) x) (Inv.inv.{0} Real Real.instInvReal (Real.sqrt x))
Case conversion may be inaccurate. Consider using '#align real.sqrt_div_self Real.sqrt_div_selfₓ'. -/
theorem sqrt_div_self : sqrt x / x = (sqrt x)⁻¹ := by rw [sqrt_div_self', one_div]
#align real.sqrt_div_self Real.sqrt_div_self

/- warning: real.lt_sqrt -> Real.lt_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt x (Real.sqrt y)) (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal x (Real.sqrt y)) (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y))
Case conversion may be inaccurate. Consider using '#align real.lt_sqrt Real.lt_sqrtₓ'. -/
theorem lt_sqrt (hx : 0 ≤ x) : x < sqrt y ↔ x ^ 2 < y := by
  rw [← sqrt_lt_sqrt_iff (sq_nonneg _), sqrt_sq hx]
#align real.lt_sqrt Real.lt_sqrt

/- warning: real.sq_lt -> Real.sq_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, Iff (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y) (And (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg (Real.sqrt y)) x) (LT.lt.{0} Real Real.hasLt x (Real.sqrt y)))
but is expected to have type
  forall {x : Real} {y : Real}, Iff (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y) (And (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal (Real.sqrt y)) x) (LT.lt.{0} Real Real.instLTReal x (Real.sqrt y)))
Case conversion may be inaccurate. Consider using '#align real.sq_lt Real.sq_ltₓ'. -/
theorem sq_lt : x ^ 2 < y ↔ -sqrt y < x ∧ x < sqrt y := by
  rw [← abs_lt, ← sq_abs, lt_sqrt (abs_nonneg _)]
#align real.sq_lt Real.sq_lt

/- warning: real.neg_sqrt_lt_of_sq_lt -> Real.neg_sqrt_lt_of_sq_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y) -> (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg (Real.sqrt y)) x)
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y) -> (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal (Real.sqrt y)) x)
Case conversion may be inaccurate. Consider using '#align real.neg_sqrt_lt_of_sq_lt Real.neg_sqrt_lt_of_sq_ltₓ'. -/
theorem neg_sqrt_lt_of_sq_lt (h : x ^ 2 < y) : -sqrt y < x :=
  (sq_lt.mp h).1
#align real.neg_sqrt_lt_of_sq_lt Real.neg_sqrt_lt_of_sq_lt

/- warning: real.lt_sqrt_of_sq_lt -> Real.lt_sqrt_of_sq_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) y) -> (LT.lt.{0} Real Real.hasLt x (Real.sqrt y))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) y) -> (LT.lt.{0} Real Real.instLTReal x (Real.sqrt y))
Case conversion may be inaccurate. Consider using '#align real.lt_sqrt_of_sq_lt Real.lt_sqrt_of_sq_ltₓ'. -/
theorem lt_sqrt_of_sq_lt (h : x ^ 2 < y) : x < sqrt y :=
  (sq_lt.mp h).2
#align real.lt_sqrt_of_sq_lt Real.lt_sqrt_of_sq_lt

/- warning: real.lt_sq_of_sqrt_lt -> Real.lt_sq_of_sqrt_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (Real.sqrt x) y) -> (LT.lt.{0} Real Real.hasLt x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) y (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (Real.sqrt x) y) -> (LT.lt.{0} Real Real.instLTReal x (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) y (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align real.lt_sq_of_sqrt_lt Real.lt_sq_of_sqrt_ltₓ'. -/
theorem lt_sq_of_sqrt_lt {x y : ℝ} (h : sqrt x < y) : x < y ^ 2 :=
  by
  have hy := x.sqrt_nonneg.trans_lt h
  rwa [← sqrt_lt_sqrt_iff_of_pos (sq_pos_of_pos hy), sqrt_sq hy.le]
#align real.lt_sq_of_sqrt_lt Real.lt_sq_of_sqrt_lt

/- warning: real.nat_sqrt_le_real_sqrt -> Real.nat_sqrt_le_real_sqrt is a dubious translation:
lean 3 declaration is
  forall {a : Nat}, LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.sqrt a)) (Real.sqrt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) a))
but is expected to have type
  forall {a : Nat}, LE.le.{0} Real Real.instLEReal (Nat.cast.{0} Real Real.natCast (Nat.sqrt a)) (Real.sqrt (Nat.cast.{0} Real Real.natCast a))
Case conversion may be inaccurate. Consider using '#align real.nat_sqrt_le_real_sqrt Real.nat_sqrt_le_real_sqrtₓ'. -/
/-- The natural square root is at most the real square root -/
theorem nat_sqrt_le_real_sqrt {a : ℕ} : ↑(Nat.sqrt a) ≤ Real.sqrt ↑a :=
  by
  rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  norm_cast
  exact Nat.sqrt_le' a
#align real.nat_sqrt_le_real_sqrt Real.nat_sqrt_le_real_sqrt

/- warning: real.real_sqrt_le_nat_sqrt_succ -> Real.real_sqrt_le_nat_sqrt_succ is a dubious translation:
lean 3 declaration is
  forall {a : Nat}, LE.le.{0} Real Real.hasLe (Real.sqrt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) a)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (Nat.sqrt a)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {a : Nat}, LE.le.{0} Real Real.instLEReal (Real.sqrt (Nat.cast.{0} Real Real.natCast a)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast (Nat.sqrt a)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.real_sqrt_le_nat_sqrt_succ Real.real_sqrt_le_nat_sqrt_succₓ'. -/
/-- The real square root is at most the natural square root plus one -/
theorem real_sqrt_le_nat_sqrt_succ {a : ℕ} : Real.sqrt ↑a ≤ Nat.sqrt a + 1 :=
  by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_cast
    simp
  · norm_cast
    exact le_of_lt (Nat.lt_succ_sqrt' a)
#align real.real_sqrt_le_nat_sqrt_succ Real.real_sqrt_le_nat_sqrt_succ

instance : StarOrderedRing ℝ :=
  { Real.orderedAddCommGroup with
    nonneg_iff := fun r =>
      by
      refine'
        ⟨fun hr => ⟨sqrt r, show r = sqrt r * sqrt r by rw [← sqrt_mul hr, sqrt_mul_self hr]⟩, _⟩
      rintro ⟨s, rfl⟩
      exact mul_self_nonneg s }

end Real

open Real

variable {α : Type _}

#print Filter.Tendsto.sqrt /-
theorem Filter.Tendsto.sqrt {f : α → ℝ} {l : Filter α} {x : ℝ} (h : Tendsto f l (𝓝 x)) :
    Tendsto (fun x => sqrt (f x)) l (𝓝 (sqrt x)) :=
  (continuous_sqrt.Tendsto _).comp h
#align filter.tendsto.sqrt Filter.Tendsto.sqrt
-/

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {x : α}

#print ContinuousWithinAt.sqrt /-
theorem ContinuousWithinAt.sqrt (h : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => sqrt (f x)) s x :=
  h.sqrt
#align continuous_within_at.sqrt ContinuousWithinAt.sqrt
-/

#print ContinuousAt.sqrt /-
theorem ContinuousAt.sqrt (h : ContinuousAt f x) : ContinuousAt (fun x => sqrt (f x)) x :=
  h.sqrt
#align continuous_at.sqrt ContinuousAt.sqrt
-/

#print ContinuousOn.sqrt /-
theorem ContinuousOn.sqrt (h : ContinuousOn f s) : ContinuousOn (fun x => sqrt (f x)) s :=
  fun x hx => (h x hx).sqrt
#align continuous_on.sqrt ContinuousOn.sqrt
-/

#print Continuous.sqrt /-
@[continuity]
theorem Continuous.sqrt (h : Continuous f) : Continuous fun x => sqrt (f x) :=
  continuous_sqrt.comp h
#align continuous.sqrt Continuous.sqrt
-/

