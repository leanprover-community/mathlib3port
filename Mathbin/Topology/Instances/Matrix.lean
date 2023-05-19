/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Eric Wieser

! This file was ported from Lean 3 source module topology.instances.matrix
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.InfiniteSum.Basic
import Mathbin.Topology.Algebra.Ring.Basic
import Mathbin.Topology.Algebra.Star
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.Trace

/-!
# Topological properties of matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is a place to collect topological results about matrices.

## Main definitions:

* `matrix.topological_ring`: square matrices form a topological ring

## Main results

* Continuity:
  * `continuous.matrix_det`: the determinant is continuous over a topological ring.
  * `continuous.matrix_adjugate`: the adjugate is continuous over a topological ring.
* Infinite sums
  * `matrix.transpose_tsum`: transpose commutes with infinite sums
  * `matrix.diagonal_tsum`: diagonal commutes with infinite sums
  * `matrix.block_diagonal_tsum`: block diagonal commutes with infinite sums
  * `matrix.block_diagonal'_tsum`: non-uniform block diagonal commutes with infinite sums
-/


open Matrix

open Matrix

variable {X α l m n p S R : Type _} {m' n' : l → Type _}

instance [TopologicalSpace R] : TopologicalSpace (Matrix m n R) :=
  Pi.topologicalSpace

instance [TopologicalSpace R] [T2Space R] : T2Space (Matrix m n R) :=
  Pi.t2Space

/-! ### Lemmas about continuity of operations -/


section Continuity

variable [TopologicalSpace X] [TopologicalSpace R]

instance [SMul α R] [ContinuousConstSMul α R] : ContinuousConstSMul α (Matrix m n R) :=
  Pi.continuousConstSMul

instance [TopologicalSpace α] [SMul α R] [ContinuousSMul α R] : ContinuousSMul α (Matrix m n R) :=
  Pi.continuousSMul

instance [Add R] [ContinuousAdd R] : ContinuousAdd (Matrix m n R) :=
  Pi.continuousAdd

instance [Neg R] [ContinuousNeg R] : ContinuousNeg (Matrix m n R) :=
  Pi.continuousNeg

instance [AddGroup R] [TopologicalAddGroup R] : TopologicalAddGroup (Matrix m n R) :=
  Pi.topologicalAddGroup

/- warning: continuous_matrix -> continuous_matrix is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : TopologicalSpace.{u1} α] {f : α -> (Matrix.{u2, u3, u4} m n R)}, (forall (i : m) (j : n), Continuous.{u1, u4} α R _inst_3 _inst_2 (fun (a : α) => f a i j)) -> (Continuous.{u1, max u2 u3 u4} α (Matrix.{u2, u3, u4} m n R) _inst_3 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) f)
but is expected to have type
  forall {α : Type.{u4}} {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalSpace.{u4} α] {f : α -> (Matrix.{u3, u2, u1} m n R)}, (forall (i : m) (j : n), Continuous.{u4, u1} α R _inst_3 _inst_2 (fun (a : α) => f a i j)) -> (Continuous.{u4, max (max u3 u2) u1} α (Matrix.{u3, u2, u1} m n R) _inst_3 (instTopologicalSpaceMatrix.{u3, u2, u1} m n R _inst_2) f)
Case conversion may be inaccurate. Consider using '#align continuous_matrix continuous_matrixₓ'. -/
/-- To show a function into matrices is continuous it suffices to show the coefficients of the
resulting matrix are continuous -/
@[continuity]
theorem continuous_matrix [TopologicalSpace α] {f : α → Matrix m n R}
    (h : ∀ i j, Continuous fun a => f a i j) : Continuous f :=
  continuous_pi fun _ => continuous_pi fun j => h _ _
#align continuous_matrix continuous_matrix

/- warning: continuous.matrix_elem -> Continuous.matrix_elem is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] {A : X -> (Matrix.{u2, u3, u4} m n R)}, (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) A) -> (forall (i : m) (j : n), Continuous.{u1, u4} X R _inst_1 _inst_2 (fun (x : X) => A x i j))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] {A : X -> (Matrix.{u4, u3, u2} m n R)}, (Continuous.{u1, max (max u4 u3) u2} X (Matrix.{u4, u3, u2} m n R) _inst_1 (instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_2) A) -> (forall (i : m) (j : n), Continuous.{u1, u2} X R _inst_1 _inst_2 (fun (x : X) => A x i j))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_elem Continuous.matrix_elemₓ'. -/
theorem Continuous.matrix_elem {A : X → Matrix m n R} (hA : Continuous A) (i : m) (j : n) :
    Continuous fun x => A x i j :=
  (continuous_apply_apply i j).comp hA
#align continuous.matrix_elem Continuous.matrix_elem

/- warning: continuous.matrix_map -> Continuous.matrix_map is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {S : Type.{u4}} {R : Type.{u5}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u5} R] [_inst_3 : TopologicalSpace.{u4} S] {A : X -> (Matrix.{u2, u3, u4} m n S)} {f : S -> R}, (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n S) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n S _inst_3) A) -> (Continuous.{u4, u5} S R _inst_3 _inst_2 f) -> (Continuous.{u1, max u2 u3 u5} X (Matrix.{u2, u3, u5} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u5} m n R _inst_2) (fun (x : X) => Matrix.map.{u4, u5, u2, u3} m n S R (A x) f))
but is expected to have type
  forall {X : Type.{u2}} {m : Type.{u4}} {n : Type.{u3}} {S : Type.{u5}} {R : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalSpace.{u5} S] {A : X -> (Matrix.{u4, u3, u5} m n S)} {f : S -> R}, (Continuous.{u2, max (max u4 u3) u5} X (Matrix.{u4, u3, u5} m n S) _inst_1 (instTopologicalSpaceMatrix.{u4, u3, u5} m n S _inst_3) A) -> (Continuous.{u5, u1} S R _inst_3 _inst_2 f) -> (Continuous.{u2, max (max u4 u3) u1} X (Matrix.{u4, u3, u1} m n R) _inst_1 (instTopologicalSpaceMatrix.{u4, u3, u1} m n R _inst_2) (fun (x : X) => Matrix.map.{u5, u1, u4, u3} m n S R (A x) f))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_map Continuous.matrix_mapₓ'. -/
@[continuity]
theorem Continuous.matrix_map [TopologicalSpace S] {A : X → Matrix m n S} {f : S → R}
    (hA : Continuous A) (hf : Continuous f) : Continuous fun x => (A x).map f :=
  continuous_matrix fun i j => hf.comp <| hA.matrix_elem _ _
#align continuous.matrix_map Continuous.matrix_map

/- warning: continuous.matrix_transpose -> Continuous.matrix_transpose is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] {A : X -> (Matrix.{u2, u3, u4} m n R)}, (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) A) -> (Continuous.{u1, max u3 u2 u4} X (Matrix.{u3, u2, u4} n m R) _inst_1 (Matrix.topologicalSpace.{u3, u2, u4} n m R _inst_2) (fun (x : X) => Matrix.transpose.{u4, u2, u3} m n R (A x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] {A : X -> (Matrix.{u4, u3, u2} m n R)}, (Continuous.{u1, max (max u4 u3) u2} X (Matrix.{u4, u3, u2} m n R) _inst_1 (instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_2) A) -> (Continuous.{u1, max (max u3 u4) u2} X (Matrix.{u3, u4, u2} n m R) _inst_1 (instTopologicalSpaceMatrix.{u3, u4, u2} n m R _inst_2) (fun (x : X) => Matrix.transpose.{u2, u4, u3} m n R (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_transpose Continuous.matrix_transposeₓ'. -/
@[continuity]
theorem Continuous.matrix_transpose {A : X → Matrix m n R} (hA : Continuous A) :
    Continuous fun x => (A x)ᵀ :=
  continuous_matrix fun i j => hA.matrix_elem j i
#align continuous.matrix_transpose Continuous.matrix_transpose

/- warning: continuous.matrix_conj_transpose -> Continuous.matrix_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : Star.{u4} R] [_inst_4 : ContinuousStar.{u4} R _inst_2 _inst_3] {A : X -> (Matrix.{u2, u3, u4} m n R)}, (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) A) -> (Continuous.{u1, max u3 u2 u4} X (Matrix.{u3, u2, u4} n m R) _inst_1 (Matrix.topologicalSpace.{u3, u2, u4} n m R _inst_2) (fun (x : X) => Matrix.conjTranspose.{u4, u2, u3} m n R _inst_3 (A x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : Star.{u4} R] [_inst_4 : ContinuousStar.{u4} R _inst_2 _inst_3] {A : X -> (Matrix.{u3, u2, u4} m n R)}, (Continuous.{u1, max (max u3 u2) u4} X (Matrix.{u3, u2, u4} m n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u2, u4} m n R _inst_2) A) -> (Continuous.{u1, max (max u2 u3) u4} X (Matrix.{u2, u3, u4} n m R) _inst_1 (instTopologicalSpaceMatrix.{u2, u3, u4} n m R _inst_2) (fun (x : X) => Matrix.conjTranspose.{u4, u3, u2} m n R _inst_3 (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_conj_transpose Continuous.matrix_conjTransposeₓ'. -/
theorem Continuous.matrix_conjTranspose [Star R] [ContinuousStar R] {A : X → Matrix m n R}
    (hA : Continuous A) : Continuous fun x => (A x)ᴴ :=
  hA.matrix_transpose.matrix_map continuous_star
#align continuous.matrix_conj_transpose Continuous.matrix_conjTranspose

instance [Star R] [ContinuousStar R] : ContinuousStar (Matrix m m R) :=
  ⟨continuous_id.matrix_conjTranspose⟩

/- warning: continuous.matrix_col -> Continuous.matrix_col is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} R] {A : X -> n -> R}, (Continuous.{u1, max u2 u3} X (n -> R) _inst_1 (Pi.topologicalSpace.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) A) -> (Continuous.{u1, max u2 u3} X (Matrix.{u2, 0, u3} n Unit R) _inst_1 (Matrix.topologicalSpace.{u2, 0, u3} n Unit R _inst_2) (fun (x : X) => Matrix.col.{u3, u2} n R (A x)))
but is expected to have type
  forall {X : Type.{u3}} {n : Type.{u2}} {R : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u1} R] {A : X -> n -> R}, (Continuous.{u3, max u2 u1} X (n -> R) _inst_1 (Pi.topologicalSpace.{u2, u1} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) A) -> (Continuous.{u3, max u2 u1} X (Matrix.{u2, 0, u1} n Unit R) _inst_1 (instTopologicalSpaceMatrix.{u2, 0, u1} n Unit R _inst_2) (fun (x : X) => Matrix.col.{u1, u2} n R (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_col Continuous.matrix_colₓ'. -/
@[continuity]
theorem Continuous.matrix_col {A : X → n → R} (hA : Continuous A) : Continuous fun x => col (A x) :=
  continuous_matrix fun i j => (continuous_apply _).comp hA
#align continuous.matrix_col Continuous.matrix_col

/- warning: continuous.matrix_row -> Continuous.matrix_row is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} R] {A : X -> n -> R}, (Continuous.{u1, max u2 u3} X (n -> R) _inst_1 (Pi.topologicalSpace.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) A) -> (Continuous.{u1, max u2 u3} X (Matrix.{0, u2, u3} Unit n R) _inst_1 (Matrix.topologicalSpace.{0, u2, u3} Unit n R _inst_2) (fun (x : X) => Matrix.row.{u3, u2} n R (A x)))
but is expected to have type
  forall {X : Type.{u3}} {n : Type.{u2}} {R : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u1} R] {A : X -> n -> R}, (Continuous.{u3, max u2 u1} X (n -> R) _inst_1 (Pi.topologicalSpace.{u2, u1} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) A) -> (Continuous.{u3, max u2 u1} X (Matrix.{0, u2, u1} Unit n R) _inst_1 (instTopologicalSpaceMatrix.{0, u2, u1} Unit n R _inst_2) (fun (x : X) => Matrix.row.{u1, u2} n R (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_row Continuous.matrix_rowₓ'. -/
@[continuity]
theorem Continuous.matrix_row {A : X → n → R} (hA : Continuous A) : Continuous fun x => row (A x) :=
  continuous_matrix fun i j => (continuous_apply _).comp hA
#align continuous.matrix_row Continuous.matrix_row

#print Continuous.matrix_diagonal /-
@[continuity]
theorem Continuous.matrix_diagonal [Zero R] [DecidableEq n] {A : X → n → R} (hA : Continuous A) :
    Continuous fun x => diagonal (A x) :=
  continuous_matrix fun i j => ((continuous_apply i).comp hA).if_const _ continuous_zero
#align continuous.matrix_diagonal Continuous.matrix_diagonal
-/

/- warning: continuous.matrix_dot_product -> Continuous.matrix_dotProduct is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} R] [_inst_3 : Fintype.{u2} n] [_inst_4 : Mul.{u3} R] [_inst_5 : AddCommMonoid.{u3} R] [_inst_6 : ContinuousAdd.{u3} R _inst_2 (AddZeroClass.toHasAdd.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_5)))] [_inst_7 : ContinuousMul.{u3} R _inst_2 _inst_4] {A : X -> n -> R} {B : X -> n -> R}, (Continuous.{u1, max u2 u3} X (n -> R) _inst_1 (Pi.topologicalSpace.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) A) -> (Continuous.{u1, max u2 u3} X (n -> R) _inst_1 (Pi.topologicalSpace.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) B) -> (Continuous.{u1, u3} X R _inst_1 _inst_2 (fun (x : X) => Matrix.dotProduct.{u3, u2} n R _inst_3 _inst_4 _inst_5 (A x) (B x)))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : Fintype.{u3} n] [_inst_4 : Mul.{u2} R] [_inst_5 : AddCommMonoid.{u2} R] [_inst_6 : ContinuousAdd.{u2} R _inst_2 (AddZeroClass.toAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_5)))] [_inst_7 : ContinuousMul.{u2} R _inst_2 _inst_4] {A : X -> n -> R} {B : X -> n -> R}, (Continuous.{u1, max u3 u2} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u2} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) A) -> (Continuous.{u1, max u3 u2} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u2} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) B) -> (Continuous.{u1, u2} X R _inst_1 _inst_2 (fun (x : X) => Matrix.dotProduct.{u2, u3} n R _inst_3 _inst_4 _inst_5 (A x) (B x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_dot_product Continuous.matrix_dotProductₓ'. -/
@[continuity]
theorem Continuous.matrix_dotProduct [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    [ContinuousMul R] {A : X → n → R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => dotProduct (A x) (B x) :=
  continuous_finset_sum _ fun i _ =>
    ((continuous_apply i).comp hA).mul ((continuous_apply i).comp hB)
#align continuous.matrix_dot_product Continuous.matrix_dotProduct

/- warning: continuous.matrix_mul -> Continuous.matrix_mul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {p : Type.{u4}} {R : Type.{u5}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u5} R] [_inst_3 : Fintype.{u3} n] [_inst_4 : Mul.{u5} R] [_inst_5 : AddCommMonoid.{u5} R] [_inst_6 : ContinuousAdd.{u5} R _inst_2 (AddZeroClass.toHasAdd.{u5} R (AddMonoid.toAddZeroClass.{u5} R (AddCommMonoid.toAddMonoid.{u5} R _inst_5)))] [_inst_7 : ContinuousMul.{u5} R _inst_2 _inst_4] {A : X -> (Matrix.{u2, u3, u5} m n R)} {B : X -> (Matrix.{u3, u4, u5} n p R)}, (Continuous.{u1, max u2 u3 u5} X (Matrix.{u2, u3, u5} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u5} m n R _inst_2) A) -> (Continuous.{u1, max u3 u4 u5} X (Matrix.{u3, u4, u5} n p R) _inst_1 (Matrix.topologicalSpace.{u3, u4, u5} n p R _inst_2) B) -> (Continuous.{u1, max u2 u4 u5} X (Matrix.{u2, u4, u5} m p R) _inst_1 (Matrix.topologicalSpace.{u2, u4, u5} m p R _inst_2) (fun (x : X) => Matrix.mul.{u5, u2, u3, u4} m n p R _inst_3 _inst_4 _inst_5 (A x) (B x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u5}} {p : Type.{u2}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : Fintype.{u5} n] [_inst_4 : Mul.{u4} R] [_inst_5 : AddCommMonoid.{u4} R] [_inst_6 : ContinuousAdd.{u4} R _inst_2 (AddZeroClass.toAdd.{u4} R (AddMonoid.toAddZeroClass.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_5)))] [_inst_7 : ContinuousMul.{u4} R _inst_2 _inst_4] {A : X -> (Matrix.{u3, u5, u4} m n R)} {B : X -> (Matrix.{u5, u2, u4} n p R)}, (Continuous.{u1, max (max u3 u5) u4} X (Matrix.{u3, u5, u4} m n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u5, u4} m n R _inst_2) A) -> (Continuous.{u1, max (max u5 u2) u4} X (Matrix.{u5, u2, u4} n p R) _inst_1 (instTopologicalSpaceMatrix.{u5, u2, u4} n p R _inst_2) B) -> (Continuous.{u1, max (max u3 u4) u2} X (Matrix.{u3, u2, u4} m p R) _inst_1 (instTopologicalSpaceMatrix.{u3, u2, u4} m p R _inst_2) (fun (x : X) => Matrix.mul.{u4, u3, u5, u2} m n p R _inst_3 _inst_4 _inst_5 (A x) (B x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_mul Continuous.matrix_mulₓ'. -/
/-- For square matrices the usual `continuous_mul` can be used. -/
@[continuity]
theorem Continuous.matrix_mul [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    [ContinuousMul R] {A : X → Matrix m n R} {B : X → Matrix n p R} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => (A x).mul (B x) :=
  continuous_matrix fun i j =>
    continuous_finset_sum _ fun k _ => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)
#align continuous.matrix_mul Continuous.matrix_mul

instance [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R] [ContinuousMul R] :
    ContinuousMul (Matrix n n R) :=
  ⟨continuous_fst.matrix_mul continuous_snd⟩

instance [Fintype n] [NonUnitalNonAssocSemiring R] [TopologicalSemiring R] :
    TopologicalSemiring (Matrix n n R) where

instance [Fintype n] [NonUnitalNonAssocRing R] [TopologicalRing R] : TopologicalRing (Matrix n n R)
    where

/- warning: continuous.matrix_vec_mul_vec -> Continuous.matrix_vecMulVec is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : Mul.{u4} R] [_inst_4 : ContinuousMul.{u4} R _inst_2 _inst_3] {A : X -> m -> R} {B : X -> n -> R}, (Continuous.{u1, max u2 u4} X (m -> R) _inst_1 (Pi.topologicalSpace.{u2, u4} m (fun (ᾰ : m) => R) (fun (a : m) => _inst_2)) A) -> (Continuous.{u1, max u3 u4} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u4} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) B) -> (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) (fun (x : X) => Matrix.vecMulVec.{u4, u2, u3} m n R _inst_3 (A x) (B x)))
but is expected to have type
  forall {X : Type.{u3}} {m : Type.{u2}} {n : Type.{u1}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : Mul.{u4} R] [_inst_4 : ContinuousMul.{u4} R _inst_2 _inst_3] {A : X -> m -> R} {B : X -> n -> R}, (Continuous.{u3, max u2 u4} X (m -> R) _inst_1 (Pi.topologicalSpace.{u2, u4} m (fun (ᾰ : m) => R) (fun (a : m) => _inst_2)) A) -> (Continuous.{u3, max u1 u4} X (n -> R) _inst_1 (Pi.topologicalSpace.{u1, u4} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) B) -> (Continuous.{u3, max (max u1 u2) u4} X (Matrix.{u2, u1, u4} m n R) _inst_1 (instTopologicalSpaceMatrix.{u2, u1, u4} m n R _inst_2) (fun (x : X) => Matrix.vecMulVec.{u4, u2, u1} m n R _inst_3 (A x) (B x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_vec_mul_vec Continuous.matrix_vecMulVecₓ'. -/
@[continuity]
theorem Continuous.matrix_vecMulVec [Mul R] [ContinuousMul R] {A : X → m → R} {B : X → n → R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => vecMulVec (A x) (B x) :=
  continuous_matrix fun i j => ((continuous_apply _).comp hA).mul ((continuous_apply _).comp hB)
#align continuous.matrix_vec_mul_vec Continuous.matrix_vecMulVec

/- warning: continuous.matrix_mul_vec -> Continuous.matrix_mulVec is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : NonUnitalNonAssocSemiring.{u4} R] [_inst_4 : ContinuousAdd.{u4} R _inst_2 (Distrib.toHasAdd.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R _inst_3))] [_inst_5 : ContinuousMul.{u4} R _inst_2 (Distrib.toHasMul.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R _inst_3))] [_inst_6 : Fintype.{u3} n] {A : X -> (Matrix.{u2, u3, u4} m n R)} {B : X -> n -> R}, (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) A) -> (Continuous.{u1, max u3 u4} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u4} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) B) -> (Continuous.{u1, max u2 u4} X (m -> R) _inst_1 (Pi.topologicalSpace.{u2, u4} m (fun (ᾰ : m) => R) (fun (a : m) => _inst_2)) (fun (x : X) => Matrix.mulVec.{u4, u2, u3} m n R _inst_3 _inst_6 (A x) (B x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : NonUnitalNonAssocSemiring.{u4} R] [_inst_4 : ContinuousAdd.{u4} R _inst_2 (Distrib.toAdd.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R _inst_3))] [_inst_5 : ContinuousMul.{u4} R _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} R _inst_3)] [_inst_6 : Fintype.{u3} n] {A : X -> (Matrix.{u2, u3, u4} m n R)} {B : X -> n -> R}, (Continuous.{u1, max (max u2 u3) u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (instTopologicalSpaceMatrix.{u2, u3, u4} m n R _inst_2) A) -> (Continuous.{u1, max u3 u4} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u4} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) B) -> (Continuous.{u1, max u2 u4} X (m -> R) _inst_1 (Pi.topologicalSpace.{u2, u4} m (fun (ᾰ : m) => R) (fun (a : m) => _inst_2)) (fun (x : X) => Matrix.mulVec.{u4, u2, u3} m n R _inst_3 _inst_6 (A x) (B x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_mul_vec Continuous.matrix_mulVecₓ'. -/
@[continuity]
theorem Continuous.matrix_mulVec [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    [Fintype n] {A : X → Matrix m n R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).mulVec (B x) :=
  continuous_pi fun i => ((continuous_apply i).comp hA).matrix_dotProduct hB
#align continuous.matrix_mul_vec Continuous.matrix_mulVec

/- warning: continuous.matrix_vec_mul -> Continuous.matrix_vecMul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : NonUnitalNonAssocSemiring.{u4} R] [_inst_4 : ContinuousAdd.{u4} R _inst_2 (Distrib.toHasAdd.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R _inst_3))] [_inst_5 : ContinuousMul.{u4} R _inst_2 (Distrib.toHasMul.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R _inst_3))] [_inst_6 : Fintype.{u2} m] {A : X -> m -> R} {B : X -> (Matrix.{u2, u3, u4} m n R)}, (Continuous.{u1, max u2 u4} X (m -> R) _inst_1 (Pi.topologicalSpace.{u2, u4} m (fun (ᾰ : m) => R) (fun (a : m) => _inst_2)) A) -> (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) B) -> (Continuous.{u1, max u3 u4} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u4} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) (fun (x : X) => Matrix.vecMul.{u4, u2, u3} m n R _inst_3 _inst_6 (A x) (B x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : NonUnitalNonAssocSemiring.{u4} R] [_inst_4 : ContinuousAdd.{u4} R _inst_2 (Distrib.toAdd.{u4} R (NonUnitalNonAssocSemiring.toDistrib.{u4} R _inst_3))] [_inst_5 : ContinuousMul.{u4} R _inst_2 (NonUnitalNonAssocSemiring.toMul.{u4} R _inst_3)] [_inst_6 : Fintype.{u3} m] {A : X -> m -> R} {B : X -> (Matrix.{u3, u2, u4} m n R)}, (Continuous.{u1, max u3 u4} X (m -> R) _inst_1 (Pi.topologicalSpace.{u3, u4} m (fun (ᾰ : m) => R) (fun (a : m) => _inst_2)) A) -> (Continuous.{u1, max (max u3 u2) u4} X (Matrix.{u3, u2, u4} m n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u2, u4} m n R _inst_2) B) -> (Continuous.{u1, max u2 u4} X (n -> R) _inst_1 (Pi.topologicalSpace.{u2, u4} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) (fun (x : X) => Matrix.vecMul.{u4, u3, u2} m n R _inst_3 _inst_6 (A x) (B x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_vec_mul Continuous.matrix_vecMulₓ'. -/
@[continuity]
theorem Continuous.matrix_vecMul [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    [Fintype m] {A : X → m → R} {B : X → Matrix m n R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => vecMul (A x) (B x) :=
  continuous_pi fun i => hA.matrix_dotProduct <| continuous_pi fun j => hB.matrix_elem _ _
#align continuous.matrix_vec_mul Continuous.matrix_vecMul

/- warning: continuous.matrix_submatrix -> Continuous.matrix_submatrix is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {p : Type.{u5}} {R : Type.{u6}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u6} R] {A : X -> (Matrix.{u2, u4, u6} l n R)}, (Continuous.{u1, max u2 u4 u6} X (Matrix.{u2, u4, u6} l n R) _inst_1 (Matrix.topologicalSpace.{u2, u4, u6} l n R _inst_2) A) -> (forall (e₁ : m -> l) (e₂ : p -> n), Continuous.{u1, max u3 u5 u6} X (Matrix.{u3, u5, u6} m p R) _inst_1 (Matrix.topologicalSpace.{u3, u5, u6} m p R _inst_2) (fun (x : X) => Matrix.submatrix.{u6, u3, u2, u4, u5} m l n p R (A x) e₁ e₂))
but is expected to have type
  forall {X : Type.{u3}} {l : Type.{u6}} {m : Type.{u1}} {n : Type.{u5}} {p : Type.{u2}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u4} R] {A : X -> (Matrix.{u6, u5, u4} l n R)}, (Continuous.{u3, max (max u6 u5) u4} X (Matrix.{u6, u5, u4} l n R) _inst_1 (instTopologicalSpaceMatrix.{u6, u5, u4} l n R _inst_2) A) -> (forall (e₁ : m -> l) (e₂ : p -> n), Continuous.{u3, max (max u4 u2) u1} X (Matrix.{u1, u2, u4} m p R) _inst_1 (instTopologicalSpaceMatrix.{u1, u2, u4} m p R _inst_2) (fun (x : X) => Matrix.submatrix.{u4, u1, u6, u5, u2} m l n p R (A x) e₁ e₂))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_submatrix Continuous.matrix_submatrixₓ'. -/
@[continuity]
theorem Continuous.matrix_submatrix {A : X → Matrix l n R} (hA : Continuous A) (e₁ : m → l)
    (e₂ : p → n) : Continuous fun x => (A x).submatrix e₁ e₂ :=
  continuous_matrix fun i j => hA.matrix_elem _ _
#align continuous.matrix_submatrix Continuous.matrix_submatrix

/- warning: continuous.matrix_reindex -> Continuous.matrix_reindex is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {p : Type.{u5}} {R : Type.{u6}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u6} R] {A : X -> (Matrix.{u2, u4, u6} l n R)}, (Continuous.{u1, max u2 u4 u6} X (Matrix.{u2, u4, u6} l n R) _inst_1 (Matrix.topologicalSpace.{u2, u4, u6} l n R _inst_2) A) -> (forall (e₁ : Equiv.{succ u2, succ u3} l m) (e₂ : Equiv.{succ u4, succ u5} n p), Continuous.{u1, max u3 u5 u6} X (Matrix.{u3, u5, u6} m p R) _inst_1 (Matrix.topologicalSpace.{u3, u5, u6} m p R _inst_2) (fun (x : X) => coeFn.{max 1 (max (succ (max u2 u4 u6)) (succ (max u3 u5 u6))) (succ (max u3 u5 u6)) (succ (max u2 u4 u6)), max (succ (max u2 u4 u6)) (succ (max u3 u5 u6))} (Equiv.{succ (max u2 u4 u6), succ (max u3 u5 u6)} (Matrix.{u2, u4, u6} l n R) (Matrix.{u3, u5, u6} m p R)) (fun (_x : Equiv.{succ (max u2 u4 u6), succ (max u3 u5 u6)} (Matrix.{u2, u4, u6} l n R) (Matrix.{u3, u5, u6} m p R)) => (Matrix.{u2, u4, u6} l n R) -> (Matrix.{u3, u5, u6} m p R)) (Equiv.hasCoeToFun.{succ (max u2 u4 u6), succ (max u3 u5 u6)} (Matrix.{u2, u4, u6} l n R) (Matrix.{u3, u5, u6} m p R)) (Matrix.reindex.{u6, u3, u2, u4, u5} m l n p R e₁ e₂) (A x)))
but is expected to have type
  forall {X : Type.{u3}} {l : Type.{u6}} {m : Type.{u2}} {n : Type.{u5}} {p : Type.{u1}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u4} R] {A : X -> (Matrix.{u6, u5, u4} l n R)}, (Continuous.{u3, max (max u6 u5) u4} X (Matrix.{u6, u5, u4} l n R) _inst_1 (instTopologicalSpaceMatrix.{u6, u5, u4} l n R _inst_2) A) -> (forall (e₁ : Equiv.{succ u6, succ u2} l m) (e₂ : Equiv.{succ u5, succ u1} n p), Continuous.{u3, max (max u2 u1) u4} X (Matrix.{u2, u1, u4} m p R) _inst_1 (instTopologicalSpaceMatrix.{u2, u1, u4} m p R _inst_2) (fun (x : X) => FunLike.coe.{max (max (max (max (succ u6) (succ u2)) (succ u5)) (succ u1)) (succ u4), max (max (succ u6) (succ u5)) (succ u4), max (max (succ u2) (succ u1)) (succ u4)} (Equiv.{max (max (succ u4) (succ u5)) (succ u6), max (max (succ u4) (succ u1)) (succ u2)} (Matrix.{u6, u5, u4} l n R) (Matrix.{u2, u1, u4} m p R)) (Matrix.{u6, u5, u4} l n R) (fun (_x : Matrix.{u6, u5, u4} l n R) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Matrix.{u6, u5, u4} l n R) => Matrix.{u2, u1, u4} m p R) _x) (Equiv.instFunLikeEquiv.{max (max (succ u6) (succ u5)) (succ u4), max (max (succ u2) (succ u1)) (succ u4)} (Matrix.{u6, u5, u4} l n R) (Matrix.{u2, u1, u4} m p R)) (Matrix.reindex.{u4, u2, u6, u5, u1} m l n p R e₁ e₂) (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_reindex Continuous.matrix_reindexₓ'. -/
@[continuity]
theorem Continuous.matrix_reindex {A : X → Matrix l n R} (hA : Continuous A) (e₁ : l ≃ m)
    (e₂ : n ≃ p) : Continuous fun x => reindex e₁ e₂ (A x) :=
  hA.matrix_submatrix _ _
#align continuous.matrix_reindex Continuous.matrix_reindex

/- warning: continuous.matrix_diag -> Continuous.matrix_diag is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} R] {A : X -> (Matrix.{u2, u2, u3} n n R)}, (Continuous.{u1, max u2 u3} X (Matrix.{u2, u2, u3} n n R) _inst_1 (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_2) A) -> (Continuous.{u1, max u2 u3} X (n -> R) _inst_1 (Pi.topologicalSpace.{u2, u3} n (fun (i : n) => R) (fun (a : n) => _inst_2)) (fun (x : X) => Matrix.diag.{u3, u2} n R (A x)))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] {A : X -> (Matrix.{u3, u3, u2} n n R)}, (Continuous.{u1, max u3 u2} X (Matrix.{u3, u3, u2} n n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_2) A) -> (Continuous.{u1, max u3 u2} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u2} n (fun (i : n) => R) (fun (a : n) => _inst_2)) (fun (x : X) => Matrix.diag.{u2, u3} n R (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_diag Continuous.matrix_diagₓ'. -/
@[continuity]
theorem Continuous.matrix_diag {A : X → Matrix n n R} (hA : Continuous A) :
    Continuous fun x => Matrix.diag (A x) :=
  continuous_pi fun _ => hA.matrix_elem _ _
#align continuous.matrix_diag Continuous.matrix_diag

/- warning: continuous_matrix_diag -> continuous_matrix_diag is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} R], Continuous.{max u1 u2, max u1 u2} (Matrix.{u1, u1, u2} n n R) (n -> R) (Matrix.topologicalSpace.{u1, u1, u2} n n R _inst_2) (Pi.topologicalSpace.{u1, u2} n (fun (i : n) => R) (fun (a : n) => _inst_2)) (Matrix.diag.{u2, u1} n R)
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} R], Continuous.{max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n R) (n -> R) (instTopologicalSpaceMatrix.{u2, u2, u1} n n R _inst_2) (Pi.topologicalSpace.{u2, u1} n (fun (i : n) => R) (fun (a : n) => _inst_2)) (Matrix.diag.{u1, u2} n R)
Case conversion may be inaccurate. Consider using '#align continuous_matrix_diag continuous_matrix_diagₓ'. -/
-- note this doesn't elaborate well from the above
theorem continuous_matrix_diag : Continuous (Matrix.diag : Matrix n n R → n → R) :=
  show Continuous fun x : Matrix n n R => Matrix.diag x from continuous_id.matrix_diag
#align continuous_matrix_diag continuous_matrix_diag

/- warning: continuous.matrix_trace -> Continuous.matrix_trace is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} R] [_inst_3 : Fintype.{u2} n] [_inst_4 : AddCommMonoid.{u3} R] [_inst_5 : ContinuousAdd.{u3} R _inst_2 (AddZeroClass.toHasAdd.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_4)))] {A : X -> (Matrix.{u2, u2, u3} n n R)}, (Continuous.{u1, max u2 u3} X (Matrix.{u2, u2, u3} n n R) _inst_1 (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_2) A) -> (Continuous.{u1, u3} X R _inst_1 _inst_2 (fun (x : X) => Matrix.trace.{u2, u3} n R _inst_3 _inst_4 (A x)))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : Fintype.{u3} n] [_inst_4 : AddCommMonoid.{u2} R] [_inst_5 : ContinuousAdd.{u2} R _inst_2 (AddZeroClass.toAdd.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_4)))] {A : X -> (Matrix.{u3, u3, u2} n n R)}, (Continuous.{u1, max u3 u2} X (Matrix.{u3, u3, u2} n n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_2) A) -> (Continuous.{u1, u2} X R _inst_1 _inst_2 (fun (x : X) => Matrix.trace.{u3, u2} n R _inst_3 _inst_4 (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_trace Continuous.matrix_traceₓ'. -/
@[continuity]
theorem Continuous.matrix_trace [Fintype n] [AddCommMonoid R] [ContinuousAdd R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => trace (A x) :=
  continuous_finset_sum _ fun i hi => hA.matrix_elem _ _
#align continuous.matrix_trace Continuous.matrix_trace

/- warning: continuous.matrix_det -> Continuous.matrix_det is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} R] [_inst_3 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] [_inst_5 : CommRing.{u3} R] [_inst_6 : TopologicalRing.{u3} R _inst_2 (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5)))] {A : X -> (Matrix.{u2, u2, u3} n n R)}, (Continuous.{u1, max u2 u3} X (Matrix.{u2, u2, u3} n n R) _inst_1 (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_2) A) -> (Continuous.{u1, u3} X R _inst_1 _inst_2 (fun (x : X) => Matrix.det.{u3, u2} n (fun (a : n) (b : n) => _inst_4 a b) _inst_3 R _inst_5 (A x)))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : Fintype.{u3} n] [_inst_4 : DecidableEq.{succ u3} n] [_inst_5 : CommRing.{u2} R] [_inst_6 : TopologicalRing.{u2} R _inst_2 (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5)))] {A : X -> (Matrix.{u3, u3, u2} n n R)}, (Continuous.{u1, max u3 u2} X (Matrix.{u3, u3, u2} n n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_2) A) -> (Continuous.{u1, u2} X R _inst_1 _inst_2 (fun (x : X) => Matrix.det.{u2, u3} n (fun (a : n) (b : n) => _inst_4 a b) _inst_3 R _inst_5 (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_det Continuous.matrix_detₓ'. -/
@[continuity]
theorem Continuous.matrix_det [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => (A x).det :=
  by
  simp_rw [Matrix.det_apply]
  refine' continuous_finset_sum _ fun l _ => Continuous.const_smul _ _
  refine' continuous_finset_prod _ fun l _ => hA.matrix_elem _ _
#align continuous.matrix_det Continuous.matrix_det

/- warning: continuous.matrix_update_column -> Continuous.matrix_updateColumn is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : DecidableEq.{succ u3} n] (i : n) {A : X -> (Matrix.{u2, u3, u4} m n R)} {B : X -> m -> R}, (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) A) -> (Continuous.{u1, max u2 u4} X (m -> R) _inst_1 (Pi.topologicalSpace.{u2, u4} m (fun (ᾰ : m) => R) (fun (a : m) => _inst_2)) B) -> (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) (fun (x : X) => Matrix.updateColumn.{u4, u2, u3} m n R (fun (a : n) (b : n) => _inst_3 a b) (A x) i (B x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u4}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : DecidableEq.{succ u4} n] (i : n) {A : X -> (Matrix.{u3, u4, u2} m n R)} {B : X -> m -> R}, (Continuous.{u1, max (max u3 u4) u2} X (Matrix.{u3, u4, u2} m n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u4, u2} m n R _inst_2) A) -> (Continuous.{u1, max u3 u2} X (m -> R) _inst_1 (Pi.topologicalSpace.{u3, u2} m (fun (ᾰ : m) => R) (fun (a : m) => _inst_2)) B) -> (Continuous.{u1, max (max u3 u4) u2} X (Matrix.{u3, u4, u2} m n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u4, u2} m n R _inst_2) (fun (x : X) => Matrix.updateColumn.{u2, u3, u4} m n R (fun (a : n) (b : n) => _inst_3 a b) (A x) i (B x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_update_column Continuous.matrix_updateColumnₓ'. -/
@[continuity]
theorem Continuous.matrix_updateColumn [DecidableEq n] (i : n) {A : X → Matrix m n R}
    {B : X → m → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).updateColumn i (B x) :=
  continuous_matrix fun j k =>
    (continuous_apply k).comp <|
      ((continuous_apply _).comp hA).update i ((continuous_apply _).comp hB)
#align continuous.matrix_update_column Continuous.matrix_updateColumn

/- warning: continuous.matrix_update_row -> Continuous.matrix_updateRow is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] [_inst_3 : DecidableEq.{succ u2} m] (i : m) {A : X -> (Matrix.{u2, u3, u4} m n R)} {B : X -> n -> R}, (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) A) -> (Continuous.{u1, max u3 u4} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u4} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) B) -> (Continuous.{u1, max u2 u3 u4} X (Matrix.{u2, u3, u4} m n R) _inst_1 (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_2) (fun (x : X) => Matrix.updateRow.{u4, u2, u3} m n R (fun (a : m) (b : m) => _inst_3 a b) (A x) i (B x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : DecidableEq.{succ u4} m] (i : m) {A : X -> (Matrix.{u4, u3, u2} m n R)} {B : X -> n -> R}, (Continuous.{u1, max (max u4 u3) u2} X (Matrix.{u4, u3, u2} m n R) _inst_1 (instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_2) A) -> (Continuous.{u1, max u3 u2} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u2} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) B) -> (Continuous.{u1, max (max u4 u3) u2} X (Matrix.{u4, u3, u2} m n R) _inst_1 (instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_2) (fun (x : X) => Matrix.updateRow.{u2, u4, u3} m n R (fun (a : m) (b : m) => _inst_3 a b) (A x) i (B x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_update_row Continuous.matrix_updateRowₓ'. -/
@[continuity]
theorem Continuous.matrix_updateRow [DecidableEq m] (i : m) {A : X → Matrix m n R} {B : X → n → R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => (A x).updateRow i (B x) :=
  hA.update i hB
#align continuous.matrix_update_row Continuous.matrix_updateRow

/- warning: continuous.matrix_cramer -> Continuous.matrix_cramer is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} R] [_inst_3 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] [_inst_5 : CommRing.{u3} R] [_inst_6 : TopologicalRing.{u3} R _inst_2 (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5)))] {A : X -> (Matrix.{u2, u2, u3} n n R)} {B : X -> n -> R}, (Continuous.{u1, max u2 u3} X (Matrix.{u2, u2, u3} n n R) _inst_1 (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_2) A) -> (Continuous.{u1, max u2 u3} X (n -> R) _inst_1 (Pi.topologicalSpace.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) B) -> (Continuous.{u1, max u2 u3} X (n -> R) _inst_1 (Pi.topologicalSpace.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) (fun (x : X) => coeFn.{succ (max u2 u3), succ (max u2 u3)} (LinearMap.{u3, u3, max u2 u3, max u2 u3} R R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)))) (n -> R) (n -> R) (Pi.addCommMonoid.{u2, u3} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5)))))) (Pi.addCommMonoid.{u2, u3} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5)))))) (Pi.Function.module.{u2, u3, u3} n R R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5))))) (Semiring.toModule.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)))) (Pi.Function.module.{u2, u3, u3} n R R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5))))) (Semiring.toModule.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5))))) (fun (_x : LinearMap.{u3, u3, max u2 u3, max u2 u3} R R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)))) (n -> R) (n -> R) (Pi.addCommMonoid.{u2, u3} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5)))))) (Pi.addCommMonoid.{u2, u3} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5)))))) (Pi.Function.module.{u2, u3, u3} n R R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5))))) (Semiring.toModule.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)))) (Pi.Function.module.{u2, u3, u3} n R R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5))))) (Semiring.toModule.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5))))) => (n -> R) -> n -> R) (LinearMap.hasCoeToFun.{u3, u3, max u2 u3, max u2 u3} R R (n -> R) (n -> R) (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (Pi.addCommMonoid.{u2, u3} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5)))))) (Pi.addCommMonoid.{u2, u3} n (fun (ᾰ : n) => R) (fun (i : n) => AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5)))))) (Pi.Function.module.{u2, u3, u3} n R R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5))))) (Semiring.toModule.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)))) (Pi.Function.module.{u2, u3, u3} n R R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)) (AddCommGroup.toAddCommMonoid.{u3} R (NonUnitalNonAssocRing.toAddCommGroup.{u3} R (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5))))) (Semiring.toModule.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5)))) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R (CommRing.toRing.{u3} R _inst_5))))) (Matrix.cramer.{u2, u3} n R (fun (a : n) (b : n) => _inst_4 a b) _inst_3 _inst_5 (A x)) (B x)))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : Fintype.{u3} n] [_inst_4 : DecidableEq.{succ u3} n] [_inst_5 : CommRing.{u2} R] [_inst_6 : TopologicalRing.{u2} R _inst_2 (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5)))] {A : X -> (Matrix.{u3, u3, u2} n n R)} {B : X -> n -> R}, (Continuous.{u1, max u3 u2} X (Matrix.{u3, u3, u2} n n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_2) A) -> (Continuous.{u1, max u3 u2} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u2} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) B) -> (Continuous.{u1, max u3 u2} X (n -> R) _inst_1 (Pi.topologicalSpace.{u3, u2} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_2)) (fun (x : X) => FunLike.coe.{max (succ u3) (succ u2), max (succ u3) (succ u2), max (succ u3) (succ u2)} (LinearMap.{u2, u2, max u3 u2, max u3 u2} R R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)))) (n -> R) (n -> R) (Pi.addCommMonoid.{u3, u2} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.Adjugate._hyg.273 : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5)))))) (Pi.addCommMonoid.{u3, u2} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.Adjugate._hyg.273 : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5)))))) (Pi.module.{u3, u2, u2} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.Adjugate._hyg.273 : n) => R) R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5))))) (fun (i : n) => Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)))) (Pi.module.{u3, u2, u2} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.Adjugate._hyg.273 : n) => R) R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5))))) (fun (i : n) => Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))))) (n -> R) (fun (_x : n -> R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6191 : n -> R) => n -> R) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, max u3 u2, max u3 u2} R R (n -> R) (n -> R) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)) (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)) (Pi.addCommMonoid.{u3, u2} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5)))))) (Pi.addCommMonoid.{u3, u2} n (fun (ᾰ : n) => R) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5)))))) (Pi.module.{u3, u2, u2} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.Adjugate._hyg.273 : n) => R) R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5))))) (fun (i : n) => Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)))) (Pi.module.{u3, u2, u2} n (fun (a._@.Mathlib.LinearAlgebra.Matrix.Adjugate._hyg.273 : n) => R) R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)) (fun (i : n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5))))) (fun (i : n) => Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5)))) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R (CommRing.toCommSemiring.{u2} R _inst_5))))) (Matrix.cramer.{u3, u2} n R (fun (a : n) (b : n) => _inst_4 a b) _inst_3 _inst_5 (A x)) (B x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_cramer Continuous.matrix_cramerₓ'. -/
@[continuity]
theorem Continuous.matrix_cramer [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    {A : X → Matrix n n R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).cramer (B x) :=
  continuous_pi fun i => (hA.matrix_updateColumn _ hB).matrix_det
#align continuous.matrix_cramer Continuous.matrix_cramer

/- warning: continuous.matrix_adjugate -> Continuous.matrix_adjugate is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} R] [_inst_3 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] [_inst_5 : CommRing.{u3} R] [_inst_6 : TopologicalRing.{u3} R _inst_2 (NonAssocRing.toNonUnitalNonAssocRing.{u3} R (Ring.toNonAssocRing.{u3} R (CommRing.toRing.{u3} R _inst_5)))] {A : X -> (Matrix.{u2, u2, u3} n n R)}, (Continuous.{u1, max u2 u3} X (Matrix.{u2, u2, u3} n n R) _inst_1 (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_2) A) -> (Continuous.{u1, max u2 u3} X (Matrix.{u2, u2, u3} n n R) _inst_1 (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_2) (fun (x : X) => Matrix.adjugate.{u2, u3} n R (fun (a : n) (b : n) => _inst_4 a b) _inst_3 _inst_5 (A x)))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : Fintype.{u3} n] [_inst_4 : DecidableEq.{succ u3} n] [_inst_5 : CommRing.{u2} R] [_inst_6 : TopologicalRing.{u2} R _inst_2 (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5)))] {A : X -> (Matrix.{u3, u3, u2} n n R)}, (Continuous.{u1, max u3 u2} X (Matrix.{u3, u3, u2} n n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_2) A) -> (Continuous.{u1, max u3 u2} X (Matrix.{u3, u3, u2} n n R) _inst_1 (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_2) (fun (x : X) => Matrix.adjugate.{u3, u2} n R (fun (a : n) (b : n) => _inst_4 a b) _inst_3 _inst_5 (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_adjugate Continuous.matrix_adjugateₓ'. -/
@[continuity]
theorem Continuous.matrix_adjugate [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => (A x).adjugate :=
  continuous_matrix fun j k =>
    (hA.matrix_transpose.matrix_updateColumn k continuous_const).matrix_det
#align continuous.matrix_adjugate Continuous.matrix_adjugate

/- warning: continuous_at_matrix_inv -> continuousAt_matrix_inv is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} {R : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : Fintype.{u1} n] [_inst_4 : DecidableEq.{succ u1} n] [_inst_5 : CommRing.{u2} R] [_inst_6 : TopologicalRing.{u2} R _inst_2 (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_5)))] (A : Matrix.{u1, u1, u2} n n R), (ContinuousAt.{u2, u2} R R _inst_2 _inst_2 (Ring.inverse.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_5)))) (Matrix.det.{u2, u1} n (fun (a : n) (b : n) => _inst_4 a b) _inst_3 R _inst_5 A)) -> (ContinuousAt.{max u1 u2, max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.{u1, u1, u2} n n R) (Matrix.topologicalSpace.{u1, u1, u2} n n R _inst_2) (Matrix.topologicalSpace.{u1, u1, u2} n n R _inst_2) (Inv.inv.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.hasInv.{u1, u2} n R _inst_3 (fun (a : n) (b : n) => _inst_4 a b) _inst_5)) A)
but is expected to have type
  forall {n : Type.{u2}} {R : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : Fintype.{u2} n] [_inst_4 : DecidableEq.{succ u2} n] [_inst_5 : CommRing.{u1} R] [_inst_6 : TopologicalRing.{u1} R _inst_2 (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_5)))] (A : Matrix.{u2, u2, u1} n n R), (ContinuousAt.{u1, u1} R R _inst_2 _inst_2 (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_5)))) (Matrix.det.{u1, u2} n (fun (a : n) (b : n) => _inst_4 a b) _inst_3 R _inst_5 A)) -> (ContinuousAt.{max u2 u1, max u2 u1} (Matrix.{u2, u2, u1} n n R) (Matrix.{u2, u2, u1} n n R) (instTopologicalSpaceMatrix.{u2, u2, u1} n n R _inst_2) (instTopologicalSpaceMatrix.{u2, u2, u1} n n R _inst_2) (Inv.inv.{max u2 u1} (Matrix.{u2, u2, u1} n n R) (Matrix.inv.{u2, u1} n R _inst_3 (fun (a : n) (b : n) => _inst_4 a b) _inst_5)) A)
Case conversion may be inaccurate. Consider using '#align continuous_at_matrix_inv continuousAt_matrix_invₓ'. -/
/-- When `ring.inverse` is continuous at the determinant (such as in a `normed_ring`, or a
`topological_field`), so is `matrix.has_inv`. -/
theorem continuousAt_matrix_inv [Fintype n] [DecidableEq n] [CommRing R] [TopologicalRing R]
    (A : Matrix n n R) (h : ContinuousAt Ring.inverse A.det) : ContinuousAt Inv.inv A :=
  (h.comp continuous_id.matrix_det.ContinuousAt).smul continuous_id.matrix_adjugate.ContinuousAt
#align continuous_at_matrix_inv continuousAt_matrix_inv

-- lemmas about functions in `data/matrix/block.lean`
section BlockMatrices

/- warning: continuous.matrix_from_blocks -> Continuous.matrix_fromBlocks is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {m : Type.{u3}} {n : Type.{u4}} {p : Type.{u5}} {R : Type.{u6}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u6} R] {A : X -> (Matrix.{u4, u2, u6} n l R)} {B : X -> (Matrix.{u4, u3, u6} n m R)} {C : X -> (Matrix.{u5, u2, u6} p l R)} {D : X -> (Matrix.{u5, u3, u6} p m R)}, (Continuous.{u1, max u4 u2 u6} X (Matrix.{u4, u2, u6} n l R) _inst_1 (Matrix.topologicalSpace.{u4, u2, u6} n l R _inst_2) A) -> (Continuous.{u1, max u4 u3 u6} X (Matrix.{u4, u3, u6} n m R) _inst_1 (Matrix.topologicalSpace.{u4, u3, u6} n m R _inst_2) B) -> (Continuous.{u1, max u5 u2 u6} X (Matrix.{u5, u2, u6} p l R) _inst_1 (Matrix.topologicalSpace.{u5, u2, u6} p l R _inst_2) C) -> (Continuous.{u1, max u5 u3 u6} X (Matrix.{u5, u3, u6} p m R) _inst_1 (Matrix.topologicalSpace.{u5, u3, u6} p m R _inst_2) D) -> (Continuous.{u1, max (max u4 u5) (max u2 u3) u6} X (Matrix.{max u4 u5, max u2 u3, u6} (Sum.{u4, u5} n p) (Sum.{u2, u3} l m) R) _inst_1 (Matrix.topologicalSpace.{max u4 u5, max u2 u3, u6} (Sum.{u4, u5} n p) (Sum.{u2, u3} l m) R _inst_2) (fun (x : X) => Matrix.fromBlocks.{u2, u3, u4, u5, u6} l m n p R (A x) (B x) (C x) (D x)))
but is expected to have type
  forall {X : Type.{u1}} {l : Type.{u5}} {m : Type.{u3}} {n : Type.{u6}} {p : Type.{u2}} {R : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u4} R] {A : X -> (Matrix.{u6, u5, u4} n l R)} {B : X -> (Matrix.{u6, u3, u4} n m R)} {C : X -> (Matrix.{u2, u5, u4} p l R)} {D : X -> (Matrix.{u2, u3, u4} p m R)}, (Continuous.{u1, max (max u5 u6) u4} X (Matrix.{u6, u5, u4} n l R) _inst_1 (instTopologicalSpaceMatrix.{u6, u5, u4} n l R _inst_2) A) -> (Continuous.{u1, max (max u3 u6) u4} X (Matrix.{u6, u3, u4} n m R) _inst_1 (instTopologicalSpaceMatrix.{u6, u3, u4} n m R _inst_2) B) -> (Continuous.{u1, max (max u5 u2) u4} X (Matrix.{u2, u5, u4} p l R) _inst_1 (instTopologicalSpaceMatrix.{u2, u5, u4} p l R _inst_2) C) -> (Continuous.{u1, max (max u3 u2) u4} X (Matrix.{u2, u3, u4} p m R) _inst_1 (instTopologicalSpaceMatrix.{u2, u3, u4} p m R _inst_2) D) -> (Continuous.{u1, max (max (max (max u4 u2) u6) u3) u5} X (Matrix.{max u2 u6, max u3 u5, u4} (Sum.{u6, u2} n p) (Sum.{u5, u3} l m) R) _inst_1 (instTopologicalSpaceMatrix.{max u6 u2, max u5 u3, u4} (Sum.{u6, u2} n p) (Sum.{u5, u3} l m) R _inst_2) (fun (x : X) => Matrix.fromBlocks.{u5, u3, u6, u2, u4} l m n p R (A x) (B x) (C x) (D x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_from_blocks Continuous.matrix_fromBlocksₓ'. -/
@[continuity]
theorem Continuous.matrix_fromBlocks {A : X → Matrix n l R} {B : X → Matrix n m R}
    {C : X → Matrix p l R} {D : X → Matrix p m R} (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x) :=
  continuous_matrix fun i j => by
    cases i <;> cases j <;> refine' Continuous.matrix_elem _ i j <;> assumption
#align continuous.matrix_from_blocks Continuous.matrix_fromBlocks

/- warning: continuous.matrix_block_diagonal -> Continuous.matrix_blockDiagonal is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {p : Type.{u4}} {R : Type.{u5}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u5} R] [_inst_3 : Zero.{u5} R] [_inst_4 : DecidableEq.{succ u4} p] {A : X -> p -> (Matrix.{u2, u3, u5} m n R)}, (Continuous.{u1, max u4 u2 u3 u5} X (p -> (Matrix.{u2, u3, u5} m n R)) _inst_1 (Pi.topologicalSpace.{u4, max u2 u3 u5} p (fun (ᾰ : p) => Matrix.{u2, u3, u5} m n R) (fun (a : p) => Matrix.topologicalSpace.{u2, u3, u5} m n R _inst_2)) A) -> (Continuous.{u1, max (max u2 u4) (max u3 u4) u5} X (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R) _inst_1 (Matrix.topologicalSpace.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_2) (fun (x : X) => Matrix.blockDiagonal.{u2, u3, u4, u5} m n p R (fun (a : p) (b : p) => _inst_4 a b) _inst_3 (A x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {p : Type.{u4}} {R : Type.{u5}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u5} R] [_inst_3 : Zero.{u5} R] [_inst_4 : DecidableEq.{succ u4} p] {A : X -> p -> (Matrix.{u3, u2, u5} m n R)}, (Continuous.{u1, max (max (max u3 u2) u4) u5} X (p -> (Matrix.{u3, u2, u5} m n R)) _inst_1 (Pi.topologicalSpace.{u4, max (max u3 u2) u5} p (fun (ᾰ : p) => Matrix.{u3, u2, u5} m n R) (fun (a : p) => instTopologicalSpaceMatrix.{u3, u2, u5} m n R _inst_2)) A) -> (Continuous.{u1, max (max (max u5 u4) u2) u3} X (Matrix.{max u4 u3, max u4 u2, u5} (Prod.{u3, u4} m p) (Prod.{u2, u4} n p) R) _inst_1 (instTopologicalSpaceMatrix.{max u3 u4, max u2 u4, u5} (Prod.{u3, u4} m p) (Prod.{u2, u4} n p) R _inst_2) (fun (x : X) => Matrix.blockDiagonal.{u3, u2, u4, u5} m n p R (fun (a : p) (b : p) => _inst_4 a b) _inst_3 (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_block_diagonal Continuous.matrix_blockDiagonalₓ'. -/
@[continuity]
theorem Continuous.matrix_blockDiagonal [Zero R] [DecidableEq p] {A : X → p → Matrix m n R}
    (hA : Continuous A) : Continuous fun x => blockDiagonal (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ =>
    (((continuous_apply i₂).comp hA).matrix_elem i₁ j₁).if_const _ continuous_zero
#align continuous.matrix_block_diagonal Continuous.matrix_blockDiagonal

/- warning: continuous.matrix_block_diag -> Continuous.matrix_blockDiag is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {p : Type.{u4}} {R : Type.{u5}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u5} R] {A : X -> (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R)}, (Continuous.{u1, max (max u2 u4) (max u3 u4) u5} X (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R) _inst_1 (Matrix.topologicalSpace.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_2) A) -> (Continuous.{u1, max u4 u2 u3 u5} X (p -> (Matrix.{u2, u3, u5} m n R)) _inst_1 (Pi.topologicalSpace.{u4, max u2 u3 u5} p (fun (k : p) => Matrix.{u2, u3, u5} m n R) (fun (a : p) => Matrix.topologicalSpace.{u2, u3, u5} m n R _inst_2)) (fun (x : X) => Matrix.blockDiag.{u2, u3, u4, u5} m n p R (A x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {p : Type.{u5}} {R : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] {A : X -> (Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R)}, (Continuous.{u1, max (max (max u4 u3) u5) u2} X (Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R) _inst_1 (instTopologicalSpaceMatrix.{max u4 u5, max u3 u5, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_2) A) -> (Continuous.{u1, max (max (max u2 u5) u3) u4} X (p -> (Matrix.{u4, u3, u2} m n R)) _inst_1 (Pi.topologicalSpace.{u5, max (max u4 u3) u2} p (fun (k : p) => Matrix.{u4, u3, u2} m n R) (fun (a : p) => instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_2)) (fun (x : X) => Matrix.blockDiag.{u4, u3, u5, u2} m n p R (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_block_diag Continuous.matrix_blockDiagₓ'. -/
@[continuity]
theorem Continuous.matrix_blockDiag {A : X → Matrix (m × p) (n × p) R} (hA : Continuous A) :
    Continuous fun x => blockDiag (A x) :=
  continuous_pi fun i => continuous_matrix fun j k => hA.matrix_elem _ _
#align continuous.matrix_block_diag Continuous.matrix_blockDiag

/- warning: continuous.matrix_block_diagonal' -> Continuous.matrix_blockDiagonal' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {R : Type.{u3}} {m' : l -> Type.{u4}} {n' : l -> Type.{u5}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} R] [_inst_3 : Zero.{u3} R] [_inst_4 : DecidableEq.{succ u2} l] {A : X -> (forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R)}, (Continuous.{u1, max u2 u4 u5 u3} X (forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R) _inst_1 (Pi.topologicalSpace.{u2, max u4 u5 u3} l (fun (i : l) => Matrix.{u4, u5, u3} (m' i) (n' i) R) (fun (a : l) => Matrix.topologicalSpace.{u4, u5, u3} (m' a) (n' a) R _inst_2)) A) -> (Continuous.{u1, max (max u2 u4) (max u2 u5) u3} X (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R) _inst_1 (Matrix.topologicalSpace.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_2) (fun (x : X) => Matrix.blockDiagonal'.{u2, u4, u5, u3} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_4 a b) _inst_3 (A x)))
but is expected to have type
  forall {X : Type.{u1}} {l : Type.{u4}} {R : Type.{u5}} {m' : l -> Type.{u3}} {n' : l -> Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u5} R] [_inst_3 : Zero.{u5} R] [_inst_4 : DecidableEq.{succ u4} l] {A : X -> (forall (i : l), Matrix.{u3, u2, u5} (m' i) (n' i) R)}, (Continuous.{u1, max (max (max u4 u5) u3) u2} X (forall (i : l), Matrix.{u3, u2, u5} (m' i) (n' i) R) _inst_1 (Pi.topologicalSpace.{u4, max (max u5 u3) u2} l (fun (i : l) => Matrix.{u3, u2, u5} (m' i) (n' i) R) (fun (a : l) => instTopologicalSpaceMatrix.{u3, u2, u5} (m' a) (n' a) R _inst_2)) A) -> (Continuous.{u1, max (max (max u5 u2) u3) u4} X (Matrix.{max u3 u4, max u2 u4, u5} (Sigma.{u4, u3} l (fun (i : l) => m' i)) (Sigma.{u4, u2} l (fun (i : l) => n' i)) R) _inst_1 (instTopologicalSpaceMatrix.{max u4 u3, max u4 u2, u5} (Sigma.{u4, u3} l (fun (i : l) => m' i)) (Sigma.{u4, u2} l (fun (i : l) => n' i)) R _inst_2) (fun (x : X) => Matrix.blockDiagonal'.{u4, u3, u2, u5} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_4 a b) _inst_3 (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_block_diagonal' Continuous.matrix_blockDiagonal'ₓ'. -/
@[continuity]
theorem Continuous.matrix_blockDiagonal' [Zero R] [DecidableEq l]
    {A : X → ∀ i, Matrix (m' i) (n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiagonal' (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ =>
    by
    dsimp only [block_diagonal'_apply']
    split_ifs
    · subst h
      exact ((continuous_apply i₁).comp hA).matrix_elem i₂ j₂
    · exact continuous_const
#align continuous.matrix_block_diagonal' Continuous.matrix_blockDiagonal'

/- warning: continuous.matrix_block_diag' -> Continuous.matrix_blockDiag' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {R : Type.{u3}} {m' : l -> Type.{u4}} {n' : l -> Type.{u5}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u3} R] {A : X -> (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R)}, (Continuous.{u1, max (max u2 u4) (max u2 u5) u3} X (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R) _inst_1 (Matrix.topologicalSpace.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_2) A) -> (Continuous.{u1, max u2 u4 u5 u3} X (forall (k : l), Matrix.{u4, u5, u3} (m' k) (n' k) R) _inst_1 (Pi.topologicalSpace.{u2, max u4 u5 u3} l (fun (k : l) => Matrix.{u4, u5, u3} (m' k) (n' k) R) (fun (a : l) => Matrix.topologicalSpace.{u4, u5, u3} (m' a) (n' a) R _inst_2)) (fun (x : X) => Matrix.blockDiag'.{u2, u4, u5, u3} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (A x)))
but is expected to have type
  forall {X : Type.{u1}} {l : Type.{u4}} {R : Type.{u2}} {m' : l -> Type.{u5}} {n' : l -> Type.{u3}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} R] {A : X -> (Matrix.{max u5 u4, max u3 u4, u2} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R)}, (Continuous.{u1, max (max (max u4 u2) u5) u3} X (Matrix.{max u5 u4, max u3 u4, u2} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R) _inst_1 (instTopologicalSpaceMatrix.{max u4 u5, max u4 u3, u2} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R _inst_2) A) -> (Continuous.{u1, max (max (max u2 u3) u5) u4} X (forall (k : l), Matrix.{u5, u3, u2} (m' k) (n' k) R) _inst_1 (Pi.topologicalSpace.{u4, max (max u2 u5) u3} l (fun (k : l) => Matrix.{u5, u3, u2} (m' k) (n' k) R) (fun (a : l) => instTopologicalSpaceMatrix.{u5, u3, u2} (m' a) (n' a) R _inst_2)) (fun (x : X) => Matrix.blockDiag'.{u4, u5, u3, u2} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (A x)))
Case conversion may be inaccurate. Consider using '#align continuous.matrix_block_diag' Continuous.matrix_blockDiag'ₓ'. -/
@[continuity]
theorem Continuous.matrix_blockDiag' {A : X → Matrix (Σi, m' i) (Σi, n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiag' (A x) :=
  continuous_pi fun i => continuous_matrix fun j k => hA.matrix_elem _ _
#align continuous.matrix_block_diag' Continuous.matrix_blockDiag'

end BlockMatrices

end Continuity

/-! ### Lemmas about infinite sums -/


section tsum

variable [Semiring α] [AddCommMonoid R] [TopologicalSpace R] [Module α R]

/- warning: has_sum.matrix_transpose -> HasSum.matrix_transpose is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] {f : X -> (Matrix.{u2, u3, u4} m n R)} {a : Matrix.{u2, u3, u4} m n R}, (HasSum.{max u2 u3 u4, u1} (Matrix.{u2, u3, u4} m n R) X (Matrix.addCommMonoid.{u4, u2, u3} m n R _inst_2) (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_3) f a) -> (HasSum.{max u3 u2 u4, u1} (Matrix.{u3, u2, u4} n m R) X (Matrix.addCommMonoid.{u4, u3, u2} n m R _inst_2) (Matrix.topologicalSpace.{u3, u2, u4} n m R _inst_3) (fun (x : X) => Matrix.transpose.{u4, u2, u3} m n R (f x)) (Matrix.transpose.{u4, u2, u3} m n R a))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] {f : X -> (Matrix.{u4, u3, u2} m n R)} {a : Matrix.{u4, u3, u2} m n R}, (HasSum.{max (max u4 u3) u2, u1} (Matrix.{u4, u3, u2} m n R) X (Matrix.addCommMonoid.{u2, u4, u3} m n R _inst_2) (instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_3) f a) -> (HasSum.{max (max u3 u4) u2, u1} (Matrix.{u3, u4, u2} n m R) X (Matrix.addCommMonoid.{u2, u3, u4} n m R _inst_2) (instTopologicalSpaceMatrix.{u3, u4, u2} n m R _inst_3) (fun (x : X) => Matrix.transpose.{u2, u4, u3} m n R (f x)) (Matrix.transpose.{u2, u4, u3} m n R a))
Case conversion may be inaccurate. Consider using '#align has_sum.matrix_transpose HasSum.matrix_transposeₓ'. -/
theorem HasSum.matrix_transpose {f : X → Matrix m n R} {a : Matrix m n R} (hf : HasSum f a) :
    HasSum (fun x => (f x)ᵀ) aᵀ :=
  (hf.map (Matrix.transposeAddEquiv m n R) continuous_id.matrix_transpose : _)
#align has_sum.matrix_transpose HasSum.matrix_transpose

/- warning: summable.matrix_transpose -> Summable.matrix_transpose is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] {f : X -> (Matrix.{u2, u3, u4} m n R)}, (Summable.{max u2 u3 u4, u1} (Matrix.{u2, u3, u4} m n R) X (Matrix.addCommMonoid.{u4, u2, u3} m n R _inst_2) (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_3) f) -> (Summable.{max u3 u2 u4, u1} (Matrix.{u3, u2, u4} n m R) X (Matrix.addCommMonoid.{u4, u3, u2} n m R _inst_2) (Matrix.topologicalSpace.{u3, u2, u4} n m R _inst_3) (fun (x : X) => Matrix.transpose.{u4, u2, u3} m n R (f x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] {f : X -> (Matrix.{u4, u3, u2} m n R)}, (Summable.{max (max u4 u3) u2, u1} (Matrix.{u4, u3, u2} m n R) X (Matrix.addCommMonoid.{u2, u4, u3} m n R _inst_2) (instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_3) f) -> (Summable.{max (max u3 u4) u2, u1} (Matrix.{u3, u4, u2} n m R) X (Matrix.addCommMonoid.{u2, u3, u4} n m R _inst_2) (instTopologicalSpaceMatrix.{u3, u4, u2} n m R _inst_3) (fun (x : X) => Matrix.transpose.{u2, u4, u3} m n R (f x)))
Case conversion may be inaccurate. Consider using '#align summable.matrix_transpose Summable.matrix_transposeₓ'. -/
theorem Summable.matrix_transpose {f : X → Matrix m n R} (hf : Summable f) :
    Summable fun x => (f x)ᵀ :=
  hf.HasSum.matrix_transpose.Summable
#align summable.matrix_transpose Summable.matrix_transpose

/- warning: summable_matrix_transpose -> summable_matrix_transpose is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] {f : X -> (Matrix.{u2, u3, u4} m n R)}, Iff (Summable.{max u3 u2 u4, u1} (Matrix.{u3, u2, u4} n m R) X (Matrix.addCommMonoid.{u4, u3, u2} n m R _inst_2) (Matrix.topologicalSpace.{u3, u2, u4} n m R _inst_3) (fun (x : X) => Matrix.transpose.{u4, u2, u3} m n R (f x))) (Summable.{max u2 u3 u4, u1} (Matrix.{u2, u3, u4} m n R) X (Matrix.addCommMonoid.{u4, u2, u3} m n R _inst_2) (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_3) f)
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] {f : X -> (Matrix.{u4, u3, u2} m n R)}, Iff (Summable.{max (max u3 u4) u2, u1} (Matrix.{u3, u4, u2} n m R) X (Matrix.addCommMonoid.{u2, u3, u4} n m R _inst_2) (instTopologicalSpaceMatrix.{u3, u4, u2} n m R _inst_3) (fun (x : X) => Matrix.transpose.{u2, u4, u3} m n R (f x))) (Summable.{max (max u4 u3) u2, u1} (Matrix.{u4, u3, u2} m n R) X (Matrix.addCommMonoid.{u2, u4, u3} m n R _inst_2) (instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_3) f)
Case conversion may be inaccurate. Consider using '#align summable_matrix_transpose summable_matrix_transposeₓ'. -/
@[simp]
theorem summable_matrix_transpose {f : X → Matrix m n R} :
    (Summable fun x => (f x)ᵀ) ↔ Summable f :=
  (Summable.map_iff_of_equiv (Matrix.transposeAddEquiv m n R)
      (@continuous_id (Matrix m n R) _).matrix_transpose continuous_id.matrix_transpose :
    _)
#align summable_matrix_transpose summable_matrix_transpose

/- warning: matrix.transpose_tsum -> Matrix.transpose_tsum is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : T2Space.{u4} R _inst_3] {f : X -> (Matrix.{u2, u3, u4} m n R)}, Eq.{succ (max u3 u2 u4)} (Matrix.{u3, u2, u4} n m R) (Matrix.transpose.{u4, u2, u3} m n R (tsum.{max u2 u3 u4, u1} (Matrix.{u2, u3, u4} m n R) (Matrix.addCommMonoid.{u4, u2, u3} m n R _inst_2) (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_3) X (fun (x : X) => f x))) (tsum.{max u3 u2 u4, u1} (Matrix.{u3, u2, u4} n m R) (Matrix.addCommMonoid.{u4, u3, u2} n m R _inst_2) (Matrix.topologicalSpace.{u3, u2, u4} n m R _inst_3) X (fun (x : X) => Matrix.transpose.{u4, u2, u3} m n R (f x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : T2Space.{u4} R _inst_3] {f : X -> (Matrix.{u3, u2, u4} m n R)}, Eq.{max (max (succ u3) (succ u2)) (succ u4)} (Matrix.{u2, u3, u4} n m R) (Matrix.transpose.{u4, u3, u2} m n R (tsum.{max (max u2 u3) u4, u1} (Matrix.{u3, u2, u4} m n R) (Matrix.addCommMonoid.{u4, u3, u2} m n R _inst_2) (instTopologicalSpaceMatrix.{u3, u2, u4} m n R _inst_3) X (fun (x : X) => f x))) (tsum.{max (max u2 u3) u4, u1} (Matrix.{u2, u3, u4} n m R) (Matrix.addCommMonoid.{u4, u2, u3} n m R _inst_2) (instTopologicalSpaceMatrix.{u2, u3, u4} n m R _inst_3) X (fun (x : X) => Matrix.transpose.{u4, u3, u2} m n R (f x)))
Case conversion may be inaccurate. Consider using '#align matrix.transpose_tsum Matrix.transpose_tsumₓ'. -/
theorem Matrix.transpose_tsum [T2Space R] {f : X → Matrix m n R} : (∑' x, f x)ᵀ = ∑' x, (f x)ᵀ :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.matrix_transpose.tsum_eq.symm
  · have hft := summable_matrix_transpose.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft, transpose_zero]
#align matrix.transpose_tsum Matrix.transpose_tsum

/- warning: has_sum.matrix_conj_transpose -> HasSum.matrix_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : StarAddMonoid.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)] [_inst_6 : ContinuousStar.{u4} R _inst_3 (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5))] {f : X -> (Matrix.{u2, u3, u4} m n R)} {a : Matrix.{u2, u3, u4} m n R}, (HasSum.{max u2 u3 u4, u1} (Matrix.{u2, u3, u4} m n R) X (Matrix.addCommMonoid.{u4, u2, u3} m n R _inst_2) (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_3) f a) -> (HasSum.{max u3 u2 u4, u1} (Matrix.{u3, u2, u4} n m R) X (Matrix.addCommMonoid.{u4, u3, u2} n m R _inst_2) (Matrix.topologicalSpace.{u3, u2, u4} n m R _inst_3) (fun (x : X) => Matrix.conjTranspose.{u4, u2, u3} m n R (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) (f x)) (Matrix.conjTranspose.{u4, u2, u3} m n R (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) a))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : StarAddMonoid.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)] [_inst_6 : ContinuousStar.{u4} R _inst_3 (InvolutiveStar.toStar.{u4} R (StarAddMonoid.toInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5))] {f : X -> (Matrix.{u3, u2, u4} m n R)} {a : Matrix.{u3, u2, u4} m n R}, (HasSum.{max (max u3 u2) u4, u1} (Matrix.{u3, u2, u4} m n R) X (Matrix.addCommMonoid.{u4, u3, u2} m n R _inst_2) (instTopologicalSpaceMatrix.{u3, u2, u4} m n R _inst_3) f a) -> (HasSum.{max (max u2 u3) u4, u1} (Matrix.{u2, u3, u4} n m R) X (Matrix.addCommMonoid.{u4, u2, u3} n m R _inst_2) (instTopologicalSpaceMatrix.{u2, u3, u4} n m R _inst_3) (fun (x : X) => Matrix.conjTranspose.{u4, u3, u2} m n R (InvolutiveStar.toStar.{u4} R (StarAddMonoid.toInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) (f x)) (Matrix.conjTranspose.{u4, u3, u2} m n R (InvolutiveStar.toStar.{u4} R (StarAddMonoid.toInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) a))
Case conversion may be inaccurate. Consider using '#align has_sum.matrix_conj_transpose HasSum.matrix_conjTransposeₓ'. -/
theorem HasSum.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R}
    {a : Matrix m n R} (hf : HasSum f a) : HasSum (fun x => (f x)ᴴ) aᴴ :=
  (hf.map (Matrix.conjTransposeAddEquiv m n R) continuous_id.matrix_conjTranspose : _)
#align has_sum.matrix_conj_transpose HasSum.matrix_conjTranspose

/- warning: summable.matrix_conj_transpose -> Summable.matrix_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : StarAddMonoid.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)] [_inst_6 : ContinuousStar.{u4} R _inst_3 (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5))] {f : X -> (Matrix.{u2, u3, u4} m n R)}, (Summable.{max u2 u3 u4, u1} (Matrix.{u2, u3, u4} m n R) X (Matrix.addCommMonoid.{u4, u2, u3} m n R _inst_2) (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_3) f) -> (Summable.{max u3 u2 u4, u1} (Matrix.{u3, u2, u4} n m R) X (Matrix.addCommMonoid.{u4, u3, u2} n m R _inst_2) (Matrix.topologicalSpace.{u3, u2, u4} n m R _inst_3) (fun (x : X) => Matrix.conjTranspose.{u4, u2, u3} m n R (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) (f x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : StarAddMonoid.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)] [_inst_6 : ContinuousStar.{u4} R _inst_3 (InvolutiveStar.toStar.{u4} R (StarAddMonoid.toInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5))] {f : X -> (Matrix.{u3, u2, u4} m n R)}, (Summable.{max (max u3 u2) u4, u1} (Matrix.{u3, u2, u4} m n R) X (Matrix.addCommMonoid.{u4, u3, u2} m n R _inst_2) (instTopologicalSpaceMatrix.{u3, u2, u4} m n R _inst_3) f) -> (Summable.{max (max u2 u3) u4, u1} (Matrix.{u2, u3, u4} n m R) X (Matrix.addCommMonoid.{u4, u2, u3} n m R _inst_2) (instTopologicalSpaceMatrix.{u2, u3, u4} n m R _inst_3) (fun (x : X) => Matrix.conjTranspose.{u4, u3, u2} m n R (InvolutiveStar.toStar.{u4} R (StarAddMonoid.toInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) (f x)))
Case conversion may be inaccurate. Consider using '#align summable.matrix_conj_transpose Summable.matrix_conjTransposeₓ'. -/
theorem Summable.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R}
    (hf : Summable f) : Summable fun x => (f x)ᴴ :=
  hf.HasSum.matrix_conjTranspose.Summable
#align summable.matrix_conj_transpose Summable.matrix_conjTranspose

/- warning: summable_matrix_conj_transpose -> summable_matrix_conjTranspose is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : StarAddMonoid.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)] [_inst_6 : ContinuousStar.{u4} R _inst_3 (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5))] {f : X -> (Matrix.{u2, u3, u4} m n R)}, Iff (Summable.{max u3 u2 u4, u1} (Matrix.{u3, u2, u4} n m R) X (Matrix.addCommMonoid.{u4, u3, u2} n m R _inst_2) (Matrix.topologicalSpace.{u3, u2, u4} n m R _inst_3) (fun (x : X) => Matrix.conjTranspose.{u4, u2, u3} m n R (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) (f x))) (Summable.{max u2 u3 u4, u1} (Matrix.{u2, u3, u4} m n R) X (Matrix.addCommMonoid.{u4, u2, u3} m n R _inst_2) (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_3) f)
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : StarAddMonoid.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)] [_inst_6 : ContinuousStar.{u4} R _inst_3 (InvolutiveStar.toStar.{u4} R (StarAddMonoid.toInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5))] {f : X -> (Matrix.{u3, u2, u4} m n R)}, Iff (Summable.{max (max u2 u3) u4, u1} (Matrix.{u2, u3, u4} n m R) X (Matrix.addCommMonoid.{u4, u2, u3} n m R _inst_2) (instTopologicalSpaceMatrix.{u2, u3, u4} n m R _inst_3) (fun (x : X) => Matrix.conjTranspose.{u4, u3, u2} m n R (InvolutiveStar.toStar.{u4} R (StarAddMonoid.toInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) (f x))) (Summable.{max (max u3 u2) u4, u1} (Matrix.{u3, u2, u4} m n R) X (Matrix.addCommMonoid.{u4, u3, u2} m n R _inst_2) (instTopologicalSpaceMatrix.{u3, u2, u4} m n R _inst_3) f)
Case conversion may be inaccurate. Consider using '#align summable_matrix_conj_transpose summable_matrix_conjTransposeₓ'. -/
@[simp]
theorem summable_matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X → Matrix m n R} :
    (Summable fun x => (f x)ᴴ) ↔ Summable f :=
  (Summable.map_iff_of_equiv (Matrix.conjTransposeAddEquiv m n R)
      (@continuous_id (Matrix m n R) _).matrix_conjTranspose continuous_id.matrix_conjTranspose :
    _)
#align summable_matrix_conj_transpose summable_matrix_conjTranspose

/- warning: matrix.conj_transpose_tsum -> Matrix.conjTranspose_tsum is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : StarAddMonoid.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)] [_inst_6 : ContinuousStar.{u4} R _inst_3 (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5))] [_inst_7 : T2Space.{u4} R _inst_3] {f : X -> (Matrix.{u2, u3, u4} m n R)}, Eq.{succ (max u3 u2 u4)} (Matrix.{u3, u2, u4} n m R) (Matrix.conjTranspose.{u4, u2, u3} m n R (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) (tsum.{max u2 u3 u4, u1} (Matrix.{u2, u3, u4} m n R) (Matrix.addCommMonoid.{u4, u2, u3} m n R _inst_2) (Matrix.topologicalSpace.{u2, u3, u4} m n R _inst_3) X (fun (x : X) => f x))) (tsum.{max u3 u2 u4, u1} (Matrix.{u3, u2, u4} n m R) (Matrix.addCommMonoid.{u4, u3, u2} n m R _inst_2) (Matrix.topologicalSpace.{u3, u2, u4} n m R _inst_3) X (fun (x : X) => Matrix.conjTranspose.{u4, u2, u3} m n R (InvolutiveStar.toHasStar.{u4} R (StarAddMonoid.toHasInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) (f x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : StarAddMonoid.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)] [_inst_6 : ContinuousStar.{u4} R _inst_3 (InvolutiveStar.toStar.{u4} R (StarAddMonoid.toInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5))] [_inst_7 : T2Space.{u4} R _inst_3] {f : X -> (Matrix.{u3, u2, u4} m n R)}, Eq.{max (max (succ u3) (succ u2)) (succ u4)} (Matrix.{u2, u3, u4} n m R) (Matrix.conjTranspose.{u4, u3, u2} m n R (InvolutiveStar.toStar.{u4} R (StarAddMonoid.toInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) (tsum.{max (max u2 u3) u4, u1} (Matrix.{u3, u2, u4} m n R) (Matrix.addCommMonoid.{u4, u3, u2} m n R _inst_2) (instTopologicalSpaceMatrix.{u3, u2, u4} m n R _inst_3) X (fun (x : X) => f x))) (tsum.{max (max u2 u3) u4, u1} (Matrix.{u2, u3, u4} n m R) (Matrix.addCommMonoid.{u4, u2, u3} n m R _inst_2) (instTopologicalSpaceMatrix.{u2, u3, u4} n m R _inst_3) X (fun (x : X) => Matrix.conjTranspose.{u4, u3, u2} m n R (InvolutiveStar.toStar.{u4} R (StarAddMonoid.toInvolutiveStar.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2) _inst_5)) (f x)))
Case conversion may be inaccurate. Consider using '#align matrix.conj_transpose_tsum Matrix.conjTranspose_tsumₓ'. -/
theorem Matrix.conjTranspose_tsum [StarAddMonoid R] [ContinuousStar R] [T2Space R]
    {f : X → Matrix m n R} : (∑' x, f x)ᴴ = ∑' x, (f x)ᴴ :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.matrix_conj_transpose.tsum_eq.symm
  · have hft := summable_matrix_conj_transpose.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft, conj_transpose_zero]
#align matrix.conj_transpose_tsum Matrix.conjTranspose_tsum

/- warning: has_sum.matrix_diagonal -> HasSum.matrix_diagonal is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_5 : DecidableEq.{succ u2} n] {f : X -> n -> R} {a : n -> R}, (HasSum.{max u2 u3, u1} (n -> R) X (Pi.addCommMonoid.{u2, u3} n (fun (ᾰ : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_3)) f a) -> (HasSum.{max u2 u3, u1} (Matrix.{u2, u2, u3} n n R) X (Matrix.addCommMonoid.{u3, u2, u2} n n R _inst_2) (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_3) (fun (x : X) => Matrix.diagonal.{u3, u2} n R (fun (a : n) (b : n) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) (f x)) (Matrix.diagonal.{u3, u2} n R (fun (a : n) (b : n) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) a))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_5 : DecidableEq.{succ u3} n] {f : X -> n -> R} {a : n -> R}, (HasSum.{max u3 u2, u1} (n -> R) X (Pi.addCommMonoid.{u3, u2} n (fun (ᾰ : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u3, u2} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_3)) f a) -> (HasSum.{max u3 u2, u1} (Matrix.{u3, u3, u2} n n R) X (Matrix.addCommMonoid.{u2, u3, u3} n n R _inst_2) (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_3) (fun (x : X) => Matrix.diagonal.{u2, u3} n R (fun (a : n) (b : n) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (f x)) (Matrix.diagonal.{u2, u3} n R (fun (a : n) (b : n) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) a))
Case conversion may be inaccurate. Consider using '#align has_sum.matrix_diagonal HasSum.matrix_diagonalₓ'. -/
theorem HasSum.matrix_diagonal [DecidableEq n] {f : X → n → R} {a : n → R} (hf : HasSum f a) :
    HasSum (fun x => diagonal (f x)) (diagonal a) :=
  (hf.map (diagonalAddMonoidHom n R) <| Continuous.matrix_diagonal <| continuous_id : _)
#align has_sum.matrix_diagonal HasSum.matrix_diagonal

/- warning: summable.matrix_diagonal -> Summable.matrix_diagonal is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_5 : DecidableEq.{succ u2} n] {f : X -> n -> R}, (Summable.{max u2 u3, u1} (n -> R) X (Pi.addCommMonoid.{u2, u3} n (fun (ᾰ : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_3)) f) -> (Summable.{max u2 u3, u1} (Matrix.{u2, u2, u3} n n R) X (Matrix.addCommMonoid.{u3, u2, u2} n n R _inst_2) (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_3) (fun (x : X) => Matrix.diagonal.{u3, u2} n R (fun (a : n) (b : n) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) (f x)))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_5 : DecidableEq.{succ u3} n] {f : X -> n -> R}, (Summable.{max u3 u2, u1} (n -> R) X (Pi.addCommMonoid.{u3, u2} n (fun (ᾰ : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u3, u2} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_3)) f) -> (Summable.{max u3 u2, u1} (Matrix.{u3, u3, u2} n n R) X (Matrix.addCommMonoid.{u2, u3, u3} n n R _inst_2) (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_3) (fun (x : X) => Matrix.diagonal.{u2, u3} n R (fun (a : n) (b : n) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (f x)))
Case conversion may be inaccurate. Consider using '#align summable.matrix_diagonal Summable.matrix_diagonalₓ'. -/
theorem Summable.matrix_diagonal [DecidableEq n] {f : X → n → R} (hf : Summable f) :
    Summable fun x => diagonal (f x) :=
  hf.HasSum.matrix_diagonal.Summable
#align summable.matrix_diagonal Summable.matrix_diagonal

/- warning: summable_matrix_diagonal -> summable_matrix_diagonal is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_5 : DecidableEq.{succ u2} n] {f : X -> n -> R}, Iff (Summable.{max u2 u3, u1} (Matrix.{u2, u2, u3} n n R) X (Matrix.addCommMonoid.{u3, u2, u2} n n R _inst_2) (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_3) (fun (x : X) => Matrix.diagonal.{u3, u2} n R (fun (a : n) (b : n) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) (f x))) (Summable.{max u2 u3, u1} (n -> R) X (Pi.addCommMonoid.{u2, u3} n (fun (ᾰ : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_3)) f)
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_5 : DecidableEq.{succ u3} n] {f : X -> n -> R}, Iff (Summable.{max u3 u2, u1} (Matrix.{u3, u3, u2} n n R) X (Matrix.addCommMonoid.{u2, u3, u3} n n R _inst_2) (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_3) (fun (x : X) => Matrix.diagonal.{u2, u3} n R (fun (a : n) (b : n) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (f x))) (Summable.{max u3 u2, u1} (n -> R) X (Pi.addCommMonoid.{u3, u2} n (fun (ᾰ : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u3, u2} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_3)) f)
Case conversion may be inaccurate. Consider using '#align summable_matrix_diagonal summable_matrix_diagonalₓ'. -/
@[simp]
theorem summable_matrix_diagonal [DecidableEq n] {f : X → n → R} :
    (Summable fun x => diagonal (f x)) ↔ Summable f :=
  (Summable.map_iff_of_leftInverse (@Matrix.diagonalAddMonoidHom n R _ _)
      (Matrix.diagAddMonoidHom n R) (Continuous.matrix_diagonal continuous_id)
      continuous_matrix_diag fun A => diag_diagonal A :
    _)
#align summable_matrix_diagonal summable_matrix_diagonal

/- warning: matrix.diagonal_tsum -> Matrix.diagonal_tsum is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_5 : DecidableEq.{succ u2} n] [_inst_6 : T2Space.{u3} R _inst_3] {f : X -> n -> R}, Eq.{succ (max u2 u3)} (Matrix.{u2, u2, u3} n n R) (Matrix.diagonal.{u3, u2} n R (fun (a : n) (b : n) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) (tsum.{max u2 u3, u1} (n -> R) (Pi.addCommMonoid.{u2, u3} n (fun (ᾰ : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u2, u3} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_3)) X (fun (x : X) => f x))) (tsum.{max u2 u3, u1} (Matrix.{u2, u2, u3} n n R) (Matrix.addCommMonoid.{u3, u2, u2} n n R _inst_2) (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_3) X (fun (x : X) => Matrix.diagonal.{u3, u2} n R (fun (a : n) (b : n) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) (f x)))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_5 : DecidableEq.{succ u3} n] [_inst_6 : T2Space.{u2} R _inst_3] {f : X -> n -> R}, Eq.{max (succ u3) (succ u2)} (Matrix.{u3, u3, u2} n n R) (Matrix.diagonal.{u2, u3} n R (fun (a : n) (b : n) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (tsum.{max u3 u2, u1} (n -> R) (Pi.addCommMonoid.{u3, u2} n (fun (ᾰ : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u3, u2} n (fun (ᾰ : n) => R) (fun (a : n) => _inst_3)) X (fun (x : X) => f x))) (tsum.{max u3 u2, u1} (Matrix.{u3, u3, u2} n n R) (Matrix.addCommMonoid.{u2, u3, u3} n n R _inst_2) (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_3) X (fun (x : X) => Matrix.diagonal.{u2, u3} n R (fun (a : n) (b : n) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (f x)))
Case conversion may be inaccurate. Consider using '#align matrix.diagonal_tsum Matrix.diagonal_tsumₓ'. -/
theorem Matrix.diagonal_tsum [DecidableEq n] [T2Space R] {f : X → n → R} :
    diagonal (∑' x, f x) = ∑' x, diagonal (f x) :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.matrix_diagonal.tsum_eq.symm
  · have hft := summable_matrix_diagonal.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft]
    exact diagonal_zero
#align matrix.diagonal_tsum Matrix.diagonal_tsum

/- warning: has_sum.matrix_diag -> HasSum.matrix_diag is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] {f : X -> (Matrix.{u2, u2, u3} n n R)} {a : Matrix.{u2, u2, u3} n n R}, (HasSum.{max u2 u3, u1} (Matrix.{u2, u2, u3} n n R) X (Matrix.addCommMonoid.{u3, u2, u2} n n R _inst_2) (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_3) f a) -> (HasSum.{max u2 u3, u1} (n -> R) X (Pi.addCommMonoid.{u2, u3} n (fun (i : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u2, u3} n (fun (i : n) => R) (fun (a : n) => _inst_3)) (fun (x : X) => Matrix.diag.{u3, u2} n R (f x)) (Matrix.diag.{u3, u2} n R a))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] {f : X -> (Matrix.{u3, u3, u2} n n R)} {a : Matrix.{u3, u3, u2} n n R}, (HasSum.{max u3 u2, u1} (Matrix.{u3, u3, u2} n n R) X (Matrix.addCommMonoid.{u2, u3, u3} n n R _inst_2) (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_3) f a) -> (HasSum.{max u3 u2, u1} (n -> R) X (Pi.addCommMonoid.{u3, u2} n (fun (i : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u3, u2} n (fun (i : n) => R) (fun (a : n) => _inst_3)) (fun (x : X) => Matrix.diag.{u2, u3} n R (f x)) (Matrix.diag.{u2, u3} n R a))
Case conversion may be inaccurate. Consider using '#align has_sum.matrix_diag HasSum.matrix_diagₓ'. -/
theorem HasSum.matrix_diag {f : X → Matrix n n R} {a : Matrix n n R} (hf : HasSum f a) :
    HasSum (fun x => diag (f x)) (diag a) :=
  (hf.map (diagAddMonoidHom n R) continuous_matrix_diag : _)
#align has_sum.matrix_diag HasSum.matrix_diag

/- warning: summable.matrix_diag -> Summable.matrix_diag is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {n : Type.{u2}} {R : Type.{u3}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] {f : X -> (Matrix.{u2, u2, u3} n n R)}, (Summable.{max u2 u3, u1} (Matrix.{u2, u2, u3} n n R) X (Matrix.addCommMonoid.{u3, u2, u2} n n R _inst_2) (Matrix.topologicalSpace.{u2, u2, u3} n n R _inst_3) f) -> (Summable.{max u2 u3, u1} (n -> R) X (Pi.addCommMonoid.{u2, u3} n (fun (i : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u2, u3} n (fun (i : n) => R) (fun (a : n) => _inst_3)) (fun (x : X) => Matrix.diag.{u3, u2} n R (f x)))
but is expected to have type
  forall {X : Type.{u1}} {n : Type.{u3}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] {f : X -> (Matrix.{u3, u3, u2} n n R)}, (Summable.{max u3 u2, u1} (Matrix.{u3, u3, u2} n n R) X (Matrix.addCommMonoid.{u2, u3, u3} n n R _inst_2) (instTopologicalSpaceMatrix.{u3, u3, u2} n n R _inst_3) f) -> (Summable.{max u3 u2, u1} (n -> R) X (Pi.addCommMonoid.{u3, u2} n (fun (i : n) => R) (fun (i : n) => _inst_2)) (Pi.topologicalSpace.{u3, u2} n (fun (i : n) => R) (fun (a : n) => _inst_3)) (fun (x : X) => Matrix.diag.{u2, u3} n R (f x)))
Case conversion may be inaccurate. Consider using '#align summable.matrix_diag Summable.matrix_diagₓ'. -/
theorem Summable.matrix_diag {f : X → Matrix n n R} (hf : Summable f) :
    Summable fun x => diag (f x) :=
  hf.HasSum.matrix_diag.Summable
#align summable.matrix_diag Summable.matrix_diag

section BlockMatrices

/- warning: has_sum.matrix_block_diagonal -> HasSum.matrix_blockDiagonal is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {p : Type.{u4}} {R : Type.{u5}} [_inst_2 : AddCommMonoid.{u5} R] [_inst_3 : TopologicalSpace.{u5} R] [_inst_5 : DecidableEq.{succ u4} p] {f : X -> p -> (Matrix.{u2, u3, u5} m n R)} {a : p -> (Matrix.{u2, u3, u5} m n R)}, (HasSum.{max u4 u2 u3 u5, u1} (p -> (Matrix.{u2, u3, u5} m n R)) X (Pi.addCommMonoid.{u4, max u2 u3 u5} p (fun (ᾰ : p) => Matrix.{u2, u3, u5} m n R) (fun (i : p) => Matrix.addCommMonoid.{u5, u2, u3} m n R _inst_2)) (Pi.topologicalSpace.{u4, max u2 u3 u5} p (fun (ᾰ : p) => Matrix.{u2, u3, u5} m n R) (fun (a : p) => Matrix.topologicalSpace.{u2, u3, u5} m n R _inst_3)) f a) -> (HasSum.{max (max u2 u4) (max u3 u4) u5, u1} (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R) X (Matrix.addCommMonoid.{u5, max u2 u4, max u3 u4} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_3) (fun (x : X) => Matrix.blockDiagonal.{u2, u3, u4, u5} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddZeroClass.toHasZero.{u5} R (AddMonoid.toAddZeroClass.{u5} R (AddCommMonoid.toAddMonoid.{u5} R _inst_2))) (f x)) (Matrix.blockDiagonal.{u2, u3, u4, u5} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddZeroClass.toHasZero.{u5} R (AddMonoid.toAddZeroClass.{u5} R (AddCommMonoid.toAddMonoid.{u5} R _inst_2))) a))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {p : Type.{u5}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_5 : DecidableEq.{succ u5} p] {f : X -> p -> (Matrix.{u4, u3, u2} m n R)} {a : p -> (Matrix.{u4, u3, u2} m n R)}, (HasSum.{max (max (max u4 u3) u5) u2, u1} (p -> (Matrix.{u4, u3, u2} m n R)) X (Pi.addCommMonoid.{u5, max (max u4 u3) u2} p (fun (ᾰ : p) => Matrix.{u4, u3, u2} m n R) (fun (i : p) => Matrix.addCommMonoid.{u2, u4, u3} m n R _inst_2)) (Pi.topologicalSpace.{u5, max (max u4 u3) u2} p (fun (ᾰ : p) => Matrix.{u4, u3, u2} m n R) (fun (a : p) => instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_3)) f a) -> (HasSum.{max (max (max u2 u5) u3) u4, u1} (Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R) X (Matrix.addCommMonoid.{u2, max u4 u5, max u3 u5} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_2) (instTopologicalSpaceMatrix.{max u4 u5, max u3 u5, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_3) (fun (x : X) => Matrix.blockDiagonal.{u4, u3, u5, u2} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (f x)) (Matrix.blockDiagonal.{u4, u3, u5, u2} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) a))
Case conversion may be inaccurate. Consider using '#align has_sum.matrix_block_diagonal HasSum.matrix_blockDiagonalₓ'. -/
theorem HasSum.matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R}
    {a : p → Matrix m n R} (hf : HasSum f a) :
    HasSum (fun x => blockDiagonal (f x)) (blockDiagonal a) :=
  (hf.map (blockDiagonalAddMonoidHom m n p R) <| Continuous.matrix_blockDiagonal <| continuous_id :
    _)
#align has_sum.matrix_block_diagonal HasSum.matrix_blockDiagonal

/- warning: summable.matrix_block_diagonal -> Summable.matrix_blockDiagonal is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {p : Type.{u4}} {R : Type.{u5}} [_inst_2 : AddCommMonoid.{u5} R] [_inst_3 : TopologicalSpace.{u5} R] [_inst_5 : DecidableEq.{succ u4} p] {f : X -> p -> (Matrix.{u2, u3, u5} m n R)}, (Summable.{max u4 u2 u3 u5, u1} (p -> (Matrix.{u2, u3, u5} m n R)) X (Pi.addCommMonoid.{u4, max u2 u3 u5} p (fun (ᾰ : p) => Matrix.{u2, u3, u5} m n R) (fun (i : p) => Matrix.addCommMonoid.{u5, u2, u3} m n R _inst_2)) (Pi.topologicalSpace.{u4, max u2 u3 u5} p (fun (ᾰ : p) => Matrix.{u2, u3, u5} m n R) (fun (a : p) => Matrix.topologicalSpace.{u2, u3, u5} m n R _inst_3)) f) -> (Summable.{max (max u2 u4) (max u3 u4) u5, u1} (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R) X (Matrix.addCommMonoid.{u5, max u2 u4, max u3 u4} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_3) (fun (x : X) => Matrix.blockDiagonal.{u2, u3, u4, u5} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddZeroClass.toHasZero.{u5} R (AddMonoid.toAddZeroClass.{u5} R (AddCommMonoid.toAddMonoid.{u5} R _inst_2))) (f x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {p : Type.{u5}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_5 : DecidableEq.{succ u5} p] {f : X -> p -> (Matrix.{u4, u3, u2} m n R)}, (Summable.{max (max (max u4 u3) u5) u2, u1} (p -> (Matrix.{u4, u3, u2} m n R)) X (Pi.addCommMonoid.{u5, max (max u4 u3) u2} p (fun (ᾰ : p) => Matrix.{u4, u3, u2} m n R) (fun (i : p) => Matrix.addCommMonoid.{u2, u4, u3} m n R _inst_2)) (Pi.topologicalSpace.{u5, max (max u4 u3) u2} p (fun (ᾰ : p) => Matrix.{u4, u3, u2} m n R) (fun (a : p) => instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_3)) f) -> (Summable.{max (max (max u2 u5) u3) u4, u1} (Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R) X (Matrix.addCommMonoid.{u2, max u4 u5, max u3 u5} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_2) (instTopologicalSpaceMatrix.{max u4 u5, max u3 u5, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_3) (fun (x : X) => Matrix.blockDiagonal.{u4, u3, u5, u2} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (f x)))
Case conversion may be inaccurate. Consider using '#align summable.matrix_block_diagonal Summable.matrix_blockDiagonalₓ'. -/
theorem Summable.matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R} (hf : Summable f) :
    Summable fun x => blockDiagonal (f x) :=
  hf.HasSum.matrix_blockDiagonal.Summable
#align summable.matrix_block_diagonal Summable.matrix_blockDiagonal

/- warning: summable_matrix_block_diagonal -> summable_matrix_blockDiagonal is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {p : Type.{u4}} {R : Type.{u5}} [_inst_2 : AddCommMonoid.{u5} R] [_inst_3 : TopologicalSpace.{u5} R] [_inst_5 : DecidableEq.{succ u4} p] {f : X -> p -> (Matrix.{u2, u3, u5} m n R)}, Iff (Summable.{max (max u2 u4) (max u3 u4) u5, u1} (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R) X (Matrix.addCommMonoid.{u5, max u2 u4, max u3 u4} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_3) (fun (x : X) => Matrix.blockDiagonal.{u2, u3, u4, u5} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddZeroClass.toHasZero.{u5} R (AddMonoid.toAddZeroClass.{u5} R (AddCommMonoid.toAddMonoid.{u5} R _inst_2))) (f x))) (Summable.{max u4 u2 u3 u5, u1} (p -> (Matrix.{u2, u3, u5} m n R)) X (Pi.addCommMonoid.{u4, max u2 u3 u5} p (fun (ᾰ : p) => Matrix.{u2, u3, u5} m n R) (fun (i : p) => Matrix.addCommMonoid.{u5, u2, u3} m n R _inst_2)) (Pi.topologicalSpace.{u4, max u2 u3 u5} p (fun (ᾰ : p) => Matrix.{u2, u3, u5} m n R) (fun (a : p) => Matrix.topologicalSpace.{u2, u3, u5} m n R _inst_3)) f)
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {p : Type.{u5}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_5 : DecidableEq.{succ u5} p] {f : X -> p -> (Matrix.{u4, u3, u2} m n R)}, Iff (Summable.{max (max (max u2 u5) u3) u4, u1} (Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R) X (Matrix.addCommMonoid.{u2, max u4 u5, max u3 u5} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_2) (instTopologicalSpaceMatrix.{max u4 u5, max u3 u5, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_3) (fun (x : X) => Matrix.blockDiagonal.{u4, u3, u5, u2} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (f x))) (Summable.{max (max (max u4 u3) u5) u2, u1} (p -> (Matrix.{u4, u3, u2} m n R)) X (Pi.addCommMonoid.{u5, max (max u4 u3) u2} p (fun (ᾰ : p) => Matrix.{u4, u3, u2} m n R) (fun (i : p) => Matrix.addCommMonoid.{u2, u4, u3} m n R _inst_2)) (Pi.topologicalSpace.{u5, max (max u4 u3) u2} p (fun (ᾰ : p) => Matrix.{u4, u3, u2} m n R) (fun (a : p) => instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_3)) f)
Case conversion may be inaccurate. Consider using '#align summable_matrix_block_diagonal summable_matrix_blockDiagonalₓ'. -/
theorem summable_matrix_blockDiagonal [DecidableEq p] {f : X → p → Matrix m n R} :
    (Summable fun x => blockDiagonal (f x)) ↔ Summable f :=
  (Summable.map_iff_of_leftInverse (Matrix.blockDiagonalAddMonoidHom m n p R)
      (Matrix.blockDiagAddMonoidHom m n p R) (Continuous.matrix_blockDiagonal continuous_id)
      (Continuous.matrix_blockDiag continuous_id) fun A => blockDiag_blockDiagonal A :
    _)
#align summable_matrix_block_diagonal summable_matrix_blockDiagonal

/- warning: matrix.block_diagonal_tsum -> Matrix.blockDiagonal_tsum is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {p : Type.{u4}} {R : Type.{u5}} [_inst_2 : AddCommMonoid.{u5} R] [_inst_3 : TopologicalSpace.{u5} R] [_inst_5 : DecidableEq.{succ u4} p] [_inst_6 : T2Space.{u5} R _inst_3] {f : X -> p -> (Matrix.{u2, u3, u5} m n R)}, Eq.{succ (max (max u2 u4) (max u3 u4) u5)} (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R) (Matrix.blockDiagonal.{u2, u3, u4, u5} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddZeroClass.toHasZero.{u5} R (AddMonoid.toAddZeroClass.{u5} R (AddCommMonoid.toAddMonoid.{u5} R _inst_2))) (tsum.{max u4 u2 u3 u5, u1} (p -> (Matrix.{u2, u3, u5} m n R)) (Pi.addCommMonoid.{u4, max u2 u3 u5} p (fun (ᾰ : p) => Matrix.{u2, u3, u5} m n R) (fun (i : p) => Matrix.addCommMonoid.{u5, u2, u3} m n R _inst_2)) (Pi.topologicalSpace.{u4, max u2 u3 u5} p (fun (ᾰ : p) => Matrix.{u2, u3, u5} m n R) (fun (a : p) => Matrix.topologicalSpace.{u2, u3, u5} m n R _inst_3)) X (fun (x : X) => f x))) (tsum.{max (max u2 u4) (max u3 u4) u5, u1} (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R) (Matrix.addCommMonoid.{u5, max u2 u4, max u3 u4} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_3) X (fun (x : X) => Matrix.blockDiagonal.{u2, u3, u4, u5} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddZeroClass.toHasZero.{u5} R (AddMonoid.toAddZeroClass.{u5} R (AddCommMonoid.toAddMonoid.{u5} R _inst_2))) (f x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u3}} {n : Type.{u2}} {p : Type.{u5}} {R : Type.{u4}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : DecidableEq.{succ u5} p] [_inst_6 : T2Space.{u4} R _inst_3] {f : X -> p -> (Matrix.{u3, u2, u4} m n R)}, Eq.{max (max (max (succ u3) (succ u2)) (succ u5)) (succ u4)} (Matrix.{max u5 u3, max u5 u2, u4} (Prod.{u3, u5} m p) (Prod.{u2, u5} n p) R) (Matrix.blockDiagonal.{u3, u2, u5, u4} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddMonoid.toZero.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)) (tsum.{max (max (max u4 u5) u2) u3, u1} (p -> (Matrix.{u3, u2, u4} m n R)) (Pi.addCommMonoid.{u5, max (max u3 u2) u4} p (fun (ᾰ : p) => Matrix.{u3, u2, u4} m n R) (fun (i : p) => Matrix.addCommMonoid.{u4, u3, u2} m n R _inst_2)) (Pi.topologicalSpace.{u5, max (max u3 u2) u4} p (fun (ᾰ : p) => Matrix.{u3, u2, u4} m n R) (fun (a : p) => instTopologicalSpaceMatrix.{u3, u2, u4} m n R _inst_3)) X (fun (x : X) => f x))) (tsum.{max (max (max u4 u5) u2) u3, u1} (Matrix.{max u5 u3, max u5 u2, u4} (Prod.{u3, u5} m p) (Prod.{u2, u5} n p) R) (Matrix.addCommMonoid.{u4, max u3 u5, max u2 u5} (Prod.{u3, u5} m p) (Prod.{u2, u5} n p) R _inst_2) (instTopologicalSpaceMatrix.{max u3 u5, max u2 u5, u4} (Prod.{u3, u5} m p) (Prod.{u2, u5} n p) R _inst_3) X (fun (x : X) => Matrix.blockDiagonal.{u3, u2, u5, u4} m n p R (fun (a : p) (b : p) => _inst_5 a b) (AddMonoid.toZero.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)) (f x)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal_tsum Matrix.blockDiagonal_tsumₓ'. -/
theorem Matrix.blockDiagonal_tsum [DecidableEq p] [T2Space R] {f : X → p → Matrix m n R} :
    blockDiagonal (∑' x, f x) = ∑' x, blockDiagonal (f x) :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.matrix_block_diagonal.tsum_eq.symm
  · have hft := summable_matrix_block_diagonal.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft]
    exact block_diagonal_zero
#align matrix.block_diagonal_tsum Matrix.blockDiagonal_tsum

/- warning: has_sum.matrix_block_diag -> HasSum.matrix_blockDiag is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {p : Type.{u4}} {R : Type.{u5}} [_inst_2 : AddCommMonoid.{u5} R] [_inst_3 : TopologicalSpace.{u5} R] {f : X -> (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R)} {a : Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R}, (HasSum.{max (max u2 u4) (max u3 u4) u5, u1} (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R) X (Matrix.addCommMonoid.{u5, max u2 u4, max u3 u4} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_3) f a) -> (HasSum.{max u4 u2 u3 u5, u1} (p -> (Matrix.{u2, u3, u5} m n R)) X (Pi.addCommMonoid.{u4, max u2 u3 u5} p (fun (k : p) => Matrix.{u2, u3, u5} m n R) (fun (i : p) => Matrix.addCommMonoid.{u5, u2, u3} m n R _inst_2)) (Pi.topologicalSpace.{u4, max u2 u3 u5} p (fun (k : p) => Matrix.{u2, u3, u5} m n R) (fun (a : p) => Matrix.topologicalSpace.{u2, u3, u5} m n R _inst_3)) (fun (x : X) => Matrix.blockDiag.{u2, u3, u4, u5} m n p R (f x)) (Matrix.blockDiag.{u2, u3, u4, u5} m n p R a))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {p : Type.{u5}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] {f : X -> (Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R)} {a : Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R}, (HasSum.{max (max (max u4 u3) u5) u2, u1} (Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R) X (Matrix.addCommMonoid.{u2, max u4 u5, max u3 u5} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_2) (instTopologicalSpaceMatrix.{max u4 u5, max u3 u5, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_3) f a) -> (HasSum.{max (max (max u2 u5) u3) u4, u1} (p -> (Matrix.{u4, u3, u2} m n R)) X (Pi.addCommMonoid.{u5, max (max u4 u3) u2} p (fun (k : p) => Matrix.{u4, u3, u2} m n R) (fun (i : p) => Matrix.addCommMonoid.{u2, u4, u3} m n R _inst_2)) (Pi.topologicalSpace.{u5, max (max u4 u3) u2} p (fun (k : p) => Matrix.{u4, u3, u2} m n R) (fun (a : p) => instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_3)) (fun (x : X) => Matrix.blockDiag.{u4, u3, u5, u2} m n p R (f x)) (Matrix.blockDiag.{u4, u3, u5, u2} m n p R a))
Case conversion may be inaccurate. Consider using '#align has_sum.matrix_block_diag HasSum.matrix_blockDiagₓ'. -/
theorem HasSum.matrix_blockDiag {f : X → Matrix (m × p) (n × p) R} {a : Matrix (m × p) (n × p) R}
    (hf : HasSum f a) : HasSum (fun x => blockDiag (f x)) (blockDiag a) :=
  (hf.map (blockDiagAddMonoidHom m n p R) <| Continuous.matrix_blockDiag continuous_id : _)
#align has_sum.matrix_block_diag HasSum.matrix_blockDiag

/- warning: summable.matrix_block_diag -> Summable.matrix_blockDiag is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {m : Type.{u2}} {n : Type.{u3}} {p : Type.{u4}} {R : Type.{u5}} [_inst_2 : AddCommMonoid.{u5} R] [_inst_3 : TopologicalSpace.{u5} R] {f : X -> (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R)}, (Summable.{max (max u2 u4) (max u3 u4) u5, u1} (Matrix.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R) X (Matrix.addCommMonoid.{u5, max u2 u4, max u3 u4} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u3 u4, u5} (Prod.{u2, u4} m p) (Prod.{u3, u4} n p) R _inst_3) f) -> (Summable.{max u4 u2 u3 u5, u1} (p -> (Matrix.{u2, u3, u5} m n R)) X (Pi.addCommMonoid.{u4, max u2 u3 u5} p (fun (k : p) => Matrix.{u2, u3, u5} m n R) (fun (i : p) => Matrix.addCommMonoid.{u5, u2, u3} m n R _inst_2)) (Pi.topologicalSpace.{u4, max u2 u3 u5} p (fun (k : p) => Matrix.{u2, u3, u5} m n R) (fun (a : p) => Matrix.topologicalSpace.{u2, u3, u5} m n R _inst_3)) (fun (x : X) => Matrix.blockDiag.{u2, u3, u4, u5} m n p R (f x)))
but is expected to have type
  forall {X : Type.{u1}} {m : Type.{u4}} {n : Type.{u3}} {p : Type.{u5}} {R : Type.{u2}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] {f : X -> (Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R)}, (Summable.{max (max (max u4 u3) u5) u2, u1} (Matrix.{max u5 u4, max u5 u3, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R) X (Matrix.addCommMonoid.{u2, max u4 u5, max u3 u5} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_2) (instTopologicalSpaceMatrix.{max u4 u5, max u3 u5, u2} (Prod.{u4, u5} m p) (Prod.{u3, u5} n p) R _inst_3) f) -> (Summable.{max (max (max u2 u5) u3) u4, u1} (p -> (Matrix.{u4, u3, u2} m n R)) X (Pi.addCommMonoid.{u5, max (max u4 u3) u2} p (fun (k : p) => Matrix.{u4, u3, u2} m n R) (fun (i : p) => Matrix.addCommMonoid.{u2, u4, u3} m n R _inst_2)) (Pi.topologicalSpace.{u5, max (max u4 u3) u2} p (fun (k : p) => Matrix.{u4, u3, u2} m n R) (fun (a : p) => instTopologicalSpaceMatrix.{u4, u3, u2} m n R _inst_3)) (fun (x : X) => Matrix.blockDiag.{u4, u3, u5, u2} m n p R (f x)))
Case conversion may be inaccurate. Consider using '#align summable.matrix_block_diag Summable.matrix_blockDiagₓ'. -/
theorem Summable.matrix_blockDiag {f : X → Matrix (m × p) (n × p) R} (hf : Summable f) :
    Summable fun x => blockDiag (f x) :=
  hf.HasSum.matrix_blockDiag.Summable
#align summable.matrix_block_diag Summable.matrix_blockDiag

/- warning: has_sum.matrix_block_diagonal' -> HasSum.matrix_blockDiagonal' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {R : Type.{u3}} {m' : l -> Type.{u4}} {n' : l -> Type.{u5}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_5 : DecidableEq.{succ u2} l] {f : X -> (forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R)} {a : forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R}, (HasSum.{max u2 u4 u5 u3, u1} (forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R) X (Pi.addCommMonoid.{u2, max u4 u5 u3} l (fun (i : l) => Matrix.{u4, u5, u3} (m' i) (n' i) R) (fun (i : l) => Matrix.addCommMonoid.{u3, u4, u5} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u2, max u4 u5 u3} l (fun (i : l) => Matrix.{u4, u5, u3} (m' i) (n' i) R) (fun (a : l) => Matrix.topologicalSpace.{u4, u5, u3} (m' a) (n' a) R _inst_3)) f a) -> (HasSum.{max (max u2 u4) (max u2 u5) u3, u1} (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R) X (Matrix.addCommMonoid.{u3, max u2 u4, max u2 u5} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_3) (fun (x : X) => Matrix.blockDiagonal'.{u2, u4, u5, u3} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) (f x)) (Matrix.blockDiagonal'.{u2, u4, u5, u3} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) a))
but is expected to have type
  forall {X : Type.{u1}} {l : Type.{u5}} {R : Type.{u2}} {m' : l -> Type.{u4}} {n' : l -> Type.{u3}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_5 : DecidableEq.{succ u5} l] {f : X -> (forall (i : l), Matrix.{u4, u3, u2} (m' i) (n' i) R)} {a : forall (i : l), Matrix.{u4, u3, u2} (m' i) (n' i) R}, (HasSum.{max (max (max u5 u2) u4) u3, u1} (forall (i : l), Matrix.{u4, u3, u2} (m' i) (n' i) R) X (Pi.addCommMonoid.{u5, max (max u2 u4) u3} l (fun (i : l) => Matrix.{u4, u3, u2} (m' i) (n' i) R) (fun (i : l) => Matrix.addCommMonoid.{u2, u4, u3} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u5, max (max u2 u4) u3} l (fun (i : l) => Matrix.{u4, u3, u2} (m' i) (n' i) R) (fun (a : l) => instTopologicalSpaceMatrix.{u4, u3, u2} (m' a) (n' a) R _inst_3)) f a) -> (HasSum.{max (max (max u2 u3) u4) u5, u1} (Matrix.{max u4 u5, max u3 u5, u2} (Sigma.{u5, u4} l (fun (i : l) => m' i)) (Sigma.{u5, u3} l (fun (i : l) => n' i)) R) X (Matrix.addCommMonoid.{u2, max u5 u4, max u5 u3} (Sigma.{u5, u4} l (fun (i : l) => m' i)) (Sigma.{u5, u3} l (fun (i : l) => n' i)) R _inst_2) (instTopologicalSpaceMatrix.{max u5 u4, max u5 u3, u2} (Sigma.{u5, u4} l (fun (i : l) => m' i)) (Sigma.{u5, u3} l (fun (i : l) => n' i)) R _inst_3) (fun (x : X) => Matrix.blockDiagonal'.{u5, u4, u3, u2} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (f x)) (Matrix.blockDiagonal'.{u5, u4, u3, u2} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) a))
Case conversion may be inaccurate. Consider using '#align has_sum.matrix_block_diagonal' HasSum.matrix_blockDiagonal'ₓ'. -/
theorem HasSum.matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R}
    {a : ∀ i, Matrix (m' i) (n' i) R} (hf : HasSum f a) :
    HasSum (fun x => blockDiagonal' (f x)) (blockDiagonal' a) :=
  (hf.map (blockDiagonal'AddMonoidHom m' n' R) <|
      Continuous.matrix_blockDiagonal' <| continuous_id :
    _)
#align has_sum.matrix_block_diagonal' HasSum.matrix_blockDiagonal'

/- warning: summable.matrix_block_diagonal' -> Summable.matrix_blockDiagonal' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {R : Type.{u3}} {m' : l -> Type.{u4}} {n' : l -> Type.{u5}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_5 : DecidableEq.{succ u2} l] {f : X -> (forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R)}, (Summable.{max u2 u4 u5 u3, u1} (forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R) X (Pi.addCommMonoid.{u2, max u4 u5 u3} l (fun (i : l) => Matrix.{u4, u5, u3} (m' i) (n' i) R) (fun (i : l) => Matrix.addCommMonoid.{u3, u4, u5} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u2, max u4 u5 u3} l (fun (i : l) => Matrix.{u4, u5, u3} (m' i) (n' i) R) (fun (a : l) => Matrix.topologicalSpace.{u4, u5, u3} (m' a) (n' a) R _inst_3)) f) -> (Summable.{max (max u2 u4) (max u2 u5) u3, u1} (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R) X (Matrix.addCommMonoid.{u3, max u2 u4, max u2 u5} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_3) (fun (x : X) => Matrix.blockDiagonal'.{u2, u4, u5, u3} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) (f x)))
but is expected to have type
  forall {X : Type.{u1}} {l : Type.{u5}} {R : Type.{u2}} {m' : l -> Type.{u4}} {n' : l -> Type.{u3}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_5 : DecidableEq.{succ u5} l] {f : X -> (forall (i : l), Matrix.{u4, u3, u2} (m' i) (n' i) R)}, (Summable.{max (max (max u5 u2) u4) u3, u1} (forall (i : l), Matrix.{u4, u3, u2} (m' i) (n' i) R) X (Pi.addCommMonoid.{u5, max (max u2 u4) u3} l (fun (i : l) => Matrix.{u4, u3, u2} (m' i) (n' i) R) (fun (i : l) => Matrix.addCommMonoid.{u2, u4, u3} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u5, max (max u2 u4) u3} l (fun (i : l) => Matrix.{u4, u3, u2} (m' i) (n' i) R) (fun (a : l) => instTopologicalSpaceMatrix.{u4, u3, u2} (m' a) (n' a) R _inst_3)) f) -> (Summable.{max (max (max u2 u3) u4) u5, u1} (Matrix.{max u4 u5, max u3 u5, u2} (Sigma.{u5, u4} l (fun (i : l) => m' i)) (Sigma.{u5, u3} l (fun (i : l) => n' i)) R) X (Matrix.addCommMonoid.{u2, max u5 u4, max u5 u3} (Sigma.{u5, u4} l (fun (i : l) => m' i)) (Sigma.{u5, u3} l (fun (i : l) => n' i)) R _inst_2) (instTopologicalSpaceMatrix.{max u5 u4, max u5 u3, u2} (Sigma.{u5, u4} l (fun (i : l) => m' i)) (Sigma.{u5, u3} l (fun (i : l) => n' i)) R _inst_3) (fun (x : X) => Matrix.blockDiagonal'.{u5, u4, u3, u2} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (f x)))
Case conversion may be inaccurate. Consider using '#align summable.matrix_block_diagonal' Summable.matrix_blockDiagonal'ₓ'. -/
theorem Summable.matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R}
    (hf : Summable f) : Summable fun x => blockDiagonal' (f x) :=
  hf.HasSum.matrix_blockDiagonal'.Summable
#align summable.matrix_block_diagonal' Summable.matrix_blockDiagonal'

/- warning: summable_matrix_block_diagonal' -> summable_matrix_blockDiagonal' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {R : Type.{u3}} {m' : l -> Type.{u4}} {n' : l -> Type.{u5}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_5 : DecidableEq.{succ u2} l] {f : X -> (forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R)}, Iff (Summable.{max (max u2 u4) (max u2 u5) u3, u1} (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R) X (Matrix.addCommMonoid.{u3, max u2 u4, max u2 u5} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_3) (fun (x : X) => Matrix.blockDiagonal'.{u2, u4, u5, u3} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) (f x))) (Summable.{max u2 u4 u5 u3, u1} (forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R) X (Pi.addCommMonoid.{u2, max u4 u5 u3} l (fun (i : l) => Matrix.{u4, u5, u3} (m' i) (n' i) R) (fun (i : l) => Matrix.addCommMonoid.{u3, u4, u5} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u2, max u4 u5 u3} l (fun (i : l) => Matrix.{u4, u5, u3} (m' i) (n' i) R) (fun (a : l) => Matrix.topologicalSpace.{u4, u5, u3} (m' a) (n' a) R _inst_3)) f)
but is expected to have type
  forall {X : Type.{u1}} {l : Type.{u5}} {R : Type.{u2}} {m' : l -> Type.{u4}} {n' : l -> Type.{u3}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] [_inst_5 : DecidableEq.{succ u5} l] {f : X -> (forall (i : l), Matrix.{u4, u3, u2} (m' i) (n' i) R)}, Iff (Summable.{max (max (max u2 u3) u4) u5, u1} (Matrix.{max u4 u5, max u3 u5, u2} (Sigma.{u5, u4} l (fun (i : l) => m' i)) (Sigma.{u5, u3} l (fun (i : l) => n' i)) R) X (Matrix.addCommMonoid.{u2, max u5 u4, max u5 u3} (Sigma.{u5, u4} l (fun (i : l) => m' i)) (Sigma.{u5, u3} l (fun (i : l) => n' i)) R _inst_2) (instTopologicalSpaceMatrix.{max u5 u4, max u5 u3, u2} (Sigma.{u5, u4} l (fun (i : l) => m' i)) (Sigma.{u5, u3} l (fun (i : l) => n' i)) R _inst_3) (fun (x : X) => Matrix.blockDiagonal'.{u5, u4, u3, u2} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddMonoid.toZero.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_2)) (f x))) (Summable.{max (max (max u5 u2) u4) u3, u1} (forall (i : l), Matrix.{u4, u3, u2} (m' i) (n' i) R) X (Pi.addCommMonoid.{u5, max (max u2 u4) u3} l (fun (i : l) => Matrix.{u4, u3, u2} (m' i) (n' i) R) (fun (i : l) => Matrix.addCommMonoid.{u2, u4, u3} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u5, max (max u2 u4) u3} l (fun (i : l) => Matrix.{u4, u3, u2} (m' i) (n' i) R) (fun (a : l) => instTopologicalSpaceMatrix.{u4, u3, u2} (m' a) (n' a) R _inst_3)) f)
Case conversion may be inaccurate. Consider using '#align summable_matrix_block_diagonal' summable_matrix_blockDiagonal'ₓ'. -/
theorem summable_matrix_blockDiagonal' [DecidableEq l] {f : X → ∀ i, Matrix (m' i) (n' i) R} :
    (Summable fun x => blockDiagonal' (f x)) ↔ Summable f :=
  (Summable.map_iff_of_leftInverse (Matrix.blockDiagonal'AddMonoidHom m' n' R)
      (Matrix.blockDiag'AddMonoidHom m' n' R) (Continuous.matrix_blockDiagonal' continuous_id)
      (Continuous.matrix_blockDiag' continuous_id) fun A => blockDiag'_blockDiagonal' A :
    _)
#align summable_matrix_block_diagonal' summable_matrix_blockDiagonal'

/- warning: matrix.block_diagonal'_tsum -> Matrix.blockDiagonal'_tsum is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {R : Type.{u3}} {m' : l -> Type.{u4}} {n' : l -> Type.{u5}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] [_inst_5 : DecidableEq.{succ u2} l] [_inst_6 : T2Space.{u3} R _inst_3] {f : X -> (forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R)}, Eq.{succ (max (max u2 u4) (max u2 u5) u3)} (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R) (Matrix.blockDiagonal'.{u2, u4, u5, u3} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) (tsum.{max u2 u4 u5 u3, u1} (forall (i : l), Matrix.{u4, u5, u3} (m' i) (n' i) R) (Pi.addCommMonoid.{u2, max u4 u5 u3} l (fun (i : l) => Matrix.{u4, u5, u3} (m' i) (n' i) R) (fun (i : l) => Matrix.addCommMonoid.{u3, u4, u5} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u2, max u4 u5 u3} l (fun (i : l) => Matrix.{u4, u5, u3} (m' i) (n' i) R) (fun (a : l) => Matrix.topologicalSpace.{u4, u5, u3} (m' a) (n' a) R _inst_3)) X (fun (x : X) => f x))) (tsum.{max (max u2 u4) (max u2 u5) u3, u1} (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R) (Matrix.addCommMonoid.{u3, max u2 u4, max u2 u5} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_3) X (fun (x : X) => Matrix.blockDiagonal'.{u2, u4, u5, u3} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_2))) (f x)))
but is expected to have type
  forall {X : Type.{u1}} {l : Type.{u5}} {R : Type.{u4}} {m' : l -> Type.{u3}} {n' : l -> Type.{u2}} [_inst_2 : AddCommMonoid.{u4} R] [_inst_3 : TopologicalSpace.{u4} R] [_inst_5 : DecidableEq.{succ u5} l] [_inst_6 : T2Space.{u4} R _inst_3] {f : X -> (forall (i : l), Matrix.{u3, u2, u4} (m' i) (n' i) R)}, Eq.{max (max (max (succ u5) (succ u4)) (succ u3)) (succ u2)} (Matrix.{max u3 u5, max u2 u5, u4} (Sigma.{u5, u3} l (fun (i : l) => m' i)) (Sigma.{u5, u2} l (fun (i : l) => n' i)) R) (Matrix.blockDiagonal'.{u5, u3, u2, u4} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddMonoid.toZero.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)) (tsum.{max (max (max u4 u2) u3) u5, u1} (forall (i : l), Matrix.{u3, u2, u4} (m' i) (n' i) R) (Pi.addCommMonoid.{u5, max (max u4 u3) u2} l (fun (i : l) => Matrix.{u3, u2, u4} (m' i) (n' i) R) (fun (i : l) => Matrix.addCommMonoid.{u4, u3, u2} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u5, max (max u4 u3) u2} l (fun (i : l) => Matrix.{u3, u2, u4} (m' i) (n' i) R) (fun (a : l) => instTopologicalSpaceMatrix.{u3, u2, u4} (m' a) (n' a) R _inst_3)) X (fun (x : X) => f x))) (tsum.{max (max (max u4 u2) u3) u5, u1} (Matrix.{max u3 u5, max u2 u5, u4} (Sigma.{u5, u3} l (fun (i : l) => m' i)) (Sigma.{u5, u2} l (fun (i : l) => n' i)) R) (Matrix.addCommMonoid.{u4, max u5 u3, max u5 u2} (Sigma.{u5, u3} l (fun (i : l) => m' i)) (Sigma.{u5, u2} l (fun (i : l) => n' i)) R _inst_2) (instTopologicalSpaceMatrix.{max u5 u3, max u5 u2, u4} (Sigma.{u5, u3} l (fun (i : l) => m' i)) (Sigma.{u5, u2} l (fun (i : l) => n' i)) R _inst_3) X (fun (x : X) => Matrix.blockDiagonal'.{u5, u3, u2, u4} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (fun (a : l) (b : l) => _inst_5 a b) (AddMonoid.toZero.{u4} R (AddCommMonoid.toAddMonoid.{u4} R _inst_2)) (f x)))
Case conversion may be inaccurate. Consider using '#align matrix.block_diagonal'_tsum Matrix.blockDiagonal'_tsumₓ'. -/
theorem Matrix.blockDiagonal'_tsum [DecidableEq l] [T2Space R]
    {f : X → ∀ i, Matrix (m' i) (n' i) R} :
    blockDiagonal' (∑' x, f x) = ∑' x, blockDiagonal' (f x) :=
  by
  by_cases hf : Summable f
  · exact hf.has_sum.matrix_block_diagonal'.tsum_eq.symm
  · have hft := summable_matrix_block_diagonal'.not.mpr hf
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hft]
    exact block_diagonal'_zero
#align matrix.block_diagonal'_tsum Matrix.blockDiagonal'_tsum

/- warning: has_sum.matrix_block_diag' -> HasSum.matrix_blockDiag' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {R : Type.{u3}} {m' : l -> Type.{u4}} {n' : l -> Type.{u5}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] {f : X -> (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R)} {a : Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R}, (HasSum.{max (max u2 u4) (max u2 u5) u3, u1} (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R) X (Matrix.addCommMonoid.{u3, max u2 u4, max u2 u5} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_3) f a) -> (HasSum.{max u2 u4 u5 u3, u1} (forall (k : l), Matrix.{u4, u5, u3} (m' k) (n' k) R) X (Pi.addCommMonoid.{u2, max u4 u5 u3} l (fun (k : l) => Matrix.{u4, u5, u3} (m' k) (n' k) R) (fun (i : l) => Matrix.addCommMonoid.{u3, u4, u5} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u2, max u4 u5 u3} l (fun (k : l) => Matrix.{u4, u5, u3} (m' k) (n' k) R) (fun (a : l) => Matrix.topologicalSpace.{u4, u5, u3} (m' a) (n' a) R _inst_3)) (fun (x : X) => Matrix.blockDiag'.{u2, u4, u5, u3} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (f x)) (Matrix.blockDiag'.{u2, u4, u5, u3} l (fun (k : l) => m' k) (fun (k : l) => n' k) R a))
but is expected to have type
  forall {X : Type.{u1}} {l : Type.{u4}} {R : Type.{u2}} {m' : l -> Type.{u5}} {n' : l -> Type.{u3}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] {f : X -> (Matrix.{max u5 u4, max u3 u4, u2} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R)} {a : Matrix.{max u5 u4, max u3 u4, u2} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R}, (HasSum.{max (max (max u4 u2) u5) u3, u1} (Matrix.{max u5 u4, max u3 u4, u2} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R) X (Matrix.addCommMonoid.{u2, max u4 u5, max u4 u3} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R _inst_2) (instTopologicalSpaceMatrix.{max u4 u5, max u4 u3, u2} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R _inst_3) f a) -> (HasSum.{max (max (max u2 u3) u5) u4, u1} (forall (k : l), Matrix.{u5, u3, u2} (m' k) (n' k) R) X (Pi.addCommMonoid.{u4, max (max u2 u5) u3} l (fun (k : l) => Matrix.{u5, u3, u2} (m' k) (n' k) R) (fun (i : l) => Matrix.addCommMonoid.{u2, u5, u3} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u4, max (max u2 u5) u3} l (fun (k : l) => Matrix.{u5, u3, u2} (m' k) (n' k) R) (fun (a : l) => instTopologicalSpaceMatrix.{u5, u3, u2} (m' a) (n' a) R _inst_3)) (fun (x : X) => Matrix.blockDiag'.{u4, u5, u3, u2} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (f x)) (Matrix.blockDiag'.{u4, u5, u3, u2} l (fun (k : l) => m' k) (fun (k : l) => n' k) R a))
Case conversion may be inaccurate. Consider using '#align has_sum.matrix_block_diag' HasSum.matrix_blockDiag'ₓ'. -/
theorem HasSum.matrix_blockDiag' {f : X → Matrix (Σi, m' i) (Σi, n' i) R}
    {a : Matrix (Σi, m' i) (Σi, n' i) R} (hf : HasSum f a) :
    HasSum (fun x => blockDiag' (f x)) (blockDiag' a) :=
  (hf.map (blockDiag'AddMonoidHom m' n' R) <| Continuous.matrix_blockDiag' continuous_id : _)
#align has_sum.matrix_block_diag' HasSum.matrix_blockDiag'

/- warning: summable.matrix_block_diag' -> Summable.matrix_blockDiag' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {l : Type.{u2}} {R : Type.{u3}} {m' : l -> Type.{u4}} {n' : l -> Type.{u5}} [_inst_2 : AddCommMonoid.{u3} R] [_inst_3 : TopologicalSpace.{u3} R] {f : X -> (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R)}, (Summable.{max (max u2 u4) (max u2 u5) u3, u1} (Matrix.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R) X (Matrix.addCommMonoid.{u3, max u2 u4, max u2 u5} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_2) (Matrix.topologicalSpace.{max u2 u4, max u2 u5, u3} (Sigma.{u2, u4} l (fun (i : l) => m' i)) (Sigma.{u2, u5} l (fun (i : l) => n' i)) R _inst_3) f) -> (Summable.{max u2 u4 u5 u3, u1} (forall (k : l), Matrix.{u4, u5, u3} (m' k) (n' k) R) X (Pi.addCommMonoid.{u2, max u4 u5 u3} l (fun (k : l) => Matrix.{u4, u5, u3} (m' k) (n' k) R) (fun (i : l) => Matrix.addCommMonoid.{u3, u4, u5} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u2, max u4 u5 u3} l (fun (k : l) => Matrix.{u4, u5, u3} (m' k) (n' k) R) (fun (a : l) => Matrix.topologicalSpace.{u4, u5, u3} (m' a) (n' a) R _inst_3)) (fun (x : X) => Matrix.blockDiag'.{u2, u4, u5, u3} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (f x)))
but is expected to have type
  forall {X : Type.{u1}} {l : Type.{u4}} {R : Type.{u2}} {m' : l -> Type.{u5}} {n' : l -> Type.{u3}} [_inst_2 : AddCommMonoid.{u2} R] [_inst_3 : TopologicalSpace.{u2} R] {f : X -> (Matrix.{max u5 u4, max u3 u4, u2} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R)}, (Summable.{max (max (max u4 u2) u5) u3, u1} (Matrix.{max u5 u4, max u3 u4, u2} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R) X (Matrix.addCommMonoid.{u2, max u4 u5, max u4 u3} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R _inst_2) (instTopologicalSpaceMatrix.{max u4 u5, max u4 u3, u2} (Sigma.{u4, u5} l (fun (i : l) => m' i)) (Sigma.{u4, u3} l (fun (i : l) => n' i)) R _inst_3) f) -> (Summable.{max (max (max u2 u3) u5) u4, u1} (forall (k : l), Matrix.{u5, u3, u2} (m' k) (n' k) R) X (Pi.addCommMonoid.{u4, max (max u2 u5) u3} l (fun (k : l) => Matrix.{u5, u3, u2} (m' k) (n' k) R) (fun (i : l) => Matrix.addCommMonoid.{u2, u5, u3} (m' i) (n' i) R _inst_2)) (Pi.topologicalSpace.{u4, max (max u2 u5) u3} l (fun (k : l) => Matrix.{u5, u3, u2} (m' k) (n' k) R) (fun (a : l) => instTopologicalSpaceMatrix.{u5, u3, u2} (m' a) (n' a) R _inst_3)) (fun (x : X) => Matrix.blockDiag'.{u4, u5, u3, u2} l (fun (i : l) => m' i) (fun (i : l) => n' i) R (f x)))
Case conversion may be inaccurate. Consider using '#align summable.matrix_block_diag' Summable.matrix_blockDiag'ₓ'. -/
theorem Summable.matrix_blockDiag' {f : X → Matrix (Σi, m' i) (Σi, n' i) R} (hf : Summable f) :
    Summable fun x => blockDiag' (f x) :=
  hf.HasSum.matrix_blockDiag'.Summable
#align summable.matrix_block_diag' Summable.matrix_blockDiag'

end BlockMatrices

end tsum

