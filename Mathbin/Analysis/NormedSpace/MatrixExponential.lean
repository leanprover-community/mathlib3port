/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Analysis.NormedSpace.Exponential
import Mathbin.Analysis.Matrix
import Mathbin.LinearAlgebra.Matrix.Zpow
import Mathbin.Topology.UniformSpace.Matrix

/-!
# Lemmas about the matrix exponential

In this file, we provide results about `exp` on `matrix`s over a topological or normed algebra.
Note that generic results over all topological spaces such as `exp_zero` can be used on matrices
without issue, so are not repeated here. The topological results specific to matrices are:

* `matrix.exp_transpose`
* `matrix.exp_conj_transpose`
* `matrix.exp_diagonal`
* `matrix.exp_block_diagonal`
* `matrix.exp_block_diagonal'`

Lemmas like `exp_add_of_commute` require a canonical norm on the type; while there are multiple
sensible choices for the norm of a `matrix` (`matrix.normed_group`, `matrix.frobenius_normed_group`,
`matrix.linfty_op_normed_group`), none of them are canonical. In an application where a particular
norm is chosen using `local attribute [instance]`, then the usual lemmas about `exp` are fine. When
choosing a norm is undesirable, the results in this file can be used.

In this file, we copy across the lemmas about `exp`, but hide the requirement for a norm inside the
proof.

* `matrix.exp_add_of_commute`
* `matrix.exp_sum_of_commute`
* `matrix.exp_nsmul`
* `matrix.is_unit_exp`
* `matrix.exp_units_conj`
* `matrix.exp_units_conj'`

Additionally, we prove some results about `matrix.has_inv` and `matrix.div_inv_monoid`, as the
results for general rings are instead stated about `ring.inverse`:

* `matrix.exp_neg`
* `matrix.exp_zsmul`
* `matrix.exp_conj`
* `matrix.exp_conj'`

## Implementation notes

This file runs into some sharp edges on typeclass search in lean 3, especially regarding pi types.
To work around this, we copy a handful of instances for when lean can't find them by itself.
Hopefully we will be able to remove these in Lean 4.

## TODO

* Show that `matrix.det (exp ???? A) = exp ???? (matrix.trace A)`

## References

* https://en.wikipedia.org/wiki/Matrix_exponential
-/


open Matrix BigOperators

section HacksForPiInstanceSearch

/-- A special case of `pi.topological_ring` for when `R` is not dependently typed. -/
instance Function.topological_ring (I : Type _) (R : Type _) [NonUnitalRing R] [TopologicalSpace R]
    [TopologicalRing R] : TopologicalRing (I ??? R) :=
  Pi.topological_ring

/-- A special case of `function.algebra` for when A is a `ring` not a `semiring` -/
instance Function.algebraRing (I : Type _) {R : Type _} (A : Type _) [CommSemiring??? R] [Ring??? A] [Algebra R A] :
    Algebra R (I ??? A) :=
  Pi.algebra _ _

/-- A special case of `pi.algebra` for when `f = ?? i, matrix (m i) (m i) A`. -/
instance Pi.matrixAlgebra (I R A : Type _) (m : I ??? Type _) [CommSemiring??? R] [Semiring??? A] [Algebra R A]
    [??? i, Fintype (m i)] [??? i, DecidableEq (m i)] : Algebra R (??? i, Matrix (m i) (m i) A) :=
  @Pi.algebra I R (fun i => Matrix (m i) (m i) A) _ _ fun i => Matrix.algebra

/-- A special case of `pi.topological_ring` for when `f = ?? i, matrix (m i) (m i) A`. -/
instance Pi.matrix_topological_ring (I A : Type _) (m : I ??? Type _) [Ring??? A] [TopologicalSpace A] [TopologicalRing A]
    [??? i, Fintype (m i)] : TopologicalRing (??? i, Matrix (m i) (m i) A) :=
  @Pi.topological_ring _ (fun i => Matrix (m i) (m i) A) _ _ fun i => Matrix.topological_ring

end HacksForPiInstanceSearch

variable (???? : Type _) {m n p : Type _} {n' : m ??? Type _} {???? : Type _}

namespace Matrix

section Topological

section Ring???

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [??? i, Fintype (n' i)] [??? i, DecidableEq (n' i)]
  [Field ????] [Ring??? ????] [TopologicalSpace ????] [TopologicalRing ????] [Algebra ???? ????] [T2Space ????]

theorem exp_diagonal (v : m ??? ????) : exp ???? (diagonal??? v) = diagonal??? (exp ???? v) := by
  simp_rw [exp_eq_tsum, diagonal_pow, ??? diagonal_smul, ??? diagonal_tsum]

theorem exp_block_diagonal (v : m ??? Matrix n n ????) : exp ???? (blockDiagonal??? v) = blockDiagonal??? (exp ???? v) := by
  simp_rw [exp_eq_tsum, ??? block_diagonal_pow, ??? block_diagonal_smul, ??? block_diagonal_tsum]

theorem exp_block_diagonal' (v : ??? i, Matrix (n' i) (n' i) ????) : exp ???? (blockDiagonal'??? v) = blockDiagonal'??? (exp ???? v) :=
  by
  simp_rw [exp_eq_tsum, ??? block_diagonal'_pow, ??? block_diagonal'_smul, ??? block_diagonal'_tsum]

theorem exp_conj_transpose [StarRing ????] [HasContinuousStar ????] (A : Matrix m m ????) : exp ???? A??? = (exp ???? A)??? :=
  (star_exp A).symm

end Ring???

section CommRing???

variable [Fintype m] [DecidableEq m] [Field ????] [CommRing??? ????] [TopologicalSpace ????] [TopologicalRing ????] [Algebra ???? ????]
  [T2Space ????]

theorem exp_transpose (A : Matrix m m ????) : exp ???? A??? = (exp ???? A)??? := by
  simp_rw [exp_eq_tsum, transpose_tsum, transpose_smul, transpose_pow]

end CommRing???

end Topological

section Normed

variable [IsROrC ????] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [??? i, Fintype (n' i)]
  [??? i, DecidableEq (n' i)] [NormedRing ????] [NormedAlgebra ???? ????] [CompleteSpace ????]

theorem exp_add_of_commute (A B : Matrix m m ????) (h : Commute A B) : exp ???? (A + B) = exp ???? A ??? exp ???? B := by
  let this : SemiNormedRing (Matrix m m ????) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m ????) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra ???? (Matrix m m ????) := Matrix.linftyOpNormedAlgebra
  exact exp_add_of_commute h

theorem exp_sum_of_commute {??} (s : Finset ??) (f : ?? ??? Matrix m m ????)
    (h : ???, ??? i ??? s, ???, ??? j ??? s, ???, Commute (f i) (f j)) :
    exp ???? (??? i in s, f i) = s.noncommProd (fun i => exp ???? (f i)) fun i hi j hj => (h i hi j hj).exp ???? := by
  let this : SemiNormedRing (Matrix m m ????) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m ????) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra ???? (Matrix m m ????) := Matrix.linftyOpNormedAlgebra
  exact exp_sum_of_commute s f h

theorem exp_nsmul (n : ???) (A : Matrix m m ????) : exp ???? (n ??? A) = exp ???? A ^ n := by
  let this : SemiNormedRing (Matrix m m ????) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m ????) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra ???? (Matrix m m ????) := Matrix.linftyOpNormedAlgebra
  exact exp_nsmul n A

theorem is_unit_exp (A : Matrix m m ????) : IsUnit (exp ???? A) := by
  let this : SemiNormedRing (Matrix m m ????) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m ????) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra ???? (Matrix m m ????) := Matrix.linftyOpNormedAlgebra
  exact is_unit_exp _ A

theorem exp_units_conj (U : (Matrix m m ????)??) (A : Matrix m m ????) :
    exp ???? (???U ??? A ??? ???U????? : Matrix m m ????) = ???U ??? exp ???? A ??? ???U????? := by
  let this : SemiNormedRing (Matrix m m ????) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m ????) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra ???? (Matrix m m ????) := Matrix.linftyOpNormedAlgebra
  exact exp_units_conj _ U A

theorem exp_units_conj' (U : (Matrix m m ????)??) (A : Matrix m m ????) :
    exp ???? (???U????? ??? A ??? U : Matrix m m ????) = ???U????? ??? exp ???? A ??? U :=
  exp_units_conj ???? U????? A

end Normed

section NormedComm

variable [IsROrC ????] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [??? i, Fintype (n' i)]
  [??? i, DecidableEq (n' i)] [NormedCommRing ????] [NormedAlgebra ???? ????] [CompleteSpace ????]

theorem exp_neg (A : Matrix m m ????) : exp ???? (-A) = (exp ???? A)????? := by
  rw [nonsing_inv_eq_ring_inverse]
  let this : SemiNormedRing (Matrix m m ????) := Matrix.linftyOpSemiNormedRing
  let this : NormedRing (Matrix m m ????) := Matrix.linftyOpNormedRing
  let this : NormedAlgebra ???? (Matrix m m ????) := Matrix.linftyOpNormedAlgebra
  exact (Ring???.inverse_exp _ A).symm

theorem exp_zsmul (z : ???) (A : Matrix m m ????) : exp ???? (z ??? A) = exp ???? A ^ z := by
  obtain ???n, rfl | rfl??? := z.eq_coe_or_neg
  ?? rw [zpow_coe_nat, coe_nat_zsmul, exp_nsmul]
    
  ?? have : IsUnit (exp ???? A).det := (Matrix.is_unit_iff_is_unit_det _).mp (is_unit_exp _ _)
    rw [Matrix.zpow_neg this, zpow_coe_nat, neg_smul, exp_neg, coe_nat_zsmul, exp_nsmul]
    

theorem exp_conj (U : Matrix m m ????) (A : Matrix m m ????) (hy : IsUnit U) : exp ???? (U ??? A ??? U?????) = U ??? exp ???? A ??? U????? :=
  let ???u, hu??? := hy
  hu ??? by
    simpa only [??? Matrix.coe_units_inv] using exp_units_conj ???? u A

theorem exp_conj' (U : Matrix m m ????) (A : Matrix m m ????) (hy : IsUnit U) : exp ???? (U????? ??? A ??? U) = U????? ??? exp ???? A ??? U :=
  let ???u, hu??? := hy
  hu ??? by
    simpa only [??? Matrix.coe_units_inv] using exp_units_conj' ???? u A

end NormedComm

end Matrix

