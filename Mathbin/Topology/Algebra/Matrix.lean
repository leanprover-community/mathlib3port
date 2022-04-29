/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Eric Wieser
-/
import Mathbin.LinearAlgebra.Determinant
import Mathbin.Topology.Algebra.Ring

/-!
# Topological properties of matrices

This file is a place to collect topological results about matrices.

## Main definitions:

 * `matrix.topological_ring`: square matrices form a topological ring
 * `continuous.matrix_det`: the determinant is continuous over a topological ring.
 * `continuous.matrix_adjugate`: the adjugate is continuous over a topological ring.
-/


open Matrix

open Matrix

variable {X α l m n p S R : Type _} {m' n' : l → Type _}

variable [TopologicalSpace X] [TopologicalSpace R]

instance : TopologicalSpace (Matrix m n R) :=
  Pi.topologicalSpace

instance [HasScalar α R] [HasContinuousConstSmul α R] : HasContinuousConstSmul α (Matrix n n R) :=
  Pi.has_continuous_const_smul

instance [TopologicalSpace α] [HasScalar α R] [HasContinuousSmul α R] : HasContinuousSmul α (Matrix n n R) :=
  Pi.has_continuous_smul

/-- To show a function into matrices is continuous it suffices to show the coefficients of the
resulting matrix are continuous -/
@[continuity]
theorem continuous_matrix [TopologicalSpace α] {f : α → Matrix m n R} (h : ∀ i j, Continuous fun a => f a i j) :
    Continuous f :=
  continuous_pi fun _ => continuous_pi fun j => h _ _

theorem Continuous.matrix_elem {A : X → Matrix m n R} (hA : Continuous A) (i : m) (j : n) :
    Continuous fun x => A x i j :=
  (continuous_apply_apply i j).comp hA

@[continuity]
theorem Continuous.matrix_map [TopologicalSpace S] {A : X → Matrix m n S} {f : S → R} (hA : Continuous A)
    (hf : Continuous f) : Continuous fun x => (A x).map f :=
  continuous_matrix fun i j => hf.comp <| hA.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_transpose {A : X → Matrix m n R} (hA : Continuous A) : Continuous fun x => (A x)ᵀ :=
  continuous_matrix fun i j => hA.matrix_elem j i

/-! TODO: add a `has_continuous_star` typeclass so we can write
```
lemma continuous.matrix.conj_transpose [has_star R] {A : X → matrix m n R} (hA : continuous A) :
  continuous (λ x, (A x)ᴴ) :=
hA.matrix_transpose.matrix_map continuous_star
```
-/


@[continuity]
theorem Continuous.matrix_col {A : X → n → R} (hA : Continuous A) : Continuous fun x => colₓ (A x) :=
  continuous_matrix fun i j => (continuous_apply _).comp hA

@[continuity]
theorem Continuous.matrix_row {A : X → n → R} (hA : Continuous A) : Continuous fun x => rowₓ (A x) :=
  continuous_matrix fun i j => (continuous_apply _).comp hA

@[continuity]
theorem Continuous.matrix_diagonal [Zero R] [DecidableEq n] {A : X → n → R} (hA : Continuous A) :
    Continuous fun x => diagonalₓ (A x) :=
  continuous_matrix fun i j => ((continuous_apply i).comp hA).if_const _ continuous_zero

@[continuity]
theorem Continuous.matrix_dot_product [Fintype n] [Mul R] [AddCommMonoidₓ R] [HasContinuousAdd R] [HasContinuousMul R]
    {A : X → n → R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => dotProduct (A x) (B x) :=
  (continuous_finset_sum _) fun i _ => ((continuous_apply i).comp hA).mul ((continuous_apply i).comp hB)

/-- For square matrices the usual `continuous_mul` can be used. -/
@[continuity]
theorem Continuous.matrix_mul [Fintype n] [Mul R] [AddCommMonoidₓ R] [HasContinuousAdd R] [HasContinuousMul R]
    {A : X → Matrix m n R} {B : X → Matrix n p R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).mul (B x) :=
  continuous_matrix fun i j => (continuous_finset_sum _) fun k _ => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

instance [Fintype n] [Mul R] [AddCommMonoidₓ R] [HasContinuousAdd R] [HasContinuousMul R] :
    HasContinuousMul (Matrix n n R) :=
  ⟨continuous_fst.matrix_mul continuous_snd⟩

instance [Fintype n] [NonUnitalNonAssocSemiringₓ R] [TopologicalSemiring R] : TopologicalSemiring (Matrix n n R) :=
  { Pi.has_continuous_add with }

instance [Fintype n] [NonUnitalNonAssocRing R] [TopologicalRing R] : TopologicalRing (Matrix n n R) :=
  { Pi.has_continuous_neg, Pi.has_continuous_add with }

@[continuity]
theorem Continuous.matrix_vec_mul_vec [Mul R] [HasContinuousMul R] {A : X → m → R} {B : X → n → R} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => vecMulVecₓ (A x) (B x) :=
  continuous_matrix fun i j => ((continuous_apply _).comp hA).mul ((continuous_apply _).comp hB)

@[continuity]
theorem Continuous.matrix_mul_vec [NonUnitalNonAssocSemiringₓ R] [HasContinuousAdd R] [HasContinuousMul R] [Fintype n]
    {A : X → Matrix m n R} {B : X → n → R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).mulVec (B x) :=
  continuous_pi fun i => ((continuous_apply i).comp hA).matrix_dot_product hB

@[continuity]
theorem Continuous.matrix_vec_mul [NonUnitalNonAssocSemiringₓ R] [HasContinuousAdd R] [HasContinuousMul R] [Fintype m]
    {A : X → m → R} {B : X → Matrix m n R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => vecMulₓ (A x) (B x) :=
  continuous_pi fun i => hA.matrix_dot_product <| continuous_pi fun j => hB.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_minor {A : X → Matrix l n R} (hA : Continuous A) (e₁ : m → l) (e₂ : p → n) :
    Continuous fun x => (A x).minor e₁ e₂ :=
  continuous_matrix fun i j => hA.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_reindex {A : X → Matrix l n R} (hA : Continuous A) (e₁ : l ≃ m) (e₂ : n ≃ p) :
    Continuous fun x => reindex e₁ e₂ (A x) :=
  hA.matrix_minor _ _

@[continuity]
theorem Continuous.matrix_diag {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => Matrix.diag (A x) :=
  continuous_pi fun _ => hA.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_trace [Fintype n] [Semiringₓ S] [AddCommMonoidₓ R] [HasContinuousAdd R] [Module S R]
    {A : X → Matrix n n R} (hA : Continuous A) : Continuous fun x => trace n S R (A x) :=
  (continuous_finset_sum _) fun i hi => hA.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_det [Fintype n] [DecidableEq n] [CommRingₓ R] [TopologicalRing R] {A : X → Matrix n n R}
    (hA : Continuous A) : Continuous fun x => (A x).det := by
  simp_rw [Matrix.det_apply]
  refine' continuous_finset_sum _ fun l _ => Continuous.const_smul _ _
  refine' continuous_finset_prod _ fun l _ => hA.matrix_elem _ _

@[continuity]
theorem Continuous.matrix_update_column [DecidableEq n] (i : n) {A : X → Matrix m n R} {B : X → m → R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => (A x).updateColumn i (B x) :=
  continuous_matrix fun j k =>
    (continuous_apply k).comp <| ((continuous_apply _).comp hA).update i ((continuous_apply _).comp hB)

@[continuity]
theorem Continuous.matrix_update_row [DecidableEq m] (i : m) {A : X → Matrix m n R} {B : X → n → R} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => (A x).updateRow i (B x) :=
  hA.update i hB

@[continuity]
theorem Continuous.matrix_cramer [Fintype n] [DecidableEq n] [CommRingₓ R] [TopologicalRing R] {A : X → Matrix n n R}
    {B : X → n → R} (hA : Continuous A) (hB : Continuous B) : Continuous fun x => (A x).cramer (B x) :=
  continuous_pi fun i => (hA.matrix_update_column _ hB).matrix_det

@[continuity]
theorem Continuous.matrix_adjugate [Fintype n] [DecidableEq n] [CommRingₓ R] [TopologicalRing R] {A : X → Matrix n n R}
    (hA : Continuous A) : Continuous fun x => (A x).adjugate :=
  continuous_matrix fun j k => (hA.matrix_transpose.matrix_update_column k continuous_const).matrix_det

/-- When `ring.inverse` is continuous at the determinant (such as in a `normed_ring`, or a
`topological_field`), so is `matrix.has_inv`. -/
theorem continuous_at_matrix_inv [Fintype n] [DecidableEq n] [CommRingₓ R] [TopologicalRing R] (A : Matrix n n R)
    (h : ContinuousAt Ring.inverse A.det) : ContinuousAt Inv.inv A :=
  (h.comp continuous_id.matrix_det.ContinuousAt).smul continuous_id.matrix_adjugate.ContinuousAt

-- lemmas about functions in `data/matrix/block.lean`
section BlockMatrices

@[continuity]
theorem Continuous.matrix_from_blocks {A : X → Matrix n l R} {B : X → Matrix n m R} {C : X → Matrix p l R}
    {D : X → Matrix p m R} (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x) :=
  continuous_matrix fun i j => by
    cases i <;> cases j <;> refine' Continuous.matrix_elem _ i j <;> assumption

@[continuity]
theorem Continuous.matrix_block_diagonal [Zero R] [DecidableEq p] {A : X → p → Matrix m n R} (hA : Continuous A) :
    Continuous fun x => blockDiagonalₓ (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ =>
    (((continuous_apply i₂).comp hA).matrix_elem i₁ j₁).if_const _ continuous_zero

@[continuity]
theorem Continuous.matrix_block_diagonal' [Zero R] [DecidableEq l] {A : X → ∀ i, Matrix (m' i) (n' i) R}
    (hA : Continuous A) : Continuous fun x => blockDiagonal'ₓ (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    dsimp only [block_diagonal']
    split_ifs
    · subst h
      exact ((continuous_apply i₁).comp hA).matrix_elem i₂ j₂
      
    · exact continuous_const
      

end BlockMatrices

