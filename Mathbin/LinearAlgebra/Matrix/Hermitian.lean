/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp

! This file was ported from Lean 3 source module linear_algebra.matrix.hermitian
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.PiL2

/-! # Hermitian matrices

This file defines hermitian matrices and some basic results about them.

## Main definition

 * `matrix.is_hermitian` : a matrix `A : matrix n n α` is hermitian if `Aᴴ = A`.

## Tags

self-adjoint matrix, hermitian matrix

-/


namespace Matrix

variable {α β : Type _} {m n : Type _} {A : Matrix n n α}

open Matrix

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner α (PiLp 2 fun _ : n => α) _ x y

section NonUnitalSemiring

variable [NonUnitalSemiring α] [StarRing α] [NonUnitalSemiring β] [StarRing β]

/-- A matrix is hermitian if it is equal to its conjugate transpose. On the reals, this definition
captures symmetric matrices. -/
def IsHermitian (A : Matrix n n α) : Prop :=
  Aᴴ = A
#align matrix.is_hermitian Matrix.IsHermitian

theorem IsHermitian.eq {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ = A :=
  h
#align matrix.is_hermitian.eq Matrix.IsHermitian.eq

@[ext]
theorem IsHermitian.ext {A : Matrix n n α} : (∀ i j, star (A j i) = A i j) → A.IsHermitian := by
  intro h
  ext (i j)
  exact h i j
#align matrix.is_hermitian.ext Matrix.IsHermitian.ext

theorem IsHermitian.apply {A : Matrix n n α} (h : A.IsHermitian) (i j : n) : star (A j i) = A i j :=
  by 
  unfold is_hermitian at h
  rw [← h, conj_transpose_apply, star_star, h]
#align matrix.is_hermitian.apply Matrix.IsHermitian.apply

theorem IsHermitian.ext_iff {A : Matrix n n α} : A.IsHermitian ↔ ∀ i j, star (A j i) = A i j :=
  ⟨IsHermitian.apply, IsHermitian.ext⟩
#align matrix.is_hermitian.ext_iff Matrix.IsHermitian.ext_iff

theorem is_hermitian_mul_conj_transpose_self [Fintype n] (A : Matrix n n α) :
    (A ⬝ Aᴴ).IsHermitian := by rw [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose]
#align matrix.is_hermitian_mul_conj_transpose_self Matrix.is_hermitian_mul_conj_transpose_self

theorem is_hermitian_transpose_mul_self [Fintype n] (A : Matrix n n α) : (Aᴴ ⬝ A).IsHermitian := by
  rw [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose]
#align matrix.is_hermitian_transpose_mul_self Matrix.is_hermitian_transpose_mul_self

theorem is_hermitian_conj_transpose_mul_mul [Fintype m] {A : Matrix m m α} (B : Matrix m n α)
    (hA : A.IsHermitian) : (Bᴴ ⬝ A ⬝ B).IsHermitian := by
  simp only [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose, hA.eq,
    Matrix.mul_assoc]
#align matrix.is_hermitian_conj_transpose_mul_mul Matrix.is_hermitian_conj_transpose_mul_mul

theorem is_hermitian_mul_mul_conj_transpose [Fintype m] {A : Matrix m m α} (B : Matrix n m α)
    (hA : A.IsHermitian) : (B ⬝ A ⬝ Bᴴ).IsHermitian := by
  simp only [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose, hA.eq,
    Matrix.mul_assoc]
#align matrix.is_hermitian_mul_mul_conj_transpose Matrix.is_hermitian_mul_mul_conj_transpose

theorem is_hermitian_add_transpose_self (A : Matrix n n α) : (A + Aᴴ).IsHermitian := by
  simp [is_hermitian, add_comm]
#align matrix.is_hermitian_add_transpose_self Matrix.is_hermitian_add_transpose_self

theorem is_hermitian_transpose_add_self (A : Matrix n n α) : (Aᴴ + A).IsHermitian := by
  simp [is_hermitian, add_comm]
#align matrix.is_hermitian_transpose_add_self Matrix.is_hermitian_transpose_add_self

@[simp]
theorem is_hermitian_zero : (0 : Matrix n n α).IsHermitian :=
  conj_transpose_zero
#align matrix.is_hermitian_zero Matrix.is_hermitian_zero

@[simp]
theorem IsHermitian.map {A : Matrix n n α} (h : A.IsHermitian) (f : α → β)
    (hf : Function.Semiconj f star star) : (A.map f).IsHermitian :=
  (conj_transpose_map f hf).symm.trans <| h.Eq.symm ▸ rfl
#align matrix.is_hermitian.map Matrix.IsHermitian.map

theorem IsHermitian.transpose {A : Matrix n n α} (h : A.IsHermitian) : Aᵀ.IsHermitian := by
  rw [is_hermitian, conj_transpose, transpose_map]
  congr
  exact h
#align matrix.is_hermitian.transpose Matrix.IsHermitian.transpose

@[simp]
theorem is_hermitian_transpose_iff (A : Matrix n n α) : Aᵀ.IsHermitian ↔ A.IsHermitian :=
  ⟨by 
    intro h
    rw [← transpose_transpose A]
    exact is_hermitian.transpose h, IsHermitian.transpose⟩
#align matrix.is_hermitian_transpose_iff Matrix.is_hermitian_transpose_iff

theorem IsHermitian.conj_transpose {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ.IsHermitian :=
  (h.transpose.map _) fun _ => rfl
#align matrix.is_hermitian.conj_transpose Matrix.IsHermitian.conj_transpose

@[simp]
theorem is_hermitian_conj_transpose_iff (A : Matrix n n α) : Aᴴ.IsHermitian ↔ A.IsHermitian :=
  ⟨by 
    intro h
    rw [← conj_transpose_conj_transpose A]
    exact is_hermitian.conj_transpose h, IsHermitian.conj_transpose⟩
#align matrix.is_hermitian_conj_transpose_iff Matrix.is_hermitian_conj_transpose_iff

@[simp]
theorem IsHermitian.add {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A + B).IsHermitian :=
  (conj_transpose_add _ _).trans (hA.symm ▸ hB.symm ▸ rfl)
#align matrix.is_hermitian.add Matrix.IsHermitian.add

@[simp]
theorem IsHermitian.submatrix {A : Matrix n n α} (h : A.IsHermitian) (f : m → n) :
    (A.submatrix f f).IsHermitian :=
  (conj_transpose_submatrix _ _ _).trans (h.symm ▸ rfl)
#align matrix.is_hermitian.submatrix Matrix.IsHermitian.submatrix

@[simp]
theorem is_hermitian_submatrix_equiv {A : Matrix n n α} (e : m ≃ n) :
    (A.submatrix e e).IsHermitian ↔ A.IsHermitian :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩
#align matrix.is_hermitian_submatrix_equiv Matrix.is_hermitian_submatrix_equiv

/-- The real diagonal matrix `diagonal v` is hermitian. -/
@[simp]
theorem is_hermitian_diagonal [DecidableEq n] (v : n → ℝ) : (diagonal v).IsHermitian :=
  diagonal_conj_transpose _
#align matrix.is_hermitian_diagonal Matrix.is_hermitian_diagonal

/-- A block matrix `A.from_blocks B C D` is hermitian,
    if `A` and `D` are hermitian and `Bᴴ = C`. -/
theorem IsHermitian.from_blocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} (hA : A.IsHermitian) (hBC : Bᴴ = C) (hD : D.IsHermitian) :
    (A.fromBlocks B C D).IsHermitian := by
  have hCB : Cᴴ = B := by 
    rw [← hBC]
    simp
  unfold Matrix.IsHermitian
  rw [from_blocks_conj_transpose]
  congr <;> assumption
#align matrix.is_hermitian.from_blocks Matrix.IsHermitian.from_blocks

/-- This is the `iff` version of `matrix.is_hermitian.from_blocks`. -/
theorem is_hermitian_from_blocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} :
    (A.fromBlocks B C D).IsHermitian ↔ A.IsHermitian ∧ Bᴴ = C ∧ Cᴴ = B ∧ D.IsHermitian :=
  ⟨fun h =>
    ⟨congr_arg toBlocks₁₁ h, congr_arg toBlocks₂₁ h, congr_arg toBlocks₁₂ h,
      congr_arg toBlocks₂₂ h⟩,
    fun ⟨hA, hBC, hCB, hD⟩ => IsHermitian.from_blocks hA hBC hD⟩
#align matrix.is_hermitian_from_blocks_iff Matrix.is_hermitian_from_blocks_iff

end NonUnitalSemiring

section Semiring

variable [Semiring α] [StarRing α] [Semiring β] [StarRing β]

@[simp]
theorem is_hermitian_one [DecidableEq n] : (1 : Matrix n n α).IsHermitian :=
  conj_transpose_one
#align matrix.is_hermitian_one Matrix.is_hermitian_one

end Semiring

section Ring

variable [Ring α] [StarRing α] [Ring β] [StarRing β]

@[simp]
theorem IsHermitian.neg {A : Matrix n n α} (h : A.IsHermitian) : (-A).IsHermitian :=
  (conj_transpose_neg _).trans (congr_arg _ h)
#align matrix.is_hermitian.neg Matrix.IsHermitian.neg

@[simp]
theorem IsHermitian.sub {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A - B).IsHermitian :=
  (conj_transpose_sub _ _).trans (hA.symm ▸ hB.symm ▸ rfl)
#align matrix.is_hermitian.sub Matrix.IsHermitian.sub

end Ring

section CommRing

variable [CommRing α] [StarRing α]

theorem IsHermitian.inv [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A⁻¹.IsHermitian := by simp [is_hermitian, conj_transpose_nonsing_inv, hA.eq]
#align matrix.is_hermitian.inv Matrix.IsHermitian.inv

@[simp]
theorem is_hermitian_inv [Fintype m] [DecidableEq m] (A : Matrix m m α) [Invertible A] :
    A⁻¹.IsHermitian ↔ A.IsHermitian :=
  ⟨fun h => by 
    rw [← inv_inv_of_invertible A]
    exact is_hermitian.inv h, IsHermitian.inv⟩
#align matrix.is_hermitian_inv Matrix.is_hermitian_inv

theorem IsHermitian.adjugate [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A.adjugate.IsHermitian := by simp [is_hermitian, adjugate_conj_transpose, hA.eq]
#align matrix.is_hermitian.adjugate Matrix.IsHermitian.adjugate

end CommRing

section IsROrC

open IsROrC

variable [IsROrC α] [IsROrC β]

/-- The diagonal elements of a complex hermitian matrix are real. -/
theorem IsHermitian.coe_re_apply_self {A : Matrix n n α} (h : A.IsHermitian) (i : n) :
    (re (A i i) : α) = A i i := by rw [← eq_conj_iff_re, ← star_def, ← conj_transpose_apply, h.eq]
#align matrix.is_hermitian.coe_re_apply_self Matrix.IsHermitian.coe_re_apply_self

/-- The diagonal elements of a complex hermitian matrix are real. -/
theorem IsHermitian.coe_re_diag {A : Matrix n n α} (h : A.IsHermitian) :
    (fun i => (re (A.diag i) : α)) = A.diag :=
  funext h.coe_re_apply_self
#align matrix.is_hermitian.coe_re_diag Matrix.IsHermitian.coe_re_diag

/-- A matrix is hermitian iff the corresponding linear map is self adjoint. -/
theorem is_hermitian_iff_is_symmetric [Fintype n] [DecidableEq n] {A : Matrix n n α} :
    IsHermitian A ↔
      LinearMap.IsSymmetric
        ((PiLp.linearEquiv 2 α fun _ : n => α).symm.conj A.toLin' : Module.EndCat α (PiLp 2 _)) :=
  by 
  rw [LinearMap.IsSymmetric, (PiLp.equiv 2 fun _ : n => α).symm.Surjective.Forall₂]
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    PiLp.linear_equiv_apply, PiLp.linear_equiv_symm_apply, LinearEquiv.symm_symm]
  simp_rw [EuclideanSpace.inner_eq_star_dot_product, Equiv.apply_symm_apply, to_lin'_apply,
    star_mul_vec, dot_product_mul_vec]
  constructor
  · rintro (h : Aᴴ = A) x y
    rw [h]
  · intro h
    ext (i j)
    simpa only [(Pi.single_star i 1).symm, ← star_mul_vec, mul_one, dot_product_single,
      single_vec_mul, star_one, one_mul] using
      h (@Pi.single _ _ _ (fun i => AddZeroClass.toHasZero α) i 1)
        (@Pi.single _ _ _ (fun i => AddZeroClass.toHasZero α) j 1)
#align matrix.is_hermitian_iff_is_symmetric Matrix.is_hermitian_iff_is_symmetric

end IsROrC

end Matrix

