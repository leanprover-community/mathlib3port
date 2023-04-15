/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.matrix.rank
! leanprover-community/mathlib commit 0e2aab2b0d521f060f62a14d2cf2e2c54e8491d6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FreeModule.Finite.Rank
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Rank of matrices

The rank of a matrix `A` is defined to be the rank of range of the linear map corresponding to `A`.
This definition does not depend on the choice of basis, see `matrix.rank_eq_finrank_range_to_lin`.

## Main declarations

* `matrix.rank`: the rank of a matrix

## TODO

* Show that `matrix.rank` is equal to the row-rank, and that `rank Aᵀ = rank A`.

-/


open Matrix

namespace Matrix

open FiniteDimensional

variable {l m n o R : Type _} [m_fin : Fintype m] [Fintype n] [Fintype o]

variable [CommRing R]

/-- The rank of a matrix is the rank of its image. -/
noncomputable def rank (A : Matrix m n R) : ℕ :=
  finrank R A.mulVecLin.range
#align matrix.rank Matrix.rank

@[simp]
theorem rank_one [StrongRankCondition R] [DecidableEq n] :
    rank (1 : Matrix n n R) = Fintype.card n := by
  rw [rank, mul_vec_lin_one, LinearMap.range_id, finrank_top, finrank_pi]
#align matrix.rank_one Matrix.rank_one

@[simp]
theorem rank_zero [Nontrivial R] : rank (0 : Matrix m n R) = 0 := by
  rw [rank, mul_vec_lin_zero, LinearMap.range_zero, finrank_bot]
#align matrix.rank_zero Matrix.rank_zero

theorem rank_le_card_width [StrongRankCondition R] (A : Matrix m n R) : A.rank ≤ Fintype.card n :=
  by
  haveI : Module.Finite R (n → R) := Module.Finite.pi
  haveI : Module.Free R (n → R) := Module.Free.pi _ _
  exact A.mul_vec_lin.finrank_range_le.trans_eq (finrank_pi _)
#align matrix.rank_le_card_width Matrix.rank_le_card_width

theorem rank_le_width [StrongRankCondition R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    A.rank ≤ n :=
  A.rank_le_card_width.trans <| (Fintype.card_fin n).le
#align matrix.rank_le_width Matrix.rank_le_width

theorem rank_mul_le_left [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A ⬝ B).rank ≤ A.rank := by
  rw [rank, rank, mul_vec_lin_mul]
  exact Cardinal.toNat_le_of_le_of_lt_aleph0 (rank_lt_aleph_0 _ _) (LinearMap.rank_comp_le_left _ _)
#align matrix.rank_mul_le_left Matrix.rank_mul_le_left

include m_fin

theorem rank_mul_le_right [StrongRankCondition R] (A : Matrix l m R) (B : Matrix m n R) :
    (A ⬝ B).rank ≤ B.rank := by
  rw [rank, rank, mul_vec_lin_mul]
  exact
    finrank_le_finrank_of_rank_le_rank (LinearMap.lift_rank_comp_le_right _ _) (rank_lt_aleph_0 _ _)
#align matrix.rank_mul_le_right Matrix.rank_mul_le_right

omit m_fin

theorem rank_mul_le [StrongRankCondition R] (A : Matrix m n R) (B : Matrix n o R) :
    (A ⬝ B).rank ≤ min A.rank B.rank :=
  le_min (rank_mul_le_left _ _) (rank_mul_le_right _ _)
#align matrix.rank_mul_le Matrix.rank_mul_le

theorem rank_unit [StrongRankCondition R] [DecidableEq n] (A : (Matrix n n R)ˣ) :
    (A : Matrix n n R).rank = Fintype.card n :=
  by
  refine' le_antisymm (rank_le_card_width A) _
  have := rank_mul_le_left (A : Matrix n n R) (↑A⁻¹ : Matrix n n R)
  rwa [← mul_eq_mul, ← Units.val_mul, mul_inv_self, Units.val_one, rank_one] at this
#align matrix.rank_unit Matrix.rank_unit

theorem rank_of_isUnit [StrongRankCondition R] [DecidableEq n] (A : Matrix n n R) (h : IsUnit A) :
    A.rank = Fintype.card n := by
  obtain ⟨A, rfl⟩ := h
  exact rank_unit A
#align matrix.rank_of_is_unit Matrix.rank_of_isUnit

/-- Taking a subset of the rows and permuting the columns reduces the rank. -/
theorem rank_submatrix_le [StrongRankCondition R] [Fintype m] (f : n → m) (e : n ≃ m)
    (A : Matrix m m R) : rank (A.submatrix f e) ≤ rank A :=
  by
  rw [rank, rank, mul_vec_lin_submatrix, LinearMap.range_comp, LinearMap.range_comp,
    show LinearMap.funLeft R R e.symm = LinearEquiv.funCongrLeft R R e.symm from rfl,
    LinearEquiv.range, Submodule.map_top]
  -- TODO: generalize `finite_dimensional.finrank_map_le` and use it here
  exact finrank_le_finrank_of_rank_le_rank (lift_rank_map_le _ _) (rank_lt_aleph_0 _ _)
#align matrix.rank_submatrix_le Matrix.rank_submatrix_le

theorem rank_reindex [Fintype m] (e₁ e₂ : m ≃ n) (A : Matrix m m R) :
    rank (reindex e₁ e₂ A) = rank A := by
  rw [rank, rank, mul_vec_lin_reindex, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]
#align matrix.rank_reindex Matrix.rank_reindex

@[simp]
theorem rank_submatrix [Fintype m] (A : Matrix m m R) (e₁ e₂ : n ≃ m) :
    rank (A.submatrix e₁ e₂) = rank A := by
  simpa only [reindex_apply] using rank_reindex e₁.symm e₂.symm A
#align matrix.rank_submatrix Matrix.rank_submatrix

include m_fin

theorem rank_eq_finrank_range_toLin [DecidableEq n] {M₁ M₂ : Type _} [AddCommGroup M₁]
    [AddCommGroup M₂] [Module R M₁] [Module R M₂] (A : Matrix m n R) (v₁ : Basis m R M₁)
    (v₂ : Basis n R M₂) : A.rank = finrank R (toLin v₂ v₁ A).range :=
  by
  let e₁ := (Pi.basisFun R m).Equiv v₁ (Equiv.refl _)
  let e₂ := (Pi.basisFun R n).Equiv v₂ (Equiv.refl _)
  have range_e₂ : (e₂ : (n → R) →ₗ[R] M₂).range = ⊤ :=
    by
    rw [LinearMap.range_eq_top]
    exact e₂.surjective
  refine' LinearEquiv.finrank_eq (e₁.of_submodules _ _ _)
  rw [← LinearMap.range_comp, ← LinearMap.range_comp_of_range_eq_top (to_lin v₂ v₁ A) range_e₂]
  congr 1
  apply LinearMap.pi_ext'
  rintro i
  apply LinearMap.ext_ring
  have aux₁ := to_lin_self (Pi.basisFun R n) (Pi.basisFun R m) A i
  have aux₂ := Basis.equiv_apply (Pi.basisFun R n) i v₂
  rw [to_lin_eq_to_lin', to_lin'_apply'] at aux₁
  rw [Pi.basisFun_apply, LinearMap.coe_stdBasis] at aux₁ aux₂
  simp only [LinearMap.comp_apply, e₁, e₂, LinearEquiv.coe_coe, Equiv.refl_apply, aux₁, aux₂,
    LinearMap.coe_single, to_lin_self, LinearEquiv.map_sum, LinearEquiv.map_smul, Basis.equiv_apply]
#align matrix.rank_eq_finrank_range_to_lin Matrix.rank_eq_finrank_range_toLin

theorem rank_le_card_height [StrongRankCondition R] (A : Matrix m n R) : A.rank ≤ Fintype.card m :=
  by
  haveI : Module.Finite R (m → R) := Module.Finite.pi
  haveI : Module.Free R (m → R) := Module.Free.pi _ _
  exact (Submodule.finrank_le _).trans (finrank_pi R).le
#align matrix.rank_le_card_height Matrix.rank_le_card_height

omit m_fin

theorem rank_le_height [StrongRankCondition R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    A.rank ≤ m :=
  A.rank_le_card_height.trans <| (Fintype.card_fin m).le
#align matrix.rank_le_height Matrix.rank_le_height

/-- The rank of a matrix is the rank of the space spanned by its columns. -/
theorem rank_eq_finrank_span_cols (A : Matrix m n R) :
    A.rank = finrank R (Submodule.span R (Set.range Aᵀ)) := by rw [rank, Matrix.range_mulVecLin]
#align matrix.rank_eq_finrank_span_cols Matrix.rank_eq_finrank_span_cols

end Matrix

