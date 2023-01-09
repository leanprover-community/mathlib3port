/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark

! This file was ported from Lean 3 source module linear_algebra.matrix.charpoly.finite_field
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathbin.FieldTheory.Finite.Basic
import Mathbin.Data.Matrix.CharP

/-!
# Results on characteristic polynomials and traces over finite fields.
-/


noncomputable section

open Polynomial Matrix

open Polynomial

variable {n : Type _} [DecidableEq n] [Fintype n]

@[simp]
theorem FiniteField.Matrix.charpoly_pow_card {K : Type _} [Field K] [Fintype K] (M : Matrix n n K) :
    (M ^ Fintype.card K).charpoly = M.charpoly :=
  by
  cases (isEmpty_or_nonempty n).symm
  · cases' CharP.exists K with p hp
    letI := hp
    rcases FiniteField.card K p with ⟨⟨k, kpos⟩, ⟨hp, hk⟩⟩
    haveI : Fact p.prime := ⟨hp⟩
    dsimp at hk
    rw [hk] at *
    apply (frobenius_inj K[X] p).iterate k
    repeat' rw [iterate_frobenius]; rw [← hk]
    rw [← FiniteField.expand_card]
    unfold charpoly
    rw [AlgHom.map_det, ← coe_det_monoid_hom, ← (det_monoid_hom : Matrix n n K[X] →* K[X]).map_pow]
    apply congr_arg det
    refine' mat_poly_equiv.injective _
    rw [AlgEquiv.map_pow, mat_poly_equiv_charmatrix, hk, sub_pow_char_pow_of_commute, ← C_pow]
    · exact (id (mat_poly_equiv_eq_X_pow_sub_C (p ^ k) M) : _)
    · exact (C M).commute_X
  · exact congr_arg _ (Subsingleton.elim _ _)
#align finite_field.matrix.charpoly_pow_card FiniteField.Matrix.charpoly_pow_card

@[simp]
theorem Zmod.charpoly_pow_card {p : ℕ} [Fact p.Prime] (M : Matrix n n (Zmod p)) :
    (M ^ p).charpoly = M.charpoly :=
  by
  have h := FiniteField.Matrix.charpoly_pow_card M
  rwa [Zmod.card] at h
#align zmod.charpoly_pow_card Zmod.charpoly_pow_card

theorem FiniteField.trace_pow_card {K : Type _} [Field K] [Fintype K] (M : Matrix n n K) :
    trace (M ^ Fintype.card K) = trace M ^ Fintype.card K :=
  by
  cases isEmpty_or_nonempty n
  · simp [zero_pow Fintype.card_pos, Matrix.trace]
  rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
    FiniteField.Matrix.charpoly_pow_card, FiniteField.pow_card]
#align finite_field.trace_pow_card FiniteField.trace_pow_card

theorem Zmod.trace_pow_card {p : ℕ} [Fact p.Prime] (M : Matrix n n (Zmod p)) :
    trace (M ^ p) = trace M ^ p :=
  by
  have h := FiniteField.trace_pow_card M
  rwa [Zmod.card] at h
#align zmod.trace_pow_card Zmod.trace_pow_card

