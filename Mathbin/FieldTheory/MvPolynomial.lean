/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module field_theory.mv_polynomial
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.MvPolynomial.CommRing
import Mathbin.RingTheory.MvPolynomial.Basic

/-!
# Multivariate polynomials over fields

This file contains basic facts about multivariate polynomials over fields, for example that the
dimension of the space of multivariate polynomials over a field is equal to the cardinality of
finitely supported functions from the indexing set to `ℕ`.
-/


noncomputable section

open Classical

open Set LinearMap Submodule

open BigOperators

namespace MvPolynomial

universe u v

variable {σ : Type u} {K : Type v}

variable (σ K) [Field K]

theorem quotient_mk_comp_c_injective (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) :
    Function.Injective ((Ideal.Quotient.mk I).comp MvPolynomial.c) :=
  by
  refine' (injective_iff_map_eq_zero _).2 fun x hx => _
  rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hx
  refine' by_contradiction fun hx0 => absurd (I.eq_top_iff_one.2 _) hI
  have := I.mul_mem_left (MvPolynomial.c x⁻¹) hx
  rwa [← mv_polynomial.C.map_mul, inv_mul_cancel hx0, MvPolynomial.c_1] at this
#align mv_polynomial.quotient_mk_comp_C_injective MvPolynomial.quotient_mk_comp_c_injective

end MvPolynomial

namespace MvPolynomial

universe u

variable {σ : Type u} {K : Type u} [Field K]

open Classical

theorem dim_mvPolynomial : Module.rank K (MvPolynomial σ K) = Cardinal.mk (σ →₀ ℕ) := by
  rw [← Cardinal.lift_inj, ← (basis_monomials σ K).mk_eq_dim]
#align mv_polynomial.dim_mv_polynomial MvPolynomial.dim_mvPolynomial

end MvPolynomial

