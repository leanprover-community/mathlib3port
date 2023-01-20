/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin

! This file was ported from Lean 3 source module ring_theory.mv_polynomial.symmetric
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.MvPolynomial.Rename
import Mathbin.Data.MvPolynomial.CommRing
import Mathbin.Algebra.Algebra.Subalgebra.Basic

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric `mv_polynomial`s and elementary symmetric `mv_polynomial`s.
We also prove some basic facts about them.

## Main declarations

* `mv_polynomial.is_symmetric`

* `mv_polynomial.symmetric_subalgebra`

* `mv_polynomial.esymm`

## Notation

+ `esymm σ R n`, is the `n`th elementary symmetric polynomial in `mv_polynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R S : Type*` `[comm_semiring R]` `[comm_semiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : mv_polynomial σ R`

-/


open Equiv (Perm)

open BigOperators

noncomputable section

namespace Multiset

variable {R : Type _} [CommSemiring R]

/-- The `n`th elementary symmetric function evaluated at the elements of `s` -/
def esymm (s : Multiset R) (n : ℕ) : R :=
  ((s.powersetLen n).map Multiset.prod).Sum
#align multiset.esymm Multiset.esymm

theorem Finset.esymm_map_val {σ} (f : σ → R) (s : Finset σ) (n : ℕ) :
    (s.val.map f).esymm n = (s.powersetLen n).Sum fun t => t.Prod f := by
  simpa only [esymm, powerset_len_map, ← Finset.map_val_val_powersetLen, map_map]
#align finset.esymm_map_val Finset.esymm_map_val

end Multiset

namespace MvPolynomial

variable {σ : Type _} {R : Type _}

variable {τ : Type _} {S : Type _}

/-- A `mv_polynomial φ` is symmetric if it is invariant under
permutations of its variables by the  `rename` operation -/
def IsSymmetric [CommSemiring R] (φ : MvPolynomial σ R) : Prop :=
  ∀ e : Perm σ, rename e φ = φ
#align mv_polynomial.is_symmetric MvPolynomial.IsSymmetric

variable (σ R)

/-- The subalgebra of symmetric `mv_polynomial`s. -/
def symmetricSubalgebra [CommSemiring R] : Subalgebra R (MvPolynomial σ R)
    where
  carrier := setOf IsSymmetric
  algebra_map_mem' r e := rename_C e r
  mul_mem' a b ha hb e := by rw [AlgHom.map_mul, ha, hb]
  add_mem' a b ha hb e := by rw [AlgHom.map_add, ha, hb]
#align mv_polynomial.symmetric_subalgebra MvPolynomial.symmetricSubalgebra

variable {σ R}

@[simp]
theorem mem_symmetric_subalgebra [CommSemiring R] (p : MvPolynomial σ R) :
    p ∈ symmetricSubalgebra σ R ↔ p.IsSymmetric :=
  Iff.rfl
#align mv_polynomial.mem_symmetric_subalgebra MvPolynomial.mem_symmetric_subalgebra

namespace IsSymmetric

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {φ ψ : MvPolynomial σ R}

@[simp]
theorem C (r : R) : IsSymmetric (c r : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).algebra_map_mem r
#align mv_polynomial.is_symmetric.C MvPolynomial.IsSymmetric.C

@[simp]
theorem zero : IsSymmetric (0 : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).zero_mem
#align mv_polynomial.is_symmetric.zero MvPolynomial.IsSymmetric.zero

@[simp]
theorem one : IsSymmetric (1 : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).one_mem
#align mv_polynomial.is_symmetric.one MvPolynomial.IsSymmetric.one

theorem add (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ + ψ) :=
  (symmetricSubalgebra σ R).add_mem hφ hψ
#align mv_polynomial.is_symmetric.add MvPolynomial.IsSymmetric.add

theorem mul (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ * ψ) :=
  (symmetricSubalgebra σ R).mul_mem hφ hψ
#align mv_polynomial.is_symmetric.mul MvPolynomial.IsSymmetric.mul

theorem smul (r : R) (hφ : IsSymmetric φ) : IsSymmetric (r • φ) :=
  (symmetricSubalgebra σ R).smul_mem hφ r
#align mv_polynomial.is_symmetric.smul MvPolynomial.IsSymmetric.smul

@[simp]
theorem map (hφ : IsSymmetric φ) (f : R →+* S) : IsSymmetric (map f φ) := fun e => by
  rw [← map_rename, hφ]
#align mv_polynomial.is_symmetric.map MvPolynomial.IsSymmetric.map

end CommSemiring

section CommRing

variable [CommRing R] {φ ψ : MvPolynomial σ R}

theorem neg (hφ : IsSymmetric φ) : IsSymmetric (-φ) :=
  (symmetricSubalgebra σ R).neg_mem hφ
#align mv_polynomial.is_symmetric.neg MvPolynomial.IsSymmetric.neg

theorem sub (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ - ψ) :=
  (symmetricSubalgebra σ R).sub_mem hφ hψ
#align mv_polynomial.is_symmetric.sub MvPolynomial.IsSymmetric.sub

end CommRing

end IsSymmetric

section ElementarySymmetric

open Finset

variable (σ R) [CommSemiring R] [CommSemiring S] [Fintype σ] [Fintype τ]

/-- The `n`th elementary symmetric `mv_polynomial σ R`. -/
def esymm (n : ℕ) : MvPolynomial σ R :=
  ∑ t in powersetLen n univ, ∏ i in t, x i
#align mv_polynomial.esymm MvPolynomial.esymm

/-- The `n`th elementary symmetric `mv_polynomial σ R` is obtained by evaluating the
`n`th elementary symmetric at the `multiset` of the monomials -/
theorem esymm_eq_multiset_esymm : esymm σ R = (Finset.univ.val.map x).esymm :=
  funext fun n => (Finset.univ.esymm_map_val x n).symm
#align mv_polynomial.esymm_eq_multiset_esymm MvPolynomial.esymm_eq_multiset_esymm

theorem aeval_esymm_eq_multiset_esymm [Algebra R S] (f : σ → S) (n : ℕ) :
    aeval f (esymm σ R n) = (Finset.univ.val.map f).esymm n := by
  simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, esymm_map_val]
#align mv_polynomial.aeval_esymm_eq_multiset_esymm MvPolynomial.aeval_esymm_eq_multiset_esymm

/-- We can define `esymm σ R n` by summing over a subtype instead of over `powerset_len`. -/
theorem esymm_eq_sum_subtype (n : ℕ) :
    esymm σ R n = ∑ t : { s : Finset σ // s.card = n }, ∏ i in (t : Finset σ), x i :=
  sum_subtype _ (fun _ => mem_powerset_len_univ_iff) _
#align mv_polynomial.esymm_eq_sum_subtype MvPolynomial.esymm_eq_sum_subtype

/-- We can define `esymm σ R n` as a sum over explicit monomials -/
theorem esymm_eq_sum_monomial (n : ℕ) :
    esymm σ R n = ∑ t in powersetLen n univ, monomial (∑ i in t, Finsupp.single i 1) 1 :=
  by
  simp_rw [monomial_sum_one]
  rfl
#align mv_polynomial.esymm_eq_sum_monomial MvPolynomial.esymm_eq_sum_monomial

@[simp]
theorem esymm_zero : esymm σ R 0 = 1 := by
  simp only [esymm, powerset_len_zero, sum_singleton, prod_empty]
#align mv_polynomial.esymm_zero MvPolynomial.esymm_zero

theorem map_esymm (n : ℕ) (f : R →+* S) : map f (esymm σ R n) = esymm σ S n := by
  simp_rw [esymm, map_sum, map_prod, map_X]
#align mv_polynomial.map_esymm MvPolynomial.map_esymm

theorem rename_esymm (n : ℕ) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n :=
  calc
    rename e (esymm σ R n) = ∑ x in powersetLen n univ, ∏ i in x, x (e i) := by
      simp_rw [esymm, map_sum, map_prod, rename_X]
    _ = ∑ t in powersetLen n (univ.map e.toEmbedding), ∏ i in t, x i := by
      simp [Finset.powersetLen_map, -Finset.map_univ_equiv]
    _ = ∑ t in powersetLen n univ, ∏ i in t, x i := by rw [Finset.map_univ_equiv]
    
#align mv_polynomial.rename_esymm MvPolynomial.rename_esymm

theorem esymm_is_symmetric (n : ℕ) : IsSymmetric (esymm σ R n) :=
  by
  intro
  rw [rename_esymm]
#align mv_polynomial.esymm_is_symmetric MvPolynomial.esymm_is_symmetric

theorem support_esymm'' (n : ℕ) [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetLen n (univ : Finset σ)).bUnion fun t =>
        (Finsupp.single (∑ i : σ in t, Finsupp.single i 1) (1 : R)).support :=
  by
  rw [esymm_eq_sum_monomial]
  simp only [← single_eq_monomial]
  convert Finsupp.support_sum_eq_bUnion (powerset_len n (univ : Finset σ)) _
  intro s t hst
  rw [Finset.disjoint_left]
  simp only [Finsupp.support_single_ne_zero _ one_ne_zero, mem_singleton]
  rintro a h rfl
  have := congr_arg Finsupp.support h
  rw [Finsupp.support_sum_eq_bUnion, Finsupp.support_sum_eq_bUnion] at this
  · simp only [Finsupp.support_single_ne_zero _ one_ne_zero, bUnion_singleton_eq_self] at this
    exact absurd this hst.symm
  all_goals intro x y; simp [Finsupp.support_single_disjoint]
#align mv_polynomial.support_esymm'' MvPolynomial.support_esymm''

theorem support_esymm' (n : ℕ) [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetLen n (univ : Finset σ)).bUnion fun t => {∑ i : σ in t, Finsupp.single i 1} :=
  by
  rw [support_esymm'']
  congr
  funext
  exact Finsupp.support_single_ne_zero _ one_ne_zero
#align mv_polynomial.support_esymm' MvPolynomial.support_esymm'

theorem support_esymm (n : ℕ) [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetLen n (univ : Finset σ)).image fun t => ∑ i : σ in t, Finsupp.single i 1 :=
  by
  rw [support_esymm']
  exact bUnion_singleton
#align mv_polynomial.support_esymm MvPolynomial.support_esymm

theorem degrees_esymm [Nontrivial R] (n : ℕ) (hpos : 0 < n) (hn : n ≤ Fintype.card σ) :
    (esymm σ R n).degrees = (univ : Finset σ).val := by
  classical
    have :
      (Finsupp.toMultiset ∘ fun t : Finset σ => ∑ i : σ in t, Finsupp.single i 1) = Finset.val :=
      by
      funext
      simp [Finsupp.to_multiset_sum_single]
    rw [degrees, support_esymm, sup_finset_image, this, ← comp_sup_eq_sup_comp]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      simpa using powerset_len_sup _ _ (Nat.lt_of_succ_le hn)
    · intros
      simp only [union_val, sup_eq_union]
      congr
    · rfl
#align mv_polynomial.degrees_esymm MvPolynomial.degrees_esymm

end ElementarySymmetric

end MvPolynomial

