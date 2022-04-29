/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
import Mathbin.Algebra.Polynomial.BigOperators
import Mathbin.Data.Matrix.CharP
import Mathbin.FieldTheory.Finite.Basic
import Mathbin.GroupTheory.Perm.Cycles
import Mathbin.LinearAlgebra.Matrix.Charpoly.Basic
import Mathbin.LinearAlgebra.Matrix.Trace
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.RingTheory.Polynomial.Basic
import Mathbin.RingTheory.PowerBasis

/-!
# Characteristic polynomials

We give methods for computing coefficients of the characteristic polynomial.

## Main definitions

- `matrix.charpoly_degree_eq_dim` proves that the degree of the characteristic polynomial
  over a nonzero ring is the dimension of the matrix
- `matrix.det_eq_sign_charpoly_coeff` proves that the determinant is the constant term of the
  characteristic polynomial, up to sign.
- `matrix.trace_eq_neg_charpoly_coeff` proves that the trace is the negative of the (d-1)th
  coefficient of the characteristic polynomial, where d is the dimension of the matrix.
  For a nonzero ring, this is the second-highest coefficient.

-/


noncomputable section

universe u v w z

open Polynomial Matrix

open BigOperators Polynomial

variable {R : Type u} [CommRingₓ R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

open Finset

variable {M : Matrix n n R}

theorem charmatrix_apply_nat_degree [Nontrivial R] (i j : n) : (charmatrix M i j).natDegree = ite (i = j) 1 0 := by
  by_cases' i = j <;> simp [h, ← degree_eq_iff_nat_degree_eq_of_pos (Nat.succ_posₓ 0)]

theorem charmatrix_apply_nat_degree_le (i j : n) : (charmatrix M i j).natDegree ≤ ite (i = j) 1 0 := by
  split_ifs <;> simp [h, nat_degree_X_sub_C_le]

namespace Matrix

variable (M)

theorem charpoly_sub_diagonal_degree_lt : (M.charpoly - ∏ i : n, X - c (M i i)).degree < ↑(Fintype.card n - 1) := by
  rw [charpoly, det_apply', ← insert_erase (mem_univ (Equivₓ.refl n)), sum_insert (not_mem_erase (Equivₓ.refl n) univ),
    add_commₓ]
  simp only [charmatrix_apply_eq, one_mulₓ, Equivₓ.Perm.sign_refl, id.def, Int.cast_oneₓ, Units.coe_one, add_sub_cancel,
    Equivₓ.coe_refl]
  rw [← mem_degree_lt]
  apply Submodule.sum_mem (degree_lt R (Fintype.card n - 1))
  intro c hc
  rw [← C_eq_int_cast, C_mul']
  apply Submodule.smul_mem (degree_lt R (Fintype.card n - 1)) ↑↑(Equivₓ.Perm.sign c)
  rw [mem_degree_lt]
  apply lt_of_le_of_ltₓ degree_le_nat_degree _
  rw [WithBot.coe_lt_coe]
  apply lt_of_le_of_ltₓ _ (Equivₓ.Perm.fixed_point_card_lt_of_ne_one (ne_of_mem_erase hc))
  apply le_transₓ (Polynomial.nat_degree_prod_le univ fun i : n => charmatrix M (c i) i) _
  rw [card_eq_sum_ones]
  rw [sum_filter]
  apply sum_le_sum
  intros
  apply charmatrix_apply_nat_degree_le

theorem charpoly_coeff_eq_prod_coeff_of_le {k : ℕ} (h : Fintype.card n - 1 ≤ k) :
    M.charpoly.coeff k = (∏ i : n, X - c (M i i)).coeff k := by
  apply eq_of_sub_eq_zero
  rw [← coeff_sub]
  apply Polynomial.coeff_eq_zero_of_degree_lt
  apply lt_of_lt_of_leₓ (charpoly_sub_diagonal_degree_lt M) _
  rw [WithBot.coe_le_coe]
  apply h

theorem det_of_card_zero (h : Fintype.card n = 0) (M : Matrix n n R) : M.det = 1 := by
  rw [Fintype.card_eq_zero_iff] at h
  suffices M = 1 by
    simp [this]
  ext i
  exact h.elim i

theorem charpoly_degree_eq_dim [Nontrivial R] (M : Matrix n n R) : M.charpoly.degree = Fintype.card n := by
  by_cases' Fintype.card n = 0
  · rw [h]
    unfold charpoly
    rw [det_of_card_zero]
    · simp
      
    · assumption
      
    
  rw [← sub_add_cancel M.charpoly (∏ i : n, X - C (M i i))]
  have h1 : (∏ i : n, X - C (M i i)).degree = Fintype.card n := by
    rw [degree_eq_iff_nat_degree_eq_of_pos]
    swap
    apply Nat.pos_of_ne_zeroₓ h
    rw [nat_degree_prod']
    simp_rw [nat_degree_X_sub_C]
    unfold Fintype.card
    simp
    simp_rw [(monic_X_sub_C _).leadingCoeff]
    simp
  rw [degree_add_eq_right_of_degree_lt]
  exact h1
  rw [h1]
  apply lt_transₓ (charpoly_sub_diagonal_degree_lt M)
  rw [WithBot.coe_lt_coe]
  rw [← Nat.pred_eq_sub_one]
  apply Nat.pred_ltₓ
  apply h

theorem charpoly_nat_degree_eq_dim [Nontrivial R] (M : Matrix n n R) : M.charpoly.natDegree = Fintype.card n :=
  nat_degree_eq_of_degree_eq_some (charpoly_degree_eq_dim M)

theorem charpoly_monic (M : Matrix n n R) : M.charpoly.Monic := by
  nontriviality
  by_cases' Fintype.card n = 0
  · rw [charpoly, det_of_card_zero h]
    apply monic_one
    
  have mon : (∏ i : n, X - C (M i i)).Monic := by
    apply monic_prod_of_monic univ fun i : n => X - C (M i i)
    simp [monic_X_sub_C]
  rw [← sub_add_cancel (∏ i : n, X - C (M i i)) M.charpoly] at mon
  rw [monic] at *
  rw [leading_coeff_add_of_degree_lt] at mon
  rw [← mon]
  rw [charpoly_degree_eq_dim]
  rw [← neg_sub]
  rw [degree_neg]
  apply lt_transₓ (charpoly_sub_diagonal_degree_lt M)
  rw [WithBot.coe_lt_coe]
  rw [← Nat.pred_eq_sub_one]
  apply Nat.pred_ltₓ
  apply h

theorem trace_eq_neg_charpoly_coeff [Nonempty n] (M : Matrix n n R) :
    (trace n R R) M = -M.charpoly.coeff (Fintype.card n - 1) := by
  rw [charpoly_coeff_eq_prod_coeff_of_le]
  swap
  rfl
  rw [Fintype.card, prod_X_sub_C_coeff_card_pred univ fun i : n => M i i]
  simp
  rw [← Fintype.card, Fintype.card_pos_iff]
  infer_instance

-- I feel like this should use polynomial.alg_hom_eval₂_algebra_map
theorem mat_poly_equiv_eval (M : Matrix n n R[X]) (r : R) (i j : n) :
    (matPolyEquiv M).eval ((scalar n) r) i j = (M i j).eval r := by
  unfold Polynomial.eval
  unfold eval₂
  trans Polynomial.sum (matPolyEquiv M) fun a : Matrix n n R => (a * (scalar n) r ^ e) i j
  · unfold Polynomial.sum
    rw [sum_apply]
    dsimp
    rfl
    
  · simp_rw [← RingHom.map_pow, ← (scalar.commute _ _).Eq]
    simp only [coe_scalar, Matrix.one_mul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_eq_mul,
      Algebra.smul_mul_assoc]
    have h : ∀ x : ℕ, (fun a : R => r ^ e * a) x 0 = 0 := by
      simp
    simp only [Polynomial.sum, mat_poly_equiv_coeff_apply, mul_comm]
    apply (Finset.sum_subset (support_subset_support_mat_poly_equiv _ _ _) _).symm
    intro n hn h'n
    rw [not_mem_support_iff] at h'n
    simp only [h'n, zero_mul]
    

theorem eval_det (M : Matrix n n R[X]) (r : R) :
    Polynomial.eval r M.det = (Polynomial.eval (scalar n r) (matPolyEquiv M)).det := by
  rw [Polynomial.eval, ← coe_eval₂_ring_hom, RingHom.map_det]
  apply congr_argₓ det
  ext
  symm
  convert mat_poly_equiv_eval _ _ _ _

theorem det_eq_sign_charpoly_coeff (M : Matrix n n R) : M.det = -1 ^ Fintype.card n * M.charpoly.coeff 0 := by
  rw [coeff_zero_eq_eval_zero, charpoly, eval_det, mat_poly_equiv_charmatrix, ← det_smul]
  simp

end Matrix

variable {p : ℕ} [Fact p.Prime]

theorem mat_poly_equiv_eq_X_pow_sub_C {K : Type _} (k : ℕ) [Field K] (M : Matrix n n K) :
    matPolyEquiv ((expand K k : K[X] →+* K[X]).mapMatrix (charmatrix (M ^ k))) = X ^ k - c (M ^ k) := by
  ext m
  rw [coeff_sub, coeff_C, mat_poly_equiv_coeff_apply, RingHom.map_matrix_apply, Matrix.map_apply,
    AlgHom.coe_to_ring_hom, Dmatrix.sub_apply, coeff_X_pow]
  by_cases' hij : i = j
  · rw [hij, charmatrix_apply_eq, AlgHom.map_sub, expand_C, expand_X, coeff_sub, coeff_X_pow, coeff_C]
    split_ifs with mp m0 <;> simp only [Matrix.one_apply_eq, Dmatrix.zero_apply]
    
  · rw [charmatrix_apply_ne _ _ _ hij, AlgHom.map_neg, expand_C, coeff_neg, coeff_C]
    split_ifs with m0 mp <;>
      simp only [hij, zero_sub, Dmatrix.zero_apply, sub_zero, neg_zero, Matrix.one_apply_ne, Ne.def, not_false_iff]
    

@[simp]
theorem FiniteField.Matrix.charpoly_pow_card {K : Type _} [Field K] [Fintype K] (M : Matrix n n K) :
    (M ^ Fintype.card K).charpoly = M.charpoly := by
  cases (is_empty_or_nonempty n).symm
  · cases' CharP.exists K with p hp
    let this := hp
    rcases FiniteField.card K p with ⟨⟨k, kpos⟩, ⟨hp, hk⟩⟩
    have : Fact p.prime := ⟨hp⟩
    dsimp  at hk
    rw [hk] at *
    apply (frobenius_inj K[X] p).iterate k
    repeat'
      rw [iterate_frobenius]
      rw [← hk]
    rw [← FiniteField.expand_card]
    unfold charpoly
    rw [AlgHom.map_det, ← coe_det_monoid_hom, ← (det_monoid_hom : Matrix n n K[X] →* K[X]).map_pow]
    apply congr_argₓ det
    refine' mat_poly_equiv.injective _
    rw [AlgEquiv.map_pow, mat_poly_equiv_charmatrix, hk, sub_pow_char_pow_of_commute, ← C_pow]
    · exact (id (mat_poly_equiv_eq_X_pow_sub_C (p ^ k) M) : _)
      
    · exact (C M).commute_X
      
    
  · -- TODO[gh-6025]: remove this `haveI` once `subsingleton_of_empty_right` is a global instance
    have : Subsingleton (Matrix n n K) := subsingleton_of_empty_right
    exact congr_argₓ _ (Subsingleton.elimₓ _ _)
    

@[simp]
theorem Zmod.charpoly_pow_card (M : Matrix n n (Zmod p)) : (M ^ p).charpoly = M.charpoly := by
  have h := FiniteField.Matrix.charpoly_pow_card M
  rwa [Zmod.card] at h

theorem FiniteField.trace_pow_card {K : Type _} [Field K] [Fintype K] (M : Matrix n n K) :
    trace n K K (M ^ Fintype.card K) = trace n K K M ^ Fintype.card K := by
  cases is_empty_or_nonempty n
  · simp [zero_pow Fintype.card_pos]
    
  rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, FiniteField.Matrix.charpoly_pow_card,
    FiniteField.pow_card]

theorem Zmod.trace_pow_card {p : ℕ} [Fact p.Prime] (M : Matrix n n (Zmod p)) :
    trace n (Zmod p) (Zmod p) (M ^ p) = trace n (Zmod p) (Zmod p) M ^ p := by
  have h := FiniteField.trace_pow_card M
  rwa [Zmod.card] at h

namespace Matrix

theorem is_integral : IsIntegral R M :=
  ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

theorem minpoly_dvd_charpoly {K : Type _} [Field K] (M : Matrix n n K) : minpoly K M ∣ M.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly M)

/-- Any matrix polynomial `p` is equivalent under evaluation to `p %ₘ M.charpoly`; that is, `p`
is equivalent to a polynomial with degree less than the dimension of the matrix. -/
theorem aeval_eq_aeval_mod_charpoly (M : Matrix n n R) (p : R[X]) : aeval M p = aeval M (p %ₘ M.charpoly) :=
  (aeval_mod_by_monic_eq_self_of_root M.charpoly_monic M.aeval_self_charpoly).symm

/-- Any matrix power can be computed as the sum of matrix powers less than `fintype.card n`.

TODO: add the statement for negative powers phrased with `zpow`. -/
theorem pow_eq_aeval_mod_charpoly (M : Matrix n n R) (k : ℕ) : M ^ k = aeval M (X ^ k %ₘ M.charpoly) := by
  rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]

end Matrix

section PowerBasis

open Algebra

/-- The characteristic polynomial of the map `λ x, a * x` is the minimal polynomial of `a`.

In combination with `det_eq_sign_charpoly_coeff` or `trace_eq_neg_charpoly_coeff`
and a bit of rewriting, this will allow us to conclude the
field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.
-/
theorem charpoly_left_mul_matrix {K S : Type _} [Field K] [CommRingₓ S] [Algebra K S] (h : PowerBasis K S) :
    (leftMulMatrix h.Basis h.gen).charpoly = minpoly K h.gen := by
  apply minpoly.unique
  · apply Matrix.charpoly_monic
    
  · apply (injective_iff_map_eq_zero (left_mul_matrix _)).mp (left_mul_matrix_injective h.basis)
    rw [← Polynomial.aeval_alg_hom_apply, aeval_self_charpoly]
    
  · intro q q_monic root_q
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin, degree_eq_nat_degree q_monic.ne_zero]
    apply with_bot.some_le_some.mpr
    exact h.dim_le_nat_degree_of_root q_monic.ne_zero root_q
    

end PowerBasis

