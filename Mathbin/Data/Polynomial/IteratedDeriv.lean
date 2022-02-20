/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Polynomial.Derivative
import Mathbin.Tactic.Linarith.Default

/-!
# Theory of iterated derivative
We define and prove some lemmas about iterated (formal) derivative for polynomials over a semiring.
-/


noncomputable section

open Finset Nat Polynomial

open_locale BigOperators Polynomial

namespace Polynomial

universe u

variable {R : Type u}

section Semiringₓ

variable [Semiringₓ R] (r : R) (f p q : R[X]) (n k : ℕ)

/-- `iterated_deriv f n` is the `n`-th formal derivative of the polynomial `f` -/
def iteratedDeriv : R[X] :=
  (derivative^[n]) f

@[simp]
theorem iterated_deriv_zero_right : iteratedDeriv f 0 = f :=
  rfl

theorem iterated_deriv_succ : iteratedDeriv f (n + 1) = (iteratedDeriv f n).derivative := by
  rw [iterated_deriv, iterated_deriv, Function.iterate_succ']

@[simp]
theorem iterated_deriv_zero_left : iteratedDeriv (0 : R[X]) n = 0 := by
  induction' n with n hn
  · exact iterated_deriv_zero_right _
    
  · rw [iterated_deriv_succ, hn, derivative_zero]
    

@[simp]
theorem iterated_deriv_add : iteratedDeriv (p + q) n = iteratedDeriv p n + iteratedDeriv q n := by
  induction' n with n ih
  · simp only [iterated_deriv_zero_right]
    
  · simp only [iterated_deriv_succ, ih, derivative_add]
    

@[simp]
theorem iterated_deriv_smul : iteratedDeriv (r • p) n = r • iteratedDeriv p n := by
  induction' n with n ih
  · simp only [iterated_deriv_zero_right]
    
  · simp only [iterated_deriv_succ, ih, derivative_smul]
    

@[simp]
theorem iterated_deriv_X_zero : iteratedDeriv (x : R[X]) 0 = X := by
  simp only [iterated_deriv_zero_right]

@[simp]
theorem iterated_deriv_X_one : iteratedDeriv (x : R[X]) 1 = 1 := by
  simp only [iterated_deriv, derivative_X, Function.iterate_one]

@[simp]
theorem iterated_deriv_X (h : 1 < n) : iteratedDeriv (x : R[X]) n = 0 := by
  induction' n with n ih
  · exfalso
    exact Nat.not_lt_zeroₓ 1 h
    
  · simp only [iterated_deriv_succ]
    by_cases' H : n = 1
    · rw [H]
      simp only [iterated_deriv_X_one, derivative_one]
      
    · replace h : 1 < n := Arrayₓ.push_back_idx h (Ne.symm H)
      rw [ih h]
      simp only [derivative_zero]
      
    

@[simp]
theorem iterated_deriv_C_zero : iteratedDeriv (c r) 0 = c r := by
  simp only [iterated_deriv_zero_right]

@[simp]
theorem iterated_deriv_C (h : 0 < n) : iteratedDeriv (c r) n = 0 := by
  induction' n with n ih
  · exfalso
    exact Nat.lt_asymmₓ h h
    
  · by_cases' H : n = 0
    · rw [iterated_deriv_succ, H]
      simp only [iterated_deriv_C_zero, derivative_C]
      
    · replace h : 0 < n := Nat.pos_of_ne_zeroₓ H
      rw [iterated_deriv_succ, ih h]
      simp only [derivative_zero]
      
    

@[simp]
theorem iterated_deriv_one_zero : iteratedDeriv (1 : R[X]) 0 = 1 := by
  simp only [iterated_deriv_zero_right]

@[simp]
theorem iterated_deriv_one : 0 < n → iteratedDeriv (1 : R[X]) n = 0 := fun h => by
  have eq1 : (1 : R[X]) = C 1 := by
    simp only [RingHom.map_one]
  rw [eq1]
  exact iterated_deriv_C _ _ h

end Semiringₓ

section Ringₓ

variable [Ringₓ R] (p q : R[X]) (n : ℕ)

@[simp]
theorem iterated_deriv_neg : iteratedDeriv (-p) n = -iteratedDeriv p n := by
  induction' n with n ih
  · simp only [iterated_deriv_zero_right]
    
  · simp only [iterated_deriv_succ, ih, derivative_neg]
    

@[simp]
theorem iterated_deriv_sub : iteratedDeriv (p - q) n = iteratedDeriv p n - iteratedDeriv q n := by
  rw [sub_eq_add_neg, iterated_deriv_add, iterated_deriv_neg, ← sub_eq_add_neg]

end Ringₓ

section CommSemiringₓ

variable [CommSemiringₓ R]

variable (f p q : R[X]) (n k : ℕ)

theorem coeff_iterated_deriv_as_prod_Ico :
    ∀ m : ℕ, (iteratedDeriv f k).coeff m = (∏ i in ico m.succ (m + k.succ), i) * f.coeff (m + k) := by
  induction' k with k ih
  · simp only [add_zeroₓ, forall_const, one_mulₓ, Ico_self, eq_self_iff_true, iterated_deriv_zero_right, prod_empty]
    
  · intro m
    rw [iterated_deriv_succ, coeff_derivative, ih (m + 1), mul_right_commₓ]
    apply congr_arg2ₓ
    · have set_eq : Ico m.succ (m + k.succ.succ) = Ico (m + 1).succ (m + 1 + k.succ) ∪ {m + 1} := by
        rw [union_comm, ← insert_eq, Ico_insert_succ_left, add_succ, add_succ, add_succ _ k, ← succ_eq_add_one,
          succ_add]
        rw [succ_eq_add_one]
        linarith
      rw [set_eq, prod_union]
      apply congr_arg2ₓ
      · rfl
        
      · simp only [prod_singleton]
        norm_cast
        
      · rw [disjoint_singleton_right, mem_Ico]
        exact fun h => (Nat.lt_succ_selfₓ _).not_le h.1
        
      
    · exact congr_argₓ _ (succ_add m k)
      
    

theorem coeff_iterated_deriv_as_prod_range :
    ∀ m : ℕ, (iteratedDeriv f k).coeff m = f.coeff (m + k) * ∏ i in range k, ↑(m + k - i) := by
  induction' k with k ih
  · simp
    
  intro m
  calc (f.iterated_deriv k.succ).coeff m = (f.coeff (m + k.succ) * ∏ i in range k, ↑(m + k.succ - i)) * (m + 1) := by
      rw [iterated_deriv_succ, coeff_derivative, ih m.succ, succ_add,
        add_succ]_ = (f.coeff (m + k.succ) * ∏ i in range k, ↑(m + k.succ - i)) * ↑(m + 1) :=
      by
      push_cast _ = f.coeff (m + k.succ) * ∏ i in range k.succ, ↑(m + k.succ - i) := by
      rw [prod_range_succ, add_tsub_assoc_of_le k.le_succ, succ_sub le_rfl, tsub_self, mul_assoc]

theorem iterated_deriv_eq_zero_of_nat_degree_lt (h : f.natDegree < n) : iteratedDeriv f n = 0 := by
  ext m
  rw [coeff_iterated_deriv_as_prod_range, coeff_zero, coeff_eq_zero_of_nat_degree_lt, zero_mul]
  linarith

theorem iterated_deriv_mul :
    iteratedDeriv (p * q) n = ∑ k in range n.succ, c (n.choose k : R) * iteratedDeriv p (n - k) * iteratedDeriv q k :=
  by
  induction' n with n IH
  · simp
    
  calc
    (p * q).iteratedDeriv n.succ =
        (∑ k : ℕ in range n.succ, C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv k).derivative :=
      by
      rw [iterated_deriv_succ,
        IH]_ =
        (∑ k : ℕ in range n.succ, C ↑(n.choose k) * p.iterated_deriv (n - k + 1) * q.iterated_deriv k) +
          ∑ k : ℕ in range n.succ, C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) :=
      by
      simp_rw [derivative_sum, derivative_mul, derivative_C, zero_mul, zero_addₓ, iterated_deriv_succ,
        sum_add_distrib]_ =
        (∑ k : ℕ in range n.succ, C ↑(n.choose k.succ) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1)) +
            C ↑1 * p.iterated_deriv n.succ * q.iterated_deriv 0 +
          ∑ k : ℕ in range n.succ, C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1) :=
      _ _ =
        ((∑ k : ℕ in range n.succ, C ↑(n.choose k) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1)) +
            ∑ k : ℕ in range n.succ, C ↑(n.choose k.succ) * p.iterated_deriv (n - k) * q.iterated_deriv (k + 1)) +
          C ↑1 * p.iterated_deriv n.succ * q.iterated_deriv 0 :=
      by
      ring _ =
        (∑ i : ℕ in range n.succ,
            C ↑((n + 1).choose (i + 1)) * p.iterated_deriv (n + 1 - (i + 1)) * q.iterated_deriv (i + 1)) +
          C ↑1 * p.iterated_deriv n.succ * q.iterated_deriv 0 :=
      by
      simp_rw [choose_succ_succ, succ_sub_succ, cast_add, C.map_add, add_mulₓ,
        sum_add_distrib]_ =
        ∑ k : ℕ in range n.succ.succ, C ↑(n.succ.choose k) * p.iterated_deriv (n.succ - k) * q.iterated_deriv k :=
      by
      rw [sum_range_succ' _ n.succ, choose_zero_right, tsub_zero]
  congr
  refine' (sum_range_succ' _ _).trans (congr_arg2ₓ (· + ·) _ _)
  · rw [sum_range_succ, Nat.choose_succ_self, cast_zero, C.map_zero, zero_mul, zero_mul, add_zeroₓ]
    refine' sum_congr rfl fun k hk => _
    rw [mem_range] at hk
    congr
    rw [tsub_add_eq_add_tsub (Nat.succ_le_of_ltₓ hk), Nat.succ_sub_succ]
    
  · rw [choose_zero_right, tsub_zero]
    

end CommSemiringₓ

end Polynomial

