import Mathbin.NumberTheory.Liouville.Basic

/-!

# Liouville constants

This file contains a construction of a family of Liouville numbers, indexed by a natural number $m$.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `liouville.is_transcendental`.

More precisely, for a real number $m$, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for $1 < m$.  However, there is no restriction on $m$, since,
if the series does not converge, then the sum of the series is defined to be zero.

We prove that, for $m \in \mathbb{N}$ satisfying $2 \le m$, Liouville's constant associated to $m$
is a transcendental number.  Classically, the Liouville number for $m = 2$ is the one called
``Liouville's constant''.

## Implementation notes

The indexing $m$ is eventually a natural number satisfying $2 ≤ m$.  However, we prove the first few
lemmas for $m \in \mathbb{R}$.
-/


noncomputable section 

open_locale Nat BigOperators

open Real Finset

namespace Liouville

/--
For a real number `m`, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for `1 < m`.  However, there is no restriction on `m`, since,
if the series does not converge, then the sum of the series is defined to be zero.
-/
def liouville_number (m : ℝ) : ℝ :=
  ∑' i : ℕ, 1 / (m^i !)

/--
`liouville_number_initial_terms` is the sum of the first `k + 1` terms of Liouville's constant,
i.e.
$$
\sum_{i=0}^k\frac{1}{m^{i!}}.
$$
-/
def liouville_number_initial_terms (m : ℝ) (k : ℕ) : ℝ :=
  ∑ i in range (k+1), 1 / (m^i !)

/--
`liouville_number_tail` is the sum of the series of the terms in `liouville_number m`
starting from `k+1`, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}.
$$
-/
def liouville_number_tail (m : ℝ) (k : ℕ) : ℝ :=
  ∑' i, 1 / (m^(i+k+1)!)

theorem liouville_number_tail_pos {m : ℝ} (hm : 1 < m) (k : ℕ) : 0 < liouville_number_tail m k :=
  calc (0 : ℝ) = ∑' i : ℕ, 0 := tsum_zero.symm 
    _ < liouville_number_tail m k :=
    tsum_lt_tsum_of_nonneg (fun _ => rfl.le) (fun i => one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))
        (one_div_pos.mpr (pow_pos (zero_lt_one.trans hm) (0+k+1)!))$
      summable_one_div_pow_of_le hm fun i => trans le_self_add (Nat.self_le_factorial _)
    

/--  Split the sum definining a Liouville number into the first `k` term and the rest. -/
theorem liouville_number_eq_initial_terms_add_tail {m : ℝ} (hm : 1 < m) (k : ℕ) :
  liouville_number m = liouville_number_initial_terms m k+liouville_number_tail m k :=
  (sum_add_tsum_nat_add _ (summable_one_div_pow_of_le hm fun i => i.self_le_factorial)).symm

/-! We now prove two useful inequalities, before collecting everything together. -/


/--  Partial inequality, works with `m ∈ ℝ` satisfying `1 < m`. -/
theorem tsum_one_div_pow_factorial_lt (n : ℕ) {m : ℝ} (m1 : 1 < m) :
  (∑' i : ℕ, 1 / (m^(i+n+1)!)) < (1 - 1 / m)⁻¹*1 / (m^(n+1)!) :=
  have m0 : 0 < m := zero_lt_one.trans m1 
  have mi : |1 / m| < 1 := (le_of_eqₓ (abs_of_pos (one_div_pos.mpr m0))).trans_lt ((div_lt_one m0).mpr m1)
  calc (∑' i, 1 / (m^(i+n+1)!)) < ∑' i, 1 / (m^i+(n+1)!) :=
    tsum_lt_tsum_of_nonneg (fun b => one_div_nonneg.mpr (pow_nonneg m0.le _))
      (fun b => one_div_pow_le_one_div_pow_of_le m1.le (b.add_factorial_succ_le_factorial_add_succ n))
      (one_div_pow_strict_mono m1 (n.add_factorial_succ_lt_factorial_add_succ rfl.le))
      (summable_one_div_pow_of_le m1 fun j => Nat.Le.intro rfl)
    _ = ∑' i, (1 / m^i)*1 / (m^(n+1)!) :=
    by 
      congr 
      ext i 
      rw [pow_addₓ, ←div_div_eq_div_mul, div_eq_mul_one_div, ←one_div_pow i]
    _ = (∑' i, 1 / m^i)*1 / (m^(n+1)!) := tsum_mul_right 
    _ = (1 - 1 / m)⁻¹*1 / (m^(n+1)!) := mul_eq_mul_right_iff.mpr (Or.inl (tsum_geometric_of_abs_lt_1 mi))
    

theorem aux_calc (n : ℕ) {m : ℝ} (hm : 2 ≤ m) : ((1 - 1 / m)⁻¹*1 / (m^(n+1)!)) ≤ 1 / ((m^n !)^n) :=
  calc ((1 - 1 / m)⁻¹*1 / (m^(n+1)!)) ≤ 2*1 / (m^(n+1)!) :=
    mul_mono_nonneg (one_div_nonneg.mpr (pow_nonneg (zero_le_two.trans hm) _)) (sub_one_div_inv_le_two hm)
    _ = 2 / (m^(n+1)!) := mul_one_div 2 _ 
    _ = 2 / (m^n !*n+1) := congr_argₓ ((· / ·) 2) (congr_argₓ (pow m) (mul_commₓ _ _))
    _ ≤ 1 / (m^n !*n) :=
    by 
      apply (div_le_div_iff _ _).mpr 
      convRHS => rw [one_mulₓ, mul_addₓ, pow_addₓ, mul_oneₓ, pow_mulₓ, mul_commₓ, ←pow_mulₓ]
      apply (mul_le_mul_right _).mpr 
      any_goals 
        exact pow_pos (zero_lt_two.trans_le hm) _ 
      exact trans (trans hm (pow_oneₓ _).symm.le) (pow_mono (one_le_two.trans hm) n.factorial_pos)
    _ = 1 / ((m^n !)^n) := congr_argₓ ((· / ·) 1) (pow_mulₓ m n ! n)
    

/-!  Starting from here, we specialize to the case in which `m` is a natural number. -/


/--  The sum of the `k` initial terms of the Liouville number to base `m` is a ratio of natural
numbers where the denominator is `m ^ k!`. -/
theorem liouville_number_rat_initial_terms {m : ℕ} (hm : 0 < m) (k : ℕ) :
  ∃ p : ℕ, liouville_number_initial_terms m k = p / (m^k !) :=
  by 
    induction' k with k h
    ·
      exact
        ⟨1,
          by 
            rw [liouville_number_initial_terms, range_one, sum_singleton, Nat.cast_one]⟩
    ·
      rcases h with ⟨p_k, h_k⟩
      use (p_k*m^(k+1)! - k !)+1
      unfold liouville_number_initial_terms  at h_k⊢
      rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, add_mulₓ]
      ·
        normCast 
        rw [add_mulₓ, one_mulₓ, Nat.factorial_succ,
          show (k.succ*k !) - k ! = (k.succ - 1)*k !by 
            rw [tsub_mul, one_mulₓ],
          Nat.succ_sub_one, add_mulₓ, one_mulₓ, pow_addₓ]
        simp [mul_assocₓ]
      refine' mul_ne_zero_iff.mpr ⟨_, _⟩
      all_goals 
        exact pow_ne_zero _ (nat.cast_ne_zero.mpr hm.ne.symm)

theorem is_liouville {m : ℕ} (hm : 2 ≤ m) : Liouville (liouville_number m) :=
  by 
    have mZ1 : 1 < (m : ℤ)
    ·
      normCast 
      exact one_lt_two.trans_le hm 
    have m1 : 1 < (m : ℝ)
    ·
      normCast 
      exact one_lt_two.trans_le hm 
    intro n 
    rcases liouville_number_rat_initial_terms (zero_lt_two.trans_le hm) n with ⟨p, hp⟩
    refine' ⟨p, m^n !, one_lt_pow mZ1 n.factorial_ne_zero, _⟩
    pushCast 
    rw [liouville_number_eq_initial_terms_add_tail m1 n, ←hp, add_sub_cancel',
      abs_of_nonneg (liouville_number_tail_pos m1 _).le]
    exact
      ⟨((lt_add_iff_pos_right _).mpr (liouville_number_tail_pos m1 n)).Ne.symm,
        (tsum_one_div_pow_factorial_lt n m1).trans_le (aux_calc _ (nat.cast_two.symm.le.trans (nat.cast_le.mpr hm)))⟩

theorem is_transcendental {m : ℕ} (hm : 2 ≤ m) : _root_.transcendental ℤ (liouville_number m) :=
  Transcendental (is_liouville hm)

end Liouville

