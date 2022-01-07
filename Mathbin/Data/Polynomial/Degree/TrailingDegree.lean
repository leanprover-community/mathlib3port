import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Trailing degree of univariate polynomials

## Main definitions

* `trailing_degree p`: the multiplicity of `X` in the polynomial `p`
* `nat_trailing_degree`: a variant of `trailing_degree` that takes values in the natural numbers
* `trailing_coeff`: the coefficient at index `nat_trailing_degree p`

Converts most results about `degree`, `nat_degree` and `leading_coeff` to results about the bottom
end of a polynomial
-/


noncomputable section

open Function Polynomial Finsupp Finset

open_locale BigOperators Classical

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q r : Polynomial R}

/-- `trailing_degree p` is the multiplicity of `x` in the polynomial `p`, i.e. the smallest
`X`-exponent in `p`.
`trailing_degree p = some n` when `p ≠ 0` and `n` is the smallest power of `X` that appears
in `p`, otherwise
`trailing_degree 0 = ⊤`. -/
def trailing_degree (p : Polynomial R) : WithTop ℕ :=
  p.support.inf some

theorem trailing_degree_lt_wf : WellFounded fun p q : Polynomial R => trailing_degree p < trailing_degree q :=
  InvImage.wfₓ trailing_degree (WithTop.well_founded_lt Nat.lt_wf)

/-- `nat_trailing_degree p` forces `trailing_degree p` to `ℕ`, by defining
`nat_trailing_degree ⊤ = 0`. -/
def nat_trailing_degree (p : Polynomial R) : ℕ :=
  (trailing_degree p).getOrElse 0

/-- `trailing_coeff p` gives the coefficient of the smallest power of `X` in `p`-/
def trailing_coeff (p : Polynomial R) : R :=
  coeff p (nat_trailing_degree p)

/-- a polynomial is `monic_at` if its trailing coefficient is 1 -/
def trailing_monic (p : Polynomial R) :=
  trailing_coeff p = (1 : R)

theorem trailing_monic.def : trailing_monic p ↔ trailing_coeff p = 1 :=
  Iff.rfl

instance trailing_monic.decidable [DecidableEq R] : Decidable (trailing_monic p) := by
  unfold trailing_monic <;> infer_instance

@[simp]
theorem trailing_monic.trailing_coeff {p : Polynomial R} (hp : p.trailing_monic) : trailing_coeff p = 1 :=
  hp

@[simp]
theorem trailing_degree_zero : trailing_degree (0 : Polynomial R) = ⊤ :=
  rfl

@[simp]
theorem trailing_coeff_zero : trailing_coeff (0 : Polynomial R) = 0 :=
  rfl

@[simp]
theorem nat_trailing_degree_zero : nat_trailing_degree (0 : Polynomial R) = 0 :=
  rfl

theorem trailing_degree_eq_top : trailing_degree p = ⊤ ↔ p = 0 :=
  ⟨fun h => by
    rw [trailing_degree, ← min_eq_inf_with_top] at h <;> exact support_eq_empty.1 (min_eq_none.1 h), fun h => by
    simp [h]⟩

theorem trailing_degree_eq_nat_trailing_degree (hp : p ≠ 0) : trailing_degree p = (nat_trailing_degree p : WithTop ℕ) :=
  by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt trailing_degree_eq_top.1 hp))
  have hn : trailing_degree p = some n := not_not.1 hn
  rw [nat_trailing_degree, hn] <;> rfl

theorem trailing_degree_eq_iff_nat_trailing_degree_eq {p : Polynomial R} {n : ℕ} (hp : p ≠ 0) :
    p.trailing_degree = n ↔ p.nat_trailing_degree = n := by
  rw [trailing_degree_eq_nat_trailing_degree hp, WithTop.coe_eq_coe]

theorem trailing_degree_eq_iff_nat_trailing_degree_eq_of_pos {p : Polynomial R} {n : ℕ} (hn : 0 < n) :
    p.trailing_degree = n ↔ p.nat_trailing_degree = n := by
  constructor
  · intro H
    rwa [← trailing_degree_eq_iff_nat_trailing_degree_eq]
    rintro rfl
    rw [trailing_degree_zero] at H
    exact Option.noConfusion H
    
  · intro H
    rwa [trailing_degree_eq_iff_nat_trailing_degree_eq]
    rintro rfl
    rw [nat_trailing_degree_zero] at H
    rw [H] at hn
    exact lt_irreflₓ _ hn
    

theorem nat_trailing_degree_eq_of_trailing_degree_eq_some {p : Polynomial R} {n : ℕ} (h : trailing_degree p = n) :
    nat_trailing_degree p = n :=
  have hp0 : p ≠ 0 := fun hp0 => by
    rw [hp0] at h <;> exact Option.noConfusion h
  Option.some_inj.1 $
    show (nat_trailing_degree p : WithTop ℕ) = n by
      rwa [← trailing_degree_eq_nat_trailing_degree hp0]

@[simp]
theorem nat_trailing_degree_le_trailing_degree : ↑nat_trailing_degree p ≤ trailing_degree p := by
  by_cases' hp : p = 0
  · rw [hp, trailing_degree_zero]
    exact le_top
    
  rw [trailing_degree_eq_nat_trailing_degree hp]
  exact le_reflₓ _

theorem nat_trailing_degree_eq_of_trailing_degree_eq [Semiringₓ S] {q : Polynomial S}
    (h : trailing_degree p = trailing_degree q) : nat_trailing_degree p = nat_trailing_degree q := by
  unfold nat_trailing_degree <;> rw [h]

theorem le_trailing_degree_of_ne_zero (h : coeff p n ≠ 0) : trailing_degree p ≤ n :=
  show @LE.le (WithTop ℕ) _ (p.support.inf some : WithTop ℕ) (some n : WithTop ℕ) from
    Finset.inf_le (mem_support_iff.2 h)

theorem nat_trailing_degree_le_of_ne_zero (h : coeff p n ≠ 0) : nat_trailing_degree p ≤ n := by
  rw [← WithTop.coe_le_coe, ← trailing_degree_eq_nat_trailing_degree]
  · exact le_trailing_degree_of_ne_zero h
    
  · intro h
    subst h
    exact h rfl
    

theorem trailing_degree_le_trailing_degree (h : coeff q (nat_trailing_degree p) ≠ 0) :
    trailing_degree q ≤ trailing_degree p := by
  by_cases' hp : p = 0
  · rw [hp]
    exact le_top
    
  · rw [trailing_degree_eq_nat_trailing_degree hp]
    exact le_trailing_degree_of_ne_zero h
    

theorem trailing_degree_ne_of_nat_trailing_degree_ne {n : ℕ} : p.nat_trailing_degree ≠ n → trailing_degree p ≠ n :=
  mt $ fun h => by
    rw [nat_trailing_degree, h, Option.get_or_else_coe]

theorem nat_trailing_degree_le_of_trailing_degree_le {n : ℕ} {hp : p ≠ 0} (H : (n : WithTop ℕ) ≤ trailing_degree p) :
    n ≤ nat_trailing_degree p := by
  rw [trailing_degree_eq_nat_trailing_degree hp] at H
  exact with_top.coe_le_coe.mp H

theorem nat_trailing_degree_le_nat_trailing_degree {hq : q ≠ 0} (hpq : p.trailing_degree ≤ q.trailing_degree) :
    p.nat_trailing_degree ≤ q.nat_trailing_degree := by
  by_cases' hp : p = 0
  · rw [hp, nat_trailing_degree_zero]
    exact zero_le _
    
  rwa [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq, WithTop.coe_le_coe] at hpq

@[simp]
theorem trailing_degree_monomial (ha : a ≠ 0) : trailing_degree (monomial n a) = n := by
  rw [trailing_degree, support_monomial _ _ ha, inf_singleton, WithTop.some_eq_coe]

theorem nat_trailing_degree_monomial (ha : a ≠ 0) : nat_trailing_degree (monomial n a) = n := by
  rw [nat_trailing_degree, trailing_degree_monomial ha] <;> rfl

theorem nat_trailing_degree_monomial_le : nat_trailing_degree (monomial n a) ≤ n :=
  if ha : a = 0 then by
    simp [ha]
  else (nat_trailing_degree_monomial ha).le

theorem le_trailing_degree_monomial : ↑n ≤ trailing_degree (monomial n a) :=
  if ha : a = 0 then by
    simp [ha]
  else (trailing_degree_monomial ha).Ge

@[simp]
theorem trailing_degree_C (ha : a ≠ 0) : trailing_degree (C a) = (0 : WithTop ℕ) :=
  trailing_degree_monomial ha

theorem le_trailing_degree_C : (0 : WithTop ℕ) ≤ trailing_degree (C a) :=
  le_trailing_degree_monomial

theorem trailing_degree_one_le : (0 : WithTop ℕ) ≤ trailing_degree (1 : Polynomial R) := by
  rw [← C_1] <;> exact le_trailing_degree_C

@[simp]
theorem nat_trailing_degree_C (a : R) : nat_trailing_degree (C a) = 0 :=
  nonpos_iff_eq_zero.1 nat_trailing_degree_monomial_le

@[simp]
theorem nat_trailing_degree_one : nat_trailing_degree (1 : Polynomial R) = 0 :=
  nat_trailing_degree_C 1

@[simp]
theorem nat_trailing_degree_nat_cast (n : ℕ) : nat_trailing_degree (n : Polynomial R) = 0 := by
  simp only [← C_eq_nat_cast, nat_trailing_degree_C]

@[simp]
theorem trailing_degree_C_mul_X_pow (n : ℕ) (ha : a ≠ 0) : trailing_degree (C a * X ^ n) = n := by
  rw [C_mul_X_pow_eq_monomial, trailing_degree_monomial ha]

theorem le_trailing_degree_C_mul_X_pow (n : ℕ) (a : R) : (n : WithTop ℕ) ≤ trailing_degree (C a * X ^ n) := by
  rw [C_mul_X_pow_eq_monomial]
  exact le_trailing_degree_monomial

theorem coeff_eq_zero_of_trailing_degree_lt (h : (n : WithTop ℕ) < trailing_degree p) : coeff p n = 0 :=
  not_not.1 (mt le_trailing_degree_of_ne_zero (not_le_of_gtₓ h))

theorem coeff_eq_zero_of_lt_nat_trailing_degree {p : Polynomial R} {n : ℕ} (h : n < p.nat_trailing_degree) :
    p.coeff n = 0 := by
  apply coeff_eq_zero_of_trailing_degree_lt
  by_cases' hp : p = 0
  · rw [hp, trailing_degree_zero]
    exact WithTop.coe_lt_top n
    
  · rwa [trailing_degree_eq_nat_trailing_degree hp, WithTop.coe_lt_coe]
    

@[simp]
theorem coeff_nat_trailing_degree_pred_eq_zero {p : Polynomial R} {hp : (0 : WithTop ℕ) < nat_trailing_degree p} :
    p.coeff (p.nat_trailing_degree - 1) = 0 :=
  coeff_eq_zero_of_lt_nat_trailing_degree $
    Nat.sub_ltₓ ((WithTop.zero_lt_coe (nat_trailing_degree p)).mp hp) Nat.one_posₓ

theorem le_trailing_degree_X_pow (n : ℕ) : (n : WithTop ℕ) ≤ trailing_degree (X ^ n : Polynomial R) := by
  simpa only [C_1, one_mulₓ] using le_trailing_degree_C_mul_X_pow n (1 : R)

theorem le_trailing_degree_X : (1 : WithTop ℕ) ≤ trailing_degree (X : Polynomial R) :=
  le_trailing_degree_monomial

theorem nat_trailing_degree_X_le : (X : Polynomial R).natTrailingDegree ≤ 1 :=
  nat_trailing_degree_monomial_le

@[simp]
theorem trailing_coeff_eq_zero : trailing_coeff p = 0 ↔ p = 0 :=
  ⟨fun h =>
    by_contradiction $ fun hp =>
      mt mem_support_iff.1 (not_not.2 h) (mem_of_min (trailing_degree_eq_nat_trailing_degree hp)),
    fun h => h.symm ▸ leading_coeff_zero⟩

theorem trailing_coeff_nonzero_iff_nonzero : trailing_coeff p ≠ 0 ↔ p ≠ 0 :=
  not_congr trailing_coeff_eq_zero

theorem nat_trailing_degree_mem_support_of_nonzero : p ≠ 0 → nat_trailing_degree p ∈ p.support :=
  mem_support_iff.mpr ∘ trailing_coeff_nonzero_iff_nonzero.mpr

theorem nat_trailing_degree_le_of_mem_supp (a : ℕ) : a ∈ p.support → nat_trailing_degree p ≤ a :=
  nat_trailing_degree_le_of_ne_zero ∘ mem_support_iff.mp

theorem nat_trailing_degree_eq_support_min' (h : p ≠ 0) :
    nat_trailing_degree p = p.support.min' (nonempty_support_iff.mpr h) := by
  apply le_antisymmₓ
  · apply le_min'
    intro y hy
    exact nat_trailing_degree_le_of_mem_supp y hy
    
  · apply Finset.min'_le
    exact mem_support_iff.mpr (trailing_coeff_nonzero_iff_nonzero.mpr h)
    

theorem nat_trailing_degree_le_nat_degree (p : Polynomial R) : p.nat_trailing_degree ≤ p.nat_degree := by
  by_cases' hp : p = 0
  · rw [hp, nat_degree_zero, nat_trailing_degree_zero]
    
  · exact le_nat_degree_of_ne_zero (mt trailing_coeff_eq_zero.mp hp)
    

theorem nat_trailing_degree_mul_X_pow {p : Polynomial R} (hp : p ≠ 0) (n : ℕ) :
    (p * X ^ n).natTrailingDegree = p.nat_trailing_degree + n := by
  apply le_antisymmₓ
  · refine' nat_trailing_degree_le_of_ne_zero fun h => mt trailing_coeff_eq_zero.mp hp _
    rwa [trailing_coeff, ← coeff_mul_X_pow]
    
  · rw [nat_trailing_degree_eq_support_min' fun h => hp (mul_X_pow_eq_zero h), Finset.le_min'_iff]
    intro y hy
    have key : n ≤ y := by
      rw [mem_support_iff, coeff_mul_X_pow'] at hy
      exact by_contra fun h => hy (if_neg h)
    rw [mem_support_iff, coeff_mul_X_pow', if_pos key] at hy
    exact (le_tsub_iff_right key).mp (nat_trailing_degree_le_of_ne_zero hy)
    

end Semiringₓ

section NonzeroSemiring

variable [Semiringₓ R] [Nontrivial R] {p q : Polynomial R}

@[simp]
theorem trailing_degree_one : trailing_degree (1 : Polynomial R) = (0 : WithTop ℕ) :=
  trailing_degree_C one_ne_zero

@[simp]
theorem trailing_degree_X : trailing_degree (X : Polynomial R) = 1 :=
  trailing_degree_monomial one_ne_zero

@[simp]
theorem nat_trailing_degree_X : (X : Polynomial R).natTrailingDegree = 1 :=
  nat_trailing_degree_monomial one_ne_zero

end NonzeroSemiring

section Ringₓ

variable [Ringₓ R]

@[simp]
theorem trailing_degree_neg (p : Polynomial R) : trailing_degree (-p) = trailing_degree p := by
  unfold trailing_degree <;> rw [support_neg]

@[simp]
theorem nat_trailing_degree_neg (p : Polynomial R) : nat_trailing_degree (-p) = nat_trailing_degree p := by
  simp [nat_trailing_degree]

@[simp]
theorem nat_trailing_degree_int_cast (n : ℤ) : nat_trailing_degree (n : Polynomial R) = 0 := by
  simp only [← C_eq_int_cast, nat_trailing_degree_C]

end Ringₓ

section Semiringₓ

variable [Semiringₓ R]

/-- The second-lowest coefficient, or 0 for constants -/
def next_coeff_up (p : Polynomial R) : R :=
  if p.nat_trailing_degree = 0 then 0 else p.coeff (p.nat_trailing_degree + 1)

@[simp]
theorem next_coeff_up_C_eq_zero (c : R) : next_coeff_up (C c) = 0 := by
  rw [next_coeff_up]
  simp

theorem next_coeff_up_of_pos_nat_trailing_degree (p : Polynomial R) (hp : 0 < p.nat_trailing_degree) :
    next_coeff_up p = p.coeff (p.nat_trailing_degree + 1) := by
  rw [next_coeff_up, if_neg]
  contrapose! hp
  simpa

end Semiringₓ

section Semiringₓ

variable [Semiringₓ R] {p q : Polynomial R} {ι : Type _}

theorem coeff_nat_trailing_degree_eq_zero_of_trailing_degree_lt (h : trailing_degree p < trailing_degree q) :
    coeff q (nat_trailing_degree p) = 0 :=
  coeff_eq_zero_of_trailing_degree_lt $ nat_trailing_degree_le_trailing_degree.trans_lt h

theorem ne_zero_of_trailing_degree_lt {n : WithTop ℕ} (h : trailing_degree p < n) : p ≠ 0 := fun h₀ =>
  h.not_le
    (by
      simp [h₀])

end Semiringₓ

end Polynomial

