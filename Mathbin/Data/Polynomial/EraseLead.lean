import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `erase_lead f`: the polynomial `f - leading term of f`

`erase_lead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/


noncomputable theory

open_locale Classical

open Polynomial Finset

namespace Polynomial

variable{R : Type _}[Semiringₓ R]{f : Polynomial R}

/-- `erase_lead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
def erase_lead (f : Polynomial R) : Polynomial R :=
  Polynomial.erase f.nat_degree f

section EraseLead

theorem erase_lead_support (f : Polynomial R) : f.erase_lead.support = f.support.erase f.nat_degree :=
  by 
    simp only [erase_lead, support_erase]

theorem erase_lead_coeff (i : ℕ) : f.erase_lead.coeff i = if i = f.nat_degree then 0 else f.coeff i :=
  by 
    simp only [erase_lead, coeff_erase]

@[simp]
theorem erase_lead_coeff_nat_degree : f.erase_lead.coeff f.nat_degree = 0 :=
  by 
    simp [erase_lead_coeff]

theorem erase_lead_coeff_of_ne (i : ℕ) (hi : i ≠ f.nat_degree) : f.erase_lead.coeff i = f.coeff i :=
  by 
    simp [erase_lead_coeff, hi]

@[simp]
theorem erase_lead_zero : erase_lead (0 : Polynomial R) = 0 :=
  by 
    simp only [erase_lead, erase_zero]

@[simp]
theorem erase_lead_add_monomial_nat_degree_leading_coeff (f : Polynomial R) :
  (f.erase_lead+monomial f.nat_degree f.leading_coeff) = f :=
  by 
    ext i 
    simp only [erase_lead_coeff, coeff_monomial, coeff_add, @eq_comm _ _ i]
    splitIfs with h
    ·
      subst i 
      simp only [leading_coeff, zero_addₓ]
    ·
      exact add_zeroₓ _

@[simp]
theorem erase_lead_add_C_mul_X_pow (f : Polynomial R) : (f.erase_lead+C f.leading_coeff*X ^ f.nat_degree) = f :=
  by 
    rw [C_mul_X_pow_eq_monomial, erase_lead_add_monomial_nat_degree_leading_coeff]

@[simp]
theorem self_sub_monomial_nat_degree_leading_coeff {R : Type _} [Ringₓ R] (f : Polynomial R) :
  f - monomial f.nat_degree f.leading_coeff = f.erase_lead :=
  (eq_sub_iff_add_eq.mpr (erase_lead_add_monomial_nat_degree_leading_coeff f)).symm

@[simp]
theorem self_sub_C_mul_X_pow {R : Type _} [Ringₓ R] (f : Polynomial R) :
  (f - C f.leading_coeff*X ^ f.nat_degree) = f.erase_lead :=
  by 
    rw [C_mul_X_pow_eq_monomial, self_sub_monomial_nat_degree_leading_coeff]

theorem erase_lead_ne_zero (f0 : 2 ≤ f.support.card) : erase_lead f ≠ 0 :=
  by 
    rw [Ne.def, ←card_support_eq_zero, erase_lead_support]
    exact (zero_lt_one.trans_le$ (tsub_le_tsub_right f0 1).trans Finset.pred_card_le_card_erase).Ne.symm

@[simp]
theorem nat_degree_not_mem_erase_lead_support : f.nat_degree ∉ (erase_lead f).Support :=
  by 
    simp [not_mem_support_iff]

theorem ne_nat_degree_of_mem_erase_lead_support {a : ℕ} (h : a ∈ (erase_lead f).Support) : a ≠ f.nat_degree :=
  by 
    rintro rfl 
    exact nat_degree_not_mem_erase_lead_support h

theorem erase_lead_support_card_lt (h : f ≠ 0) : (erase_lead f).Support.card < f.support.card :=
  by 
    rw [erase_lead_support]
    exact card_lt_card (erase_ssubset$ nat_degree_mem_support_of_nonzero h)

theorem erase_lead_card_support {c : ℕ} (fc : f.support.card = c) : f.erase_lead.support.card = c - 1 :=
  by 
    byCases' f0 : f = 0
    ·
      rw [←fc, f0, erase_lead_zero, support_zero, card_empty]
    ·
      rw [erase_lead_support, card_erase_of_mem (nat_degree_mem_support_of_nonzero f0), fc]
      exact c.pred_eq_sub_one

theorem erase_lead_card_support' {c : ℕ} (fc : f.support.card = c+1) : f.erase_lead.support.card = c :=
  erase_lead_card_support fc

@[simp]
theorem erase_lead_monomial (i : ℕ) (r : R) : erase_lead (monomial i r) = 0 :=
  by 
    byCases' hr : r = 0
    ·
      subst r 
      simp only [monomial_zero_right, erase_lead_zero]
    ·
      rw [erase_lead, nat_degree_monomial _ _ hr, erase_monomial]

@[simp]
theorem erase_lead_C (r : R) : erase_lead (C r) = 0 :=
  erase_lead_monomial _ _

@[simp]
theorem erase_lead_X : erase_lead (X : Polynomial R) = 0 :=
  erase_lead_monomial _ _

@[simp]
theorem erase_lead_X_pow (n : ℕ) : erase_lead (X ^ n : Polynomial R) = 0 :=
  by 
    rw [X_pow_eq_monomial, erase_lead_monomial]

@[simp]
theorem erase_lead_C_mul_X_pow (r : R) (n : ℕ) : erase_lead (C r*X ^ n) = 0 :=
  by 
    rw [C_mul_X_pow_eq_monomial, erase_lead_monomial]

theorem erase_lead_degree_le : (erase_lead f).degree ≤ f.degree :=
  by 
    rw [degree_le_iff_coeff_zero]
    intro i hi 
    rw [erase_lead_coeff]
    splitIfs with h
    ·
      rfl 
    apply coeff_eq_zero_of_degree_lt hi

theorem erase_lead_nat_degree_le : (erase_lead f).natDegree ≤ f.nat_degree :=
  nat_degree_le_nat_degree erase_lead_degree_le

theorem erase_lead_nat_degree_lt (f0 : 2 ≤ f.support.card) : (erase_lead f).natDegree < f.nat_degree :=
  lt_of_le_of_neₓ erase_lead_nat_degree_le$
    ne_nat_degree_of_mem_erase_lead_support$ nat_degree_mem_support_of_nonzero$ erase_lead_ne_zero f0

theorem erase_lead_nat_degree_lt_or_erase_lead_eq_zero (f : Polynomial R) :
  (erase_lead f).natDegree < f.nat_degree ∨ f.erase_lead = 0 :=
  by 
    byCases' h : f.support.card ≤ 1
    ·
      right 
      rw [←C_mul_X_pow_eq_self h]
      simp 
    ·
      left 
      apply erase_lead_nat_degree_lt (lt_of_not_geₓ h)

end EraseLead

/-- An induction lemma for polynomials. It takes a natural number `N` as a parameter, that is
required to be at least as big as the `nat_degree` of the polynomial.  This is useful to prove
results where you want to change each term in a polynomial to something else depending on the
`nat_degree` of the polynomial itself and not on the specific `nat_degree` of each term. -/
theorem induction_with_nat_degree_le {R : Type _} [Semiringₓ R] {P : Polynomial R → Prop} (N : ℕ) (P_0 : P 0)
  (P_C_mul_pow : ∀ (n : ℕ), ∀ (r : R), r ≠ 0 → n ≤ N → P (C r*X ^ n))
  (P_C_add : ∀ (f g : Polynomial R), f.nat_degree ≤ N → g.nat_degree ≤ N → P f → P g → P (f+g)) :
  ∀ (f : Polynomial R), f.nat_degree ≤ N → P f :=
  by 
    intro f df 
    generalize hd : card f.support = c 
    revert f 
    induction' c with c hc
    ·
      intro f df f0 
      convert P_0 
      simpa only [support_eq_empty, card_eq_zero] using f0
    ·
      intro f df f0 
      rw [←erase_lead_add_C_mul_X_pow f]
      refine' P_C_add f.erase_lead _ (erase_lead_nat_degree_le.trans df) _ _ _
      ·
        exact (nat_degree_C_mul_X_pow_le f.leading_coeff f.nat_degree).trans df
      ·
        exact hc _ (erase_lead_nat_degree_le.trans df) (erase_lead_card_support f0)
      ·
        refine' P_C_mul_pow _ _ _ df 
        rw [Ne.def, leading_coeff_eq_zero]
        rintro rfl 
        exact not_le.mpr c.succ_pos f0.ge

end Polynomial

