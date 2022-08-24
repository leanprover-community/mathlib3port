/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Data.Polynomial.Degree.Definitions
import Mathbin.Tactic.ComputeDegree

/-!
# Cancel the leading terms of two polynomials

## Definition

* `cancel_leads p q`: the polynomial formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting.

## Main Results
The degree of `cancel_leads` is less than that of the larger of the two polynomials being cancelled.
Thus it is useful for induction or minimal-degree arguments.
-/


namespace Polynomial

noncomputable section

open Polynomial

variable {R : Type _}

section Ringₓ

variable [Ringₓ R] (p q : R[X])

/-- `cancel_leads p q` is formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting. -/
def cancelLeads : R[X] :=
  c p.leadingCoeff * X ^ (p.natDegree - q.natDegree) * q - c q.leadingCoeff * X ^ (q.natDegree - p.natDegree) * p

variable {p q}

@[simp]
theorem neg_cancel_leads : -p.cancelLeads q = q.cancelLeads p :=
  neg_sub _ _

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `compute_degree_le #[]
theorem nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree_of_comm
    (comm : p.leadingCoeff * q.leadingCoeff = q.leadingCoeff * p.leadingCoeff) (h : p.natDegree ≤ q.natDegree)
    (hq : 0 < q.natDegree) : (p.cancelLeads q).natDegree < q.natDegree := by
  by_cases' hp : p = 0
  · convert hq
    simp [hp, cancel_leads]
    
  rw [cancel_leads, sub_eq_add_neg, tsub_eq_zero_iff_le.mpr h, pow_zeroₓ, mul_oneₓ]
  by_cases' h0 : C p.leading_coeff * q + -(C q.leading_coeff * X ^ (q.nat_degree - p.nat_degree) * p) = 0
  · exact
      (le_of_eqₓ
            (by
              simp only [h0, nat_degree_zero])).trans_lt
        hq
    
  apply lt_of_le_of_neₓ
  · trace "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `compute_degree_le #[]"
    repeat'
      rwa [Nat.sub_add_cancelₓ]
    
  · contrapose! h0
    rw [← leading_coeff_eq_zero, leading_coeff, h0, mul_assoc, X_pow_mul, ← tsub_add_cancel_of_le h,
      add_commₓ _ p.nat_degree]
    simp only [coeff_mul_X_pow, coeff_neg, coeff_C_mul, add_tsub_cancel_left, coeff_add]
    rw [add_commₓ p.nat_degree, tsub_add_cancel_of_le h, ← leading_coeff, ← leading_coeff, comm, add_right_negₓ]
    

end Ringₓ

section CommRingₓ

variable [CommRingₓ R] {p q : R[X]}

theorem dvd_cancel_leads_of_dvd_of_dvd {r : R[X]} (pq : p ∣ q) (pr : p ∣ r) : p ∣ q.cancelLeads r :=
  dvd_sub (pr.trans (Dvd.intro_left _ rfl)) (pq.trans (Dvd.intro_left _ rfl))

theorem nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree (h : p.natDegree ≤ q.natDegree) (hq : 0 < q.natDegree) :
    (p.cancelLeads q).natDegree < q.natDegree :=
  nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree_of_comm (mul_comm _ _) h hq

end CommRingₓ

end Polynomial

