/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module data.polynomial.cancel_leads
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Degree.Definitions
import Mathbin.Tactic.ComputeDegree
import Mathbin.Data.Polynomial.Degree.Lemmas

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

section Ring

variable [Ring R] (p q : R[X])

/-- `cancel_leads p q` is formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting. -/
def cancelLeads : R[X] :=
  c p.leadingCoeff * x ^ (p.natDegree - q.natDegree) * q -
    c q.leadingCoeff * x ^ (q.natDegree - p.natDegree) * p
#align polynomial.cancel_leads Polynomial.cancelLeads

variable {p q}

@[simp]
theorem neg_cancelLeads : -p.cancelLeads q = q.cancelLeads p :=
  neg_sub _ _
#align polynomial.neg_cancel_leads Polynomial.neg_cancelLeads

theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm
    (comm : p.leadingCoeff * q.leadingCoeff = q.leadingCoeff * p.leadingCoeff)
    (h : p.natDegree ≤ q.natDegree) (hq : 0 < q.natDegree) :
    (p.cancelLeads q).natDegree < q.natDegree :=
  by
  by_cases hp : p = 0
  · convert hq
    simp [hp, cancel_leads]
  rw [cancel_leads, sub_eq_add_neg, tsub_eq_zero_iff_le.mpr h, pow_zero, mul_one]
  by_cases h0 :
    C p.leading_coeff * q + -(C q.leading_coeff * X ^ (q.nat_degree - p.nat_degree) * p) = 0
  · exact (le_of_eq (by simp only [h0, nat_degree_zero])).trans_lt hq
  apply lt_of_le_of_ne
  · compute_degree_le
    repeat' rwa [Nat.sub_add_cancel]
  · contrapose! h0
    rw [← leading_coeff_eq_zero, leading_coeff, h0, mul_assoc, X_pow_mul, ← tsub_add_cancel_of_le h,
      add_comm _ p.nat_degree]
    simp only [coeff_mul_X_pow, coeff_neg, coeff_C_mul, add_tsub_cancel_left, coeff_add]
    rw [add_comm p.nat_degree, tsub_add_cancel_of_le h, ← leading_coeff, ← leading_coeff, comm,
      add_right_neg]
#align polynomial.nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree_of_comm Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm

end Ring

section CommRing

variable [CommRing R] {p q : R[X]}

theorem dvd_cancelLeads_of_dvd_of_dvd {r : R[X]} (pq : p ∣ q) (pr : p ∣ r) : p ∣ q.cancelLeads r :=
  dvd_sub (pr.trans (Dvd.intro_left _ rfl)) (pq.trans (Dvd.intro_left _ rfl))
#align polynomial.dvd_cancel_leads_of_dvd_of_dvd Polynomial.dvd_cancelLeads_of_dvd_of_dvd

theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree (h : p.natDegree ≤ q.natDegree)
    (hq : 0 < q.natDegree) : (p.cancelLeads q).natDegree < q.natDegree :=
  natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm (mul_comm _ _) h hq
#align polynomial.nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree

end CommRing

end Polynomial

