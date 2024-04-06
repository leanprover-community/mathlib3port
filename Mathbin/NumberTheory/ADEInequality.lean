/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Data.Multiset.Sort
import Data.PNat.Interval
import Data.Rat.Order
import Data.PNat.Basic
import Tactic.NormNum
import Tactic.FieldSimp
import Tactic.IntervalCases

#align_import number_theory.ADE_inequality from "leanprover-community/mathlib"@"1ead22342e1a078bd44744ace999f85756555d35"

/-!
# The inequality `p⁻¹ + q⁻¹ + r⁻¹ > 1`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we classify solutions to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`, for positive natural numbers `p`, `q`, and `r`.

The solutions are exactly of the form.
* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`

This inequality shows up in Lie theory,
in the classification of Dynkin diagrams, root systems, and semisimple Lie algebras.

## Main declarations

* `pqr.A' q r`, the multiset `{1,q,r}`
* `pqr.D' r`, the multiset `{2,2,r}`
* `pqr.E6`, the multiset `{2,3,3}`
* `pqr.E7`, the multiset `{2,3,4}`
* `pqr.E8`, the multiset `{2,3,5}`
* `pqr.classification`, the classification of solutions to `p⁻¹ + q⁻¹ + r⁻¹ > 1`

-/


namespace ADEInequality

open Multiset

#print ADEInequality.A' /-
/-- `A' q r := {1,q,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`. -/
def A' (q r : ℕ+) : Multiset ℕ+ :=
  {1, q, r}
#align ADE_inequality.A' ADEInequality.A'
-/

#print ADEInequality.A /-
/-- `A r := {1,1,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $A_r$. -/
def A (r : ℕ+) : Multiset ℕ+ :=
  A' 1 r
#align ADE_inequality.A ADEInequality.A
-/

#print ADEInequality.D' /-
/-- `D' r := {2,2,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $D_{r+2}$. -/
def D' (r : ℕ+) : Multiset ℕ+ :=
  {2, 2, r}
#align ADE_inequality.D' ADEInequality.D'
-/

#print ADEInequality.E' /-
/-- `E' r := {2,3,r}` is a `multiset ℕ+`.
For `r ∈ {3,4,5}` is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $E_{r+3}$. -/
def E' (r : ℕ+) : Multiset ℕ+ :=
  {2, 3, r}
#align ADE_inequality.E' ADEInequality.E'
-/

#print ADEInequality.E6 /-
/-- `E6 := {2,3,3}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_6$. -/
def E6 : Multiset ℕ+ :=
  E' 3
#align ADE_inequality.E6 ADEInequality.E6
-/

#print ADEInequality.E7 /-
/-- `E7 := {2,3,4}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_7$. -/
def E7 : Multiset ℕ+ :=
  E' 4
#align ADE_inequality.E7 ADEInequality.E7
-/

#print ADEInequality.E8 /-
/-- `E8 := {2,3,5}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_8$. -/
def E8 : Multiset ℕ+ :=
  E' 5
#align ADE_inequality.E8 ADEInequality.E8
-/

#print ADEInequality.sumInv /-
/-- `sum_inv pqr` for a `pqr : multiset ℕ+` is the sum of the inverses
of the elements of `pqr`, as rational number.

The intended argument is a multiset `{p,q,r}` of cardinality `3`. -/
def sumInv (pqr : Multiset ℕ+) : ℚ :=
  Multiset.sum <| pqr.map fun x => x⁻¹
#align ADE_inequality.sum_inv ADEInequality.sumInv
-/

#print ADEInequality.sumInv_pqr /-
theorem sumInv_pqr (p q r : ℕ+) : sumInv {p, q, r} = p⁻¹ + q⁻¹ + r⁻¹ := by
  simp only [sum_inv, coe_coe, add_zero, insert_eq_cons, add_assoc, map_cons, sum_cons,
    map_singleton, sum_singleton]
#align ADE_inequality.sum_inv_pqr ADEInequality.sumInv_pqr
-/

#print ADEInequality.Admissible /-
/-- A multiset `pqr` of positive natural numbers is `admissible`
if it is equal to `A' q r`, or `D' r`, or one of `E6`, `E7`, or `E8`. -/
def Admissible (pqr : Multiset ℕ+) : Prop :=
  (∃ q r, A' q r = pqr) ∨ (∃ r, D' r = pqr) ∨ E' 3 = pqr ∨ E' 4 = pqr ∨ E' 5 = pqr
#align ADE_inequality.admissible ADEInequality.Admissible
-/

#print ADEInequality.admissible_A' /-
theorem admissible_A' (q r : ℕ+) : Admissible (A' q r) :=
  Or.inl ⟨q, r, rfl⟩
#align ADE_inequality.admissible_A' ADEInequality.admissible_A'
-/

#print ADEInequality.admissible_D' /-
theorem admissible_D' (n : ℕ+) : Admissible (D' n) :=
  Or.inr <| Or.inl ⟨n, rfl⟩
#align ADE_inequality.admissible_D' ADEInequality.admissible_D'
-/

#print ADEInequality.admissible_E'3 /-
theorem admissible_E'3 : Admissible (E' 3) :=
  Or.inr <| Or.inr <| Or.inl rfl
#align ADE_inequality.admissible_E'3 ADEInequality.admissible_E'3
-/

#print ADEInequality.admissible_E'4 /-
theorem admissible_E'4 : Admissible (E' 4) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inl rfl
#align ADE_inequality.admissible_E'4 ADEInequality.admissible_E'4
-/

#print ADEInequality.admissible_E'5 /-
theorem admissible_E'5 : Admissible (E' 5) :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr rfl
#align ADE_inequality.admissible_E'5 ADEInequality.admissible_E'5
-/

#print ADEInequality.admissible_E6 /-
theorem admissible_E6 : Admissible E6 :=
  admissible_E'3
#align ADE_inequality.admissible_E6 ADEInequality.admissible_E6
-/

#print ADEInequality.admissible_E7 /-
theorem admissible_E7 : Admissible E7 :=
  admissible_E'4
#align ADE_inequality.admissible_E7 ADEInequality.admissible_E7
-/

#print ADEInequality.admissible_E8 /-
theorem admissible_E8 : Admissible E8 :=
  admissible_E'5
#align ADE_inequality.admissible_E8 ADEInequality.admissible_E8
-/

#print ADEInequality.Admissible.one_lt_sumInv /-
theorem Admissible.one_lt_sumInv {pqr : Multiset ℕ+} : Admissible pqr → 1 < sumInv pqr :=
  by
  rw [admissible]
  rintro (⟨p', q', H⟩ | ⟨n, H⟩ | H | H | H)
  · rw [← H, A', sum_inv_pqr, add_assoc]
    simp only [lt_add_iff_pos_right, PNat.one_coe, inv_one, Nat.cast_one, coe_coe]
    apply add_pos <;> simp only [PNat.pos, Nat.cast_pos, inv_pos]
  · rw [← H, D', sum_inv_pqr]
    simp only [lt_add_iff_pos_right, PNat.one_coe, inv_one, Nat.cast_one, coe_coe, PNat.coe_bit0,
      Nat.cast_bit0]
    norm_num
  all_goals rw [← H, E', sum_inv_pqr]; norm_num
#align ADE_inequality.admissible.one_lt_sum_inv ADEInequality.Admissible.one_lt_sumInv
-/

#print ADEInequality.lt_three /-
theorem lt_three {p q r : ℕ+} (hpq : p ≤ q) (hqr : q ≤ r) (H : 1 < sumInv {p, q, r}) : p < 3 :=
  by
  have h3 : (0 : ℚ) < 3 := by norm_num
  contrapose! H; rw [sum_inv_pqr]
  have h3q := H.trans hpq
  have h3r := h3q.trans hqr
  calc
    (p⁻¹ + q⁻¹ + r⁻¹ : ℚ) ≤ 3⁻¹ + 3⁻¹ + 3⁻¹ := add_le_add (add_le_add _ _) _
    _ = 1 := by norm_num
  all_goals rw [inv_le_inv _ h3] <;> [assumption_mod_cast; norm_num]
#align ADE_inequality.lt_three ADEInequality.lt_three
-/

#print ADEInequality.lt_four /-
theorem lt_four {q r : ℕ+} (hqr : q ≤ r) (H : 1 < sumInv {2, q, r}) : q < 4 :=
  by
  have h4 : (0 : ℚ) < 4 := by norm_num
  contrapose! H; rw [sum_inv_pqr]
  have h4r := H.trans hqr
  simp only [PNat.coe_bit0, Nat.cast_bit0, PNat.one_coe, Nat.cast_one, coe_coe]
  calc
    (2⁻¹ + q⁻¹ + r⁻¹ : ℚ) ≤ 2⁻¹ + 4⁻¹ + 4⁻¹ := add_le_add (add_le_add le_rfl _) _
    _ = 1 := by norm_num
  all_goals rw [inv_le_inv _ h4] <;> [assumption_mod_cast; norm_num]
#align ADE_inequality.lt_four ADEInequality.lt_four
-/

#print ADEInequality.lt_six /-
theorem lt_six {r : ℕ+} (H : 1 < sumInv {2, 3, r}) : r < 6 :=
  by
  have h6 : (0 : ℚ) < 6 := by norm_num
  contrapose! H; rw [sum_inv_pqr]
  simp only [PNat.coe_bit0, Nat.cast_bit0, PNat.one_coe, Nat.cast_bit1, Nat.cast_one, PNat.coe_bit1,
    coe_coe]
  calc
    (2⁻¹ + 3⁻¹ + r⁻¹ : ℚ) ≤ 2⁻¹ + 3⁻¹ + 6⁻¹ := add_le_add (add_le_add le_rfl le_rfl) _
    _ = 1 := by norm_num
  rw [inv_le_inv _ h6] <;> [assumption_mod_cast; norm_num]
#align ADE_inequality.lt_six ADEInequality.lt_six
-/

#print ADEInequality.admissible_of_one_lt_sumInv_aux' /-
theorem admissible_of_one_lt_sumInv_aux' {p q r : ℕ+} (hpq : p ≤ q) (hqr : q ≤ r)
    (H : 1 < sumInv {p, q, r}) : Admissible {p, q, r} :=
  by
  have hp3 : p < 3 := lt_three hpq hqr H
  interval_cases
  · exact admissible_A' q r
  have hq4 : q < 4 := lt_four hqr H
  interval_cases
  · exact admissible_D' r
  have hr6 : r < 6 := lt_six H
  interval_cases
  · exact admissible_E6
  · exact admissible_E7
  · exact admissible_E8
#align ADE_inequality.admissible_of_one_lt_sum_inv_aux' ADEInequality.admissible_of_one_lt_sumInv_aux'
-/

#print ADEInequality.admissible_of_one_lt_sumInv_aux /-
theorem admissible_of_one_lt_sumInv_aux :
    ∀ {pqr : List ℕ+} (hs : pqr.Sorted (· ≤ ·)) (hl : pqr.length = 3) (H : 1 < sumInv pqr),
      Admissible pqr
  | [p, q, r], hs, hl, H =>
    by
    obtain ⟨⟨hpq, -⟩, hqr⟩ : (p ≤ q ∧ p ≤ r) ∧ q ≤ r
    simpa using hs
    exact admissible_of_one_lt_sum_inv_aux' hpq hqr H
#align ADE_inequality.admissible_of_one_lt_sum_inv_aux ADEInequality.admissible_of_one_lt_sumInv_aux
-/

#print ADEInequality.admissible_of_one_lt_sumInv /-
theorem admissible_of_one_lt_sumInv {p q r : ℕ+} (H : 1 < sumInv {p, q, r}) :
    Admissible {p, q, r} := by
  simp only [admissible]
  let S := sort ((· ≤ ·) : ℕ+ → ℕ+ → Prop) {p, q, r}
  have hS : S.sorted (· ≤ ·) := sort_sorted _ _
  have hpqr : ({p, q, r} : Multiset ℕ+) = S := (sort_eq LE.le {p, q, r}).symm
  simp only [hpqr] at *
  apply admissible_of_one_lt_sum_inv_aux hS _ H
  simp only [S, length_sort]
  decide
#align ADE_inequality.admissible_of_one_lt_sum_inv ADEInequality.admissible_of_one_lt_sumInv
-/

#print ADEInequality.classification /-
/-- A multiset `{p,q,r}` of positive natural numbers
is a solution to `(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1` if and only if
it is `admissible` which means it is one of:

* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`
-/
theorem classification (p q r : ℕ+) : 1 < sumInv {p, q, r} ↔ Admissible {p, q, r} :=
  ⟨admissible_of_one_lt_sumInv, Admissible.one_lt_sumInv⟩
#align ADE_inequality.classification ADEInequality.classification
-/

end ADEInequality

