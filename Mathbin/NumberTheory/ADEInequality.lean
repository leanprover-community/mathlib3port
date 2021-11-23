import Mathbin.Data.Multiset.Sort 
import Mathbin.Data.Pnat.Interval 
import Mathbin.Data.Rat.Order 
import Mathbin.Tactic.NormNum 
import Mathbin.Tactic.FieldSimp 
import Mathbin.Tactic.IntervalCases

/-!
# The inequality `p⁻¹ + q⁻¹ + r⁻¹ > 1`

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

/-- `A' q r := {1,q,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`. -/
def A' (q r : ℕ+) : Multiset ℕ+ :=
  {1, q, r}

/-- `A r := {1,1,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $A_r$. -/
def A (r : ℕ+) : Multiset ℕ+ :=
  A' 1 r

/-- `D' r := {2,2,r}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $D_{r+2}$. -/
def D' (r : ℕ+) : Multiset ℕ+ :=
  {2, 2, r}

/-- `E' r := {2,3,r}` is a `multiset ℕ+`.
For `r ∈ {3,4,5}` is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

These solutions are related to the Dynkin diagrams $E_{r+3}$. -/
def E' (r : ℕ+) : Multiset ℕ+ :=
  {2, 3, r}

/-- `E6 := {2,3,3}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_6$. -/
def E6 : Multiset ℕ+ :=
  E' 3

/-- `E7 := {2,3,4}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_7$. -/
def E7 : Multiset ℕ+ :=
  E' 4

/-- `E8 := {2,3,5}` is a `multiset ℕ+`
that is a solution to the inequality
`(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1`.

This solution is related to the Dynkin diagrams $E_8$. -/
def E8 : Multiset ℕ+ :=
  E' 5

/-- `sum_inv pqr` for a `pqr : multiset ℕ+` is the sum of the inverses
of the elements of `pqr`, as rational number.

The intended argument is a multiset `{p,q,r}` of cardinality `3`. -/
def sum_inv (pqr : Multiset ℕ+) : ℚ :=
  Multiset.sum$ pqr.map$ fun x => x⁻¹

theorem sum_inv_pqr (p q r : ℕ+) : sum_inv {p, q, r} = (p⁻¹+q⁻¹)+r⁻¹ :=
  by 
    simp only [sum_inv, coe_coe, add_zeroₓ, insert_eq_cons, add_assocₓ, map_cons, sum_cons, map_singleton,
      sum_singleton]

/-- A multiset `pqr` of positive natural numbers is `admissible`
if it is equal to `A' q r`, or `D' r`, or one of `E6`, `E7`, or `E8`. -/
def admissible (pqr : Multiset ℕ+) : Prop :=
  (∃ q r, A' q r = pqr) ∨ (∃ r, D' r = pqr) ∨ E' 3 = pqr ∨ E' 4 = pqr ∨ E' 5 = pqr

theorem admissible_A' (q r : ℕ+) : admissible (A' q r) :=
  Or.inl ⟨q, r, rfl⟩

theorem admissible_D' (n : ℕ+) : admissible (D' n) :=
  Or.inr$ Or.inl ⟨n, rfl⟩

theorem admissible_E'3 : admissible (E' 3) :=
  Or.inr$ Or.inr$ Or.inl rfl

theorem admissible_E'4 : admissible (E' 4) :=
  Or.inr$ Or.inr$ Or.inr$ Or.inl rfl

theorem admissible_E'5 : admissible (E' 5) :=
  Or.inr$ Or.inr$ Or.inr$ Or.inr rfl

theorem admissible_E6 : admissible E6 :=
  admissible_E'3

theorem admissible_E7 : admissible E7 :=
  admissible_E'4

theorem admissible_E8 : admissible E8 :=
  admissible_E'5

theorem admissible.one_lt_sum_inv {pqr : Multiset ℕ+} : admissible pqr → 1 < sum_inv pqr :=
  by 
    rw [admissible]
    rintro (⟨p', q', H⟩ | ⟨n, H⟩ | H | H | H)
    ·
      rw [←H, A', sum_inv_pqr, add_assocₓ]
      simp only [lt_add_iff_pos_right, Pnat.one_coe, inv_one, Nat.cast_one, coe_coe]
      apply add_pos <;> simp only [Pnat.pos, Nat.cast_pos, inv_pos]
    ·
      rw [←H, D', sum_inv_pqr]
      simp only [lt_add_iff_pos_right, Pnat.one_coe, inv_one, Nat.cast_one, coe_coe, Pnat.coe_bit0, Nat.cast_bit0]
      normNum 
    all_goals 
      rw [←H, E', sum_inv_pqr]
      normNum

-- error in NumberTheory.ADEInequality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_three
{p q r : «exprℕ+»()}
(hpq : «expr ≤ »(p, q))
(hqr : «expr ≤ »(q, r))
(H : «expr < »(1, sum_inv {p, q, r})) : «expr < »(p, 3) :=
begin
  have [ident h3] [":", expr «expr < »((0 : exprℚ()), 3)] [],
  by norm_num [] [],
  contrapose ["!"] [ident H],
  rw [expr sum_inv_pqr] [],
  have [ident h3q] [] [":=", expr H.trans hpq],
  have [ident h3r] [] [":=", expr h3q.trans hqr],
  calc
    «expr ≤ »((«expr + »(«expr + »(«expr ⁻¹»(p), «expr ⁻¹»(q)), «expr ⁻¹»(r)) : exprℚ()), «expr + »(«expr + »(«expr ⁻¹»(3), «expr ⁻¹»(3)), «expr ⁻¹»(3))) : add_le_add (add_le_add _ _) _
    «expr = »(..., 1) : by norm_num [] [],
  all_goals { rw [expr inv_le_inv _ h3] []; [assumption_mod_cast, norm_num [] []] }
end

-- error in NumberTheory.ADEInequality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_four {q r : «exprℕ+»()} (hqr : «expr ≤ »(q, r)) (H : «expr < »(1, sum_inv {2, q, r})) : «expr < »(q, 4) :=
begin
  have [ident h4] [":", expr «expr < »((0 : exprℚ()), 4)] [],
  by norm_num [] [],
  contrapose ["!"] [ident H],
  rw [expr sum_inv_pqr] [],
  have [ident h4r] [] [":=", expr H.trans hqr],
  simp [] [] ["only"] ["[", expr pnat.coe_bit0, ",", expr nat.cast_bit0, ",", expr pnat.one_coe, ",", expr nat.cast_one, ",", expr coe_coe, "]"] [] [],
  calc
    «expr ≤ »((«expr + »(«expr + »(«expr ⁻¹»(2), «expr ⁻¹»(q)), «expr ⁻¹»(r)) : exprℚ()), «expr + »(«expr + »(«expr ⁻¹»(2), «expr ⁻¹»(4)), «expr ⁻¹»(4))) : add_le_add (add_le_add le_rfl _) _
    «expr = »(..., 1) : by norm_num [] [],
  all_goals { rw [expr inv_le_inv _ h4] []; [assumption_mod_cast, norm_num [] []] }
end

-- error in NumberTheory.ADEInequality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_six {r : «exprℕ+»()} (H : «expr < »(1, sum_inv {2, 3, r})) : «expr < »(r, 6) :=
begin
  have [ident h6] [":", expr «expr < »((0 : exprℚ()), 6)] [],
  by norm_num [] [],
  contrapose ["!"] [ident H],
  rw [expr sum_inv_pqr] [],
  simp [] [] ["only"] ["[", expr pnat.coe_bit0, ",", expr nat.cast_bit0, ",", expr pnat.one_coe, ",", expr nat.cast_bit1, ",", expr nat.cast_one, ",", expr pnat.coe_bit1, ",", expr coe_coe, "]"] [] [],
  calc
    «expr ≤ »((«expr + »(«expr + »(«expr ⁻¹»(2), «expr ⁻¹»(3)), «expr ⁻¹»(r)) : exprℚ()), «expr + »(«expr + »(«expr ⁻¹»(2), «expr ⁻¹»(3)), «expr ⁻¹»(6))) : add_le_add (add_le_add le_rfl le_rfl) _
    «expr = »(..., 1) : by norm_num [] [],
  rw [expr inv_le_inv _ h6] []; [assumption_mod_cast, norm_num [] []]
end

-- error in NumberTheory.ADEInequality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem admissible_of_one_lt_sum_inv_aux'
{p q r : «exprℕ+»()}
(hpq : «expr ≤ »(p, q))
(hqr : «expr ≤ »(q, r))
(H : «expr < »(1, sum_inv {p, q, r})) : admissible {p, q, r} :=
begin
  have [ident hp3] [":", expr «expr < »(p, 3)] [":=", expr lt_three hpq hqr H],
  interval_cases [expr p] [] [],
  { exact [expr admissible_A' q r] },
  have [ident hq4] [":", expr «expr < »(q, 4)] [":=", expr lt_four hqr H],
  interval_cases [expr q] [] [],
  { exact [expr admissible_D' r] },
  have [ident hr6] [":", expr «expr < »(r, 6)] [":=", expr lt_six H],
  interval_cases [expr r] [] [],
  { exact [expr admissible_E6] },
  { exact [expr admissible_E7] },
  { exact [expr admissible_E8] }
end

theorem admissible_of_one_lt_sum_inv_aux :
  ∀ {pqr : List ℕ+} hs : pqr.sorted (· ≤ ·) hl : pqr.length = 3 H : 1 < sum_inv pqr, admissible pqr
| [p, q, r], hs, hl, H =>
  by 
    obtain ⟨⟨hpq, -⟩, hqr⟩ : (p ≤ q ∧ p ≤ r) ∧ q ≤ r 
    simpa using hs 
    exact admissible_of_one_lt_sum_inv_aux' hpq hqr H

-- error in NumberTheory.ADEInequality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem admissible_of_one_lt_sum_inv
{p q r : «exprℕ+»()}
(H : «expr < »(1, sum_inv {p, q, r})) : admissible {p, q, r} :=
begin
  simp [] [] ["only"] ["[", expr admissible, "]"] [] [],
  let [ident S] [] [":=", expr sort ((«expr ≤ ») : «exprℕ+»() → «exprℕ+»() → exprProp()) {p, q, r}],
  have [ident hS] [":", expr S.sorted ((«expr ≤ »))] [":=", expr sort_sorted _ _],
  have [ident hpqr] [":", expr «expr = »(({p, q, r} : multiset «exprℕ+»()), S)] [":=", expr (sort_eq has_le.le {p, q, r}).symm],
  simp [] [] ["only"] ["[", expr hpqr, "]"] [] ["at", "*"],
  apply [expr admissible_of_one_lt_sum_inv_aux hS _ H],
  simp [] [] ["only"] ["[", expr S, ",", expr length_sort, "]"] [] [],
  dec_trivial []
end

/-- A multiset `{p,q,r}` of positive natural numbers
is a solution to `(p⁻¹ + q⁻¹ + r⁻¹ : ℚ) > 1` if and only if
it is `admissible` which means it is one of:

* `A' q r := {1,q,r}`
* `D' r := {2,2,r}`
* `E6 := {2,3,3}`, or `E7 := {2,3,4}`, or `E8 := {2,3,5}`
-/
theorem classification (p q r : ℕ+) : 1 < sum_inv {p, q, r} ↔ admissible {p, q, r} :=
  ⟨admissible_of_one_lt_sum_inv, admissible.one_lt_sum_inv⟩

end ADEInequality

