import Mathbin.Data.Real.Irrational 
import Mathbin.Data.Nat.Fib 
import Mathbin.Data.Fin.VecNotation 
import Mathbin.Tactic.RingExp 
import Mathbin.Algebra.LinearRecurrence

/-!
# The golden ratio and its conjugate

This file defines the golden ratio `φ := (1 + √5)/2` and its conjugate
`ψ := (1 - √5)/2`, which are the two real roots of `X² - X - 1`.

Along with various computational facts about them, we prove their
irrationality, and we link them to the Fibonacci sequence by proving
Binet's formula.
-/


noncomputable theory

/-- The golden ratio `φ := (1 + √5)/2`. -/
@[reducible]
def goldenRatio :=
  (1+Real.sqrt 5) / 2

/-- The conjugate of the golden ratio `ψ := (1 - √5)/2`. -/
@[reducible]
def goldenConj :=
  (1 - Real.sqrt 5) / 2

localized [Real] notation "φ" => goldenRatio

localized [Real] notation "ψ" => goldenConj

-- error in Data.Real.GoldenRatio: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inverse of the golden ratio is the opposite of its conjugate. -/
theorem inv_gold : «expr = »(«expr ⁻¹»(exprφ()), «expr- »(exprψ())) :=
begin
  have [] [":", expr «expr ≠ »(«expr + »(1, real.sqrt 5), 0)] [],
  from [expr ne_of_gt «expr $ »(add_pos (by norm_num [] []), real.sqrt_pos.mpr (by norm_num [] []))],
  field_simp [] ["[", expr sub_mul, ",", expr mul_add, "]"] [] [],
  norm_num [] []
end

/-- The opposite of the golden ratio is the inverse of its conjugate. -/
theorem inv_gold_conj : ψ⁻¹ = -φ :=
  by 
    rw [inv_eq_iff, ←neg_inv, neg_eq_iff_neg_eq]
    exact inv_gold.symm

@[simp]
theorem gold_mul_gold_conj : (φ*ψ) = -1 :=
  by 
    fieldSimp 
    rw [←sq_sub_sq]
    normNum

@[simp]
theorem gold_conj_mul_gold : (ψ*φ) = -1 :=
  by 
    rw [mul_commₓ]
    exact gold_mul_gold_conj

@[simp]
theorem gold_add_gold_conj : (φ+ψ) = 1 :=
  by 
    rw [goldenRatio, goldenConj]
    ring

theorem one_sub_gold_conj : 1 - φ = ψ :=
  by 
    linarith [gold_add_gold_conj]

theorem one_sub_gold : 1 - ψ = φ :=
  by 
    linarith [gold_add_gold_conj]

@[simp]
theorem gold_sub_gold_conj : φ - ψ = Real.sqrt 5 :=
  by 
    rw [goldenRatio, goldenConj]
    ring

@[simp]
theorem gold_sq : (φ^2) = φ+1 :=
  by 
    rw [goldenRatio, ←sub_eq_zero]
    ringExp 
    rw [Real.sq_sqrt] <;> normNum

@[simp]
theorem gold_conj_sq : (ψ^2) = ψ+1 :=
  by 
    rw [goldenConj, ←sub_eq_zero]
    ringExp 
    rw [Real.sq_sqrt] <;> normNum

theorem gold_pos : 0 < φ :=
  mul_pos
      (by 
        apply add_pos <;> normNum)$
    inv_pos.2 zero_lt_two

theorem gold_ne_zero : φ ≠ 0 :=
  ne_of_gtₓ gold_pos

theorem one_lt_gold : 1 < φ :=
  by 
    refine' lt_of_mul_lt_mul_left _ (le_of_ltₓ gold_pos)
    simp [←sq, gold_pos, zero_lt_one]

theorem gold_conj_neg : ψ < 0 :=
  by 
    linarith [one_sub_gold_conj, one_lt_gold]

theorem gold_conj_ne_zero : ψ ≠ 0 :=
  ne_of_ltₓ gold_conj_neg

theorem neg_one_lt_gold_conj : -1 < ψ :=
  by 
    rw [neg_lt, ←inv_gold]
    exact inv_lt_one one_lt_gold

/-!
## Irrationality
-/


-- error in Data.Real.GoldenRatio: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The golden ratio is irrational. -/ theorem gold_irrational : irrational exprφ() :=
begin
  have [] [] [":=", expr nat.prime.irrational_sqrt (show nat.prime 5, by norm_num [] [])],
  have [] [] [":=", expr this.rat_add 1],
  have [] [] [":=", expr this.rat_mul (show «expr ≠ »((1/2 : exprℚ()), 0), by norm_num [] [])],
  convert [] [expr this] [],
  field_simp [] [] [] []
end

-- error in Data.Real.GoldenRatio: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The conjugate of the golden ratio is irrational. -/ theorem gold_conj_irrational : irrational exprψ() :=
begin
  have [] [] [":=", expr nat.prime.irrational_sqrt (show nat.prime 5, by norm_num [] [])],
  have [] [] [":=", expr this.rat_sub 1],
  have [] [] [":=", expr this.rat_mul (show «expr ≠ »((1/2 : exprℚ()), 0), by norm_num [] [])],
  convert [] [expr this] [],
  field_simp [] [] [] []
end

/-!
## Links with Fibonacci sequence
-/


section Fibrec

variable {α : Type _} [CommSemiringₓ α]

-- error in Data.Real.GoldenRatio: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr![ , ]»
/-- The recurrence relation satisfied by the Fibonacci sequence. -/ def fib_rec : linear_recurrence α :=
{ order := 2, coeffs := «expr![ , ]»([1, 1]) }

section Poly

open Polynomial

/-- The characteristic polynomial of `fib_rec` is `X² - (X + 1)`. -/
theorem fib_rec_char_poly_eq {β : Type _} [CommRingₓ β] : fibRec.charPoly = (X^2) - X+(1 : Polynomial β) :=
  by 
    rw [fibRec, LinearRecurrence.charPoly]
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', monomial_eq_smul_X]

end Poly

/-- As expected, the Fibonacci sequence is a solution of `fib_rec`. -/
theorem fib_is_sol_fib_rec : fibRec.IsSolution (fun x => x.fib : ℕ → α) :=
  by 
    rw [fibRec]
    intro n 
    simp only 
    rw [Nat.fib_succ_succ, add_commₓ]
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ']

/-- The geometric sequence `λ n, φ^n` is a solution of `fib_rec`. -/
theorem geom_gold_is_sol_fib_rec : fibRec.IsSolution (pow φ) :=
  by 
    rw [fib_rec.geom_sol_iff_root_char_poly, fib_rec_char_poly_eq]
    simp [sub_eq_zero]

/-- The geometric sequence `λ n, ψ^n` is a solution of `fib_rec`. -/
theorem geom_gold_conj_is_sol_fib_rec : fibRec.IsSolution (pow ψ) :=
  by 
    rw [fib_rec.geom_sol_iff_root_char_poly, fib_rec_char_poly_eq]
    simp [sub_eq_zero]

end Fibrec

/-- Binet's formula as a function equality. -/
theorem Real.coe_fib_eq' : (fun n => Nat.fib n : ℕ → ℝ) = fun n => ((φ^n) - (ψ^n)) / Real.sqrt 5 :=
  by 
    rw [fib_rec.sol_eq_of_eq_init]
    ·
      intro i hi 
      finCases hi
      ·
        simp 
      ·
        simp only [goldenRatio, goldenConj]
        ringExp 
        rw [mul_inv_cancel] <;> normNum
    ·
      exact fib_is_sol_fib_rec
    ·
      ringNF 
      exact
        (@fibRec ℝ _).solSpace.sub_mem (Submodule.smul_mem fib_rec.sol_space (Real.sqrt 5⁻¹) geom_gold_is_sol_fib_rec)
          (Submodule.smul_mem fib_rec.sol_space (Real.sqrt 5⁻¹) geom_gold_conj_is_sol_fib_rec)

/-- Binet's formula as a dependent equality. -/
theorem Real.coe_fib_eq : ∀ n, (Nat.fib n : ℝ) = ((φ^n) - (ψ^n)) / Real.sqrt 5 :=
  by 
    rw [←Function.funext_iffₓ, Real.coe_fib_eq']

