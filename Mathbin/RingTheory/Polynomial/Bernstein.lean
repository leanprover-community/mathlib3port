import Mathbin.Data.Polynomial.Derivative 
import Mathbin.Data.Nat.Choose.Sum 
import Mathbin.RingTheory.Polynomial.Pochhammer 
import Mathbin.Data.Polynomial.AlgebraMap 
import Mathbin.LinearAlgebra.LinearIndependent 
import Mathbin.Data.MvPolynomial.Pderiv

/-!
# Bernstein polynomials

The definition of the Bernstein polynomials
```
bernstein_polynomial (R : Type*) [comm_ring R] (n ν : ℕ) : polynomial R :=
(choose n ν) * X^ν * (1 - X)^(n - ν)
```
and the fact that for `ν : fin (n+1)` these are linearly independent over `ℚ`.

We prove the basic identities
* `(finset.range (n + 1)).sum (λ ν, bernstein_polynomial R n ν) = 1`
* `(finset.range (n + 1)).sum (λ ν, ν • bernstein_polynomial R n ν) = n • X`
* `(finset.range (n + 1)).sum (λ ν, (ν * (ν-1)) • bernstein_polynomial R n ν) = (n * (n-1)) • X^2`

## Notes

See also `analysis.special_functions.bernstein`, which defines the Bernstein approximations
of a continuous function `f : C([0,1], ℝ)`, and shows that these converge uniformly to `f`.
-/


noncomputable theory

open nat(choose)

open polynomial(x)

variable(R : Type _)[CommRingₓ R]

/--
`bernstein_polynomial R n ν` is `(choose n ν) * X^ν * (1 - X)^(n - ν)`.

Although the coefficients are integers, it is convenient to work over an arbitrary commutative ring.
-/
def bernsteinPolynomial (n ν : ℕ) : Polynomial R :=
  (choose n ν*X^ν)*1 - X^n - ν

example  : bernsteinPolynomial ℤ 3 2 = (3*X^2) - 3*X^3 :=
  by 
    normNum [bernsteinPolynomial, choose]
    ring

namespace bernsteinPolynomial

theorem eq_zero_of_lt {n ν : ℕ} (h : n < ν) : bernsteinPolynomial R n ν = 0 :=
  by 
    simp [bernsteinPolynomial, Nat.choose_eq_zero_of_lt h]

section 

variable{R}{S : Type _}[CommRingₓ S]

@[simp]
theorem map (f : R →+* S) (n ν : ℕ) : (bernsteinPolynomial R n ν).map f = bernsteinPolynomial S n ν :=
  by 
    simp [bernsteinPolynomial]

end 

theorem flip (n ν : ℕ) (h : ν ≤ n) : (bernsteinPolynomial R n ν).comp (1 - X) = bernsteinPolynomial R n (n - ν) :=
  by 
    dsimp [bernsteinPolynomial]
    simp [h, tsub_tsub_assoc, mul_right_commₓ]

theorem flip' (n ν : ℕ) (h : ν ≤ n) : bernsteinPolynomial R n ν = (bernsteinPolynomial R n (n - ν)).comp (1 - X) :=
  by 
    rw [←flip _ _ _ h, Polynomial.comp_assoc]
    simp 

theorem eval_at_0 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 0 = if ν = 0 then 1 else 0 :=
  by 
    dsimp [bernsteinPolynomial]
    splitIfs
    ·
      subst h 
      simp 
    ·
      simp [zero_pow (Nat.pos_of_ne_zeroₓ h)]

theorem eval_at_1 (n ν : ℕ) : (bernsteinPolynomial R n ν).eval 1 = if ν = n then 1 else 0 :=
  by 
    dsimp [bernsteinPolynomial]
    splitIfs
    ·
      subst h 
      simp 
    ·
      obtain w | w := (n - ν).eq_zero_or_pos
      ·
        simp [Nat.choose_eq_zero_of_lt ((tsub_eq_zero_iff_le.mp w).lt_of_ne (Ne.symm h))]
      ·
        simp [zero_pow w]

theorem derivative_succ_aux (n ν : ℕ) :
  (bernsteinPolynomial R (n+1) (ν+1)).derivative = (n+1)*bernsteinPolynomial R n ν - bernsteinPolynomial R n (ν+1) :=
  by 
    dsimp [bernsteinPolynomial]
    suffices  :
      (((«expr↑ » ((n+1).choose (ν+1))*(«expr↑ » ν+1)*X^ν)*1 - X^n - ν) -
          («expr↑ » ((n+1).choose (ν+1))*X^ν+1)*«expr↑ » (n - ν)*1 - X^n - ν - 1) =
        («expr↑ » n+1)*((«expr↑ » (n.choose ν)*X^ν)*1 - X^n - ν) - («expr↑ » (n.choose (ν+1))*X^ν+1)*1 - X^n - ν+1
    ·
      simpa [Polynomial.derivative_pow, ←sub_eq_add_neg]
    convRHS => rw [mul_sub]
    refine' congr (congr_argₓ Sub.sub _) _
    ·
      simp only [←mul_assocₓ]
      refine' congr (congr_argₓ (·*·) (congr (congr_argₓ (·*·) _) rfl)) rfl 
      exactModCast congr_argₓ (fun m : ℕ => (m : Polynomial R)) (Nat.succ_mul_choose_eq n ν).symm
    ·
      rw [←tsub_add_eq_tsub_tsub, ←mul_assocₓ, ←mul_assocₓ]
      congr 1
      rw [mul_commₓ]
      rw [←mul_assocₓ, ←mul_assocₓ]
      congr 1
      normCast 
      congr 1
      convert (Nat.choose_mul_succ_eq n (ν+1)).symm using 1
      ·
        convert mul_commₓ _ _ using 2
        simp 
      ·
        apply mul_commₓ

theorem derivative_succ (n ν : ℕ) :
  (bernsteinPolynomial R n (ν+1)).derivative =
    n*bernsteinPolynomial R (n - 1) ν - bernsteinPolynomial R (n - 1) (ν+1) :=
  by 
    cases n
    ·
      simp [bernsteinPolynomial]
    ·
      apply derivative_succ_aux

theorem derivative_zero (n : ℕ) : (bernsteinPolynomial R n 0).derivative = (-n)*bernsteinPolynomial R (n - 1) 0 :=
  by 
    dsimp [bernsteinPolynomial]
    simp [Polynomial.derivative_pow]

theorem iterate_derivative_at_0_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
  k < ν → ((Polynomial.derivative^[k]) (bernsteinPolynomial R n ν)).eval 0 = 0 :=
  by 
    cases ν
    ·
      rintro ⟨⟩
    ·
      rw [Nat.lt_succ_iff]
      induction' k with k ih generalizing n ν
      ·
        simp [eval_at_0]
      ·
        simp only [derivative_succ, Int.coe_nat_eq_zero, Int.nat_cast_eq_coe_nat, mul_eq_zero, Function.comp_app,
          Function.iterate_succ, Polynomial.iterate_derivative_sub, Polynomial.iterate_derivative_cast_nat_mul,
          Polynomial.eval_mul, Polynomial.eval_nat_cast, Polynomial.eval_sub]
        intro h 
        apply mul_eq_zero_of_right 
        rw [ih _ _ (Nat.le_of_succ_leₓ h), sub_zero]
        convert ih _ _ (Nat.pred_le_predₓ h)
        exact (Nat.succ_pred_eq_of_posₓ (k.succ_pos.trans_le h)).symm

@[simp]
theorem iterate_derivative_succ_at_0_eq_zero (n ν : ℕ) :
  ((Polynomial.derivative^[ν]) (bernsteinPolynomial R n (ν+1))).eval 0 = 0 :=
  iterate_derivative_at_0_eq_zero_of_lt R n (lt_add_one ν)

open Polynomial

-- error in RingTheory.Polynomial.Bernstein: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem iterate_derivative_at_0
(n
 ν : exprℕ()) : «expr = »((«expr ^[ ]»(polynomial.derivative, ν) (bernstein_polynomial R n ν)).eval 0, (pochhammer R ν).eval («expr - »(n, «expr - »(ν, 1)) : exprℕ())) :=
begin
  by_cases [expr h, ":", expr «expr ≤ »(ν, n)],
  { induction [expr ν] [] ["with", ident ν, ident ih] ["generalizing", ident n, ident h],
    { simp [] [] [] ["[", expr eval_at_0, "]"] [] [] },
    { have [ident h'] [":", expr «expr ≤ »(ν, «expr - »(n, 1))] [":=", expr le_tsub_of_add_le_right h],
      simp [] [] ["only"] ["[", expr derivative_succ, ",", expr ih «expr - »(n, 1) h', ",", expr iterate_derivative_succ_at_0_eq_zero, ",", expr nat.succ_sub_succ_eq_sub, ",", expr tsub_zero, ",", expr sub_zero, ",", expr iterate_derivative_sub, ",", expr iterate_derivative_cast_nat_mul, ",", expr eval_one, ",", expr eval_mul, ",", expr eval_add, ",", expr eval_sub, ",", expr eval_X, ",", expr eval_comp, ",", expr eval_nat_cast, ",", expr function.comp_app, ",", expr function.iterate_succ, ",", expr pochhammer_succ_left, "]"] [] [],
      obtain [ident rfl, "|", ident h'', ":=", expr ν.eq_zero_or_pos],
      { simp [] [] [] [] [] [] },
      { have [] [":", expr «expr = »(«expr - »(«expr - »(n, 1), «expr - »(ν, 1)), «expr - »(n, ν))] [],
        { rw ["<-", expr nat.succ_le_iff] ["at", ident h''],
          rw ["[", "<-", expr tsub_add_eq_tsub_tsub, ",", expr add_comm, ",", expr tsub_add_cancel_of_le h'', "]"] [] },
        rw ["[", expr this, ",", expr pochhammer_eval_succ, "]"] [],
        rw_mod_cast [expr tsub_add_cancel_of_le (h'.trans n.pred_le)] [] } } },
  { simp [] [] ["only"] ["[", expr not_le, "]"] [] ["at", ident h],
    rw ["[", expr tsub_eq_zero_iff_le.mpr (nat.le_pred_of_lt h), ",", expr eq_zero_of_lt R h, "]"] [],
    simp [] [] [] ["[", expr pos_iff_ne_zero.mp (pos_of_gt h), "]"] [] [] }
end

theorem iterate_derivative_at_0_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
  ((Polynomial.derivative^[ν]) (bernsteinPolynomial R n ν)).eval 0 ≠ 0 :=
  by 
    simp only [Int.coe_nat_eq_zero, bernsteinPolynomial.iterate_derivative_at_0, Ne.def, Nat.cast_eq_zero]
    simp only [←pochhammer_eval_cast]
    normCast 
    apply ne_of_gtₓ 
    obtain rfl | h' := Nat.eq_zero_or_posₓ ν
    ·
      simp 
    ·
      rw [←Nat.succ_pred_eq_of_posₓ h'] at h 
      exact pochhammer_pos _ _ (tsub_pos_of_lt (Nat.lt_of_succ_leₓ h))

/-!
Rather than redoing the work of evaluating the derivatives at 1,
we use the symmetry of the Bernstein polynomials.
-/


theorem iterate_derivative_at_1_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
  k < n - ν → ((Polynomial.derivative^[k]) (bernsteinPolynomial R n ν)).eval 1 = 0 :=
  by 
    intro w 
    rw [flip' _ _ _ (tsub_pos_iff_lt.mp (pos_of_gt w)).le]
    simp [Polynomial.eval_comp, iterate_derivative_at_0_eq_zero_of_lt R n w]

@[simp]
theorem iterate_derivative_at_1 (n ν : ℕ) (h : ν ≤ n) :
  ((Polynomial.derivative^[n - ν]) (bernsteinPolynomial R n ν)).eval 1 = (-1^n - ν)*(pochhammer R (n - ν)).eval (ν+1) :=
  by 
    rw [flip' _ _ _ h]
    simp [Polynomial.eval_comp, h]
    obtain rfl | h' := h.eq_or_lt
    ·
      simp 
    ·
      congr 
      normCast 
      rw [←tsub_add_eq_tsub_tsub, tsub_tsub_cancel_of_le (nat.succ_le_iff.mpr h')]

theorem iterate_derivative_at_1_ne_zero [CharZero R] (n ν : ℕ) (h : ν ≤ n) :
  ((Polynomial.derivative^[n - ν]) (bernsteinPolynomial R n ν)).eval 1 ≠ 0 :=
  by 
    rw [bernsteinPolynomial.iterate_derivative_at_1 _ _ _ h, Ne.def, neg_one_pow_mul_eq_zero_iff, ←Nat.cast_succ,
      ←pochhammer_eval_cast, ←Nat.cast_zero, Nat.cast_inj]
    exact (pochhammer_pos _ _ (Nat.succ_posₓ ν)).ne'

open Submodule

theorem linear_independent_aux (n k : ℕ) (h : k ≤ n+1) :
  LinearIndependent ℚ fun ν : Finₓ k => bernsteinPolynomial ℚ n ν :=
  by 
    induction' k with k ih
    ·
      apply linear_independent_empty_type
    ·
      apply linear_independent_fin_succ'.mpr 
      fsplit
      ·
        exact ih (le_of_ltₓ h)
      ·
        clear ih 
        simp only [Nat.succ_eq_add_one, add_le_add_iff_right] at h 
        simp only [Finₓ.coe_last, Finₓ.init_def]
        dsimp 
        apply not_mem_span_of_apply_not_mem_span_image (Polynomial.derivativeLhom ℚ^n - k)
        simp only [not_exists, not_and, Submodule.mem_map, Submodule.span_image]
        intro p m 
        applyFun Polynomial.eval (1 : ℚ)
        simp only [Polynomial.derivative_lhom_coe, LinearMap.pow_apply]
        suffices  : ((Polynomial.derivative^[n - k]) p).eval 1 = 0
        ·
          rw [this]
          exact (iterate_derivative_at_1_ne_zero ℚ n k h).symm 
        apply span_induction m
        ·
          simp 
          rintro ⟨a, w⟩
          simp only [Finₓ.coe_mk]
          rw [iterate_derivative_at_1_eq_zero_of_lt ℚ n ((tsub_lt_tsub_iff_left_of_le h).mpr w)]
        ·
          simp 
        ·
          intro x y hx hy 
          simp [hx, hy]
        ·
          intro a x h 
          simp [h]

/--
The Bernstein polynomials are linearly independent.

We prove by induction that the collection of `bernstein_polynomial n ν` for `ν = 0, ..., k`
are linearly independent.
The inductive step relies on the observation that the `(n-k)`-th derivative, evaluated at 1,
annihilates `bernstein_polynomial n ν` for `ν < k`, but has a nonzero value at `ν = k`.
-/
theorem LinearIndependent (n : ℕ) : LinearIndependent ℚ fun ν : Finₓ (n+1) => bernsteinPolynomial ℚ n ν :=
  linear_independent_aux n (n+1) (le_reflₓ _)

theorem Sum (n : ℕ) : ((Finset.range (n+1)).Sum fun ν => bernsteinPolynomial R n ν) = 1 :=
  by 
    conv  => congr congr skip ext dsimp [bernsteinPolynomial]rw [mul_assocₓ, mul_commₓ]
    rw [←add_pow]
    simp 

open Polynomial

open MvPolynomial

-- error in RingTheory.Polynomial.Bernstein: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sum_smul
(n : exprℕ()) : «expr = »((finset.range «expr + »(n, 1)).sum (λ
  ν, «expr • »(ν, bernstein_polynomial R n ν)), «expr • »(n, X)) :=
begin
  let [ident x] [":", expr mv_polynomial bool R] [":=", expr mv_polynomial.X tt],
  let [ident y] [":", expr mv_polynomial bool R] [":=", expr mv_polynomial.X ff],
  have [ident pderiv_tt_x] [":", expr «expr = »(pderiv tt x, 1)] [],
  { simp [] [] [] ["[", expr x, "]"] [] [] },
  have [ident pderiv_tt_y] [":", expr «expr = »(pderiv tt y, 0)] [],
  { simp [] [] [] ["[", expr pderiv_X, ",", expr y, "]"] [] [] },
  let [ident e] [":", expr bool → polynomial R] [":=", expr λ i, cond i X «expr - »(1, X)],
  have [ident h] [":", expr «expr = »(«expr ^ »(«expr + »(x, y), n), «expr ^ »(«expr + »(x, y), n))] [":=", expr rfl],
  apply_fun [expr pderiv tt] ["at", ident h] [],
  apply_fun [expr aeval e] ["at", ident h] [],
  apply_fun [expr λ p, «expr * »(p, X)] ["at", ident h] [],
  have [ident w] [":", expr ∀
   k : exprℕ(), «expr = »(«expr * »(«expr * »(«expr * »(«expr * »(«expr↑ »(k), «expr ^ »(polynomial.X, «expr - »(k, 1))), «expr ^ »(«expr - »(1, polynomial.X), «expr - »(n, k))), «expr↑ »(n.choose k)), polynomial.X), «expr • »(k, bernstein_polynomial R n k))] [],
  { rintro ["(", "_", "|", ident k, ")"],
    { simp [] [] [] [] [] [] },
    { dsimp [] ["[", expr bernstein_polynomial, "]"] [] [],
      simp [] [] ["only"] ["[", "<-", expr nat_cast_mul, ",", expr nat.succ_eq_add_one, ",", expr nat.add_succ_sub_one, ",", expr add_zero, ",", expr pow_succ, "]"] [] [],
      push_cast [] [],
      ring [] } },
  conv ["at", ident h] [] { to_lhs,
    rw ["[", expr add_pow, ",", expr (pderiv tt).map_sum, ",", expr (mv_polynomial.aeval e).map_sum, ",", expr finset.sum_mul, "]"],
    apply_congr [],
    skip,
    simp [] ["[", expr pderiv_mul, ",", expr pderiv_tt_x, ",", expr pderiv_tt_y, ",", expr e, ",", expr w, "]"] [] },
  conv ["at", ident h] [] { to_rhs,
    rw ["[", expr pderiv_pow, ",", expr (pderiv tt).map_add, ",", expr pderiv_tt_x, ",", expr pderiv_tt_y, "]"],
    simp [] ["[", expr e, "]"] [] },
  simpa [] [] [] [] [] ["using", expr h]
end

-- error in RingTheory.Polynomial.Bernstein: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sum_mul_smul
(n : exprℕ()) : «expr = »((finset.range «expr + »(n, 1)).sum (λ
  ν, «expr • »(«expr * »(ν, «expr - »(ν, 1)), bernstein_polynomial R n ν)), «expr • »(«expr * »(n, «expr - »(n, 1)), «expr ^ »(X, 2))) :=
begin
  let [ident x] [":", expr mv_polynomial bool R] [":=", expr mv_polynomial.X tt],
  let [ident y] [":", expr mv_polynomial bool R] [":=", expr mv_polynomial.X ff],
  have [ident pderiv_tt_x] [":", expr «expr = »(pderiv tt x, 1)] [],
  { simp [] [] [] ["[", expr x, "]"] [] [] },
  have [ident pderiv_tt_y] [":", expr «expr = »(pderiv tt y, 0)] [],
  { simp [] [] [] ["[", expr pderiv_X, ",", expr y, "]"] [] [] },
  let [ident e] [":", expr bool → polynomial R] [":=", expr λ i, cond i X «expr - »(1, X)],
  have [ident h] [":", expr «expr = »(«expr ^ »(«expr + »(x, y), n), «expr ^ »(«expr + »(x, y), n))] [":=", expr rfl],
  apply_fun [expr pderiv tt] ["at", ident h] [],
  apply_fun [expr pderiv tt] ["at", ident h] [],
  apply_fun [expr aeval e] ["at", ident h] [],
  apply_fun [expr λ p, «expr * »(p, «expr ^ »(X, 2))] ["at", ident h] [],
  have [ident w] [":", expr ∀
   k : exprℕ(), «expr = »(«expr * »(«expr * »(«expr * »(«expr * »(«expr↑ »(k), «expr * »(«expr↑ »(«expr - »(k, 1)), «expr ^ »(polynomial.X, «expr - »(«expr - »(k, 1), 1)))), «expr ^ »(«expr - »(1, polynomial.X), «expr - »(n, k))), «expr↑ »(n.choose k)), «expr ^ »(polynomial.X, 2)), «expr • »(«expr * »(k, «expr - »(k, 1)), bernstein_polynomial R n k))] [],
  { rintro ["(", "_", "|", ident k, ")"],
    { simp [] [] [] [] [] [] },
    { rcases [expr k, "with", "(", "_", "|", ident k, ")"],
      { simp [] [] [] [] [] [] },
      { dsimp [] ["[", expr bernstein_polynomial, "]"] [] [],
        simp [] [] ["only"] ["[", "<-", expr nat_cast_mul, ",", expr nat.succ_eq_add_one, ",", expr nat.add_succ_sub_one, ",", expr add_zero, ",", expr pow_succ, "]"] [] [],
        push_cast [] [],
        ring [] } } },
  conv ["at", ident h] [] { to_lhs,
    rw ["[", expr add_pow, ",", expr (pderiv tt).map_sum, ",", expr (pderiv tt).map_sum, ",", expr (mv_polynomial.aeval e).map_sum, ",", expr finset.sum_mul, "]"],
    apply_congr [],
    skip,
    simp [] ["[", expr pderiv_mul, ",", expr pderiv_tt_x, ",", expr pderiv_tt_y, ",", expr e, ",", expr w, "]"] [] },
  conv ["at", ident h] [] { to_rhs,
    simp ["only"] ["[", expr pderiv_one, ",", expr pderiv_mul, ",", expr pderiv_pow, ",", expr pderiv_nat_cast, ",", expr (pderiv tt).map_add, ",", expr pderiv_tt_x, ",", expr pderiv_tt_y, "]"] [],
    simp [] ["[", expr e, ",", expr smul_smul, "]"] [] },
  simpa [] [] [] [] [] ["using", expr h]
end

-- error in RingTheory.Polynomial.Bernstein: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A certain linear combination of the previous three identities,
which we'll want later.
-/
theorem variance
(n : exprℕ()) : «expr = »((finset.range «expr + »(n, 1)).sum (λ
  ν, «expr * »(«expr ^ »(«expr - »(«expr • »(n, polynomial.X), ν), 2), bernstein_polynomial R n ν)), «expr * »(«expr • »(n, polynomial.X), «expr - »(1, polynomial.X))) :=
begin
  have [ident p] [":", expr «expr = »(«expr + »(«expr + »((finset.range «expr + »(n, 1)).sum (λ
       ν, «expr • »(«expr * »(ν, «expr - »(ν, 1)), bernstein_polynomial R n ν)), «expr * »(«expr - »(1, «expr • »(«expr * »(2, n), polynomial.X)), (finset.range «expr + »(n, 1)).sum (λ
        ν, «expr • »(ν, bernstein_polynomial R n ν)))), «expr * »(«expr • »(«expr ^ »(n, 2), «expr ^ »(X, 2)), (finset.range «expr + »(n, 1)).sum (λ
       ν, bernstein_polynomial R n ν))), _)] [":=", expr rfl],
  conv ["at", ident p] [] { to_lhs,
    rw ["[", expr finset.mul_sum, ",", expr finset.mul_sum, ",", "<-", expr finset.sum_add_distrib, ",", "<-", expr finset.sum_add_distrib, "]"],
    simp ["only"] ["[", "<-", expr nat_cast_mul, "]"] [],
    simp ["only"] ["[", "<-", expr mul_assoc, "]"] [],
    simp ["only"] ["[", "<-", expr add_mul, "]"] [] },
  conv ["at", ident p] [] { to_rhs,
    rw ["[", expr sum, ",", expr sum_smul, ",", expr sum_mul_smul, ",", "<-", expr nat_cast_mul, "]"] },
  calc
    «expr = »(_, _) : finset.sum_congr rfl (λ k m, _)
    «expr = »(..., _) : p
    «expr = »(..., _) : _,
  { congr' [1] [],
    simp [] [] ["only"] ["[", "<-", expr nat_cast_mul, "]"] ["with", ident push_cast] [],
    cases [expr k] []; { simp [] [] [] [] [] [],
      ring [] } },
  { simp [] [] ["only"] ["[", "<-", expr nat_cast_mul, "]"] ["with", ident push_cast] [],
    cases [expr n] [],
    { simp [] [] [] [] [] [] },
    { simp [] [] [] [] [] [],
      ring [] } }
end

end bernsteinPolynomial

