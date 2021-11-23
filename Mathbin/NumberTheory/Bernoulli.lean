import Mathbin.Algebra.BigOperators.NatAntidiagonal 
import Mathbin.Algebra.GeomSum 
import Mathbin.Data.Fintype.Card 
import Mathbin.RingTheory.PowerSeries.WellKnown 
import Mathbin.Tactic.FieldSimp

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, -1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the formula for the sums of $k$th
powers. They are related to the Taylor series expansions of $x/\tan(x)$ and
of $\coth(x)$, and also show up in the values that the Riemann Zeta function
takes both at both negative and positive integers (and hence in the
theory of modular forms). For example, if $1 \leq n$ is even then

$$\zeta(2n)=\sum_{t\geq1}t^{-2n}=(-1)^{n+1}\frac{(2\pi)^{2n}B_{2n}}{2(2n)!}.$$

Note however that this result is not yet formalised in Lean.

The Bernoulli numbers can be formally defined using the power series

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* and need not concern the mathematician).

Note that $B_1=-1/2$, meaning that we are using the $B_n^-$ of
[from Wikipedia](https://en.wikipedia.org/wiki/Bernoulli_number).

## Implementation detail

The Bernoulli numbers are defined using well-founded induction, by the formula
$$B_n=1-\sum_{k\lt n}\frac{\binom{n}{k}}{n-k+1}B_k.$$
This formula is true for all $n$ and in particular $B_0=1$. Note that this is the definition
for positive Bernoulli numbers, which we call `bernoulli'`. The negative Bernoulli numbers are
then defined as `bernoulli := (-1)^n * bernoulli'`.

## Main theorems

`sum_bernoulli : ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = 0`
-/


open_locale Nat BigOperators

open Finset Nat Finset.Nat PowerSeries

variable(A : Type _)[CommRingₓ A][Algebra ℚ A]

/-! ### Definitions -/


/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = 1 - \sum_{k < n} \binom{n}{k}\frac{B_k}{n+1-k}$$ -/
def bernoulli' : ℕ → ℚ :=
  WellFounded.fix lt_wf$ fun n bernoulli' => 1 - ∑k : Finₓ n, (n.choose k / (n - k)+1)*bernoulli' k k.2

theorem bernoulli'_def' (n : ℕ) : bernoulli' n = 1 - ∑k : Finₓ n, (n.choose k / (n - k)+1)*bernoulli' k :=
  WellFounded.fix_eq _ _ _

theorem bernoulli'_def (n : ℕ) : bernoulli' n = 1 - ∑k in range n, (n.choose k / (n - k)+1)*bernoulli' k :=
  by 
    rw [bernoulli'_def', ←Finₓ.sum_univ_eq_sum_range]
    rfl

theorem bernoulli'_spec (n : ℕ) : (∑k in range n.succ, ((n.choose (n - k) : ℚ) / (n - k)+1)*bernoulli' k) = 1 :=
  by 
    rw [sum_range_succ_comm, bernoulli'_def n, tsub_self]
    conv  in n.choose (_ - _) => rw [choose_symm (mem_range.1 H).le]
    simp only [one_mulₓ, cast_one, sub_self, sub_add_cancel, choose_zero_right, zero_addₓ, div_one]

theorem bernoulli'_spec' (n : ℕ) : (∑k in antidiagonal n, (((k.1+k.2).choose k.2 : ℚ) / k.2+1)*bernoulli' k.1) = 1 :=
  by 
    refine' ((sum_antidiagonal_eq_sum_range_succ_mk _ n).trans _).trans (bernoulli'_spec n)
    refine' sum_congr rfl fun x hx => _ 
    simp only [add_tsub_cancel_of_le, mem_range_succ_iff.mp hx, cast_sub]

/-! ### Examples -/


section Examples

@[simp]
theorem bernoulli'_zero : bernoulli' 0 = 1 :=
  by 
    rw [bernoulli'_def]
    normNum

@[simp]
theorem bernoulli'_one : bernoulli' 1 = 1 / 2 :=
  by 
    rw [bernoulli'_def]
    normNum

@[simp]
theorem bernoulli'_two : bernoulli' 2 = 1 / 6 :=
  by 
    rw [bernoulli'_def]
    normNum [sum_range_succ]

@[simp]
theorem bernoulli'_three : bernoulli' 3 = 0 :=
  by 
    rw [bernoulli'_def]
    normNum [sum_range_succ]

@[simp]
theorem bernoulli'_four : bernoulli' 4 = -1 / 30 :=
  have  : Nat.choose 4 2 = 6 :=
    by 
      decide 
  by 
    rw [bernoulli'_def]
    normNum [sum_range_succ, this]

end Examples

-- error in NumberTheory.Bernoulli: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem sum_bernoulli'
(n : exprℕ()) : «expr = »(«expr∑ in , »((k), range n, «expr * »((n.choose k : exprℚ()), bernoulli' k)), n) :=
begin
  cases [expr n] [],
  { simp [] [] [] [] [] [] },
  suffices [] [":", expr «expr = »(«expr * »((«expr + »(n, 1) : exprℚ()), «expr∑ in , »((k), range n, «expr * »(«expr / »(«expr↑ »(n.choose k), «expr + »(«expr - »(n, k), 1)), bernoulli' k))), «expr∑ in , »((x), range n, «expr * »(«expr↑ »(n.succ.choose x), bernoulli' x)))],
  { rw_mod_cast ["[", expr sum_range_succ, ",", expr bernoulli'_def, ",", "<-", expr this, ",", expr choose_succ_self_right, "]"] [],
    ring [] },
  simp_rw ["[", expr mul_sum, ",", "<-", expr mul_assoc, "]"] [],
  refine [expr sum_congr rfl (λ k hk, _)],
  congr' [] [],
  have [] [":", expr «expr ≠ »(«expr + »(((«expr - »(n, k) : exprℕ()) : exprℚ()), 1), 0)] [":=", expr by apply_mod_cast [expr succ_ne_zero]],
  field_simp [] ["[", "<-", expr cast_sub (mem_range.1 hk).le, ",", expr mul_comm, "]"] [] [],
  rw_mod_cast ["[", expr tsub_add_eq_add_tsub (mem_range.1 hk).le, ",", expr choose_mul_succ_eq, "]"] []
end

/-- The exponential generating function for the Bernoulli numbers `bernoulli' n`. -/
def bernoulli'PowerSeries :=
  mk$ fun n => algebraMap ℚ A (bernoulli' n / n !)

-- error in NumberTheory.Bernoulli: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bernoulli'_power_series_mul_exp_sub_one : «expr = »(«expr * »(bernoulli'_power_series A, «expr - »(exp A, 1)), «expr * »(X, exp A)) :=
begin
  ext [] [ident n] [],
  cases [expr n] [],
  { simp [] [] [] [] [] [] },
  rw ["[", expr bernoulli'_power_series, ",", expr coeff_mul, ",", expr mul_comm X, ",", expr sum_antidiagonal_succ', "]"] [],
  suffices [] [":", expr «expr = »(«expr∑ in , »((p), antidiagonal n, «expr * »(«expr / »(bernoulli' p.1, «expr !»(p.1)), «expr ⁻¹»(«expr * »(«expr + »(p.2, 1), «expr !»(p.2))))), «expr ⁻¹»(«expr !»(n)))],
  { simpa [] [] [] ["[", expr ring_hom.map_sum, "]"] [] ["using", expr congr_arg (algebra_map exprℚ() A) this] },
  apply [expr eq_inv_of_mul_left_eq_one],
  rw [expr sum_mul] [],
  convert [] [expr bernoulli'_spec' n] ["using", 1],
  apply [expr sum_congr rfl],
  simp_rw ["[", expr mem_antidiagonal, "]"] [],
  rintro ["⟨", ident i, ",", ident j, "⟩", ident rfl],
  have [] [":", expr «expr ≠ »((«expr + »(j, 1) : exprℚ()), 0)] [":=", expr by exact_mod_cast [expr succ_ne_zero j]],
  have [] [":", expr «expr ≠ »(«expr * »(«expr * »((«expr + »(j, 1) : exprℚ()), «expr !»(j)), «expr !»(i)), 0)] [":=", expr by simpa [] [] [] ["[", expr factorial_ne_zero, "]"] [] []],
  have [] [] [":=", expr factorial_mul_factorial_dvd_factorial_add i j],
  field_simp [] ["[", expr mul_comm _ (bernoulli' i), ",", expr mul_assoc, ",", expr add_choose, "]"] [] [],
  rw_mod_cast ["[", expr mul_comm «expr + »(j, 1), ",", expr mul_div_assoc, ",", "<-", expr mul_assoc, "]"] [],
  rw ["[", expr cast_mul, ",", expr cast_mul, ",", expr mul_div_mul_right, ",", expr cast_dvd_char_zero, ",", expr cast_mul, "]"] [],
  assumption'
end

-- error in NumberTheory.Bernoulli: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Odd Bernoulli numbers (greater than 1) are zero. -/
theorem bernoulli'_odd_eq_zero {n : exprℕ()} (h_odd : odd n) (hlt : «expr < »(1, n)) : «expr = »(bernoulli' n, 0) :=
begin
  let [ident B] [] [":=", expr mk (λ n, «expr / »(bernoulli' n, «expr !»(n)))],
  suffices [] [":", expr «expr = »(«expr * »(«expr - »(B, eval_neg_hom B), «expr - »(exp exprℚ(), 1)), «expr * »(X, «expr - »(exp exprℚ(), 1)))],
  { cases [expr mul_eq_mul_right_iff.mp this] []; simp [] [] ["only"] ["[", expr power_series.ext_iff, ",", expr eval_neg_hom, ",", expr coeff_X, "]"] [] ["at", ident h],
    { apply [expr eq_zero_of_neg_eq],
      specialize [expr h n],
      split_ifs ["at", ident h] []; simp [] [] [] ["[", expr neg_one_pow_of_odd h_odd, ",", expr factorial_ne_zero, ",", "*", "]"] [] ["at", "*"] },
    { simpa [] [] [] [] [] ["using", expr h 1] } },
  have [ident h] [":", expr «expr = »(«expr * »(B, «expr - »(exp exprℚ(), 1)), «expr * »(X, exp exprℚ()))] [],
  { simpa [] [] [] ["[", expr bernoulli'_power_series, "]"] [] ["using", expr bernoulli'_power_series_mul_exp_sub_one exprℚ()] },
  rw ["[", expr sub_mul, ",", expr h, ",", expr mul_sub X, ",", expr sub_right_inj, ",", "<-", expr neg_sub, ",", "<-", expr neg_mul_eq_mul_neg, ",", expr neg_eq_iff_neg_eq, "]"] [],
  suffices [] [":", expr «expr = »(«expr * »(eval_neg_hom «expr * »(B, «expr - »(exp exprℚ(), 1)), exp exprℚ()), «expr * »(eval_neg_hom «expr * »(X, exp exprℚ()), exp exprℚ()))],
  { simpa [] [] [] ["[", expr mul_assoc, ",", expr sub_mul, ",", expr mul_comm (eval_neg_hom (exp exprℚ())), ",", expr exp_mul_exp_neg_eq_one, ",", expr eq_comm, "]"] [] [] },
  congr' [] []
end

/-- The Bernoulli numbers are defined to be `bernoulli'` with a parity sign. -/
def bernoulli (n : ℕ) : ℚ :=
  (-1^n)*bernoulli' n

theorem bernoulli'_eq_bernoulli (n : ℕ) : bernoulli' n = (-1^n)*bernoulli n :=
  by 
    simp [bernoulli, ←mul_assocₓ, ←sq, ←pow_mulₓ, mul_commₓ n 2, pow_mulₓ]

@[simp]
theorem bernoulli_zero : bernoulli 0 = 1 :=
  by 
    simp [bernoulli]

@[simp]
theorem bernoulli_one : bernoulli 1 = -1 / 2 :=
  by 
    normNum [bernoulli]

theorem bernoulli_eq_bernoulli'_of_ne_one {n : ℕ} (hn : n ≠ 1) : bernoulli n = bernoulli' n :=
  by 
    byCases' h0 : n = 0
    ·
      simp [h0]
    rw [bernoulli, neg_one_pow_eq_pow_mod_two]
    cases mod_two_eq_zero_or_one n
    ·
      simp [h]
    simp [bernoulli'_odd_eq_zero (odd_iff.mpr h) (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, hn⟩)]

-- error in NumberTheory.Bernoulli: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem sum_bernoulli
(n : exprℕ()) : «expr = »(«expr∑ in , »((k), range n, «expr * »((n.choose k : exprℚ()), bernoulli k)), if «expr = »(n, 1) then 1 else 0) :=
begin
  cases [expr n] [],
  { simp [] [] [] [] [] [] },
  cases [expr n] [],
  { simp [] [] [] [] [] [] },
  suffices [] [":", expr «expr = »(«expr∑ in , »((i), range n, «expr * »(«expr↑ »(«expr + »(n, 2).choose «expr + »(i, 2)), bernoulli «expr + »(i, 2))), «expr / »(n, 2))],
  { simp [] [] ["only"] ["[", expr this, ",", expr sum_range_succ', ",", expr cast_succ, ",", expr bernoulli_one, ",", expr bernoulli_zero, ",", expr choose_one_right, ",", expr mul_one, ",", expr choose_zero_right, ",", expr cast_zero, ",", expr if_false, ",", expr zero_add, ",", expr succ_succ_ne_one, "]"] [] [],
    ring [] },
  have [ident f] [] [":=", expr sum_bernoulli' n.succ.succ],
  simp_rw ["[", expr sum_range_succ', ",", expr bernoulli'_one, ",", expr choose_one_right, ",", expr cast_succ, ",", "<-", expr eq_sub_iff_add_eq, "]"] ["at", ident f],
  convert [] [expr f] [],
  { ext [] [ident x] [],
    rw [expr bernoulli_eq_bernoulli'_of_ne_one «expr ∘ »(succ_ne_zero x, succ.inj)] [] },
  { simp [] [] ["only"] ["[", expr one_div, ",", expr mul_one, ",", expr bernoulli'_zero, ",", expr cast_one, ",", expr choose_zero_right, ",", expr add_sub_cancel, "]"] [] [],
    ring [] }
end

-- error in NumberTheory.Bernoulli: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bernoulli_spec'
(n : exprℕ()) : «expr = »(«expr∑ in , »((k), antidiagonal n, «expr * »(«expr / »((«expr + »(k.1, k.2).choose k.2 : exprℚ()), «expr + »(k.2, 1)), bernoulli k.1)), if «expr = »(n, 0) then 1 else 0) :=
begin
  cases [expr n] [],
  { simp [] [] [] [] [] [] },
  rw [expr if_neg (succ_ne_zero _)] [],
  have [ident h₁] [":", expr «expr ∈ »((1, n), antidiagonal n.succ)] [":=", expr by simp [] [] [] ["[", expr mem_antidiagonal, ",", expr add_comm, "]"] [] []],
  have [ident h₂] [":", expr «expr ≠ »(«expr + »((n : exprℚ()), 1), 0)] [":=", expr by apply_mod_cast [expr succ_ne_zero]],
  have [ident h₃] [":", expr «expr = »(«expr + »(1, n).choose n, «expr + »(n, 1))] [":=", expr by simp [] [] [] ["[", expr add_comm, "]"] [] []],
  have [ident H] [] [":=", expr bernoulli'_spec' n.succ],
  rw [expr sum_eq_add_sum_diff_singleton h₁] ["at", ident H, "⊢"],
  apply [expr add_eq_of_eq_sub'],
  convert [] [expr eq_sub_of_add_eq' H] ["using", 1],
  { refine [expr sum_congr rfl (λ p h, _)],
    obtain ["⟨", ident h', ",", ident h'', "⟩", ":", expr «expr ∧ »(«expr ∈ »(p, _), «expr ≠ »(p, _)), ":=", expr by rwa ["[", expr mem_sdiff, ",", expr mem_singleton, "]"] ["at", ident h]],
    simp [] [] [] ["[", expr bernoulli_eq_bernoulli'_of_ne_one ((not_congr (antidiagonal_congr h' h₁)).mp h''), "]"] [] [] },
  { field_simp [] ["[", expr h₃, "]"] [] [],
    norm_num [] [] }
end

/-- The exponential generating function for the Bernoulli numbers `bernoulli n`. -/
def bernoulliPowerSeries :=
  mk$ fun n => algebraMap ℚ A (bernoulli n / n !)

-- error in NumberTheory.Bernoulli: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bernoulli_power_series_mul_exp_sub_one : «expr = »(«expr * »(bernoulli_power_series A, «expr - »(exp A, 1)), X) :=
begin
  ext [] [ident n] [],
  cases [expr n] [],
  { simp [] [] [] [] [] [] },
  simp [] [] ["only"] ["[", expr bernoulli_power_series, ",", expr coeff_mul, ",", expr coeff_X, ",", expr sum_antidiagonal_succ', ",", expr one_div, ",", expr coeff_mk, ",", expr coeff_one, ",", expr coeff_exp, ",", expr linear_map.map_sub, ",", expr factorial, ",", expr if_pos, ",", expr cast_succ, ",", expr cast_one, ",", expr cast_mul, ",", expr sub_zero, ",", expr ring_hom.map_one, ",", expr add_eq_zero_iff, ",", expr if_false, ",", expr inv_one, ",", expr zero_add, ",", expr one_ne_zero, ",", expr mul_zero, ",", expr and_false, ",", expr sub_self, ",", "<-", expr ring_hom.map_mul, ",", "<-", expr ring_hom.map_sum, "]"] [] [],
  suffices [] [":", expr «expr = »(«expr∑ in , »((x), antidiagonal n, «expr * »(«expr / »(bernoulli x.1, «expr !»(x.1)), «expr ⁻¹»(«expr * »(«expr + »(x.2, 1), «expr !»(x.2))))), if «expr = »(n.succ, 1) then 1 else 0)],
  { split_ifs [] []; simp [] [] [] ["[", expr h, ",", expr this, "]"] [] [] },
  cases [expr n] [],
  { simp [] [] [] [] [] [] },
  have [ident hfact] [":", expr ∀
   m, «expr ≠ »((«expr !»(m) : exprℚ()), 0)] [":=", expr λ m, by exact_mod_cast [expr factorial_ne_zero m]],
  have [ident hite1] [":", expr «expr = »(ite «expr = »(n.succ.succ, 1) 1 0, («expr / »(0, «expr !»(n.succ)) : exprℚ()))] [":=", expr by simp [] [] [] [] [] []],
  have [ident hite2] [":", expr «expr = »(ite «expr = »(n.succ, 0) 1 0, (0 : exprℚ()))] [":=", expr by simp [] [] [] ["[", expr succ_ne_zero, "]"] [] []],
  rw ["[", expr hite1, ",", expr eq_div_iff (hfact n.succ), ",", "<-", expr hite2, ",", "<-", expr bernoulli_spec', ",", expr sum_mul, "]"] [],
  apply [expr sum_congr rfl],
  rintro ["⟨", ident i, ",", ident j, "⟩", ident h],
  rw [expr mem_antidiagonal] ["at", ident h],
  have [ident hj] [":", expr «expr ≠ »((j.succ : exprℚ()), 0)] [":=", expr by exact_mod_cast [expr succ_ne_zero j]],
  field_simp [] ["[", "<-", expr h, ",", expr mul_ne_zero hj (hfact j), ",", expr hfact i, ",", expr mul_comm _ (bernoulli i), ",", expr mul_assoc, "]"] [] [],
  rw_mod_cast ["[", expr mul_comm «expr + »(j, 1), ",", expr mul_div_assoc, ",", "<-", expr mul_assoc, "]"] [],
  rw ["[", expr cast_mul, ",", expr cast_mul, ",", expr mul_div_mul_right _ _ hj, ",", expr add_choose, ",", expr cast_dvd_char_zero, "]"] [],
  apply [expr factorial_mul_factorial_dvd_factorial_add]
end

section Faulhaber

-- error in NumberTheory.Bernoulli: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Faulhaber's theorem** relating the **sum of of p-th powers** to the Bernoulli numbers:
$$\sum_{k=0}^{n-1} k^p = \sum_{i=0}^p B_i\binom{p+1}{i}\frac{n^{p+1-i}}{p+1}.$$
See https://proofwiki.org/wiki/Faulhaber%27s_Formula and [orosi2018faulhaber] for
the proof provided here. -/
theorem sum_range_pow
(n
 p : exprℕ()) : «expr = »(«expr∑ in , »((k), range n, «expr ^ »((k : exprℚ()), p)), «expr∑ in , »((i), range «expr + »(p, 1), «expr / »(«expr * »(«expr * »(bernoulli i, «expr + »(p, 1).choose i), «expr ^ »(n, «expr - »(«expr + »(p, 1), i))), «expr + »(p, 1)))) :=
begin
  have [ident hne] [":", expr ∀
   m : exprℕ(), «expr ≠ »((«expr !»(m) : exprℚ()), 0)] [":=", expr λ m, by exact_mod_cast [expr factorial_ne_zero m]],
  have [ident h_cauchy] [":", expr «expr = »(«expr * »(mk (λ
      p, «expr / »(bernoulli p, «expr !»(p))), mk (λ
      q, coeff exprℚ() «expr + »(q, 1) «expr ^ »(exp exprℚ(), n))), mk (λ
     p, «expr∑ in , »((i), range «expr + »(p, 1), «expr / »(«expr * »(«expr * »(bernoulli i, «expr + »(p, 1).choose i), «expr ^ »(n, «expr - »(«expr + »(p, 1), i))), «expr !»(«expr + »(p, 1))))))] [],
  { ext [] [ident q] [],
    let [ident f] [] [":=", expr λ
     a b, «expr * »(«expr / »(bernoulli a, «expr !»(a)), coeff exprℚ() «expr + »(b, 1) «expr ^ »(exp exprℚ(), n))],
    simp [] [] ["only"] ["[", expr coeff_mul, ",", expr coeff_mk, ",", expr cast_mul, ",", expr sum_antidiagonal_eq_sum_range_succ f, "]"] [] [],
    apply [expr sum_congr rfl],
    simp_intros [ident m, ident h] ["only"] ["[", expr finset.mem_range, "]"] [],
    simp [] [] ["only"] ["[", expr f, ",", expr exp_pow_eq_rescale_exp, ",", expr rescale, ",", expr one_div, ",", expr coeff_mk, ",", expr ring_hom.coe_mk, ",", expr coeff_exp, ",", expr ring_hom.id_apply, ",", expr cast_mul, ",", expr rat.algebra_map_rat_rat, "]"] [] [],
    rw ["[", expr choose_eq_factorial_div_factorial h.le, ",", expr eq_comm, ",", expr div_eq_iff (hne q.succ), ",", expr succ_eq_add_one, ",", expr mul_assoc _ _ «expr↑ »(«expr !»(q.succ)), ",", expr mul_comm _ «expr↑ »(«expr !»(q.succ)), ",", "<-", expr mul_assoc, ",", expr div_mul_eq_mul_div, ",", expr mul_comm «expr ^ »(«expr↑ »(n), «expr + »(«expr - »(q, m), 1)), ",", "<-", expr mul_assoc _ _ «expr ^ »(«expr↑ »(n), «expr + »(«expr - »(q, m), 1)), ",", "<-", expr one_div, ",", expr mul_one_div, ",", expr div_div_eq_div_mul, ",", expr tsub_add_eq_add_tsub (le_of_lt_succ h), ",", expr cast_dvd, ",", expr cast_mul, "]"] [],
    { ring [] },
    { exact [expr factorial_mul_factorial_dvd_factorial h.le] },
    { simp [] [] [] ["[", expr hne, "]"] [] [] } },
  have [ident hps] [":", expr «expr = »(«expr∑ in , »((k), range n, «expr ^ »(«expr↑ »(k), p)), «expr * »(«expr∑ in , »((i), range «expr + »(p, 1), «expr / »(«expr * »(«expr * »(bernoulli i, «expr + »(p, 1).choose i), «expr ^ »(n, «expr - »(«expr + »(p, 1), i))), «expr !»(«expr + »(p, 1)))), «expr !»(p)))] [],
  { suffices [] [":", expr «expr = »(mk (λ
       p, «expr∑ in , »((k), range n, «expr * »(«expr ^ »(«expr↑ »(k), p), algebra_map exprℚ() exprℚ() «expr ⁻¹»(«expr !»(p))))), mk (λ
       p, «expr∑ in , »((i), range «expr + »(p, 1), «expr / »(«expr * »(«expr * »(bernoulli i, «expr + »(p, 1).choose i), «expr ^ »(n, «expr - »(«expr + »(p, 1), i))), «expr !»(«expr + »(p, 1))))))],
    { rw ["[", "<-", expr div_eq_iff (hne p), ",", expr div_eq_mul_inv, ",", expr sum_mul, "]"] [],
      rw [expr power_series.ext_iff] ["at", ident this],
      simpa [] [] [] [] [] ["using", expr this p] },
    have [ident hexp] [":", expr «expr ≠ »(«expr - »(exp exprℚ(), 1), 0)] [],
    { simp [] [] ["only"] ["[", expr exp, ",", expr power_series.ext_iff, ",", expr ne, ",", expr not_forall, "]"] [] [],
      use [expr 1],
      simp [] [] [] [] [] [] },
    have [ident h_r] [":", expr «expr = »(«expr - »(«expr ^ »(exp exprℚ(), n), 1), «expr * »(X, mk (λ
        p, coeff exprℚ() «expr + »(p, 1) «expr ^ »(exp exprℚ(), n))))] [],
    { have [ident h_const] [":", expr «expr = »(C exprℚ() (constant_coeff exprℚ() «expr ^ »(exp exprℚ(), n)), 1)] [":=", expr by simp [] [] [] [] [] []],
      rw ["[", "<-", expr h_const, ",", expr sub_const_eq_X_mul_shift, "]"] [] },
    rw ["[", "<-", expr mul_right_inj' hexp, ",", expr mul_comm, ",", "<-", expr exp_pow_sum, ",", "<-", expr geom_sum_def, ",", expr geom_sum_mul, ",", expr h_r, ",", "<-", expr bernoulli_power_series_mul_exp_sub_one, ",", expr bernoulli_power_series, ",", expr mul_right_comm, "]"] [],
    simp [] [] [] ["[", expr h_cauchy, ",", expr mul_comm, "]"] [] [] },
  rw ["[", expr hps, ",", expr sum_mul, "]"] [],
  refine [expr sum_congr rfl (λ x hx, _)],
  field_simp [] ["[", expr mul_right_comm _ «expr↑ »(«expr !»(p)), ",", "<-", expr mul_assoc _ _ «expr↑ »(«expr !»(p)), ",", expr cast_add_one_ne_zero, ",", expr hne, "]"] [] []
end

-- error in NumberTheory.Bernoulli: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Alternate form of **Faulhaber's theorem**, relating the sum of p-th powers to the Bernoulli
numbers: $$\sum_{k=1}^{n} k^p = \sum_{i=0}^p (-1)^iB_i\binom{p+1}{i}\frac{n^{p+1-i}}{p+1}.$$
Deduced from `sum_range_pow`. -/
theorem sum_Ico_pow
(n
 p : exprℕ()) : «expr = »(«expr∑ in , »((k), Ico 1 «expr + »(n, 1), «expr ^ »((k : exprℚ()), p)), «expr∑ in , »((i), range «expr + »(p, 1), «expr / »(«expr * »(«expr * »(bernoulli' i, «expr + »(p, 1).choose i), «expr ^ »(n, «expr - »(«expr + »(p, 1), i))), «expr + »(p, 1)))) :=
begin
  cases [expr p] [],
  { simp [] [] [] [] [] [] },
  let [ident f] [] [":=", expr λ
   i, «expr / »(«expr * »(«expr * »(bernoulli i, p.succ.succ.choose i), «expr ^ »(n, «expr - »(p.succ.succ, i))), p.succ.succ)],
  let [ident f'] [] [":=", expr λ
   i, «expr / »(«expr * »(«expr * »(bernoulli' i, p.succ.succ.choose i), «expr ^ »(n, «expr - »(p.succ.succ, i))), p.succ.succ)],
  suffices [] [":", expr «expr = »(«expr∑ in , »((k), Ico 1 n.succ, «expr ^ »(«expr↑ »(k), p.succ)), «expr∑ in , »((i), range p.succ.succ, f' i))],
  { convert [] [expr this] [] },
  have [ident hle] [] [":=", expr nat.le_add_left 1 n],
  have [ident hne] [":", expr «expr ≠ »((«expr + »(«expr + »(p, 1), 1) : exprℚ()), 0)] [":=", expr by exact_mod_cast [expr succ_ne_zero p.succ]],
  have [ident h1] [":", expr ∀
   r : exprℚ(), «expr = »(«expr / »(«expr * »(«expr * »(r, «expr + »(«expr + »(p, 1), 1)), «expr ^ »(n, p.succ)), («expr + »(«expr + »(p, 1), 1) : exprℚ())), «expr * »(r, «expr ^ »(n, p.succ)))] [":=", expr λ
   r, by rw ["[", expr mul_div_right_comm, ",", expr mul_div_cancel _ hne, "]"] []],
  have [ident h2] [":", expr «expr = »(«expr + »(f 1, «expr ^ »(n, p.succ)), «expr * »(«expr / »(1, 2), «expr ^ »(n, p.succ)))] [],
  { simp_rw ["[", expr f, ",", expr bernoulli_one, ",", expr choose_one_right, ",", expr succ_sub_succ_eq_sub, ",", expr cast_succ, ",", expr tsub_zero, ",", expr h1, "]"] [],
    ring [] },
  have [] [":", expr «expr = »(«expr∑ in , »((i), range p, «expr / »(«expr * »(«expr * »(bernoulli «expr + »(i, 2), «expr + »(p, 2).choose «expr + »(i, 2)), «expr ^ »(n, «expr - »(p, i))), «expr↑ »(«expr + »(p, 2)))), «expr∑ in , »((i), range p, «expr / »(«expr * »(«expr * »(bernoulli' «expr + »(i, 2), «expr + »(p, 2).choose «expr + »(i, 2)), «expr ^ »(n, «expr - »(p, i))), «expr↑ »(«expr + »(p, 2)))))] [":=", expr sum_congr rfl (λ
    i h, by rw [expr bernoulli_eq_bernoulli'_of_ne_one (succ_succ_ne_one i)] [])],
  calc
    «expr = »(«expr∑ in , »((k), Ico 1 n.succ, «expr ^ »(«expr↑ »(k), p.succ)), «expr∑ in , »((k), range n.succ, «expr ^ »(«expr↑ »(k), p.succ))) : by simp [] [] [] ["[", expr sum_Ico_eq_sub _ hle, ",", expr succ_ne_zero, "]"] [] []
    «expr = »(..., «expr + »(«expr∑ in , »((k), range n, «expr ^ »((k : exprℚ()), p.succ)), «expr ^ »(n, p.succ))) : by rw [expr sum_range_succ] []
    «expr = »(..., «expr + »(«expr∑ in , »((i), range p.succ.succ, f i), «expr ^ »(n, p.succ))) : by simp [] [] [] ["[", expr f, ",", expr sum_range_pow, "]"] [] []
    «expr = »(..., «expr + »(«expr + »(«expr + »(«expr∑ in , »((i), range p, f i.succ.succ), f 1), f 0), «expr ^ »(n, p.succ))) : by simp_rw ["[", expr sum_range_succ', "]"] []
    «expr = »(..., «expr + »(«expr + »(«expr∑ in , »((i), range p, f i.succ.succ), «expr + »(f 1, «expr ^ »(n, p.succ))), f 0)) : by ring []
    «expr = »(..., «expr + »(«expr + »(«expr∑ in , »((i), range p, f i.succ.succ), «expr * »(«expr / »(1, 2), «expr ^ »(n, p.succ))), f 0)) : by rw [expr h2] []
    «expr = »(..., «expr + »(«expr + »(«expr∑ in , »((i), range p, f' i.succ.succ), f' 1), f' 0)) : by { simp [] [] ["only"] ["[", expr f, ",", expr f', "]"] [] [],
      simpa [] [] [] ["[", expr h1, "]"] [] [] }
    «expr = »(..., «expr∑ in , »((i), range p.succ.succ, f' i)) : by simp_rw ["[", expr sum_range_succ', "]"] []
end

end Faulhaber

