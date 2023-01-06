/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll

! This file was ported from Lean 3 source module analysis.calculus.taylor
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.IteratedDeriv
import Mathbin.Analysis.Calculus.MeanValue
import Mathbin.Data.Polynomial.Basic
import Mathbin.Data.Polynomial.Module

/-!
# Taylor's theorem

This file defines the Taylor polynomial of a real function `f : ℝ → E`,
where `E` is a normed vector space over `ℝ` and proves Taylor's theorem,
which states that if `f` is sufficiently smooth, then
`f` can be approximated by the Taylor polynomial up to an explicit error term.

## Main definitions

* `taylor_coeff_within`: the Taylor coefficient using `deriv_within`
* `taylor_within`: the Taylor polynomial using `deriv_within`

## Main statements

* `taylor_mean_remainder`: Taylor's theorem with the general form of the remainder term
* `taylor_mean_remainder_lagrange`: Taylor's theorem with the Lagrange remainder
* `taylor_mean_remainder_cauchy`: Taylor's theorem with the Cauchy remainder
* `exists_taylor_mean_remainder_bound`: Taylor's theorem for vector valued functions with a
polynomial bound on the remainder

## TODO

* the Peano form of the remainder
* the integral form of the remainder
* Generalization to higher dimensions

## Tags

Taylor polynomial, Taylor's theorem
-/


open BigOperators Interval TopologicalSpace Nat

open Set

variable {𝕜 E F : Type _}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `k`th coefficient of the Taylor polynomial. -/
noncomputable def taylorCoeffWithin (f : ℝ → E) (k : ℕ) (s : Set ℝ) (x₀ : ℝ) : E :=
  (k ! : ℝ)⁻¹ • iteratedDerivWithin k f s x₀
#align taylor_coeff_within taylorCoeffWithin

/-- The Taylor polynomial with derivatives inside of a set `s`.

The Taylor polynomial is given by
$$∑_{k=0}^n \frac{(x - x₀)^k}{k!} f^{(k)}(x₀),$$
where $f^{(k)}(x₀)$ denotes the iterated derivative in the set `s`. -/
noncomputable def taylorWithin (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) : PolynomialModule ℝ E :=
  (Finset.range (n + 1)).Sum fun k =>
    PolynomialModule.comp (Polynomial.x - Polynomial.c x₀)
      (PolynomialModule.single ℝ k (taylorCoeffWithin f k s x₀))
#align taylor_within taylorWithin

/-- The Taylor polynomial with derivatives inside of a set `s` considered as a function `ℝ → E`-/
noncomputable def taylorWithinEval (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) : E :=
  PolynomialModule.eval x (taylorWithin f n s x₀)
#align taylor_within_eval taylorWithinEval

theorem taylor_within_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithin f (n + 1) s x₀ =
      taylorWithin f n s x₀ +
        PolynomialModule.comp (Polynomial.x - Polynomial.c x₀)
          (PolynomialModule.single ℝ (n + 1) (taylorCoeffWithin f (n + 1) s x₀)) :=
  by
  dsimp only [taylorWithin]
  rw [Finset.sum_range_succ]
#align taylor_within_succ taylor_within_succ

@[simp]
theorem taylor_within_eval_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f (n + 1) s x₀ x =
      taylorWithinEval f n s x₀ x +
        (((n + 1 : ℝ) * n !)⁻¹ * (x - x₀) ^ (n + 1)) • iteratedDerivWithin (n + 1) f s x₀ :=
  by
  simp_rw [taylorWithinEval, taylor_within_succ, LinearMap.map_add, PolynomialModule.comp_eval]
  congr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    PolynomialModule.eval_single, mul_inv_rev]
  dsimp only [taylorCoeffWithin]
  rw [← mul_smul, mul_comm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    mul_inv_rev]
#align taylor_within_eval_succ taylor_within_eval_succ

/-- The Taylor polynomial of order zero evaluates to `f x`. -/
@[simp]
theorem taylor_within_zero_eval (f : ℝ → E) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f 0 s x₀ x = f x₀ :=
  by
  dsimp only [taylorWithinEval]
  dsimp only [taylorWithin]
  dsimp only [taylorCoeffWithin]
  simp
#align taylor_within_zero_eval taylor_within_zero_eval

/-- Evaluating the Taylor polynomial at `x = x₀` yields `f x`. -/
@[simp]
theorem taylor_within_eval_self (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithinEval f n s x₀ x₀ = f x₀ :=
  by
  induction' n with k hk
  · exact taylor_within_zero_eval _ _ _ _
  simp [hk]
#align taylor_within_eval_self taylor_within_eval_self

theorem taylor_within_apply (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f n s x₀ x =
      ∑ k in Finset.range (n + 1), ((k ! : ℝ)⁻¹ * (x - x₀) ^ k) • iteratedDerivWithin k f s x₀ :=
  by
  induction' n with k hk
  · simp
  rw [taylor_within_eval_succ, Finset.sum_range_succ, hk]
  simp
#align taylor_within_apply taylor_within_apply

/-- If `f` is `n` times continuous differentiable on a set `s`, then the Taylor polynomial
  `taylor_within_eval f n s x₀ x` is continuous in `x₀`. -/
theorem continuous_on_taylor_within_eval {f : ℝ → E} {x : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hf : ContDiffOn ℝ n f s) :
    ContinuousOn (fun t => taylorWithinEval f n s t x) s :=
  by
  simp_rw [taylor_within_apply]
  refine' continuous_on_finset_sum (Finset.range (n + 1)) fun i hi => _
  refine' (continuous_on_const.mul ((continuous_on_const.sub continuous_on_id).pow _)).smul _
  rw [cont_diff_on_iff_continuous_on_differentiable_on_deriv hs] at hf
  cases hf
  specialize hf_left i
  simp only [Finset.mem_range] at hi
  refine' hf_left _
  simp only [WithTop.coe_le_coe]
  exact nat.lt_succ_iff.mp hi
#align continuous_on_taylor_within_eval continuous_on_taylor_within_eval

/-- Helper lemma for calculating the derivative of the monomial that appears in Taylor expansions.-/
theorem monomial_has_deriv_aux (t x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => (x - y) ^ (n + 1)) (-(n + 1) * (x - t) ^ n) t :=
  by
  simp_rw [sub_eq_neg_add]
  rw [← neg_one_mul, mul_comm (-1 : ℝ), mul_assoc, mul_comm (-1 : ℝ), ← mul_assoc]
  convert @HasDerivAt.pow _ _ _ _ _ (n + 1) ((has_deriv_at_id t).neg.AddConst x)
  simp only [Nat.cast_add, Nat.cast_one]
#align monomial_has_deriv_aux monomial_has_deriv_aux

theorem has_deriv_within_at_taylor_coeff_within {f : ℝ → E} {x y : ℝ} {k : ℕ} {s s' : Set ℝ}
    (hs'_unique : UniqueDiffWithinAt ℝ s' y) (hs' : s' ∈ 𝓝[s] y) (hy : y ∈ s') (h : s' ⊆ s)
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin (k + 1) f s) s') :
    HasDerivWithinAt
      (fun t => (((k + 1 : ℝ) * k !)⁻¹ * (x - t) ^ (k + 1)) • iteratedDerivWithin (k + 1) f s t)
      ((((k + 1 : ℝ) * k !)⁻¹ * (x - y) ^ (k + 1)) • iteratedDerivWithin (k + 2) f s y -
        ((k ! : ℝ)⁻¹ * (x - y) ^ k) • iteratedDerivWithin (k + 1) f s y)
      s' y :=
  by
  have hf'' :
    HasDerivWithinAt (fun t => iteratedDerivWithin (k + 1) f s t)
      (iteratedDerivWithin (k + 2) f s y) s' y :=
    by
    convert (hf' y hy).HasDerivWithinAt
    rw [iterated_deriv_within_succ (hs'_unique.mono h)]
    refine' (deriv_within_subset h hs'_unique _).symm
    exact (hf' y hy).antimono h hs'
  have :
    HasDerivWithinAt (fun t => ((k + 1 : ℝ) * k !)⁻¹ * (x - t) ^ (k + 1))
      (-((k ! : ℝ)⁻¹ * (x - y) ^ k)) s' y :=
    by
    -- Commuting the factors:
    have : -((k ! : ℝ)⁻¹ * (x - y) ^ k) = ((k + 1 : ℝ) * k !)⁻¹ * (-(k + 1) * (x - y) ^ k) :=
      by
      field_simp [Nat.cast_add_one_ne_zero k, Nat.factorial_ne_zero k]
      ring_nf
    rw [this]
    exact (monomial_has_deriv_aux y x _).HasDerivWithinAt.const_mul _
  convert this.smul hf''
  field_simp [Nat.cast_add_one_ne_zero k, Nat.factorial_ne_zero k]
  rw [neg_div, neg_smul, sub_eq_add_neg]
#align has_deriv_within_at_taylor_coeff_within has_deriv_within_at_taylor_coeff_within

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for arbitrary sets -/
theorem has_deriv_within_at_taylor_within_eval {f : ℝ → E} {x y : ℝ} {n : ℕ} {s s' : Set ℝ}
    (hs'_unique : UniqueDiffWithinAt ℝ s' y) (hs_unique : UniqueDiffOn ℝ s) (hs' : s' ∈ 𝓝[s] y)
    (hy : y ∈ s') (h : s' ⊆ s) (hf : ContDiffOn ℝ n f s)
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f s) s') :
    HasDerivWithinAt (fun t => taylorWithinEval f n s t x)
      (((n ! : ℝ)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f s y) s' y :=
  by
  induction' n with k hk
  · simp only [taylor_within_zero_eval, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
      mul_one, zero_add, one_smul]
    simp only [iterated_deriv_within_zero] at hf'
    rw [iterated_deriv_within_one hs_unique (h hy)]
    refine' HasDerivWithinAt.mono _ h
    refine' DifferentiableWithinAt.has_deriv_within_at _
    exact (hf' y hy).antimono h hs'
  simp_rw [Nat.add_succ, taylor_within_eval_succ]
  simp only [add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin k f s) s' :=
    by
    have coe_lt_succ : (k : WithTop ℕ) < k.succ :=
      by
      rw [WithTop.coe_lt_coe]
      exact lt_add_one k
    refine' DifferentiableOn.mono _ h
    exact hf.differentiable_on_iterated_deriv_within coe_lt_succ hs_unique
  specialize hk (ContDiffOn.of_succ hf) hdiff
  convert hk.add (has_deriv_within_at_taylor_coeff_within hs'_unique hs' hy h hf')
  exact (add_sub_cancel'_right _ _).symm
#align has_deriv_within_at_taylor_within_eval has_deriv_within_at_taylor_within_eval

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for open intervals -/
theorem taylor_within_eval_has_deriv_at_Ioo {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ} (hx : a < b)
    (ht : t ∈ Ioo a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b)) :
    HasDerivAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) t :=
  haveI h_nhds := IsOpen.mem_nhds is_open_Ioo ht
  (has_deriv_within_at_taylor_within_eval (uniqueDiffWithinAtIoo ht) (unique_diff_on_Icc hx)
        (nhds_within_le_nhds h_nhds) ht Ioo_subset_Icc_self hf hf').HasDerivAt
    h_nhds
#align taylor_within_eval_has_deriv_at_Ioo taylor_within_eval_has_deriv_at_Ioo

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for closed intervals -/
theorem has_deriv_within_taylor_within_eval_at_Icc {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ}
    (hx : a < b) (ht : t ∈ Icc a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Icc a b)) :
    HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a b) t :=
  has_deriv_within_at_taylor_within_eval (unique_diff_on_Icc hx t ht) (unique_diff_on_Icc hx)
    self_mem_nhds_within ht rfl.Subset hf hf'
#align has_deriv_within_taylor_within_eval_at_Icc has_deriv_within_taylor_within_eval_at_Icc

/-! ### Taylor's theorem with mean value type remainder estimate -/


/-- **Taylor's theorem** with the general mean value form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable in the closed set `Icc x₀ x` and
`n+1`-times differentiable on the open set `Ioo x₀ x`, and `g` is a differentiable function on
`Ioo x₀ x` and continuous on `Icc x₀ x`. Then there exists a `x' ∈ Ioo x₀ x` such that
$$f(x) - (P_n f)(x₀, x) = \frac{(x - x')^n}{n!} \frac{g(x) - g(x₀)}{g' x'},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$. -/
theorem taylor_mean_remainder {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x))
    (gcont : ContinuousOn g (Icc x₀ x))
    (gdiff : ∀ x_1 : ℝ, x_1 ∈ Ioo x₀ x → HasDerivAt g (g' x_1) x_1)
    (g'_ne : ∀ x_1 : ℝ, x_1 ∈ Ioo x₀ x → g' x_1 ≠ 0) :
    ∃ (x' : ℝ)(hx' : x' ∈ Ioo x₀ x),
      f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
        ((x - x') ^ n / n ! * (g x - g x₀) / g' x') • iteratedDerivWithin (n + 1) f (Icc x₀ x) x' :=
  by
  -- We apply the mean value theorem
  rcases exists_ratio_has_deriv_at_eq_ratio_slope (fun t => taylorWithinEval f n (Icc x₀ x) t x)
      (fun t => ((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc x₀ x) t) hx
      (continuous_on_taylor_within_eval (unique_diff_on_Icc hx) hf)
      (fun _ hy => taylor_within_eval_has_deriv_at_Ioo x hx hy hf hf') g g' gcont gdiff with
    ⟨y, hy, h⟩
  use y, hy
  -- The rest is simplifications and trivial calculations
  simp only [taylor_within_eval_self] at h
  rw [mul_comm, ← div_left_inj' (g'_ne y hy), mul_div_cancel _ (g'_ne y hy)] at h
  rw [← h]
  field_simp [g'_ne y hy, n.factorial_ne_zero]
  ring
#align taylor_mean_remainder taylor_mean_remainder

/-- **Taylor's theorem** with the Lagrange form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable in the closed set `Icc x₀ x` and
`n+1`-times differentiable on the open set `Ioo x₀ x`. Then there exists a `x' ∈ Ioo x₀ x` such that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x₀)^{n+1}}{(n+1)!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
theorem taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ (x' : ℝ)(hx' : x' ∈ Ioo x₀ x),
      f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
        iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! :=
  by
  have gcont : ContinuousOn (fun t : ℝ => (x - t) ^ (n + 1)) (Icc x₀ x) :=
    by
    refine' Continuous.continuous_on _
    continuity
  have xy_ne : ∀ y : ℝ, y ∈ Ioo x₀ x → (x - y) ^ n ≠ 0 :=
    by
    intro y hy
    refine' pow_ne_zero _ _
    rw [mem_Ioo] at hy
    rw [sub_ne_zero]
    exact hy.2.Ne.symm
  have hg' : ∀ y : ℝ, y ∈ Ioo x₀ x → -(↑n + 1) * (x - y) ^ n ≠ 0 := fun y hy =>
    mul_ne_zero (neg_ne_zero.mpr (Nat.cast_add_one_ne_zero n)) (xy_ne y hy)
  -- We apply the general theorem with g(t) = (x - t)^(n+1)
  rcases taylor_mean_remainder hx hf hf' gcont (fun y _ => monomial_has_deriv_aux y x _) hg' with
    ⟨y, hy, h⟩
  use y, hy
  simp only [sub_self, zero_pow', Ne.def, Nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h
  rw [h, neg_div, ← div_neg, neg_mul, neg_neg]
  field_simp [n.cast_add_one_ne_zero, n.factorial_ne_zero, xy_ne y hy]
  ring
#align taylor_mean_remainder_lagrange taylor_mean_remainder_lagrange

/-- **Taylor's theorem** with the Cauchy form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc x₀ x` and
`n+1`-times differentiable on the open set `Ioo x₀ x`. Then there exists a `x' ∈ Ioo x₀ x` such that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x')^n (x-x₀)}{n!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
theorem taylor_mean_remainder_cauchy {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ < x)
    (hf : ContDiffOn ℝ n f (Icc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc x₀ x)) (Ioo x₀ x)) :
    ∃ (x' : ℝ)(hx' : x' ∈ Ioo x₀ x),
      f x - taylorWithinEval f n (Icc x₀ x) x₀ x =
        iteratedDerivWithin (n + 1) f (Icc x₀ x) x' * (x - x') ^ n / n ! * (x - x₀) :=
  by
  have gcont : ContinuousOn id (Icc x₀ x) := Continuous.continuous_on (by continuity)
  have gdiff : ∀ x_1 : ℝ, x_1 ∈ Ioo x₀ x → HasDerivAt id ((fun t : ℝ => (1 : ℝ)) x_1) x_1 :=
    fun _ _ => has_deriv_at_id _
  -- We apply the general theorem with g = id
  rcases taylor_mean_remainder hx hf hf' gcont gdiff fun _ _ => by simp with ⟨y, hy, h⟩
  use y, hy
  rw [h]
  field_simp [n.factorial_ne_zero]
  ring
#align taylor_mean_remainder_cauchy taylor_mean_remainder_cauchy

/-- **Taylor's theorem** with a polynomial bound on the remainder

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc a b`.
The difference of `f` and its `n`-th Taylor polynomial can be estimated by
`C * (x - a)^(n+1) / n!` where `C` is a bound for the `n+1`-th iterated derivative of `f`. -/
theorem taylor_mean_remainder_bound {f : ℝ → E} {a b C x : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx : x ∈ Icc a b)
    (hC : ∀ y ∈ Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤ C) :
    ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / n ! :=
  by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · rw [Icc_self, mem_singleton_iff] at hx
    simp [hx]
  -- The nth iterated derivative is differentiable
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Icc a b) :=
    hf.differentiable_on_iterated_deriv_within (with_top.coe_lt_coe.mpr n.lt_succ_self)
      (unique_diff_on_Icc h)
  -- We can uniformly bound the derivative of the Taylor polynomial
  have h' :
    ∀ (y : ℝ) (hy : y ∈ Ico a x),
      ‖((n ! : ℝ)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤
        (n ! : ℝ)⁻¹ * |x - a| ^ n * C :=
    by
    rintro y ⟨hay, hyx⟩
    rw [norm_smul, Real.norm_eq_abs]
    -- Estimate the iterated derivative by `C`
    refine' mul_le_mul _ (hC y ⟨hay, hyx.le.trans hx.2⟩) (by positivity) (by positivity)
    -- The rest is a trivial calculation
    rw [abs_mul, abs_pow, abs_inv, Nat.abs_cast]
    mono* with 0 ≤ (n ! : ℝ)⁻¹
    any_goals positivity
    linarith [hx.1, hyx]
  -- Apply the mean value theorem for vector valued functions:
  have A :
    ∀ t ∈ Icc a x,
      HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
        (((↑n !)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a x) t :=
    by
    intro t ht
    have I : Icc a x ⊆ Icc a b := Icc_subset_Icc_right hx.2
    exact (has_deriv_within_taylor_within_eval_at_Icc x h (I ht) hf.of_succ hf').mono I
  have := norm_image_sub_le_of_norm_deriv_le_segment' A h' x (right_mem_Icc.2 hx.1)
  simp only [taylor_within_eval_self] at this
  refine' this.trans_eq _
  -- The rest is a trivial calculation
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
  ring
#align taylor_mean_remainder_bound taylor_mean_remainder_bound

/-- **Taylor's theorem** with a polynomial bound on the remainder

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc a b`.
There exists a constant `C` such that for all `x ∈ Icc a b` the difference of `f` and its `n`-th
Taylor polynomial can be estimated by `C * (x - a)^(n+1)`. -/
theorem exists_taylor_mean_remainder_bound {f : ℝ → E} {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) :
    ∃ C, ∀ x ∈ Icc a b, ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) :=
  by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · refine' ⟨0, fun x hx => _⟩
    have : a = x := by simpa [← le_antisymm_iff] using hx
    simp [← this]
  -- We estimate by the supremum of the norm of the iterated derivative
  let g : ℝ → ℝ := fun y => ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖
  use SupSet.supₛ (g '' Icc a b) / n !
  intro x hx
  rw [div_mul_eq_mul_div₀]
  refine' taylor_mean_remainder_bound hab hf hx fun y => _
  exact
    (hf.continuous_on_iterated_deriv_within rfl.le <| unique_diff_on_Icc h).norm.le_Sup_image_Icc
#align exists_taylor_mean_remainder_bound exists_taylor_mean_remainder_bound

