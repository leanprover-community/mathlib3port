/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn

! This file was ported from Lean 3 source module analysis.calculus.specific_functions
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.IteratedDeriv
import Mathbin.Analysis.InnerProductSpace.EuclideanDist
import Mathbin.MeasureTheory.Function.LocallyIntegrable
import Mathbin.MeasureTheory.Integral.SetIntegral

/-!
# Infinitely smooth bump function

In this file we construct several infinitely smooth functions with properties that an analytic
function cannot have:

* `exp_neg_inv_glue` is equal to zero for `x ≤ 0` and is strictly positive otherwise; it is given by
  `x ↦ exp (-1/x)` for `x > 0`;

* `real.smooth_transition` is equal to zero for `x ≤ 0` and is equal to one for `x ≥ 1`; it is given
  by `exp_neg_inv_glue x / (exp_neg_inv_glue x + exp_neg_inv_glue (1 - x))`;

* `f : cont_diff_bump_of_inner c`, where `c` is a point in an inner product space, is
  a bundled smooth function such that

  - `f` is equal to `1` in `metric.closed_ball c f.r`;
  - `support f = metric.ball c f.R`;
  - `0 ≤ f x ≤ 1` for all `x`.

  The structure `cont_diff_bump_of_inner` contains the data required to construct the
  function: real numbers `r`, `R`, and proofs of `0 < r < R`. The function itself is available
  through `coe_fn`.

* If `f : cont_diff_bump_of_inner c` and `μ` is a measure on the domain of `f`, then `f.normed μ`
  is a smooth bump function with integral `1` w.r.t. `μ`.

* `f : cont_diff_bump c`, where `c` is a point in a finite dimensional real vector space, is a
  bundled smooth function such that

  - `f` is equal to `1` in `euclidean.closed_ball c f.r`;
  - `support f = euclidean.ball c f.R`;
  - `0 ≤ f x ≤ 1` for all `x`.

  The structure `cont_diff_bump` contains the data required to construct the function: real
  numbers `r`, `R`, and proofs of `0 < r < R`. The function itself is available through `coe_fn`.
-/


noncomputable section

open Classical Topology

open Polynomial Real Filter Set Function

open Polynomial

/-- `exp_neg_inv_glue` is the real function given by `x ↦ exp (-1/x)` for `x > 0` and `0`
for `x ≤ 0`. It is a basic building block to construct smooth partitions of unity. Its main property
is that it vanishes for `x ≤ 0`, it is positive for `x > 0`, and the junction between the two
behaviors is flat enough to retain smoothness. The fact that this function is `C^∞` is proved in
`exp_neg_inv_glue.smooth`. -/
def expNegInvGlue (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else exp (-x⁻¹)
#align exp_neg_inv_glue expNegInvGlue

namespace expNegInvGlue

/-- Our goal is to prove that `exp_neg_inv_glue` is `C^∞`. For this, we compute its successive
derivatives for `x > 0`. The `n`-th derivative is of the form `P_aux n (x) exp(-1/x) / x^(2 n)`,
where `P_aux n` is computed inductively. -/
noncomputable def pAux : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => x ^ 2 * (P_aux n).derivative + (1 - c ↑(2 * n) * x) * P_aux n
#align exp_neg_inv_glue.P_aux expNegInvGlue.pAux

/-- Formula for the `n`-th derivative of `exp_neg_inv_glue`, as an auxiliary function `f_aux`. -/
def fAux (n : ℕ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else (pAux n).eval x * exp (-x⁻¹) / x ^ (2 * n)
#align exp_neg_inv_glue.f_aux expNegInvGlue.fAux

/-- The `0`-th auxiliary function `f_aux 0` coincides with `exp_neg_inv_glue`, by definition. -/
theorem fAux_zero_eq : fAux 0 = expNegInvGlue :=
  by
  ext x
  by_cases h : x ≤ 0
  · simp [expNegInvGlue, f_aux, h]
  · simp [h, expNegInvGlue, f_aux, ne_of_gt (not_le.1 h), P_aux]
#align exp_neg_inv_glue.f_aux_zero_eq expNegInvGlue.fAux_zero_eq

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[["[", expr pow_ne_zero, "]"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error -/
/-- For positive values, the derivative of the `n`-th auxiliary function `f_aux n`
(given in this statement in unfolded form) is the `n+1`-th auxiliary function, since
the polynomial `P_aux (n+1)` was chosen precisely to ensure this. -/
theorem f_aux_deriv (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun x => (pAux n).eval x * exp (-x⁻¹) / x ^ (2 * n))
      ((pAux (n + 1)).eval x * exp (-x⁻¹) / x ^ (2 * (n + 1))) x :=
  by
  simp only [P_aux, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_one]
  convert
    (((P_aux n).HasDerivAt x).mul ((has_deriv_at_exp _).comp x (hasDerivAt_inv hx).neg)).div
      (hasDerivAt_pow (2 * n) x) (pow_ne_zero _ hx) using
    1
  rw [div_eq_div_iff]
  · have := pow_ne_zero 2 hx
    field_simp only
    cases n
    · simp only [mul_zero, Nat.cast_zero, mul_one]
      ring
    · rw [(id rfl : 2 * n.succ - 1 = 2 * n + 1)]
      ring
  all_goals
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\"[\", expr pow_ne_zero, \"]\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error"
#align exp_neg_inv_glue.f_aux_deriv expNegInvGlue.f_aux_deriv

/-- For positive values, the derivative of the `n`-th auxiliary function `f_aux n`
is the `n+1`-th auxiliary function. -/
theorem fAux_deriv_pos (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fAux n) ((pAux (n + 1)).eval x * exp (-x⁻¹) / x ^ (2 * (n + 1))) x :=
  by
  apply (f_aux_deriv n x (ne_of_gt hx)).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hx]with _ hy
  simp [f_aux, hy.not_le]
#align exp_neg_inv_glue.f_aux_deriv_pos expNegInvGlue.fAux_deriv_pos

/-- To get differentiability at `0` of the auxiliary functions, we need to know that their limit
is `0`, to be able to apply general differentiability extension theorems. This limit is checked in
this lemma. -/
theorem f_aux_limit (n : ℕ) :
    Tendsto (fun x => (pAux n).eval x * exp (-x⁻¹) / x ^ (2 * n)) (𝓝[>] 0) (𝓝 0) :=
  by
  have A : tendsto (fun x => (P_aux n).eval x) (𝓝[>] 0) (𝓝 ((P_aux n).eval 0)) :=
    (P_aux n).ContinuousWithinAt
  have B : tendsto (fun x => exp (-x⁻¹) / x ^ (2 * n)) (𝓝[>] 0) (𝓝 0) :=
    by
    convert (tendsto_pow_mul_exp_neg_at_top_nhds_0 (2 * n)).comp tendsto_inv_zero_atTop
    ext x
    field_simp
  convert A.mul B <;> simp [mul_div_assoc]
#align exp_neg_inv_glue.f_aux_limit expNegInvGlue.f_aux_limit

/-- Deduce from the limiting behavior at `0` of its derivative and general differentiability
extension theorems that the auxiliary function `f_aux n` is differentiable at `0`,
with derivative `0`. -/
theorem fAux_deriv_zero (n : ℕ) : HasDerivAt (fAux n) 0 0 :=
  by
  -- we check separately differentiability on the left and on the right
  have A : HasDerivWithinAt (f_aux n) (0 : ℝ) (Iic 0) 0 :=
    by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).HasDerivWithinAt.congr
    · intro y hy
      simp at hy
      simp [f_aux, hy]
    · simp [f_aux, le_refl]
  have B : HasDerivWithinAt (f_aux n) (0 : ℝ) (Ici 0) 0 :=
    by
    have diff : DifferentiableOn ℝ (f_aux n) (Ioi 0) := fun x hx =>
      (f_aux_deriv_pos n x hx).DifferentiableAt.DifferentiableWithinAt
    -- next line is the nontrivial bit of this proof, appealing to differentiability
    -- extension results.
    apply has_deriv_at_interval_left_endpoint_of_tendsto_deriv diff _ self_mem_nhdsWithin
    · refine' (f_aux_limit (n + 1)).congr' _
      apply mem_of_superset self_mem_nhdsWithin fun x hx => _
      simp [(f_aux_deriv_pos n x hx).deriv]
    · have : f_aux n 0 = 0 := by simp [f_aux, le_refl]
      simp only [ContinuousWithinAt, this]
      refine' (f_aux_limit n).congr' _
      apply mem_of_superset self_mem_nhdsWithin fun x hx => _
      have : ¬x ≤ 0 := by simpa using hx
      simp [f_aux, this]
  simpa using A.union B
#align exp_neg_inv_glue.f_aux_deriv_zero expNegInvGlue.fAux_deriv_zero

/-- At every point, the auxiliary function `f_aux n` has a derivative which is
equal to `f_aux (n+1)`. -/
theorem fAux_hasDerivAt (n : ℕ) (x : ℝ) : HasDerivAt (fAux n) (fAux (n + 1) x) x :=
  by
  -- check separately the result for `x < 0`, where it is trivial, for `x > 0`, where it is done
  -- in `f_aux_deriv_pos`, and for `x = 0`, done in
  -- `f_aux_deriv_zero`.
  rcases lt_trichotomy x 0 with (hx | hx | hx)
  · have : f_aux (n + 1) x = 0 := by simp [f_aux, le_of_lt hx]
    rw [this]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx]with _ hy
    simp [f_aux, hy.le]
  · have : f_aux (n + 1) 0 = 0 := by simp [f_aux, le_refl]
    rw [hx, this]
    exact f_aux_deriv_zero n
  · have : f_aux (n + 1) x = (P_aux (n + 1)).eval x * exp (-x⁻¹) / x ^ (2 * (n + 1)) := by
      simp [f_aux, not_le_of_gt hx]
    rw [this]
    exact f_aux_deriv_pos n x hx
#align exp_neg_inv_glue.f_aux_has_deriv_at expNegInvGlue.fAux_hasDerivAt

/-- The successive derivatives of the auxiliary function `f_aux 0` are the
functions `f_aux n`, by induction. -/
theorem fAux_iteratedDeriv (n : ℕ) : iteratedDeriv n (fAux 0) = fAux n :=
  by
  induction' n with n IH
  · simp
  · simp [iteratedDeriv_succ, IH]
    ext x
    exact (f_aux_has_deriv_at n x).deriv
#align exp_neg_inv_glue.f_aux_iterated_deriv expNegInvGlue.fAux_iteratedDeriv

/-- The function `exp_neg_inv_glue` is smooth. -/
protected theorem contDiff {n} : ContDiff ℝ n expNegInvGlue :=
  by
  rw [← f_aux_zero_eq]
  apply contDiff_of_differentiable_iteratedDeriv fun m hm => _
  rw [f_aux_iterated_deriv m]
  exact fun x => (f_aux_has_deriv_at m x).DifferentiableAt
#align exp_neg_inv_glue.cont_diff expNegInvGlue.contDiff

/-- The function `exp_neg_inv_glue` vanishes on `(-∞, 0]`. -/
theorem zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : expNegInvGlue x = 0 := by simp [expNegInvGlue, hx]
#align exp_neg_inv_glue.zero_of_nonpos expNegInvGlue.zero_of_nonpos

/-- The function `exp_neg_inv_glue` is positive on `(0, +∞)`. -/
theorem pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < expNegInvGlue x := by
  simp [expNegInvGlue, not_le.2 hx, exp_pos]
#align exp_neg_inv_glue.pos_of_pos expNegInvGlue.pos_of_pos

/-- The function exp_neg_inv_glue` is nonnegative. -/
theorem nonneg (x : ℝ) : 0 ≤ expNegInvGlue x :=
  by
  cases le_or_gt x 0
  · exact ge_of_eq (zero_of_nonpos h)
  · exact le_of_lt (pos_of_pos h)
#align exp_neg_inv_glue.nonneg expNegInvGlue.nonneg

end expNegInvGlue

/-- An infinitely smooth function `f : ℝ → ℝ` such that `f x = 0` for `x ≤ 0`,
`f x = 1` for `1 ≤ x`, and `0 < f x < 1` for `0 < x < 1`. -/
def Real.smoothTransition (x : ℝ) : ℝ :=
  expNegInvGlue x / (expNegInvGlue x + expNegInvGlue (1 - x))
#align real.smooth_transition Real.smoothTransition

namespace Real

namespace SmoothTransition

variable {x : ℝ}

open expNegInvGlue

theorem pos_denom (x) : 0 < expNegInvGlue x + expNegInvGlue (1 - x) :=
  (zero_lt_one.lt_or_lt x).elim (fun hx => add_pos_of_pos_of_nonneg (pos_of_pos hx) (nonneg _))
    fun hx => add_pos_of_nonneg_of_pos (nonneg _) (pos_of_pos <| sub_pos.2 hx)
#align real.smooth_transition.pos_denom Real.smoothTransition.pos_denom

theorem one_of_one_le (h : 1 ≤ x) : smoothTransition x = 1 :=
  (div_eq_one_iff_eq <| (pos_denom x).ne').2 <| by rw [zero_of_nonpos (sub_nonpos.2 h), add_zero]
#align real.smooth_transition.one_of_one_le Real.smoothTransition.one_of_one_le

theorem zero_of_nonpos (h : x ≤ 0) : smoothTransition x = 0 := by
  rw [smooth_transition, zero_of_nonpos h, zero_div]
#align real.smooth_transition.zero_of_nonpos Real.smoothTransition.zero_of_nonpos

@[simp]
protected theorem zero : smoothTransition 0 = 0 :=
  zero_of_nonpos le_rfl
#align real.smooth_transition.zero Real.smoothTransition.zero

@[simp]
protected theorem one : smoothTransition 1 = 1 :=
  one_of_one_le le_rfl
#align real.smooth_transition.one Real.smoothTransition.one

theorem le_one (x : ℝ) : smoothTransition x ≤ 1 :=
  (div_le_one (pos_denom x)).2 <| le_add_of_nonneg_right (nonneg _)
#align real.smooth_transition.le_one Real.smoothTransition.le_one

theorem nonneg (x : ℝ) : 0 ≤ smoothTransition x :=
  div_nonneg (expNegInvGlue.nonneg _) (pos_denom x).le
#align real.smooth_transition.nonneg Real.smoothTransition.nonneg

theorem lt_one_of_lt_one (h : x < 1) : smoothTransition x < 1 :=
  (div_lt_one <| pos_denom x).2 <| lt_add_of_pos_right _ <| pos_of_pos <| sub_pos.2 h
#align real.smooth_transition.lt_one_of_lt_one Real.smoothTransition.lt_one_of_lt_one

theorem pos_of_pos (h : 0 < x) : 0 < smoothTransition x :=
  div_pos (expNegInvGlue.pos_of_pos h) (pos_denom x)
#align real.smooth_transition.pos_of_pos Real.smoothTransition.pos_of_pos

protected theorem contDiff {n} : ContDiff ℝ n smoothTransition :=
  expNegInvGlue.contDiff.div
    (expNegInvGlue.contDiff.add <| expNegInvGlue.contDiff.comp <| contDiff_const.sub contDiff_id)
    fun x => (pos_denom x).ne'
#align real.smooth_transition.cont_diff Real.smoothTransition.contDiff

protected theorem contDiffAt {x n} : ContDiffAt ℝ n smoothTransition x :=
  smoothTransition.contDiff.ContDiffAt
#align real.smooth_transition.cont_diff_at Real.smoothTransition.contDiffAt

protected theorem continuous : Continuous smoothTransition :=
  (@smoothTransition.contDiff 0).Continuous
#align real.smooth_transition.continuous Real.smoothTransition.continuous

end SmoothTransition

end Real

variable {E X : Type _}

/-- `f : cont_diff_bump_of_inner c`, where `c` is a point in an inner product space, is a
bundled smooth function such that

- `f` is equal to `1` in `metric.closed_ball c f.r`;
- `support f = metric.ball c f.R`;
- `0 ≤ f x ≤ 1` for all `x`.

The structure `cont_diff_bump_of_inner` contains the data required to construct the function:
real numbers `r`, `R`, and proofs of `0 < r < R`. The function itself is available through
`coe_fn`. -/
structure ContDiffBumpOfInner (c : E) where
  (R r : ℝ)
  r_pos : 0 < r
  r_lt_r : r < R
#align cont_diff_bump_of_inner ContDiffBumpOfInner

namespace ContDiffBumpOfInner

/- warning: cont_diff_bump_of_inner.R_pos clashes with cont_diff_bump_of_inner.r_pos -> ContDiffBumpOfInner.r_pos
Case conversion may be inaccurate. Consider using '#align cont_diff_bump_of_inner.R_pos ContDiffBumpOfInner.r_posₓ'. -/
#print ContDiffBumpOfInner.r_pos /-
theorem r_pos {c : E} (f : ContDiffBumpOfInner c) : 0 < f.r :=
  f.r_pos.trans f.r_lt_r
#align cont_diff_bump_of_inner.R_pos ContDiffBumpOfInner.r_pos
-/

instance (c : E) : Inhabited (ContDiffBumpOfInner c) :=
  ⟨⟨1, 2, zero_lt_one, one_lt_two⟩⟩

variable [InnerProductSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {c : E} (f : ContDiffBumpOfInner c) {x : E} {n : ℕ∞}

/-- The function defined by `f : cont_diff_bump_of_inner c`. Use automatic coercion to
function instead. -/
def toFun (f : ContDiffBumpOfInner c) : E → ℝ := fun x =>
  Real.smoothTransition ((f.r - dist x c) / (f.r - f.R))
#align cont_diff_bump_of_inner.to_fun ContDiffBumpOfInner.toFun

instance : CoeFun (ContDiffBumpOfInner c) fun _ => E → ℝ :=
  ⟨toFun⟩

protected theorem def (x : E) : f x = Real.smoothTransition ((f.r - dist x c) / (f.r - f.R)) :=
  rfl
#align cont_diff_bump_of_inner.def ContDiffBumpOfInner.def

protected theorem sub (x : E) : f (c - x) = f (c + x) := by
  simp_rw [f.def, dist_self_sub_left, dist_self_add_left]
#align cont_diff_bump_of_inner.sub ContDiffBumpOfInner.sub

protected theorem neg (f : ContDiffBumpOfInner (0 : E)) (x : E) : f (-x) = f x := by
  simp_rw [← zero_sub, f.sub, zero_add]
#align cont_diff_bump_of_inner.neg ContDiffBumpOfInner.neg

open Real (smoothTransition)

open Real.smoothTransition Metric

theorem one_of_mem_closedBall (hx : x ∈ closedBall c f.R) : f x = 1 :=
  one_of_one_le <| (one_le_div (sub_pos.2 f.r_lt_r)).2 <| sub_le_sub_left hx _
#align cont_diff_bump_of_inner.one_of_mem_closed_ball ContDiffBumpOfInner.one_of_mem_closedBall

theorem nonneg : 0 ≤ f x :=
  nonneg _
#align cont_diff_bump_of_inner.nonneg ContDiffBumpOfInner.nonneg

/-- A version of `cont_diff_bump_of_inner.nonneg` with `x` explicit -/
theorem nonneg' (x : E) : 0 ≤ f x :=
  f.NonNeg
#align cont_diff_bump_of_inner.nonneg' ContDiffBumpOfInner.nonneg'

theorem le_one : f x ≤ 1 :=
  le_one _
#align cont_diff_bump_of_inner.le_one ContDiffBumpOfInner.le_one

theorem pos_of_mem_ball (hx : x ∈ ball c f.r) : 0 < f x :=
  pos_of_pos <| div_pos (sub_pos.2 hx) (sub_pos.2 f.r_lt_r)
#align cont_diff_bump_of_inner.pos_of_mem_ball ContDiffBumpOfInner.pos_of_mem_ball

theorem lt_one_of_lt_dist (h : f.R < dist x c) : f x < 1 :=
  lt_one_of_lt_one <| (div_lt_one (sub_pos.2 f.r_lt_r)).2 <| sub_lt_sub_left h _
#align cont_diff_bump_of_inner.lt_one_of_lt_dist ContDiffBumpOfInner.lt_one_of_lt_dist

theorem zero_of_le_dist (hx : f.r ≤ dist x c) : f x = 0 :=
  zero_of_nonpos <| div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx) (sub_nonneg.2 f.r_lt_r.le)
#align cont_diff_bump_of_inner.zero_of_le_dist ContDiffBumpOfInner.zero_of_le_dist

theorem support_eq : support (f : E → ℝ) = Metric.ball c f.r :=
  by
  ext x
  suffices f x ≠ 0 ↔ dist x c < f.R by simpa [mem_support]
  cases' lt_or_le (dist x c) f.R with hx hx
  · simp [hx, (f.pos_of_mem_ball hx).ne']
  · simp [hx.not_lt, f.zero_of_le_dist hx]
#align cont_diff_bump_of_inner.support_eq ContDiffBumpOfInner.support_eq

theorem tsupport_eq : tsupport f = closedBall c f.r := by
  simp_rw [tsupport, f.support_eq, closure_ball _ f.R_pos.ne']
#align cont_diff_bump_of_inner.tsupport_eq ContDiffBumpOfInner.tsupport_eq

protected theorem hasCompactSupport [FiniteDimensional ℝ E] : HasCompactSupport f := by
  simp_rw [HasCompactSupport, f.tsupport_eq, is_compact_closed_ball]
#align cont_diff_bump_of_inner.has_compact_support ContDiffBumpOfInner.hasCompactSupport

theorem eventuallyEq_one_of_mem_ball (h : x ∈ ball c f.R) : f =ᶠ[𝓝 x] 1 :=
  ((isOpen_lt (continuous_id.dist continuous_const) continuous_const).eventually_mem h).mono
    fun z hz => f.one_of_mem_closedBall (le_of_lt hz)
#align cont_diff_bump_of_inner.eventually_eq_one_of_mem_ball ContDiffBumpOfInner.eventuallyEq_one_of_mem_ball

theorem eventuallyEq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventuallyEq_one_of_mem_ball (mem_ball_self f.r_pos)
#align cont_diff_bump_of_inner.eventually_eq_one ContDiffBumpOfInner.eventuallyEq_one

/-- `cont_diff_bump` is `𝒞ⁿ` in all its arguments. -/
protected theorem ContDiffAt.cont_diff_bump {c g : X → E} {f : ∀ x, ContDiffBumpOfInner (c x)}
    {x : X} (hc : ContDiffAt ℝ n c x) (hr : ContDiffAt ℝ n (fun x => (f x).R) x)
    (hR : ContDiffAt ℝ n (fun x => (f x).r) x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun x => f x (g x)) x :=
  by
  rcases eq_or_ne (g x) (c x) with (hx | hx)
  · have : (fun x => f x (g x)) =ᶠ[𝓝 x] fun x => 1 :=
      by
      have : dist (g x) (c x) < (f x).R := by simp_rw [hx, dist_self, (f x).r_pos]
      have :=
        ContinuousAt.eventually_lt (hg.continuous_at.dist hc.continuous_at) hr.continuous_at this
      exact eventually_of_mem this fun x hx => (f x).one_of_mem_closedBall (mem_set_of_eq.mp hx).le
    exact cont_diff_at_const.congr_of_eventually_eq this
  · refine' real.smooth_transition.cont_diff_at.comp x _
    refine' (hR.sub <| hg.dist hc hx).div (hR.sub hr) (sub_pos.mpr (f x).r_lt_r).ne'
#align cont_diff_at.cont_diff_bump ContDiffAt.cont_diff_bump

theorem ContDiff.contDiff_bump {c g : X → E} {f : ∀ x, ContDiffBumpOfInner (c x)}
    (hc : ContDiff ℝ n c) (hr : ContDiff ℝ n fun x => (f x).R) (hR : ContDiff ℝ n fun x => (f x).r)
    (hg : ContDiff ℝ n g) : ContDiff ℝ n fun x => f x (g x) :=
  by
  rw [contDiff_iff_contDiffAt] at *
  exact fun x => (hc x).cont_diff_bump (hr x) (hR x) (hg x)
#align cont_diff.cont_diff_bump ContDiff.contDiff_bump

protected theorem contDiff : ContDiff ℝ n f :=
  contDiff_const.cont_diff_bump contDiff_const contDiff_const contDiff_id
#align cont_diff_bump_of_inner.cont_diff ContDiffBumpOfInner.contDiff

protected theorem contDiffAt : ContDiffAt ℝ n f x :=
  f.ContDiff.ContDiffAt
#align cont_diff_bump_of_inner.cont_diff_at ContDiffBumpOfInner.contDiffAt

protected theorem contDiffWithinAt {s : Set E} : ContDiffWithinAt ℝ n f s x :=
  f.ContDiffAt.ContDiffWithinAt
#align cont_diff_bump_of_inner.cont_diff_within_at ContDiffBumpOfInner.contDiffWithinAt

protected theorem continuous : Continuous f :=
  contDiff_zero.mp f.ContDiff
#align cont_diff_bump_of_inner.continuous ContDiffBumpOfInner.continuous

open MeasureTheory

variable [MeasurableSpace E] {μ : Measure E}

/-- A bump function normed so that `∫ x, f.normed μ x ∂μ = 1`. -/
protected def normed (μ : Measure E) : E → ℝ := fun x => f x / ∫ x, f x ∂μ
#align cont_diff_bump_of_inner.normed ContDiffBumpOfInner.normed

theorem normed_def {μ : Measure E} (x : E) : f.normed μ x = f x / ∫ x, f x ∂μ :=
  rfl
#align cont_diff_bump_of_inner.normed_def ContDiffBumpOfInner.normed_def

theorem nonneg_normed (x : E) : 0 ≤ f.normed μ x :=
  div_nonneg f.NonNeg <| integral_nonneg f.nonneg'
#align cont_diff_bump_of_inner.nonneg_normed ContDiffBumpOfInner.nonneg_normed

theorem contDiff_normed {n : ℕ∞} : ContDiff ℝ n (f.normed μ) :=
  f.ContDiff.div_const
#align cont_diff_bump_of_inner.cont_diff_normed ContDiffBumpOfInner.contDiff_normed

theorem continuous_normed : Continuous (f.normed μ) :=
  f.Continuous.div_const
#align cont_diff_bump_of_inner.continuous_normed ContDiffBumpOfInner.continuous_normed

theorem normed_sub (x : E) : f.normed μ (c - x) = f.normed μ (c + x) := by
  simp_rw [f.normed_def, f.sub]
#align cont_diff_bump_of_inner.normed_sub ContDiffBumpOfInner.normed_sub

theorem normed_neg (f : ContDiffBumpOfInner (0 : E)) (x : E) : f.normed μ (-x) = f.normed μ x := by
  simp_rw [f.normed_def, f.neg]
#align cont_diff_bump_of_inner.normed_neg ContDiffBumpOfInner.normed_neg

variable [BorelSpace E] [FiniteDimensional ℝ E] [IsLocallyFiniteMeasure μ]

protected theorem integrable : Integrable f μ :=
  f.Continuous.integrableOfHasCompactSupport f.HasCompactSupport
#align cont_diff_bump_of_inner.integrable ContDiffBumpOfInner.integrable

protected theorem integrableNormed : Integrable (f.normed μ) μ :=
  f.Integrable.div_const _
#align cont_diff_bump_of_inner.integrable_normed ContDiffBumpOfInner.integrableNormed

variable [μ.IsOpenPosMeasure]

theorem integral_pos : 0 < ∫ x, f x ∂μ :=
  by
  refine' (integral_pos_iff_support_of_nonneg f.nonneg' f.integrable).mpr _
  rw [f.support_eq]
  refine' is_open_ball.measure_pos _ (nonempty_ball.mpr f.R_pos)
#align cont_diff_bump_of_inner.integral_pos ContDiffBumpOfInner.integral_pos

theorem integral_normed : (∫ x, f.normed μ x ∂μ) = 1 :=
  by
  simp_rw [ContDiffBumpOfInner.normed, div_eq_mul_inv, mul_comm (f _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel f.integral_pos.ne'
#align cont_diff_bump_of_inner.integral_normed ContDiffBumpOfInner.integral_normed

theorem support_normed_eq : support (f.normed μ) = Metric.ball c f.r := by
  simp_rw [ContDiffBumpOfInner.normed, support_div, f.support_eq, support_const f.integral_pos.ne',
    inter_univ]
#align cont_diff_bump_of_inner.support_normed_eq ContDiffBumpOfInner.support_normed_eq

theorem tsupport_normed_eq : tsupport (f.normed μ) = Metric.closedBall c f.r := by
  simp_rw [tsupport, f.support_normed_eq, closure_ball _ f.R_pos.ne']
#align cont_diff_bump_of_inner.tsupport_normed_eq ContDiffBumpOfInner.tsupport_normed_eq

theorem hasCompactSupport_normed : HasCompactSupport (f.normed μ) := by
  simp_rw [HasCompactSupport, f.tsupport_normed_eq, is_compact_closed_ball]
#align cont_diff_bump_of_inner.has_compact_support_normed ContDiffBumpOfInner.hasCompactSupport_normed

theorem tendsto_support_normed_smallSets {ι} {φ : ι → ContDiffBumpOfInner c} {l : Filter ι}
    (hφ : Tendsto (fun i => (φ i).r) l (𝓝 0)) :
    Tendsto (fun i => support fun x => (φ i).normed μ x) l (𝓝 c).smallSets :=
  by
  simp_rw [NormedAddCommGroup.tendsto_nhds_zero, Real.norm_eq_abs,
    abs_eq_self.mpr (φ _).r_pos.le] at hφ
  rw [tendsto_small_sets_iff]
  intro t ht
  rcases metric.mem_nhds_iff.mp ht with ⟨ε, hε, ht⟩
  refine' (hφ ε hε).mono fun i hi => subset_trans _ ht
  simp_rw [(φ i).support_normed_eq]
  exact ball_subset_ball hi.le
#align cont_diff_bump_of_inner.tendsto_support_normed_small_sets ContDiffBumpOfInner.tendsto_support_normed_smallSets

variable (μ)

theorem integral_normed_smul (z : X) [CompleteSpace X] : (∫ x, f.normed μ x • z ∂μ) = z := by
  simp_rw [integral_smul_const, f.integral_normed, one_smul]
#align cont_diff_bump_of_inner.integral_normed_smul ContDiffBumpOfInner.integral_normed_smul

end ContDiffBumpOfInner

/-- `f : cont_diff_bump c`, where `c` is a point in a finite dimensional real vector space, is
a bundled smooth function such that

  - `f` is equal to `1` in `euclidean.closed_ball c f.r`;
  - `support f = euclidean.ball c f.R`;
  - `0 ≤ f x ≤ 1` for all `x`.

The structure `cont_diff_bump` contains the data required to construct the function: real
numbers `r`, `R`, and proofs of `0 < r < R`. The function itself is available through `coe_fn`.-/
structure ContDiffBump [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (c : E) extends ContDiffBumpOfInner (toEuclidean c)
#align cont_diff_bump ContDiffBump

namespace ContDiffBump

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {c x : E}
  (f : ContDiffBump c)

/-- The function defined by `f : cont_diff_bump c`. Use automatic coercion to function
instead. -/
def toFun (f : ContDiffBump c) : E → ℝ :=
  f.toContDiffBumpOfInner ∘ toEuclidean
#align cont_diff_bump.to_fun ContDiffBump.toFun

instance : CoeFun (ContDiffBump c) fun _ => E → ℝ :=
  ⟨toFun⟩

instance (c : E) : Inhabited (ContDiffBump c) :=
  ⟨⟨default⟩⟩

theorem r_pos : 0 < f.r :=
  f.toContDiffBumpOfInner.r_pos
#align cont_diff_bump.R_pos ContDiffBump.r_pos

theorem coe_eq_comp : ⇑f = f.toContDiffBumpOfInner ∘ toEuclidean :=
  rfl
#align cont_diff_bump.coe_eq_comp ContDiffBump.coe_eq_comp

theorem one_of_mem_closedBall (hx : x ∈ Euclidean.closedBall c f.R) : f x = 1 :=
  f.toContDiffBumpOfInner.one_of_mem_closedBall hx
#align cont_diff_bump.one_of_mem_closed_ball ContDiffBump.one_of_mem_closedBall

theorem nonneg : 0 ≤ f x :=
  f.toContDiffBumpOfInner.NonNeg
#align cont_diff_bump.nonneg ContDiffBump.nonneg

theorem le_one : f x ≤ 1 :=
  f.toContDiffBumpOfInner.le_one
#align cont_diff_bump.le_one ContDiffBump.le_one

theorem pos_of_mem_ball (hx : x ∈ Euclidean.ball c f.r) : 0 < f x :=
  f.toContDiffBumpOfInner.pos_of_mem_ball hx
#align cont_diff_bump.pos_of_mem_ball ContDiffBump.pos_of_mem_ball

theorem lt_one_of_lt_dist (h : f.R < Euclidean.dist x c) : f x < 1 :=
  f.toContDiffBumpOfInner.lt_one_of_lt_dist h
#align cont_diff_bump.lt_one_of_lt_dist ContDiffBump.lt_one_of_lt_dist

theorem zero_of_le_dist (hx : f.r ≤ Euclidean.dist x c) : f x = 0 :=
  f.toContDiffBumpOfInner.zero_of_le_dist hx
#align cont_diff_bump.zero_of_le_dist ContDiffBump.zero_of_le_dist

theorem support_eq : support (f : E → ℝ) = Euclidean.ball c f.r := by
  rw [Euclidean.ball_eq_preimage, ← f.to_cont_diff_bump_of_inner.support_eq, ←
    support_comp_eq_preimage, coe_eq_comp]
#align cont_diff_bump.support_eq ContDiffBump.support_eq

theorem tsupport_eq : tsupport f = Euclidean.closedBall c f.r := by
  rw [tsupport, f.support_eq, Euclidean.closure_ball _ f.R_pos.ne']
#align cont_diff_bump.tsupport_eq ContDiffBump.tsupport_eq

protected theorem hasCompactSupport : HasCompactSupport f := by
  simp_rw [HasCompactSupport, f.tsupport_eq, Euclidean.isCompact_closedBall]
#align cont_diff_bump.has_compact_support ContDiffBump.hasCompactSupport

theorem eventuallyEq_one_of_mem_ball (h : x ∈ Euclidean.ball c f.R) : f =ᶠ[𝓝 x] 1 :=
  toEuclidean.ContinuousAt (f.toContDiffBumpOfInner.eventuallyEq_one_of_mem_ball h)
#align cont_diff_bump.eventually_eq_one_of_mem_ball ContDiffBump.eventuallyEq_one_of_mem_ball

theorem eventuallyEq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventuallyEq_one_of_mem_ball <| Euclidean.mem_ball_self f.r_pos
#align cont_diff_bump.eventually_eq_one ContDiffBump.eventuallyEq_one

protected theorem contDiff {n} : ContDiff ℝ n f :=
  f.toContDiffBumpOfInner.ContDiff.comp (toEuclidean : E ≃L[ℝ] _).ContDiff
#align cont_diff_bump.cont_diff ContDiffBump.contDiff

protected theorem contDiffAt {n} : ContDiffAt ℝ n f x :=
  f.ContDiff.ContDiffAt
#align cont_diff_bump.cont_diff_at ContDiffBump.contDiffAt

protected theorem contDiffWithinAt {s n} : ContDiffWithinAt ℝ n f s x :=
  f.ContDiffAt.ContDiffWithinAt
#align cont_diff_bump.cont_diff_within_at ContDiffBump.contDiffWithinAt

theorem exists_tsupport_subset {s : Set E} (hs : s ∈ 𝓝 c) : ∃ f : ContDiffBump c, tsupport f ⊆ s :=
  let ⟨R, h0, hR⟩ := Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  ⟨⟨⟨R / 2, R, half_pos h0, half_lt_self h0⟩⟩, by rwa [tsupport_eq]⟩
#align cont_diff_bump.exists_tsupport_subset ContDiffBump.exists_tsupport_subset

theorem exists_closure_subset {R : ℝ} (hR : 0 < R) {s : Set E} (hs : IsClosed s)
    (hsR : s ⊆ Euclidean.ball c R) : ∃ f : ContDiffBump c, f.r = R ∧ s ⊆ Euclidean.ball c f.R :=
  by
  rcases Euclidean.exists_pos_lt_subset_ball hR hs hsR with ⟨r, hr, hsr⟩
  exact ⟨⟨⟨r, R, hr.1, hr.2⟩⟩, rfl, hsr⟩
#align cont_diff_bump.exists_closure_subset ContDiffBump.exists_closure_subset

end ContDiffBump

open FiniteDimensional Metric

/-- If `E` is a finite dimensional normed space over `ℝ`, then for any point `x : E` and its
neighborhood `s` there exists an infinitely smooth function with the following properties:

* `f y = 1` in a neighborhood of `x`;
* `f y = 0` outside of `s`;
*  moreover, `tsupport f ⊆ s` and `f` has compact support;
* `f y ∈ [0, 1]` for all `y`.

This lemma is a simple wrapper around lemmas about bundled smooth bump functions, see
`cont_diff_bump`. -/
theorem exists_contDiff_bump_function_of_mem_nhds [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {x : E} {s : Set E} (hs : s ∈ 𝓝 x) :
    ∃ f : E → ℝ,
      f =ᶠ[𝓝 x] 1 ∧
        (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧ ContDiff ℝ ⊤ f ∧ HasCompactSupport f ∧ tsupport f ⊆ s :=
  let ⟨f, hf⟩ := ContDiffBump.exists_tsupport_subset hs
  ⟨f, f.eventuallyEq_one, fun y => ⟨f.NonNeg, f.le_one⟩, f.ContDiff, f.HasCompactSupport, hf⟩
#align exists_cont_diff_bump_function_of_mem_nhds exists_contDiff_bump_function_of_mem_nhds

