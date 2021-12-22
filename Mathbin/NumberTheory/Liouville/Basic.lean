import Mathbin.Analysis.Calculus.MeanValue
import Mathbin.Data.Polynomial.DenomsClearable
import Mathbin.Data.Real.Irrational

/-!

# Liouville's theorem

This file contains a proof of Liouville's theorem stating that all Liouville numbers are
transcendental.

To obtain this result, there is first a proof that Liouville numbers are irrational and two
technical lemmas.  These lemmas exploit the fact that a polynomial with integer coefficients
takes integer values at integers.  When evaluating at a rational number, we can clear denominators
and obtain precise inequalities that ultimately allow us to prove transcendence of
Liouville numbers.
-/


/-- 
A Liouville number is a real number `x` such that for every natural number `n`, there exist
`a, b ∈ ℤ` with `1 < b` such that `0 < |x - a/b| < 1/bⁿ`.
In the implementation, the condition `x ≠ a/b` replaces the traditional equivalent `0 < |x - a/b|`.
-/
def Liouville (x : ℝ) :=
  ∀ n : ℕ, ∃ a b : ℤ, 1 < b ∧ x ≠ a / b ∧ |x - a / b| < 1 / (b^n)

namespace Liouville

@[protected]
theorem Irrational {x : ℝ} (h : Liouville x) : Irrational x := by
  rintro ⟨⟨a, b, bN0, cop⟩, rfl⟩
  change Liouville (a / b) at h
  rcases h (b+1) with ⟨p, q, q1, a0, a1⟩
  have qR0 : (0 : ℝ) < q := int.cast_pos.mpr (zero_lt_one.trans q1)
  have b0 : (b : ℝ) ≠ 0 := ne_of_gtₓ (nat.cast_pos.mpr bN0)
  have bq0 : (0 : ℝ) < b*q := mul_pos (nat.cast_pos.mpr bN0) qR0
  replace a1 : (|(a*q) - b*p|*q^b+1) < b*q
  ·
    rwa [div_sub_div _ _ b0 (ne_of_gtₓ qR0), abs_div, div_lt_div_iff (abs_pos.mpr (ne_of_gtₓ bq0)) (pow_pos qR0 _),
      abs_of_pos bq0, one_mulₓ, ← Int.cast_pow, ← Int.cast_mul, ← Int.cast_coe_nat, ← Int.cast_mul, ← Int.cast_mul, ←
      Int.cast_sub, ← Int.cast_abs, ← Int.cast_mul, Int.cast_lt] at a1
  replace a0 : ¬((a*q) - (↑b)*p) = 0
  ·
    rwa [Ne.def, div_eq_div_iff b0 (ne_of_gtₓ qR0), mul_commₓ (↑p), ← sub_eq_zero, ← Int.cast_coe_nat, ← Int.cast_mul, ←
      Int.cast_mul, ← Int.cast_sub, Int.cast_eq_zero] at a0
  lift q to ℕ using (zero_lt_one.trans q1).le
  have ap : 0 < |(a*↑q) - (↑b)*p| := abs_pos.mpr a0
  lift |(a*↑q) - (↑b)*p| to ℕ using abs_nonneg ((a*↑q) - (↑b)*p)
  rw [← Int.coe_nat_mul, ← Int.coe_nat_pow, ← Int.coe_nat_mul, Int.coe_nat_lt] at a1
  exact not_le.mpr a1 (Nat.mul_lt_mul_pow_succ (int.coe_nat_pos.mp ap) (int.coe_nat_lt.mp q1)).le

open Polynomial Metric Set Real RingHom

/--  Let `Z, N` be types, let `R` be a metric space, let `α : R` be a point and let
`j : Z → N → R` be a function.  We aim to estimate how close we can get to `α`, while staying
in the image of `j`.  The points `j z a` of `R` in the image of `j` come with a "cost" equal to
`d a`.  As we get closer to `α` while staying in the image of `j`, we are interested in bounding
the quantity `d a * dist α (j z a)` from below by a strictly positive amount `1 / A`: the intuition
is that approximating well `α` with the points in the image of `j` should come at a high cost.  The
hypotheses on the function `f : R → R` provide us with sufficient conditions to ensure our goal.
The first hypothesis is that `f` is Lipschitz at `α`: this yields a bound on the distance.
The second hypothesis is specific to the Liouville argument and provides the missing bound
involving the cost function `d`.

This lemma collects the properties used in the proof of `exists_pos_real_of_irrational_root`.
It is stated in more general form than needed: in the intended application, `Z = ℤ`, `N = ℕ`,
`R = ℝ`, `d a = (a + 1) ^ f.nat_degree`, `j z a  = z / (a + 1)`, `f ∈ ℤ[x]`, `α` is an irrational
root of `f`, `ε` is small, `M` is a bound on the Lipschitz constant of `f` near `α`, `n` is
the degree of the polynomial `f`.
-/
theorem exists_one_le_pow_mul_dist {Z N R : Type _} [MetricSpace R] {d : N → ℝ} {j : Z → N → R} {f : R → R} {α : R}
    {ε M : ℝ} (d0 : ∀ a : N, 1 ≤ d a) (e0 : 0 < ε) (B : ∀ ⦃y : R⦄, y ∈ closed_ball α ε → dist (f α) (f y) ≤ dist α y*M)
    (L : ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closed_ball α ε → 1 ≤ d a*dist (f α) (f (j z a))) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : Z, ∀ a : N, 1 ≤ d a*dist α (j z a)*A := by
  have me0 : 0 < max (1 / ε) M := lt_max_iff.mpr (Or.inl (one_div_pos.mpr e0))
  refine' ⟨max (1 / ε) M, me0, fun z a => _⟩
  by_cases' dm1 : 1 ≤ dist α (j z a)*max (1 / ε) M
  ·
    exact one_le_mul_of_one_le_of_one_le (d0 a) dm1
  ·
    have : j z a ∈ closed_ball α ε := by
      refine' mem_closed_ball'.mp (le_transₓ _ ((one_div_le me0 e0).mpr (le_max_leftₓ _ _)))
      exact (le_div_iff me0).mpr (not_le.mp dm1).le
    refine' (L this).trans _
    refine' mul_le_mul_of_nonneg_left ((B this).trans _) (zero_le_one.trans (d0 a))
    exact mul_le_mul_of_nonneg_left (le_max_rightₓ _ M) dist_nonneg

theorem exists_pos_real_of_irrational_root {α : ℝ} (ha : Irrational α) {f : Polynomial ℤ} (f0 : f ≠ 0)
    (fa : eval α (map (algebraMap ℤ ℝ) f) = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℤ, ∀ b : ℕ, (1 : ℝ) ≤ ((b+1)^f.nat_degree)*|α - a / b+1|*A := by
  set fR : Polynomial ℝ := map (algebraMap ℤ ℝ) f
  obtain fR0 : fR ≠ 0 := fun fR0 =>
    (map_injective (algebraMap ℤ ℝ) fun _ _ A => int.cast_inj.mp A).Ne f0 (fR0.trans (Polynomial.map_zero _).symm)
  have ar : α ∈ (fR.roots.to_finset : Set ℝ) :=
    finset.mem_coe.mpr (multiset.mem_to_finset.mpr ((mem_roots fR0).mpr (is_root.def.mpr fa)))
  obtain ⟨ζ, z0, U⟩ : ∃ ζ > 0, closed_ball α ζ ∩ fR.roots.to_finset = {α} :=
    @exists_closed_ball_inter_eq_singleton_of_discrete _ _ _ discrete_of_t1_of_finite _ ar
  obtain ⟨xm, -, hM⟩ :
    ∃ (xm : ℝ)(H : xm ∈ Icc (α - ζ) (α+ζ)),
      ∀ y : ℝ, y ∈ Icc (α - ζ) (α+ζ) → |fR.derivative.eval y| ≤ |fR.derivative.eval xm| :=
    IsCompact.exists_forall_ge is_compact_Icc ⟨α, (sub_lt_self α z0).le, (lt_add_of_pos_right α z0).le⟩
      (continuous_abs.comp fR.derivative.continuous_aeval).ContinuousOn
  refine'
    @exists_one_le_pow_mul_dist ℤ ℕ ℝ _ _ _ (fun y => fR.eval y) α ζ |fR.derivative.eval xm| _ z0 (fun y hy => _)
      fun z a hq => _
  ·
    exact fun a => one_le_pow_of_one_le ((le_add_iff_nonneg_left 1).mpr a.cast_nonneg) _
  ·
    rw [mul_commₓ]
    rw [Real.closed_ball_eq_Icc] at hy
    refine'
      Convex.norm_image_sub_le_of_norm_deriv_le (fun _ _ => fR.differentiable_at)
        (fun y h => by
          rw [fR.deriv]
          exact hM _ h)
        (convex_Icc _ _) hy (mem_Icc_iff_abs_le.mp _)
    exact @mem_closed_ball_self ℝ _ α ζ (le_of_ltₓ z0)
  ·
    show 1 ≤ ((a+1 : ℝ)^f.nat_degree)*|eval α fR - eval (z / a+1) fR|
    rw [fa, zero_sub, abs_neg]
    refine' one_le_pow_mul_abs_eval_div (Int.coe_nat_succ_pos a) fun hy => _
    refine' (irrational_iff_ne_rational α).mp ha z (a+1) (mem_singleton_iff.mp _).symm
    refine' U.subset _
    refine' ⟨hq, finset.mem_coe.mp (multiset.mem_to_finset.mpr _)⟩
    exact (mem_roots fR0).mpr (is_root.def.mpr hy)

/--  **Liouville's Theorem** -/
theorem Transcendental {x : ℝ} (lx : Liouville x) : Transcendental ℤ x := by
  rintro ⟨f : Polynomial ℤ, f0, ef0⟩
  replace ef0 : (f.map (algebraMap ℤ ℝ)).eval x = 0
  ·
    rwa [aeval_def, ← eval_map] at ef0
  obtain ⟨A, hA, h⟩ : ∃ A : ℝ, 0 < A ∧ ∀ a : ℤ b : ℕ, (1 : ℝ) ≤ (b.succ^f.nat_degree)*|x - a / b.succ|*A :=
    exists_pos_real_of_irrational_root lx.irrational f0 ef0
  rcases pow_unbounded_of_one_lt A (lt_add_one 1) with ⟨r, hn⟩
  obtain ⟨a, b, b1, -, a1⟩ : ∃ a b : ℤ, 1 < b ∧ x ≠ a / b ∧ |x - a / b| < 1 / (b^r+f.nat_degree) := lx (r+f.nat_degree)
  have b0 : (0 : ℝ) < b :=
    zero_lt_one.trans
      (by
        rw [← Int.cast_one]
        exact int.cast_lt.mpr b1)
  refine' lt_irreflₓ (((b : ℝ)^f.nat_degree)*|x - ↑a / ↑b|) _
  rw [lt_div_iff' (pow_pos b0 _), pow_addₓ, mul_assocₓ] at a1
  refine' (_ : (((b : ℝ)^f.nat_degree)*|x - a / b|) < 1 / A).trans_le _
  ·
    refine' (lt_div_iff' hA).mpr _
    refine' lt_of_le_of_ltₓ _ a1
    refine' mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg b0.le _) (abs_nonneg _))
    refine' hn.le.trans _
    refine' pow_le_pow_of_le_left zero_le_two _ _
    exact int.cast_two.symm.le.trans (int.cast_le.mpr (int.add_one_le_iff.mpr b1))
  ·
    lift b to ℕ using zero_le_one.trans b1.le
    specialize h a b.pred
    rwa [Nat.succ_pred_eq_of_posₓ (zero_lt_one.trans _), ← mul_assocₓ, ← div_le_iff hA] at h
    exact int.coe_nat_lt.mp b1

end Liouville

