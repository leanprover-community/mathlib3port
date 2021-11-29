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
  ∀ (n : ℕ), ∃ a b : ℤ, 1 < b ∧ x ≠ a / b ∧ |x - a / b| < 1 / (b^n)

namespace Liouville

-- error in NumberTheory.Liouville.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[protected #[]] theorem irrational {x : exprℝ()} (h : liouville x) : irrational x :=
begin
  rintros ["⟨", "⟨", ident a, ",", ident b, ",", ident bN0, ",", ident cop, "⟩", ",", ident rfl, "⟩"],
  change [expr liouville «expr / »(a, b)] [] ["at", ident h],
  rcases [expr h «expr + »(b, 1), "with", "⟨", ident p, ",", ident q, ",", ident q1, ",", ident a0, ",", ident a1, "⟩"],
  have [ident qR0] [":", expr «expr < »((0 : exprℝ()), q)] [":=", expr int.cast_pos.mpr (zero_lt_one.trans q1)],
  have [ident b0] [":", expr «expr ≠ »((b : exprℝ()), 0)] [":=", expr ne_of_gt (nat.cast_pos.mpr bN0)],
  have [ident bq0] [":", expr «expr < »((0 : exprℝ()), «expr * »(b, q))] [":=", expr mul_pos (nat.cast_pos.mpr bN0) qR0],
  replace [ident a1] [":", expr «expr < »(«expr * »(«expr| |»(«expr - »(«expr * »(a, q), «expr * »(b, p))), «expr ^ »(q, «expr + »(b, 1))), «expr * »(b, q))] [],
  by rwa ["[", expr div_sub_div _ _ b0 (ne_of_gt qR0), ",", expr abs_div, ",", expr div_lt_div_iff (abs_pos.mpr (ne_of_gt bq0)) (pow_pos qR0 _), ",", expr abs_of_pos bq0, ",", expr one_mul, ",", "<-", expr int.cast_pow, ",", "<-", expr int.cast_mul, ",", "<-", expr int.cast_coe_nat, ",", "<-", expr int.cast_mul, ",", "<-", expr int.cast_mul, ",", "<-", expr int.cast_sub, ",", "<-", expr int.cast_abs, ",", "<-", expr int.cast_mul, ",", expr int.cast_lt, "]"] ["at", ident a1],
  replace [ident a0] [":", expr «expr¬ »(«expr = »(«expr - »(«expr * »(a, q), «expr * »(«expr↑ »(b), p)), 0))] [],
  by rwa ["[", expr ne.def, ",", expr div_eq_div_iff b0 (ne_of_gt qR0), ",", expr mul_comm «expr↑ »(p), ",", "<-", expr sub_eq_zero, ",", "<-", expr int.cast_coe_nat, ",", "<-", expr int.cast_mul, ",", "<-", expr int.cast_mul, ",", "<-", expr int.cast_sub, ",", expr int.cast_eq_zero, "]"] ["at", ident a0],
  lift [expr q] ["to", expr exprℕ()] ["using", expr (zero_lt_one.trans q1).le] [],
  have [ident ap] [":", expr «expr < »(0, «expr| |»(«expr - »(«expr * »(a, «expr↑ »(q)), «expr * »(«expr↑ »(b), p))))] [":=", expr abs_pos.mpr a0],
  lift [expr «expr| |»(«expr - »(«expr * »(a, «expr↑ »(q)), «expr * »(«expr↑ »(b), p)))] ["to", expr exprℕ()] ["using", expr abs_nonneg «expr - »(«expr * »(a, «expr↑ »(q)), «expr * »(«expr↑ »(b), p))] [],
  rw ["[", "<-", expr int.coe_nat_mul, ",", "<-", expr int.coe_nat_pow, ",", "<-", expr int.coe_nat_mul, ",", expr int.coe_nat_lt, "]"] ["at", ident a1],
  exact [expr not_le.mpr a1 (nat.mul_lt_mul_pow_succ (int.coe_nat_pos.mp ap) (int.coe_nat_lt.mp q1)).le]
end

open Polynomial Metric Set Real RingHom

-- error in NumberTheory.Liouville.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Let `Z, N` be types, let `R` be a metric space, let `α : R` be a point and let
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
theorem exists_one_le_pow_mul_dist
{Z N R : Type*}
[metric_space R]
{d : N → exprℝ()}
{j : Z → N → R}
{f : R → R}
{α : R}
{ε M : exprℝ()}
(d0 : ∀ a : N, «expr ≤ »(1, d a))
(e0 : «expr < »(0, ε))
(B : ∀ {{y : R}}, «expr ∈ »(y, closed_ball α ε) → «expr ≤ »(dist (f α) (f y), «expr * »(dist α y, M)))
(L : ∀
 {{z : Z}}, ∀
 {{a : N}}, «expr ∈ »(j z a, closed_ball α ε) → «expr ≤ »(1, «expr * »(d a, dist (f α) (f (j z a))))) : «expr∃ , »((A : exprℝ()), «expr ∧ »(«expr < »(0, A), ∀
  z : Z, ∀ a : N, «expr ≤ »(1, «expr * »(d a, «expr * »(dist α (j z a), A))))) :=
begin
  have [ident me0] [":", expr «expr < »(0, max «expr / »(1, ε) M)] [":=", expr lt_max_iff.mpr (or.inl (one_div_pos.mpr e0))],
  refine [expr ⟨max «expr / »(1, ε) M, me0, λ z a, _⟩],
  by_cases [expr dm1, ":", expr «expr ≤ »(1, «expr * »(dist α (j z a), max «expr / »(1, ε) M))],
  { exact [expr one_le_mul_of_one_le_of_one_le (d0 a) dm1] },
  { have [] [":", expr «expr ∈ »(j z a, closed_ball α ε)] [],
    { refine [expr mem_closed_ball'.mp (le_trans _ ((one_div_le me0 e0).mpr (le_max_left _ _)))],
      exact [expr (le_div_iff me0).mpr (not_le.mp dm1).le] },
    refine [expr (L this).trans _],
    refine [expr mul_le_mul_of_nonneg_left ((B this).trans _) (zero_le_one.trans (d0 a))],
    exact [expr mul_le_mul_of_nonneg_left (le_max_right _ M) dist_nonneg] }
end

-- error in NumberTheory.Liouville.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_pos_real_of_irrational_root
{α : exprℝ()}
(ha : irrational α)
{f : polynomial exprℤ()}
(f0 : «expr ≠ »(f, 0))
(fa : «expr = »(eval α (map (algebra_map exprℤ() exprℝ()) f), 0)) : «expr∃ , »((A : exprℝ()), «expr ∧ »(«expr < »(0, A), ∀
  a : exprℤ(), ∀
  b : exprℕ(), «expr ≤ »((1 : exprℝ()), «expr * »(«expr ^ »(«expr + »(b, 1), f.nat_degree), «expr * »(«expr| |»(«expr - »(α, «expr / »(a, «expr + »(b, 1)))), A))))) :=
begin
  set [] [ident fR] [":", expr polynomial exprℝ()] [":="] [expr map (algebra_map exprℤ() exprℝ()) f] [],
  obtain [ident fR0, ":", expr «expr ≠ »(fR, 0), ":=", expr λ
   fR0, (map_injective (algebra_map exprℤ() exprℝ()) (λ
     _ _ A, int.cast_inj.mp A)).ne f0 (fR0.trans (polynomial.map_zero _).symm)],
  have [ident ar] [":", expr «expr ∈ »(α, (fR.roots.to_finset : set exprℝ()))] [":=", expr finset.mem_coe.mpr (multiset.mem_to_finset.mpr ((mem_roots fR0).mpr (is_root.def.mpr fa)))],
  obtain ["⟨", ident ζ, ",", ident z0, ",", ident U, "⟩", ":", expr «expr∃ , »((ζ «expr > » 0), «expr = »(«expr ∩ »(closed_ball α ζ, fR.roots.to_finset), {α})), ":=", expr @exists_closed_ball_inter_eq_singleton_of_discrete _ _ _ discrete_of_t1_of_finite _ ar],
  obtain ["⟨", ident xm, ",", "-", ",", ident hM, "⟩", ":", expr «expr∃ , »((xm : exprℝ())
    (H : «expr ∈ »(xm, Icc «expr - »(α, ζ) «expr + »(α, ζ))), ∀
    y : exprℝ(), «expr ∈ »(y, Icc «expr - »(α, ζ) «expr + »(α, ζ)) → «expr ≤ »(«expr| |»(fR.derivative.eval y), «expr| |»(fR.derivative.eval xm))), ":=", expr is_compact.exists_forall_ge is_compact_Icc ⟨α, (sub_lt_self α z0).le, (lt_add_of_pos_right α z0).le⟩ (continuous_abs.comp fR.derivative.continuous_aeval).continuous_on],
  refine [expr @exists_one_le_pow_mul_dist exprℤ() exprℕ() exprℝ() _ _ _ (λ
    y, fR.eval y) α ζ «expr| |»(fR.derivative.eval xm) _ z0 (λ y hy, _) (λ z a hq, _)],
  { exact [expr λ a, one_le_pow_of_one_le ((le_add_iff_nonneg_left 1).mpr a.cast_nonneg) _] },
  { rw [expr mul_comm] [],
    rw [expr real.closed_ball_eq] ["at", ident hy],
    refine [expr convex.norm_image_sub_le_of_norm_deriv_le (λ
      _
      _, fR.differentiable_at) (λ y h, by { rw [expr fR.deriv] [],
        exact [expr hM _ h] }) (convex_Icc _ _) hy (mem_Icc_iff_abs_le.mp _)],
    exact [expr @mem_closed_ball_self exprℝ() _ α ζ (le_of_lt z0)] },
  { show [expr «expr ≤ »(1, «expr * »(«expr ^ »((«expr + »(a, 1) : exprℝ()), f.nat_degree), «expr| |»(«expr - »(eval α fR, eval «expr / »(z, «expr + »(a, 1)) fR))))],
    rw ["[", expr fa, ",", expr zero_sub, ",", expr abs_neg, "]"] [],
    refine [expr one_le_pow_mul_abs_eval_div (int.coe_nat_succ_pos a) (λ hy, _)],
    refine [expr (irrational_iff_ne_rational α).mp ha z «expr + »(a, 1) (mem_singleton_iff.mp _).symm],
    refine [expr U.subset _],
    refine [expr ⟨hq, finset.mem_coe.mp (multiset.mem_to_finset.mpr _)⟩],
    exact [expr (mem_roots fR0).mpr (is_root.def.mpr hy)] }
end

-- error in NumberTheory.Liouville.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Liouville's Theorem** -/ theorem transcendental {x : exprℝ()} (lx : liouville x) : transcendental exprℤ() x :=
begin
  rintros ["⟨", ident f, ":", expr polynomial exprℤ(), ",", ident f0, ",", ident ef0, "⟩"],
  replace [ident ef0] [":", expr «expr = »((f.map (algebra_map exprℤ() exprℝ())).eval x, 0)] [],
  { rwa ["[", expr aeval_def, ",", "<-", expr eval_map, "]"] ["at", ident ef0] },
  obtain ["⟨", ident A, ",", ident hA, ",", ident h, "⟩", ":", expr «expr∃ , »((A : exprℝ()), «expr ∧ »(«expr < »(0, A), ∀
     (a : exprℤ())
     (b : exprℕ()), «expr ≤ »((1 : exprℝ()), «expr * »(«expr ^ »(b.succ, f.nat_degree), «expr * »(«expr| |»(«expr - »(x, «expr / »(a, b.succ))), A))))), ":=", expr exists_pos_real_of_irrational_root lx.irrational f0 ef0],
  rcases [expr pow_unbounded_of_one_lt A (lt_add_one 1), "with", "⟨", ident r, ",", ident hn, "⟩"],
  obtain ["⟨", ident a, ",", ident b, ",", ident b1, ",", "-", ",", ident a1, "⟩", ":", expr «expr∃ , »((a
     b : exprℤ()), «expr ∧ »(«expr < »(1, b), «expr ∧ »(«expr ≠ »(x, «expr / »(a, b)), «expr < »(«expr| |»(«expr - »(x, «expr / »(a, b))), «expr / »(1, «expr ^ »(b, «expr + »(r, f.nat_degree))))))), ":=", expr lx «expr + »(r, f.nat_degree)],
  have [ident b0] [":", expr «expr < »((0 : exprℝ()), b)] [":=", expr zero_lt_one.trans (by { rw ["<-", expr int.cast_one] [],
      exact [expr int.cast_lt.mpr b1] })],
  refine [expr lt_irrefl «expr * »(«expr ^ »((b : exprℝ()), f.nat_degree), «expr| |»(«expr - »(x, «expr / »(«expr↑ »(a), «expr↑ »(b))))) _],
  rw ["[", expr lt_div_iff' (pow_pos b0 _), ",", expr pow_add, ",", expr mul_assoc, "]"] ["at", ident a1],
  refine [expr (_ : «expr < »(«expr * »(«expr ^ »((b : exprℝ()), f.nat_degree), «expr| |»(«expr - »(x, «expr / »(a, b)))), «expr / »(1, A))).trans_le _],
  { refine [expr (lt_div_iff' hA).mpr _],
    refine [expr lt_of_le_of_lt _ a1],
    refine [expr mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg b0.le _) (abs_nonneg _))],
    refine [expr hn.le.trans _],
    refine [expr pow_le_pow_of_le_left zero_le_two _ _],
    exact [expr int.cast_two.symm.le.trans (int.cast_le.mpr (int.add_one_le_iff.mpr b1))] },
  { lift [expr b] ["to", expr exprℕ()] ["using", expr zero_le_one.trans b1.le] [],
    specialize [expr h a b.pred],
    rwa ["[", expr nat.succ_pred_eq_of_pos (zero_lt_one.trans _), ",", "<-", expr mul_assoc, ",", "<-", expr div_le_iff hA, "]"] ["at", ident h],
    exact [expr int.coe_nat_lt.mp b1] }
end

end Liouville

