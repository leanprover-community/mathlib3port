import Mathbin.Analysis.Analytic.Basic 
import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# Representation of `formal_multilinear_series.radius` as a `liminf`

In this file we prove that the radius of convergence of a `formal_multilinear_series` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{∥p n∥}}$. This lemma can't go to `basic.lean` because this
would create a circular dependency once we redefine `exp` using `formal_multilinear_series`.
-/


variable{𝕜 :
    Type
      _}[NondiscreteNormedField
      𝕜]{E : Type _}[NormedGroup E][NormedSpace 𝕜 E]{F : Type _}[NormedGroup F][NormedSpace 𝕜 F]

open_locale TopologicalSpace Classical BigOperators Nnreal Ennreal

open Filter Asymptotics

namespace FormalMultilinearSeries

variable(p : FormalMultilinearSeries 𝕜 E F)

-- error in Analysis.Analytic.RadiusLiminf: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{∥p n∥}}$. The actual statement uses `ℝ≥0` and some
coercions. -/
theorem radius_eq_liminf : «expr = »(p.radius, liminf at_top (λ
  n, «expr / »(1, («expr ^ »(nnnorm (p n), «expr / »(1, (n : exprℝ()))) : «exprℝ≥0»())))) :=
begin
  have [] [":", expr ∀
   (r : «exprℝ≥0»())
   {n : exprℕ()}, «expr < »(0, n) → «expr ↔ »(«expr ≤ »((r : «exprℝ≥0∞»()), «expr / »(1, «expr↑ »(«expr ^ »(nnnorm (p n), «expr / »(1, (n : exprℝ())))))), «expr ≤ »(«expr * »(nnnorm (p n), «expr ^ »(r, n)), 1))] [],
  { intros [ident r, ident n, ident hn],
    have [] [":", expr «expr < »(0, (n : exprℝ()))] [":=", expr nat.cast_pos.2 hn],
    conv_lhs [] [] { rw ["[", expr one_div, ",", expr ennreal.le_inv_iff_mul_le, ",", "<-", expr ennreal.coe_mul, ",", expr ennreal.coe_le_one_iff, ",", expr one_div, ",", "<-", expr nnreal.rpow_one r, ",", "<-", expr mul_inv_cancel this.ne', ",", expr nnreal.rpow_mul, ",", "<-", expr nnreal.mul_rpow, ",", "<-", expr nnreal.one_rpow «expr ⁻¹»(n), ",", expr nnreal.rpow_le_rpow_iff (inv_pos.2 this), ",", expr mul_comm, ",", expr nnreal.rpow_nat_cast, "]"] } },
  apply [expr le_antisymm]; refine [expr ennreal.le_of_forall_nnreal_lt (λ r hr, _)],
  { rcases [expr ((tfae_exists_lt_is_o_pow (λ
        n, «expr * »(«expr∥ ∥»(p n), «expr ^ »(r, n))) 1).out 1 7).1 (p.is_o_of_lt_radius hr), "with", "⟨", ident a, ",", ident ha, ",", ident H, "⟩"],
    refine [expr le_Liminf_of_le (by apply_auto_param) «expr $ »(eventually_map.2, _)],
    refine [expr H.mp «expr $ »((eventually_gt_at_top 0).mono, λ n hn₀ hn, (this _ hn₀).2 (nnreal.coe_le_coe.1 _))],
    push_cast [] [],
    exact [expr (le_abs_self _).trans (hn.trans (pow_le_one _ ha.1.le ha.2.le))] },
  { refine [expr p.le_radius_of_is_O (is_O.of_bound 1 _)],
    refine [expr (eventually_lt_of_lt_liminf hr).mp ((eventually_gt_at_top 0).mono (λ n hn₀ hn, _))],
    simpa [] [] [] [] [] ["using", expr nnreal.coe_le_coe.2 ((this _ hn₀).1 hn.le)] }
end

end FormalMultilinearSeries

