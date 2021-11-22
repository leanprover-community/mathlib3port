import Mathbin.Topology.MetricSpace.HausdorffDistance

/-!
# Riesz's lemma

Riesz's lemma, stated for a normed space over a normed field: for any
closed proper subspace `F` of `E`, there is a nonzero `x` such that `∥x - F∥`
is at least `r * ∥x∥` for any `r < 1`. This is `riesz_lemma`.

In a nondiscrete normed field (with an element `c` of norm `> 1`) and any `R > ∥c∥`, one can
guarantee `∥x∥ ≤ R` and `∥x - y∥ ≥ 1` for any `y` in `F`. This is `riesz_lemma_of_norm_lt`.
-/


variable{𝕜 : Type _}[NormedField 𝕜]

variable{E : Type _}[NormedGroup E][NormedSpace 𝕜 E]

-- error in Analysis.NormedSpace.RieszLemma: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Riesz's lemma, which usually states that it is possible to find a
vector with norm 1 whose distance to a closed proper subspace is
arbitrarily close to 1. The statement here is in terms of multiples of
norms, since in general the existence of an element of norm exactly 1
is not guaranteed. For a variant giving an element with norm in `[1, R]`, see
`riesz_lemma_of_norm_lt`. -/
theorem riesz_lemma
{F : subspace 𝕜 E}
(hFc : is_closed (F : set E))
(hF : «expr∃ , »((x : E), «expr ∉ »(x, F)))
{r : exprℝ()}
(hr : «expr < »(r, 1)) : «expr∃ , »((x₀ : E), «expr ∧ »(«expr ∉ »(x₀, F), ∀
  y «expr ∈ » F, «expr ≤ »(«expr * »(r, «expr∥ ∥»(x₀)), «expr∥ ∥»(«expr - »(x₀, y))))) :=
begin
  classical,
  obtain ["⟨", ident x, ",", ident hx, "⟩", ":", expr «expr∃ , »((x : E), «expr ∉ »(x, F)), ":=", expr hF],
  let [ident d] [] [":=", expr metric.inf_dist x F],
  have [ident hFn] [":", expr (F : set E).nonempty] [],
  from [expr ⟨_, F.zero_mem⟩],
  have [ident hdp] [":", expr «expr < »(0, d)] [],
  from [expr lt_of_le_of_ne metric.inf_dist_nonneg (λ heq, hx ((hFc.mem_iff_inf_dist_zero hFn).2 heq.symm))],
  let [ident r'] [] [":=", expr max r «expr ⁻¹»(2)],
  have [ident hr'] [":", expr «expr < »(r', 1)] [],
  by { simp [] [] [] ["[", expr r', ",", expr hr, "]"] [] [],
    norm_num [] [] },
  have [ident hlt] [":", expr «expr < »(0, r')] [":=", expr lt_of_lt_of_le (by norm_num [] []) (le_max_right r «expr ⁻¹»(2))],
  have [ident hdlt] [":", expr «expr < »(d, «expr / »(d, r'))] [],
  from [expr (lt_div_iff hlt).mpr ((mul_lt_iff_lt_one_right hdp).2 hr')],
  obtain ["⟨", ident y₀, ",", ident hy₀F, ",", ident hxy₀, "⟩", ":", expr «expr∃ , »((y «expr ∈ » F), «expr < »(dist x y, «expr / »(d, r'))), ":=", expr metric.exists_dist_lt_of_inf_dist_lt hdlt hFn],
  have [ident x_ne_y₀] [":", expr «expr ∉ »(«expr - »(x, y₀), F)] [],
  { by_contradiction [ident h],
    have [] [":", expr «expr ∈ »(«expr + »(«expr - »(x, y₀), y₀), F)] [],
    from [expr F.add_mem h hy₀F],
    simp [] [] ["only"] ["[", expr neg_add_cancel_right, ",", expr sub_eq_add_neg, "]"] [] ["at", ident this],
    exact [expr hx this] },
  refine [expr ⟨«expr - »(x, y₀), x_ne_y₀, λ y hy, le_of_lt _⟩],
  have [ident hy₀y] [":", expr «expr ∈ »(«expr + »(y₀, y), F)] [],
  from [expr F.add_mem hy₀F hy],
  calc
    «expr ≤ »(«expr * »(r, «expr∥ ∥»(«expr - »(x, y₀))), «expr * »(r', «expr∥ ∥»(«expr - »(x, y₀)))) : mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    «expr < »(..., d) : by { rw ["<-", expr dist_eq_norm] [],
      exact [expr (lt_div_iff' hlt).1 hxy₀] }
    «expr ≤ »(..., dist x «expr + »(y₀, y)) : metric.inf_dist_le_dist_of_mem hy₀y
    «expr = »(..., «expr∥ ∥»(«expr - »(«expr - »(x, y₀), y))) : by { rw ["[", expr sub_sub, ",", expr dist_eq_norm, "]"] [] }
end

/--
A version of Riesz lemma: given a strict closed subspace `F`, one may find an element of norm `≤ R`
which is at distance  at least `1` of every element of `F`. Here, `R` is any given constant
strictly larger than the norm of an element of norm `> 1`. For a version without an `R`, see
`riesz_lemma`.

Since we are considering a general nondiscrete normed field, there may be a gap in possible norms
(for instance no element of norm in `(1,2)`). Hence, we can not allow `R` arbitrarily close to `1`,
and require `R > ∥c∥` for some `c : 𝕜` with norm `> 1`.
-/
theorem riesz_lemma_of_norm_lt {c : 𝕜} (hc : 1 < ∥c∥) {R : ℝ} (hR : ∥c∥ < R) {F : Subspace 𝕜 E}
  (hFc : IsClosed (F : Set E)) (hF : ∃ x : E, x ∉ F) : ∃ x₀ : E, ∥x₀∥ ≤ R ∧ ∀ y _ : y ∈ F, 1 ≤ ∥x₀ - y∥ :=
  by 
    have Rpos : 0 < R := (norm_nonneg _).trans_lt hR 
    have  : ∥c∥ / R < 1
    ·
      ·
        rw [div_lt_iff Rpos]
        simpa using hR 
    rcases riesz_lemma hFc hF this with ⟨x, xF, hx⟩
    have x0 : x ≠ 0 :=
      fun H =>
        by 
          simpa [H] using xF 
    obtain ⟨d, d0, dxlt, ledx, -⟩ : ∃ d : 𝕜, d ≠ 0 ∧ ∥d • x∥ < R ∧ R / ∥c∥ ≤ ∥d • x∥ ∧ ∥d∥⁻¹ ≤ (R⁻¹*∥c∥)*∥x∥ :=
      rescale_to_shell hc Rpos x0 
    refine' ⟨d • x, dxlt.le, fun y hy => _⟩
    set y' := d⁻¹ • y with hy' 
    have y'F : y' ∈ F
    ·
      simp [hy', Submodule.smul_mem _ _ hy]
    have yy' : y = d • y'
    ·
      simp [hy', smul_smul, mul_inv_cancel d0]
    calc 1 = (∥c∥ / R)*R / ∥c∥ :=
      by 
        fieldSimp [Rpos.ne', (zero_lt_one.trans hc).ne']_ ≤ (∥c∥ / R)*∥d • x∥ :=
      mul_le_mul_of_nonneg_left ledx (div_nonneg (norm_nonneg _) Rpos.le)_ = ∥d∥*(∥c∥ / R)*∥x∥ :=
      by 
        simp [norm_smul]
        ring _ ≤ ∥d∥*∥x - y'∥ :=
      mul_le_mul_of_nonneg_left
        (hx y'
          (by 
            simp [hy', Submodule.smul_mem _ _ hy]))
        (norm_nonneg _)_ = ∥d • x - y∥ :=
      by 
        simp [yy', ←smul_sub, norm_smul]

