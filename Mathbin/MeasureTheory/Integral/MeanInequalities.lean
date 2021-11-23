import Mathbin.MeasureTheory.Integral.Lebesgue 
import Mathbin.Analysis.MeanInequalities 
import Mathbin.Analysis.MeanInequalitiesPow 
import Mathbin.MeasureTheory.Function.SpecialFunctions

/-!
# Mean value inequalities for integrals

In this file we prove several inequalities on integrals, notably the Hölder inequality and
the Minkowski inequality. The versions for finite sums are in `analysis.mean_inequalities`.

## Main results

Hölder's inequality for the Lebesgue integral of `ℝ≥0∞` and `ℝ≥0` functions: we prove
`∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q` conjugate real exponents
and `α→(e)nnreal` functions in two cases,
* `ennreal.lintegral_mul_le_Lp_mul_Lq` : ℝ≥0∞ functions,
* `nnreal.lintegral_mul_le_Lp_mul_Lq`  : ℝ≥0 functions.

Minkowski's inequality for the Lebesgue integral of measurable functions with `ℝ≥0∞` values:
we prove `(∫ (f + g)^p ∂μ) ^ (1/p) ≤ (∫ f^p ∂μ) ^ (1/p) + (∫ g^p ∂μ) ^ (1/p)` for `1 ≤ p`.
-/


section Lintegral

/-!
### Hölder's inequality for the Lebesgue integral of ℝ≥0∞ and nnreal functions

We prove `∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q`
conjugate real exponents and `α→(e)nnreal` functions in several cases, the first two being useful
only to prove the more general results:
* `ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one` : ℝ≥0∞ functions for which the
    integrals on the right are equal to 1,
* `ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top` : ℝ≥0∞ functions for which the
    integrals on the right are neither ⊤ nor 0,
* `ennreal.lintegral_mul_le_Lp_mul_Lq` : ℝ≥0∞ functions,
* `nnreal.lintegral_mul_le_Lp_mul_Lq`  : nnreal functions.
-/


noncomputable theory

open_locale Classical BigOperators Nnreal Ennreal

open MeasureTheory

variable{α : Type _}[MeasurableSpace α]{μ : Measureₓ α}

namespace Ennreal

theorem lintegral_mul_le_one_of_lintegral_rpow_eq_one {p q : ℝ} (hpq : p.is_conjugate_exponent q) {f g : α → ℝ≥0∞}
  (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) (hf_norm : (∫⁻a, f a^p ∂μ) = 1) (hg_norm : (∫⁻a, g a^q ∂μ) = 1) :
  (∫⁻a, (f*g) a ∂μ) ≤ 1 :=
  by 
    calc (∫⁻a : α, (f*g) a ∂μ) ≤ ∫⁻a : α, ((f a^p) / Ennreal.ofReal p)+(g a^q) / Ennreal.ofReal q ∂μ :=
      lintegral_mono fun a => young_inequality (f a) (g a) hpq _ = 1 :=
      by 
        simp only [div_eq_mul_inv]
        rw [lintegral_add']
        ·
          rw [lintegral_mul_const'' _ (hf.pow_const p), lintegral_mul_const'' _ (hg.pow_const q), hf_norm, hg_norm,
            ←div_eq_mul_inv, ←div_eq_mul_inv, hpq.inv_add_inv_conj_ennreal]
        ·
          exact (hf.pow_const _).mul_const _
        ·
          exact (hg.pow_const _).mul_const _

/-- Function multiplied by the inverse of its p-seminorm `(∫⁻ f^p ∂μ) ^ 1/p`-/
def fun_mul_inv_snorm (f : α → ℝ≥0∞) (p : ℝ) (μ : Measureₓ α) : α → ℝ≥0∞ :=
  fun a => f a*((∫⁻c, f c^p ∂μ)^1 / p)⁻¹

theorem fun_eq_fun_mul_inv_snorm_mul_snorm {p : ℝ} (f : α → ℝ≥0∞) (hf_nonzero : (∫⁻a, f a^p ∂μ) ≠ 0)
  (hf_top : (∫⁻a, f a^p ∂μ) ≠ ⊤) {a : α} : f a = fun_mul_inv_snorm f p μ a*(∫⁻c, f c^p ∂μ)^1 / p :=
  by 
    simp [fun_mul_inv_snorm, mul_assocₓ, inv_mul_cancel, hf_nonzero, hf_top]

theorem fun_mul_inv_snorm_rpow {p : ℝ} (hp0 : 0 < p) {f : α → ℝ≥0∞} {a : α} :
  (fun_mul_inv_snorm f p μ a^p) = (f a^p)*(∫⁻c, f c^p ∂μ)⁻¹ :=
  by 
    rw [fun_mul_inv_snorm, mul_rpow_of_nonneg _ _ (le_of_ltₓ hp0)]
    suffices h_inv_rpow : (((∫⁻c : α, f c^p ∂μ)^1 / p)⁻¹^p) = (∫⁻c : α, f c^p ∂μ)⁻¹
    ·
      rw [h_inv_rpow]
    rw [inv_rpow, ←rpow_mul, one_div_mul_cancel hp0.ne', rpow_one]

theorem lintegral_rpow_fun_mul_inv_snorm_eq_one {p : ℝ} (hp0_lt : 0 < p) {f : α → ℝ≥0∞} (hf : AeMeasurable f μ)
  (hf_nonzero : (∫⁻a, f a^p ∂μ) ≠ 0) (hf_top : (∫⁻a, f a^p ∂μ) ≠ ⊤) : (∫⁻c, fun_mul_inv_snorm f p μ c^p ∂μ) = 1 :=
  by 
    simpRw [fun_mul_inv_snorm_rpow hp0_lt]
    rw [lintegral_mul_const'' _ (hf.pow_const p), mul_inv_cancel hf_nonzero hf_top]

-- error in MeasureTheory.Integral.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Hölder's inequality in case of finite non-zero integrals -/
theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top
{p q : exprℝ()}
(hpq : p.is_conjugate_exponent q)
{f g : α → «exprℝ≥0∞»()}
(hf : ae_measurable f μ)
(hg : ae_measurable g μ)
(hf_nontop : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr⊤»()))
(hg_nontop : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, q), μ), «expr⊤»()))
(hf_nonzero : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), 0))
(hg_nonzero : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, q), μ), 0)) : «expr ≤ »(«expr∫⁻ , ∂ »((a), «expr * »(f, g) a, μ), «expr * »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr / »(1, p)), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, q), μ), «expr / »(1, q)))) :=
begin
  let [ident npf] [] [":=", expr «expr ^ »(«expr∫⁻ , ∂ »((c : α), «expr ^ »(f c, p), μ), «expr / »(1, p))],
  let [ident nqg] [] [":=", expr «expr ^ »(«expr∫⁻ , ∂ »((c : α), «expr ^ »(g c, q), μ), «expr / »(1, q))],
  calc
    «expr = »(«expr∫⁻ , ∂ »((a : α), «expr * »(f, g) a, μ), «expr∫⁻ , ∂ »((a : α), «expr * »(«expr * »(fun_mul_inv_snorm f p μ, fun_mul_inv_snorm g q μ) a, «expr * »(npf, nqg)), μ)) : begin
      refine [expr lintegral_congr (λ a, _)],
      rw ["[", expr pi.mul_apply, ",", expr fun_eq_fun_mul_inv_snorm_mul_snorm f hf_nonzero hf_nontop, ",", expr fun_eq_fun_mul_inv_snorm_mul_snorm g hg_nonzero hg_nontop, ",", expr pi.mul_apply, "]"] [],
      ring []
    end
    «expr ≤ »(..., «expr * »(npf, nqg)) : begin
      rw [expr lintegral_mul_const' «expr * »(npf, nqg) _ (by simp [] [] [] ["[", expr hf_nontop, ",", expr hg_nontop, ",", expr hf_nonzero, ",", expr hg_nonzero, "]"] [] [])] [],
      nth_rewrite [1] ["<-", expr one_mul «expr * »(npf, nqg)] [],
      refine [expr mul_le_mul _ (le_refl «expr * »(npf, nqg))],
      have [ident hf1] [] [":=", expr lintegral_rpow_fun_mul_inv_snorm_eq_one hpq.pos hf hf_nonzero hf_nontop],
      have [ident hg1] [] [":=", expr lintegral_rpow_fun_mul_inv_snorm_eq_one hpq.symm.pos hg hg_nonzero hg_nontop],
      exact [expr lintegral_mul_le_one_of_lintegral_rpow_eq_one hpq (hf.mul_const _) (hg.mul_const _) hf1 hg1]
    end
end

theorem ae_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0_lt : 0 < p) {f : α → ℝ≥0∞} (hf : AeMeasurable f μ)
  (hf_zero : (∫⁻a, f a^p ∂μ) = 0) : f =ᵐ[μ] 0 :=
  by 
    rw [lintegral_eq_zero_iff' (hf.pow_const p)] at hf_zero 
    refine' Filter.Eventually.mp hf_zero (Filter.eventually_of_forall fun x => _)
    dsimp only 
    rw [Pi.zero_apply, rpow_eq_zero_iff]
    intro hx 
    cases hx
    ·
      exact hx.left
    ·
      exfalso 
      linarith

-- error in MeasureTheory.Integral.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero
{p : exprℝ()}
(hp0_lt : «expr < »(0, p))
{f g : α → «exprℝ≥0∞»()}
(hf : ae_measurable f μ)
(hf_zero : «expr = »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), 0)) : «expr = »(«expr∫⁻ , ∂ »((a), «expr * »(f, g) a, μ), 0) :=
begin
  rw ["<-", expr @lintegral_zero_fun α _ μ] [],
  refine [expr lintegral_congr_ae _],
  suffices [ident h_mul_zero] [":", expr «expr =ᵐ[ ] »(«expr * »(f, g), μ, «expr * »(0, g))],
  by rwa [expr zero_mul] ["at", ident h_mul_zero],
  have [ident hf_eq_zero] [":", expr «expr =ᵐ[ ] »(f, μ, 0)] [],
  from [expr ae_eq_zero_of_lintegral_rpow_eq_zero hp0_lt hf hf_zero],
  exact [expr filter.eventually_eq.mul hf_eq_zero (ae_eq_refl g)]
end

-- error in MeasureTheory.Integral.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top
{p q : exprℝ()}
(hp0_lt : «expr < »(0, p))
(hq0 : «expr ≤ »(0, q))
{f g : α → «exprℝ≥0∞»()}
(hf_top : «expr = »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr⊤»()))
(hg_nonzero : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, q), μ), 0)) : «expr ≤ »(«expr∫⁻ , ∂ »((a), «expr * »(f, g) a, μ), «expr * »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr / »(1, p)), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, q), μ), «expr / »(1, q)))) :=
begin
  refine [expr le_trans le_top (le_of_eq _)],
  have [ident hp0_inv_lt] [":", expr «expr < »(0, «expr / »(1, p))] [],
  by simp [] [] [] ["[", expr hp0_lt, "]"] [] [],
  rw ["[", expr hf_top, ",", expr ennreal.top_rpow_of_pos hp0_inv_lt, "]"] [],
  simp [] [] [] ["[", expr hq0, ",", expr hg_nonzero, "]"] [] []
end

/-- Hölder's inequality for functions `α → ℝ≥0∞`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem lintegral_mul_le_Lp_mul_Lq (μ : Measureₓ α) {p q : ℝ} (hpq : p.is_conjugate_exponent q) {f g : α → ℝ≥0∞}
  (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) : (∫⁻a, (f*g) a ∂μ) ≤ ((∫⁻a, f a^p ∂μ)^1 / p)*(∫⁻a, g a^q ∂μ)^1 / q :=
  by 
    byCases' hf_zero : (∫⁻a, f a^p ∂μ) = 0
    ·
      refine' le_transₓ (le_of_eqₓ _) (zero_le _)
      exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.pos hf hf_zero 
    byCases' hg_zero : (∫⁻a, g a^q ∂μ) = 0
    ·
      refine' le_transₓ (le_of_eqₓ _) (zero_le _)
      rw [mul_commₓ]
      exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.symm.pos hg hg_zero 
    byCases' hf_top : (∫⁻a, f a^p ∂μ) = ⊤
    ·
      exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.pos hpq.symm.nonneg hf_top hg_zero 
    byCases' hg_top : (∫⁻a, g a^q ∂μ) = ⊤
    ·
      rw [mul_commₓ, mul_commₓ ((∫⁻a : α, f a^p ∂μ)^1 / p)]
      exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.symm.pos hpq.nonneg hg_top hf_zero 
    exact Ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top hpq hf hg hf_top hg_top hf_zero hg_zero

-- error in MeasureTheory.Integral.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top
{p : exprℝ()}
{f g : α → «exprℝ≥0∞»()}
(hf : ae_measurable f μ)
(hf_top : «expr < »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr⊤»()))
(hg : ae_measurable g μ)
(hg_top : «expr < »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, p), μ), «expr⊤»()))
(hp1 : «expr ≤ »(1, p)) : «expr < »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), «expr⊤»()) :=
begin
  have [ident hp0_lt] [":", expr «expr < »(0, p)] [],
  from [expr lt_of_lt_of_le zero_lt_one hp1],
  have [ident hp0] [":", expr «expr ≤ »(0, p)] [],
  from [expr le_of_lt hp0_lt],
  calc
    «expr ≤ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(«expr + »(f a, g a), p), μ), «expr∫⁻ , ∂ »((a), «expr + »(«expr * »(«expr ^ »((2 : «exprℝ≥0∞»()), «expr - »(p, 1)), «expr ^ »(f a, p)), «expr * »(«expr ^ »((2 : «exprℝ≥0∞»()), «expr - »(p, 1)), «expr ^ »(g a, p))), μ)) : begin
      refine [expr lintegral_mono (λ a, _)],
      dsimp ["only"] [] [] [],
      have [ident h_zero_lt_half_rpow] [":", expr «expr < »((0 : «exprℝ≥0∞»()), «expr ^ »(«expr / »(1, 2), p))] [],
      { rw ["[", "<-", expr ennreal.zero_rpow_of_pos hp0_lt, "]"] [],
        exact [expr ennreal.rpow_lt_rpow (by simp [] [] [] ["[", expr zero_lt_one, "]"] [] []) hp0_lt] },
      have [ident h_rw] [":", expr «expr = »(«expr * »(«expr ^ »(«expr / »(1, 2), p), «expr ^ »((2 : «exprℝ≥0∞»()), «expr - »(p, 1))), «expr / »(1, 2))] [],
      { rw ["[", expr sub_eq_add_neg, ",", expr ennreal.rpow_add _ _ ennreal.two_ne_zero ennreal.coe_ne_top, ",", "<-", expr mul_assoc, ",", "<-", expr ennreal.mul_rpow_of_nonneg _ _ hp0, ",", expr one_div, ",", expr ennreal.inv_mul_cancel ennreal.two_ne_zero ennreal.coe_ne_top, ",", expr ennreal.one_rpow, ",", expr one_mul, ",", expr ennreal.rpow_neg_one, "]"] [] },
      rw ["<-", expr ennreal.mul_le_mul_left (ne_of_lt h_zero_lt_half_rpow).symm _] [],
      { rw ["[", expr mul_add, ",", "<-", expr mul_assoc, ",", "<-", expr mul_assoc, ",", expr h_rw, ",", "<-", expr ennreal.mul_rpow_of_nonneg _ _ hp0, ",", expr mul_add, "]"] [],
        refine [expr ennreal.rpow_arith_mean_le_arith_mean2_rpow («expr / »(1, 2) : «exprℝ≥0∞»()) («expr / »(1, 2) : «exprℝ≥0∞»()) (f a) (g a) _ hp1],
        rw ["[", expr ennreal.div_add_div_same, ",", expr one_add_one_eq_two, ",", expr ennreal.div_self ennreal.two_ne_zero ennreal.coe_ne_top, "]"] [] },
      { rw ["<-", expr lt_top_iff_ne_top] [],
        refine [expr ennreal.rpow_lt_top_of_nonneg hp0 _],
        rw ["[", expr one_div, ",", expr ennreal.inv_ne_top, "]"] [],
        exact [expr ennreal.two_ne_zero] }
    end
    «expr < »(..., «expr⊤»()) : begin
      rw ["[", expr lintegral_add', ",", expr lintegral_const_mul'' _ (hf.pow_const p), ",", expr lintegral_const_mul'' _ (hg.pow_const p), ",", expr ennreal.add_lt_top, "]"] [],
      { have [ident h_two] [":", expr «expr < »(«expr ^ »((2 : «exprℝ≥0∞»()), «expr - »(p, 1)), «expr⊤»())] [],
        from [expr ennreal.rpow_lt_top_of_nonneg (by simp [] [] [] ["[", expr hp1, "]"] [] []) ennreal.coe_ne_top],
        repeat { rw [expr ennreal.mul_lt_top_iff] [] },
        simp [] [] [] ["[", expr hf_top, ",", expr hg_top, ",", expr h_two, "]"] [] [] },
      { exact [expr (hf.pow_const _).const_mul _] },
      { exact [expr (hg.pow_const _).const_mul _] }
    end
end

-- error in MeasureTheory.Integral.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lintegral_Lp_mul_le_Lq_mul_Lr
{α}
[measurable_space α]
{p q r : exprℝ()}
(hp0_lt : «expr < »(0, p))
(hpq : «expr < »(p, q))
(hpqr : «expr = »(«expr / »(1, p), «expr + »(«expr / »(1, q), «expr / »(1, r))))
(μ : measure α)
{f g : α → «exprℝ≥0∞»()}
(hf : ae_measurable f μ)
(hg : ae_measurable g μ) : «expr ≤ »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr * »(f, g) a, p), μ), «expr / »(1, p)), «expr * »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, q), μ), «expr / »(1, q)), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, r), μ), «expr / »(1, r)))) :=
begin
  have [ident hp0_ne] [":", expr «expr ≠ »(p, 0)] [],
  from [expr (ne_of_lt hp0_lt).symm],
  have [ident hp0] [":", expr «expr ≤ »(0, p)] [],
  from [expr le_of_lt hp0_lt],
  have [ident hq0_lt] [":", expr «expr < »(0, q)] [],
  from [expr lt_of_le_of_lt hp0 hpq],
  have [ident hq0_ne] [":", expr «expr ≠ »(q, 0)] [],
  from [expr (ne_of_lt hq0_lt).symm],
  have [ident h_one_div_r] [":", expr «expr = »(«expr / »(1, r), «expr - »(«expr / »(1, p), «expr / »(1, q)))] [],
  by simp [] [] [] ["[", expr hpqr, "]"] [] [],
  have [ident hr0_ne] [":", expr «expr ≠ »(r, 0)] [],
  { have [ident hr_inv_pos] [":", expr «expr < »(0, «expr / »(1, r))] [],
    by rwa ["[", expr h_one_div_r, ",", expr sub_pos, ",", expr one_div_lt_one_div hq0_lt hp0_lt, "]"] [],
    rw ["[", expr one_div, ",", expr _root_.inv_pos, "]"] ["at", ident hr_inv_pos],
    exact [expr (ne_of_lt hr_inv_pos).symm] },
  let [ident p2] [] [":=", expr «expr / »(q, p)],
  let [ident q2] [] [":=", expr p2.conjugate_exponent],
  have [ident hp2q2] [":", expr p2.is_conjugate_exponent q2] [],
  from [expr real.is_conjugate_exponent_conjugate_exponent (by simp [] [] [] ["[", expr lt_div_iff, ",", expr hpq, ",", expr hp0_lt, "]"] [] [])],
  calc
    «expr = »(«expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(«expr * »(f, g) a, p), μ), «expr / »(1, p)), «expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr * »(«expr ^ »(f a, p), «expr ^ »(g a, p)), μ), «expr / »(1, p))) : by simp_rw ["[", expr pi.mul_apply, ",", expr ennreal.mul_rpow_of_nonneg _ _ hp0, "]"] []
    «expr ≤ »(..., «expr ^ »(«expr * »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, «expr * »(p, p2)), μ), «expr / »(1, p2)), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, «expr * »(p, q2)), μ), «expr / »(1, q2))), «expr / »(1, p))) : begin
      refine [expr ennreal.rpow_le_rpow _ (by simp [] [] [] ["[", expr hp0, "]"] [] [])],
      simp_rw [expr ennreal.rpow_mul] [],
      exact [expr ennreal.lintegral_mul_le_Lp_mul_Lq μ hp2q2 (hf.pow_const _) (hg.pow_const _)]
    end
    «expr = »(..., «expr * »(«expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(f a, q), μ), «expr / »(1, q)), «expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(g a, r), μ), «expr / »(1, r)))) : begin
      rw ["[", expr @ennreal.mul_rpow_of_nonneg _ _ «expr / »(1, p) (by simp [] [] [] ["[", expr hp0, "]"] [] []), ",", "<-", expr ennreal.rpow_mul, ",", "<-", expr ennreal.rpow_mul, "]"] [],
      have [ident hpp2] [":", expr «expr = »(«expr * »(p, p2), q)] [],
      { symmetry,
        rw ["[", expr mul_comm, ",", "<-", expr div_eq_iff hp0_ne, "]"] [] },
      have [ident hpq2] [":", expr «expr = »(«expr * »(p, q2), r)] [],
      { rw ["[", "<-", expr inv_inv₀ r, ",", "<-", expr one_div, ",", "<-", expr one_div, ",", expr h_one_div_r, "]"] [],
        field_simp [] ["[", expr q2, ",", expr real.conjugate_exponent, ",", expr p2, ",", expr hp0_ne, ",", expr hq0_ne, "]"] [] [] },
      simp_rw ["[", expr div_mul_div, ",", expr mul_one, ",", expr mul_comm p2, ",", expr mul_comm q2, ",", expr hpp2, ",", expr hpq2, "]"] []
    end
end

-- error in MeasureTheory.Integral.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
{p q : exprℝ()}
(hpq : p.is_conjugate_exponent q)
{f g : α → «exprℝ≥0∞»()}
(hf : ae_measurable f μ)
(hg : ae_measurable g μ)
(hf_top : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr⊤»())) : «expr ≤ »(«expr∫⁻ , ∂ »((a), «expr * »(f a, «expr ^ »(g a, «expr - »(p, 1))), μ), «expr * »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr / »(1, p)), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, p), μ), «expr / »(1, q)))) :=
begin
  refine [expr le_trans (ennreal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (hg.pow_const _)) _],
  by_cases [expr hf_zero_rpow, ":", expr «expr = »(«expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(f a, p), μ), «expr / »(1, p)), 0)],
  { rw ["[", expr hf_zero_rpow, ",", expr zero_mul, "]"] [],
    exact [expr zero_le _] },
  have [ident hf_top_rpow] [":", expr «expr ≠ »(«expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(f a, p), μ), «expr / »(1, p)), «expr⊤»())] [],
  { by_contra [ident h],
    refine [expr hf_top _],
    have [ident hp_not_neg] [":", expr «expr¬ »(«expr < »(p, 0))] [],
    by simp [] [] [] ["[", expr hpq.nonneg, "]"] [] [],
    simpa [] [] [] ["[", expr hpq.pos, ",", expr hp_not_neg, "]"] [] ["using", expr h] },
  refine [expr (ennreal.mul_le_mul_left hf_zero_rpow hf_top_rpow).mpr (le_of_eq _)],
  congr,
  ext1 [] [ident a],
  rw ["[", "<-", expr ennreal.rpow_mul, ",", expr hpq.sub_one_mul_conj, "]"] []
end

-- error in MeasureTheory.Integral.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add
{p q : exprℝ()}
(hpq : p.is_conjugate_exponent q)
{f g : α → «exprℝ≥0∞»()}
(hf : ae_measurable f μ)
(hf_top : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr⊤»()))
(hg : ae_measurable g μ)
(hg_top : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, p), μ), «expr⊤»())) : «expr ≤ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), «expr * »(«expr + »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr / »(1, p)), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, p), μ), «expr / »(1, p))), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f a, g a), p), μ), «expr / »(1, q)))) :=
begin
  calc
    «expr ≤ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), «expr∫⁻ , ∂ »((a), «expr * »(«expr + »(f, g) a, «expr ^ »(«expr + »(f, g) a, «expr - »(p, 1))), μ)) : begin
      refine [expr lintegral_mono (λ a, _)],
      dsimp ["only"] [] [] [],
      by_cases [expr h_zero, ":", expr «expr = »(«expr + »(f, g) a, 0)],
      { rw ["[", expr h_zero, ",", expr ennreal.zero_rpow_of_pos hpq.pos, "]"] [],
        exact [expr zero_le _] },
      by_cases [expr h_top, ":", expr «expr = »(«expr + »(f, g) a, «expr⊤»())],
      { rw ["[", expr h_top, ",", expr ennreal.top_rpow_of_pos hpq.sub_one_pos, ",", expr ennreal.top_mul_top, "]"] [],
        exact [expr le_top] },
      refine [expr le_of_eq _],
      nth_rewrite [1] ["<-", expr ennreal.rpow_one («expr + »(f, g) a)] [],
      rw ["[", "<-", expr ennreal.rpow_add _ _ h_zero h_top, ",", expr add_sub_cancel'_right, "]"] []
    end
    «expr = »(..., «expr + »(«expr∫⁻ , ∂ »((a : α), «expr * »(f a, «expr ^ »(«expr + »(f, g) a, «expr - »(p, 1))), μ), «expr∫⁻ , ∂ »((a : α), «expr * »(g a, «expr ^ »(«expr + »(f, g) a, «expr - »(p, 1))), μ))) : begin
      have [ident h_add_m] [":", expr ae_measurable (λ a : α, «expr ^ »(«expr + »(f, g) a, «expr - »(p, 1))) μ] [],
      from [expr (hf.add hg).pow_const _],
      have [ident h_add_apply] [":", expr «expr = »(«expr∫⁻ , ∂ »((a : α), «expr * »(«expr + »(f, g) a, «expr ^ »(«expr + »(f, g) a, «expr - »(p, 1))), μ), «expr∫⁻ , ∂ »((a : α), «expr * »(«expr + »(f a, g a), «expr ^ »(«expr + »(f, g) a, «expr - »(p, 1))), μ))] [],
      from [expr rfl],
      simp_rw ["[", expr h_add_apply, ",", expr add_mul, "]"] [],
      rw [expr lintegral_add' (hf.mul h_add_m) (hg.mul h_add_m)] []
    end
    «expr ≤ »(..., «expr * »(«expr + »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr / »(1, p)), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, p), μ), «expr / »(1, p))), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f a, g a), p), μ), «expr / »(1, q)))) : begin
      rw [expr add_mul] [],
      exact [expr add_le_add (lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hf (hf.add hg) hf_top) (lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hg (hf.add hg) hg_top)]
    end
end

-- error in MeasureTheory.Integral.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem lintegral_Lp_add_le_aux
{p q : exprℝ()}
(hpq : p.is_conjugate_exponent q)
{f g : α → «exprℝ≥0∞»()}
(hf : ae_measurable f μ)
(hf_top : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr⊤»()))
(hg : ae_measurable g μ)
(hg_top : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, p), μ), «expr⊤»()))
(h_add_zero : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), 0))
(h_add_top : «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), «expr⊤»())) : «expr ≤ »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), «expr / »(1, p)), «expr + »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr / »(1, p)), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, p), μ), «expr / »(1, p)))) :=
begin
  have [ident hp_not_nonpos] [":", expr «expr¬ »(«expr ≤ »(p, 0))] [],
  by simp [] [] [] ["[", expr hpq.pos, "]"] [] [],
  have [ident htop_rpow] [":", expr «expr ≠ »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), «expr / »(1, p)), «expr⊤»())] [],
  { by_contra [ident h],
    exact [expr h_add_top (@ennreal.rpow_eq_top_of_nonneg _ «expr / »(1, p) (by simp [] [] [] ["[", expr hpq.nonneg, "]"] [] []) h)] },
  have [ident h0_rpow] [":", expr «expr ≠ »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), «expr / »(1, p)), 0)] [],
  by simp [] [] [] ["[", expr h_add_zero, ",", expr h_add_top, ",", expr hpq.nonneg, ",", expr hp_not_nonpos, ",", "-", ident pi.add_apply, "]"] [] [],
  suffices [ident h] [":", expr «expr ≤ »(1, «expr * »(«expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(«expr + »(f, g) a, p), μ), «expr- »(«expr / »(1, p))), «expr + »(«expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(f a, p), μ), «expr / »(1, p)), «expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(g a, p), μ), «expr / »(1, p)))))],
  by rwa ["[", "<-", expr mul_le_mul_left h0_rpow htop_rpow, ",", "<-", expr mul_assoc, ",", "<-", expr rpow_add _ _ h_add_zero h_add_top, ",", "<-", expr sub_eq_add_neg, ",", expr _root_.sub_self, ",", expr rpow_zero, ",", expr one_mul, ",", expr mul_one, "]"] ["at", ident h],
  have [ident h] [":", expr «expr ≤ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(«expr + »(f, g) a, p), μ), «expr * »(«expr + »(«expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(f a, p), μ), «expr / »(1, p)), «expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(g a, p), μ), «expr / »(1, p))), «expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(«expr + »(f, g) a, p), μ), «expr / »(1, q))))] [],
  from [expr lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add hpq hf hf_top hg hg_top],
  have [ident h_one_div_q] [":", expr «expr = »(«expr / »(1, q), «expr - »(1, «expr / »(1, p)))] [],
  by { nth_rewrite [1] ["<-", expr hpq.inv_add_inv_conj] [],
    ring [] },
  simp_rw ["[", expr h_one_div_q, ",", expr sub_eq_add_neg 1 «expr / »(1, p), ",", expr ennreal.rpow_add _ _ h_add_zero h_add_top, ",", expr rpow_one, "]"] ["at", ident h],
  nth_rewrite [1] [expr mul_comm] ["at", ident h],
  nth_rewrite [0] ["<-", expr one_mul «expr∫⁻ , ∂ »((a : α), «expr ^ »(«expr + »(f, g) a, p), μ)] ["at", ident h],
  rwa ["[", "<-", expr mul_assoc, ",", expr ennreal.mul_le_mul_right h_add_zero h_add_top, ",", expr mul_comm, "]"] ["at", ident h]
end

-- error in MeasureTheory.Integral.MeanInequalities: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Minkowski's inequality for functions `α → ℝ≥0∞`: the `ℒp` seminorm of the sum of two
functions is bounded by the sum of their `ℒp` seminorms. -/
theorem lintegral_Lp_add_le
{p : exprℝ()}
{f g : α → «exprℝ≥0∞»()}
(hf : ae_measurable f μ)
(hg : ae_measurable g μ)
(hp1 : «expr ≤ »(1, p)) : «expr ≤ »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), «expr / »(1, p)), «expr + »(«expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr / »(1, p)), «expr ^ »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, p), μ), «expr / »(1, p)))) :=
begin
  have [ident hp_pos] [":", expr «expr < »(0, p)] [],
  from [expr lt_of_lt_of_le zero_lt_one hp1],
  by_cases [expr hf_top, ":", expr «expr = »(«expr∫⁻ , ∂ »((a), «expr ^ »(f a, p), μ), «expr⊤»())],
  { simp [] [] [] ["[", expr hf_top, ",", expr hp_pos, "]"] [] [] },
  by_cases [expr hg_top, ":", expr «expr = »(«expr∫⁻ , ∂ »((a), «expr ^ »(g a, p), μ), «expr⊤»())],
  { simp [] [] [] ["[", expr hg_top, ",", expr hp_pos, "]"] [] [] },
  by_cases [expr h1, ":", expr «expr = »(p, 1)],
  { refine [expr le_of_eq _],
    simp_rw ["[", expr h1, ",", expr one_div_one, ",", expr ennreal.rpow_one, "]"] [],
    exact [expr lintegral_add' hf hg] },
  have [ident hp1_lt] [":", expr «expr < »(1, p)] [],
  by { refine [expr lt_of_le_of_ne hp1 _],
    symmetry,
    exact [expr h1] },
  have [ident hpq] [] [":=", expr real.is_conjugate_exponent_conjugate_exponent hp1_lt],
  by_cases [expr h0, ":", expr «expr = »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), 0)],
  { rw ["[", expr h0, ",", expr @ennreal.zero_rpow_of_pos «expr / »(1, p) (by simp [] [] [] ["[", expr lt_of_lt_of_le zero_lt_one hp1, "]"] [] []), "]"] [],
    exact [expr zero_le _] },
  have [ident htop] [":", expr «expr ≠ »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr + »(f, g) a, p), μ), «expr⊤»())] [],
  { rw ["<-", expr ne.def] ["at", ident hf_top, ident hg_top],
    rw ["<-", expr lt_top_iff_ne_top] ["at", ident hf_top, ident hg_top, "⊢"],
    exact [expr lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top hf hf_top hg hg_top hp1] },
  exact [expr lintegral_Lp_add_le_aux hpq hf hf_top hg hg_top h0 htop]
end

end Ennreal

/-- Hölder's inequality for functions `α → ℝ≥0`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem Nnreal.lintegral_mul_le_Lp_mul_Lq {p q : ℝ} (hpq : p.is_conjugate_exponent q) {f g : α →  ℝ≥0 }
  (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) : (∫⁻a, (f*g) a ∂μ) ≤ ((∫⁻a, f a^p ∂μ)^1 / p)*(∫⁻a, g a^q ∂μ)^1 / q :=
  by 
    simpRw [Pi.mul_apply, Ennreal.coe_mul]
    exact Ennreal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.coe_nnreal_ennreal hg.coe_nnreal_ennreal

end Lintegral

