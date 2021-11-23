import Mathbin.MeasureTheory.Measure.Regular 
import Mathbin.Topology.Semicontinuous 
import Mathbin.MeasureTheory.Integral.Bochner 
import Mathbin.Topology.Instances.Ereal

/-!
# Vitali-Carathéodory theorem

Vitali-Carathéodory theorem asserts the following. Consider an integrable function `f : α → ℝ` on
a space with a regular measure. Then there exists a function `g : α → ereal` such that `f x < g x`
everywhere, `g` is lower semicontinuous, and the integral of `g` is arbitrarily close to that of
`f`. This theorem is proved in this file, as `exists_lt_lower_semicontinuous_integral_lt`.

Symmetrically, there exists `g < f` which is upper semicontinuous, with integral arbitrarily close
to that of `f`. It follows from the previous statement applied to `-f`. It is formalized under
the name `exists_upper_semicontinuous_lt_integral_gt`.

The most classical version of Vitali-Carathéodory theorem only ensures a large inequality
`f x ≤ g x`. For applications to the fundamental theorem of calculus, though, the strict inequality
`f x < g x` is important. Therefore, we prove the stronger version with strict inequalities in this
file. There is a price to pay: we require that the measure is `σ`-finite, which is not necessary for
the classical Vitali-Carathéodory theorem. Since this is satisfied in all applications, this is
not a real problem.

## Sketch of proof

Decomposing `f` as the difference of its positive and negative parts, it suffices to show that a
positive function can be bounded from above by a lower semicontinuous function, and from below
by an upper semicontinuous function, with integrals close to that of `f`.

For the bound from above, write `f` as a series `∑' n, cₙ * indicator (sₙ)` of simple functions.
Then, approximate `sₙ` by a larger open set `uₙ` with measure very close to that of `sₙ` (this is
possible by regularity of the measure), and set `g = ∑' n, cₙ * indicator (uₙ)`. It is
lower semicontinuous as a series of lower semicontinuous functions, and its integral is arbitrarily
close to that of `f`.

For the bound from below, use finitely many terms in the series, and approximate `sₙ` from inside by
a closed set `Fₙ`. Then `∑ n < N, cₙ * indicator (Fₙ)` is bounded from above by `f`, it is
upper semicontinuous as a finite sum of upper semicontinuous functions, and its integral is
arbitrarily close to that of `f`.

The main pain point in the implementation is that one needs to jump between the spaces `ℝ`, `ℝ≥0`,
`ℝ≥0∞` and `ereal` (and be careful that addition is not well behaved on `ereal`), and between
`lintegral` and `integral`.

We first show the bound from above for simple functions and the nonnegative integral
(this is the main nontrivial mathematical point), then deduce it for general nonnegative functions,
first for the nonnegative integral and then for the Bochner integral.

Then we follow the same steps for the lower bound.

Finally, we glue them together to obtain the main statement
`exists_lt_lower_semicontinuous_integral_lt`.

## Related results

Are you looking for a result on approximation by continuous functions (not just semicontinuous)?
See result `measure_theory.Lp.continuous_map_dense`, in the file
`measure_theory.continuous_map_dense`.

## References

[Rudin, *Real and Complex Analysis* (Theorem 2.24)][rudin2006real]

-/


open_locale Ennreal Nnreal

open MeasureTheory MeasureTheory.Measure

variable{α : Type _}[TopologicalSpace α][MeasurableSpace α][BorelSpace α](μ : Measureₓ α)[weakly_regular μ]

namespace MeasureTheory

local infixr:25 " →ₛ " => simple_func

/-! ### Lower semicontinuous upper bound for nonnegative functions -/


-- error in MeasureTheory.Integral.VitaliCaratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a simple function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem simple_func.exists_le_lower_semicontinuous_lintegral_ge
(f : «expr →ₛ »(α, «exprℝ≥0»()))
{ε : «exprℝ≥0∞»()}
(ε0 : «expr ≠ »(ε, 0)) : «expr∃ , »((g : α → «exprℝ≥0»()), «expr ∧ »(∀
  x, «expr ≤ »(f x, g x), «expr ∧ »(lower_semicontinuous g, «expr ≤ »(«expr∫⁻ , ∂ »((x), g x, μ), «expr + »(«expr∫⁻ , ∂ »((x), f x, μ), ε))))) :=
begin
  induction [expr f] ["using", ident measure_theory.simple_func.induction] ["with", ident c, ident s, ident hs, ident f₁, ident f₂, ident H, ident h₁, ident h₂] ["generalizing", ident ε],
  { let [ident f] [] [":=", expr simple_func.piecewise s hs (simple_func.const α c) (simple_func.const α 0)],
    by_cases [expr h, ":", expr «expr = »(«expr∫⁻ , ∂ »((x), f x, μ), «expr⊤»())],
    { refine [expr ⟨λ
        x, c, λ
        x, _, lower_semicontinuous_const, by simp [] [] ["only"] ["[", expr ennreal.top_add, ",", expr le_top, ",", expr h, "]"] [] []⟩],
      simp [] [] ["only"] ["[", expr simple_func.coe_const, ",", expr simple_func.const_zero, ",", expr simple_func.coe_zero, ",", expr set.piecewise_eq_indicator, ",", expr simple_func.coe_piecewise, "]"] [] [],
      exact [expr set.indicator_le_self _ _ _] },
    by_cases [expr hc, ":", expr «expr = »(c, 0)],
    { refine [expr ⟨λ x, 0, _, lower_semicontinuous_const, _⟩],
      { simp [] [] ["only"] ["[", expr hc, ",", expr set.indicator_zero', ",", expr pi.zero_apply, ",", expr simple_func.const_zero, ",", expr implies_true_iff, ",", expr eq_self_iff_true, ",", expr simple_func.coe_zero, ",", expr set.piecewise_eq_indicator, ",", expr simple_func.coe_piecewise, ",", expr le_zero_iff, "]"] [] [] },
      { simp [] [] ["only"] ["[", expr lintegral_const, ",", expr zero_mul, ",", expr zero_le, ",", expr ennreal.coe_zero, "]"] [] [] } },
    have [] [":", expr «expr < »(μ s, «expr + »(μ s, «expr / »(ε, c)))] [],
    { have [] [":", expr «expr < »((0 : «exprℝ≥0∞»()), «expr / »(ε, c))] [":=", expr ennreal.div_pos_iff.2 ⟨ε0, ennreal.coe_ne_top⟩],
      simpa [] [] [] [] [] ["using", expr ennreal.add_lt_add_left _ this],
      simpa [] [] ["only"] ["[", expr hs, ",", expr hc, ",", expr lt_top_iff_ne_top, ",", expr true_and, ",", expr simple_func.coe_const, ",", expr function.const_apply, ",", expr lintegral_const, ",", expr ennreal.coe_indicator, ",", expr set.univ_inter, ",", expr ennreal.coe_ne_top, ",", expr measurable_set.univ, ",", expr with_top.mul_eq_top_iff, ",", expr simple_func.const_zero, ",", expr or_false, ",", expr lintegral_indicator, ",", expr ennreal.coe_eq_zero, ",", expr ne.def, ",", expr not_false_iff, ",", expr simple_func.coe_zero, ",", expr set.piecewise_eq_indicator, ",", expr simple_func.coe_piecewise, ",", expr false_and, ",", expr restrict_apply, "]"] [] ["using", expr h] },
    obtain ["⟨", ident u, ",", ident su, ",", ident u_open, ",", ident μu, "⟩", ":", expr «expr∃ , »((u «expr ⊇ » s), «expr ∧ »(is_open u, «expr < »(μ u, «expr + »(μ s, «expr / »(ε, c))))), ":=", expr s.exists_is_open_lt_of_lt _ this],
    refine [expr ⟨set.indicator u (λ x, c), λ x, _, u_open.lower_semicontinuous_indicator (zero_le _), _⟩],
    { simp [] [] ["only"] ["[", expr simple_func.coe_const, ",", expr simple_func.const_zero, ",", expr simple_func.coe_zero, ",", expr set.piecewise_eq_indicator, ",", expr simple_func.coe_piecewise, "]"] [] [],
      exact [expr set.indicator_le_indicator_of_subset su (λ x, zero_le _) _] },
    { suffices [] [":", expr «expr ≤ »(«expr * »((c : «exprℝ≥0∞»()), μ u), «expr + »(«expr * »(c, μ s), ε))],
      by simpa [] [] ["only"] ["[", expr hs, ",", expr u_open.measurable_set, ",", expr simple_func.coe_const, ",", expr function.const_apply, ",", expr lintegral_const, ",", expr ennreal.coe_indicator, ",", expr set.univ_inter, ",", expr measurable_set.univ, ",", expr simple_func.const_zero, ",", expr lintegral_indicator, ",", expr simple_func.coe_zero, ",", expr set.piecewise_eq_indicator, ",", expr simple_func.coe_piecewise, ",", expr restrict_apply, "]"] [] [],
      calc
        «expr ≤ »(«expr * »((c : «exprℝ≥0∞»()), μ u), «expr * »(c, «expr + »(μ s, «expr / »(ε, c)))) : ennreal.mul_le_mul (le_refl _) μu.le
        «expr = »(..., «expr + »(«expr * »(c, μ s), ε)) : begin
          simp_rw ["[", expr mul_add, "]"] [],
          rw [expr ennreal.mul_div_cancel' _ ennreal.coe_ne_top] [],
          simpa [] [] [] [] [] ["using", expr hc]
        end } },
  { rcases [expr h₁ (ennreal.half_pos ε0).ne', "with", "⟨", ident g₁, ",", ident f₁_le_g₁, ",", ident g₁cont, ",", ident g₁int, "⟩"],
    rcases [expr h₂ (ennreal.half_pos ε0).ne', "with", "⟨", ident g₂, ",", ident f₂_le_g₂, ",", ident g₂cont, ",", ident g₂int, "⟩"],
    refine [expr ⟨λ x, «expr + »(g₁ x, g₂ x), λ x, add_le_add (f₁_le_g₁ x) (f₂_le_g₂ x), g₁cont.add g₂cont, _⟩],
    simp [] [] ["only"] ["[", expr simple_func.coe_add, ",", expr ennreal.coe_add, ",", expr pi.add_apply, "]"] [] [],
    rw ["[", expr lintegral_add f₁.measurable.coe_nnreal_ennreal f₂.measurable.coe_nnreal_ennreal, ",", expr lintegral_add g₁cont.measurable.coe_nnreal_ennreal g₂cont.measurable.coe_nnreal_ennreal, "]"] [],
    convert [] [expr add_le_add g₁int g₂int] ["using", 1],
    conv_lhs [] [] { rw ["<-", expr ennreal.add_halves ε] },
    abel [] [] [] }
end

open simple_func(eapproxDiff tsum_eapprox_diff)

-- error in MeasureTheory.Integral.VitaliCaratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a measurable function `f` with values in `ℝ≥0`, there exists a lower semicontinuous
function `g ≥ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_le_lower_semicontinuous_lintegral_ge
(f : α → «exprℝ≥0∞»())
(hf : measurable f)
{ε : «exprℝ≥0∞»()}
(εpos : «expr ≠ »(ε, 0)) : «expr∃ , »((g : α → «exprℝ≥0∞»()), «expr ∧ »(∀
  x, «expr ≤ »(f x, g x), «expr ∧ »(lower_semicontinuous g, «expr ≤ »(«expr∫⁻ , ∂ »((x), g x, μ), «expr + »(«expr∫⁻ , ∂ »((x), f x, μ), ε))))) :=
begin
  rcases [expr ennreal.exists_pos_sum_of_encodable' εpos exprℕ(), "with", "⟨", ident δ, ",", ident δpos, ",", ident hδ, "⟩"],
  have [] [":", expr ∀
   n, «expr∃ , »((g : α → «exprℝ≥0»()), «expr ∧ »(∀
     x, «expr ≤ »(simple_func.eapprox_diff f n x, g x), «expr ∧ »(lower_semicontinuous g, «expr ≤ »(«expr∫⁻ , ∂ »((x), g x, μ), «expr + »(«expr∫⁻ , ∂ »((x), simple_func.eapprox_diff f n x, μ), δ n)))))] [":=", expr λ
   n, simple_func.exists_le_lower_semicontinuous_lintegral_ge μ (simple_func.eapprox_diff f n) (δpos n).ne'],
  choose [] [ident g] [ident f_le_g, ident gcont, ident hg] ["using", expr this],
  refine [expr ⟨λ x, «expr∑' , »((n), g n x), λ x, _, _, _⟩],
  { rw ["<-", expr tsum_eapprox_diff f hf] [],
    exact [expr ennreal.tsum_le_tsum (λ n, ennreal.coe_le_coe.2 (f_le_g n x))] },
  { apply [expr lower_semicontinuous_tsum (λ n, _)],
    exact [expr ennreal.continuous_coe.comp_lower_semicontinuous (gcont n) (λ x y hxy, ennreal.coe_le_coe.2 hxy)] },
  { calc
      «expr = »(«expr∫⁻ , ∂ »((x), «expr∑' , »((n : exprℕ()), g n x), μ), «expr∑' , »((n), «expr∫⁻ , ∂ »((x), g n x, μ))) : by rw [expr lintegral_tsum (λ
        n, (gcont n).measurable.coe_nnreal_ennreal)] []
      «expr ≤ »(..., «expr∑' , »((n), «expr + »(«expr∫⁻ , ∂ »((x), eapprox_diff f n x, μ), δ n))) : ennreal.tsum_le_tsum hg
      «expr = »(..., «expr + »(«expr∑' , »((n), «expr∫⁻ , ∂ »((x), eapprox_diff f n x, μ)), «expr∑' , »((n), δ n))) : ennreal.tsum_add
      «expr ≤ »(..., «expr + »(«expr∫⁻ , ∂ »((x : α), f x, μ), ε)) : begin
        refine [expr add_le_add _ hδ.le],
        rw ["[", "<-", expr lintegral_tsum, "]"] [],
        { simp_rw ["[", expr tsum_eapprox_diff f hf, ",", expr le_refl, "]"] [] },
        { assume [binders (n)],
          exact [expr (simple_func.measurable _).coe_nnreal_ennreal] }
      end }
end

-- error in MeasureTheory.Integral.VitaliCaratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a measurable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_lt_lower_semicontinuous_lintegral_ge
[sigma_finite μ]
(f : α → «exprℝ≥0»())
(fmeas : measurable f)
{ε : «exprℝ≥0∞»()}
(ε0 : «expr ≠ »(ε, 0)) : «expr∃ , »((g : α → «exprℝ≥0∞»()), «expr ∧ »(∀
  x, «expr < »((f x : «exprℝ≥0∞»()), g x), «expr ∧ »(lower_semicontinuous g, «expr ≤ »(«expr∫⁻ , ∂ »((x), g x, μ), «expr + »(«expr∫⁻ , ∂ »((x), f x, μ), ε))))) :=
begin
  have [] [":", expr «expr ≠ »(«expr / »(ε, 2), 0)] [":=", expr (ennreal.half_pos ε0).ne'],
  rcases [expr exists_pos_lintegral_lt_of_sigma_finite μ this, "with", "⟨", ident w, ",", ident wpos, ",", ident wmeas, ",", ident wint, "⟩"],
  let [ident f'] [] [":=", expr λ x, ((«expr + »(f x, w x) : «exprℝ≥0»()) : «exprℝ≥0∞»())],
  rcases [expr exists_le_lower_semicontinuous_lintegral_ge μ f' (fmeas.add wmeas).coe_nnreal_ennreal this, "with", "⟨", ident g, ",", ident le_g, ",", ident gcont, ",", ident gint, "⟩"],
  refine [expr ⟨g, λ x, _, gcont, _⟩],
  { calc
      «expr < »((f x : «exprℝ≥0∞»()), f' x) : by simpa [] [] [] ["[", "<-", expr ennreal.coe_lt_coe, "]"] [] ["using", expr add_lt_add_left (wpos x) (f x)]
      «expr ≤ »(..., g x) : le_g x },
  { calc
      «expr ≤ »(«expr∫⁻ , ∂ »((x : α), g x, μ), «expr + »(«expr∫⁻ , ∂ »((x : α), «expr + »(f x, w x), μ), «expr / »(ε, 2))) : gint
      «expr = »(..., «expr + »(«expr + »(«expr∫⁻ , ∂ »((x : α), f x, μ), «expr∫⁻ , ∂ »((x : α), w x, μ)), «expr / »(ε, 2))) : by rw [expr lintegral_add fmeas.coe_nnreal_ennreal wmeas.coe_nnreal_ennreal] []
      «expr ≤ »(..., «expr + »(«expr + »(«expr∫⁻ , ∂ »((x : α), f x, μ), «expr / »(ε, 2)), «expr / »(ε, 2))) : add_le_add_right (add_le_add_left wint.le _) _
      «expr = »(..., «expr + »(«expr∫⁻ , ∂ »((x : α), f x, μ), ε)) : by rw ["[", expr add_assoc, ",", expr ennreal.add_halves, "]"] [] }
end

-- error in MeasureTheory.Integral.VitaliCaratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given an almost everywhere measurable function `f` with values in `ℝ≥0` in a sigma-finite space,
there exists a lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable
[sigma_finite μ]
(f : α → «exprℝ≥0»())
(fmeas : ae_measurable f μ)
{ε : «exprℝ≥0∞»()}
(ε0 : «expr ≠ »(ε, 0)) : «expr∃ , »((g : α → «exprℝ≥0∞»()), «expr ∧ »(∀
  x, «expr < »((f x : «exprℝ≥0∞»()), g x), «expr ∧ »(lower_semicontinuous g, «expr ≤ »(«expr∫⁻ , ∂ »((x), g x, μ), «expr + »(«expr∫⁻ , ∂ »((x), f x, μ), ε))))) :=
begin
  have [] [":", expr «expr ≠ »(«expr / »(ε, 2), 0)] [":=", expr (ennreal.half_pos ε0).ne'],
  rcases [expr exists_lt_lower_semicontinuous_lintegral_ge μ (fmeas.mk f) fmeas.measurable_mk this, "with", "⟨", ident g0, ",", ident f_lt_g0, ",", ident g0_cont, ",", ident g0_int, "⟩"],
  rcases [expr exists_measurable_superset_of_null fmeas.ae_eq_mk, "with", "⟨", ident s, ",", ident hs, ",", ident smeas, ",", ident μs, "⟩"],
  rcases [expr exists_le_lower_semicontinuous_lintegral_ge μ (s.indicator (λ
     x, «expr∞»())) (measurable_const.indicator smeas) this, "with", "⟨", ident g1, ",", ident le_g1, ",", ident g1_cont, ",", ident g1_int, "⟩"],
  refine [expr ⟨λ x, «expr + »(g0 x, g1 x), λ x, _, g0_cont.add g1_cont, _⟩],
  { by_cases [expr h, ":", expr «expr ∈ »(x, s)],
    { have [] [] [":=", expr le_g1 x],
      simp [] [] ["only"] ["[", expr h, ",", expr set.indicator_of_mem, ",", expr top_le_iff, "]"] [] ["at", ident this],
      simp [] [] [] ["[", expr this, "]"] [] [] },
    { have [] [":", expr «expr = »(f x, fmeas.mk f x)] [],
      by { rw [expr set.compl_subset_comm] ["at", ident hs],
        exact [expr hs h] },
      rw [expr this] [],
      exact [expr (f_lt_g0 x).trans_le le_self_add] } },
  { calc
      «expr = »(«expr∫⁻ , ∂ »((x), «expr + »(g0 x, g1 x), μ), «expr + »(«expr∫⁻ , ∂ »((x), g0 x, μ), «expr∫⁻ , ∂ »((x), g1 x, μ))) : lintegral_add g0_cont.measurable g1_cont.measurable
      «expr ≤ »(..., «expr + »(«expr + »(«expr∫⁻ , ∂ »((x), f x, μ), «expr / »(ε, 2)), «expr + »(0, «expr / »(ε, 2)))) : begin
        refine [expr add_le_add _ _],
        { convert [] [expr g0_int] ["using", 2],
          exact [expr lintegral_congr_ae (fmeas.ae_eq_mk.fun_comp _)] },
        { convert [] [expr g1_int] [],
          simp [] [] ["only"] ["[", expr smeas, ",", expr μs, ",", expr lintegral_const, ",", expr set.univ_inter, ",", expr measurable_set.univ, ",", expr lintegral_indicator, ",", expr mul_zero, ",", expr restrict_apply, "]"] [] [] }
      end
      «expr = »(..., «expr + »(«expr∫⁻ , ∂ »((x), f x, μ), ε)) : by simp [] [] ["only"] ["[", expr add_assoc, ",", expr ennreal.add_halves, ",", expr zero_add, "]"] [] [] }
end

variable{μ}

-- error in MeasureTheory.Integral.VitaliCaratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given an integrable function `f` with values in `ℝ≥0` in a sigma-finite space, there exists a
lower semicontinuous function `g > f` with integral arbitrarily close to that of `f`.
Formulation in terms of `integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_lt_lower_semicontinuous_integral_gt_nnreal
[sigma_finite μ]
(f : α → «exprℝ≥0»())
(fint : integrable (λ x, (f x : exprℝ())) μ)
{ε : exprℝ()}
(εpos : «expr < »(0, ε)) : «expr∃ , »((g : α → «exprℝ≥0∞»()), «expr ∧ »(∀
  x, «expr < »((f x : «exprℝ≥0∞»()), g x), «expr ∧ »(lower_semicontinuous g, «expr ∧ »(«expr∀ᵐ ∂ , »((x), μ, «expr < »(g x, «expr⊤»())), «expr ∧ »(integrable (λ
      x, (g x).to_real) μ, «expr < »(«expr∫ , ∂ »((x), (g x).to_real, μ), «expr + »(«expr∫ , ∂ »((x), f x, μ), ε))))))) :=
begin
  have [ident fmeas] [":", expr ae_measurable f μ] [],
  by { convert [] [expr fint.ae_measurable.real_to_nnreal] [],
    ext1 [] [ident x],
    simp [] [] ["only"] ["[", expr real.to_nnreal_coe, "]"] [] [] },
  lift [expr ε] ["to", expr «exprℝ≥0»()] ["using", expr εpos.le] [],
  obtain ["⟨", ident δ, ",", ident δpos, ",", ident hδε, "⟩", ":", expr «expr∃ , »((δ : «exprℝ≥0»()), «expr ∧ »(«expr < »(0, δ), «expr < »(δ, ε)))],
  from [expr exists_between εpos],
  have [ident int_f_ne_top] [":", expr «expr ≠ »(«expr∫⁻ , ∂ »((a : α), f a, μ), «expr∞»())] [":=", expr (has_finite_integral_iff_of_nnreal.1 fint.has_finite_integral).ne],
  rcases [expr exists_lt_lower_semicontinuous_lintegral_ge_of_ae_measurable μ f fmeas (ennreal.coe_ne_zero.2 δpos.ne'), "with", "⟨", ident g, ",", ident f_lt_g, ",", ident gcont, ",", ident gint, "⟩"],
  have [ident gint_ne] [":", expr «expr ≠ »(«expr∫⁻ , ∂ »((x : α), g x, μ), «expr∞»())] [":=", expr ne_top_of_le_ne_top (by simpa [] [] [] [] [] []) gint],
  have [ident g_lt_top] [":", expr «expr∀ᵐ ∂ , »((x : α), μ, «expr < »(g x, «expr∞»()))] [":=", expr ae_lt_top gcont.measurable gint_ne],
  have [ident Ig] [":", expr «expr = »(«expr∫⁻ , ∂ »((a : α), ennreal.of_real (g a).to_real, μ), «expr∫⁻ , ∂ »((a : α), g a, μ))] [],
  { apply [expr lintegral_congr_ae],
    filter_upwards ["[", expr g_lt_top, "]"] [],
    assume [binders (x hx)],
    simp [] [] ["only"] ["[", expr hx.ne, ",", expr ennreal.of_real_to_real, ",", expr ne.def, ",", expr not_false_iff, "]"] [] [] },
  refine [expr ⟨g, f_lt_g, gcont, g_lt_top, _, _⟩],
  { refine [expr ⟨gcont.measurable.ennreal_to_real.ae_measurable, _⟩],
    simp [] [] ["only"] ["[", expr has_finite_integral_iff_norm, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg ennreal.to_real_nonneg, "]"] [] [],
    convert [] [expr gint_ne.lt_top] ["using", 1] },
  { rw ["[", expr integral_eq_lintegral_of_nonneg_ae, ",", expr integral_eq_lintegral_of_nonneg_ae, "]"] [],
    { calc
        «expr = »(ennreal.to_real «expr∫⁻ , ∂ »((a : α), ennreal.of_real (g a).to_real, μ), ennreal.to_real «expr∫⁻ , ∂ »((a : α), g a, μ)) : by congr' [1] []
        «expr ≤ »(..., ennreal.to_real «expr + »(«expr∫⁻ , ∂ »((a : α), f a, μ), δ)) : begin
          apply [expr ennreal.to_real_mono _ gint],
          simpa [] [] [] [] [] ["using", expr int_f_ne_top]
        end
        «expr = »(..., «expr + »(ennreal.to_real «expr∫⁻ , ∂ »((a : α), f a, μ), δ)) : by rw ["[", expr ennreal.to_real_add int_f_ne_top ennreal.coe_ne_top, ",", expr ennreal.coe_to_real, "]"] []
        «expr < »(..., «expr + »(ennreal.to_real «expr∫⁻ , ∂ »((a : α), f a, μ), ε)) : add_lt_add_left hδε _
        «expr = »(..., «expr + »(«expr∫⁻ , ∂ »((a : α), ennreal.of_real «expr↑ »(f a), μ).to_real, ε)) : by simp [] [] [] [] [] [] },
    { apply [expr filter.eventually_of_forall (λ x, _)],
      simp [] [] [] [] [] [] },
    { exact [expr fmeas.coe_nnreal_real] },
    { apply [expr filter.eventually_of_forall (λ x, _)],
      simp [] [] [] [] [] [] },
    { apply [expr gcont.measurable.ennreal_to_real.ae_measurable] } }
end

/-! ### Upper semicontinuous lower bound for nonnegative functions -/


-- error in MeasureTheory.Integral.VitaliCaratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a simple function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem simple_func.exists_upper_semicontinuous_le_lintegral_le
(f : «expr →ₛ »(α, «exprℝ≥0»()))
(int_f : «expr ≠ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr∞»()))
{ε : «exprℝ≥0∞»()}
(ε0 : «expr ≠ »(ε, 0)) : «expr∃ , »((g : α → «exprℝ≥0»()), «expr ∧ »(∀
  x, «expr ≤ »(g x, f x), «expr ∧ »(upper_semicontinuous g, «expr ≤ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr + »(«expr∫⁻ , ∂ »((x), g x, μ), ε))))) :=
begin
  induction [expr f] ["using", ident measure_theory.simple_func.induction] ["with", ident c, ident s, ident hs, ident f₁, ident f₂, ident H, ident h₁, ident h₂] ["generalizing", ident ε],
  { let [ident f] [] [":=", expr simple_func.piecewise s hs (simple_func.const α c) (simple_func.const α 0)],
    by_cases [expr hc, ":", expr «expr = »(c, 0)],
    { refine [expr ⟨λ x, 0, _, upper_semicontinuous_const, _⟩],
      { simp [] [] ["only"] ["[", expr hc, ",", expr set.indicator_zero', ",", expr pi.zero_apply, ",", expr simple_func.const_zero, ",", expr implies_true_iff, ",", expr eq_self_iff_true, ",", expr simple_func.coe_zero, ",", expr set.piecewise_eq_indicator, ",", expr simple_func.coe_piecewise, ",", expr le_zero_iff, "]"] [] [] },
      { simp [] [] ["only"] ["[", expr hc, ",", expr set.indicator_zero', ",", expr lintegral_const, ",", expr zero_mul, ",", expr pi.zero_apply, ",", expr simple_func.const_zero, ",", expr zero_add, ",", expr zero_le', ",", expr simple_func.coe_zero, ",", expr set.piecewise_eq_indicator, ",", expr ennreal.coe_zero, ",", expr simple_func.coe_piecewise, ",", expr zero_le, "]"] [] [] } },
    have [ident μs_lt_top] [":", expr «expr < »(μ s, «expr∞»())] [],
    by simpa [] [] ["only"] ["[", expr hs, ",", expr hc, ",", expr lt_top_iff_ne_top, ",", expr true_and, ",", expr simple_func.coe_const, ",", expr or_false, ",", expr lintegral_const, ",", expr ennreal.coe_indicator, ",", expr set.univ_inter, ",", expr ennreal.coe_ne_top, ",", expr restrict_apply measurable_set.univ, ",", expr with_top.mul_eq_top_iff, ",", expr simple_func.const_zero, ",", expr function.const_apply, ",", expr lintegral_indicator, ",", expr ennreal.coe_eq_zero, ",", expr ne.def, ",", expr not_false_iff, ",", expr simple_func.coe_zero, ",", expr set.piecewise_eq_indicator, ",", expr simple_func.coe_piecewise, ",", expr false_and, "]"] [] ["using", expr int_f],
    have [] [":", expr «expr < »((0 : «exprℝ≥0∞»()), «expr / »(ε, c))] [":=", expr ennreal.div_pos_iff.2 ⟨ε0, ennreal.coe_ne_top⟩],
    obtain ["⟨", ident F, ",", ident Fs, ",", ident F_closed, ",", ident μF, "⟩", ":", expr «expr∃ , »((F «expr ⊆ » s), «expr ∧ »(is_closed F, «expr < »(μ s, «expr + »(μ F, «expr / »(ε, c))))), ":=", expr hs.exists_is_closed_lt_add μs_lt_top.ne this.ne'],
    refine [expr ⟨set.indicator F (λ x, c), λ x, _, F_closed.upper_semicontinuous_indicator (zero_le _), _⟩],
    { simp [] [] ["only"] ["[", expr simple_func.coe_const, ",", expr simple_func.const_zero, ",", expr simple_func.coe_zero, ",", expr set.piecewise_eq_indicator, ",", expr simple_func.coe_piecewise, "]"] [] [],
      exact [expr set.indicator_le_indicator_of_subset Fs (λ x, zero_le _) _] },
    { suffices [] [":", expr «expr ≤ »(«expr * »((c : «exprℝ≥0∞»()), μ s), «expr + »(«expr * »(c, μ F), ε))],
      by simpa [] [] ["only"] ["[", expr hs, ",", expr F_closed.measurable_set, ",", expr simple_func.coe_const, ",", expr function.const_apply, ",", expr lintegral_const, ",", expr ennreal.coe_indicator, ",", expr set.univ_inter, ",", expr measurable_set.univ, ",", expr simple_func.const_zero, ",", expr lintegral_indicator, ",", expr simple_func.coe_zero, ",", expr set.piecewise_eq_indicator, ",", expr simple_func.coe_piecewise, ",", expr restrict_apply, "]"] [] [],
      calc
        «expr ≤ »(«expr * »((c : «exprℝ≥0∞»()), μ s), «expr * »(c, «expr + »(μ F, «expr / »(ε, c)))) : ennreal.mul_le_mul (le_refl _) μF.le
        «expr = »(..., «expr + »(«expr * »(c, μ F), ε)) : begin
          simp_rw ["[", expr mul_add, "]"] [],
          rw [expr ennreal.mul_div_cancel' _ ennreal.coe_ne_top] [],
          simpa [] [] [] [] [] ["using", expr hc]
        end } },
  { have [ident A] [":", expr «expr ≠ »(«expr + »(«expr∫⁻ , ∂ »((x : α), f₁ x, μ), «expr∫⁻ , ∂ »((x : α), f₂ x, μ)), «expr⊤»())] [],
    by rwa ["<-", expr lintegral_add f₁.measurable.coe_nnreal_ennreal f₂.measurable.coe_nnreal_ennreal] [],
    rcases [expr h₁ (ennreal.add_ne_top.1 A).1 (ennreal.half_pos ε0).ne', "with", "⟨", ident g₁, ",", ident f₁_le_g₁, ",", ident g₁cont, ",", ident g₁int, "⟩"],
    rcases [expr h₂ (ennreal.add_ne_top.1 A).2 (ennreal.half_pos ε0).ne', "with", "⟨", ident g₂, ",", ident f₂_le_g₂, ",", ident g₂cont, ",", ident g₂int, "⟩"],
    refine [expr ⟨λ x, «expr + »(g₁ x, g₂ x), λ x, add_le_add (f₁_le_g₁ x) (f₂_le_g₂ x), g₁cont.add g₂cont, _⟩],
    simp [] [] ["only"] ["[", expr simple_func.coe_add, ",", expr ennreal.coe_add, ",", expr pi.add_apply, "]"] [] [],
    rw ["[", expr lintegral_add f₁.measurable.coe_nnreal_ennreal f₂.measurable.coe_nnreal_ennreal, ",", expr lintegral_add g₁cont.measurable.coe_nnreal_ennreal g₂cont.measurable.coe_nnreal_ennreal, "]"] [],
    convert [] [expr add_le_add g₁int g₂int] ["using", 1],
    conv_lhs [] [] { rw ["<-", expr ennreal.add_halves ε] },
    abel [] [] [] }
end

-- error in MeasureTheory.Integral.VitaliCaratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`lintegral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_upper_semicontinuous_le_lintegral_le
(f : α → «exprℝ≥0»())
(int_f : «expr ≠ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr∞»()))
{ε : «exprℝ≥0∞»()}
(ε0 : «expr ≠ »(ε, 0)) : «expr∃ , »((g : α → «exprℝ≥0»()), «expr ∧ »(∀
  x, «expr ≤ »(g x, f x), «expr ∧ »(upper_semicontinuous g, «expr ≤ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr + »(«expr∫⁻ , ∂ »((x), g x, μ), ε))))) :=
begin
  obtain ["⟨", ident fs, ",", ident fs_le_f, ",", ident int_fs, "⟩", ":", expr «expr∃ , »((fs : «expr →ₛ »(α, «exprℝ≥0»())), «expr ∧ »(∀
     x, «expr ≤ »(fs x, f x), «expr ≤ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr + »(«expr∫⁻ , ∂ »((x), fs x, μ), «expr / »(ε, 2))))), ":=", expr begin
     have [] [] [":=", expr ennreal.lt_add_right int_f (ennreal.half_pos ε0).ne'],
     conv_rhs ["at", ident this] [] { rw [expr lintegral_eq_nnreal (λ x, (f x : «exprℝ≥0∞»())) μ] },
     erw [expr ennreal.bsupr_add] ["at", ident this]; [skip, exact [expr ⟨0, λ x, by simp [] [] [] [] [] []⟩]],
     simp [] [] ["only"] ["[", expr lt_supr_iff, "]"] [] ["at", ident this],
     rcases [expr this, "with", "⟨", ident fs, ",", ident fs_le_f, ",", ident int_fs, "⟩"],
     refine [expr ⟨fs, λ
       x, by simpa [] [] ["only"] ["[", expr ennreal.coe_le_coe, "]"] [] ["using", expr fs_le_f x], _⟩],
     convert [] [expr int_fs.le] [],
     rw ["<-", expr simple_func.lintegral_eq_lintegral] [],
     refl
   end],
  have [ident int_fs_lt_top] [":", expr «expr ≠ »(«expr∫⁻ , ∂ »((x), fs x, μ), «expr∞»())] [],
  { apply [expr ne_top_of_le_ne_top int_f (lintegral_mono (λ x, _))],
    simpa [] [] ["only"] ["[", expr ennreal.coe_le_coe, "]"] [] ["using", expr fs_le_f x] },
  obtain ["⟨", ident g, ",", ident g_le_fs, ",", ident gcont, ",", ident gint, "⟩", ":", expr «expr∃ , »((g : α → «exprℝ≥0»()), «expr ∧ »(∀
     x, «expr ≤ »(g x, fs x), «expr ∧ »(upper_semicontinuous g, «expr ≤ »(«expr∫⁻ , ∂ »((x), fs x, μ), «expr + »(«expr∫⁻ , ∂ »((x), g x, μ), «expr / »(ε, 2)))))), ":=", expr fs.exists_upper_semicontinuous_le_lintegral_le int_fs_lt_top (ennreal.half_pos ε0).ne'],
  refine [expr ⟨g, λ x, (g_le_fs x).trans (fs_le_f x), gcont, _⟩],
  calc
    «expr ≤ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr + »(«expr∫⁻ , ∂ »((x), fs x, μ), «expr / »(ε, 2))) : int_fs
    «expr ≤ »(..., «expr + »(«expr + »(«expr∫⁻ , ∂ »((x), g x, μ), «expr / »(ε, 2)), «expr / »(ε, 2))) : add_le_add gint (le_refl _)
    «expr = »(..., «expr + »(«expr∫⁻ , ∂ »((x), g x, μ), ε)) : by rw ["[", expr add_assoc, ",", expr ennreal.add_halves, "]"] []
end

-- error in MeasureTheory.Integral.VitaliCaratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given an integrable function `f` with values in `ℝ≥0`, there exists an upper semicontinuous
function `g ≤ f` with integral arbitrarily close to that of `f`. Formulation in terms of
`integral`.
Auxiliary lemma for Vitali-Carathéodory theorem `exists_lt_lower_semicontinuous_integral_lt`. -/
theorem exists_upper_semicontinuous_le_integral_le
(f : α → «exprℝ≥0»())
(fint : integrable (λ x, (f x : exprℝ())) μ)
{ε : exprℝ()}
(εpos : «expr < »(0, ε)) : «expr∃ , »((g : α → «exprℝ≥0»()), «expr ∧ »(∀
  x, «expr ≤ »(g x, f x), «expr ∧ »(upper_semicontinuous g, «expr ∧ »(integrable (λ
     x, (g x : exprℝ())) μ, «expr ≤ »(«expr - »(«expr∫ , ∂ »((x), (f x : exprℝ()), μ), ε), «expr∫ , ∂ »((x), g x, μ)))))) :=
begin
  lift [expr ε] ["to", expr «exprℝ≥0»()] ["using", expr εpos.le] [],
  rw ["[", expr nnreal.coe_pos, ",", "<-", expr ennreal.coe_pos, "]"] ["at", ident εpos],
  have [ident If] [":", expr «expr < »(«expr∫⁻ , ∂ »((x), f x, μ), «expr∞»())] [":=", expr has_finite_integral_iff_of_nnreal.1 fint.has_finite_integral],
  rcases [expr exists_upper_semicontinuous_le_lintegral_le f If.ne εpos.ne', "with", "⟨", ident g, ",", ident gf, ",", ident gcont, ",", ident gint, "⟩"],
  have [ident Ig] [":", expr «expr < »(«expr∫⁻ , ∂ »((x), g x, μ), «expr∞»())] [],
  { apply [expr lt_of_le_of_lt (lintegral_mono (λ x, _)) If],
    simpa [] [] [] [] [] ["using", expr gf x] },
  refine [expr ⟨g, gf, gcont, _, _⟩],
  { refine [expr integrable.mono fint gcont.measurable.coe_nnreal_real.ae_measurable _],
    exact [expr filter.eventually_of_forall (λ x, by simp [] [] [] ["[", expr gf x, "]"] [] [])] },
  { rw ["[", expr integral_eq_lintegral_of_nonneg_ae, ",", expr integral_eq_lintegral_of_nonneg_ae, "]"] [],
    { rw [expr sub_le_iff_le_add] [],
      convert [] [expr ennreal.to_real_mono _ gint] [],
      { simp [] [] [] [] [] [] },
      { rw [expr ennreal.to_real_add Ig.ne ennreal.coe_ne_top] [],
        simp [] [] [] [] [] [] },
      { simpa [] [] [] [] [] ["using", expr Ig.ne] } },
    { apply [expr filter.eventually_of_forall],
      simp [] [] [] [] [] [] },
    { exact [expr gcont.measurable.coe_nnreal_real.ae_measurable] },
    { apply [expr filter.eventually_of_forall],
      simp [] [] [] [] [] [] },
    { exact [expr fint.ae_measurable] } }
end

/-! ### Vitali-Carathéodory theorem -/


-- error in MeasureTheory.Integral.VitaliCaratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Vitali-Carathéodory Theorem**: given an integrable real function `f`, there exists an
integrable function `g > f` which is lower semicontinuous, with integral arbitrarily close
to that of `f`. This function has to be `ereal`-valued in general. -/
theorem exists_lt_lower_semicontinuous_integral_lt
[sigma_finite μ]
(f : α → exprℝ())
(hf : integrable f μ)
{ε : exprℝ()}
(εpos : «expr < »(0, ε)) : «expr∃ , »((g : α → ereal), «expr ∧ »(∀
  x, «expr < »((f x : ereal), g x), «expr ∧ »(lower_semicontinuous g, «expr ∧ »(integrable (λ
     x, ereal.to_real (g x)) μ, «expr ∧ »(«expr∀ᵐ ∂ , »((x), μ, «expr < »(g x, «expr⊤»())), «expr < »(«expr∫ , ∂ »((x), ereal.to_real (g x), μ), «expr + »(«expr∫ , ∂ »((x), f x, μ), ε))))))) :=
begin
  let [ident δ] [":", expr «exprℝ≥0»()] [":=", expr ⟨«expr / »(ε, 2), (half_pos εpos).le⟩],
  have [ident δpos] [":", expr «expr < »(0, δ)] [":=", expr half_pos εpos],
  let [ident fp] [":", expr α → «exprℝ≥0»()] [":=", expr λ x, real.to_nnreal (f x)],
  have [ident int_fp] [":", expr integrable (λ x, (fp x : exprℝ())) μ] [":=", expr hf.real_to_nnreal],
  rcases [expr exists_lt_lower_semicontinuous_integral_gt_nnreal fp int_fp δpos, "with", "⟨", ident gp, ",", ident fp_lt_gp, ",", ident gpcont, ",", ident gp_lt_top, ",", ident gp_integrable, ",", ident gpint, "⟩"],
  let [ident fm] [":", expr α → «exprℝ≥0»()] [":=", expr λ x, real.to_nnreal «expr- »(f x)],
  have [ident int_fm] [":", expr integrable (λ x, (fm x : exprℝ())) μ] [":=", expr hf.neg.real_to_nnreal],
  rcases [expr exists_upper_semicontinuous_le_integral_le fm int_fm δpos, "with", "⟨", ident gm, ",", ident gm_le_fm, ",", ident gmcont, ",", ident gm_integrable, ",", ident gmint, "⟩"],
  let [ident g] [":", expr α → ereal] [":=", expr λ x, «expr - »((gp x : ereal), gm x)],
  have [ident ae_g] [":", expr «expr∀ᵐ ∂ , »((x), μ, «expr = »((g x).to_real, «expr - »((gp x : ereal).to_real, (gm x : ereal).to_real)))] [],
  { filter_upwards ["[", expr gp_lt_top, "]"] [],
    assume [binders (x hx)],
    rw [expr ereal.to_real_sub] []; simp [] [] [] ["[", expr hx.ne, "]"] [] [] },
  refine [expr ⟨g, _, _, _, _, _⟩],
  show [expr integrable (λ x, ereal.to_real (g x)) μ],
  { rw [expr integrable_congr ae_g] [],
    convert [] [expr gp_integrable.sub gm_integrable] [],
    ext [] [ident x] [],
    simp [] [] [] [] [] [] },
  show [expr «expr < »(«expr∫ , ∂ »((x : α), (g x).to_real, μ), «expr + »(«expr∫ , ∂ »((x : α), f x, μ), ε))],
  from [expr calc
     «expr = »(«expr∫ , ∂ »((x : α), (g x).to_real, μ), «expr∫ , ∂ »((x : α), «expr - »(ereal.to_real (gp x), ereal.to_real (gm x)), μ)) : integral_congr_ae ae_g
     «expr = »(..., «expr - »(«expr∫ , ∂ »((x : α), ereal.to_real (gp x), μ), «expr∫ , ∂ »((x : α), gm x, μ))) : begin
       simp [] [] ["only"] ["[", expr ereal.to_real_coe_ennreal, ",", expr ennreal.coe_to_real, ",", expr coe_coe, "]"] [] [],
       exact [expr integral_sub gp_integrable gm_integrable]
     end
     «expr < »(..., «expr - »(«expr + »(«expr∫ , ∂ »((x : α), «expr↑ »(fp x), μ), «expr↑ »(δ)), «expr∫ , ∂ »((x : α), gm x, μ))) : begin
       apply [expr sub_lt_sub_right],
       convert [] [expr gpint] [],
       simp [] [] ["only"] ["[", expr ereal.to_real_coe_ennreal, "]"] [] []
     end
     «expr ≤ »(..., «expr - »(«expr + »(«expr∫ , ∂ »((x : α), «expr↑ »(fp x), μ), «expr↑ »(δ)), «expr - »(«expr∫ , ∂ »((x : α), fm x, μ), δ))) : sub_le_sub_left gmint _
     «expr = »(..., «expr + »(«expr∫ , ∂ »((x : α), f x, μ), «expr * »(2, δ))) : by { simp_rw ["[", expr integral_eq_integral_pos_part_sub_integral_neg_part hf, ",", expr fp, ",", expr fm, "]"] [],
       ring [] }
     «expr = »(..., «expr + »(«expr∫ , ∂ »((x : α), f x, μ), ε)) : by { congr' [1] [],
       field_simp [] ["[", expr δ, ",", expr mul_comm, "]"] [] [] }],
  show [expr «expr∀ᵐ ∂ , »((x : α), μ, «expr < »(g x, «expr⊤»()))],
  { filter_upwards ["[", expr gp_lt_top, "]"] [],
    assume [binders (x hx)],
    simp [] [] [] ["[", expr g, ",", expr ereal.sub_eq_add_neg, ",", expr lt_top_iff_ne_top, ",", expr lt_top_iff_ne_top.1 hx, "]"] [] [] },
  show [expr ∀ x, «expr < »((f x : ereal), g x)],
  { assume [binders (x)],
    rw [expr ereal.coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal (f x)] [],
    refine [expr ereal.sub_lt_sub_of_lt_of_le _ _ _ _],
    { simp [] [] ["only"] ["[", expr ereal.coe_ennreal_lt_coe_ennreal_iff, ",", expr coe_coe, "]"] [] [],
      exact [expr fp_lt_gp x] },
    { simp [] [] ["only"] ["[", expr ennreal.coe_le_coe, ",", expr ereal.coe_ennreal_le_coe_ennreal_iff, ",", expr coe_coe, "]"] [] [],
      exact [expr gm_le_fm x] },
    { simp [] [] ["only"] ["[", expr ereal.coe_ennreal_ne_bot, ",", expr ne.def, ",", expr not_false_iff, ",", expr coe_coe, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr ereal.coe_nnreal_ne_top, ",", expr ne.def, ",", expr not_false_iff, ",", expr coe_coe, "]"] [] [] } },
  show [expr lower_semicontinuous g],
  { apply [expr lower_semicontinuous.add'],
    { exact [expr continuous_coe_ennreal_ereal.comp_lower_semicontinuous gpcont (λ
        x y hxy, ereal.coe_ennreal_le_coe_ennreal_iff.2 hxy)] },
    { apply [expr ereal.continuous_neg.comp_upper_semicontinuous_antitone _ (λ x y hxy, ereal.neg_le_neg_iff.2 hxy)],
      dsimp [] [] [] [],
      apply [expr continuous_coe_ennreal_ereal.comp_upper_semicontinuous _ (λ
        x y hxy, ereal.coe_ennreal_le_coe_ennreal_iff.2 hxy)],
      exact [expr ennreal.continuous_coe.comp_upper_semicontinuous gmcont (λ x y hxy, ennreal.coe_le_coe.2 hxy)] },
    { assume [binders (x)],
      exact [expr ereal.continuous_at_add (by simp [] [] [] [] [] []) (by simp [] [] [] [] [] [])] } }
end

/-- **Vitali-Carathéodory Theorem**: given an integrable real function `f`, there exists an
integrable function `g < f` which is upper semicontinuous, with integral arbitrarily close to that
of `f`. This function has to be `ereal`-valued in general. -/
theorem exists_upper_semicontinuous_lt_integral_gt [sigma_finite μ] (f : α → ℝ) (hf : integrable f μ) {ε : ℝ}
  (εpos : 0 < ε) :
  ∃ g : α → Ereal,
    (∀ x, (g x : Ereal) < f x) ∧
      UpperSemicontinuous g ∧
        integrable (fun x => Ereal.toReal (g x)) μ ∧ (∀ᵐx ∂μ, ⊥ < g x) ∧ (∫x, f x ∂μ) < (∫x, Ereal.toReal (g x) ∂μ)+ε :=
  by 
    rcases exists_lt_lower_semicontinuous_integral_lt (fun x => -f x) hf.neg εpos with
      ⟨g, g_lt_f, gcont, g_integrable, g_lt_top, gint⟩
    refine' ⟨fun x => -g x, _, _, _, _, _⟩
    ·
      exact
        fun x =>
          Ereal.neg_lt_iff_neg_lt.1
            (by 
              simpa only [Ereal.coe_neg] using g_lt_f x)
    ·
      exact ereal.continuous_neg.comp_lower_semicontinuous_antitone gcont fun x y hxy => Ereal.neg_le_neg_iff.2 hxy
    ·
      convert g_integrable.neg 
      ext x 
      simp 
    ·
      simpa [bot_lt_iff_ne_bot, lt_top_iff_ne_top] using g_lt_top
    ·
      simpRw [integral_neg, lt_neg_add_iff_add_lt]  at gint 
      rw [add_commₓ] at gint 
      simpa [integral_neg] using gint

end MeasureTheory

