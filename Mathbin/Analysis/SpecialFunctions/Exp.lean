import Mathbin.Analysis.Complex.Basic 
import Mathbin.Data.Complex.Exponential

/-!
# Complex and real exponential

In this file we prove continuity of `complex.exp` and `real.exp`. We also prove a few facts about
limits of `real.exp` at infinity.

## Tags

exp
-/


noncomputable theory

open Finset Filter Metric Asymptotics Set Function

open_locale Classical TopologicalSpace

namespace Complex

variable{z y x : ℝ}

theorem exp_bound_sq (x z : ℂ) (hz : ∥z∥ ≤ 1) : ∥exp (x+z) - exp x - z • exp x∥ ≤ ∥exp x∥*∥z∥^2 :=
  calc ∥exp (x+z) - exp x - z*exp x∥ = ∥exp x*exp z - 1 - z∥ :=
    by 
      congr 
      rw [exp_add]
      ring 
    _ = ∥exp x∥*∥exp z - 1 - z∥ := NormedField.norm_mul _ _ 
    _ ≤ ∥exp x∥*∥z∥^2 := mul_le_mul_of_nonneg_left (abs_exp_sub_one_sub_id_le hz) (norm_nonneg _)
    

-- error in Analysis.SpecialFunctions.Exp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem locally_lipschitz_exp
{r : exprℝ()}
(hr_nonneg : «expr ≤ »(0, r))
(hr_le : «expr ≤ »(r, 1))
(x y : exprℂ())
(hyx : «expr < »(«expr∥ ∥»(«expr - »(y, x)), r)) : «expr ≤ »(«expr∥ ∥»(«expr - »(exp y, exp x)), «expr * »(«expr * »(«expr + »(1, r), «expr∥ ∥»(exp x)), «expr∥ ∥»(«expr - »(y, x)))) :=
begin
  have [ident hy_eq] [":", expr «expr = »(y, «expr + »(x, «expr - »(y, x)))] [],
  by abel [] [] [],
  have [ident hyx_sq_le] [":", expr «expr ≤ »(«expr ^ »(«expr∥ ∥»(«expr - »(y, x)), 2), «expr * »(r, «expr∥ ∥»(«expr - »(y, x))))] [],
  { rw [expr pow_two] [],
    exact [expr mul_le_mul hyx.le le_rfl (norm_nonneg _) hr_nonneg] },
  have [ident h_sq] [":", expr ∀
   z, «expr ≤ »(«expr∥ ∥»(z), 1) → «expr ≤ »(«expr∥ ∥»(«expr - »(exp «expr + »(x, z), exp x)), «expr + »(«expr * »(«expr∥ ∥»(z), «expr∥ ∥»(exp x)), «expr * »(«expr∥ ∥»(exp x), «expr ^ »(«expr∥ ∥»(z), 2))))] [],
  { intros [ident z, ident hz],
    have [] [":", expr «expr ≤ »(«expr∥ ∥»(«expr - »(«expr - »(exp «expr + »(x, z), exp x), «expr • »(z, exp x))), «expr * »(«expr∥ ∥»(exp x), «expr ^ »(«expr∥ ∥»(z), 2)))] [],
    from [expr exp_bound_sq x z hz],
    rw ["[", "<-", expr sub_le_iff_le_add', ",", "<-", expr norm_smul z, "]"] [],
    exact [expr (norm_sub_norm_le _ _).trans this] },
  calc
    «expr = »(«expr∥ ∥»(«expr - »(exp y, exp x)), «expr∥ ∥»(«expr - »(exp «expr + »(x, «expr - »(y, x)), exp x))) : by nth_rewrite [0] [expr hy_eq] []
    «expr ≤ »(..., «expr + »(«expr * »(«expr∥ ∥»(«expr - »(y, x)), «expr∥ ∥»(exp x)), «expr * »(«expr∥ ∥»(exp x), «expr ^ »(«expr∥ ∥»(«expr - »(y, x)), 2)))) : h_sq «expr - »(y, x) (hyx.le.trans hr_le)
    «expr ≤ »(..., «expr + »(«expr * »(«expr∥ ∥»(«expr - »(y, x)), «expr∥ ∥»(exp x)), «expr * »(«expr∥ ∥»(exp x), «expr * »(r, «expr∥ ∥»(«expr - »(y, x)))))) : add_le_add_left (mul_le_mul le_rfl hyx_sq_le (sq_nonneg _) (norm_nonneg _)) _
    «expr = »(..., «expr * »(«expr * »(«expr + »(1, r), «expr∥ ∥»(exp x)), «expr∥ ∥»(«expr - »(y, x)))) : by ring []
end

@[continuity]
theorem continuous_exp : Continuous exp :=
  continuous_iff_continuous_at.mpr$
    fun x => continuous_at_of_locally_lipschitz zero_lt_one (2*∥exp x∥) (locally_lipschitz_exp zero_le_one le_rfl x)

theorem continuous_on_exp {s : Set ℂ} : ContinuousOn exp s :=
  continuous_exp.ContinuousOn

end Complex

section ComplexContinuousExpComp

variable{α : Type _}

open Complex

theorem Filter.Tendsto.cexp {l : Filter α} {f : α → ℂ} {z : ℂ} (hf : tendsto f l (𝓝 z)) :
  tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.Tendsto _).comp hf

variable[TopologicalSpace α]{f : α → ℂ}{s : Set α}{x : α}

theorem ContinuousWithinAt.cexp (h : ContinuousWithinAt f s x) : ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.cexp

theorem ContinuousAt.cexp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.cexp

theorem ContinuousOn.cexp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y)) s :=
  fun x hx => (h x hx).cexp

theorem Continuous.cexp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuous_at.2$ fun x => h.continuous_at.cexp

end ComplexContinuousExpComp

namespace Real

@[continuity]
theorem continuous_exp : Continuous exp :=
  Complex.continuous_re.comp Complex.continuous_of_real.cexp

theorem continuous_on_exp {s : Set ℝ} : ContinuousOn exp s :=
  continuous_exp.ContinuousOn

end Real

section RealContinuousExpComp

variable{α : Type _}

open Real

theorem Filter.Tendsto.exp {l : Filter α} {f : α → ℝ} {z : ℝ} (hf : tendsto f l (𝓝 z)) :
  tendsto (fun x => exp (f x)) l (𝓝 (exp z)) :=
  (continuous_exp.Tendsto _).comp hf

variable[TopologicalSpace α]{f : α → ℝ}{s : Set α}{x : α}

theorem ContinuousWithinAt.exp (h : ContinuousWithinAt f s x) : ContinuousWithinAt (fun y => exp (f y)) s x :=
  h.exp

theorem ContinuousAt.exp (h : ContinuousAt f x) : ContinuousAt (fun y => exp (f y)) x :=
  h.exp

theorem ContinuousOn.exp (h : ContinuousOn f s) : ContinuousOn (fun y => exp (f y)) s :=
  fun x hx => (h x hx).exp

theorem Continuous.exp (h : Continuous f) : Continuous fun y => exp (f y) :=
  continuous_iff_continuous_at.2$ fun x => h.continuous_at.exp

end RealContinuousExpComp

namespace Real

variable{x y z : ℝ}

-- error in Analysis.SpecialFunctions.Exp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The real exponential function tends to `+∞` at `+∞`. -/ theorem tendsto_exp_at_top : tendsto exp at_top at_top :=
begin
  have [ident A] [":", expr tendsto (λ
    x : exprℝ(), «expr + »(x, 1)) at_top at_top] [":=", expr tendsto_at_top_add_const_right at_top 1 tendsto_id],
  have [ident B] [":", expr «expr∀ᶠ in , »((x), at_top, «expr ≤ »(«expr + »(x, 1), exp x))] [":=", expr eventually_at_top.2 ⟨0, λ
    x hx, add_one_le_exp_of_nonneg hx⟩],
  exact [expr tendsto_at_top_mono' at_top B A]
end

/-- The real exponential function tends to `0` at `-∞` or, equivalently, `exp(-x)` tends to `0`
at `+∞` -/
theorem tendsto_exp_neg_at_top_nhds_0 : tendsto (fun x => exp (-x)) at_top (𝓝 0) :=
  (tendsto_inv_at_top_zero.comp tendsto_exp_at_top).congr fun x => (exp_neg x).symm

/-- The real exponential function tends to `1` at `0`. -/
theorem tendsto_exp_nhds_0_nhds_1 : tendsto exp (𝓝 0) (𝓝 1) :=
  by 
    convert continuous_exp.tendsto 0
    simp 

theorem tendsto_exp_at_bot : tendsto exp at_bot (𝓝 0) :=
  (tendsto_exp_neg_at_top_nhds_0.comp tendsto_neg_at_bot_at_top).congr$ fun x => congr_argₓ exp$ neg_negₓ x

theorem tendsto_exp_at_bot_nhds_within : tendsto exp at_bot (𝓝[Ioi 0] 0) :=
  tendsto_inf.2 ⟨tendsto_exp_at_bot, tendsto_principal.2$ eventually_of_forall exp_pos⟩

-- error in Analysis.SpecialFunctions.Exp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The function `exp(x)/x^n` tends to `+∞` at `+∞`, for any natural number `n` -/
theorem tendsto_exp_div_pow_at_top (n : exprℕ()) : tendsto (λ x, «expr / »(exp x, «expr ^ »(x, n))) at_top at_top :=
begin
  refine [expr (at_top_basis_Ioi.tendsto_iff (at_top_basis' 1)).2 (λ C hC₁, _)],
  have [ident hC₀] [":", expr «expr < »(0, C)] [],
  from [expr zero_lt_one.trans_le hC₁],
  have [] [":", expr «expr < »(0, «expr ⁻¹»(«expr * »(exp 1, C)))] [":=", expr inv_pos.2 (mul_pos (exp_pos _) hC₀)],
  obtain ["⟨", ident N, ",", ident hN, "⟩", ":", expr «expr∃ , »((N), ∀
    k «expr ≥ » N, «expr < »(«expr / »((«expr ^ »(«expr↑ »(k), n) : exprℝ()), «expr ^ »(exp 1, k)), «expr ⁻¹»(«expr * »(exp 1, C)))), ":=", expr eventually_at_top.1 ((tendsto_pow_const_div_const_pow_of_one_lt n (one_lt_exp_iff.2 zero_lt_one)).eventually (gt_mem_nhds this))],
  simp [] [] ["only"] ["[", "<-", expr exp_nat_mul, ",", expr mul_one, ",", expr div_lt_iff, ",", expr exp_pos, ",", "<-", expr div_eq_inv_mul, "]"] [] ["at", ident hN],
  refine [expr ⟨N, trivial, λ x hx, _⟩],
  rw [expr set.mem_Ioi] ["at", ident hx],
  have [ident hx₀] [":", expr «expr < »(0, x)] [],
  from [expr N.cast_nonneg.trans_lt hx],
  rw ["[", expr set.mem_Ici, ",", expr le_div_iff (pow_pos hx₀ _), ",", "<-", expr le_div_iff' hC₀, "]"] [],
  calc
    «expr ≤ »(«expr ^ »(x, n), «expr ^ »(«expr⌈ ⌉₊»(x), n)) : pow_le_pow_of_le_left hx₀.le (nat.le_ceil _) _
    «expr ≤ »(..., «expr / »(exp «expr⌈ ⌉₊»(x), «expr * »(exp 1, C))) : (hN _ (nat.lt_ceil.2 hx).le).le
    «expr ≤ »(..., «expr / »(exp «expr + »(x, 1), «expr * »(exp 1, C))) : div_le_div_of_le (mul_pos (exp_pos _) hC₀).le «expr $ »(exp_le_exp.2, (nat.ceil_lt_add_one hx₀.le).le)
    «expr = »(..., «expr / »(exp x, C)) : by rw ["[", expr add_comm, ",", expr exp_add, ",", expr mul_div_mul_left _ _ (exp_pos _).ne', "]"] []
end

/-- The function `x^n * exp(-x)` tends to `0` at `+∞`, for any natural number `n`. -/
theorem tendsto_pow_mul_exp_neg_at_top_nhds_0 (n : ℕ) : tendsto (fun x => (x^n)*exp (-x)) at_top (𝓝 0) :=
  (tendsto_inv_at_top_zero.comp (tendsto_exp_div_pow_at_top n)).congr$
    fun x =>
      by 
        rw [comp_app, inv_eq_one_div, div_div_eq_mul_div, one_mulₓ, div_eq_mul_inv, exp_neg]

/-- The function `(b * exp x + c) / (x ^ n)` tends to `+∞` at `+∞`, for any positive natural number
`n` and any real numbers `b` and `c` such that `b` is positive. -/
theorem tendsto_mul_exp_add_div_pow_at_top (b c : ℝ) (n : ℕ) (hb : 0 < b) (hn : 1 ≤ n) :
  tendsto (fun x => ((b*exp x)+c) / (x^n)) at_top at_top :=
  by 
    refine'
      tendsto.congr' (eventually_eq_of_mem (Ioi_mem_at_top 0) _)
        (((tendsto_exp_div_pow_at_top n).const_mul_at_top hb).at_top_add
          ((tendsto_pow_neg_at_top hn).mul (@tendsto_const_nhds _ _ _ c _)))
    intro x hx 
    simp only [zpow_neg₀ x n]
    ring

-- error in Analysis.SpecialFunctions.Exp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The function `(x ^ n) / (b * exp x + c)` tends to `0` at `+∞`, for any positive natural number
`n` and any real numbers `b` and `c` such that `b` is nonzero. -/
theorem tendsto_div_pow_mul_exp_add_at_top
(b c : exprℝ())
(n : exprℕ())
(hb : «expr ≠ »(0, b))
(hn : «expr ≤ »(1, n)) : tendsto (λ
 x, «expr / »(«expr ^ »(x, n), «expr + »(«expr * »(b, exp x), c))) at_top (expr𝓝() 0) :=
begin
  have [ident H] [":", expr ∀
   d
   e, «expr < »(0, d) → tendsto (λ
    x : exprℝ(), «expr / »(«expr ^ »(x, n), «expr + »(«expr * »(d, exp x), e))) at_top (expr𝓝() 0)] [],
  { intros [ident b', ident c', ident h],
    convert [] [expr (tendsto_mul_exp_add_div_pow_at_top b' c' n h hn).inv_tendsto_at_top] [],
    ext [] [ident x] [],
    simpa [] [] ["only"] ["[", expr pi.inv_apply, "]"] [] ["using", expr inv_div.symm] },
  cases [expr lt_or_gt_of_ne hb] [],
  { exact [expr H b c h] },
  { convert [] [expr (H «expr- »(b) «expr- »(c) (neg_pos.mpr h)).neg] [],
    { ext [] [ident x] [],
      field_simp [] [] [] [],
      rw ["[", "<-", expr neg_add «expr * »(b, exp x) c, ",", expr neg_div_neg_eq, "]"] [] },
    { exact [expr neg_zero.symm] } }
end

/-- `real.exp` as an order isomorphism between `ℝ` and `(0, +∞)`. -/
def exp_order_iso : ℝ ≃o Ioi (0 : ℝ) :=
  StrictMono.orderIsoOfSurjective _ (exp_strict_mono.codRestrict exp_pos)$
    (continuous_subtype_mk _ continuous_exp).Surjective
      (by 
        simp only [tendsto_Ioi_at_top, Subtype.coe_mk, tendsto_exp_at_top])
      (by 
        simp [tendsto_exp_at_bot_nhds_within])

@[simp]
theorem coe_exp_order_iso_apply (x : ℝ) : (exp_order_iso x : ℝ) = exp x :=
  rfl

@[simp]
theorem coe_comp_exp_order_iso : (coeₓ ∘ exp_order_iso) = exp :=
  rfl

@[simp]
theorem range_exp : range exp = Ioi 0 :=
  by 
    rw [←coe_comp_exp_order_iso, range_comp, exp_order_iso.range_eq, image_univ, Subtype.range_coe]

@[simp]
theorem map_exp_at_top : map exp at_top = at_top :=
  by 
    rw [←coe_comp_exp_order_iso, ←Filter.map_map, OrderIso.map_at_top, map_coe_Ioi_at_top]

@[simp]
theorem comap_exp_at_top : comap exp at_top = at_top :=
  by 
    rw [←map_exp_at_top, comap_map exp_injective, map_exp_at_top]

@[simp]
theorem tendsto_exp_comp_at_top {α : Type _} {l : Filter α} {f : α → ℝ} :
  tendsto (fun x => exp (f x)) l at_top ↔ tendsto f l at_top :=
  by 
    rw [←tendsto_comap_iff, comap_exp_at_top]

theorem tendsto_comp_exp_at_top {α : Type _} {l : Filter α} {f : ℝ → α} :
  tendsto (fun x => f (exp x)) at_top l ↔ tendsto f at_top l :=
  by 
    rw [←tendsto_map'_iff, map_exp_at_top]

@[simp]
theorem map_exp_at_bot : map exp at_bot = 𝓝[Ioi 0] 0 :=
  by 
    rw [←coe_comp_exp_order_iso, ←Filter.map_map, exp_order_iso.map_at_bot, ←map_coe_Ioi_at_bot]

theorem comap_exp_nhds_within_Ioi_zero : comap exp (𝓝[Ioi 0] 0) = at_bot :=
  by 
    rw [←map_exp_at_bot, comap_map exp_injective]

theorem tendsto_comp_exp_at_bot {α : Type _} {l : Filter α} {f : ℝ → α} :
  tendsto (fun x => f (exp x)) at_bot l ↔ tendsto f (𝓝[Ioi 0] 0) l :=
  by 
    rw [←map_exp_at_bot, tendsto_map'_iff]

end Real

