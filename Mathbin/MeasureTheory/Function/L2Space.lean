import Mathbin.Analysis.InnerProductSpace.Basic 
import Mathbin.MeasureTheory.Integral.SetIntegral

/-! # `L^2` space

If `E` is an inner product space over `𝕜` (`ℝ` or `ℂ`), then `Lp E 2 μ` (defined in `lp_space.lean`)
is also an inner product space, with inner product defined as `inner f g = ∫ a, ⟪f a, g a⟫ ∂μ`.

### Main results

* `mem_L1_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `λ x, ⟪f x, g x⟫`
  belongs to `Lp 𝕜 1 μ`.
* `integrable_inner` : for `f` and `g` in `Lp E 2 μ`, the pointwise inner product `λ x, ⟪f x, g x⟫`
  is integrable.
* `L2.inner_product_space` : `Lp E 2 μ` is an inner product space.

-/


noncomputable theory

open TopologicalSpace MeasureTheory MeasureTheory.lp

open_locale Nnreal Ennreal MeasureTheory

namespace MeasureTheory

namespace L2

variable{α E F 𝕜 :
    Type
      _}[IsROrC
      𝕜][MeasurableSpace
      α]{μ :
    Measureₓ
      α}[MeasurableSpace
      E][InnerProductSpace 𝕜
      E][BorelSpace
      E][second_countable_topology E][NormedGroup F][MeasurableSpace F][BorelSpace F][second_countable_topology F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

-- error in MeasureTheory.Function.L2Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem snorm_rpow_two_norm_lt_top
(f : Lp F 2 μ) : «expr < »(snorm (λ x, «expr ^ »(«expr∥ ∥»(f x), (2 : exprℝ()))) 1 μ, «expr∞»()) :=
begin
  have [ident h_two] [":", expr «expr = »(ennreal.of_real (2 : exprℝ()), 2)] [],
  by simp [] [] [] ["[", expr zero_le_one, "]"] [] [],
  rw ["[", expr snorm_norm_rpow f zero_lt_two, ",", expr one_mul, ",", expr h_two, "]"] [],
  exact [expr ennreal.rpow_lt_top_of_nonneg zero_le_two (Lp.snorm_ne_top f)]
end

-- error in MeasureTheory.Function.L2Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem snorm_inner_lt_top
(f g : «expr →₂[ ] »(α, μ, E)) : «expr < »(snorm (λ x : α, «expr⟪ , ⟫»(f x, g x)) 1 μ, «expr∞»()) :=
begin
  have [ident h] [":", expr ∀
   x, «expr ≤ »(is_R_or_C.abs «expr⟪ , ⟫»(f x, g x), «expr * »(«expr∥ ∥»(f x), «expr∥ ∥»(g x)))] [],
  from [expr λ x, abs_inner_le_norm _ _],
  have [ident h'] [":", expr ∀
   x, «expr ≤ »(is_R_or_C.abs «expr⟪ , ⟫»(f x, g x), is_R_or_C.abs «expr + »(«expr ^ »(«expr∥ ∥»(f x), 2), «expr ^ »(«expr∥ ∥»(g x), 2)))] [],
  { refine [expr λ x, le_trans (h x) _],
    rw ["[", expr is_R_or_C.abs_to_real, ",", expr abs_eq_self.mpr, "]"] [],
    swap,
    { exact [expr add_nonneg (by simp [] [] [] [] [] []) (by simp [] [] [] [] [] [])] },
    refine [expr le_trans _ (half_le_self (add_nonneg (sq_nonneg _) (sq_nonneg _)))],
    refine [expr (le_div_iff (@zero_lt_two exprℝ() _ _)).mpr ((le_of_eq _).trans (two_mul_le_add_sq _ _))],
    ring [] },
  simp_rw ["[", "<-", expr is_R_or_C.norm_eq_abs, ",", "<-", expr real.rpow_nat_cast, "]"] ["at", ident h'],
  refine [expr (snorm_mono_ae (ae_of_all _ h')).trans_lt ((snorm_add_le _ _ le_rfl).trans_lt _)],
  { exact [expr (Lp.ae_measurable f).norm.pow_const _] },
  { exact [expr (Lp.ae_measurable g).norm.pow_const _] },
  simp [] [] ["only"] ["[", expr nat.cast_bit0, ",", expr ennreal.add_lt_top, ",", expr nat.cast_one, "]"] [] [],
  exact [expr ⟨snorm_rpow_two_norm_lt_top f, snorm_rpow_two_norm_lt_top g⟩]
end

section InnerProductSpace

open_locale ComplexConjugate

include 𝕜

instance  : HasInner 𝕜 (α →₂[μ] E) :=
  ⟨fun f g => ∫a, ⟪f a, g a⟫ ∂μ⟩

theorem inner_def (f g : α →₂[μ] E) : inner f g = ∫a : α, ⟪f a, g a⟫ ∂μ :=
  rfl

-- error in MeasureTheory.Function.L2Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integral_inner_eq_sq_snorm
(f : «expr →₂[ ] »(α, μ, E)) : «expr = »(«expr∫ , ∂ »((a), «expr⟪ , ⟫»(f a, f a), μ), ennreal.to_real «expr∫⁻ , ∂ »((a), «expr ^ »((nnnorm (f a) : «exprℝ≥0∞»()), (2 : exprℝ())), μ)) :=
begin
  simp_rw [expr inner_self_eq_norm_sq_to_K] [],
  norm_cast [],
  rw [expr integral_eq_lintegral_of_nonneg_ae] [],
  swap,
  { exact [expr filter.eventually_of_forall (λ x, sq_nonneg _)] },
  swap,
  { exact [expr (Lp.ae_measurable f).norm.pow_const _] },
  congr,
  ext1 [] [ident x],
  have [ident h_two] [":", expr «expr = »((2 : exprℝ()), ((2 : exprℕ()) : exprℝ()))] [],
  by simp [] [] [] [] [] [],
  rw ["[", "<-", expr real.rpow_nat_cast _ 2, ",", "<-", expr h_two, ",", "<-", expr ennreal.of_real_rpow_of_nonneg (norm_nonneg _) zero_le_two, ",", expr of_real_norm_eq_coe_nnnorm, "]"] [],
  norm_cast []
end

-- error in MeasureTheory.Function.L2Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem norm_sq_eq_inner'
(f : «expr →₂[ ] »(α, μ, E)) : «expr = »(«expr ^ »(«expr∥ ∥»(f), 2), is_R_or_C.re (inner f f : 𝕜)) :=
begin
  have [ident h_two] [":", expr «expr = »((2 : «exprℝ≥0∞»()).to_real, 2)] [":=", expr by simp [] [] [] [] [] []],
  rw ["[", expr inner_def, ",", expr integral_inner_eq_sq_snorm, ",", expr norm_def, ",", "<-", expr ennreal.to_real_pow, ",", expr is_R_or_C.of_real_re, ",", expr ennreal.to_real_eq_to_real (ennreal.pow_ne_top (Lp.snorm_ne_top f)) _, "]"] [],
  { rw ["[", "<-", expr ennreal.rpow_nat_cast, ",", expr snorm_eq_snorm' ennreal.two_ne_zero ennreal.two_ne_top, ",", expr snorm', ",", "<-", expr ennreal.rpow_mul, ",", expr one_div, ",", expr h_two, "]"] [],
    simp [] [] [] [] [] [] },
  { refine [expr (lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top zero_lt_two _).ne],
    rw ["[", "<-", expr h_two, ",", "<-", expr snorm_eq_snorm' ennreal.two_ne_zero ennreal.two_ne_top, "]"] [],
    exact [expr Lp.snorm_lt_top f] }
end

theorem mem_L1_inner (f g : α →₂[μ] E) :
  ae_eq_fun.mk (fun x => ⟪f x, g x⟫) ((Lp.ae_measurable f).inner (Lp.ae_measurable g)) ∈ Lp 𝕜 1 μ :=
  by 
    simpRw [mem_Lp_iff_snorm_lt_top, snorm_ae_eq_fun]
    exact snorm_inner_lt_top f g

-- error in MeasureTheory.Function.L2Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem integrable_inner (f g : «expr →₂[ ] »(α, μ, E)) : integrable (λ x : α, «expr⟪ , ⟫»(f x, g x)) μ :=
(integrable_congr (ae_eq_fun.coe_fn_mk (λ
   x, «expr⟪ , ⟫»(f x, g x)) ((Lp.ae_measurable f).inner (Lp.ae_measurable g)))).mp (ae_eq_fun.integrable_iff_mem_L1.mpr (mem_L1_inner f g))

private theorem add_left' (f f' g : α →₂[μ] E) : (inner (f+f') g : 𝕜) = inner f g+inner f' g :=
  by 
    simpRw [inner_def, ←integral_add (integrable_inner f g) (integrable_inner f' g), ←inner_add_left]
    refine' integral_congr_ae ((coe_fn_add f f').mono fun x hx => _)
    congr 
    rwa [Pi.add_apply] at hx

private theorem smul_left' (f g : α →₂[μ] E) (r : 𝕜) : inner (r • f) g = conj r*inner f g :=
  by 
    rw [inner_def, inner_def, ←smul_eq_mul, ←integral_smul]
    refine' integral_congr_ae ((coe_fn_smul r f).mono fun x hx => _)
    rw [smul_eq_mul, ←inner_smul_left]
    congr 
    rwa [Pi.smul_apply] at hx

instance InnerProductSpace : InnerProductSpace 𝕜 (α →₂[μ] E) :=
  { norm_sq_eq_inner := norm_sq_eq_inner',
    conj_sym :=
      fun _ _ =>
        by 
          simpRw [inner_def, ←integral_conj, inner_conj_sym],
    add_left := add_left', smulLeft := smul_left' }

end InnerProductSpace

section IndicatorConstLp

variable{s : Set α}

variable(𝕜)

-- error in MeasureTheory.Function.L2Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is
equal to the integral of the inner product over `s`: `∫ x in s, ⟪c, f x⟫ ∂μ`. -/
theorem inner_indicator_const_Lp_eq_set_integral_inner
(f : Lp E 2 μ)
(hs : measurable_set s)
(c : E)
(hμs : «expr ≠ »(μ s, «expr∞»())) : «expr = »(inner (indicator_const_Lp 2 hs hμs c) f, «expr∫ in , ∂ »((x), s, «expr⟪ , ⟫»(c, f x), μ)) :=
begin
  rw ["[", expr inner_def, ",", "<-", expr integral_add_compl hs (L2.integrable_inner _ f), "]"] [],
  have [ident h_left] [":", expr «expr = »(«expr∫ in , ∂ »((x), s, «expr⟪ , ⟫»(indicator_const_Lp 2 hs hμs c x, f x), μ), «expr∫ in , ∂ »((x), s, «expr⟪ , ⟫»(c, f x), μ))] [],
  { suffices [ident h_ae_eq] [":", expr «expr∀ᵐ ∂ , »((x), μ, «expr ∈ »(x, s) → «expr = »(«expr⟪ , ⟫»(indicator_const_Lp 2 hs hμs c x, f x), «expr⟪ , ⟫»(c, f x)))],
    from [expr set_integral_congr_ae hs h_ae_eq],
    have [ident h_indicator] [":", expr «expr∀ᵐ ∂ , »((x : α), μ, «expr ∈ »(x, s) → «expr = »(indicator_const_Lp 2 hs hμs c x, c))] [],
    from [expr indicator_const_Lp_coe_fn_mem],
    refine [expr h_indicator.mono (λ x hx hxs, _)],
    congr,
    exact [expr hx hxs] },
  have [ident h_right] [":", expr «expr = »(«expr∫ in , ∂ »((x), «expr ᶜ»(s), «expr⟪ , ⟫»(indicator_const_Lp 2 hs hμs c x, f x), μ), 0)] [],
  { suffices [ident h_ae_eq] [":", expr «expr∀ᵐ ∂ , »((x), μ, «expr ∉ »(x, s) → «expr = »(«expr⟪ , ⟫»(indicator_const_Lp 2 hs hμs c x, f x), 0))],
    { simp_rw ["<-", expr set.mem_compl_iff] ["at", ident h_ae_eq],
      suffices [ident h_int_zero] [":", expr «expr = »(«expr∫ in , ∂ »((x), «expr ᶜ»(s), inner (indicator_const_Lp 2 hs hμs c x) (f x), μ), «expr∫ in , ∂ »((x), «expr ᶜ»(s), (0 : 𝕜), μ))],
      { rw [expr h_int_zero] [],
        simp [] [] [] [] [] [] },
      exact [expr set_integral_congr_ae hs.compl h_ae_eq] },
    have [ident h_indicator] [":", expr «expr∀ᵐ ∂ , »((x : α), μ, «expr ∉ »(x, s) → «expr = »(indicator_const_Lp 2 hs hμs c x, 0))] [],
    from [expr indicator_const_Lp_coe_fn_nmem],
    refine [expr h_indicator.mono (λ x hx hxs, _)],
    rw [expr hx hxs] [],
    exact [expr inner_zero_left] },
  rw ["[", expr h_left, ",", expr h_right, ",", expr add_zero, "]"] []
end

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs c` and `f` is
equal to the inner product of the constant `c` and the integral of `f` over `s`. -/
theorem inner_indicator_const_Lp_eq_inner_set_integral [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) (f : Lp E 2 μ) :
  inner (indicator_const_Lp 2 hs hμs c) f = ⟪c, ∫x in s, f x ∂μ⟫ :=
  by 
    rw [←integral_inner (integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs),
      L2.inner_indicator_const_Lp_eq_set_integral_inner]

variable{𝕜}

/-- The inner product in `L2` of the indicator of a set `indicator_const_Lp 2 hs hμs (1 : 𝕜)` and
a real or complex function `f` is equal to the integral of `f` over `s`. -/
theorem inner_indicator_const_Lp_one (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : Lp 𝕜 2 μ) :
  inner (indicator_const_Lp 2 hs hμs (1 : 𝕜)) f = ∫x in s, f x ∂μ :=
  by 
    rw [L2.inner_indicator_const_Lp_eq_inner_set_integral 𝕜 hs hμs (1 : 𝕜) f]
    simp 

end IndicatorConstLp

end L2

section InnerContinuous

variable{α : Type _}[TopologicalSpace α][measure_space α][BorelSpace α]{𝕜 : Type _}[IsROrC 𝕜]

variable(μ : Measureₓ α)[is_finite_measure μ]

open_locale BoundedContinuousFunction ComplexConjugate

attribute [local instance] fact_one_le_two_ennreal

local notation "⟪" x ", " y "⟫" => @inner 𝕜 (α →₂[μ] 𝕜) _ x y

-- error in MeasureTheory.Function.L2Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For bounded continuous functions `f`, `g` on a finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
theorem bounded_continuous_function.inner_to_Lp
(f
 g : «expr →ᵇ »(α, 𝕜)) : «expr = »(«expr⟪ , ⟫»(bounded_continuous_function.to_Lp 2 μ 𝕜 f, bounded_continuous_function.to_Lp 2 μ 𝕜 g), «expr∫ , ∂ »((x), «expr * »(exprconj() (f x), g x), μ)) :=
begin
  apply [expr integral_congr_ae],
  have [ident hf_ae] [] [":=", expr f.coe_fn_to_Lp μ],
  have [ident hg_ae] [] [":=", expr g.coe_fn_to_Lp μ],
  filter_upwards ["[", expr hf_ae, ",", expr hg_ae, "]"] [],
  intros [ident x, ident hf, ident hg],
  rw ["[", expr hf, ",", expr hg, "]"] [],
  simp [] [] [] [] [] []
end

variable[CompactSpace α]

-- error in MeasureTheory.Function.L2Space: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For continuous functions `f`, `g` on a compact, finite-measure topological space `α`, the L^2
inner product is the integral of their pointwise inner product. -/
theorem continuous_map.inner_to_Lp
(f
 g : «exprC( , )»(α, 𝕜)) : «expr = »(«expr⟪ , ⟫»(continuous_map.to_Lp 2 μ 𝕜 f, continuous_map.to_Lp 2 μ 𝕜 g), «expr∫ , ∂ »((x), «expr * »(exprconj() (f x), g x), μ)) :=
begin
  apply [expr integral_congr_ae],
  have [ident hf_ae] [] [":=", expr f.coe_fn_to_Lp μ],
  have [ident hg_ae] [] [":=", expr g.coe_fn_to_Lp μ],
  filter_upwards ["[", expr hf_ae, ",", expr hg_ae, "]"] [],
  intros [ident x, ident hf, ident hg],
  rw ["[", expr hf, ",", expr hg, "]"] [],
  simp [] [] [] [] [] []
end

end InnerContinuous

end MeasureTheory

