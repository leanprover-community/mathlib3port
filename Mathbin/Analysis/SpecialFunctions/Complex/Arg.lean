import Mathbin.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The argument of a complex number.

We define `arg : ℂ → ℝ`, returing a real number in the range (-π, π],
such that for `x ≠ 0`, `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
while `arg 0` defaults to `0`
-/


noncomputable theory

namespace Complex

open_locale Real TopologicalSpace

open Filter Set

/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
noncomputable def arg (x : ℂ) : ℝ :=
  if 0 ≤ x.re then Real.arcsin (x.im / x.abs) else
    if 0 ≤ x.im then Real.arcsin ((-x).im / x.abs)+π else Real.arcsin ((-x).im / x.abs) - π

theorem sin_arg (x : ℂ) : Real.sin (arg x) = x.im / x.abs :=
  by 
    unfold arg <;>
      splitIfs <;>
        simp [sub_eq_add_neg, arg,
          Real.sin_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1 (abs_le.1 (abs_im_div_abs_le_one x)).2, Real.sin_add,
          neg_div, Real.arcsin_neg, Real.sin_neg]

-- error in Analysis.SpecialFunctions.Complex.Arg: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem cos_arg {x : exprℂ()} (hx : «expr ≠ »(x, 0)) : «expr = »(real.cos (arg x), «expr / »(x.re, x.abs)) :=
begin
  have [ident habs] [":", expr «expr < »(0, abs x)] [":=", expr abs_pos.2 hx],
  have [ident him] [":", expr «expr ≤ »(«expr| |»(«expr / »(im x, abs x)), 1)] [],
  { rw ["[", expr _root_.abs_div, ",", expr abs_abs, "]"] [],
    exact [expr div_le_one_of_le x.abs_im_le_abs x.abs_nonneg] },
  rw [expr abs_le] ["at", ident him],
  rw [expr arg] [],
  split_ifs [] ["with", ident h₁, ident h₂, ident h₂],
  { rw ["[", expr real.cos_arcsin, "]"] []; field_simp [] ["[", expr real.sqrt_sq, ",", expr habs.le, ",", "*", "]"] [] [] },
  { rw ["[", expr real.cos_add_pi, ",", expr real.cos_arcsin, "]"] [],
    { field_simp [] ["[", expr real.sqrt_div (sq_nonneg _), ",", expr real.sqrt_sq_eq_abs, ",", expr _root_.abs_of_neg (not_le.1 h₁), ",", "*", "]"] [] [] },
    { simpa [] [] [] ["[", expr neg_div, "]"] [] ["using", expr him.2] },
    { simpa [] [] [] ["[", expr neg_div, ",", expr neg_le, "]"] [] ["using", expr him.1] } },
  { rw ["[", expr real.cos_sub_pi, ",", expr real.cos_arcsin, "]"] [],
    { field_simp [] ["[", expr real.sqrt_div (sq_nonneg _), ",", expr real.sqrt_sq_eq_abs, ",", expr _root_.abs_of_neg (not_le.1 h₁), ",", "*", "]"] [] [] },
    { simpa [] [] [] ["[", expr neg_div, "]"] [] ["using", expr him.2] },
    { simpa [] [] [] ["[", expr neg_div, ",", expr neg_le, "]"] [] ["using", expr him.1] } }
end

-- error in Analysis.SpecialFunctions.Complex.Arg: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem abs_mul_exp_arg_mul_I (x : exprℂ()) : «expr = »(«expr * »(«expr↑ »(abs x), exp «expr * »(arg x, I)), x) :=
begin
  rcases [expr eq_or_ne x 0, "with", "(", ident rfl, "|", ident hx, ")"],
  { simp [] [] [] [] [] [] },
  { have [] [":", expr «expr ≠ »(abs x, 0)] [":=", expr abs_ne_zero.2 hx],
    ext [] [] []; field_simp [] ["[", expr sin_arg, ",", expr cos_arg hx, ",", expr this, ",", expr mul_comm (abs x), "]"] [] [] }
end

@[simp]
theorem abs_mul_cos_add_sin_mul_I (x : ℂ) : (abs x*cos (arg x)+sin (arg x)*I : ℂ) = x :=
  by 
    rw [←exp_mul_I, abs_mul_exp_arg_mul_I]

-- error in Analysis.SpecialFunctions.Complex.Arg: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem arg_mul_cos_add_sin_mul_I
{r : exprℝ()}
(hr : «expr < »(0, r))
{θ : exprℝ()}
(hθ : «expr ∈ »(θ, Ioc «expr- »(exprπ()) exprπ())) : «expr = »(arg «expr * »(r, «expr + »(cos θ, «expr * »(sin θ, I))), θ) :=
begin
  have [ident hπ] [] [":=", expr real.pi_pos],
  simp [] [] ["only"] ["[", expr arg, ",", expr abs_mul, ",", expr abs_cos_add_sin_mul_I, ",", expr abs_of_nonneg hr.le, ",", expr mul_one, "]"] [] [],
  simp [] [] ["only"] ["[", expr of_real_mul_re, ",", expr of_real_mul_im, ",", expr neg_im, ",", "<-", expr of_real_cos, ",", "<-", expr of_real_sin, ",", "<-", expr mk_eq_add_mul_I, ",", expr neg_div, ",", expr mul_div_cancel_left _ hr.ne', ",", expr mul_nonneg_iff_right_nonneg_of_pos hr, "]"] [] [],
  by_cases [expr h₁, ":", expr «expr ∈ »(θ, Icc «expr- »(«expr / »(exprπ(), 2)) «expr / »(exprπ(), 2))],
  { rw [expr if_pos] [],
    exacts ["[", expr real.arcsin_sin' h₁, ",", expr real.cos_nonneg_of_mem_Icc h₁, "]"] },
  { rw ["[", expr mem_Icc, ",", expr not_and_distrib, ",", expr not_le, ",", expr not_le, "]"] ["at", ident h₁],
    cases [expr h₁] [],
    { replace [ident hθ] [] [":=", expr hθ.1],
      have [ident hcos] [":", expr «expr < »(real.cos θ, 0)] [],
      { rw ["[", "<-", expr neg_pos, ",", "<-", expr real.cos_add_pi, "]"] [],
        refine [expr real.cos_pos_of_mem_Ioo ⟨_, _⟩]; linarith [] [] [] },
      have [ident hsin] [":", expr «expr < »(real.sin θ, 0)] [":=", expr real.sin_neg_of_neg_of_neg_pi_lt (by linarith [] [] []) hθ],
      rw ["[", expr if_neg, ",", expr if_neg, ",", "<-", expr real.sin_add_pi, ",", expr real.arcsin_sin, ",", expr add_sub_cancel, "]"] []; [linarith [] [] [], linarith [] [] [], exact [expr hsin.not_le], exact [expr hcos.not_le]] },
    { replace [ident hθ] [] [":=", expr hθ.2],
      have [ident hcos] [":", expr «expr < »(real.cos θ, 0)] [":=", expr real.cos_neg_of_pi_div_two_lt_of_lt h₁ (by linarith [] [] [])],
      have [ident hsin] [":", expr «expr ≤ »(0, real.sin θ)] [":=", expr real.sin_nonneg_of_mem_Icc ⟨by linarith [] [] [], hθ⟩],
      rw ["[", expr if_neg, ",", expr if_pos, ",", "<-", expr real.sin_sub_pi, ",", expr real.arcsin_sin, ",", expr sub_add_cancel, "]"] []; [linarith [] [] [], linarith [] [] [], exact [expr hsin], exact [expr hcos.not_le]] } }
end

theorem arg_cos_add_sin_mul_I {θ : ℝ} (hθ : θ ∈ Ioc (-π) π) : arg (cos θ+sin θ*I) = θ :=
  by 
    rw [←one_mulₓ (_+_), ←of_real_one, arg_mul_cos_add_sin_mul_I zero_lt_one hθ]

@[simp]
theorem arg_zero : arg 0 = 0 :=
  by 
    simp [arg, le_reflₓ]

theorem ext_abs_arg {x y : ℂ} (h₁ : x.abs = y.abs) (h₂ : x.arg = y.arg) : x = y :=
  by 
    rw [←abs_mul_exp_arg_mul_I x, ←abs_mul_exp_arg_mul_I y, h₁, h₂]

theorem ext_abs_arg_iff {x y : ℂ} : x = y ↔ abs x = abs y ∧ arg x = arg y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, and_imp.2 ext_abs_arg⟩

-- error in Analysis.SpecialFunctions.Complex.Arg: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem arg_mem_Ioc (z : exprℂ()) : «expr ∈ »(arg z, Ioc «expr- »(exprπ()) exprπ()) :=
begin
  have [ident hπ] [":", expr «expr < »(0, exprπ())] [":=", expr real.pi_pos],
  rcases [expr eq_or_ne z 0, "with", "(", ident rfl, "|", ident hz, ")"],
  simp [] [] [] ["[", expr hπ, ",", expr hπ.le, "]"] [] [],
  rcases [expr exists_unique_add_zsmul_mem_Ioc real.two_pi_pos (arg z) «expr- »(exprπ()), "with", "⟨", ident N, ",", ident hN, ",", "-", "⟩"],
  rw ["[", expr two_mul, ",", expr neg_add_cancel_left, ",", "<-", expr two_mul, ",", expr zsmul_eq_mul, "]"] ["at", ident hN],
  rw ["[", "<-", expr abs_mul_cos_add_sin_mul_I z, ",", "<-", expr cos_add_int_mul_two_pi _ N, ",", "<-", expr sin_add_int_mul_two_pi _ N, "]"] [],
  simp [] [] ["only"] ["[", "<-", expr of_real_one, ",", "<-", expr of_real_bit0, ",", "<-", expr of_real_mul, ",", "<-", expr of_real_add, ",", "<-", expr of_real_int_cast, "]"] [] [],
  rwa ["[", expr arg_mul_cos_add_sin_mul_I (abs_pos.2 hz) hN, "]"] []
end

@[simp]
theorem range_arg : range arg = Ioc (-π) π :=
  (range_subset_iff.2 arg_mem_Ioc).antisymm fun x hx => ⟨_, arg_cos_add_sin_mul_I hx⟩

theorem arg_le_pi (x : ℂ) : arg x ≤ π :=
  (arg_mem_Ioc x).2

theorem neg_pi_lt_arg (x : ℂ) : -π < arg x :=
  (arg_mem_Ioc x).1

@[simp]
theorem arg_nonneg_iff {z : ℂ} : 0 ≤ arg z ↔ 0 ≤ z.im :=
  by 
    rcases eq_or_ne z 0 with (rfl | h₀)
    ·
      simp 
    calc 0 ≤ arg z ↔ 0 ≤ Real.sin (arg z) :=
      ⟨fun h => Real.sin_nonneg_of_mem_Icc ⟨h, arg_le_pi z⟩,
        by 
          contrapose! 
          intro h 
          exact Real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_arg _)⟩_ ↔ _ :=
      by 
        rw [sin_arg, le_div_iff (abs_pos.2 h₀), zero_mul]

@[simp]
theorem arg_neg_iff {z : ℂ} : arg z < 0 ↔ z.im < 0 :=
  lt_iff_lt_of_le_iff_le arg_nonneg_iff

theorem arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r*x) = arg x :=
  by 
    rcases eq_or_ne x 0 with (rfl | hx)
    ·
      rw [mul_zero]
    convLHS =>
      rw [←abs_mul_cos_add_sin_mul_I x, ←mul_assocₓ, ←of_real_mul,
        arg_mul_cos_add_sin_mul_I (mul_pos hr (abs_pos.2 hx)) x.arg_mem_Ioc]

theorem arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) : arg x = arg y ↔ ((abs y / abs x : ℂ)*x) = y :=
  by 
    simp only [ext_abs_arg_iff, abs_mul, abs_div, abs_of_real, abs_abs, div_mul_cancel _ (abs_ne_zero.2 hx),
      eq_self_iff_true, true_andₓ]
    rw [←of_real_div, arg_real_mul]
    exact div_pos (abs_pos.2 hy) (abs_pos.2 hx)

theorem arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg {x : ℂ} (hxr : x.re < 0) (hxi : 0 ≤ x.im) : arg x = arg (-x)+π :=
  have  : 0 ≤ (-x).re :=
    le_of_ltₓ$
      by 
        simpa [neg_pos]
  by 
    rw [arg, arg, if_neg (not_leₓ.2 hxr), if_pos this, if_pos hxi, abs_neg]

theorem arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg {x : ℂ} (hxr : x.re < 0) (hxi : x.im < 0) : arg x = arg (-x) - π :=
  have  : 0 ≤ (-x).re :=
    le_of_ltₓ$
      by 
        simpa [neg_pos]
  by 
    rw [arg, arg, if_neg (not_leₓ.2 hxr), if_neg (not_leₓ.2 hxi), if_pos this, abs_neg]

@[simp]
theorem arg_one : arg 1 = 0 :=
  by 
    simp [arg, zero_le_one]

@[simp]
theorem arg_neg_one : arg (-1) = π :=
  by 
    simp [arg, le_reflₓ, not_leₓ.2 (@zero_lt_one ℝ _ _)]

@[simp]
theorem arg_I : arg I = π / 2 :=
  by 
    simp [arg, le_reflₓ]

@[simp]
theorem arg_neg_I : arg (-I) = -(π / 2) :=
  by 
    simp [arg, le_reflₓ]

@[simp]
theorem tan_arg (x : ℂ) : Real.tan (arg x) = x.im / x.re :=
  by 
    byCases' h : x = 0
    ·
      simp only [h, zero_div, Complex.zero_im, Complex.arg_zero, Real.tan_zero, Complex.zero_re]
    rw [Real.tan_eq_sin_div_cos, sin_arg, cos_arg h, div_div_div_cancel_right _ (abs_ne_zero.2 h)]

theorem arg_of_real_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 :=
  by 
    simp [arg, hx]

theorem arg_eq_pi_iff {z : ℂ} : arg z = π ↔ z.re < 0 ∧ z.im = 0 :=
  by 
    byCases' h₀ : z = 0
    ·
      simp [h₀, lt_irreflₓ, real.pi_ne_zero.symm]
    split 
    ·
      intro h 
      rw [←abs_mul_cos_add_sin_mul_I z, h]
      simp [h₀]
    ·
      cases' z with x y 
      rintro ⟨h : x < 0, rfl : y = 0⟩
      rw [←arg_neg_one, ←arg_real_mul (-1) (neg_pos.2 h)]
      simp [←of_real_def]

theorem arg_of_real_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
  arg_eq_pi_iff.2 ⟨hx, rfl⟩

theorem arg_eq_pi_div_two_iff {z : ℂ} : arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im :=
  by 
    byCases' h₀ : z = 0
    ·
      simp [h₀, lt_irreflₓ, real.pi_div_two_pos.ne]
    split 
    ·
      intro h 
      rw [←abs_mul_cos_add_sin_mul_I z, h]
      simp [h₀]
    ·
      cases' z with x y 
      rintro ⟨rfl : x = 0, hy : 0 < y⟩
      rw [←arg_I, ←arg_real_mul I hy, of_real_mul', I_re, I_im, mul_zero, mul_oneₓ]

theorem arg_eq_neg_pi_div_two_iff {z : ℂ} : arg z = -(π / 2) ↔ z.re = 0 ∧ z.im < 0 :=
  by 
    byCases' h₀ : z = 0
    ·
      simp [h₀, lt_irreflₓ, Real.pi_ne_zero]
    split 
    ·
      intro h 
      rw [←abs_mul_cos_add_sin_mul_I z, h]
      simp [h₀]
    ·
      cases' z with x y 
      rintro ⟨rfl : x = 0, hy : y < 0⟩
      rw [←arg_neg_I, ←arg_real_mul (-I) (neg_pos.2 hy), mk_eq_add_mul_I]
      simp 

theorem arg_of_re_nonneg {x : ℂ} (hx : 0 ≤ x.re) : arg x = Real.arcsin (x.im / x.abs) :=
  if_pos hx

theorem arg_of_re_neg_of_im_nonneg {x : ℂ} (hx_re : x.re < 0) (hx_im : 0 ≤ x.im) :
  arg x = Real.arcsin ((-x).im / x.abs)+π :=
  by 
    simp only [arg, hx_re.not_le, hx_im, if_true, if_false]

theorem arg_of_re_neg_of_im_neg {x : ℂ} (hx_re : x.re < 0) (hx_im : x.im < 0) :
  arg x = Real.arcsin ((-x).im / x.abs) - π :=
  by 
    simp only [arg, hx_re.not_le, hx_im.not_le, if_false]

theorem arg_of_im_nonneg_of_ne_zero {z : ℂ} (h₁ : 0 ≤ z.im) (h₂ : z ≠ 0) : arg z = Real.arccos (z.re / abs z) :=
  by 
    rw [←cos_arg h₂, Real.arccos_cos (arg_nonneg_iff.2 h₁) (arg_le_pi _)]

theorem arg_of_im_pos {z : ℂ} (hz : 0 < z.im) : arg z = Real.arccos (z.re / abs z) :=
  arg_of_im_nonneg_of_ne_zero hz.le fun h => hz.ne'$ h.symm ▸ rfl

-- error in Analysis.SpecialFunctions.Complex.Arg: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem arg_of_im_neg
{z : exprℂ()}
(hz : «expr < »(z.im, 0)) : «expr = »(arg z, «expr- »(real.arccos «expr / »(z.re, abs z))) :=
begin
  have [ident h₀] [":", expr «expr ≠ »(z, 0)] [],
  from [expr mt (congr_arg im) hz.ne],
  rw ["[", "<-", expr cos_arg h₀, ",", "<-", expr real.cos_neg, ",", expr real.arccos_cos, ",", expr neg_neg, "]"] [],
  exacts ["[", expr neg_nonneg.2 (arg_neg_iff.2 hz).le, ",", expr neg_le.2 (neg_pi_lt_arg z).le, "]"]
end

section Continuity

variable {x z : ℂ}

theorem arg_eq_nhds_of_re_pos (hx : 0 < x.re) : arg =ᶠ[𝓝 x] fun x => Real.arcsin (x.im / x.abs) :=
  ((continuous_re.Tendsto _).Eventually (lt_mem_nhds hx)).mono$ fun y hy => arg_of_re_nonneg hy.le

theorem arg_eq_nhds_of_re_neg_of_im_pos (hx_re : x.re < 0) (hx_im : 0 < x.im) :
  arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / x.abs)+π :=
  by 
    suffices h_forall_nhds : ∀ᶠy : ℂ in 𝓝 x, y.re < 0 ∧ 0 < y.im 
    exact h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_nonneg hy.1 hy.2.le 
    refine' IsOpen.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im)
    exact IsOpen.and (is_open_lt continuous_re continuous_zero) (is_open_lt continuous_zero continuous_im)

theorem arg_eq_nhds_of_re_neg_of_im_neg (hx_re : x.re < 0) (hx_im : x.im < 0) :
  arg =ᶠ[𝓝 x] fun x => Real.arcsin ((-x).im / x.abs) - π :=
  by 
    suffices h_forall_nhds : ∀ᶠy : ℂ in 𝓝 x, y.re < 0 ∧ y.im < 0 
    exact h_forall_nhds.mono fun y hy => arg_of_re_neg_of_im_neg hy.1 hy.2
    refine' IsOpen.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0)
    exact IsOpen.and (is_open_lt continuous_re continuous_zero) (is_open_lt continuous_im continuous_zero)

theorem arg_eq_nhds_of_im_pos (hz : 0 < im z) : arg =ᶠ[𝓝 z] fun x => Real.arccos (x.re / abs x) :=
  ((continuous_im.Tendsto _).Eventually (lt_mem_nhds hz)).mono$ fun x => arg_of_im_pos

theorem arg_eq_nhds_of_im_neg (hz : im z < 0) : arg =ᶠ[𝓝 z] fun x => -Real.arccos (x.re / abs x) :=
  ((continuous_im.Tendsto _).Eventually (gt_mem_nhds hz)).mono$ fun x => arg_of_im_neg

-- error in Analysis.SpecialFunctions.Complex.Arg: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_at_arg (h : «expr ∨ »(«expr < »(0, x.re), «expr ≠ »(x.im, 0))) : continuous_at arg x :=
begin
  have [ident h₀] [":", expr «expr ≠ »(abs x, 0)] [],
  { rw [expr abs_ne_zero] [],
    rintro [ident rfl],
    simpa [] [] [] [] [] ["using", expr h] },
  rw ["[", "<-", expr lt_or_lt_iff_ne, "]"] ["at", ident h],
  rcases [expr h, "with", "(", ident hx_re, "|", ident hx_im, "|", ident hx_im, ")"],
  exacts ["[", expr (real.continuous_at_arcsin.comp (continuous_im.continuous_at.div continuous_abs.continuous_at h₀)).congr (arg_eq_nhds_of_re_pos hx_re).symm, ",", expr (real.continuous_arccos.continuous_at.comp (continuous_re.continuous_at.div continuous_abs.continuous_at h₀)).neg.congr (arg_eq_nhds_of_im_neg hx_im).symm, ",", expr (real.continuous_arccos.continuous_at.comp (continuous_re.continuous_at.div continuous_abs.continuous_at h₀)).congr (arg_eq_nhds_of_im_pos hx_im).symm, "]"]
end

-- error in Analysis.SpecialFunctions.Complex.Arg: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero
{z : exprℂ()}
(hre : «expr < »(z.re, 0))
(him : «expr = »(z.im, 0)) : tendsto arg «expr𝓝[ ] »({z : exprℂ() | «expr < »(z.im, 0)}, z) (expr𝓝() «expr- »(exprπ())) :=
begin
  suffices [ident H] [":", expr tendsto (λ
    x : exprℂ(), «expr - »(real.arcsin «expr / »(«expr- »(x).im, x.abs), exprπ())) «expr𝓝[ ] »({z : exprℂ() | «expr < »(z.im, 0)}, z) (expr𝓝() «expr- »(exprπ()))],
  { refine [expr H.congr' _],
    have [] [":", expr «expr∀ᶠ in , »((x : exprℂ()), expr𝓝() z, «expr < »(x.re, 0))] [],
    from [expr continuous_re.tendsto z (gt_mem_nhds hre)],
    filter_upwards ["[", expr self_mem_nhds_within, ",", expr mem_nhds_within_of_mem_nhds this, "]"] [],
    intros [ident w, ident him, ident hre],
    rw ["[", expr arg, ",", expr if_neg hre.not_le, ",", expr if_neg him.not_le, "]"] [] },
  convert [] [expr (real.continuous_at_arcsin.comp_continuous_within_at ((continuous_im.continuous_at.comp_continuous_within_at continuous_within_at_neg).div continuous_abs.continuous_within_at _)).sub tendsto_const_nhds] [],
  { simp [] [] [] ["[", expr him, "]"] [] [] },
  { lift [expr z] ["to", expr exprℝ()] ["using", expr him] [],
    simpa [] [] [] [] [] ["using", expr hre.ne] }
end

-- error in Analysis.SpecialFunctions.Complex.Arg: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_within_at_arg_of_re_neg_of_im_zero
{z : exprℂ()}
(hre : «expr < »(z.re, 0))
(him : «expr = »(z.im, 0)) : continuous_within_at arg {z : exprℂ() | «expr ≤ »(0, z.im)} z :=
begin
  have [] [":", expr «expr =ᶠ[ ] »(arg, «expr𝓝[ ] »({z : exprℂ() | «expr ≤ »(0, z.im)}, z), λ
    x, «expr + »(real.arcsin «expr / »(«expr- »(x).im, x.abs), exprπ()))] [],
  { have [] [":", expr «expr∀ᶠ in , »((x : exprℂ()), expr𝓝() z, «expr < »(x.re, 0))] [],
    from [expr continuous_re.tendsto z (gt_mem_nhds hre)],
    filter_upwards ["[", expr self_mem_nhds_within, ",", expr mem_nhds_within_of_mem_nhds this, "]"] [],
    intros [ident w, ident him, ident hre],
    rw ["[", expr arg, ",", expr if_neg hre.not_le, ",", expr if_pos him, "]"] [] },
  refine [expr continuous_within_at.congr_of_eventually_eq _ this _],
  { refine [expr (real.continuous_at_arcsin.comp_continuous_within_at ((continuous_im.continuous_at.comp_continuous_within_at continuous_within_at_neg).div continuous_abs.continuous_within_at _)).add tendsto_const_nhds],
    lift [expr z] ["to", expr exprℝ()] ["using", expr him] [],
    simpa [] [] [] [] [] ["using", expr hre.ne] },
  { rw ["[", expr arg, ",", expr if_neg hre.not_le, ",", expr if_pos him.ge, "]"] [] }
end

theorem tendsto_arg_nhds_within_im_nonneg_of_re_neg_of_im_zero {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  tendsto arg (𝓝[{ z:ℂ | 0 ≤ z.im }] z) (𝓝 π) :=
  by 
    simpa only [arg_eq_pi_iff.2 ⟨hre, him⟩] using (continuous_within_at_arg_of_re_neg_of_im_zero hre him).Tendsto

end Continuity

end Complex

