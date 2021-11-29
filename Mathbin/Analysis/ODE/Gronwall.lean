import Mathbin.Analysis.SpecialFunctions.ExpDeriv

/-!
# Grönwall's inequality

The main technical result of this file is the Grönwall-like inequality
`norm_le_gronwall_bound_of_norm_deriv_right_le`. It states that if `f : ℝ → E` satisfies `∥f a∥ ≤ δ`
and `∀ x ∈ [a, b), ∥f' x∥ ≤ K * ∥f x∥ + ε`, then for all `x ∈ [a, b]` we have `∥f x∥ ≤ δ * exp (K *
x) + (ε / K) * (exp (K * x) - 1)`.

Then we use this inequality to prove some estimates on the possible rate of growth of the distance
between two approximate or exact solutions of an ordinary differential equation.

The proofs are based on [Hubbard and West, *Differential Equations: A Dynamical Systems Approach*,
Sec. 4.5][HubbardWest-ode], where `norm_le_gronwall_bound_of_norm_deriv_right_le` is called
“Fundamental Inequality”.

## TODO

- Once we have FTC, prove an inequality for a function satisfying `∥f' x∥ ≤ K x * ∥f x∥ + ε`,
  or more generally `liminf_{y→x+0} (f y - f x)/(y - x) ≤ K x * f x + ε` with any sign
  of `K x` and `f x`.
-/


variable{E : Type _}[NormedGroup E][NormedSpace ℝ E]{F : Type _}[NormedGroup F][NormedSpace ℝ F]

open Metric Set Asymptotics Filter Real

open_locale Classical TopologicalSpace Nnreal

/-! ### Technical lemmas about `gronwall_bound` -/


/-- Upper bound used in several Grönwall-like inequalities. -/
noncomputable def gronwallBound (δ K ε x : ℝ) : ℝ :=
  if K = 0 then δ+ε*x else (δ*exp (K*x))+(ε / K)*exp (K*x) - 1

theorem gronwall_bound_K0 (δ ε : ℝ) : gronwallBound δ 0 ε = fun x => δ+ε*x :=
  funext$ fun x => if_pos rfl

theorem gronwall_bound_of_K_ne_0 {δ K ε : ℝ} (hK : K ≠ 0) :
  gronwallBound δ K ε = fun x => (δ*exp (K*x))+(ε / K)*exp (K*x) - 1 :=
  funext$ fun x => if_neg hK

theorem has_deriv_at_gronwall_bound (δ K ε x : ℝ) : HasDerivAt (gronwallBound δ K ε) ((K*gronwallBound δ K ε x)+ε) x :=
  by 
    byCases' hK : K = 0
    ·
      subst K 
      simp only [gronwall_bound_K0, zero_mul, zero_addₓ]
      convert ((has_deriv_at_id x).const_mul ε).const_add δ 
      rw [mul_oneₓ]
    ·
      simp only [gronwall_bound_of_K_ne_0 hK]
      convert
        (((has_deriv_at_id x).const_mul K).exp.const_mul δ).add
          ((((has_deriv_at_id x).const_mul K).exp.sub_const 1).const_mul (ε / K)) using
        1
      simp only [id, mul_addₓ, (mul_assocₓ _ _ _).symm, mul_commₓ _ K, mul_div_cancel' _ hK]
      ring

theorem has_deriv_at_gronwall_bound_shift (δ K ε x a : ℝ) :
  HasDerivAt (fun y => gronwallBound δ K ε (y - a)) ((K*gronwallBound δ K ε (x - a))+ε) x :=
  by 
    convert (has_deriv_at_gronwall_bound δ K ε _).comp x ((has_deriv_at_id x).sub_const a)
    rw [id, mul_oneₓ]

theorem gronwall_bound_x0 (δ K ε : ℝ) : gronwallBound δ K ε 0 = δ :=
  by 
    byCases' hK : K = 0
    ·
      simp only [gronwallBound, if_pos hK, mul_zero, add_zeroₓ]
    ·
      simp only [gronwallBound, if_neg hK, mul_zero, exp_zero, sub_self, mul_oneₓ, add_zeroₓ]

theorem gronwall_bound_ε0 (δ K x : ℝ) : gronwallBound δ K 0 x = δ*exp (K*x) :=
  by 
    byCases' hK : K = 0
    ·
      simp only [gronwall_bound_K0, hK, zero_mul, exp_zero, add_zeroₓ, mul_oneₓ]
    ·
      simp only [gronwall_bound_of_K_ne_0 hK, zero_div, zero_mul, add_zeroₓ]

theorem gronwall_bound_ε0_δ0 (K x : ℝ) : gronwallBound 0 K 0 x = 0 :=
  by 
    simp only [gronwall_bound_ε0, zero_mul]

theorem gronwall_bound_continuous_ε (δ K x : ℝ) : Continuous fun ε => gronwallBound δ K ε x :=
  by 
    byCases' hK : K = 0
    ·
      simp only [gronwall_bound_K0, hK]
      exact continuous_const.add (continuous_id.mul continuous_const)
    ·
      simp only [gronwall_bound_of_K_ne_0 hK]
      exact continuous_const.add ((continuous_id.mul continuous_const).mul continuous_const)

/-! ### Inequality and corollaries -/


-- error in Analysis.ODE.Gronwall: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A Grönwall-like inequality: if `f : ℝ → ℝ` is continuous on `[a, b]` and satisfies
the inequalities `f a ≤ δ` and
`∀ x ∈ [a, b), liminf_{z→x+0} (f z - f x)/(z - x) ≤ K * (f x) + ε`, then `f x`
is bounded by `gronwall_bound δ K ε (x - a)` on `[a, b]`.

See also `norm_le_gronwall_bound_of_norm_deriv_right_le` for a version bounding `∥f x∥`,
`f : ℝ → E`. -/
theorem le_gronwall_bound_of_liminf_deriv_right_le
{f f' : exprℝ() → exprℝ()}
{δ K ε : exprℝ()}
{a b : exprℝ()}
(hf : continuous_on f (Icc a b))
(hf' : ∀
 x «expr ∈ » Ico a b, ∀
 r, «expr < »(f' x, r) → «expr∃ᶠ in , »((z), «expr𝓝[ ] »(Ioi x, x), «expr < »(«expr * »(«expr ⁻¹»(«expr - »(z, x)), «expr - »(f z, f x)), r)))
(ha : «expr ≤ »(f a, δ))
(bound : ∀
 x «expr ∈ » Ico a b, «expr ≤ »(f' x, «expr + »(«expr * »(K, f x), ε))) : ∀
x «expr ∈ » Icc a b, «expr ≤ »(f x, gronwall_bound δ K ε «expr - »(x, a)) :=
begin
  have [ident H] [":", expr ∀
   x «expr ∈ » Icc a b, ∀ ε' «expr ∈ » Ioi ε, «expr ≤ »(f x, gronwall_bound δ K ε' «expr - »(x, a))] [],
  { assume [binders (x hx ε' hε')],
    apply [expr image_le_of_liminf_slope_right_lt_deriv_boundary hf hf'],
    { rwa ["[", expr sub_self, ",", expr gronwall_bound_x0, "]"] [] },
    { exact [expr λ x, has_deriv_at_gronwall_bound_shift δ K ε' x a] },
    { assume [binders (x hx hfB)],
      rw ["[", "<-", expr hfB, "]"] [],
      apply [expr lt_of_le_of_lt (bound x hx)],
      exact [expr add_lt_add_left hε' _] },
    { exact [expr hx] } },
  assume [binders (x hx)],
  change [expr «expr ≤ »(f x, λ ε', gronwall_bound δ K ε' «expr - »(x, a) ε)] [] [],
  convert [] [expr continuous_within_at_const.closure_le _ _ (H x hx)] [],
  { simp [] [] ["only"] ["[", expr closure_Ioi, ",", expr left_mem_Ici, "]"] [] [] },
  exact [expr (gronwall_bound_continuous_ε δ K «expr - »(x, a)).continuous_within_at]
end

/-- A Grönwall-like inequality: if `f : ℝ → E` is continuous on `[a, b]`, has right derivative
`f' x` at every point `x ∈ [a, b)`, and satisfies the inequalities `∥f a∥ ≤ δ`,
`∀ x ∈ [a, b), ∥f' x∥ ≤ K * ∥f x∥ + ε`, then `∥f x∥` is bounded by `gronwall_bound δ K ε (x - a)`
on `[a, b]`. -/
theorem norm_le_gronwall_bound_of_norm_deriv_right_le {f f' : ℝ → E} {δ K ε : ℝ} {a b : ℝ}
  (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x (_ : x ∈ Ico a b), HasDerivWithinAt f (f' x) (Ici x) x) (ha : ∥f a∥ ≤ δ)
  (bound : ∀ x (_ : x ∈ Ico a b), ∥f' x∥ ≤ (K*∥f x∥)+ε) : ∀ x (_ : x ∈ Icc a b), ∥f x∥ ≤ gronwallBound δ K ε (x - a) :=
  le_gronwall_bound_of_liminf_deriv_right_le (continuous_norm.comp_continuous_on hf)
    (fun x hx r hr => (hf' x hx).liminf_right_slope_norm_le hr) ha bound

-- error in Analysis.ODE.Gronwall: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_approx_trajectories_ODE_of_mem_set
{v : exprℝ() → E → E}
{s : exprℝ() → set E}
{K : exprℝ()}
(hv : ∀ t, ∀ x y «expr ∈ » s t, «expr ≤ »(dist (v t x) (v t y), «expr * »(K, dist x y)))
{f g f' g' : exprℝ() → E}
{a b : exprℝ()}
{εf εg δ : exprℝ()}
(hf : continuous_on f (Icc a b))
(hf' : ∀ t «expr ∈ » Ico a b, has_deriv_within_at f (f' t) (Ici t) t)
(f_bound : ∀ t «expr ∈ » Ico a b, «expr ≤ »(dist (f' t) (v t (f t)), εf))
(hfs : ∀ t «expr ∈ » Ico a b, «expr ∈ »(f t, s t))
(hg : continuous_on g (Icc a b))
(hg' : ∀ t «expr ∈ » Ico a b, has_deriv_within_at g (g' t) (Ici t) t)
(g_bound : ∀ t «expr ∈ » Ico a b, «expr ≤ »(dist (g' t) (v t (g t)), εg))
(hgs : ∀ t «expr ∈ » Ico a b, «expr ∈ »(g t, s t))
(ha : «expr ≤ »(dist (f a) (g a), δ)) : ∀
t «expr ∈ » Icc a b, «expr ≤ »(dist (f t) (g t), gronwall_bound δ K «expr + »(εf, εg) «expr - »(t, a)) :=
begin
  simp [] [] ["only"] ["[", expr dist_eq_norm, "]"] [] ["at", ident ha, "⊢"],
  have [ident h_deriv] [":", expr ∀
   t «expr ∈ » Ico a b, has_deriv_within_at (λ t, «expr - »(f t, g t)) «expr - »(f' t, g' t) (Ici t) t] [],
  from [expr λ t ht, (hf' t ht).sub (hg' t ht)],
  apply [expr norm_le_gronwall_bound_of_norm_deriv_right_le (hf.sub hg) h_deriv ha],
  assume [binders (t ht)],
  have [] [] [":=", expr dist_triangle4_right (f' t) (g' t) (v t (f t)) (v t (g t))],
  rw ["[", expr dist_eq_norm, "]"] ["at", ident this],
  apply [expr le_trans this],
  apply [expr le_trans (add_le_add (add_le_add (f_bound t ht) (g_bound t ht)) (hv t (f t) (g t) (hfs t ht) (hgs t ht)))],
  rw ["[", expr dist_eq_norm, ",", expr add_comm, "]"] []
end

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
theorem dist_le_of_approx_trajectories_ODE {v : ℝ → E → E} {K :  ℝ≥0 } (hv : ∀ t, LipschitzWith K (v t))
  {f g f' g' : ℝ → E} {a b : ℝ} {εf εg δ : ℝ} (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ t (_ : t ∈ Ico a b), HasDerivWithinAt f (f' t) (Ici t) t)
  (f_bound : ∀ t (_ : t ∈ Ico a b), dist (f' t) (v t (f t)) ≤ εf) (hg : ContinuousOn g (Icc a b))
  (hg' : ∀ t (_ : t ∈ Ico a b), HasDerivWithinAt g (g' t) (Ici t) t)
  (g_bound : ∀ t (_ : t ∈ Ico a b), dist (g' t) (v t (g t)) ≤ εg) (ha : dist (f a) (g a) ≤ δ) :
  ∀ t (_ : t ∈ Icc a b), dist (f t) (g t) ≤ gronwallBound δ K (εf+εg) (t - a) :=
  have hfs : ∀ t (_ : t ∈ Ico a b), f t ∈ @univ E := fun t ht => trivialₓ 
  dist_le_of_approx_trajectories_ODE_of_mem_set (fun t x y hx hy => (hv t).dist_le_mul x y) hf hf' f_bound hfs hg hg'
    g_bound (fun t ht => trivialₓ) ha

-- error in Analysis.ODE.Gronwall: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
theorem dist_le_of_trajectories_ODE_of_mem_set
{v : exprℝ() → E → E}
{s : exprℝ() → set E}
{K : exprℝ()}
(hv : ∀ t, ∀ x y «expr ∈ » s t, «expr ≤ »(dist (v t x) (v t y), «expr * »(K, dist x y)))
{f g : exprℝ() → E}
{a b : exprℝ()}
{δ : exprℝ()}
(hf : continuous_on f (Icc a b))
(hf' : ∀ t «expr ∈ » Ico a b, has_deriv_within_at f (v t (f t)) (Ici t) t)
(hfs : ∀ t «expr ∈ » Ico a b, «expr ∈ »(f t, s t))
(hg : continuous_on g (Icc a b))
(hg' : ∀ t «expr ∈ » Ico a b, has_deriv_within_at g (v t (g t)) (Ici t) t)
(hgs : ∀ t «expr ∈ » Ico a b, «expr ∈ »(g t, s t))
(ha : «expr ≤ »(dist (f a) (g a), δ)) : ∀
t «expr ∈ » Icc a b, «expr ≤ »(dist (f t) (g t), «expr * »(δ, exp «expr * »(K, «expr - »(t, a)))) :=
begin
  have [ident f_bound] [":", expr ∀ t «expr ∈ » Ico a b, «expr ≤ »(dist (v t (f t)) (v t (f t)), 0)] [],
  by { intros [],
    rw ["[", expr dist_self, "]"] [] },
  have [ident g_bound] [":", expr ∀ t «expr ∈ » Ico a b, «expr ≤ »(dist (v t (g t)) (v t (g t)), 0)] [],
  by { intros [],
    rw ["[", expr dist_self, "]"] [] },
  assume [binders (t ht)],
  have [] [] [":=", expr dist_le_of_approx_trajectories_ODE_of_mem_set hv hf hf' f_bound hfs hg hg' g_bound hgs ha t ht],
  rwa ["[", expr zero_add, ",", expr gronwall_bound_ε0, "]"] ["at", ident this]
end

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
theorem dist_le_of_trajectories_ODE {v : ℝ → E → E} {K :  ℝ≥0 } (hv : ∀ t, LipschitzWith K (v t)) {f g : ℝ → E}
  {a b : ℝ} {δ : ℝ} (hf : ContinuousOn f (Icc a b))
  (hf' : ∀ t (_ : t ∈ Ico a b), HasDerivWithinAt f (v t (f t)) (Ici t) t) (hg : ContinuousOn g (Icc a b))
  (hg' : ∀ t (_ : t ∈ Ico a b), HasDerivWithinAt g (v t (g t)) (Ici t) t) (ha : dist (f a) (g a) ≤ δ) :
  ∀ t (_ : t ∈ Icc a b), dist (f t) (g t) ≤ δ*exp (K*t - a) :=
  have hfs : ∀ t (_ : t ∈ Ico a b), f t ∈ @univ E := fun t ht => trivialₓ 
  dist_le_of_trajectories_ODE_of_mem_set (fun t x y hx hy => (hv t).dist_le_mul x y) hf hf' hfs hg hg'
    (fun t ht => trivialₓ) ha

-- error in Analysis.ODE.Gronwall: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) in a set `s ⊆ ℝ × E` with
a given initial value provided that RHS is Lipschitz continuous in `x` within `s`,
and we consider only solutions included in `s`. -/
theorem ODE_solution_unique_of_mem_set
{v : exprℝ() → E → E}
{s : exprℝ() → set E}
{K : exprℝ()}
(hv : ∀ t, ∀ x y «expr ∈ » s t, «expr ≤ »(dist (v t x) (v t y), «expr * »(K, dist x y)))
{f g : exprℝ() → E}
{a b : exprℝ()}
(hf : continuous_on f (Icc a b))
(hf' : ∀ t «expr ∈ » Ico a b, has_deriv_within_at f (v t (f t)) (Ici t) t)
(hfs : ∀ t «expr ∈ » Ico a b, «expr ∈ »(f t, s t))
(hg : continuous_on g (Icc a b))
(hg' : ∀ t «expr ∈ » Ico a b, has_deriv_within_at g (v t (g t)) (Ici t) t)
(hgs : ∀ t «expr ∈ » Ico a b, «expr ∈ »(g t, s t))
(ha : «expr = »(f a, g a)) : ∀ t «expr ∈ » Icc a b, «expr = »(f t, g t) :=
begin
  assume [binders (t ht)],
  have [] [] [":=", expr dist_le_of_trajectories_ODE_of_mem_set hv hf hf' hfs hg hg' hgs (dist_le_zero.2 ha) t ht],
  rwa ["[", expr zero_mul, ",", expr dist_le_zero, "]"] ["at", ident this]
end

/-- There exists only one solution of an ODE \(\dot x=v(t, x)\) with
a given initial value provided that RHS is Lipschitz continuous in `x`. -/
theorem ODE_solution_unique {v : ℝ → E → E} {K :  ℝ≥0 } (hv : ∀ t, LipschitzWith K (v t)) {f g : ℝ → E} {a b : ℝ}
  (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t (_ : t ∈ Ico a b), HasDerivWithinAt f (v t (f t)) (Ici t) t)
  (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t (_ : t ∈ Ico a b), HasDerivWithinAt g (v t (g t)) (Ici t) t)
  (ha : f a = g a) : ∀ t (_ : t ∈ Icc a b), f t = g t :=
  have hfs : ∀ t (_ : t ∈ Ico a b), f t ∈ @univ E := fun t ht => trivialₓ 
  ODE_solution_unique_of_mem_set (fun t x y hx hy => (hv t).dist_le_mul x y) hf hf' hfs hg hg' (fun t ht => trivialₓ) ha

