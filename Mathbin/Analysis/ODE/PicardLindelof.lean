import Mathbin.Analysis.SpecialFunctions.Integrals 
import Mathbin.Topology.MetricSpace.Contracting

/-!
# Picard-Lindelöf (Cauchy-Lipschitz) Theorem

In this file we prove that an ordinary differential equation $\dot x=v(t, x)$ such that $v$ is
Lipschitz continuous in $x$ and continuous in $t$ has a local solution, see
`exists_forall_deriv_within_Icc_eq_of_lipschitz_of_continuous`.

## Implementation notes

In order to split the proof into small lemmas, we introduce a structure `picard_lindelof` that holds
all assumptions of the main theorem. This structure and lemmas in the `picard_lindelof` namespace
should be treated as private implementation details.

We only prove existence of a solution in this file. For uniqueness see `ODE_solution_unique` and
related theorems in `analysis.ODE.gronwall`.

## Tags

differential equation
-/


open Filter Function Set Metric TopologicalSpace intervalIntegral MeasureTheory

open measure_theory.measure_space(volume)

open_locale Filter TopologicalSpace Nnreal Ennreal Nat Interval

noncomputable theory

variable{E : Type _}[NormedGroup E][NormedSpace ℝ E]

/-- This structure holds arguments of the Picard-Lipschitz (Cauchy-Lipschitz) theorem. Unless you
want to use one of the auxiliary lemmas, use
`exists_forall_deriv_within_Icc_eq_of_lipschitz_of_continuous` instead of using this structure. -/
structure PicardLindelof(E : Type _)[NormedGroup E][NormedSpace ℝ E] where 
  toFun : ℝ → E → E
  (tMin tMax : ℝ)
  t₀ : Icc t_min t_max 
  x₀ : E
  (c r l :  ℝ≥0 )
  lipschitz' : ∀ t _ : t ∈ Icc t_min t_max, LipschitzOnWith L (to_fun t) (closed_ball x₀ R)
  cont : ∀ x _ : x ∈ closed_ball x₀ R, ContinuousOn (fun t => to_fun t x) (Icc t_min t_max)
  norm_le' : ∀ t _ : t ∈ Icc t_min t_max x _ : x ∈ closed_ball x₀ R, ∥to_fun t x∥ ≤ C 
  C_mul_le_R : ((C : ℝ)*max (t_max - t₀) (t₀ - t_min)) ≤ R

namespace PicardLindelof

variable(v : PicardLindelof E)

instance  : CoeFun (PicardLindelof E) fun _ => ℝ → E → E :=
  ⟨to_fun⟩

instance  : Inhabited (PicardLindelof E) :=
  ⟨⟨0, 0, 0, ⟨0, le_rfl, le_rfl⟩, 0, 0, 0, 0, fun t ht => (LipschitzWith.const 0).LipschitzOnWith _,
      fun _ _ =>
        by 
          simpa only [Pi.zero_apply] using continuous_on_const,
      fun t ht x hx => norm_zero.le, (zero_mul _).le⟩⟩

theorem t_min_le_t_max : v.t_min ≤ v.t_max :=
  v.t₀.2.1.trans v.t₀.2.2

protected theorem nonempty_Icc : (Icc v.t_min v.t_max).Nonempty :=
  nonempty_Icc.2 v.t_min_le_t_max

protected theorem LipschitzOnWith {t} (ht : t ∈ Icc v.t_min v.t_max) :
  LipschitzOnWith v.L (v t) (closed_ball v.x₀ v.R) :=
  v.lipschitz' t ht

protected theorem ContinuousOn : ContinuousOn (uncurry v) ((Icc v.t_min v.t_max).Prod (closed_ball v.x₀ v.R)) :=
  have  : ContinuousOn (uncurry (flip v)) ((closed_ball v.x₀ v.R).Prod (Icc v.t_min v.t_max)) :=
    continuous_on_prod_of_continuous_on_lipschitz_on _ v.L v.cont v.lipschitz' 
  this.comp continuous_swap.ContinuousOn preimage_swap_prod.symm.Subset

theorem norm_le {t : ℝ} (ht : t ∈ Icc v.t_min v.t_max) {x : E} (hx : x ∈ closed_ball v.x₀ v.R) : ∥v t x∥ ≤ v.C :=
  v.norm_le' _ ht _ hx

/-- The maximum of distances from `t₀` to the endpoints of `[t_min, t_max]`. -/
def t_dist : ℝ :=
  max (v.t_max - v.t₀) (v.t₀ - v.t_min)

theorem t_dist_nonneg : 0 ≤ v.t_dist :=
  le_max_iff.2$ Or.inl$ sub_nonneg.2 v.t₀.2.2

theorem dist_t₀_le (t : Icc v.t_min v.t_max) : dist t v.t₀ ≤ v.t_dist :=
  by 
    rw [Subtype.dist_eq, Real.dist_eq]
    cases' le_totalₓ t v.t₀ with ht ht
    ·
      rw [abs_of_nonpos (sub_nonpos.2$ Subtype.coe_le_coe.2 ht), neg_sub]
      exact (sub_le_sub_left t.2.1 _).trans (le_max_rightₓ _ _)
    ·
      rw [abs_of_nonneg (sub_nonneg.2$ Subtype.coe_le_coe.2 ht)]
      exact (sub_le_sub_right t.2.2 _).trans (le_max_leftₓ _ _)

/-- Projection $ℝ → [t_{\min}, t_{\max}]$ sending $(-∞, t_{\min}]$ to $t_{\min}$ and $[t_{\max}, ∞)$
to $t_{\max}$. -/
def proj : ℝ → Icc v.t_min v.t_max :=
  proj_Icc v.t_min v.t_max v.t_min_le_t_max

theorem proj_coe (t : Icc v.t_min v.t_max) : v.proj t = t :=
  proj_Icc_coe _ _

theorem proj_of_mem {t : ℝ} (ht : t ∈ Icc v.t_min v.t_max) : «expr↑ » (v.proj t) = t :=
  by 
    simp only [proj, proj_Icc_of_mem _ ht, Subtype.coe_mk]

@[continuity]
theorem continuous_proj : Continuous v.proj :=
  continuous_proj_Icc

/-- The space of curves $γ \colon [t_{\min}, t_{\max}] \to E$ such that $γ(t₀) = x₀$ and $γ$ is
Lipschitz continuous with constant $C$. The map sending $γ$ to
$\mathbf Pγ(t)=x₀ + ∫_{t₀}^{t} v(τ, γ(τ))\,dτ$ is a contracting map on this space, and its fixed
point is a solution of the ODE $\dot x=v(t, x)$. -/
structure fun_space where 
  toFun : Icc v.t_min v.t_max → E 
  map_t₀' : to_fun v.t₀ = v.x₀ 
  lipschitz' : LipschitzWith v.C to_fun

namespace FunSpace

variable{v}(f : fun_space v)

instance  : CoeFun (fun_space v) fun _ => Icc v.t_min v.t_max → E :=
  ⟨to_fun⟩

instance  : Inhabited v.fun_space :=
  ⟨⟨fun _ => v.x₀, rfl, (LipschitzWith.const _).weaken (zero_le _)⟩⟩

protected theorem lipschitz : LipschitzWith v.C f :=
  f.lipschitz'

protected theorem Continuous : Continuous f :=
  f.lipschitz.continuous

/-- Each curve in `picard_lindelof.fun_space` is continuous. -/
def to_continuous_map : v.fun_space ↪ C(Icc v.t_min v.t_max, E) :=
  ⟨fun f => ⟨f, f.continuous⟩,
    fun f g h =>
      by 
        cases f 
        cases g 
        simpa using h⟩

instance  : MetricSpace v.fun_space :=
  MetricSpace.induced to_continuous_map to_continuous_map.Injective inferInstance

theorem uniform_inducing_to_continuous_map : UniformInducing (@to_continuous_map _ _ _ v) :=
  ⟨rfl⟩

theorem range_to_continuous_map :
  range to_continuous_map = { f:C(Icc v.t_min v.t_max, E) | f v.t₀ = v.x₀ ∧ LipschitzWith v.C f } :=
  by 
    ext f 
    split 
    ·
      rintro ⟨⟨f, hf₀, hf_lip⟩, rfl⟩
      exact ⟨hf₀, hf_lip⟩
    ·
      rcases f with ⟨f, hf⟩
      rintro ⟨hf₀, hf_lip⟩
      exact ⟨⟨f, hf₀, hf_lip⟩, rfl⟩

theorem map_t₀ : f v.t₀ = v.x₀ :=
  f.map_t₀'

protected theorem mem_closed_ball (t : Icc v.t_min v.t_max) : f t ∈ closed_ball v.x₀ v.R :=
  calc dist (f t) v.x₀ = dist (f t) (f.to_fun v.t₀) :=
    by 
      rw [f.map_t₀']
    _ ≤ v.C*dist t v.t₀ := f.lipschitz.dist_le_mul _ _ 
    _ ≤ v.C*v.t_dist := mul_le_mul_of_nonneg_left (v.dist_t₀_le _) v.C.2
    _ ≤ v.R := v.C_mul_le_R
    

/-- Given a curve $γ \colon [t_{\min}, t_{\max}] → E$, `v_comp` is the function
$F(t)=v(π t, γ(π t))$, where `π` is the projection $ℝ → [t_{\min}, t_{\max}]$. The integral of this
function is the image of `γ` under the contracting map we are going to define below. -/
def v_comp (t : ℝ) : E :=
  v (v.proj t) (f (v.proj t))

theorem v_comp_apply_coe (t : Icc v.t_min v.t_max) : f.v_comp t = v t (f t) :=
  by 
    simp only [v_comp, proj_coe]

-- error in Analysis.ODE.PicardLindelof: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_v_comp : continuous f.v_comp :=
begin
  have [] [] [":=", expr (continuous_subtype_coe.prod_mk f.continuous).comp v.continuous_proj],
  refine [expr continuous_on.comp_continuous v.continuous_on this (λ x, _)],
  exact [expr ⟨(v.proj x).2, f.mem_closed_ball _⟩]
end

theorem norm_v_comp_le (t : ℝ) : ∥f.v_comp t∥ ≤ v.C :=
  v.norm_le (v.proj t).2$ f.mem_closed_ball _

theorem dist_apply_le_dist (f₁ f₂ : fun_space v) (t : Icc v.t_min v.t_max) : dist (f₁ t) (f₂ t) ≤ dist f₁ f₂ :=
  @ContinuousMap.dist_apply_le_dist _ _ _ _ _ f₁.to_continuous_map f₂.to_continuous_map _

theorem dist_le_of_forall {f₁ f₂ : fun_space v} {d : ℝ} (h : ∀ t, dist (f₁ t) (f₂ t) ≤ d) : dist f₁ f₂ ≤ d :=
  (@ContinuousMap.dist_le_iff_of_nonempty _ _ _ _ _ f₁.to_continuous_map f₂.to_continuous_map _
        v.nonempty_Icc.to_subtype).2
    h

-- error in Analysis.ODE.PicardLindelof: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance [complete_space E] : complete_space v.fun_space :=
begin
  refine [expr (complete_space_iff_is_complete_range uniform_inducing_to_continuous_map).2 (is_closed.is_complete _)],
  rw ["[", expr range_to_continuous_map, ",", expr set_of_and, "]"] [],
  refine [expr (is_closed_eq (continuous_map.continuous_evalx _) continuous_const).inter _],
  have [] [":", expr is_closed {f : Icc v.t_min v.t_max → E | lipschitz_with v.C f}] [":=", expr is_closed_set_of_lipschitz_with v.C],
  exact [expr this.preimage continuous_map.continuous_coe]
end

variable[MeasurableSpace E][BorelSpace E]

theorem interval_integrable_v_comp (t₁ t₂ : ℝ) : IntervalIntegrable f.v_comp volume t₁ t₂ :=
  f.continuous_v_comp.IntervalIntegrable _ _

variable[second_countable_topology E][CompleteSpace E]

/-- The Picard-Lindelöf operator. This is a contracting map on `picard_lindelof.fun_space v` such
that the fixed point of this map is the solution of the corresponding ODE.

More precisely, some iteration of this map is a contracting map. -/
def next (f : fun_space v) : fun_space v :=
  { toFun := fun t => v.x₀+∫τ : ℝ in v.t₀..t, f.v_comp τ,
    map_t₀' :=
      by 
        rw [integral_same, add_zeroₓ],
    lipschitz' :=
      LipschitzWith.of_dist_le_mul$
        fun t₁ t₂ =>
          by 
            rw [dist_add_left, dist_eq_norm,
              integral_interval_sub_left (f.interval_integrable_v_comp _ _) (f.interval_integrable_v_comp _ _)]
            exact norm_integral_le_of_norm_le_const fun t ht => f.norm_v_comp_le _ }

theorem next_apply (t : Icc v.t_min v.t_max) : f.next t = v.x₀+∫τ : ℝ in v.t₀..t, f.v_comp τ :=
  rfl

-- error in Analysis.ODE.PicardLindelof: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_deriv_within_at_next
(t : Icc v.t_min v.t_max) : has_deriv_within_at «expr ∘ »(f.next, v.proj) (v t (f t)) (Icc v.t_min v.t_max) t :=
begin
  haveI [] [":", expr fact «expr ∈ »((t : exprℝ()), Icc v.t_min v.t_max)] [":=", expr ⟨t.2⟩],
  simp [] [] ["only"] ["[", expr («expr ∘ »), ",", expr next_apply, "]"] [] [],
  refine [expr has_deriv_within_at.const_add _ _],
  have [] [":", expr has_deriv_within_at (λ
    t : exprℝ(), «expr∫ in .. , »((τ), v.t₀, t, f.v_comp τ)) (f.v_comp t) (Icc v.t_min v.t_max) t] [],
  from [expr integral_has_deriv_within_at_right (f.interval_integrable_v_comp _ _) (f.continuous_v_comp.measurable_at_filter _ _) f.continuous_v_comp.continuous_within_at],
  rw [expr v_comp_apply_coe] ["at", ident this],
  refine [expr this.congr_of_eventually_eq_of_mem _ t.coe_prop],
  filter_upwards ["[", expr self_mem_nhds_within, "]"] [],
  intros [ident t', ident ht'],
  rw [expr v.proj_of_mem ht'] []
end

theorem dist_next_apply_le_of_le {f₁ f₂ : fun_space v} {n : ℕ} {d : ℝ}
  (h : ∀ t, dist (f₁ t) (f₂ t) ≤ (((v.L*|t - v.t₀|)^n) / n !)*d) (t : Icc v.t_min v.t_max) :
  dist (next f₁ t) (next f₂ t) ≤ (((v.L*|t - v.t₀|)^n+1) / (n+1)!)*d :=
  by 
    simp only [dist_eq_norm, next_apply, add_sub_add_left_eq_sub,
      ←intervalIntegral.integral_sub (interval_integrable_v_comp _ _ _) (interval_integrable_v_comp _ _ _),
      norm_integral_eq_norm_integral_Ioc] at *
    calc ∥∫τ in Ι (v.t₀ : ℝ) t, f₁.v_comp τ - f₂.v_comp τ∥ ≤ ∫τ in Ι (v.t₀ : ℝ) t, v.L*(((v.L*|τ - v.t₀|)^n) / n !)*d :=
      by 
        refine' norm_integral_le_of_norm_le (Continuous.integrable_on_interval_oc _) _
        ·
          continuity
        ·
          refine' (ae_restrict_mem measurable_set_Ioc).mono fun τ hτ => _ 
          refine'
            (v.lipschitz_on_with (v.proj τ).2).norm_sub_le_of_le (f₁.mem_closed_ball _) (f₂.mem_closed_ball _)
              ((h _).trans_eq _)
          rw [v.proj_of_mem]
          exact interval_subset_Icc v.t₀.2 t.2$ Ioc_subset_Icc_self hτ _ = (((v.L*|t - v.t₀|)^n+1) / (n+1)!)*d :=
      _ 
    simpRw [mul_powₓ, div_eq_mul_inv, mul_assocₓ, MeasureTheory.integral_mul_left, MeasureTheory.integral_mul_right,
      integral_pow_abs_sub_interval_oc, div_eq_mul_inv, pow_succₓ (v.L : ℝ), Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_succ, mul_inv₀, mul_assocₓ]

theorem dist_iterate_next_apply_le (f₁ f₂ : fun_space v) (n : ℕ) (t : Icc v.t_min v.t_max) :
  dist ((next^[n]) f₁ t) ((next^[n]) f₂ t) ≤ (((v.L*|t - v.t₀|)^n) / n !)*dist f₁ f₂ :=
  by 
    induction' n with n ihn generalizing t
    ·
      rw [pow_zeroₓ, Nat.factorial_zero, Nat.cast_one, div_one, one_mulₓ]
      exact dist_apply_le_dist f₁ f₂ t
    ·
      rw [iterate_succ_apply', iterate_succ_apply']
      exact dist_next_apply_le_of_le ihn _

-- error in Analysis.ODE.PicardLindelof: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dist_iterate_next_le
(f₁ f₂ : fun_space v)
(n : exprℕ()) : «expr ≤ »(dist («expr ^[ ]»(next, n) f₁) («expr ^[ ]»(next, n) f₂), «expr * »(«expr / »(«expr ^ »(«expr * »(v.L, v.t_dist), n), «expr !»(n)), dist f₁ f₂)) :=
begin
  refine [expr dist_le_of_forall (λ t, (dist_iterate_next_apply_le _ _ _ _).trans _)],
  have [] [":", expr «expr ≤ »(0, dist f₁ f₂)] [":=", expr dist_nonneg],
  have [] [":", expr «expr ≤ »(«expr| |»((«expr - »(t, v.t₀) : exprℝ())), v.t_dist)] [":=", expr v.dist_t₀_le t],
  mono ["*"] [] [] []; simp [] [] ["only"] ["[", expr nat.cast_nonneg, ",", expr mul_nonneg, ",", expr nnreal.coe_nonneg, ",", expr abs_nonneg, ",", "*", "]"] [] []
end

end FunSpace

variable[second_countable_topology E][CompleteSpace E]

section 

variable[MeasurableSpace E][BorelSpace E]

-- error in Analysis.ODE.PicardLindelof: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_contracting_iterate : «expr∃ , »((N : exprℕ())
 (K), contracting_with K «expr ^[ ]»((fun_space.next : v.fun_space → v.fun_space), N)) :=
begin
  rcases [expr ((real.tendsto_pow_div_factorial_at_top «expr * »(v.L, v.t_dist)).eventually (gt_mem_nhds zero_lt_one)).exists, "with", "⟨", ident N, ",", ident hN, "⟩"],
  have [] [":", expr «expr ≤ »((0 : exprℝ()), «expr / »(«expr ^ »(«expr * »(v.L, v.t_dist), N), «expr !»(N)))] [],
  from [expr div_nonneg (pow_nonneg (mul_nonneg v.L.2 v.t_dist_nonneg) _) (nat.cast_nonneg _)],
  exact [expr ⟨N, ⟨_, this⟩, hN, lipschitz_with.of_dist_le_mul (λ f g, fun_space.dist_iterate_next_le f g N)⟩]
end

theorem exists_fixed : ∃ f : v.fun_space, f.next = f :=
  let ⟨N, K, hK⟩ := exists_contracting_iterate v
  ⟨_, hK.is_fixed_pt_fixed_point_iterate⟩

end 

-- error in Analysis.ODE.PicardLindelof: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. -/
theorem exists_solution : «expr∃ , »((f : exprℝ() → E), «expr ∧ »(«expr = »(f v.t₀, v.x₀), ∀
  t «expr ∈ » Icc v.t_min v.t_max, has_deriv_within_at f (v t (f t)) (Icc v.t_min v.t_max) t)) :=
begin
  letI [] [":", expr measurable_space E] [":=", expr borel E],
  haveI [] [":", expr borel_space E] [":=", expr ⟨rfl⟩],
  rcases [expr v.exists_fixed, "with", "⟨", ident f, ",", ident hf, "⟩"],
  refine [expr ⟨«expr ∘ »(f, v.proj), _, λ t ht, _⟩],
  { simp [] [] ["only"] ["[", expr («expr ∘ »), ",", expr proj_coe, ",", expr f.map_t₀, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr («expr ∘ »), ",", expr v.proj_of_mem ht, "]"] [] [],
    lift [expr t] ["to", expr Icc v.t_min v.t_max] ["using", expr ht] [],
    simpa [] [] ["only"] ["[", expr hf, ",", expr v.proj_coe, "]"] [] ["using", expr f.has_deriv_within_at_next t] }
end

end PicardLindelof

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. -/
theorem exists_forall_deriv_within_Icc_eq_of_lipschitz_of_continuous [CompleteSpace E] [second_countable_topology E]
  {v : ℝ → E → E} {t_min t₀ t_max : ℝ} (ht₀ : t₀ ∈ Icc t_min t_max) (x₀ : E) {C R : ℝ} (hR : 0 ≤ R) {L :  ℝ≥0 }
  (Hlip : ∀ t _ : t ∈ Icc t_min t_max, LipschitzOnWith L (v t) (closed_ball x₀ R))
  (Hcont : ∀ x _ : x ∈ closed_ball x₀ R, ContinuousOn (fun t => v t x) (Icc t_min t_max))
  (Hnorm : ∀ t _ : t ∈ Icc t_min t_max x _ : x ∈ closed_ball x₀ R, ∥v t x∥ ≤ C)
  (Hmul_le : (C*max (t_max - t₀) (t₀ - t_min)) ≤ R) :
  ∃ f : ℝ → E, f t₀ = x₀ ∧ ∀ t _ : t ∈ Icc t_min t_max, HasDerivWithinAt f (v t (f t)) (Icc t_min t_max) t :=
  by 
    lift C to  ℝ≥0  using (norm_nonneg _).trans$ Hnorm t₀ ht₀ x₀ (mem_closed_ball_self hR)
    lift R to  ℝ≥0  using hR 
    lift t₀ to Icc t_min t_max using ht₀ 
    exact PicardLindelof.exists_solution ⟨v, t_min, t_max, t₀, x₀, C, R, L, Hlip, Hcont, Hnorm, Hmul_le⟩

