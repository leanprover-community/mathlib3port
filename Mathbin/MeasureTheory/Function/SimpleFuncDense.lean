import Mathbin.MeasureTheory.Function.L1Space

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated pointwise, and each `Lᵖ` Borel
measurable function can be approximated in `Lᵖ` norm, by a sequence of simple functions.

## Main definitions

* `measure_theory.simple_func.nearest_pt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `simple_func` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `measure_theory.simple_func.approx_on (f : β → α) (hf : measurable f) (s : set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [separable_space s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`.
* `measure_theory.Lp.simple_func`, the type of `Lp` simple functions
* `coe_to_Lp`, the embedding of `Lp.simple_func E p μ` into `Lp E p μ`

## Main results

* `tendsto_approx_on` (pointwise convergence): If `f x ∈ s`, then the sequence of simple
  approximations `measure_theory.simple_func.approx_on f hf s y₀ h₀ n`, evaluated at `x`,
  tends to `f x` as `n` tends to `∞`.
* `tendsto_approx_on_univ_Lp` (Lᵖ convergence): If `E` is a `normed_group` and `f` is measurable
  and `mem_ℒp` (for `p < ∞`), then the simple functions `simple_func.approx_on f hf s 0 h₀ n` may
  be considered as elements of `Lp E p μ`, and they tend in Lᵖ to `f`.
* `Lp.simple_func.dense_embedding`: the embedding `coe_to_Lp` of the `Lp` simple functions into
  `Lp` is dense.
* `Lp.simple_func.induction`, `Lp.induction`, `mem_ℒp.induction`, `integrable.induction`: to prove
  a predicate for all elements of one of these classes of functions, it suffices to check that it
  behaves correctly on simple functions.

## TODO

For `E` finite-dimensional, simple functions `α →ₛ E` are dense in L^∞ -- prove this.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
* `α →₁ₛ[μ] E`: the type of `L1` simple functions `α → β`.
-/


open Set Function Filter TopologicalSpace Ennreal Emetric Finset

open_locale Classical TopologicalSpace Ennreal MeasureTheory BigOperators

variable{α β ι E F 𝕜 : Type _}

noncomputable theory

namespace MeasureTheory

local infixr:25 " →ₛ " => simple_func

namespace SimpleFunc

/-! ### Pointwise approximation by simple functions -/


section Pointwise

variable[MeasurableSpace α][EmetricSpace α][OpensMeasurableSpace α]

/-- `nearest_pt_ind e N x` is the index `k` such that `e k` is the nearest point to `x` among the
points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then
`nearest_pt_ind e N x` returns the least of their indexes. -/
noncomputable def nearest_pt_ind (e : ℕ → α) : ℕ → α →ₛ ℕ
| 0 => const α 0
| N+1 =>
  piecewise (⋂(k : _)(_ : k ≤ N), { x | edist (e (N+1)) x < edist (e k) x })
    (MeasurableSet.Inter$
      fun k => MeasurableSet.Inter_Prop$ fun hk => measurable_set_lt measurable_edist_right measurable_edist_right)
    (const α$ N+1) (nearest_pt_ind N)

/-- `nearest_pt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than
one point are at the same distance from `x`, then `nearest_pt e N x` returns the point with the
least possible index. -/
noncomputable def nearest_pt (e : ℕ → α) (N : ℕ) : α →ₛ α :=
  (nearest_pt_ind e N).map e

@[simp]
theorem nearest_pt_ind_zero (e : ℕ → α) : nearest_pt_ind e 0 = const α 0 :=
  rfl

@[simp]
theorem nearest_pt_zero (e : ℕ → α) : nearest_pt e 0 = const α (e 0) :=
  rfl

theorem nearest_pt_ind_succ (e : ℕ → α) (N : ℕ) (x : α) :
  nearest_pt_ind e (N+1) x = if ∀ k (_ : k ≤ N), edist (e (N+1)) x < edist (e k) x then N+1 else nearest_pt_ind e N x :=
  by 
    simp only [nearest_pt_ind, coe_piecewise, Set.piecewise]
    congr 
    simp 

theorem nearest_pt_ind_le (e : ℕ → α) (N : ℕ) (x : α) : nearest_pt_ind e N x ≤ N :=
  by 
    induction' N with N ihN
    ·
      simp 
    simp only [nearest_pt_ind_succ]
    splitIfs 
    exacts[le_rfl, ihN.trans N.le_succ]

theorem edist_nearest_pt_le (e : ℕ → α) (x : α) {k N : ℕ} (hk : k ≤ N) : edist (nearest_pt e N x) x ≤ edist (e k) x :=
  by 
    induction' N with N ihN generalizing k
    ·
      simp [nonpos_iff_eq_zero.1 hk, le_reflₓ]
    ·
      simp only [nearest_pt, nearest_pt_ind_succ, map_apply]
      splitIfs
      ·
        rcases hk.eq_or_lt with (rfl | hk)
        exacts[le_rfl, (h k (Nat.lt_succ_iff.1 hk)).le]
      ·
        pushNeg  at h 
        rcases h with ⟨l, hlN, hxl⟩
        rcases hk.eq_or_lt with (rfl | hk)
        exacts[(ihN hlN).trans hxl, ihN (Nat.lt_succ_iff.1 hk)]

theorem tendsto_nearest_pt {e : ℕ → α} {x : α} (hx : x ∈ Closure (range e)) :
  tendsto (fun N => nearest_pt e N x) at_top (𝓝 x) :=
  by 
    refine' (at_top_basis.tendsto_iff nhds_basis_eball).2 fun ε hε => _ 
    rcases Emetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩
    rw [edist_comm] at hN 
    exact ⟨N, trivialₓ, fun n hn => (edist_nearest_pt_le e x hn).trans_lt hN⟩

variable[MeasurableSpace β]{f : β → α}

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Approximate a measurable function by a sequence of simple functions `F n` such that
`F n x ∈ s`. -/
noncomputable
def approx_on
(f : β → α)
(hf : measurable f)
(s : set α)
(y₀ : α)
(h₀ : «expr ∈ »(y₀, s))
[separable_space s]
(n : exprℕ()) : «expr →ₛ »(β, α) :=
by haveI [] [":", expr nonempty s] [":=", expr ⟨⟨y₀, h₀⟩⟩]; exact [expr comp (nearest_pt (λ
  k, nat.cases_on k y₀ «expr ∘ »(coe, dense_seq s) : exprℕ() → α) n) f hf]

@[simp]
theorem approx_on_zero {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [separable_space s] (x : β) :
  approx_on f hf s y₀ h₀ 0 x = y₀ :=
  rfl

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem approx_on_mem
{f : β → α}
(hf : measurable f)
{s : set α}
{y₀ : α}
(h₀ : «expr ∈ »(y₀, s))
[separable_space s]
(n : exprℕ())
(x : β) : «expr ∈ »(approx_on f hf s y₀ h₀ n x, s) :=
begin
  haveI [] [":", expr nonempty s] [":=", expr ⟨⟨y₀, h₀⟩⟩],
  suffices [] [":", expr ∀ n, «expr ∈ »((nat.cases_on n y₀ «expr ∘ »(coe, dense_seq s) : α), s)],
  { apply [expr this] },
  rintro ["(", "_", "|", ident n, ")"],
  exacts ["[", expr h₀, ",", expr subtype.mem _, "]"]
end

@[simp]
theorem approx_on_comp {γ : Type _} [MeasurableSpace γ] {f : β → α} (hf : Measurable f) {g : γ → β} (hg : Measurable g)
  {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [separable_space s] (n : ℕ) :
  approx_on (f ∘ g) (hf.comp hg) s y₀ h₀ n = (approx_on f hf s y₀ h₀ n).comp g hg :=
  rfl

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_approx_on
{f : β → α}
(hf : measurable f)
{s : set α}
{y₀ : α}
(h₀ : «expr ∈ »(y₀, s))
[separable_space s]
{x : β}
(hx : «expr ∈ »(f x, closure s)) : tendsto (λ n, approx_on f hf s y₀ h₀ n x) at_top «expr $ »(expr𝓝(), f x) :=
begin
  haveI [] [":", expr nonempty s] [":=", expr ⟨⟨y₀, h₀⟩⟩],
  rw ["[", "<-", expr @subtype.range_coe _ s, ",", "<-", expr image_univ, ",", "<-", expr (dense_range_dense_seq s).closure_eq, "]"] ["at", ident hx],
  simp [] [] ["only"] ["[", expr approx_on, ",", expr coe_comp, "]"] [] [],
  refine [expr tendsto_nearest_pt (closure_minimal _ is_closed_closure hx)],
  simp [] [] ["only"] ["[", expr nat.range_cases_on, ",", expr closure_union, ",", expr range_comp coe, "]"] [] [],
  exact [expr subset.trans (image_closure_subset_closure_image continuous_subtype_coe) (subset_union_right _ _)]
end

theorem edist_approx_on_mono {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [separable_space s]
  (x : β) {m n : ℕ} (h : m ≤ n) : edist (approx_on f hf s y₀ h₀ n x) (f x) ≤ edist (approx_on f hf s y₀ h₀ m x) (f x) :=
  by 
    dsimp only [approx_on, coe_comp, · ∘ ·]
    exact edist_nearest_pt_le _ _ ((nearest_pt_ind_le _ _ _).trans h)

theorem edist_approx_on_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [separable_space s]
  (x : β) (n : ℕ) : edist (approx_on f hf s y₀ h₀ n x) (f x) ≤ edist y₀ (f x) :=
  edist_approx_on_mono hf h₀ x (zero_le n)

theorem edist_approx_on_y0_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [separable_space s]
  (x : β) (n : ℕ) : edist y₀ (approx_on f hf s y₀ h₀ n x) ≤ edist y₀ (f x)+edist y₀ (f x) :=
  calc edist y₀ (approx_on f hf s y₀ h₀ n x) ≤ edist y₀ (f x)+edist (approx_on f hf s y₀ h₀ n x) (f x) :=
    edist_triangle_right _ _ _ 
    _ ≤ edist y₀ (f x)+edist y₀ (f x) := add_le_add_left (edist_approx_on_le hf h₀ x n) _
    

end Pointwise

/-! ### Lp approximation by simple functions -/


section Lp

variable[MeasurableSpace β]

variable[MeasurableSpace E][NormedGroup E]{q : ℝ}{p : ℝ≥0∞}

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nnnorm_approx_on_le
[opens_measurable_space E]
{f : β → E}
(hf : measurable f)
{s : set E}
{y₀ : E}
(h₀ : «expr ∈ »(y₀, s))
[separable_space s]
(x : β)
(n : exprℕ()) : «expr ≤ »(«expr∥ ∥₊»(«expr - »(approx_on f hf s y₀ h₀ n x, f x)), «expr∥ ∥₊»(«expr - »(f x, y₀))) :=
begin
  have [] [] [":=", expr edist_approx_on_le hf h₀ x n],
  rw [expr edist_comm y₀] ["at", ident this],
  simp [] [] ["only"] ["[", expr edist_nndist, ",", expr nndist_eq_nnnorm, "]"] [] ["at", ident this],
  exact_mod_cast [expr this]
end

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_approx_on_y₀_le
[opens_measurable_space E]
{f : β → E}
(hf : measurable f)
{s : set E}
{y₀ : E}
(h₀ : «expr ∈ »(y₀, s))
[separable_space s]
(x : β)
(n : exprℕ()) : «expr ≤ »(«expr∥ ∥»(«expr - »(approx_on f hf s y₀ h₀ n x, y₀)), «expr + »(«expr∥ ∥»(«expr - »(f x, y₀)), «expr∥ ∥»(«expr - »(f x, y₀)))) :=
begin
  have [] [] [":=", expr edist_approx_on_y0_le hf h₀ x n],
  repeat { rw ["[", expr edist_comm y₀, ",", expr edist_eq_coe_nnnorm_sub, "]"] ["at", ident this] },
  exact_mod_cast [expr this]
end

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_approx_on_zero_le
[opens_measurable_space E]
{f : β → E}
(hf : measurable f)
{s : set E}
(h₀ : «expr ∈ »((0 : E), s))
[separable_space s]
(x : β)
(n : exprℕ()) : «expr ≤ »(«expr∥ ∥»(approx_on f hf s 0 h₀ n x), «expr + »(«expr∥ ∥»(f x), «expr∥ ∥»(f x))) :=
begin
  have [] [] [":=", expr edist_approx_on_y0_le hf h₀ x n],
  simp [] [] [] ["[", expr edist_comm (0 : E), ",", expr edist_eq_coe_nnnorm, "]"] [] ["at", ident this],
  exact_mod_cast [expr this]
end

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_approx_on_Lp_snorm
[opens_measurable_space E]
{f : β → E}
(hf : measurable f)
{s : set E}
{y₀ : E}
(h₀ : «expr ∈ »(y₀, s))
[separable_space s]
(hp_ne_top : «expr ≠ »(p, «expr∞»()))
{μ : measure β}
(hμ : «expr∀ᵐ ∂ , »((x), μ, «expr ∈ »(f x, closure s)))
(hi : «expr < »(snorm (λ
   x, «expr - »(f x, y₀)) p μ, «expr∞»())) : tendsto (λ
 n, snorm «expr - »(approx_on f hf s y₀ h₀ n, f) p μ) at_top (expr𝓝() 0) :=
begin
  by_cases [expr hp_zero, ":", expr «expr = »(p, 0)],
  { simpa [] [] ["only"] ["[", expr hp_zero, ",", expr snorm_exponent_zero, "]"] [] ["using", expr tendsto_const_nhds] },
  have [ident hp] [":", expr «expr < »(0, p.to_real)] [":=", expr to_real_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr hp_zero, hp_ne_top⟩],
  suffices [] [":", expr tendsto (λ
    n, «expr∫⁻ , ∂ »((x), «expr ^ »(«expr∥ ∥₊»(«expr - »(approx_on f hf s y₀ h₀ n x, f x)), p.to_real), μ)) at_top (expr𝓝() 0)],
  { simp [] [] ["only"] ["[", expr snorm_eq_lintegral_rpow_nnnorm hp_zero hp_ne_top, "]"] [] [],
    convert [] [expr continuous_rpow_const.continuous_at.tendsto.comp this] []; simp [] [] [] ["[", expr _root_.inv_pos.mpr hp, "]"] [] [] },
  have [ident hF_meas] [":", expr ∀
   n, measurable (λ
    x, «expr ^ »((«expr∥ ∥₊»(«expr - »(approx_on f hf s y₀ h₀ n x, f x)) : «exprℝ≥0∞»()), p.to_real))] [],
  { simpa [] [] ["only"] ["[", "<-", expr edist_eq_coe_nnnorm_sub, "]"] [] ["using", expr λ
     n, (approx_on f hf s y₀ h₀ n).measurable_bind (λ
      y x, «expr ^ »(edist y (f x), p.to_real)) (λ y, (measurable_edist_right.comp hf).pow_const p.to_real)] },
  have [ident h_bound] [":", expr ∀
   n, «expr ≤ᵐ[ ] »(λ
    x, «expr ^ »((«expr∥ ∥₊»(«expr - »(approx_on f hf s y₀ h₀ n x, f x)) : «exprℝ≥0∞»()), p.to_real), μ, λ
    x, «expr ^ »(«expr∥ ∥₊»(«expr - »(f x, y₀)), p.to_real))] [],
  { exact [expr λ
     n, eventually_of_forall (λ x, rpow_le_rpow (coe_mono (nnnorm_approx_on_le hf h₀ x n)) to_real_nonneg)] },
  have [ident h_fin] [":", expr «expr ≠ »(«expr∫⁻ , ∂ »((a : β), «expr ^ »(«expr∥ ∥₊»(«expr - »(f a, y₀)), p.to_real), μ), «expr⊤»())] [],
  from [expr (lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp_zero hp_ne_top hi).ne],
  have [ident h_lim] [":", expr «expr∀ᵐ ∂ , »((a : β), μ, tendsto (λ
     n, «expr ^ »((«expr∥ ∥₊»(«expr - »(approx_on f hf s y₀ h₀ n a, f a)) : «exprℝ≥0∞»()), p.to_real)) at_top (expr𝓝() 0))] [],
  { filter_upwards ["[", expr hμ, "]"] [],
    intros [ident a, ident ha],
    have [] [":", expr tendsto (λ
      n, «expr - »(approx_on f hf s y₀ h₀ n a, f a)) at_top (expr𝓝() «expr - »(f a, f a))] [],
    { exact [expr (tendsto_approx_on hf h₀ ha).sub tendsto_const_nhds] },
    convert [] [expr continuous_rpow_const.continuous_at.tendsto.comp (tendsto_coe.mpr this.nnnorm)] [],
    simp [] [] [] ["[", expr zero_rpow_of_pos hp, "]"] [] [] },
  simpa [] [] [] [] [] ["using", expr tendsto_lintegral_of_dominated_convergence _ hF_meas h_bound h_fin h_lim]
end

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_ℒp_approx_on
[borel_space E]
{f : β → E}
{μ : measure β}
(fmeas : measurable f)
(hf : mem_ℒp f p μ)
{s : set E}
{y₀ : E}
(h₀ : «expr ∈ »(y₀, s))
[separable_space s]
(hi₀ : mem_ℒp (λ x, y₀) p μ)
(n : exprℕ()) : mem_ℒp (approx_on f fmeas s y₀ h₀ n) p μ :=
begin
  refine [expr ⟨(approx_on f fmeas s y₀ h₀ n).ae_measurable, _⟩],
  suffices [] [":", expr «expr < »(snorm (λ x, «expr - »(approx_on f fmeas s y₀ h₀ n x, y₀)) p μ, «expr⊤»())],
  { have [] [":", expr mem_ℒp (λ
      x, «expr - »(approx_on f fmeas s y₀ h₀ n x, y₀)) p μ] [":=", expr ⟨«expr - »(approx_on f fmeas s y₀ h₀ n, const β y₀).ae_measurable, this⟩],
    convert [] [expr snorm_add_lt_top this hi₀] [],
    ext [] [ident x] [],
    simp [] [] [] [] [] [] },
  have [ident hf'] [":", expr mem_ℒp (λ x, «expr∥ ∥»(«expr - »(f x, y₀))) p μ] [],
  { have [ident h_meas] [":", expr measurable (λ x, «expr∥ ∥»(«expr - »(f x, y₀)))] [],
    { simp [] [] ["only"] ["[", "<-", expr dist_eq_norm, "]"] [] [],
      exact [expr (continuous_id.dist continuous_const).measurable.comp fmeas] },
    refine [expr ⟨h_meas.ae_measurable, _⟩],
    rw [expr snorm_norm] [],
    convert [] [expr snorm_add_lt_top hf hi₀.neg] [],
    ext [] [ident x] [],
    simp [] [] [] ["[", expr sub_eq_add_neg, "]"] [] [] },
  have [] [":", expr «expr∀ᵐ ∂ , »((x), μ, «expr ≤ »(«expr∥ ∥»(«expr - »(approx_on f fmeas s y₀ h₀ n x, y₀)), «expr∥ ∥»(«expr + »(«expr∥ ∥»(«expr - »(f x, y₀)), «expr∥ ∥»(«expr - »(f x, y₀))))))] [],
  { refine [expr eventually_of_forall _],
    intros [ident x],
    convert [] [expr norm_approx_on_y₀_le fmeas h₀ x n] [],
    rw ["[", expr real.norm_eq_abs, ",", expr abs_of_nonneg, "]"] [],
    exact [expr add_nonneg (norm_nonneg _) (norm_nonneg _)] },
  calc
    «expr ≤ »(snorm (λ
      x, «expr - »(approx_on f fmeas s y₀ h₀ n x, y₀)) p μ, snorm (λ
      x, «expr + »(«expr∥ ∥»(«expr - »(f x, y₀)), «expr∥ ∥»(«expr - »(f x, y₀)))) p μ) : snorm_mono_ae this
    «expr < »(..., «expr⊤»()) : snorm_add_lt_top hf' hf'
end

theorem tendsto_approx_on_univ_Lp_snorm [OpensMeasurableSpace E] [second_countable_topology E] {f : β → E}
  (hp_ne_top : p ≠ ∞) {μ : Measureₓ β} (fmeas : Measurable f) (hf : snorm f p μ < ∞) :
  tendsto (fun n => snorm (approx_on f fmeas univ 0 trivialₓ n - f) p μ) at_top (𝓝 0) :=
  tendsto_approx_on_Lp_snorm fmeas trivialₓ hp_ne_top
    (by 
      simp )
    (by 
      simpa using hf)

theorem mem_ℒp_approx_on_univ [BorelSpace E] [second_countable_topology E] {f : β → E} {μ : Measureₓ β}
  (fmeas : Measurable f) (hf : mem_ℒp f p μ) (n : ℕ) : mem_ℒp (approx_on f fmeas univ 0 trivialₓ n) p μ :=
  mem_ℒp_approx_on fmeas hf (mem_univ _) zero_mem_ℒp n

theorem tendsto_approx_on_univ_Lp [BorelSpace E] [second_countable_topology E] {f : β → E} [hp : Fact (1 ≤ p)]
  (hp_ne_top : p ≠ ∞) {μ : Measureₓ β} (fmeas : Measurable f) (hf : mem_ℒp f p μ) :
  tendsto (fun n => (mem_ℒp_approx_on_univ fmeas hf n).toLp (approx_on f fmeas univ 0 trivialₓ n)) at_top
    (𝓝 (hf.to_Lp f)) :=
  by 
    simp [Lp.tendsto_Lp_iff_tendsto_ℒp'', tendsto_approx_on_univ_Lp_snorm hp_ne_top fmeas hf.2]

end Lp

/-! ### L1 approximation by simple functions -/


section Integrable

variable[MeasurableSpace β]

variable[MeasurableSpace E][NormedGroup E]

theorem tendsto_approx_on_L1_nnnorm [OpensMeasurableSpace E] {f : β → E} (hf : Measurable f) {s : Set E} {y₀ : E}
  (h₀ : y₀ ∈ s) [separable_space s] {μ : Measureₓ β} (hμ : ∀ᵐx ∂μ, f x ∈ Closure s)
  (hi : has_finite_integral (fun x => f x - y₀) μ) :
  tendsto (fun n => ∫⁻x, ∥approx_on f hf s y₀ h₀ n x - f x∥₊ ∂μ) at_top (𝓝 0) :=
  by 
    simpa [snorm_one_eq_lintegral_nnnorm] using
      tendsto_approx_on_Lp_snorm hf h₀ one_ne_top hμ
        (by 
          simpa [snorm_one_eq_lintegral_nnnorm] using hi)

theorem integrable_approx_on [BorelSpace E] {f : β → E} {μ : Measureₓ β} (fmeas : Measurable f) (hf : integrable f μ)
  {s : Set E} {y₀ : E} (h₀ : y₀ ∈ s) [separable_space s] (hi₀ : integrable (fun x => y₀) μ) (n : ℕ) :
  integrable (approx_on f fmeas s y₀ h₀ n) μ :=
  by 
    rw [←mem_ℒp_one_iff_integrable] at hf hi₀⊢
    exact mem_ℒp_approx_on fmeas hf h₀ hi₀ n

theorem tendsto_approx_on_univ_L1_nnnorm [OpensMeasurableSpace E] [second_countable_topology E] {f : β → E}
  {μ : Measureₓ β} (fmeas : Measurable f) (hf : integrable f μ) :
  tendsto (fun n => ∫⁻x, ∥approx_on f fmeas univ 0 trivialₓ n x - f x∥₊ ∂μ) at_top (𝓝 0) :=
  tendsto_approx_on_L1_nnnorm fmeas trivialₓ
    (by 
      simp )
    (by 
      simpa using hf.2)

theorem integrable_approx_on_univ [BorelSpace E] [second_countable_topology E] {f : β → E} {μ : Measureₓ β}
  (fmeas : Measurable f) (hf : integrable f μ) (n : ℕ) : integrable (approx_on f fmeas univ 0 trivialₓ n) μ :=
  integrable_approx_on fmeas hf _ (integrable_zero _ _ _) n

end Integrable

section SimpleFuncProperties

variable[MeasurableSpace α]

variable[NormedGroup E][MeasurableSpace E][NormedGroup F]

variable{μ : Measureₓ α}{p : ℝ≥0∞}

/-!
### Properties of simple functions in `Lp` spaces

A simple function `f : α →ₛ E` into a normed group `E` verifies, for a measure `μ`:
- `mem_ℒp f 0 μ` and `mem_ℒp f ∞ μ`, since `f` is a.e.-measurable and bounded,
- for `0 < p < ∞`,
  `mem_ℒp f p μ ↔ integrable f μ ↔ f.fin_meas_supp μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞`.
-/


theorem exists_forall_norm_le (f : α →ₛ F) : ∃ C, ∀ x, ∥f x∥ ≤ C :=
  exists_forall_le (f.map fun x => ∥x∥)

theorem mem_ℒp_zero (f : α →ₛ E) (μ : Measureₓ α) : mem_ℒp f 0 μ :=
  mem_ℒp_zero_iff_ae_measurable.mpr f.ae_measurable

theorem mem_ℒp_top (f : α →ₛ E) (μ : Measureₓ α) : mem_ℒp f ∞ μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le 
  mem_ℒp_top_of_bound f.ae_measurable C$ eventually_of_forall hfC

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected
theorem snorm'_eq
{p : exprℝ()}
(f : «expr →ₛ »(α, F))
(μ : measure α) : «expr = »(snorm' f p μ, «expr ^ »(«expr∑ in , »((y), f.range, «expr * »(«expr ^ »((nnnorm y : «exprℝ≥0∞»()), p), μ «expr ⁻¹' »(f, {y}))), «expr / »(1, p))) :=
have h_map : «expr = »(λ
 a, «expr ^ »((nnnorm (f a) : «exprℝ≥0∞»()), p), f.map (λ
  a : F, «expr ^ »((nnnorm a : «exprℝ≥0∞»()), p))), by simp [] [] [] [] [] [],
by rw ["[", expr snorm', ",", expr h_map, ",", expr lintegral_eq_lintegral, ",", expr map_lintegral, "]"] []

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measure_preimage_lt_top_of_mem_ℒp
(hp_pos : «expr < »(0, p))
(hp_ne_top : «expr ≠ »(p, «expr∞»()))
(f : «expr →ₛ »(α, E))
(hf : mem_ℒp f p μ)
(y : E)
(hy_ne : «expr ≠ »(y, 0)) : «expr < »(μ «expr ⁻¹' »(f, {y}), «expr∞»()) :=
begin
  have [ident hp_pos_real] [":", expr «expr < »(0, p.to_real)] [],
  from [expr ennreal.to_real_pos_iff.mpr ⟨hp_pos, hp_ne_top⟩],
  have [ident hf_snorm] [] [":=", expr mem_ℒp.snorm_lt_top hf],
  rw ["[", expr snorm_eq_snorm' hp_pos.ne.symm hp_ne_top, ",", expr f.snorm'_eq, ",", "<-", expr @ennreal.lt_rpow_one_div_iff _ _ «expr / »(1, p.to_real) (by simp [] [] [] ["[", expr hp_pos_real, "]"] [] []), ",", expr @ennreal.top_rpow_of_pos «expr / »(1, «expr / »(1, p.to_real)) (by simp [] [] [] ["[", expr hp_pos_real, "]"] [] []), ",", expr ennreal.sum_lt_top_iff, "]"] ["at", ident hf_snorm],
  by_cases [expr hyf, ":", expr «expr ∈ »(y, f.range)],
  swap,
  { suffices [ident h_empty] [":", expr «expr = »(«expr ⁻¹' »(f, {y}), «expr∅»())],
    by { rw ["[", expr h_empty, ",", expr measure_empty, "]"] [],
      exact [expr ennreal.coe_lt_top] },
    ext1 [] [ident x],
    rw ["[", expr set.mem_preimage, ",", expr set.mem_singleton_iff, ",", expr mem_empty_eq, ",", expr iff_false, "]"] [],
    refine [expr λ hxy, hyf _],
    rw ["[", expr mem_range, ",", expr set.mem_range, "]"] [],
    exact [expr ⟨x, hxy⟩] },
  specialize [expr hf_snorm y hyf],
  rw [expr ennreal.mul_lt_top_iff] ["at", ident hf_snorm],
  cases [expr hf_snorm] [],
  { exact [expr hf_snorm.2] },
  cases [expr hf_snorm] [],
  { refine [expr absurd _ hy_ne],
    simpa [] [] [] ["[", expr hp_pos_real, "]"] [] ["using", expr hf_snorm] },
  { simp [] [] [] ["[", expr hf_snorm, "]"] [] [] }
end

theorem mem_ℒp_of_finite_measure_preimage (p : ℝ≥0∞) {f : α →ₛ E} (hf : ∀ y (_ : y ≠ 0), μ (f ⁻¹' {y}) < ∞) :
  mem_ℒp f p μ :=
  by 
    byCases' hp0 : p = 0
    ·
      rw [hp0, mem_ℒp_zero_iff_ae_measurable]
      exact f.ae_measurable 
    byCases' hp_top : p = ∞
    ·
      rw [hp_top]
      exact mem_ℒp_top f μ 
    refine' ⟨f.ae_measurable, _⟩
    rw [snorm_eq_snorm' hp0 hp_top, f.snorm'_eq]
    refine'
      Ennreal.rpow_lt_top_of_nonneg
        (by 
          simp )
        (ennreal.sum_lt_top_iff.mpr fun y hy => _).Ne 
    byCases' hy0 : y = 0
    ·
      simp [hy0, ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_neₓ (zero_le _) (Ne.symm hp0), hp_top⟩]
    ·
      refine' Ennreal.mul_lt_top _ (hf y hy0).Ne 
      exact (Ennreal.rpow_lt_top_of_nonneg Ennreal.to_real_nonneg Ennreal.coe_ne_top).Ne

theorem mem_ℒp_iff {f : α →ₛ E} (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  mem_ℒp f p μ ↔ ∀ y (_ : y ≠ 0), μ (f ⁻¹' {y}) < ∞ :=
  ⟨fun h => measure_preimage_lt_top_of_mem_ℒp hp_pos hp_ne_top f h, fun h => mem_ℒp_of_finite_measure_preimage p h⟩

theorem integrable_iff {f : α →ₛ E} : integrable f μ ↔ ∀ y (_ : y ≠ 0), μ (f ⁻¹' {y}) < ∞ :=
  mem_ℒp_one_iff_integrable.symm.trans$ mem_ℒp_iff Ennreal.zero_lt_one Ennreal.coe_ne_top

theorem mem_ℒp_iff_integrable {f : α →ₛ E} (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) : mem_ℒp f p μ ↔ integrable f μ :=
  (mem_ℒp_iff hp_pos hp_ne_top).trans integrable_iff.symm

theorem mem_ℒp_iff_fin_meas_supp {f : α →ₛ E} (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) : mem_ℒp f p μ ↔ f.fin_meas_supp μ :=
  (mem_ℒp_iff hp_pos hp_ne_top).trans fin_meas_supp_iff.symm

theorem integrable_iff_fin_meas_supp {f : α →ₛ E} : integrable f μ ↔ f.fin_meas_supp μ :=
  integrable_iff.trans fin_meas_supp_iff.symm

theorem fin_meas_supp.integrable {f : α →ₛ E} (h : f.fin_meas_supp μ) : integrable f μ :=
  integrable_iff_fin_meas_supp.2 h

theorem integrable_pair [MeasurableSpace F] {f : α →ₛ E} {g : α →ₛ F} :
  integrable f μ → integrable g μ → integrable (pair f g) μ :=
  by 
    simpa only [integrable_iff_fin_meas_supp] using fin_meas_supp.pair

theorem mem_ℒp_of_is_finite_measure (f : α →ₛ E) (p : ℝ≥0∞) (μ : Measureₓ α) [is_finite_measure μ] : mem_ℒp f p μ :=
  let ⟨C, hfC⟩ := f.exists_forall_norm_le 
  mem_ℒp.of_bound f.ae_measurable C$ eventually_of_forall hfC

theorem integrable_of_is_finite_measure [is_finite_measure μ] (f : α →ₛ E) : integrable f μ :=
  mem_ℒp_one_iff_integrable.mp (f.mem_ℒp_of_is_finite_measure 1 μ)

theorem measure_preimage_lt_top_of_integrable (f : α →ₛ E) (hf : integrable f μ) {x : E} (hx : x ≠ 0) :
  μ (f ⁻¹' {x}) < ∞ :=
  integrable_iff.mp hf x hx

theorem measure_support_lt_top [HasZero β] (f : α →ₛ β) (hf : ∀ y (_ : y ≠ 0), μ (f ⁻¹' {y}) < ∞) : μ (support f) < ∞ :=
  by 
    rw [support_eq]
    refine' (measure_bUnion_finset_le _ _).trans_lt (ennreal.sum_lt_top_iff.mpr fun y hy => _)
    rw [Finset.mem_filter] at hy 
    exact hf y hy.2

theorem measure_support_lt_top_of_mem_ℒp (f : α →ₛ E) (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  μ (support f) < ∞ :=
  f.measure_support_lt_top ((mem_ℒp_iff (pos_iff_ne_zero.mpr hp_ne_zero) hp_ne_top).mp hf)

theorem measure_support_lt_top_of_integrable (f : α →ₛ E) (hf : integrable f μ) : μ (support f) < ∞ :=
  f.measure_support_lt_top (integrable_iff.mp hf)

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem measure_lt_top_of_mem_ℒp_indicator
(hp_pos : «expr < »(0, p))
(hp_ne_top : «expr ≠ »(p, «expr∞»()))
{c : E}
(hc : «expr ≠ »(c, 0))
{s : set α}
(hs : measurable_set s)
(hcs : mem_ℒp ((const α c).piecewise s hs (const α 0)) p μ) : «expr < »(μ s, «expr⊤»()) :=
begin
  have [] [":", expr «expr = »(function.support (const α c), set.univ)] [":=", expr function.support_const hc],
  simpa [] [] ["only"] ["[", expr mem_ℒp_iff_fin_meas_supp hp_pos hp_ne_top, ",", expr fin_meas_supp_iff_support, ",", expr support_indicator, ",", expr set.inter_univ, ",", expr this, "]"] [] ["using", expr hcs]
end

end SimpleFuncProperties

end SimpleFunc

/-! Construction of the space of `Lp` simple functions, and its dense embedding into `Lp`. -/


namespace Lp

open AeEqFun

variable[MeasurableSpace
      α][NormedGroup
      E][second_countable_topology
      E][MeasurableSpace
      E][BorelSpace
      E][NormedGroup F][second_countable_topology F][MeasurableSpace F][BorelSpace F](p : ℝ≥0∞)(μ : Measureₓ α)

variable(E)

/-- `Lp.simple_func` is a subspace of Lp consisting of equivalence classes of an integrable simple
    function. -/
def simple_func : AddSubgroup (Lp E p μ) :=
  { Carrier := { f:Lp E p μ | ∃ s : α →ₛ E, (ae_eq_fun.mk s s.ae_measurable : α →ₘ[μ] E) = f }, zero_mem' := ⟨0, rfl⟩,
    add_mem' :=
      fun f g ⟨s, hs⟩ ⟨t, ht⟩ =>
        ⟨s+t,
          by 
            simp only [←hs, ←ht, mk_add_mk, AddSubgroup.coe_add, mk_eq_mk, simple_func.coe_add]⟩,
    neg_mem' :=
      fun f ⟨s, hs⟩ =>
        ⟨-s,
          by 
            simp only [←hs, neg_mk, simple_func.coe_neg, mk_eq_mk, AddSubgroup.coe_neg]⟩ }

variable{E p μ}

namespace SimpleFunc

section Instances

/-! Simple functions in Lp space form a `normed_space`. -/


@[normCast]
theorem coe_coe (f : Lp.simple_func E p μ) : «expr⇑ » (f : Lp E p μ) = f :=
  rfl

protected theorem eq' {f g : Lp.simple_func E p μ} : (f : α →ₘ[μ] E) = (g : α →ₘ[μ] E) → f = g :=
  Subtype.eq ∘ Subtype.eq

/-! Implementation note:  If `Lp.simple_func E p μ` were defined as a `𝕜`-submodule of `Lp E p μ`,
then the next few lemmas, putting a normed `𝕜`-group structure on `Lp.simple_func E p μ`, would be
unnecessary.  But instead, `Lp.simple_func E p μ` is defined as an `add_subgroup` of `Lp E p μ`,
which does not permit this (but has the advantage of working when `E` itself is a normed group,
i.e. has no scalar action). -/


variable[NormedField 𝕜][NormedSpace 𝕜 E][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

/-- If `E` is a normed space, `Lp.simple_func E p μ` is a `has_scalar`. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def HasScalar : HasScalar 𝕜 (Lp.simple_func E p μ) :=
  ⟨fun k f =>
      ⟨k • f,
        by 
          rcases f with ⟨f, ⟨s, hs⟩⟩
          use k • s 
          apply Eq.trans (smul_mk k s s.ae_measurable).symm _ 
          rw [hs]
          rfl⟩⟩

attribute [local instance] simple_func.has_scalar

@[simp, normCast]
theorem coe_smul (c : 𝕜) (f : Lp.simple_func E p μ) :
  ((c • f : Lp.simple_func E p μ) : Lp E p μ) = c • (f : Lp E p μ) :=
  rfl

/-- If `E` is a normed space, `Lp.simple_func E p μ` is a module. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def Module : Module 𝕜 (Lp.simple_func E p μ) :=
  { one_smul :=
      fun f =>
        by 
          ext1 
          exact one_smul _ _,
    mul_smul :=
      fun x y f =>
        by 
          ext1 
          exact mul_smul _ _ _,
    smul_add :=
      fun x f g =>
        by 
          ext1 
          exact smul_add _ _ _,
    smul_zero :=
      fun x =>
        by 
          ext1 
          exact smul_zero _,
    add_smul :=
      fun x y f =>
        by 
          ext1 
          exact add_smul _ _ _,
    zero_smul :=
      fun f =>
        by 
          ext1 
          exact zero_smul _ _ }

attribute [local instance] simple_func.module

/-- If `E` is a normed space, `Lp.simple_func E p μ` is a normed space. Not declared as an
instance as it is (as of writing) used only in the construction of the Bochner integral. -/
protected def NormedSpace [Fact (1 ≤ p)] : NormedSpace 𝕜 (Lp.simple_func E p μ) :=
  ⟨fun c f =>
      by 
        rw [coe_norm_subgroup, coe_norm_subgroup, coe_smul, norm_smul]⟩

end Instances

attribute [local instance] simple_func.module simple_func.normed_space

section ToLp

/-- Construct the equivalence class `[f]` of a simple function `f` satisfying `mem_ℒp`. -/
@[reducible]
def to_Lp (f : α →ₛ E) (hf : mem_ℒp f p μ) : Lp.simple_func E p μ :=
  ⟨hf.to_Lp f, ⟨f, rfl⟩⟩

theorem to_Lp_eq_to_Lp (f : α →ₛ E) (hf : mem_ℒp f p μ) : (to_Lp f hf : Lp E p μ) = hf.to_Lp f :=
  rfl

theorem to_Lp_eq_mk (f : α →ₛ E) (hf : mem_ℒp f p μ) : (to_Lp f hf : α →ₘ[μ] E) = ae_eq_fun.mk f f.ae_measurable :=
  rfl

theorem to_Lp_zero : to_Lp (0 : α →ₛ E) zero_mem_ℒp = (0 : Lp.simple_func E p μ) :=
  rfl

theorem to_Lp_add (f g : α →ₛ E) (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  to_Lp (f+g) (hf.add hg) = to_Lp f hf+to_Lp g hg :=
  rfl

theorem to_Lp_neg (f : α →ₛ E) (hf : mem_ℒp f p μ) : to_Lp (-f) hf.neg = -to_Lp f hf :=
  rfl

theorem to_Lp_sub (f g : α →ₛ E) (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  to_Lp (f - g) (hf.sub hg) = to_Lp f hf - to_Lp g hg :=
  by 
    simp only [sub_eq_add_neg, ←to_Lp_neg, ←to_Lp_add]
    rfl

variable[NormedField 𝕜][NormedSpace 𝕜 E][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

theorem to_Lp_smul (f : α →ₛ E) (hf : mem_ℒp f p μ) (c : 𝕜) : to_Lp (c • f) (hf.const_smul c) = c • to_Lp f hf :=
  rfl

theorem norm_to_Lp [Fact (1 ≤ p)] (f : α →ₛ E) (hf : mem_ℒp f p μ) : ∥to_Lp f hf∥ = Ennreal.toReal (snorm f p μ) :=
  norm_to_Lp f hf

end ToLp

section ToSimpleFunc

/-- Find a representative of a `Lp.simple_func`. -/
def to_simple_func (f : Lp.simple_func E p μ) : α →ₛ E :=
  Classical.some f.2

/-- `(to_simple_func f)` is measurable. -/
@[measurability]
protected theorem Measurable (f : Lp.simple_func E p μ) : Measurable (to_simple_func f) :=
  (to_simple_func f).Measurable

@[measurability]
protected theorem AeMeasurable (f : Lp.simple_func E p μ) : AeMeasurable (to_simple_func f) μ :=
  (simple_func.measurable f).AeMeasurable

theorem to_simple_func_eq_to_fun (f : Lp.simple_func E p μ) : to_simple_func f =ᵐ[μ] f :=
  show «expr⇑ » (to_simple_func f) =ᵐ[μ] «expr⇑ » (f : α →ₘ[μ] E)by 
    convert (ae_eq_fun.coe_fn_mk (to_simple_func f) (simple_func.ae_measurable f)).symm using 2 
    exact (Classical.some_spec f.2).symm

/-- `to_simple_func f` satisfies the predicate `mem_ℒp`. -/
protected theorem mem_ℒp (f : Lp.simple_func E p μ) : mem_ℒp (to_simple_func f) p μ :=
  mem_ℒp.ae_eq (to_simple_func_eq_to_fun f).symm$ mem_Lp_iff_mem_ℒp.mp (f : Lp E p μ).2

theorem to_Lp_to_simple_func (f : Lp.simple_func E p μ) : to_Lp (to_simple_func f) (simple_func.mem_ℒp f) = f :=
  simple_func.eq' (Classical.some_spec f.2)

theorem to_simple_func_to_Lp (f : α →ₛ E) (hfi : mem_ℒp f p μ) : to_simple_func (to_Lp f hfi) =ᵐ[μ] f :=
  by 
    rw [←mk_eq_mk]
    exact Classical.some_spec (to_Lp f hfi).2

variable(E μ)

theorem zero_to_simple_func : to_simple_func (0 : Lp.simple_func E p μ) =ᵐ[μ] 0 :=
  by 
    filterUpwards [to_simple_func_eq_to_fun (0 : Lp.simple_func E p μ), Lp.coe_fn_zero E 1 μ]
    intro a h₁ h₂ 
    rwa [h₁]

variable{E μ}

theorem add_to_simple_func (f g : Lp.simple_func E p μ) :
  to_simple_func (f+g) =ᵐ[μ] to_simple_func f+to_simple_func g :=
  by 
    filterUpwards [to_simple_func_eq_to_fun (f+g), to_simple_func_eq_to_fun f, to_simple_func_eq_to_fun g,
      Lp.coe_fn_add (f : Lp E p μ) g]
    intro a 
    simp only [←coe_coe, AddSubgroup.coe_add, Pi.add_apply]
    iterate 4
      intro h 
      rw [h]

theorem neg_to_simple_func (f : Lp.simple_func E p μ) : to_simple_func (-f) =ᵐ[μ] -to_simple_func f :=
  by 
    filterUpwards [to_simple_func_eq_to_fun (-f), to_simple_func_eq_to_fun f, Lp.coe_fn_neg (f : Lp E p μ)]
    intro a 
    simp only [Pi.neg_apply, AddSubgroup.coe_neg, ←coe_coe]
    repeat' 
      intro h 
      rw [h]

theorem sub_to_simple_func (f g : Lp.simple_func E p μ) :
  to_simple_func (f - g) =ᵐ[μ] to_simple_func f - to_simple_func g :=
  by 
    filterUpwards [to_simple_func_eq_to_fun (f - g), to_simple_func_eq_to_fun f, to_simple_func_eq_to_fun g,
      Lp.coe_fn_sub (f : Lp E p μ) g]
    intro a 
    simp only [AddSubgroup.coe_sub, Pi.sub_apply, ←coe_coe]
    repeat' 
      intro h 
      rw [h]

variable[NormedField 𝕜][NormedSpace 𝕜 E][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

theorem smul_to_simple_func (k : 𝕜) (f : Lp.simple_func E p μ) : to_simple_func (k • f) =ᵐ[μ] k • to_simple_func f :=
  by 
    filterUpwards [to_simple_func_eq_to_fun (k • f), to_simple_func_eq_to_fun f, Lp.coe_fn_smul k (f : Lp E p μ)]
    intro a 
    simp only [Pi.smul_apply, coe_smul, ←coe_coe]
    repeat' 
      intro h 
      rw [h]

theorem norm_to_simple_func [Fact (1 ≤ p)] (f : Lp.simple_func E p μ) :
  ∥f∥ = Ennreal.toReal (snorm (to_simple_func f) p μ) :=
  by 
    simpa [to_Lp_to_simple_func] using norm_to_Lp (to_simple_func f) (simple_func.mem_ℒp f)

end ToSimpleFunc

section Induction

variable(p)

/-- The characteristic function of a finite-measure measurable set `s`, as an `Lp` simple function.
-/
def indicator_const {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) : Lp.simple_func E p μ :=
  to_Lp ((simple_func.const _ c).piecewise s hs (simple_func.const _ 0)) (mem_ℒp_indicator_const p hs c (Or.inr hμs))

variable{p}

@[simp]
theorem coe_indicator_const {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
  («expr↑ » (indicator_const p hs hμs c) : Lp E p μ) = indicator_const_Lp p hs hμs c :=
  rfl

theorem to_simple_func_indicator_const {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
  to_simple_func (indicator_const p hs hμs c) =ᵐ[μ] (simple_func.const _ c).piecewise s hs (simple_func.const _ 0) :=
  Lp.simple_func.to_simple_func_to_Lp _ _

/-- To prove something for an arbitrary `Lp` simple function, with `0 < p < ∞`, it suffices to show
that the property holds for (multiples of) characteristic functions of finite-measure measurable
sets and is closed under addition (of functions with disjoint support). -/
@[elab_as_eliminator]
protected theorem induction (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) {P : Lp.simple_func E p μ → Prop}
  (h_ind :
    ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞), P (Lp.simple_func.indicator_const p hs hμs.ne c))
  (h_add :
    ∀ ⦃f g : α →ₛ E⦄,
      ∀ (hf : mem_ℒp f p μ),
        ∀ (hg : mem_ℒp g p μ),
          Disjoint (support f) (support g) →
            P (Lp.simple_func.to_Lp f hf) →
              P (Lp.simple_func.to_Lp g hg) → P (Lp.simple_func.to_Lp f hf+Lp.simple_func.to_Lp g hg))
  (f : Lp.simple_func E p μ) : P f :=
  by 
    suffices  : ∀ (f : α →ₛ E), ∀ (hf : mem_ℒp f p μ), P (to_Lp f hf)
    ·
      rw [←to_Lp_to_simple_func f]
      apply this 
    clear f 
    refine' simple_func.induction _ _
    ·
      intro c s hs hf 
      byCases' hc : c = 0
      ·
        convert
          h_ind 0 MeasurableSet.empty
            (by 
              simp ) using
          1 
        ext1 
        simp [hc]
      exact h_ind c hs (simple_func.measure_lt_top_of_mem_ℒp_indicator hp_pos hp_ne_top hc hs hf)
    ·
      intro f g hfg hf hg hfg' 
      obtain ⟨hf', hg'⟩ : mem_ℒp f p μ ∧ mem_ℒp g p μ
      ·
        exact (mem_ℒp_add_of_disjoint hfg f.measurable g.measurable).mp hfg' 
      exact h_add hf' hg' hfg (hf hf') (hg hg')

end Induction

section CoeToLp

variable[Fact (1 ≤ p)]

protected theorem UniformContinuous : UniformContinuous (coeₓ : Lp.simple_func E p μ → Lp E p μ) :=
  uniform_continuous_comap

protected theorem UniformEmbedding : UniformEmbedding (coeₓ : Lp.simple_func E p μ → Lp E p μ) :=
  uniform_embedding_comap Subtype.val_injective

protected theorem UniformInducing : UniformInducing (coeₓ : Lp.simple_func E p μ → Lp E p μ) :=
  simple_func.uniform_embedding.to_uniform_inducing

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem dense_embedding
(hp_ne_top : «expr ≠ »(p, «expr∞»())) : dense_embedding (coe : Lp.simple_func E p μ → Lp E p μ) :=
begin
  apply [expr simple_func.uniform_embedding.dense_embedding],
  assume [binders (f)],
  rw [expr mem_closure_iff_seq_limit] [],
  have [ident hfi'] [":", expr mem_ℒp f p μ] [":=", expr Lp.mem_ℒp f],
  refine [expr ⟨λ
    n, «expr↑ »(to_Lp (simple_func.approx_on f (Lp.measurable f) univ 0 trivial n) (simple_func.mem_ℒp_approx_on_univ (Lp.measurable f) hfi' n)), λ
    n, mem_range_self _, _⟩],
  convert [] [expr simple_func.tendsto_approx_on_univ_Lp hp_ne_top (Lp.measurable f) hfi'] [],
  rw [expr to_Lp_coe_fn f (Lp.mem_ℒp f)] []
end

protected theorem DenseInducing (hp_ne_top : p ≠ ∞) : DenseInducing (coeₓ : Lp.simple_func E p μ → Lp E p μ) :=
  (simple_func.dense_embedding hp_ne_top).to_dense_inducing

protected theorem DenseRange (hp_ne_top : p ≠ ∞) : DenseRange (coeₓ : Lp.simple_func E p μ → Lp E p μ) :=
  (simple_func.dense_inducing hp_ne_top).dense

variable[NormedField 𝕜][NormedSpace 𝕜 E][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

variable(α E 𝕜)

/-- The embedding of Lp simple functions into Lp functions, as a continuous linear map. -/
def coe_to_Lp : Lp.simple_func E p μ →L[𝕜] Lp E p μ :=
  { AddSubgroup.subtype (Lp.simple_func E p μ) with map_smul' := fun k f => rfl,
    cont := Lp.simple_func.uniform_continuous.Continuous }

variable{α E 𝕜}

end CoeToLp

end SimpleFunc

end Lp

variable[MeasurableSpace
      α][NormedGroup
      E][MeasurableSpace E][BorelSpace E][second_countable_topology E]{f : α → E}{p : ℝ≥0∞}{μ : Measureₓ α}

/-- To prove something for an arbitrary `Lp` function in a second countable Borel normed group, it
suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in `Lp` for which the property holds is closed.
-/
@[elab_as_eliminator]
theorem Lp.induction [_i : Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) (P : Lp E p μ → Prop)
  (h_ind :
    ∀ (c : E) {s : Set α} (hs : MeasurableSet s) (hμs : μ s < ∞), P (Lp.simple_func.indicator_const p hs hμs.ne c))
  (h_add :
    ∀ ⦃f g⦄,
      ∀ (hf : mem_ℒp f p μ),
        ∀ (hg : mem_ℒp g p μ),
          Disjoint (support f) (support g) → P (hf.to_Lp f) → P (hg.to_Lp g) → P (hf.to_Lp f+hg.to_Lp g))
  (h_closed : IsClosed { f:Lp E p μ | P f }) : ∀ (f : Lp E p μ), P f :=
  by 
    refine' fun f => (Lp.simple_func.dense_range hp_ne_top).induction_on f h_closed _ 
    refine' Lp.simple_func.induction (lt_of_lt_of_leₓ Ennreal.zero_lt_one _i.elim) hp_ne_top _ _
    ·
      exact fun c s => h_ind c
    ·
      exact fun f g hf hg => h_add hf hg

-- error in MeasureTheory.Function.SimpleFuncDense: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- To prove something for an arbitrary `mem_ℒp` function in a second countable
Borel normed group, it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `Lᵖ` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
@[elab_as_eliminator]
theorem mem_ℒp.induction
[_i : fact «expr ≤ »(1, p)]
(hp_ne_top : «expr ≠ »(p, «expr∞»()))
(P : (α → E) → exprProp())
(h_ind : ∀ (c : E) {{s}}, measurable_set s → «expr < »(μ s, «expr∞»()) → P (s.indicator (λ _, c)))
(h_add : ∀
 {{f g : α → E}}, disjoint (support f) (support g) → mem_ℒp f p μ → mem_ℒp g p μ → P f → P g → P «expr + »(f, g))
(h_closed : is_closed {f : Lp E p μ | P f})
(h_ae : ∀ {{f g}}, «expr =ᵐ[ ] »(f, μ, g) → mem_ℒp f p μ → P f → P g) : ∀ {{f : α → E}} (hf : mem_ℒp f p μ), P f :=
begin
  have [] [":", expr ∀ f : simple_func α E, mem_ℒp f p μ → P f] [],
  { refine [expr simple_func.induction _ _],
    { intros [ident c, ident s, ident hs, ident h],
      by_cases [expr hc, ":", expr «expr = »(c, 0)],
      { subst [expr hc],
        convert [] [expr h_ind 0 measurable_set.empty (by simp [] [] [] [] [] [])] ["using", 1],
        ext [] [] [],
        simp [] [] [] ["[", expr const, "]"] [] [] },
      have [ident hp_pos] [":", expr «expr < »(0, p)] [":=", expr lt_of_lt_of_le ennreal.zero_lt_one _i.elim],
      exact [expr h_ind c hs (simple_func.measure_lt_top_of_mem_ℒp_indicator hp_pos hp_ne_top hc hs h)] },
    { intros [ident f, ident g, ident hfg, ident hf, ident hg, ident int_fg],
      rw ["[", expr simple_func.coe_add, ",", expr mem_ℒp_add_of_disjoint hfg f.measurable g.measurable, "]"] ["at", ident int_fg],
      refine [expr h_add hfg int_fg.1 int_fg.2 (hf int_fg.1) (hg int_fg.2)] } },
  have [] [":", expr ∀ f : Lp.simple_func E p μ, P f] [],
  { intro [ident f],
    exact [expr h_ae (Lp.simple_func.to_simple_func_eq_to_fun f) (Lp.simple_func.mem_ℒp f) (this (Lp.simple_func.to_simple_func f) (Lp.simple_func.mem_ℒp f))] },
  have [] [":", expr ∀
   f : Lp E p μ, P f] [":=", expr λ f, (Lp.simple_func.dense_range hp_ne_top).induction_on f h_closed this],
  exact [expr λ f hf, h_ae hf.coe_fn_to_Lp (Lp.mem_ℒp _) (this (hf.to_Lp f))]
end

section Integrable

attribute [local instance] fact_one_le_one_ennreal

notation:25 α " →₁ₛ[" μ "] " E => @MeasureTheory.lp.simpleFunc α E _ _ _ _ _ 1 μ

theorem L1.simple_func.to_Lp_one_eq_to_L1 (f : α →ₛ E) (hf : integrable f μ) :
  (Lp.simple_func.to_Lp f (mem_ℒp_one_iff_integrable.2 hf) : α →₁[μ] E) = hf.to_L1 f :=
  rfl

protected theorem L1.simple_func.integrable (f : α →₁ₛ[μ] E) : integrable (Lp.simple_func.to_simple_func f) μ :=
  by 
    rw [←mem_ℒp_one_iff_integrable]
    exact Lp.simple_func.mem_ℒp f

/-- To prove something for an arbitrary integrable function in a second countable
Borel normed group, it suffices to show that
* the property holds for (multiples of) characteristic functions;
* is closed under addition;
* the set of functions in the `L¹` space for which the property holds is closed.
* the property is closed under the almost-everywhere equal relation.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`).
-/
@[elab_as_eliminator]
theorem integrable.induction (P : (α → E) → Prop)
  (h_ind : ∀ (c : E) ⦃s⦄, MeasurableSet s → μ s < ∞ → P (s.indicator fun _ => c))
  (h_add : ∀ ⦃f g : α → E⦄, Disjoint (support f) (support g) → integrable f μ → integrable g μ → P f → P g → P (f+g))
  (h_closed : IsClosed { f:α →₁[μ] E | P f }) (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → integrable f μ → P f → P g) :
  ∀ ⦃f : α → E⦄ (hf : integrable f μ), P f :=
  by 
    simp only [←mem_ℒp_one_iff_integrable] at *
    exact mem_ℒp.induction one_ne_top P h_ind h_add h_closed h_ae

end Integrable

end MeasureTheory

