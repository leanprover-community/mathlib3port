import Mathbin.MeasureTheory.Measure.Lebesgue 
import Mathbin.MeasureTheory.Measure.Haar 
import Mathbin.LinearAlgebra.FiniteDimensional

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`, in
`measure_theory.add_haar_measure_eq_volume` and `measure_theory.add_haar_measure_eq_volume_pi`.

We deduce basic properties of any Haar measure on a finite dimensional real vector space:
* `map_linear_map_add_haar_eq_smul_add_haar`: a linear map rescales the Haar measure by the
  absolute value of its determinant.
* `add_haar_smul` : the measure of `r • s` is `|r| ^ dim * μ s`.
* `add_haar_ball`: the measure of `ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_closed_ball`: the measure of `closed_ball x r` is `r ^ dim * μ (ball 0 1)`.
* `add_haar_sphere`: spheres have zero measure.

-/


open TopologicalSpace Set Filter Metric

open_locale Ennreal Pointwise TopologicalSpace

/-- The interval `[0,1]` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.icc01 : positive_compacts ℝ :=
  ⟨Icc 0 1, is_compact_Icc,
    by 
      simpRw [interior_Icc, nonempty_Ioo, zero_lt_one]⟩

universe u

/-- The set `[0,1]^ι` as a compact set with non-empty interior. -/
def TopologicalSpace.PositiveCompacts.piIcc01 (ι : Type _) [Fintype ι] : positive_compacts (ι → ℝ) :=
  ⟨Set.Pi Set.Univ fun i => Icc 0 1, is_compact_univ_pi fun i => is_compact_Icc,
    by 
      simp only [interior_pi_set, finite.of_fintype, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo, implies_true_iff,
        zero_lt_one]⟩

namespace MeasureTheory

open Measureₓ TopologicalSpace.PositiveCompacts FiniteDimensional

/-!
### The Lebesgue measure is a Haar measure on `ℝ` and on `ℝ^ι`.
-/


theorem is_add_left_invariant_real_volume : is_add_left_invariant («expr⇑ » (volume : Measureₓ ℝ)) :=
  by 
    simp [←map_add_left_eq_self, Real.map_volume_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ`. -/
theorem add_haar_measure_eq_volume : add_haar_measure Icc01 = volume :=
  by 
    convert (add_haar_measure_unique _ Icc01).symm
    ·
      simp [Icc01]
    ·
      infer_instance
    ·
      exact is_add_left_invariant_real_volume

instance  : is_add_haar_measure (volume : Measureₓ ℝ) :=
  by 
    rw [←add_haar_measure_eq_volume]
    infer_instance

theorem is_add_left_invariant_real_volume_pi (ι : Type _) [Fintype ι] :
  is_add_left_invariant («expr⇑ » (volume : Measureₓ (ι → ℝ))) :=
  by 
    simp [←map_add_left_eq_self, Real.map_volume_pi_add_left]

/-- The Haar measure equals the Lebesgue measure on `ℝ^ι`. -/
theorem add_haar_measure_eq_volume_pi (ι : Type _) [Fintype ι] : add_haar_measure (pi_Icc01 ι) = volume :=
  by 
    convert (add_haar_measure_unique _ (pi_Icc01 ι)).symm
    ·
      simp only [pi_Icc01, volume_pi_pi fun i => Icc (0 : ℝ) 1, Finset.prod_const_one, Ennreal.of_real_one,
        Real.volume_Icc, one_smul, sub_zero]
    ·
      infer_instance
    ·
      exact is_add_left_invariant_real_volume_pi ι

instance is_add_haar_measure_volume_pi (ι : Type _) [Fintype ι] : is_add_haar_measure (volume : Measureₓ (ι → ℝ)) :=
  by 
    rw [←add_haar_measure_eq_volume_pi]
    infer_instance

namespace Measureₓ

/-!
### Applying a linear map rescales Haar measure by the determinant

We first prove this on `ι → ℝ`, using that this is already known for the product Lebesgue
measure (thanks to matrices computations). Then, we extend this to any finite-dimensional real
vector space by using a linear equiv with a space of the form `ι → ℝ`, and arguing that such a
linear equiv maps Haar measure to Haar measure.
-/


-- error in MeasureTheory.Measure.HaarLebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_linear_map_add_haar_pi_eq_smul_add_haar
{ι : Type*}
[fintype ι]
{f : «expr →ₗ[ ] »(ι → exprℝ(), exprℝ(), ι → exprℝ())}
(hf : «expr ≠ »(f.det, 0))
(μ : measure (ι → exprℝ()))
[is_add_haar_measure μ] : «expr = »(measure.map f μ, «expr • »(ennreal.of_real (abs «expr ⁻¹»(f.det)), μ)) :=
begin
  have [] [] [":=", expr add_haar_measure_unique (is_add_left_invariant_add_haar μ) (pi_Icc01 ι)],
  conv_lhs [] [] { rw [expr this] },
  conv_rhs [] [] { rw [expr this] },
  simp [] [] [] ["[", expr add_haar_measure_eq_volume_pi, ",", expr real.map_linear_map_volume_pi_eq_smul_volume_pi hf, ",", expr smul_smul, ",", expr mul_comm, "]"] [] []
end

-- error in MeasureTheory.Measure.HaarLebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_linear_map_add_haar_eq_smul_add_haar
{E : Type*}
[normed_group E]
[normed_space exprℝ() E]
[measurable_space E]
[borel_space E]
[finite_dimensional exprℝ() E]
(μ : measure E)
[is_add_haar_measure μ]
{f : «expr →ₗ[ ] »(E, exprℝ(), E)}
(hf : «expr ≠ »(f.det, 0)) : «expr = »(measure.map f μ, «expr • »(ennreal.of_real (abs «expr ⁻¹»(f.det)), μ)) :=
begin
  let [ident ι] [] [":=", expr fin (finrank exprℝ() E)],
  haveI [] [":", expr finite_dimensional exprℝ() (ι → exprℝ())] [":=", expr by apply_instance],
  have [] [":", expr «expr = »(finrank exprℝ() E, finrank exprℝ() (ι → exprℝ()))] [],
  by simp [] [] [] [] [] [],
  have [ident e] [":", expr «expr ≃ₗ[ ] »(E, exprℝ(), ι → exprℝ())] [":=", expr linear_equiv.of_finrank_eq E (ι → exprℝ()) this],
  obtain ["⟨", ident g, ",", ident hg, "⟩", ":", expr «expr∃ , »((g), «expr = »(g, (e : «expr →ₗ[ ] »(E, exprℝ(), ι → exprℝ())).comp (f.comp (e.symm : «expr →ₗ[ ] »(ι → exprℝ(), exprℝ(), E))))), ":=", expr ⟨_, rfl⟩],
  have [ident gdet] [":", expr «expr = »(g.det, f.det)] [],
  by { rw ["[", expr hg, "]"] [],
    exact [expr linear_map.det_conj f e] },
  rw ["<-", expr gdet] ["at", ident hf, "⊢"],
  have [ident fg] [":", expr «expr = »(f, (e.symm : «expr →ₗ[ ] »(ι → exprℝ(), exprℝ(), E)).comp (g.comp (e : «expr →ₗ[ ] »(E, exprℝ(), ι → exprℝ()))))] [],
  { ext [] [ident x] [],
    simp [] [] ["only"] ["[", expr linear_equiv.coe_coe, ",", expr function.comp_app, ",", expr linear_map.coe_comp, ",", expr linear_equiv.symm_apply_apply, ",", expr hg, "]"] [] [] },
  simp [] [] ["only"] ["[", expr fg, ",", expr linear_equiv.coe_coe, ",", expr linear_map.coe_comp, "]"] [] [],
  have [ident Ce] [":", expr continuous e] [":=", expr (e : «expr →ₗ[ ] »(E, exprℝ(), ι → exprℝ())).continuous_of_finite_dimensional],
  have [ident Cg] [":", expr continuous g] [":=", expr linear_map.continuous_of_finite_dimensional g],
  have [ident Cesymm] [":", expr continuous e.symm] [":=", expr (e.symm : «expr →ₗ[ ] »(ι → exprℝ(), exprℝ(), E)).continuous_of_finite_dimensional],
  rw ["[", "<-", expr map_map Cesymm.measurable (Cg.comp Ce).measurable, ",", "<-", expr map_map Cg.measurable Ce.measurable, "]"] [],
  haveI [] [":", expr is_add_haar_measure (map e μ)] [":=", expr is_add_haar_measure_map μ e.to_add_equiv Ce Cesymm],
  have [ident ecomp] [":", expr «expr = »(«expr ∘ »(e.symm, e), id)] [],
  by { ext [] [ident x] [],
    simp [] [] ["only"] ["[", expr id.def, ",", expr function.comp_app, ",", expr linear_equiv.symm_apply_apply, "]"] [] [] },
  rw ["[", expr map_linear_map_add_haar_pi_eq_smul_add_haar hf (map e μ), ",", expr linear_map.map_smul, ",", expr map_map Cesymm.measurable Ce.measurable, ",", expr ecomp, ",", expr measure.map_id, "]"] []
end

@[simp]
theorem haar_preimage_linear_map {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measureₓ E) [is_add_haar_measure μ] {f : E →ₗ[ℝ] E} (hf : f.det ≠ 0) (s : Set E) :
  μ (f ⁻¹' s) = Ennreal.ofReal (abs (f.det⁻¹))*μ s :=
  calc μ (f ⁻¹' s) = measure.map f μ s :=
    ((f.equiv_of_det_ne_zero hf).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.map_apply s).symm 
    _ = Ennreal.ofReal (abs (f.det⁻¹))*μ s :=
    by 
      rw [map_linear_map_add_haar_eq_smul_add_haar μ hf]
      rfl
    

/-!
### Basic properties of Haar measures on real vector spaces
-/


variable{E :
    Type
      _}[NormedGroup
      E][MeasurableSpace E][NormedSpace ℝ E][FiniteDimensional ℝ E][BorelSpace E](μ : Measureₓ E)[is_add_haar_measure μ]

-- error in MeasureTheory.Measure.HaarLebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_add_haar_smul
{r : exprℝ()}
(hr : «expr ≠ »(r, 0)) : «expr = »(measure.map (((«expr • »)) r) μ, «expr • »(ennreal.of_real (abs «expr ⁻¹»(«expr ^ »(r, finrank exprℝ() E))), μ)) :=
begin
  let [ident f] [":", expr «expr →ₗ[ ] »(E, exprℝ(), E)] [":=", expr «expr • »(r, 1)],
  change [expr «expr = »(measure.map f μ, _)] [] [],
  have [ident hf] [":", expr «expr ≠ »(f.det, 0)] [],
  { simp [] [] ["only"] ["[", expr mul_one, ",", expr linear_map.det_smul, ",", expr ne.def, ",", expr monoid_hom.map_one, "]"] [] [],
    assume [binders (h)],
    exact [expr hr (pow_eq_zero h)] },
  simp [] [] ["only"] ["[", expr map_linear_map_add_haar_eq_smul_add_haar μ hf, ",", expr mul_one, ",", expr linear_map.det_smul, ",", expr monoid_hom.map_one, "]"] [] []
end

theorem add_haar_preimage_smul {r : ℝ} (hr : r ≠ 0) (s : Set E) :
  μ ((· • ·) r ⁻¹' s) = Ennreal.ofReal (abs ((r^finrank ℝ E)⁻¹))*μ s :=
  calc μ ((· • ·) r ⁻¹' s) = measure.map ((· • ·) r) μ s :=
    ((Homeomorph.smul (is_unit_iff_ne_zero.2 hr).Unit).toMeasurableEquiv.map_apply s).symm 
    _ = Ennreal.ofReal (abs ((r^finrank ℝ E)⁻¹))*μ s :=
    by 
      rw [map_add_haar_smul μ hr]
      rfl
    

-- error in MeasureTheory.Measure.HaarLebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Rescaling a set by a factor `r` multiplies its measure by `abs (r ^ dim)`. -/
theorem add_haar_smul
(r : exprℝ())
(s : set E) : «expr = »(μ «expr • »(r, s), «expr * »(ennreal.of_real (abs «expr ^ »(r, finrank exprℝ() E)), μ s)) :=
begin
  rcases [expr ne_or_eq r 0, "with", ident h, "|", ident rfl],
  { rw ["[", "<-", expr preimage_smul_inv₀ h, ",", expr add_haar_preimage_smul μ (inv_ne_zero h), ",", expr inv_pow₀, ",", expr inv_inv₀, "]"] [] },
  rcases [expr eq_empty_or_nonempty s, "with", ident rfl, "|", ident hs],
  { simp [] [] ["only"] ["[", expr measure_empty, ",", expr mul_zero, ",", expr smul_set_empty, "]"] [] [] },
  rw ["[", expr zero_smul_set hs, ",", "<-", expr singleton_zero, "]"] [],
  by_cases [expr h, ":", expr «expr = »(finrank exprℝ() E, 0)],
  { haveI [] [":", expr subsingleton E] [":=", expr finrank_zero_iff.1 h],
    simp [] [] ["only"] ["[", expr h, ",", expr one_mul, ",", expr ennreal.of_real_one, ",", expr abs_one, ",", expr subsingleton.eq_univ_of_nonempty hs, ",", expr pow_zero, ",", expr subsingleton.eq_univ_of_nonempty (singleton_nonempty (0 : E)), "]"] [] [] },
  { haveI [] [":", expr nontrivial E] [":=", expr nontrivial_of_finrank_pos (bot_lt_iff_ne_bot.2 h)],
    simp [] [] ["only"] ["[", expr h, ",", expr zero_mul, ",", expr ennreal.of_real_zero, ",", expr abs_zero, ",", expr ne.def, ",", expr not_false_iff, ",", expr zero_pow', ",", expr measure_singleton, "]"] [] [] }
end

/-! We don't need to state `map_add_haar_neg` here, because it has already been proved for
general Haar measures on general commutative groups. -/


/-! ### Measure of balls -/


-- error in MeasureTheory.Measure.HaarLebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_haar_ball_center
{E : Type*}
[normed_group E]
[measurable_space E]
[borel_space E]
(μ : measure E)
[is_add_haar_measure μ]
(x : E)
(r : exprℝ()) : «expr = »(μ (ball x r), μ (ball (0 : E) r)) :=
begin
  have [] [":", expr «expr = »(ball (0 : E) r, «expr ⁻¹' »(((«expr + »)) x, ball x r))] [],
  by simp [] [] [] ["[", expr preimage_add_ball, "]"] [] [],
  rw ["[", expr this, ",", expr add_haar_preimage_add, "]"] []
end

-- error in MeasureTheory.Measure.HaarLebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_haar_closed_ball_center
{E : Type*}
[normed_group E]
[measurable_space E]
[borel_space E]
(μ : measure E)
[is_add_haar_measure μ]
(x : E)
(r : exprℝ()) : «expr = »(μ (closed_ball x r), μ (closed_ball (0 : E) r)) :=
begin
  have [] [":", expr «expr = »(closed_ball (0 : E) r, «expr ⁻¹' »(((«expr + »)) x, closed_ball x r))] [],
  by simp [] [] [] ["[", expr preimage_add_closed_ball, "]"] [] [],
  rw ["[", expr this, ",", expr add_haar_preimage_add, "]"] []
end

theorem add_haar_closed_ball_lt_top {E : Type _} [NormedGroup E] [ProperSpace E] [MeasurableSpace E] (μ : Measureₓ E)
  [is_add_haar_measure μ] (x : E) (r : ℝ) : μ (closed_ball x r) < ∞ :=
  (ProperSpace.is_compact_closed_ball x r).add_haar_lt_top μ

theorem add_haar_ball_lt_top {E : Type _} [NormedGroup E] [ProperSpace E] [MeasurableSpace E] (μ : Measureₓ E)
  [is_add_haar_measure μ] (x : E) (r : ℝ) : μ (ball x r) < ∞ :=
  lt_of_le_of_ltₓ (measure_mono ball_subset_closed_ball) (add_haar_closed_ball_lt_top μ x r)

theorem add_haar_ball_pos {E : Type _} [NormedGroup E] [MeasurableSpace E] (μ : Measureₓ E) [is_add_haar_measure μ]
  (x : E) {r : ℝ} (hr : 0 < r) : 0 < μ (ball x r) :=
  is_open_ball.add_haar_pos μ (nonempty_ball.2 hr)

theorem add_haar_closed_ball_pos {E : Type _} [NormedGroup E] [MeasurableSpace E] (μ : Measureₓ E)
  [is_add_haar_measure μ] (x : E) {r : ℝ} (hr : 0 < r) : 0 < μ (closed_ball x r) :=
  lt_of_lt_of_leₓ (add_haar_ball_pos μ x hr) (measure_mono ball_subset_closed_ball)

-- error in MeasureTheory.Measure.HaarLebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_haar_ball_of_pos
(x : E)
{r : exprℝ()}
(hr : «expr < »(0, r)) : «expr = »(μ (ball x r), «expr * »(ennreal.of_real «expr ^ »(r, finrank exprℝ() E), μ (ball 0 1))) :=
begin
  have [] [":", expr «expr = »(ball (0 : E) r, «expr • »(r, ball 0 1))] [],
  by simp [] [] [] ["[", expr smul_ball hr.ne' (0 : E) 1, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg hr.le, "]"] [] [],
  simp [] [] [] ["[", expr this, ",", expr add_haar_smul, ",", expr abs_of_nonneg hr.le, ",", expr add_haar_ball_center, "]"] [] []
end

theorem add_haar_ball [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) :
  μ (ball x r) = Ennreal.ofReal (r^finrank ℝ E)*μ (ball 0 1) :=
  by 
    rcases LE.le.eq_or_lt hr with (h | h)
    ·
      simp [←h, zero_pow finrank_pos]
    ·
      exact add_haar_ball_of_pos μ x h

-- error in MeasureTheory.Measure.HaarLebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The measure of a closed ball can be expressed in terms of the measure of the closed unit ball.
Use instead `add_haar_closed_ball`, which uses the measure of the open unit ball as a standard
form. -/
theorem add_haar_closed_ball'
(x : E)
{r : exprℝ()}
(hr : «expr ≤ »(0, r)) : «expr = »(μ (closed_ball x r), «expr * »(ennreal.of_real «expr ^ »(r, finrank exprℝ() E), μ (closed_ball 0 1))) :=
begin
  have [] [":", expr «expr = »(closed_ball (0 : E) r, «expr • »(r, closed_ball 0 1))] [],
  by simp [] [] [] ["[", expr smul_closed_ball r (0 : E) zero_le_one, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg hr, "]"] [] [],
  simp [] [] [] ["[", expr this, ",", expr add_haar_smul, ",", expr abs_of_nonneg hr, ",", expr add_haar_closed_ball_center, "]"] [] []
end

-- error in MeasureTheory.Measure.HaarLebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_haar_closed_unit_ball_eq_add_haar_unit_ball : «expr = »(μ (closed_ball (0 : E) 1), μ (ball 0 1)) :=
begin
  apply [expr le_antisymm _ (measure_mono ball_subset_closed_ball)],
  have [ident A] [":", expr tendsto (λ
    r : exprℝ(), «expr * »(ennreal.of_real «expr ^ »(r, finrank exprℝ() E), μ (closed_ball (0 : E) 1))) «expr𝓝[ ] »(Iio 1, 1) (expr𝓝() «expr * »(ennreal.of_real «expr ^ »(1, finrank exprℝ() E), μ (closed_ball (0 : E) 1)))] [],
  { refine [expr ennreal.tendsto.mul _ (by simp [] [] [] [] [] []) tendsto_const_nhds (by simp [] [] [] [] [] [])],
    exact [expr ennreal.tendsto_of_real ((tendsto_id' nhds_within_le_nhds).pow _)] },
  simp [] [] ["only"] ["[", expr one_pow, ",", expr one_mul, ",", expr ennreal.of_real_one, "]"] [] ["at", ident A],
  refine [expr le_of_tendsto A _],
  refine [expr mem_nhds_within_Iio_iff_exists_Ioo_subset.2 ⟨(0 : exprℝ()), by simp [] [] [] [] [] [], λ r hr, _⟩],
  dsimp [] [] [] [],
  rw ["<-", expr add_haar_closed_ball' μ (0 : E) hr.1.le] [],
  exact [expr measure_mono (closed_ball_subset_ball hr.2)]
end

theorem add_haar_closed_ball (x : E) {r : ℝ} (hr : 0 ≤ r) :
  μ (closed_ball x r) = Ennreal.ofReal (r^finrank ℝ E)*μ (ball 0 1) :=
  by 
    rw [add_haar_closed_ball' μ x hr, add_haar_closed_unit_ball_eq_add_haar_unit_ball]

theorem add_haar_sphere_of_ne_zero (x : E) {r : ℝ} (hr : r ≠ 0) : μ (sphere x r) = 0 :=
  by 
    rcases lt_trichotomyₓ r 0 with (h | rfl | h)
    ·
      simp only [empty_diff, measure_empty, ←closed_ball_diff_ball, closed_ball_eq_empty.2 h]
    ·
      exact (hr rfl).elim
    ·
      rw [←closed_ball_diff_ball,
        measure_diff ball_subset_closed_ball measurable_set_closed_ball measurable_set_ball
          (add_haar_ball_lt_top μ x r).Ne,
        add_haar_ball_of_pos μ _ h, add_haar_closed_ball μ _ h.le, tsub_self]

theorem add_haar_sphere [Nontrivial E] (x : E) (r : ℝ) : μ (sphere x r) = 0 :=
  by 
    rcases eq_or_ne r 0 with (rfl | h)
    ·
      simp only [←closed_ball_diff_ball, diff_empty, closed_ball_zero, ball_zero, measure_singleton]
    ·
      exact add_haar_sphere_of_ne_zero μ x h

end Measureₓ

end MeasureTheory

