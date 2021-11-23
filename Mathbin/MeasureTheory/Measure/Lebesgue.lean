import Mathbin.Dynamics.Ergodic.MeasurePreserving 
import Mathbin.LinearAlgebra.Determinant 
import Mathbin.LinearAlgebra.Matrix.Diagonal 
import Mathbin.LinearAlgebra.Matrix.Transvection 
import Mathbin.MeasureTheory.Constructions.Pi 
import Mathbin.MeasureTheory.Measure.Stieltjes

/-!
# Lebesgue measure on the real line and on `ℝⁿ`

We construct Lebesgue measure on the real line, as a particular case of Stieltjes measure associated
to the function `x ↦ x`. We obtain as a consequence Lebesgue measure on `ℝⁿ`. We prove that they
are translation invariant.

We show that, on `ℝⁿ`, a linear map acts on Lebesgue measure by rescaling it through the absolute
value of its determinant, in `real.map_linear_map_volume_pi_eq_smul_volume_pi`.

More properties of the Lebesgue measure are deduced from this in `haar_lebesgue.lean`, where they
are proved more generally for any additive Haar measure on a finite-dimensional real vector space.
-/


noncomputable theory

open Classical Set Filter MeasureTheory

open ennreal(ofReal)

open_locale BigOperators Ennreal Nnreal TopologicalSpace

/-!
### Definition of the Lebesgue measure and lengths of intervals
-/


/-- Lebesgue measure on the Borel sigma algebra, giving measure `b - a` to the interval `[a, b]`. -/
instance Real.measureSpace : measure_space ℝ :=
  ⟨StieltjesFunction.id.Measure⟩

namespace Real

variable{ι : Type _}[Fintype ι]

open_locale TopologicalSpace

theorem volume_val s : volume s = StieltjesFunction.id.Measure s :=
  rfl

@[simp]
theorem volume_Ico {a b : ℝ} : volume (Ico a b) = of_real (b - a) :=
  by 
    simp [volume_val]

@[simp]
theorem volume_Icc {a b : ℝ} : volume (Icc a b) = of_real (b - a) :=
  by 
    simp [volume_val]

@[simp]
theorem volume_Ioo {a b : ℝ} : volume (Ioo a b) = of_real (b - a) :=
  by 
    simp [volume_val]

@[simp]
theorem volume_Ioc {a b : ℝ} : volume (Ioc a b) = of_real (b - a) :=
  by 
    simp [volume_val]

@[simp]
theorem volume_singleton {a : ℝ} : volume ({a} : Set ℝ) = 0 :=
  by 
    simp [volume_val]

@[simp]
theorem volume_univ : volume (univ : Set ℝ) = ∞ :=
  Ennreal.eq_top_of_forall_nnreal_le$
    fun r =>
      calc (r : ℝ≥0∞) = volume (Icc (0 : ℝ) r) :=
        by 
          simp 
        _ ≤ volume univ := measure_mono (subset_univ _)
        

@[simp]
theorem volume_ball (a r : ℝ) : volume (Metric.Ball a r) = of_real (2*r) :=
  by 
    rw [ball_eq, volume_Ioo, ←sub_add, add_sub_cancel', two_mul]

@[simp]
theorem volume_closed_ball (a r : ℝ) : volume (Metric.ClosedBall a r) = of_real (2*r) :=
  by 
    rw [closed_ball_eq, volume_Icc, ←sub_add, add_sub_cancel', two_mul]

@[simp]
theorem volume_emetric_ball (a : ℝ) (r : ℝ≥0∞) : volume (Emetric.Ball a r) = 2*r :=
  by 
    rcases eq_or_ne r ∞ with (rfl | hr)
    ·
      rw [Metric.emetric_ball_top, volume_univ, two_mul, Ennreal.top_add]
    ·
      lift r to  ℝ≥0  using hr 
      rw [Metric.emetric_ball_nnreal, volume_ball, two_mul, ←Nnreal.coe_add, Ennreal.of_real_coe_nnreal,
        Ennreal.coe_add, two_mul]

@[simp]
theorem volume_emetric_closed_ball (a : ℝ) (r : ℝ≥0∞) : volume (Emetric.ClosedBall a r) = 2*r :=
  by 
    rcases eq_or_ne r ∞ with (rfl | hr)
    ·
      rw [Emetric.closed_ball_top, volume_univ, two_mul, Ennreal.top_add]
    ·
      lift r to  ℝ≥0  using hr 
      rw [Metric.emetric_closed_ball_nnreal, volume_closed_ball, two_mul, ←Nnreal.coe_add, Ennreal.of_real_coe_nnreal,
        Ennreal.coe_add, two_mul]

instance has_no_atoms_volume : has_no_atoms (volume : Measureₓ ℝ) :=
  ⟨fun x => volume_singleton⟩

@[simp]
theorem volume_interval {a b : ℝ} : volume (interval a b) = of_real |b - a| :=
  by 
    rw [interval, volume_Icc, max_sub_min_eq_abs]

@[simp]
theorem volume_Ioi {a : ℝ} : volume (Ioi a) = ∞ :=
  top_unique$
    le_of_tendsto' Ennreal.tendsto_nat_nhds_top$
      fun n =>
        calc (n : ℝ≥0∞) = volume (Ioo a (a+n)) :=
          by 
            simp 
          _ ≤ volume (Ioi a) := measure_mono Ioo_subset_Ioi_self
          

@[simp]
theorem volume_Ici {a : ℝ} : volume (Ici a) = ∞ :=
  by 
    simp [←measure_congr Ioi_ae_eq_Ici]

@[simp]
theorem volume_Iio {a : ℝ} : volume (Iio a) = ∞ :=
  top_unique$
    le_of_tendsto' Ennreal.tendsto_nat_nhds_top$
      fun n =>
        calc (n : ℝ≥0∞) = volume (Ioo (a - n) a) :=
          by 
            simp 
          _ ≤ volume (Iio a) := measure_mono Ioo_subset_Iio_self
          

@[simp]
theorem volume_Iic {a : ℝ} : volume (Iic a) = ∞ :=
  by 
    simp [←measure_congr Iio_ae_eq_Iic]

instance locally_finite_volume : is_locally_finite_measure (volume : Measureₓ ℝ) :=
  ⟨fun x =>
      ⟨Ioo (x - 1) (x+1), IsOpen.mem_nhds is_open_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩,
        by 
          simp only [Real.volume_Ioo, Ennreal.of_real_lt_top]⟩⟩

instance is_finite_measure_restrict_Icc (x y : ℝ) : is_finite_measure (volume.restrict (Icc x y)) :=
  ⟨by 
      simp ⟩

instance is_finite_measure_restrict_Ico (x y : ℝ) : is_finite_measure (volume.restrict (Ico x y)) :=
  ⟨by 
      simp ⟩

instance is_finite_measure_restrict_Ioc (x y : ℝ) : is_finite_measure (volume.restrict (Ioc x y)) :=
  ⟨by 
      simp ⟩

instance is_finite_measure_restrict_Ioo (x y : ℝ) : is_finite_measure (volume.restrict (Ioo x y)) :=
  ⟨by 
      simp ⟩

/-!
### Volume of a box in `ℝⁿ`
-/


theorem volume_Icc_pi {a b : ι → ℝ} : volume (Icc a b) = ∏i, Ennreal.ofReal (b i - a i) :=
  by 
    rw [←pi_univ_Icc, volume_pi_pi]
    simp only [Real.volume_Icc]

@[simp]
theorem volume_Icc_pi_to_real {a b : ι → ℝ} (h : a ≤ b) : (volume (Icc a b)).toReal = ∏i, b i - a i :=
  by 
    simp only [volume_Icc_pi, Ennreal.to_real_prod, Ennreal.to_real_of_real (sub_nonneg.2 (h _))]

theorem volume_pi_Ioo {a b : ι → ℝ} : volume (pi univ fun i => Ioo (a i) (b i)) = ∏i, Ennreal.ofReal (b i - a i) :=
  (measure_congr measure.univ_pi_Ioo_ae_eq_Icc).trans volume_Icc_pi

@[simp]
theorem volume_pi_Ioo_to_real {a b : ι → ℝ} (h : a ≤ b) :
  (volume (pi univ fun i => Ioo (a i) (b i))).toReal = ∏i, b i - a i :=
  by 
    simp only [volume_pi_Ioo, Ennreal.to_real_prod, Ennreal.to_real_of_real (sub_nonneg.2 (h _))]

theorem volume_pi_Ioc {a b : ι → ℝ} : volume (pi univ fun i => Ioc (a i) (b i)) = ∏i, Ennreal.ofReal (b i - a i) :=
  (measure_congr measure.univ_pi_Ioc_ae_eq_Icc).trans volume_Icc_pi

@[simp]
theorem volume_pi_Ioc_to_real {a b : ι → ℝ} (h : a ≤ b) :
  (volume (pi univ fun i => Ioc (a i) (b i))).toReal = ∏i, b i - a i :=
  by 
    simp only [volume_pi_Ioc, Ennreal.to_real_prod, Ennreal.to_real_of_real (sub_nonneg.2 (h _))]

theorem volume_pi_Ico {a b : ι → ℝ} : volume (pi univ fun i => Ico (a i) (b i)) = ∏i, Ennreal.ofReal (b i - a i) :=
  (measure_congr measure.univ_pi_Ico_ae_eq_Icc).trans volume_Icc_pi

@[simp]
theorem volume_pi_Ico_to_real {a b : ι → ℝ} (h : a ≤ b) :
  (volume (pi univ fun i => Ico (a i) (b i))).toReal = ∏i, b i - a i :=
  by 
    simp only [volume_pi_Ico, Ennreal.to_real_prod, Ennreal.to_real_of_real (sub_nonneg.2 (h _))]

@[simp]
theorem volume_pi_ball (a : ι → ℝ) {r : ℝ} (hr : 0 < r) :
  volume (Metric.Ball a r) = Ennreal.ofReal ((2*r)^Fintype.card ι) :=
  by 
    simp only [volume_pi_ball a hr, volume_ball, Finset.prod_const]
    exact (Ennreal.of_real_pow (mul_nonneg zero_le_two hr.le) _).symm

@[simp]
theorem volume_pi_closed_ball (a : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
  volume (Metric.ClosedBall a r) = Ennreal.ofReal ((2*r)^Fintype.card ι) :=
  by 
    simp only [volume_pi_closed_ball a hr, volume_closed_ball, Finset.prod_const]
    exact (Ennreal.of_real_pow (mul_nonneg zero_le_two hr) _).symm

theorem volume_le_diam (s : Set ℝ) : volume s ≤ Emetric.diam s :=
  by 
    byCases' hs : Metric.Bounded s
    ·
      rw [Real.ediam_eq hs, ←volume_Icc]
      exact volume.mono (Real.subset_Icc_Inf_Sup_of_bounded hs)
    ·
      rw [Metric.ediam_of_unbounded hs]
      exact le_top

theorem volume_pi_le_prod_diam (s : Set (ι → ℝ)) : volume s ≤ ∏i : ι, Emetric.diam (Function.eval i '' s) :=
  calc volume s ≤ volume (pi univ fun i => Closure (Function.eval i '' s)) :=
    volume.mono$ subset.trans (subset_pi_eval_image univ s)$ pi_mono$ fun i hi => subset_closure 
    _ = ∏i, volume (Closure$ Function.eval i '' s) := volume_pi_pi _ 
    _ ≤ ∏i : ι, Emetric.diam (Function.eval i '' s) :=
    Finset.prod_le_prod'$ fun i hi => (volume_le_diam _).trans_eq (Emetric.diam_closure _)
    

theorem volume_pi_le_diam_pow (s : Set (ι → ℝ)) : volume s ≤ (Emetric.diam s^Fintype.card ι) :=
  calc volume s ≤ ∏i : ι, Emetric.diam (Function.eval i '' s) := volume_pi_le_prod_diam s 
    _ ≤ ∏i : ι, (1 :  ℝ≥0 )*Emetric.diam s := Finset.prod_le_prod'$ fun i hi => (LipschitzWith.eval i).ediam_image_le s 
    _ = (Emetric.diam s^Fintype.card ι) :=
    by 
      simp only [Ennreal.coe_one, one_mulₓ, Finset.prod_const, Fintype.card]
    

/-!
### Images of the Lebesgue measure under translation/multiplication in ℝ
-/


theorem map_volume_add_left (a : ℝ) : measure.map ((·+·) a) volume = volume :=
  Eq.symm$
    Real.measure_ext_Ioo_rat$
      fun p q =>
        by 
          simp [measure.map_apply (measurable_const_add a) measurable_set_Ioo, sub_sub_sub_cancel_right]

@[simp]
theorem volume_preimage_add_left (a : ℝ) (s : Set ℝ) : volume ((·+·) a ⁻¹' s) = volume s :=
  calc volume ((·+·) a ⁻¹' s) = measure.map ((·+·) a) volume s :=
    ((Homeomorph.addLeft a).toMeasurableEquiv.map_apply s).symm 
    _ = volume s :=
    by 
      rw [map_volume_add_left]
    

theorem map_volume_add_right (a : ℝ) : measure.map (·+a) volume = volume :=
  by 
    simpa only [add_commₓ] using Real.map_volume_add_left a

@[simp]
theorem volume_preimage_add_right (a : ℝ) (s : Set ℝ) : volume ((·+a) ⁻¹' s) = volume s :=
  calc volume ((·+a) ⁻¹' s) = measure.map (·+a) volume s :=
    ((Homeomorph.addRight a).toMeasurableEquiv.map_apply s).symm 
    _ = volume s :=
    by 
      rw [map_volume_add_right]
    

theorem smul_map_volume_mul_left {a : ℝ} (h : a ≠ 0) : Ennreal.ofReal |a| • measure.map ((·*·) a) volume = volume :=
  by 
    refine' (Real.measure_ext_Ioo_rat$ fun p q => _).symm 
    cases' lt_or_gt_of_neₓ h with h h
    ·
      simp only [Real.volume_Ioo, measure.smul_apply, ←Ennreal.of_real_mul (le_of_ltₓ$ neg_pos.2 h),
        measure.map_apply (measurable_const_mul a) measurable_set_Ioo, neg_sub_neg, ←neg_mul_eq_neg_mul,
        preimage_const_mul_Ioo_of_neg _ _ h, abs_of_neg h, mul_sub, mul_div_cancel' _ (ne_of_ltₓ h)]
    ·
      simp only [Real.volume_Ioo, measure.smul_apply, ←Ennreal.of_real_mul (le_of_ltₓ h),
        measure.map_apply (measurable_const_mul a) measurable_set_Ioo, preimage_const_mul_Ioo _ _ h, abs_of_pos h,
        mul_sub, mul_div_cancel' _ (ne_of_gtₓ h)]

theorem map_volume_mul_left {a : ℝ} (h : a ≠ 0) : measure.map ((·*·) a) volume = Ennreal.ofReal |a⁻¹| • volume :=
  by 
    convRHS =>
      rw [←Real.smul_map_volume_mul_left h, smul_smul, ←Ennreal.of_real_mul (abs_nonneg _), ←abs_mul, inv_mul_cancel h,
        abs_one, Ennreal.of_real_one, one_smul]

@[simp]
theorem volume_preimage_mul_left {a : ℝ} (h : a ≠ 0) (s : Set ℝ) :
  volume ((·*·) a ⁻¹' s) = Ennreal.ofReal (abs (a⁻¹))*volume s :=
  calc volume ((·*·) a ⁻¹' s) = measure.map ((·*·) a) volume s :=
    ((Homeomorph.mulLeft₀ a h).toMeasurableEquiv.map_apply s).symm 
    _ = Ennreal.ofReal (abs (a⁻¹))*volume s :=
    by 
      rw [map_volume_mul_left h]
      rfl
    

theorem smul_map_volume_mul_right {a : ℝ} (h : a ≠ 0) : Ennreal.ofReal |a| • measure.map (·*a) volume = volume :=
  by 
    simpa only [mul_commₓ] using Real.smul_map_volume_mul_left h

theorem map_volume_mul_right {a : ℝ} (h : a ≠ 0) : measure.map (·*a) volume = Ennreal.ofReal |a⁻¹| • volume :=
  by 
    simpa only [mul_commₓ] using Real.map_volume_mul_left h

@[simp]
theorem volume_preimage_mul_right {a : ℝ} (h : a ≠ 0) (s : Set ℝ) :
  volume ((·*a) ⁻¹' s) = Ennreal.ofReal (abs (a⁻¹))*volume s :=
  calc volume ((·*a) ⁻¹' s) = measure.map (·*a) volume s :=
    ((Homeomorph.mulRight₀ a h).toMeasurableEquiv.map_apply s).symm 
    _ = Ennreal.ofReal (abs (a⁻¹))*volume s :=
    by 
      rw [map_volume_mul_right h]
      rfl
    

@[simp]
theorem map_volume_neg : measure.map Neg.neg (volume : Measureₓ ℝ) = volume :=
  Eq.symm$
    Real.measure_ext_Ioo_rat$
      fun p q =>
        by 
          simp
            [show measure.map Neg.neg volume (Ioo (p : ℝ) q) = _ from
              measure.map_apply measurable_neg measurable_set_Ioo]

/-!
### Images of the Lebesgue measure under translation/linear maps in ℝⁿ
-/


-- error in MeasureTheory.Measure.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_volume_pi_add_left (a : ι → exprℝ()) : «expr = »(measure.map (((«expr + »)) a) volume, volume) :=
begin
  refine [expr (measure.pi_eq (λ s hs, _)).symm],
  have [ident A] [":", expr «expr = »(«expr ⁻¹' »(has_add.add a, set.pi univ (λ
      i : ι, s i)), set.pi univ (λ i : ι, «expr ⁻¹' »(((«expr + »)) (a i), s i)))] [],
  by { ext [] [] [],
    simp [] [] [] [] [] [] },
  rw ["[", expr measure.map_apply (measurable_const_add a) (measurable_set.univ_pi_fintype hs), ",", expr A, ",", expr volume_pi_pi, "]"] [],
  simp [] [] ["only"] ["[", expr volume_preimage_add_left, "]"] [] []
end

@[simp]
theorem volume_pi_preimage_add_left (a : ι → ℝ) (s : Set (ι → ℝ)) : volume ((·+·) a ⁻¹' s) = volume s :=
  calc volume ((·+·) a ⁻¹' s) = measure.map ((·+·) a) volume s :=
    ((Homeomorph.addLeft a).toMeasurableEquiv.map_apply s).symm 
    _ = volume s :=
    by 
      rw [map_volume_pi_add_left]
    

open Matrix

-- error in MeasureTheory.Measure.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A diagonal matrix rescales Lebesgue according to its determinant. This is a special case of
`real.map_matrix_volume_pi_eq_smul_volume_pi`, that one should use instead (and whose proof
uses this particular case). -/
theorem smul_map_diagonal_volume_pi
[decidable_eq ι]
{D : ι → exprℝ()}
(h : «expr ≠ »(det (diagonal D), 0)) : «expr = »(«expr • »(ennreal.of_real (abs (det (diagonal D))), measure.map (diagonal D).to_lin' volume), volume) :=
begin
  refine [expr (measure.pi_eq (λ s hs, _)).symm],
  simp [] [] ["only"] ["[", expr det_diagonal, ",", expr measure.coe_smul, ",", expr algebra.id.smul_eq_mul, ",", expr pi.smul_apply, "]"] [] [],
  rw ["[", expr measure.map_apply _ (measurable_set.univ_pi_fintype hs), "]"] [],
  swap,
  { exact [expr continuous.measurable (linear_map.continuous_on_pi _)] },
  have [] [":", expr «expr = »(«expr ⁻¹' »(matrix.to_lin' (diagonal D), set.pi set.univ (λ
      i : ι, s i)), set.pi set.univ (λ i : ι, «expr ⁻¹' »(((«expr * »)) (D i), s i)))] [],
  { ext [] [ident f] [],
    simp [] [] ["only"] ["[", expr linear_map.coe_proj, ",", expr algebra.id.smul_eq_mul, ",", expr linear_map.smul_apply, ",", expr mem_univ_pi, ",", expr mem_preimage, ",", expr linear_map.pi_apply, ",", expr diagonal_to_lin', "]"] [] [] },
  have [ident B] [":", expr ∀
   i, «expr = »(«expr * »(of_real (abs (D i)), volume «expr ⁻¹' »(has_mul.mul (D i), s i)), volume (s i))] [],
  { assume [binders (i)],
    have [ident A] [":", expr «expr ≠ »(D i, 0)] [],
    { simp [] [] ["only"] ["[", expr det_diagonal, ",", expr ne.def, "]"] [] ["at", ident h],
      exact [expr finset.prod_ne_zero_iff.1 h i (finset.mem_univ i)] },
    rw ["[", expr volume_preimage_mul_left A, ",", "<-", expr mul_assoc, ",", "<-", expr ennreal.of_real_mul (abs_nonneg _), ",", "<-", expr abs_mul, ",", expr mul_inv_cancel A, ",", expr abs_one, ",", expr ennreal.of_real_one, ",", expr one_mul, "]"] [] },
  rw ["[", expr this, ",", expr volume_pi_pi, ",", expr finset.abs_prod, ",", expr ennreal.of_real_prod_of_nonneg (λ
    i hi, abs_nonneg (D i)), ",", "<-", expr finset.prod_mul_distrib, "]"] [],
  simp [] [] ["only"] ["[", expr B, "]"] [] []
end

-- error in MeasureTheory.Measure.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A transvection preserves Lebesgue measure. -/
theorem map_transvection_volume_pi
[decidable_eq ι]
(t : transvection_struct ι exprℝ()) : «expr = »(measure.map t.to_matrix.to_lin' volume, volume) :=
begin
  suffices [ident H] [":", expr measure_preserving t.to_matrix.to_lin' volume volume],
  by exact [expr H.2],
  let [ident p] [":", expr ι → exprProp()] [":=", expr λ i, «expr ≠ »(i, t.i)],
  let [ident α] [":", expr Type*] [":=", expr {x // p x}],
  let [ident β] [":", expr Type*] [":=", expr {x // «expr¬ »(p x)}],
  let [ident g] [":", expr (α → exprℝ()) → (β → exprℝ()) → β → exprℝ()] [":=", expr λ
   a b, «expr + »(λ x, «expr * »(t.c, a ⟨t.j, t.hij.symm⟩), b)],
  let [ident F] [":", expr «expr × »(α → exprℝ(), β → exprℝ()) → «expr × »(α → exprℝ(), β → exprℝ())] [":=", expr λ
   p, (id p.1, g p.1 p.2)],
  let [ident e] [] [":=", expr equiv.pi_equiv_pi_subtype_prod p (λ i : ι, exprℝ())],
  have [] [":", expr «expr = »((t.to_matrix.to_lin' : (ι → exprℝ()) → ι → exprℝ()), «expr ∘ »(e.symm, «expr ∘ »(F, e)))] [],
  { cases [expr t] [],
    ext [] [ident f, ident k] [],
    simp [] [] ["only"] ["[", expr linear_equiv.map_smul, ",", expr dite_eq_ite, ",", expr linear_map.id_coe, ",", expr p, ",", expr ite_not, ",", expr algebra.id.smul_eq_mul, ",", expr one_mul, ",", expr dot_product, ",", expr std_basis_matrix, ",", expr equiv.pi_equiv_pi_subtype_prod_symm_apply, ",", expr id.def, ",", expr transvection, ",", expr pi.add_apply, ",", expr zero_mul, ",", expr linear_map.smul_apply, ",", expr function.comp_app, ",", expr equiv.pi_equiv_pi_subtype_prod_apply, ",", expr matrix.transvection_struct.to_matrix_mk, ",", expr matrix.mul_vec, ",", expr linear_equiv.map_add, ",", expr ite_mul, ",", expr e, ",", expr matrix.to_lin'_apply, ",", expr pi.smul_apply, ",", expr subtype.coe_mk, ",", expr g, ",", expr linear_map.add_apply, ",", expr finset.sum_congr, ",", expr matrix.to_lin'_one, "]"] [] [],
    by_cases [expr h, ":", expr «expr = »(t_i, k)],
    { simp [] [] ["only"] ["[", expr h, ",", expr true_and, ",", expr finset.mem_univ, ",", expr if_true, ",", expr eq_self_iff_true, ",", expr finset.sum_ite_eq, ",", expr one_apply, ",", expr boole_mul, ",", expr add_comm, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr h, ",", expr ne.symm h, ",", expr add_zero, ",", expr if_false, ",", expr finset.sum_const_zero, ",", expr false_and, ",", expr mul_zero, "]"] [] [] } },
  rw [expr this] [],
  have [ident A] [":", expr measure_preserving e volume volume] [":=", expr ⟨measurable_pi_equiv_pi_subtype_prod (λ
     i, exprℝ()) _, (measure.map_pi_equiv_pi_subtype_prod (λ i, (volume : measure exprℝ())) p : _)⟩],
  have [ident B] [":", expr measure_preserving F volume volume] [],
  { have [ident g_meas] [":", expr measurable (function.uncurry g)] [],
    { have [] [":", expr measurable (λ
        c : α → exprℝ(), c ⟨t.j, t.hij.symm⟩)] [":=", expr measurable_pi_apply ⟨t.j, t.hij.symm⟩],
      refine [expr measurable.add (measurable_pi_lambda _ (λ i, measurable.const_mul _ _)) measurable_snd],
      exact [expr this.comp measurable_fst] },
    exact [expr measure_preserving.skew_product (measure_preserving.id _) g_meas (eventually_of_forall (λ
       a, map_volume_pi_add_left _))] },
  have [ident C] [":", expr measure_preserving e.symm volume volume] [":=", expr ⟨(measurable_pi_equiv_pi_subtype_prod_symm (λ
     i : ι, exprℝ()) p : _), (measure.map_pi_equiv_pi_subtype_prod_symm (λ i : ι, volume) p : _)⟩],
  exact [expr (C.comp B).comp A]
end

/-- Any invertible matrix rescales Lebesgue measure through the absolute value of its
determinant. -/
theorem map_matrix_volume_pi_eq_smul_volume_pi [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : det M ≠ 0) :
  measure.map M.to_lin' volume = Ennreal.ofReal (abs (det M⁻¹)) • volume :=
  by 
    apply diagonal_transvection_induction_of_det_ne_zero _ M hM (fun D hD => _) (fun t => _) fun A B hA hB IHA IHB => _
    ·
      convRHS => rw [←smul_map_diagonal_volume_pi hD]
      rw [smul_smul, ←Ennreal.of_real_mul (abs_nonneg _), ←abs_mul, inv_mul_cancel hD, abs_one, Ennreal.of_real_one,
        one_smul]
    ·
      simp only [Matrix.TransvectionStruct.det, Ennreal.of_real_one, map_transvection_volume_pi, one_smul,
        _root_.inv_one, abs_one]
    ·
      rw [to_lin'_mul, det_mul, LinearMap.coe_comp, ←measure.map_map, IHB, LinearMap.map_smul, IHA, smul_smul,
        ←Ennreal.of_real_mul (abs_nonneg _), ←abs_mul, mul_commₓ, mul_inv₀]
      ·
        apply Continuous.measurable 
        apply LinearMap.continuous_on_pi
      ·
        apply Continuous.measurable 
        apply LinearMap.continuous_on_pi

-- error in MeasureTheory.Measure.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any invertible linear map rescales Lebesgue measure through the absolute value of its
determinant. -/
theorem map_linear_map_volume_pi_eq_smul_volume_pi
{f : «expr →ₗ[ ] »(ι → exprℝ(), exprℝ(), ι → exprℝ())}
(hf : «expr ≠ »(f.det, 0)) : «expr = »(measure.map f volume, «expr • »(ennreal.of_real (abs «expr ⁻¹»(f.det)), volume)) :=
begin
  classical,
  let [ident M] [] [":=", expr f.to_matrix'],
  have [ident A] [":", expr «expr = »(f.det, det M)] [],
  by simp [] [] ["only"] ["[", expr linear_map.det_to_matrix', "]"] [] [],
  have [ident B] [":", expr «expr = »(f, M.to_lin')] [],
  by simp [] [] ["only"] ["[", expr to_lin'_to_matrix', "]"] [] [],
  rw ["[", expr A, ",", expr B, "]"] [],
  apply [expr map_matrix_volume_pi_eq_smul_volume_pi],
  rwa [expr A] ["at", ident hf]
end

end Real

open_locale TopologicalSpace

theorem Filter.Eventually.volume_pos_of_nhds_real {p : ℝ → Prop} {a : ℝ} (h : ∀ᶠx in 𝓝 a, p x) :
  (0 : ℝ≥0∞) < volume { x | p x } :=
  by 
    rcases h.exists_Ioo_subset with ⟨l, u, hx, hs⟩
    refine' lt_of_lt_of_leₓ _ (measure_mono hs)
    simpa [-mem_Ioo] using hx.1.trans hx.2

section RegionBetween

open_locale Classical

variable{α : Type _}

/-- The region between two real-valued functions on an arbitrary set. -/
def RegionBetween (f g : α → ℝ) (s : Set α) : Set (α × ℝ) :=
  { p:α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioo (f p.1) (g p.1) }

theorem region_between_subset (f g : α → ℝ) (s : Set α) : RegionBetween f g s ⊆ s.prod univ :=
  by 
    simpa only [prod_univ, RegionBetween, Set.Preimage, set_of_subset_set_of] using fun a => And.left

variable[MeasurableSpace α]{μ : Measureₓ α}{f g : α → ℝ}{s : Set α}

/-- The region between two measurable functions on a measurable set is measurable. -/
theorem measurable_set_region_between (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
  MeasurableSet (RegionBetween f g s) :=
  by 
    dsimp only [RegionBetween, Ioo, mem_set_of_eq, set_of_and]
    refine'
      MeasurableSet.inter _
        ((measurable_set_lt (hf.comp measurable_fst) measurable_snd).inter
          (measurable_set_lt measurable_snd (hg.comp measurable_fst)))
    convert hs.prod MeasurableSet.univ 
    simp only [and_trueₓ, mem_univ]

-- error in MeasureTheory.Measure.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem volume_region_between_eq_lintegral'
(hf : measurable f)
(hg : measurable g)
(hs : measurable_set s) : «expr = »(μ.prod volume (region_between f g s), «expr∫⁻ in , ∂ »((y), s, ennreal.of_real («expr - »(g, f) y), μ)) :=
begin
  rw [expr measure.prod_apply] [],
  { have [ident h] [":", expr «expr = »(λ
      x, volume {a | «expr ∧ »(«expr ∈ »(x, s), «expr ∈ »(a, Ioo (f x) (g x)))}, s.indicator (λ
       x, ennreal.of_real «expr - »(g x, f x)))] [],
    { funext [ident x],
      rw [expr indicator_apply] [],
      split_ifs [] [],
      { have [ident hx] [":", expr «expr = »({a | «expr ∧ »(«expr ∈ »(x, s), «expr ∈ »(a, Ioo (f x) (g x)))}, Ioo (f x) (g x))] [":=", expr by simp [] [] [] ["[", expr h, ",", expr Ioo, "]"] [] []],
        simp [] [] ["only"] ["[", expr hx, ",", expr real.volume_Ioo, ",", expr sub_zero, "]"] [] [] },
      { have [ident hx] [":", expr «expr = »({a | «expr ∧ »(«expr ∈ »(x, s), «expr ∈ »(a, Ioo (f x) (g x)))}, «expr∅»())] [":=", expr by simp [] [] [] ["[", expr h, "]"] [] []],
        simp [] [] ["only"] ["[", expr hx, ",", expr measure_empty, "]"] [] [] } },
    dsimp ["only"] ["[", expr region_between, ",", expr preimage_set_of_eq, "]"] [] [],
    rw ["[", expr h, ",", expr lintegral_indicator, "]"] []; simp [] [] ["only"] ["[", expr hs, ",", expr pi.sub_apply, "]"] [] [] },
  { exact [expr measurable_set_region_between hf hg hs] }
end

-- error in MeasureTheory.Measure.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The volume of the region between two almost everywhere measurable functions on a measurable set
    can be represented as a Lebesgue integral. -/
theorem volume_region_between_eq_lintegral
[sigma_finite μ]
(hf : ae_measurable f (μ.restrict s))
(hg : ae_measurable g (μ.restrict s))
(hs : measurable_set s) : «expr = »(μ.prod volume (region_between f g s), «expr∫⁻ in , ∂ »((y), s, ennreal.of_real («expr - »(g, f) y), μ)) :=
begin
  have [ident h₁] [":", expr «expr =ᵐ[ ] »(λ
    y, ennreal.of_real («expr - »(g, f) y), μ.restrict s, λ
    y, ennreal.of_real («expr - »(ae_measurable.mk g hg, ae_measurable.mk f hf) y))] [":=", expr (hg.ae_eq_mk.sub hf.ae_eq_mk).fun_comp _],
  have [ident h₂] [":", expr «expr = »((μ.restrict s).prod volume (region_between f g s), (μ.restrict s).prod volume (region_between (ae_measurable.mk f hf) (ae_measurable.mk g hg) s))] [],
  { apply [expr measure_congr],
    apply [expr eventually_eq.rfl.inter],
    exact [expr ((ae_eq_comp' measurable_fst hf.ae_eq_mk measure.prod_fst_absolutely_continuous).comp₂ _ eventually_eq.rfl).inter (eventually_eq.rfl.comp₂ _ (ae_eq_comp' measurable_fst hg.ae_eq_mk measure.prod_fst_absolutely_continuous))] },
  rw ["[", expr lintegral_congr_ae h₁, ",", "<-", expr volume_region_between_eq_lintegral' hf.measurable_mk hg.measurable_mk hs, "]"] [],
  convert [] [expr h₂] ["using", 1],
  { rw [expr measure.restrict_prod_eq_prod_univ] [],
    exact [expr (measure.restrict_eq_self' (hs.prod measurable_set.univ) (region_between_subset f g s)).symm] },
  { rw [expr measure.restrict_prod_eq_prod_univ] [],
    exact [expr (measure.restrict_eq_self' (hs.prod measurable_set.univ) (region_between_subset (ae_measurable.mk f hf) (ae_measurable.mk g hg) s)).symm] }
end

-- error in MeasureTheory.Measure.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem volume_region_between_eq_integral'
[sigma_finite μ]
(f_int : integrable_on f s μ)
(g_int : integrable_on g s μ)
(hs : measurable_set s)
(hfg : «expr ≤ᵐ[ ] »(f, μ.restrict s, g)) : «expr = »(μ.prod volume (region_between f g s), ennreal.of_real «expr∫ in , ∂ »((y), s, «expr - »(g, f) y, μ)) :=
begin
  have [ident h] [":", expr «expr =ᵐ[ ] »(«expr - »(g, f), μ.restrict s, λ x, real.to_nnreal «expr - »(g x, f x))] [],
  from [expr hfg.mono (λ x hx, «expr $ »(real.coe_to_nnreal _, sub_nonneg.2 hx).symm)],
  rw ["[", expr volume_region_between_eq_lintegral f_int.ae_measurable g_int.ae_measurable hs, ",", expr integral_congr_ae h, ",", expr lintegral_congr_ae, ",", expr lintegral_coe_eq_integral _ ((integrable_congr h).mp (g_int.sub f_int)), "]"] [],
  simpa [] [] ["only"] [] [] []
end

/-- If two functions are integrable on a measurable set, and one function is less than
    or equal to the other on that set, then the volume of the region
    between the two functions can be represented as an integral. -/
theorem volume_region_between_eq_integral [sigma_finite μ] (f_int : integrable_on f s μ) (g_int : integrable_on g s μ)
  (hs : MeasurableSet s) (hfg : ∀ x _ : x ∈ s, f x ≤ g x) :
  μ.prod volume (RegionBetween f g s) = Ennreal.ofReal (∫y in s, (g - f) y ∂μ) :=
  volume_region_between_eq_integral' f_int g_int hs ((ae_restrict_iff' hs).mpr (eventually_of_forall hfg))

end RegionBetween

