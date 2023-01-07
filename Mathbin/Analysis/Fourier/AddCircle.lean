/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, David Loeffler

! This file was ported from Lean 3 source module analysis.fourier.add_circle
! leanprover-community/mathlib commit 134625f523e737f650a6ea7f0c82a6177e45e622
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Complex.Circle
import Mathbin.Topology.Instances.AddCircle
import Mathbin.Analysis.InnerProductSpace.L2Space
import Mathbin.MeasureTheory.Function.ContinuousMapDense
import Mathbin.MeasureTheory.Function.L2Space
import Mathbin.MeasureTheory.Group.Integration
import Mathbin.MeasureTheory.Integral.Periodic
import Mathbin.Topology.ContinuousFunction.StoneWeierstrass

/-!

# Fourier analysis on the additive circle

This file contains basic results on Fourier series for functions on the additive circle
`add_circle T = ℝ / ℤ • T`.

## Main definitions

* `haar_add_circle`, Haar measure on `add_circle T`, normalized to have total measure `1`. (Note
  that this is not the same normalisation as the standard measure defined in `integral.periodic`,
  so we do not declare it as a `measure_space` instance, to avoid confusion.)
* for `n : ℤ`, `fourier n` is the monomial `λ x, exp (2 π i n x / T)`, bundled as a continuous map
  from `add_circle T` to `ℂ`.
* for `n : ℤ` and `p : ℝ≥0∞`, `fourier_Lp p n` is an abbreviation for the monomial `fourier n`
  considered as an element of the Lᵖ-space `Lp ℂ p haar_add_circle`, via the embedding
  `continuous_map.to_Lp`.
* `fourier_series` is the canonical isometric isomorphism from `Lp ℂ 2 haar_add_circle` to
  `ℓ²(ℤ, ℂ)` induced by taking Fourier coefficients.

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(add_circle T, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows
from the Stone-Weierstrass theorem after checking that it is a subalgebra, closed under conjugation,
and separates points.

The theorem `span_fourier_Lp_closure_eq_top` states that for `1 ≤ p < ∞` the span of the monomials
`fourier_Lp` is dense in the Lᵖ space of `add_circle T`, i.e. that its
`submodule.topological_closure` is `⊤`. This follows from the previous theorem using general theory
on approximation of Lᵖ functions by continuous functions.

The theorem `orthonormal_fourier` states that the monomials `fourier_Lp 2 n` form an orthonormal set
(in the L² space of `add_circle T` with respect to `haar_add_circle`).

The last two results together provide that the functions `fourier_Lp 2 n` form a Hilbert basis for
L²; this is named as `fourier_series`.

Parseval's identity, `tsum_sq_fourier_series_repr`, is a direct consequence of the construction of
this Hilbert basis.
-/


noncomputable section

open Ennreal ComplexConjugate Classical Real

open TopologicalSpace ContinuousMap MeasureTheory MeasureTheory.Measure Algebra Submodule Set

variable {T : ℝ}

namespace AddCircle

/-! ### Map from `add_circle` to `circle` -/


theorem scaled_exp_map_periodic : Function.Periodic (fun x => expMapCircle (2 * π / T * x)) T :=
  by
  -- The case T = 0 is not interesting, but it is true, so we prove it to save hypotheses
  rcases eq_or_ne T 0 with (rfl | hT)
  · intro x
    simp
  · intro x
    simp_rw [mul_add]
    rw [div_mul_cancel _ hT, periodic_exp_map_circle]
#align add_circle.scaled_exp_map_periodic AddCircle.scaled_exp_map_periodic

/-- The canonical map `λ x, exp (2 π i x / T)` from `ℝ / ℤ • T` to the unit circle in `ℂ`.
If `T = 0` we understand this as the constant function 1. -/
def toCircle : AddCircle T → circle :=
  (@scaled_exp_map_periodic T).lift
#align add_circle.to_circle AddCircle.toCircle

theorem to_circle_add (x : AddCircle T) (y : AddCircle T) :
    toCircle (x + y) = toCircle x * toCircle y :=
  by
  induction x using QuotientAddGroup.induction_on'
  induction y using QuotientAddGroup.induction_on'
  simp_rw [← QuotientAddGroup.coe_add, to_circle, Function.Periodic.lift_coe, mul_add,
    exp_map_circle_add]
#align add_circle.to_circle_add AddCircle.to_circle_add

theorem continuous_to_circle : Continuous (@toCircle T) :=
  continuous_coinduced_dom.mpr (expMapCircle.Continuous.comp <| continuous_const.mul continuous_id')
#align add_circle.continuous_to_circle AddCircle.continuous_to_circle

theorem injective_to_circle (hT : T ≠ 0) : Function.Injective (@toCircle T) :=
  by
  intro a b h
  induction a using QuotientAddGroup.induction_on'
  induction b using QuotientAddGroup.induction_on'
  simp_rw [to_circle, Function.Periodic.lift_coe] at h
  obtain ⟨m, hm⟩ := exp_map_circle_eq_exp_map_circle.mp h.symm
  simp_rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff, zsmul_eq_mul]
  use m
  field_simp [real.two_pi_pos.ne']  at hm
  rw [← mul_right_inj' real.two_pi_pos.ne']
  linarith
#align add_circle.injective_to_circle AddCircle.injective_to_circle

/-! ### Measure on `add_circle T`

In this file we use the Haar measure on `add_circle T` normalised to have total measure 1 (which is
**not** the same as the standard measure defined in `topology.instances.add_circle`). -/


variable [hT : Fact (0 < T)]

include hT

/-- Haar measure on the additive circle, normalised to have total measure 1. -/
def haarAddCircle : Measure (AddCircle T) :=
  addHaarMeasure ⊤deriving IsAddHaarMeasure
#align add_circle.haar_add_circle AddCircle.haarAddCircle

instance : IsProbabilityMeasure (@haarAddCircle T _) :=
  IsProbabilityMeasure.mk add_haar_measure_self

theorem volume_eq_smul_haar_add_circle :
    (volume : Measure (AddCircle T)) = Ennreal.ofReal T • haar_add_circle :=
  rfl
#align add_circle.volume_eq_smul_haar_add_circle AddCircle.volume_eq_smul_haar_add_circle

end AddCircle

open AddCircle

section Monomials

/-- The family of exponential monomials `λ x, exp (2 π i n x / T)`, parametrized by `n : ℤ` and
considered as bundled continuous maps from `ℝ / ℤ • T` to `ℂ`. -/
def fourier (n : ℤ) : C(AddCircle T, ℂ)
    where
  toFun x := toCircle (n • x)
  continuous_to_fun :=
    continuous_induced_dom.comp <| continuous_to_circle.comp <| continuous_zsmul _
#align fourier fourier

@[simp]
theorem fourier_apply {n : ℤ} {x : AddCircle T} : fourier n x = toCircle (n • x) :=
  rfl
#align fourier_apply fourier_apply

@[simp]
theorem fourier_zero {x : AddCircle T} : fourier 0 x = 1 :=
  by
  induction x using QuotientAddGroup.induction_on'
  rw [fourier_apply, to_circle, zero_zsmul, ← QuotientAddGroup.coe_zero, Function.Periodic.lift_coe,
    mul_zero, exp_map_circle_zero, coe_one_unit_sphere]
#align fourier_zero fourier_zero

@[simp]
theorem fourier_one {x : AddCircle T} : fourier 1 x = toCircle x := by rw [fourier_apply, one_zsmul]
#align fourier_one fourier_one

@[simp]
theorem fourier_neg {n : ℤ} {x : AddCircle T} : fourier (-n) x = conj (fourier n x) :=
  by
  induction x using QuotientAddGroup.induction_on'
  simp_rw [fourier_apply, to_circle, ← QuotientAddGroup.coe_zsmul, Function.Periodic.lift_coe, ←
    coe_inv_circle_eq_conj, ← exp_map_circle_neg, neg_smul, mul_neg]
#align fourier_neg fourier_neg

@[simp]
theorem fourier_add {m n : ℤ} {x : AddCircle T} : fourier (m + n) x = fourier m x * fourier n x :=
  by simp_rw [fourier_apply, add_zsmul, to_circle_add, coe_mul_unit_sphere]
#align fourier_add fourier_add

/-- For `n ≠ 0`, a translation by `T / 2 / n` negates the function `fourier n`. -/
theorem fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (hT : 0 < T) (x : AddCircle T) :
    fourier n (x + (T / 2 / n : ℝ)) = -fourier n x :=
  by
  rw [fourier_apply, zsmul_add, ← QuotientAddGroup.coe_zsmul, to_circle_add, coe_mul_unit_sphere]
  have : (n : ℂ) ≠ 0 := by simpa using hn
  have : (@to_circle T (n • (T / 2 / n) : ℝ) : ℂ) = -1 :=
    by
    rw [zsmul_eq_mul, to_circle, Function.Periodic.lift_coe, exp_map_circle_apply]
    replace hT := complex.of_real_ne_zero.mpr hT.ne'
    convert Complex.exp_pi_mul_I using 3
    field_simp
    ring
  rw [this]
  simp
#align fourier_add_half_inv_index fourier_add_half_inv_index

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` . -/
def fourierSubalgebra : Subalgebra ℂ C(AddCircle T, ℂ) :=
  Algebra.adjoin ℂ (range fourier)
#align fourier_subalgebra fourierSubalgebra

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is in fact the
linear span of these functions. -/
theorem fourier_subalgebra_coe : (@fourierSubalgebra T).toSubmodule = span ℂ (range fourier) :=
  by
  apply adjoin_eq_span_of_subset
  refine' subset.trans _ Submodule.subset_span
  intro x hx
  apply Submonoid.closure_induction hx (fun _ => id) ⟨0, _⟩
  · rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    refine' ⟨m + n, _⟩
    ext1 z
    exact fourier_add
  · ext1 z
    exact fourier_zero
#align fourier_subalgebra_coe fourier_subalgebra_coe

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is invariant under
complex conjugation. -/
theorem fourierSubalgebraConjInvariant :
    ConjInvariantSubalgebra ((@fourierSubalgebra T).restrictScalars ℝ) :=
  by
  apply subalgebra_conj_invariant
  rintro _ ⟨n, rfl⟩
  exact ⟨-n, ext fun _ => fourier_neg⟩
#align fourier_subalgebra_conj_invariant fourierSubalgebraConjInvariant

variable [hT : Fact (0 < T)]

include hT

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ`
separates points. -/
theorem fourier_subalgebra_separates_points : (@fourierSubalgebra T).SeparatesPoints :=
  by
  intro x y hxy
  refine' ⟨_, ⟨fourier 1, subset_adjoin ⟨1, rfl⟩, rfl⟩, _⟩
  dsimp only; rw [fourier_one, fourier_one]
  contrapose! hxy
  rw [Subtype.coe_inj] at hxy
  exact injective_to_circle hT.elim.ne' hxy
#align fourier_subalgebra_separates_points fourier_subalgebra_separates_points

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is dense. -/
theorem fourier_subalgebra_closure_eq_top : (@fourierSubalgebra T).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points
    fourierSubalgebra fourier_subalgebra_separates_points fourierSubalgebraConjInvariant
#align fourier_subalgebra_closure_eq_top fourier_subalgebra_closure_eq_top

/-- The linear span of the monomials `fourier n` is dense in `C(add_circle T, ℂ)`. -/
theorem span_fourier_closure_eq_top : (span ℂ (range <| @fourier T)).topologicalClosure = ⊤ :=
  by
  rw [← fourier_subalgebra_coe]
  exact congr_arg Subalgebra.toSubmodule fourier_subalgebra_closure_eq_top
#align span_fourier_closure_eq_top span_fourier_closure_eq_top

/-- The family of monomials `fourier n`, parametrized by `n : ℤ` and considered as
elements of the `Lp` space of functions `add_circle T → ℂ`. -/
abbrev fourierLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : lp ℂ p (@haarAddCircle T hT) :=
  toLp p haarAddCircle ℂ (fourier n)
#align fourier_Lp fourierLp

theorem coe_fn_fourier_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    @fourierLp T hT p _ n =ᵐ[haar_add_circle] fourier n :=
  coe_fn_to_Lp haarAddCircle (fourier n)
#align coe_fn_fourier_Lp coe_fn_fourier_Lp

/-- For each `1 ≤ p < ∞`, the linear span of the monomials `fourier n` is dense in
`Lp ℂ p haar_circle`. -/
theorem span_fourier_Lp_closure_eq_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (span ℂ (range (@fourierLp T _ p _))).topologicalClosure = ⊤ :=
  by
  convert
    (ContinuousMap.to_Lp_dense_range ℂ hp (@haar_add_circle T hT)
          ℂ).topological_closure_map_submodule
      span_fourier_closure_eq_top
  rw [map_span, range_comp]
  simp only [ContinuousLinearMap.coe_coe]
#align span_fourier_Lp_closure_eq_top span_fourier_Lp_closure_eq_top

/-- The monomials `fourier n` are an orthonormal set with respect to normalised Haar measure. -/
theorem orthonormalFourier : Orthonormal ℂ (@fourierLp T _ 2 _) :=
  by
  rw [orthonormal_iff_ite]
  intro i j
  rw [continuous_map.inner_to_Lp (@haar_add_circle T hT) (fourier i) (fourier j)]
  simp_rw [← fourier_neg, ← fourier_add]
  split_ifs
  · simp_rw [h, neg_add_self]
    have : ⇑(@fourier T 0) = (fun x => 1 : AddCircle T → ℂ) :=
      by
      ext1
      exact fourier_zero
    rw [this, integral_const, measure_univ, Ennreal.one_to_real, Complex.real_smul,
      Complex.of_real_one, mul_one]
  have hij : -i + j ≠ 0 := by
    rw [add_comm]
    exact sub_ne_zero.mpr (Ne.symm h)
  convert integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hij hT.elim)
  exact IsAddLeftInvariant.isAddRightInvariant
#align orthonormal_fourier orthonormalFourier

end Monomials

section fourier

variable [hT : Fact (0 < T)]

include hT

/-- We define `fourier_series` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 haar_add_circle`,
which by definition is an isometric isomorphism from `Lp ℂ 2 haar_add_circle` to `ℓ²(ℤ, ℂ)`. -/
def fourierSeries : HilbertBasis ℤ ℂ (lp ℂ 2 <| @haarAddCircle T hT) :=
  HilbertBasis.mk orthonormalFourier (span_fourier_Lp_closure_eq_top (by norm_num)).ge
#align fourier_series fourierSeries

/-- The elements of the Hilbert basis `fourier_series` are the functions `fourier_Lp 2`, i.e. the
monomials `fourier n` on the circle considered as elements of `L²`. -/
@[simp]
theorem coe_fourier_series : ⇑(@fourierSeries _ hT) = fourierLp 2 :=
  HilbertBasis.coe_mk _ _
#align coe_fourier_series coe_fourier_series

/-- Under the isometric isomorphism `fourier_series` from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is the integral over `add_circle T` of `λ t, fourier (-i) t * f t`. -/
theorem fourier_series_repr (f : lp ℂ 2 <| @haarAddCircle T hT) (i : ℤ) :
    fourierSeries.repr f i = ∫ t : AddCircle T, fourier (-i) t * f t ∂haar_add_circle :=
  by
  trans ∫ t : AddCircle T, conj ((@fourierLp T hT 2 _ i : AddCircle T → ℂ) t) * f t ∂haar_add_circle
  · simp [fourier_series.repr_apply_apply f i, MeasureTheory.L2Cat.inner_def]
  · apply integral_congr_ae
    filter_upwards [coe_fn_fourier_Lp 2 i] with _ ht
    rw [ht, ← fourier_neg]
#align fourier_series_repr fourier_series_repr

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L²` space of `add_circle T`. -/
theorem has_sum_fourier_series (f : lp ℂ 2 <| @haarAddCircle T hT) :
    HasSum (fun i => fourierSeries.repr f i • fourierLp 2 i) f := by
  simpa using HilbertBasis.has_sum_repr fourierSeries f
#align has_sum_fourier_series has_sum_fourier_series

/-- **Parseval's identity**: for an `L²` function `f` on `add_circle T`, the sum of the squared
norms of the Fourier coefficients equals the `L²` norm of `f`. -/
theorem tsum_sq_fourier_series_repr (f : lp ℂ 2 <| @haarAddCircle T hT) :
    (∑' i : ℤ, ‖fourierSeries.repr f i‖ ^ 2) = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haar_add_circle :=
  by
  have H₁ : ‖fourier_series.repr f‖ ^ 2 = ∑' i, ‖fourier_series.repr f i‖ ^ 2 :=
    by
    exact_mod_cast lp.norm_rpow_eq_tsum _ (fourier_series.repr f)
    norm_num
  have H₂ : ‖fourier_series.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp
  have H₃ := congr_arg IsROrC.re (@L2.inner_def (AddCircle T) ℂ ℂ _ _ _ _ f f)
  rw [← integral_re] at H₃
  · simp only [← norm_sq_eq_inner] at H₃
    rw [← H₁, H₂, H₃]
  · exact L2.integrable_inner f f
#align tsum_sq_fourier_series_repr tsum_sq_fourier_series_repr

/-- The Fourier coefficients are given by integrating over the interval `[a, a + T] ⊂ ℝ`. -/
theorem fourier_series_repr' (f : lp ℂ 2 <| @haarAddCircle T hT) (n : ℤ) (a : ℝ) :
    fourierSeries.repr f n = 1 / T * ∫ x in a..a + T, @fourier T (-n) x * f x :=
  by
  have ha : ae_strongly_measurable (fun t : AddCircle T => fourier (-n) t * f t) haar_add_circle :=
    (map_continuous _).AeStronglyMeasurable.mul (Lp.ae_strongly_measurable _)
  rw [fourier_series_repr, AddCircle.interval_integral_preimage T a (ha.smul_measure _),
    volume_eq_smul_haar_add_circle, integral_smul_measure]
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.out.ne'
  field_simp [Ennreal.to_real_of_real hT.out.le, Complex.real_smul]
  ring
#align fourier_series_repr' fourier_series_repr'

end fourier

