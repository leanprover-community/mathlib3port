/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, David Loeffler

! This file was ported from Lean 3 source module analysis.fourier.add_circle
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
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
* `fourier_basis` is the Hilbert basis of `Lp ℂ 2 haar_add_circle` given by the images of the
  monomials `fourier n`.
* `fourier_coeff f n`, for `f : add_circle T → ℂ`, is the `n`-th Fourier coefficient of `f`
  (defined as an integral over `add_circle T`).

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(add_circle T, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows
from the Stone-Weierstrass theorem after checking that the span is a subalgebra, is closed under
conjugation, and separates points.

Using this and general theory on approximation of Lᵖ functions by continuous functions, we deduce
(`span_fourier_Lp_closure_eq_top`) that for any `1 ≤ p < ∞`, the span of the Fourier monomials is
dense in the Lᵖ space of `add_circle T`. For `p = 2` we show (`orthonormal_fourier`) that the
monomials are also orthonormal, so they form a Hilbert basis for L², which is named as
`fourier_basis`; in particular, for `L²` functions `f`, the Fourier series of `f` converges to `f`
in the `L²` topology (`has_sum_fourier_series_L2`). Parseval's identity, `tsum_sq_fourier_coeff`, is
a direct consequence.

For continuous maps `f : add_circle T → ℂ`, the theorem
`continuous_map.has_sum_fourier_series_of_summable` states that if the sequence of Fourier
coefficients of `f` is summable, then the Fourier series `∑ (i:ℤ), f.fourier_coeff i * fourier i`
converges to `f` in the uniform-convergence topology of `C(add_circle T, ℂ)`.
-/


noncomputable section

open Ennreal ComplexConjugate Real

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
theorem fourier_coe_apply {n : ℤ} {x : ℝ} :
    fourier n (x : AddCircle T) = Complex.exp (2 * π * Complex.i * n * x / T) :=
  by
  rw [fourier_apply, ← QuotientAddGroup.coe_zsmul, to_circle, Function.Periodic.lift_coe,
    exp_map_circle_apply, Complex.of_real_mul, Complex.of_real_div, Complex.of_real_mul,
    zsmul_eq_mul, Complex.of_real_mul, Complex.of_real_int_cast, Complex.of_real_bit0,
    Complex.of_real_one]
  congr 1; ring
#align fourier_coe_apply fourier_coe_apply

@[simp]
theorem fourier_zero {x : AddCircle T} : fourier 0 x = 1 :=
  by
  induction x using QuotientAddGroup.induction_on'
  simp only [fourier_coe_apply, algebraMap.coe_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero]
#align fourier_zero fourier_zero

@[simp]
theorem fourier_eval_zero (n : ℤ) : fourier n (0 : AddCircle T) = 1 := by
  rw [← QuotientAddGroup.coe_zero, fourier_coe_apply, Complex.of_real_zero, mul_zero, zero_div,
    Complex.exp_zero]
#align fourier_eval_zero fourier_eval_zero

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

theorem fourier_norm [Fact (0 < T)] (n : ℤ) : ‖@fourier T n‖ = 1 :=
  by
  rw [ContinuousMap.norm_eq_supr_norm]
  have : ∀ x : AddCircle T, ‖fourier n x‖ = 1 := fun x => abs_coe_circle _
  simp_rw [this]
  exact @csupᵢ_const _ _ _ Zero.nonempty _
#align fourier_norm fourier_norm

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

section ScopeHT

-- everything from here on needs `0 < T`
variable [hT : Fact (0 < T)]

include hT

section fourierCoeff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The `n`-th Fourier coefficient of a function `add_circle T → E`, for `E` a complete normed
`ℂ`-vector space, defined as the integral over `add_circle T` of `fourier (-n) t • f t`. -/
def fourierCoeff (f : AddCircle T → E) (n : ℤ) : E :=
  ∫ t : AddCircle T, fourier (-n) t • f t ∂haar_add_circle
#align fourier_coeff fourierCoeff

/-- The Fourier coefficients of a function can be computed as an integral
over `[a, a + T]` for any real `a`. -/
theorem fourier_coeff_eq_interval_integral (f : AddCircle T → E) (n : ℤ) (a : ℝ) :
    fourierCoeff f n = (1 / T) • ∫ x in a..a + T, @fourier T (-n) x • f x :=
  by
  have : ∀ x : ℝ, @fourier T (-n) x • f x = (fun z : AddCircle T => @fourier T (-n) z • f z) x :=
    by
    intro x
    rfl
  simp_rw [this]
  rw [fourierCoeff, AddCircle.interval_integral_preimage T a, volume_eq_smul_haar_add_circle,
    integral_smul_measure, Ennreal.to_real_of_real hT.out.le, ← smul_assoc, smul_eq_mul,
    one_div_mul_cancel hT.out.ne', one_smul]
#align fourier_coeff_eq_interval_integral fourier_coeff_eq_interval_integral

end fourierCoeff

section FourierL2

/-- We define `fourier_basis` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 haar_add_circle`,
which by definition is an isometric isomorphism from `Lp ℂ 2 haar_add_circle` to `ℓ²(ℤ, ℂ)`. -/
def fourierBasis : HilbertBasis ℤ ℂ (lp ℂ 2 <| @haarAddCircle T hT) :=
  HilbertBasis.mk orthonormalFourier (span_fourier_Lp_closure_eq_top (by norm_num)).ge
#align fourier_basis fourierBasis

/-- The elements of the Hilbert basis `fourier_basis` are the functions `fourier_Lp 2`, i.e. the
monomials `fourier n` on the circle considered as elements of `L²`. -/
@[simp]
theorem coe_fourier_basis : ⇑(@fourierBasis _ hT) = fourierLp 2 :=
  HilbertBasis.coe_mk _ _
#align coe_fourier_basis coe_fourier_basis

/-- Under the isometric isomorphism `fourier_basis` from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is `fourier_coeff f i`, i.e., the integral over `add_circle T` of
`λ t, fourier (-i) t * f t` with respect to the Haar measure of total mass 1. -/
theorem fourier_basis_repr (f : lp ℂ 2 <| @haarAddCircle T hT) (i : ℤ) :
    fourierBasis.repr f i = fourierCoeff f i :=
  by
  trans ∫ t : AddCircle T, conj ((@fourierLp T hT 2 _ i : AddCircle T → ℂ) t) * f t ∂haar_add_circle
  · simp [fourier_basis.repr_apply_apply f i, MeasureTheory.L2Cat.inner_def]
  · apply integral_congr_ae
    filter_upwards [coe_fn_fourier_Lp 2 i] with _ ht
    rw [ht, ← fourier_neg, smul_eq_mul]
#align fourier_basis_repr fourier_basis_repr

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L²` space of `add_circle T`. -/
theorem has_sum_fourier_series_L2 (f : lp ℂ 2 <| @haarAddCircle T hT) :
    HasSum (fun i => fourierCoeff f i • fourierLp 2 i) f :=
  by
  simp_rw [← fourier_basis_repr]
  simpa using HilbertBasis.has_sum_repr fourierBasis f
#align has_sum_fourier_series_L2 has_sum_fourier_series_L2

/-- **Parseval's identity**: for an `L²` function `f` on `add_circle T`, the sum of the squared
norms of the Fourier coefficients equals the `L²` norm of `f`. -/
theorem tsum_sq_fourier_coeff (f : lp ℂ 2 <| @haarAddCircle T hT) :
    (∑' i : ℤ, ‖fourierCoeff f i‖ ^ 2) = ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haar_add_circle :=
  by
  simp_rw [← fourier_basis_repr]
  have H₁ : ‖fourier_basis.repr f‖ ^ 2 = ∑' i, ‖fourier_basis.repr f i‖ ^ 2 :=
    by
    exact_mod_cast lp.norm_rpow_eq_tsum _ (fourier_basis.repr f)
    norm_num
  have H₂ : ‖fourier_basis.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp
  have H₃ := congr_arg IsROrC.re (@L2.inner_def (AddCircle T) ℂ ℂ _ _ _ _ f f)
  rw [← integral_re] at H₃
  · simp only [← norm_sq_eq_inner] at H₃
    rw [← H₁, H₂, H₃]
  · exact L2.integrable_inner f f
#align tsum_sq_fourier_coeff tsum_sq_fourier_coeff

end FourierL2

section Convergence

variable (f : C(AddCircle T, ℂ))

theorem fourier_coeff_to_Lp (n : ℤ) :
    fourierCoeff (toLp 2 haarAddCircle ℂ f) n = fourierCoeff f n :=
  integral_congr_ae
    (Filter.EventuallyEq.mul (Filter.eventually_of_forall (by tauto))
      (ContinuousMap.coe_fn_to_ae_eq_fun haarAddCircle f))
#align fourier_coeff_to_Lp fourier_coeff_to_Lp

variable {f}

/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series converges
uniformly to `f`. -/
theorem has_sum_fourier_series_of_summable (h : Summable (fourierCoeff f)) :
    HasSum (fun i => fourierCoeff f i • fourier i) f :=
  by
  have sum_L2 := has_sum_fourier_series_L2 (to_Lp 2 haar_add_circle ℂ f)
  simp_rw [fourier_coeff_to_Lp] at sum_L2
  refine' ContinuousMap.has_sum_of_has_sum_Lp (summable_of_summable_norm _) sum_L2
  simp_rw [norm_smul, fourier_norm, mul_one, summable_norm_iff]
  exact h
#align has_sum_fourier_series_of_summable has_sum_fourier_series_of_summable

/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series of `f`
converges everywhere pointwise to `f`. -/
theorem has_pointwise_sum_fourier_series_of_summable (h : Summable (fourierCoeff f))
    (x : AddCircle T) : HasSum (fun i => fourierCoeff f i • fourier i x) (f x) :=
  (ContinuousMap.evalClm ℂ x).HasSum (has_sum_fourier_series_of_summable h)
#align has_pointwise_sum_fourier_series_of_summable has_pointwise_sum_fourier_series_of_summable

end Convergence

end ScopeHT

