/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module measure_theory.group.prod
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Constructions.Prod
import Mathbin.MeasureTheory.Group.Measure

/-!
# Measure theory in the product of groups
In this file we show properties about measure theory in products of measurable groups
and properties of iterated integrals in measurable groups.

These lemmas show the uniqueness of left invariant measures on measurable groups, up to
scaling. In this file we follow the proof and refer to the book *Measure Theory* by Paul Halmos.

The idea of the proof is to use the translation invariance of measures to prove `μ(t) = c * μ(s)`
for two sets `s` and `t`, where `c` is a constant that does not depend on `μ`. Let `e` and `f` be
the characteristic functions of `s` and `t`.
Assume that `μ` and `ν` are left-invariant measures. Then the map `(x, y) ↦ (y * x, x⁻¹)`
preserves the measure `μ × ν`, which means that
```
  ∫ x, ∫ y, h x y ∂ν ∂μ = ∫ x, ∫ y, h (y * x) x⁻¹ ∂ν ∂μ
```
If we apply this to `h x y := e x * f y⁻¹ / ν ((λ h, h * y⁻¹) ⁻¹' s)`, we can rewrite the RHS to
`μ(t)`, and the LHS to `c * μ(s)`, where `c = c(ν)` does not depend on `μ`.
Applying this to `μ` and to `ν` gives `μ (t) / μ (s) = ν (t) / ν (s)`, which is the uniqueness up to
scalar multiplication.

The proof in [Halmos] seems to contain an omission in §60 Th. A, see
`measure_theory.measure_lintegral_div_measure`.

-/


noncomputable section

open Set hiding prod_eq

open Function MeasureTheory

open Filter hiding map

open Classical Ennreal Pointwise MeasureTheory

variable (G : Type _) [MeasurableSpace G]

variable [Group G] [HasMeasurableMul₂ G]

variable (μ ν : Measure G) [SigmaFinite ν] [SigmaFinite μ] {s : Set G}

/-- The map `(x, y) ↦ (x, xy)` as a `measurable_equiv`. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a `measurable_equiv`."]
protected def MeasurableEquiv.shearMulRight [HasMeasurableInv G] : G × G ≃ᵐ G × G :=
  {
    Equiv.prodShear (Equiv.refl _)
      Equiv.mulLeft with
    measurable_to_fun := measurable_fst.prod_mk measurable_mul
    measurable_inv_fun := measurable_fst.prod_mk <| measurable_fst.inv.mul measurable_snd }
#align measurable_equiv.shear_mul_right MeasurableEquiv.shearMulRight
#align measurable_equiv.shear_add_right MeasurableEquiv.shear_add_right

/-- The map `(x, y) ↦ (x, y / x)` as a `measurable_equiv` with as inverse `(x, y) ↦ (x, yx)` -/
@[to_additive
      "The map `(x, y) ↦ (x, y - x)` as a `measurable_equiv` with as inverse `(x, y) ↦ (x, y + x)`."]
protected def MeasurableEquiv.shearDivRight [HasMeasurableInv G] : G × G ≃ᵐ G × G :=
  {
    Equiv.prodShear (Equiv.refl _)
      Equiv.divRight with
    measurable_to_fun := measurable_fst.prod_mk <| measurable_snd.div measurable_fst
    measurable_inv_fun := measurable_fst.prod_mk <| measurable_snd.mul measurable_fst }
#align measurable_equiv.shear_div_right MeasurableEquiv.shearDivRight
#align measurable_equiv.shear_sub_right MeasurableEquiv.shear_sub_right

variable {G}

namespace MeasureTheory

open Measure

section LeftInvariant

/-- The multiplicative shear mapping `(x, y) ↦ (x, xy)` preserves the measure `μ × ν`.
This condition is part of the definition of a measurable group in [Halmos, §59].
There, the map in this lemma is called `S`. -/
@[to_additive measure_preserving_prod_add
      " The shear mapping `(x, y) ↦ (x, x + y)` preserves the measure `μ × ν`. "]
theorem measurePreservingProdMul [IsMulLeftInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.1 * z.2)) (μ.Prod ν) (μ.Prod ν) :=
  (MeasurePreserving.id μ).skewProduct measurable_mul <|
    Filter.eventually_of_forall <| map_mul_left_eq_self ν
#align measure_theory.measure_preserving_prod_mul MeasureTheory.measurePreservingProdMul
#align measure_theory.measure_preserving_prod_add MeasureTheory.measure_preserving_prod_add

/-- The map `(x, y) ↦ (y, yx)` sends the measure `μ × ν` to `ν × μ`.
This is the map `SR` in [Halmos, §59].
`S` is the map `(x, y) ↦ (x, xy)` and `R` is `prod.swap`. -/
@[to_additive measure_preserving_prod_add_swap
      " The map `(x, y) ↦ (y, y + x)` sends the measure `μ × ν` to `ν × μ`. "]
theorem measurePreservingProdMulSwap [IsMulLeftInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.2, z.2 * z.1)) (μ.Prod ν) (ν.Prod μ) :=
  (measurePreservingProdMul ν μ).comp measurePreservingSwap
#align measure_theory.measure_preserving_prod_mul_swap MeasureTheory.measurePreservingProdMulSwap
#align measure_theory.measure_preserving_prod_add_swap MeasureTheory.measure_preserving_prod_add_swap

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem measurable_measure_mul_right (hs : MeasurableSet s) :
    Measurable fun x => μ ((fun y => y * x) ⁻¹' s) :=
  by
  suffices
    Measurable fun y =>
      μ ((fun x => (x, y)) ⁻¹' ((fun z : G × G => ((1 : G), z.1 * z.2)) ⁻¹' univ ×ˢ s))
    by
    convert this
    ext1 x
    congr 1 with y : 1
    simp
  apply measurable_measure_prod_mk_right
  exact measurable_const.prod_mk measurable_mul (measurable_set.univ.prod hs)
#align measure_theory.measurable_measure_mul_right MeasureTheory.measurable_measure_mul_right
#align measure_theory.measurable_measure_add_right MeasureTheory.measurable_measure_add_right

variable [HasMeasurableInv G]

/-- The map `(x, y) ↦ (x, x⁻¹y)` is measure-preserving.
This is the function `S⁻¹` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)`. -/
@[to_additive measure_preserving_prod_neg_add
      "The map `(x, y) ↦ (x, - x + y)` is measure-preserving."]
theorem measurePreservingProdInvMul [IsMulLeftInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.1⁻¹ * z.2)) (μ.Prod ν) (μ.Prod ν) :=
  (measurePreservingProdMul μ ν).symm <| MeasurableEquiv.shearMulRight G
#align measure_theory.measure_preserving_prod_inv_mul MeasureTheory.measurePreservingProdInvMul
#align measure_theory.measure_preserving_prod_neg_add MeasureTheory.measure_preserving_prod_neg_add

variable [IsMulLeftInvariant μ]

/-- The map `(x, y) ↦ (y, y⁻¹x)` sends `μ × ν` to `ν × μ`.
This is the function `S⁻¹R` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)` and `R` is `prod.swap`. -/
@[to_additive measure_preserving_prod_neg_add_swap
      "The map `(x, y) ↦ (y, - y + x)` sends `μ × ν` to `ν × μ`."]
theorem measurePreservingProdInvMulSwap :
    MeasurePreserving (fun z : G × G => (z.2, z.2⁻¹ * z.1)) (μ.Prod ν) (ν.Prod μ) :=
  (measurePreservingProdInvMul ν μ).comp measurePreservingSwap
#align measure_theory.measure_preserving_prod_inv_mul_swap MeasureTheory.measurePreservingProdInvMulSwap
#align measure_theory.measure_preserving_prod_neg_add_swap MeasureTheory.measure_preserving_prod_neg_add_swap

/-- The map `(x, y) ↦ (yx, x⁻¹)` is measure-preserving.
This is the function `S⁻¹RSR` in [Halmos, §59],
where `S` is the map `(x, y) ↦ (x, xy)` and `R` is `prod.swap`. -/
@[to_additive measure_preserving_add_prod_neg
      "The map `(x, y) ↦ (y + x, - x)` is measure-preserving."]
theorem measurePreservingMulProdInv [IsMulLeftInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.Prod ν) (μ.Prod ν) :=
  by
  convert (measure_preserving_prod_inv_mul_swap ν μ).comp (measure_preserving_prod_mul_swap μ ν)
  ext1 ⟨x, y⟩
  simp_rw [Function.comp_apply, mul_inv_rev, inv_mul_cancel_right]
#align measure_theory.measure_preserving_mul_prod_inv MeasureTheory.measurePreservingMulProdInv
#align measure_theory.measure_preserving_add_prod_neg MeasureTheory.measure_preserving_add_prod_neg

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem quasiMeasurePreservingInv : QuasiMeasurePreserving (Inv.inv : G → G) μ μ :=
  by
  refine' ⟨measurable_inv, absolutely_continuous.mk fun s hsm hμs => _⟩
  rw [map_apply measurable_inv hsm, inv_preimage]
  have hf : Measurable fun z : G × G => (z.2 * z.1, z.1⁻¹) :=
    (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv
  suffices map (fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.prod μ) (s⁻¹ ×ˢ s⁻¹) = 0 by
    simpa only [(measure_preserving_mul_prod_inv μ μ).map_eq, prod_prod, mul_eq_zero,
      or_self_iff] using this
  have hsm' : MeasurableSet (s⁻¹ ×ˢ s⁻¹) := hsm.inv.prod hsm.inv
  simp_rw [map_apply hf hsm', prod_apply_symm (hf hsm'), preimage_preimage, mk_preimage_prod,
    inv_preimage, inv_inv, measure_mono_null (inter_subset_right _ _) hμs, lintegral_zero]
#align measure_theory.quasi_measure_preserving_inv MeasureTheory.quasiMeasurePreservingInv
#align measure_theory.quasi_measure_preserving_neg MeasureTheory.quasi_measure_preserving_neg

@[to_additive]
theorem measure_inv_null : μ s⁻¹ = 0 ↔ μ s = 0 :=
  by
  refine' ⟨fun hs => _, (quasi_measure_preserving_inv μ).preimage_null⟩
  rw [← inv_inv s]
  exact (quasi_measure_preserving_inv μ).preimage_null hs
#align measure_theory.measure_inv_null MeasureTheory.measure_inv_null
#align measure_theory.measure_neg_null MeasureTheory.measure_neg_null

@[to_additive]
theorem invAbsolutelyContinuous : μ.inv ≪ μ :=
  (quasiMeasurePreservingInv μ).AbsolutelyContinuous
#align measure_theory.inv_absolutely_continuous MeasureTheory.invAbsolutelyContinuous
#align measure_theory.neg_absolutely_continuous MeasureTheory.neg_absolutely_continuous

@[to_additive]
theorem absolutelyContinuousInv : μ ≪ μ.inv :=
  by
  refine' absolutely_continuous.mk fun s hs => _
  simp_rw [inv_apply μ s, measure_inv_null, imp_self]
#align measure_theory.absolutely_continuous_inv MeasureTheory.absolutelyContinuousInv
#align measure_theory.absolutely_continuous_neg MeasureTheory.absolutely_continuous_neg

@[to_additive]
theorem lintegral_lintegral_mul_inv [IsMulLeftInvariant ν] (f : G → G → ℝ≥0∞)
    (hf : AeMeasurable (uncurry f) (μ.Prod ν)) :
    (∫⁻ x, ∫⁻ y, f (y * x) x⁻¹ ∂ν ∂μ) = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ :=
  by
  have h : Measurable fun z : G × G => (z.2 * z.1, z.1⁻¹) :=
    (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv
  have h2f : AeMeasurable (uncurry fun x y => f (y * x) x⁻¹) (μ.prod ν) :=
    hf.comp_quasi_measure_preserving (measure_preserving_mul_prod_inv μ ν).QuasiMeasurePreserving
  simp_rw [lintegral_lintegral h2f, lintegral_lintegral hf]
  conv_rhs => rw [← (measure_preserving_mul_prod_inv μ ν).map_eq]
  symm
  exact
    lintegral_map' (hf.mono' (measure_preserving_mul_prod_inv μ ν).map_eq.AbsolutelyContinuous)
      h.ae_measurable
#align measure_theory.lintegral_lintegral_mul_inv MeasureTheory.lintegral_lintegral_mul_inv
#align measure_theory.lintegral_lintegral_add_neg MeasureTheory.lintegral_lintegral_add_neg

@[to_additive]
theorem measure_mul_right_null (y : G) : μ ((fun x => x * y) ⁻¹' s) = 0 ↔ μ s = 0 :=
  calc
    μ ((fun x => x * y) ⁻¹' s) = 0 ↔ μ ((fun x => y⁻¹ * x) ⁻¹' s⁻¹)⁻¹ = 0 := by
      simp_rw [← inv_preimage, preimage_preimage, mul_inv_rev, inv_inv]
    _ ↔ μ s = 0 := by simp only [measure_inv_null μ, measure_preimage_mul]
    
#align measure_theory.measure_mul_right_null MeasureTheory.measure_mul_right_null
#align measure_theory.measure_add_right_null MeasureTheory.measure_add_right_null

@[to_additive]
theorem measure_mul_right_ne_zero (h2s : μ s ≠ 0) (y : G) : μ ((fun x => x * y) ⁻¹' s) ≠ 0 :=
  (not_congr (measure_mul_right_null μ y)).mpr h2s
#align measure_theory.measure_mul_right_ne_zero MeasureTheory.measure_mul_right_ne_zero
#align measure_theory.measure_add_right_ne_zero MeasureTheory.measure_add_right_ne_zero

@[to_additive]
theorem absolutelyContinuousMapMulRight (g : G) : μ ≪ map (· * g) μ :=
  by
  refine' absolutely_continuous.mk fun s hs => _
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null]; exact id
#align measure_theory.absolutely_continuous_map_mul_right MeasureTheory.absolutelyContinuousMapMulRight
#align measure_theory.absolutely_continuous_map_add_right MeasureTheory.absolutely_continuous_map_add_right

@[to_additive]
theorem absolutelyContinuousMapDivLeft (g : G) : μ ≪ map (fun h => g / h) μ :=
  by
  simp_rw [div_eq_mul_inv]
  rw [← map_map (measurable_const_mul g) measurable_inv]
  conv_lhs => rw [← map_mul_left_eq_self μ g]
  exact (absolutely_continuous_inv μ).map (measurable_const_mul g)
#align measure_theory.absolutely_continuous_map_div_left MeasureTheory.absolutelyContinuousMapDivLeft
#align measure_theory.absolutely_continuous_map_sub_left MeasureTheory.absolutely_continuous_map_sub_left

/-- This is the computation performed in the proof of [Halmos, §60 Th. A]. -/
@[to_additive "This is the computation performed in the proof of [Halmos, §60 Th. A]."]
theorem measure_mul_lintegral_eq [IsMulLeftInvariant ν] (sm : MeasurableSet s) (f : G → ℝ≥0∞)
    (hf : Measurable f) : (μ s * ∫⁻ y, f y ∂ν) = ∫⁻ x, ν ((fun z => z * x) ⁻¹' s) * f x⁻¹ ∂μ :=
  by
  rw [← set_lintegral_one, ← lintegral_indicator _ sm, ←
    lintegral_lintegral_mul (measurable_const.indicator sm).AeMeasurable hf.ae_measurable, ←
    lintegral_lintegral_mul_inv μ ν]
  swap
  ·
    exact
      (((measurable_const.indicator sm).comp measurable_fst).mul
          (hf.comp measurable_snd)).AeMeasurable
  have ms :
    ∀ x : G, Measurable fun y => ((fun z => z * x) ⁻¹' s).indicator (fun z => (1 : ℝ≥0∞)) y :=
    fun x => measurable_const.indicator (measurable_mul_const _ sm)
  have :
    ∀ x y,
      s.indicator (fun z : G => (1 : ℝ≥0∞)) (y * x) =
        ((fun z => z * x) ⁻¹' s).indicator (fun b : G => 1) y :=
    by
    intro x y
    symm
    convert indicator_comp_right fun y => y * x
    ext1 z
    rfl
  simp_rw [this, lintegral_mul_const _ (ms _), lintegral_indicator _ (measurable_mul_const _ sm),
    set_lintegral_one]
#align measure_theory.measure_mul_lintegral_eq MeasureTheory.measure_mul_lintegral_eq
#align measure_theory.measure_add_lintegral_eq MeasureTheory.measure_add_lintegral_eq

/-- Any two nonzero left-invariant measures are absolutely continuous w.r.t. each other. -/
@[to_additive
      " Any two nonzero left-invariant measures are absolutely continuous w.r.t. each\nother. "]
theorem absolutelyContinuousOfIsMulLeftInvariant [IsMulLeftInvariant ν] (hν : ν ≠ 0) : μ ≪ ν :=
  by
  refine' absolutely_continuous.mk fun s sm hνs => _
  have h1 := measure_mul_lintegral_eq μ ν sm 1 measurable_one
  simp_rw [Pi.one_apply, lintegral_one, mul_one, (measure_mul_right_null ν _).mpr hνs,
    lintegral_zero, mul_eq_zero, measure_univ_eq_zero.not.mpr hν, or_false_iff] at h1
  exact h1
#align measure_theory.absolutely_continuous_of_is_mul_left_invariant MeasureTheory.absolutelyContinuousOfIsMulLeftInvariant
#align measure_theory.absolutely_continuous_of_is_add_left_invariant MeasureTheory.absolutely_continuous_of_is_add_left_invariant

@[to_additive]
theorem ae_measure_preimage_mul_right_lt_top [IsMulLeftInvariant ν] (sm : MeasurableSet s)
    (hμs : μ s ≠ ∞) : ∀ᵐ x ∂μ, ν ((fun y => y * x) ⁻¹' s) < ∞ :=
  by
  refine' ae_of_forall_measure_lt_top_ae_restrict' ν.inv _ _
  intro A hA h2A h3A
  simp only [ν.inv_apply] at h3A
  apply ae_lt_top (measurable_measure_mul_right ν sm)
  have h1 := measure_mul_lintegral_eq μ ν sm (A⁻¹.indicator 1) (measurable_one.indicator hA.inv)
  rw [lintegral_indicator _ hA.inv] at h1
  simp_rw [Pi.one_apply, set_lintegral_one, ← image_inv, indicator_image inv_injective, image_inv, ←
    indicator_mul_right _ fun x => ν ((fun y => y * x) ⁻¹' s), Function.comp, Pi.one_apply,
    mul_one] at h1
  rw [← lintegral_indicator _ hA, ← h1]
  exact Ennreal.mul_ne_top hμs h3A.ne
#align measure_theory.ae_measure_preimage_mul_right_lt_top MeasureTheory.ae_measure_preimage_mul_right_lt_top
#align measure_theory.ae_measure_preimage_add_right_lt_top MeasureTheory.ae_measure_preimage_add_right_lt_top

@[to_additive]
theorem ae_measure_preimage_mul_right_lt_top_of_ne_zero [IsMulLeftInvariant ν]
    (sm : MeasurableSet s) (h2s : ν s ≠ 0) (h3s : ν s ≠ ∞) :
    ∀ᵐ x ∂μ, ν ((fun y => y * x) ⁻¹' s) < ∞ :=
  by
  refine' (ae_measure_preimage_mul_right_lt_top ν ν sm h3s).filter_mono _
  refine' (absolutely_continuous_of_is_mul_left_invariant μ ν _).ae_le
  refine' mt _ h2s
  intro hν
  rw [hν, measure.coe_zero, Pi.zero_apply]
#align measure_theory.ae_measure_preimage_mul_right_lt_top_of_ne_zero MeasureTheory.ae_measure_preimage_mul_right_lt_top_of_ne_zero
#align measure_theory.ae_measure_preimage_add_right_lt_top_of_ne_zero MeasureTheory.ae_measure_preimage_add_right_lt_top_of_ne_zero

/-- A technical lemma relating two different measures. This is basically [Halmos, §60 Th. A].
  Note that if `f` is the characteristic function of a measurable set `t` this states that
  `μ t = c * μ s` for a constant `c` that does not depend on `μ`.

  Note: There is a gap in the last step of the proof in [Halmos].
  In the last line, the equality `g(x⁻¹)ν(sx⁻¹) = f(x)` holds if we can prove that
  `0 < ν(sx⁻¹) < ∞`. The first inequality follows from §59, Th. D, but the second inequality is
  not justified. We prove this inequality for almost all `x` in
  `measure_theory.ae_measure_preimage_mul_right_lt_top_of_ne_zero`. -/
@[to_additive
      "A technical lemma relating two different measures. This is basically\n[Halmos, §60 Th. A]. Note that if `f` is the characteristic function of a measurable set `t` this\nstates that `μ t = c * μ s` for a constant `c` that does not depend on `μ`.\n\nNote: There is a gap in the last step of the proof in [Halmos]. In the last line, the equality\n`g(-x) + ν(s - x) = f(x)` holds if we can prove that `0 < ν(s - x) < ∞`. The first inequality\nfollows from §59, Th. D, but the second inequality is not justified. We prove this inequality for\nalmost all `x` in `measure_theory.ae_measure_preimage_add_right_lt_top_of_ne_zero`."]
theorem measure_lintegral_div_measure [IsMulLeftInvariant ν] (sm : MeasurableSet s) (h2s : ν s ≠ 0)
    (h3s : ν s ≠ ∞) (f : G → ℝ≥0∞) (hf : Measurable f) :
    (μ s * ∫⁻ y, f y⁻¹ / ν ((fun x => x * y⁻¹) ⁻¹' s) ∂ν) = ∫⁻ x, f x ∂μ :=
  by
  set g := fun y => f y⁻¹ / ν ((fun x => x * y⁻¹) ⁻¹' s)
  have hg : Measurable g :=
    (hf.comp measurable_inv).div ((measurable_measure_mul_right ν sm).comp measurable_inv)
  simp_rw [measure_mul_lintegral_eq μ ν sm g hg, g, inv_inv]
  refine' lintegral_congr_ae _
  refine' (ae_measure_preimage_mul_right_lt_top_of_ne_zero μ ν sm h2s h3s).mono fun x hx => _
  simp_rw [Ennreal.mul_div_cancel' (measure_mul_right_ne_zero ν h2s _) hx.ne]
#align measure_theory.measure_lintegral_div_measure MeasureTheory.measure_lintegral_div_measure
#align measure_theory.measure_lintegral_sub_measure MeasureTheory.measure_lintegral_sub_measure

@[to_additive]
theorem measure_mul_measure_eq [IsMulLeftInvariant ν] {s t : Set G} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h2s : ν s ≠ 0) (h3s : ν s ≠ ∞) : μ s * ν t = ν s * μ t :=
  by
  have h1 :=
    measure_lintegral_div_measure ν ν hs h2s h3s (t.indicator fun x => 1)
      (measurable_const.indicator ht)
  have h2 :=
    measure_lintegral_div_measure μ ν hs h2s h3s (t.indicator fun x => 1)
      (measurable_const.indicator ht)
  rw [lintegral_indicator _ ht, set_lintegral_one] at h1 h2
  rw [← h1, mul_left_comm, h2]
#align measure_theory.measure_mul_measure_eq MeasureTheory.measure_mul_measure_eq
#align measure_theory.measure_add_measure_eq MeasureTheory.measure_add_measure_eq

/-- Left invariant Borel measures on a measurable group are unique (up to a scalar). -/
@[to_additive
      " Left invariant Borel measures on an additive measurable group are unique\n  (up to a scalar). "]
theorem measure_eq_div_smul [IsMulLeftInvariant ν] (hs : MeasurableSet s) (h2s : ν s ≠ 0)
    (h3s : ν s ≠ ∞) : μ = (μ s / ν s) • ν := by
  ext1 t ht
  rw [smul_apply, smul_eq_mul, mul_comm, ← mul_div_assoc, mul_comm,
    measure_mul_measure_eq μ ν hs ht h2s h3s, mul_div_assoc, Ennreal.mul_div_cancel' h2s h3s]
#align measure_theory.measure_eq_div_smul MeasureTheory.measure_eq_div_smul
#align measure_theory.measure_eq_sub_vadd MeasureTheory.measure_eq_sub_vadd

end LeftInvariant

section RightInvariant

@[to_additive measure_preserving_prod_add_right]
theorem measurePreservingProdMulRight [IsMulRightInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.2 * z.1)) (μ.Prod ν) (μ.Prod ν) :=
  (MeasurePreserving.id μ).skewProduct (measurable_snd.mul measurable_fst) <|
    Filter.eventually_of_forall <| map_mul_right_eq_self ν
#align measure_theory.measure_preserving_prod_mul_right MeasureTheory.measurePreservingProdMulRight
#align measure_theory.measure_preserving_prod_add_right MeasureTheory.measure_preserving_prod_add_right

/-- The map `(x, y) ↦ (y, xy)` sends the measure `μ × ν` to `ν × μ`. -/
@[to_additive measure_preserving_prod_add_swap_right
      " The map `(x, y) ↦ (y, x + y)` sends the measure `μ × ν` to `ν × μ`. "]
theorem measurePreservingProdMulSwapRight [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.2, z.1 * z.2)) (μ.Prod ν) (ν.Prod μ) :=
  (measurePreservingProdMulRight ν μ).comp measurePreservingSwap
#align measure_theory.measure_preserving_prod_mul_swap_right MeasureTheory.measurePreservingProdMulSwapRight
#align measure_theory.measure_preserving_prod_add_swap_right MeasureTheory.measure_preserving_prod_add_swap_right

/-- The map `(x, y) ↦ (xy, y)` preserves the measure `μ × ν`. -/
@[to_additive measure_preserving_add_prod
      " The map `(x, y) ↦ (x + y, y)` preserves the measure `μ × ν`. "]
theorem measurePreservingMulProd [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.1 * z.2, z.2)) (μ.Prod ν) (μ.Prod ν) :=
  measurePreservingSwap.comp <| by apply measure_preserving_prod_mul_swap_right μ ν
#align measure_theory.measure_preserving_mul_prod MeasureTheory.measurePreservingMulProd
#align measure_theory.measure_preserving_add_prod MeasureTheory.measure_preserving_add_prod

variable [HasMeasurableInv G]

/-- The map `(x, y) ↦ (x, y / x)` is measure-preserving. -/
@[to_additive measure_preserving_prod_sub "The map `(x, y) ↦ (x, y - x)` is measure-preserving."]
theorem measurePreservingProdDiv [IsMulRightInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1, z.2 / z.1)) (μ.Prod ν) (μ.Prod ν) :=
  (measurePreservingProdMulRight μ ν).symm (MeasurableEquiv.shearDivRight G).symm
#align measure_theory.measure_preserving_prod_div MeasureTheory.measurePreservingProdDiv
#align measure_theory.measure_preserving_prod_sub MeasureTheory.measure_preserving_prod_sub

/-- The map `(x, y) ↦ (y, x / y)` sends `μ × ν` to `ν × μ`. -/
@[to_additive measure_preserving_prod_sub_swap
      "The map `(x, y) ↦ (y, x - y)` sends `μ × ν` to `ν × μ`."]
theorem measurePreservingProdDivSwap [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.2, z.1 / z.2)) (μ.Prod ν) (ν.Prod μ) :=
  (measurePreservingProdDiv ν μ).comp measurePreservingSwap
#align measure_theory.measure_preserving_prod_div_swap MeasureTheory.measurePreservingProdDivSwap
#align measure_theory.measure_preserving_prod_sub_swap MeasureTheory.measure_preserving_prod_sub_swap

/-- The map `(x, y) ↦ (x / y, y)` preserves the measure `μ × ν`. -/
@[to_additive measure_preserving_sub_prod
      " The map `(x, y) ↦ (x - y, y)` preserves the measure `μ × ν`. "]
theorem measurePreservingDivProd [IsMulRightInvariant μ] :
    MeasurePreserving (fun z : G × G => (z.1 / z.2, z.2)) (μ.Prod ν) (μ.Prod ν) :=
  measurePreservingSwap.comp <| by apply measure_preserving_prod_div_swap μ ν
#align measure_theory.measure_preserving_div_prod MeasureTheory.measurePreservingDivProd
#align measure_theory.measure_preserving_sub_prod MeasureTheory.measure_preserving_sub_prod

/-- The map `(x, y) ↦ (xy, x⁻¹)` is measure-preserving. -/
@[to_additive measure_preserving_add_prod_neg_right
      "The map `(x, y) ↦ (x + y, - x)` is measure-preserving."]
theorem measurePreservingMulProdInvRight [IsMulRightInvariant μ] [IsMulRightInvariant ν] :
    MeasurePreserving (fun z : G × G => (z.1 * z.2, z.1⁻¹)) (μ.Prod ν) (μ.Prod ν) :=
  by
  convert (measure_preserving_prod_div_swap ν μ).comp (measure_preserving_prod_mul_swap_right μ ν)
  ext1 ⟨x, y⟩
  simp_rw [Function.comp_apply, div_mul_eq_div_div_swap, div_self', one_div]
#align measure_theory.measure_preserving_mul_prod_inv_right MeasureTheory.measurePreservingMulProdInvRight
#align measure_theory.measure_preserving_add_prod_neg_right MeasureTheory.measure_preserving_add_prod_neg_right

end RightInvariant

section QuasiMeasurePreserving

variable [HasMeasurableInv G]

@[to_additive]
theorem quasiMeasurePreservingInvOfRightInvariant [IsMulRightInvariant μ] :
    QuasiMeasurePreserving (Inv.inv : G → G) μ μ :=
  by
  rw [← μ.inv_inv]
  exact
    (quasi_measure_preserving_inv μ.inv).mono (inv_absolutely_continuous μ.inv)
      (absolutely_continuous_inv μ.inv)
#align measure_theory.quasi_measure_preserving_inv_of_right_invariant MeasureTheory.quasiMeasurePreservingInvOfRightInvariant
#align measure_theory.quasi_measure_preserving_neg_of_right_invariant MeasureTheory.quasi_measure_preserving_neg_of_right_invariant

@[to_additive]
theorem quasiMeasurePreservingDivLeft [IsMulLeftInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => g / h) μ μ :=
  by
  simp_rw [div_eq_mul_inv]
  exact
    (measure_preserving_mul_left μ g).QuasiMeasurePreserving.comp (quasi_measure_preserving_inv μ)
#align measure_theory.quasi_measure_preserving_div_left MeasureTheory.quasiMeasurePreservingDivLeft
#align measure_theory.quasi_measure_preserving_sub_left MeasureTheory.quasi_measure_preserving_sub_left

@[to_additive]
theorem quasiMeasurePreservingDivLeftOfRightInvariant [IsMulRightInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => g / h) μ μ :=
  by
  rw [← μ.inv_inv]
  exact
    (quasi_measure_preserving_div_left μ.inv g).mono (inv_absolutely_continuous μ.inv)
      (absolutely_continuous_inv μ.inv)
#align measure_theory.quasi_measure_preserving_div_left_of_right_invariant MeasureTheory.quasiMeasurePreservingDivLeftOfRightInvariant
#align measure_theory.quasi_measure_preserving_sub_left_of_right_invariant MeasureTheory.quasi_measure_preserving_sub_left_of_right_invariant

@[to_additive]
theorem quasiMeasurePreservingDivOfRightInvariant [IsMulRightInvariant μ] :
    QuasiMeasurePreserving (fun p : G × G => p.1 / p.2) (μ.Prod ν) μ :=
  by
  refine' quasi_measure_preserving.prod_of_left measurable_div (eventually_of_forall fun y => _)
  exact (measure_preserving_div_right μ y).QuasiMeasurePreserving
#align measure_theory.quasi_measure_preserving_div_of_right_invariant MeasureTheory.quasiMeasurePreservingDivOfRightInvariant
#align measure_theory.quasi_measure_preserving_sub_of_right_invariant MeasureTheory.quasi_measure_preserving_sub_of_right_invariant

@[to_additive]
theorem quasiMeasurePreservingDiv [IsMulLeftInvariant μ] :
    QuasiMeasurePreserving (fun p : G × G => p.1 / p.2) (μ.Prod ν) μ :=
  (quasiMeasurePreservingDivOfRightInvariant μ.inv ν).mono
    ((absolutelyContinuousInv μ).Prod AbsolutelyContinuous.rfl) (invAbsolutelyContinuous μ)
#align measure_theory.quasi_measure_preserving_div MeasureTheory.quasiMeasurePreservingDiv
#align measure_theory.quasi_measure_preserving_sub MeasureTheory.quasi_measure_preserving_sub

/-- A *left*-invariant measure is quasi-preserved by *right*-multiplication.
This should not be confused with `(measure_preserving_mul_right μ g).quasi_measure_preserving`. -/
@[to_additive
      "A *left*-invariant measure is quasi-preserved by *right*-addition.\nThis should not be confused with `(measure_preserving_add_right μ g).quasi_measure_preserving`. "]
theorem quasiMeasurePreservingMulRight [IsMulLeftInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => h * g) μ μ :=
  by
  refine' ⟨measurable_mul_const g, absolutely_continuous.mk fun s hs => _⟩
  rw [map_apply (measurable_mul_const g) hs, measure_mul_right_null]; exact id
#align measure_theory.quasi_measure_preserving_mul_right MeasureTheory.quasiMeasurePreservingMulRight
#align measure_theory.quasi_measure_preserving_add_right MeasureTheory.quasi_measure_preserving_add_right

/-- A *right*-invariant measure is quasi-preserved by *left*-multiplication.
This should not be confused with `(measure_preserving_mul_left μ g).quasi_measure_preserving`. -/
@[to_additive
      "A *right*-invariant measure is quasi-preserved by *left*-addition.\nThis should not be confused with `(measure_preserving_add_left μ g).quasi_measure_preserving`. "]
theorem quasiMeasurePreservingMulLeft [IsMulRightInvariant μ] (g : G) :
    QuasiMeasurePreserving (fun h : G => g * h) μ μ :=
  by
  have :=
    (quasi_measure_preserving_mul_right μ.inv g⁻¹).mono (inv_absolutely_continuous μ.inv)
      (absolutely_continuous_inv μ.inv)
  rw [μ.inv_inv] at this
  have :=
    (quasi_measure_preserving_inv_of_right_invariant μ).comp
      (this.comp (quasi_measure_preserving_inv_of_right_invariant μ))
  simp_rw [Function.comp, mul_inv_rev, inv_inv] at this
  exact this
#align measure_theory.quasi_measure_preserving_mul_left MeasureTheory.quasiMeasurePreservingMulLeft
#align measure_theory.quasi_measure_preserving_add_left MeasureTheory.quasi_measure_preserving_add_left

end QuasiMeasurePreserving

end MeasureTheory

