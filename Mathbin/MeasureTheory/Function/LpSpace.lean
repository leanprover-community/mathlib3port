import Mathbin.Analysis.NormedSpace.IndicatorFunction 
import Mathbin.Analysis.Normed.Group.Hom 
import Mathbin.MeasureTheory.Function.EssSup 
import Mathbin.MeasureTheory.Function.AeEqFun 
import Mathbin.MeasureTheory.Integral.MeanInequalities 
import Mathbin.Topology.ContinuousFunction.Compact

/-!
# ℒp space and Lp space

This file describes properties of almost everywhere measurable functions with finite seminorm,
denoted by `snorm f p μ` and defined for `p:ℝ≥0∞` as `0` if `p=0`, `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for
`0 < p < ∞` and `ess_sup ∥f∥ μ` for `p=∞`.

The Prop-valued `mem_ℒp f p μ` states that a function `f : α → E` has finite seminorm.
The space `Lp E p μ` is the subtype of elements of `α →ₘ[μ] E` (see ae_eq_fun) such that
`snorm f p μ` is finite. For `1 ≤ p`, `snorm` defines a norm and `Lp` is a complete metric space.

## Main definitions

* `snorm' f p μ` : `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a  measurable
  space and `F` is a normed group.
* `snorm_ess_sup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `ess_sup ∥f∥ μ`.
* `snorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `snorm' f p μ`
  for `0 < p < ∞` and to `snorm_ess_sup f μ` for `p = ∞`.

* `mem_ℒp f p μ` : property that the function `f` is almost everywhere measurable and has finite
  p-seminorm for measure `μ` (`snorm f p μ < ∞`)
* `Lp E p μ` : elements of `α →ₘ[μ] E` (see ae_eq_fun) such that `snorm f p μ` is finite. Defined
  as an `add_subgroup` of `α →ₘ[μ] E`.

Lipschitz functions vanishing at zero act by composition on `Lp`. We define this action, and prove
that it is continuous. In particular,
* `continuous_linear_map.comp_Lp` defines the action on `Lp` of a continuous linear map.
* `Lp.pos_part` is the positive part of an `Lp` function.
* `Lp.neg_part` is the negative part of an `Lp` function.

When `α` is a topological space equipped with a finite Borel measure, there is a bounded linear map
from the normed space of bounded continuous functions (`α →ᵇ E`) to `Lp E p μ`.  We construct this
as `bounded_continuous_function.to_Lp`.

## Notations

* `α →₁[μ] E` : the type `Lp E 1 μ`.
* `α →₂[μ] E` : the type `Lp E 2 μ`.

## Implementation

Since `Lp` is defined as an `add_subgroup`, dot notation does not work. Use `Lp.measurable f` to
say that the coercion of `f` to a genuine function is measurable, instead of the non-working
`f.measurable`.

To prove that two `Lp` elements are equal, it suffices to show that their coercions to functions
coincide almost everywhere (this is registered as an `ext` rule). This can often be done using
`filter_upwards`. For instance, a proof from first principles that `f + (g + h) = (f + g) + h`
could read (in the `Lp` namespace)
```
example (f g h : Lp E p μ) : (f + g) + h = f + (g + h) :=
begin
  ext1,
  filter_upwards [coe_fn_add (f + g) h, coe_fn_add f g, coe_fn_add f (g + h), coe_fn_add g h],
  assume a ha1 ha2 ha3 ha4,
  simp only [ha1, ha2, ha3, ha4, add_assoc],
end
```
The lemma `coe_fn_add` states that the coercion of `f + g` coincides almost everywhere with the sum
of the coercions of `f` and `g`. All such lemmas use `coe_fn` in their name, to distinguish the
function coercion from the coercion to almost everywhere defined functions.
-/


noncomputable theory

open TopologicalSpace MeasureTheory Filter

open_locale Nnreal Ennreal BigOperators TopologicalSpace MeasureTheory

theorem fact_one_le_one_ennreal : Fact ((1 : ℝ≥0∞) ≤ 1) :=
  ⟨le_reflₓ _⟩

theorem fact_one_le_two_ennreal : Fact ((1 : ℝ≥0∞) ≤ 2) :=
  ⟨Ennreal.coe_le_coe.2
      (show (1 :  ℝ≥0 ) ≤ 2by 
        normNum)⟩

theorem fact_one_le_top_ennreal : Fact ((1 : ℝ≥0∞) ≤ ∞) :=
  ⟨le_top⟩

attribute [local instance] fact_one_le_one_ennreal fact_one_le_two_ennreal fact_one_le_top_ennreal

variable{α E F G :
    Type
      _}{m m0 :
    MeasurableSpace
      α}{p : ℝ≥0∞}{q : ℝ}{μ ν : Measureₓ α}[MeasurableSpace E][NormedGroup E][NormedGroup F][NormedGroup G]

namespace MeasureTheory

section ℒp

/-!
### ℒp seminorm

We define the ℒp seminorm, denoted by `snorm f p μ`. For real `p`, it is given by an integral
formula (for which we use the notation `snorm' f p μ`), and for `p = ∞` it is the essential
supremum (for which we use the notation `snorm_ess_sup f μ`).

We also define a predicate `mem_ℒp f p μ`, requesting that a function is almost everywhere
measurable and has finite `snorm f p μ`.

This paragraph is devoted to the basic properties of these definitions. It is constructed as
follows: for a given property, we prove it for `snorm'` and `snorm_ess_sup` when it makes sense,
deduce it for `snorm`, and translate it in terms of `mem_ℒp`.
-/


section ℒpSpaceDefinition

/-- `(∫ ∥f a∥^q ∂μ) ^ (1/q)`, which is a seminorm on the space of measurable functions for which
this quantity is finite -/
def snorm' {m : MeasurableSpace α} (f : α → F) (q : ℝ) (μ : Measureₓ α) : ℝ≥0∞ :=
  (∫⁻a, nnnorm (f a)^q ∂μ)^1 / q

/-- seminorm for `ℒ∞`, equal to the essential supremum of `∥f∥`. -/
def snorm_ess_sup {m : MeasurableSpace α} (f : α → F) (μ : Measureₓ α) :=
  essSup (fun x => (nnnorm (f x) : ℝ≥0∞)) μ

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`ess_sup ∥f∥ μ` for `p = ∞`. -/
def snorm {m : MeasurableSpace α} (f : α → F) (p : ℝ≥0∞) (μ : Measureₓ α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then snorm_ess_sup f μ else snorm' f (Ennreal.toReal p) μ

theorem snorm_eq_snorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → F} :
  snorm f p μ = snorm' f (Ennreal.toReal p) μ :=
  by 
    simp [snorm, hp_ne_zero, hp_ne_top]

theorem snorm_eq_lintegral_rpow_nnnorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → F} :
  snorm f p μ = ((∫⁻x, nnnorm (f x)^p.to_real ∂μ)^1 / p.to_real) :=
  by 
    rw [snorm_eq_snorm' hp_ne_zero hp_ne_top, snorm']

theorem snorm_one_eq_lintegral_nnnorm {f : α → F} : snorm f 1 μ = ∫⁻x, nnnorm (f x) ∂μ :=
  by 
    simpRw [snorm_eq_lintegral_rpow_nnnorm one_ne_zero Ennreal.coe_ne_top, Ennreal.one_to_real, one_div_one,
      Ennreal.rpow_one]

@[simp]
theorem snorm_exponent_top {f : α → F} : snorm f ∞ μ = snorm_ess_sup f μ :=
  by 
    simp [snorm]

/-- The property that `f:α→E` is ae_measurable and `(∫ ∥f a∥^p ∂μ)^(1/p)` is finite if `p < ∞`, or
`ess_sup f < ∞` if `p = ∞`. -/
def mem_ℒp {α} {m : MeasurableSpace α} (f : α → E) (p : ℝ≥0∞) (μ : Measureₓ α) : Prop :=
  AeMeasurable f μ ∧ snorm f p μ < ∞

theorem mem_ℒp.ae_measurable {f : α → E} {p : ℝ≥0∞} (h : mem_ℒp f p μ) : AeMeasurable f μ :=
  h.1

theorem lintegral_rpow_nnnorm_eq_rpow_snorm' {f : α → F} (hq0_lt : 0 < q) :
  (∫⁻a, nnnorm (f a)^q ∂μ) = (snorm' f q μ^q) :=
  by 
    rw [snorm', ←Ennreal.rpow_mul, one_div, inv_mul_cancel, Ennreal.rpow_one]
    exact (ne_of_ltₓ hq0_lt).symm

end ℒpSpaceDefinition

section Top

theorem mem_ℒp.snorm_lt_top {f : α → E} (hfp : mem_ℒp f p μ) : snorm f p μ < ∞ :=
  hfp.2

theorem mem_ℒp.snorm_ne_top {f : α → E} (hfp : mem_ℒp f p μ) : snorm f p μ ≠ ∞ :=
  ne_of_ltₓ hfp.2

theorem lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top {f : α → F} (hq0_lt : 0 < q) (hfq : snorm' f q μ < ∞) :
  (∫⁻a, nnnorm (f a)^q ∂μ) < ∞ :=
  by 
    rw [lintegral_rpow_nnnorm_eq_rpow_snorm' hq0_lt]
    exact Ennreal.rpow_lt_top_of_nonneg (le_of_ltₓ hq0_lt) (ne_of_ltₓ hfq)

theorem lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top {f : α → F} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
  (hfp : snorm f p μ < ∞) : (∫⁻a, nnnorm (f a)^p.to_real ∂μ) < ∞ :=
  by 
    apply lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top
    ·
      exact ennreal.to_real_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr hp_ne_zero, hp_ne_top⟩
    ·
      simpa [snorm_eq_snorm' hp_ne_zero hp_ne_top] using hfp

theorem snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top {f : α → F} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  snorm f p μ < ∞ ↔ (∫⁻a, nnnorm (f a)^p.to_real ∂μ) < ∞ :=
  ⟨lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp_ne_zero hp_ne_top,
    by 
      intro h 
      have hp' := ennreal.to_real_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr hp_ne_zero, hp_ne_top⟩
      have  : 0 < 1 / p.to_real := div_pos zero_lt_one hp' 
      simpa [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top] using
        Ennreal.rpow_lt_top_of_nonneg (le_of_ltₓ this) (ne_of_ltₓ h)⟩

end Top

section Zero

@[simp]
theorem snorm'_exponent_zero {f : α → F} : snorm' f 0 μ = 1 :=
  by 
    rw [snorm', div_zero, Ennreal.rpow_zero]

@[simp]
theorem snorm_exponent_zero {f : α → F} : snorm f 0 μ = 0 :=
  by 
    simp [snorm]

theorem mem_ℒp_zero_iff_ae_measurable {f : α → E} : mem_ℒp f 0 μ ↔ AeMeasurable f μ :=
  by 
    simp [mem_ℒp, snorm_exponent_zero]

@[simp]
theorem snorm'_zero (hp0_lt : 0 < q) : snorm' (0 : α → F) q μ = 0 :=
  by 
    simp [snorm', hp0_lt]

@[simp]
theorem snorm'_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) : snorm' (0 : α → F) q μ = 0 :=
  by 
    cases' le_or_ltₓ 0 q with hq0 hq_neg
    ·
      exact snorm'_zero (lt_of_le_of_neₓ hq0 hq0_ne.symm)
    ·
      simp [snorm', Ennreal.rpow_eq_zero_iff, hμ, hq_neg]

@[simp]
theorem snorm_ess_sup_zero : snorm_ess_sup (0 : α → F) μ = 0 :=
  by 
    simpRw [snorm_ess_sup, Pi.zero_apply, nnnorm_zero, Ennreal.coe_zero, ←Ennreal.bot_eq_zero]
    exact ess_sup_const_bot

@[simp]
theorem snorm_zero : snorm (0 : α → F) p μ = 0 :=
  by 
    byCases' h0 : p = 0
    ·
      simp [h0]
    byCases' h_top : p = ∞
    ·
      simp only [h_top, snorm_exponent_top, snorm_ess_sup_zero]
    rw [←Ne.def] at h0 
    simp [snorm_eq_snorm' h0 h_top, ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_neₓ (zero_le _) h0.symm, h_top⟩]

@[simp]
theorem snorm_zero' : snorm (fun x : α => (0 : F)) p μ = 0 :=
  by 
    convert snorm_zero

theorem zero_mem_ℒp : mem_ℒp (0 : α → E) p μ :=
  ⟨measurable_zero.AeMeasurable,
    by 
      rw [snorm_zero]
      exact Ennreal.coe_lt_top⟩

theorem zero_mem_ℒp' : mem_ℒp (fun x : α => (0 : E)) p μ :=
  by 
    convert zero_mem_ℒp

variable[MeasurableSpace α]

theorem snorm'_measure_zero_of_pos {f : α → F} (hq_pos : 0 < q) : snorm' f q (0 : Measureₓ α) = 0 :=
  by 
    simp [snorm', hq_pos]

theorem snorm'_measure_zero_of_exponent_zero {f : α → F} : snorm' f 0 (0 : Measureₓ α) = 1 :=
  by 
    simp [snorm']

theorem snorm'_measure_zero_of_neg {f : α → F} (hq_neg : q < 0) : snorm' f q (0 : Measureₓ α) = ∞ :=
  by 
    simp [snorm', hq_neg]

@[simp]
theorem snorm_ess_sup_measure_zero {f : α → F} : snorm_ess_sup f (0 : Measureₓ α) = 0 :=
  by 
    simp [snorm_ess_sup]

@[simp]
theorem snorm_measure_zero {f : α → F} : snorm f p (0 : Measureₓ α) = 0 :=
  by 
    byCases' h0 : p = 0
    ·
      simp [h0]
    byCases' h_top : p = ∞
    ·
      simp [h_top]
    rw [←Ne.def] at h0 
    simp [snorm_eq_snorm' h0 h_top, snorm', ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_neₓ (zero_le _) h0.symm, h_top⟩]

end Zero

section Const

theorem snorm'_const (c : F) (hq_pos : 0 < q) : snorm' (fun x : α => c) q μ = (nnnorm c : ℝ≥0∞)*μ Set.Univ^1 / q :=
  by 
    rw [snorm', lintegral_const,
      Ennreal.mul_rpow_of_nonneg _ _
        (by 
          simp [hq_pos.le] :
        0 ≤ 1 / q)]
    congr 
    rw [←Ennreal.rpow_mul]
    suffices hq_cancel : (q*1 / q) = 1
    ·
      rw [hq_cancel, Ennreal.rpow_one]
    rw [one_div, mul_inv_cancel (ne_of_ltₓ hq_pos).symm]

theorem snorm'_const' [is_finite_measure μ] (c : F) (hc_ne_zero : c ≠ 0) (hq_ne_zero : q ≠ 0) :
  snorm' (fun x : α => c) q μ = (nnnorm c : ℝ≥0∞)*μ Set.Univ^1 / q :=
  by 
    rw [snorm', lintegral_const, Ennreal.mul_rpow_of_ne_top _ (measure_ne_top μ Set.Univ)]
    ·
      congr 
      rw [←Ennreal.rpow_mul]
      suffices hp_cancel : (q*1 / q) = 1
      ·
        rw [hp_cancel, Ennreal.rpow_one]
      rw [one_div, mul_inv_cancel hq_ne_zero]
    ·
      rw [Ne.def, Ennreal.rpow_eq_top_iff, Auto.not_or_eq, Auto.not_and_eq, Auto.not_and_eq]
      split 
      ·
        left 
        rwa [Ennreal.coe_eq_zero, nnnorm_eq_zero]
      ·
        exact Or.inl Ennreal.coe_ne_top

theorem snorm_ess_sup_const (c : F) (hμ : μ ≠ 0) : snorm_ess_sup (fun x : α => c) μ = (nnnorm c : ℝ≥0∞) :=
  by 
    rw [snorm_ess_sup, ess_sup_const _ hμ]

theorem snorm'_const_of_is_probability_measure (c : F) (hq_pos : 0 < q) [is_probability_measure μ] :
  snorm' (fun x : α => c) q μ = (nnnorm c : ℝ≥0∞) :=
  by 
    simp [snorm'_const c hq_pos, measure_univ]

theorem snorm_const (c : F) (h0 : p ≠ 0) (hμ : μ ≠ 0) :
  snorm (fun x : α => c) p μ = (nnnorm c : ℝ≥0∞)*μ Set.Univ^1 / Ennreal.toReal p :=
  by 
    byCases' h_top : p = ∞
    ·
      simp [h_top, snorm_ess_sup_const c hμ]
    simp [snorm_eq_snorm' h0 h_top, snorm'_const,
      ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_neₓ (zero_le _) h0.symm, h_top⟩]

theorem snorm_const' (c : F) (h0 : p ≠ 0) (h_top : p ≠ ∞) :
  snorm (fun x : α => c) p μ = (nnnorm c : ℝ≥0∞)*μ Set.Univ^1 / Ennreal.toReal p :=
  by 
    simp [snorm_eq_snorm' h0 h_top, snorm'_const,
      ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_neₓ (zero_le _) h0.symm, h_top⟩]

theorem snorm_const_lt_top_iff {p : ℝ≥0∞} {c : F} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  snorm (fun x : α => c) p μ < ∞ ↔ c = 0 ∨ μ Set.Univ < ∞ :=
  by 
    have hp : 0 < p.to_real 
    exact ennreal.to_real_pos_iff.mpr ⟨hp_ne_zero.bot_lt, hp_ne_top⟩
    byCases' hμ : μ = 0
    ·
      simp only [hμ, measure.coe_zero, Pi.zero_apply, or_trueₓ, WithTop.zero_lt_top, snorm_measure_zero]
    byCases' hc : c = 0
    ·
      simp only [hc, true_orₓ, eq_self_iff_true, WithTop.zero_lt_top, snorm_zero']
    rw [snorm_const' c hp_ne_zero hp_ne_top]
    byCases' hμ_top : μ Set.Univ = ∞
    ·
      simp [hc, hμ_top, hp]
    rw [Ennreal.mul_lt_top_iff]
    simp only [true_andₓ, one_div, Ennreal.rpow_eq_zero_iff, hμ, false_orₓ, or_falseₓ, Ennreal.coe_lt_top,
      nnnorm_eq_zero, Ennreal.coe_eq_zero, MeasureTheory.Measure.measure_univ_eq_zero, hp, inv_lt_zero, hc, and_falseₓ,
      false_andₓ, _root_.inv_pos, or_selfₓ, hμ_top, Ne.lt_top hμ_top, iff_trueₓ]
    exact Ennreal.rpow_lt_top_of_nonneg (inv_nonneg.mpr hp.le) hμ_top

theorem mem_ℒp_const (c : E) [is_finite_measure μ] : mem_ℒp (fun a : α => c) p μ :=
  by 
    refine' ⟨measurable_const.ae_measurable, _⟩
    byCases' h0 : p = 0
    ·
      simp [h0]
    byCases' hμ : μ = 0
    ·
      simp [hμ]
    rw [snorm_const c h0 hμ]
    refine' Ennreal.mul_lt_top Ennreal.coe_ne_top _ 
    refine' (Ennreal.rpow_lt_top_of_nonneg _ (measure_ne_top μ Set.Univ)).Ne 
    simp 

theorem mem_ℒp_const_iff {p : ℝ≥0∞} {c : E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  mem_ℒp (fun x : α => c) p μ ↔ c = 0 ∨ μ Set.Univ < ∞ :=
  by 
    rw [←snorm_const_lt_top_iff hp_ne_zero hp_ne_top]
    exact ⟨fun h => h.2, fun h => ⟨ae_measurable_const, h⟩⟩

end Const

theorem snorm'_mono_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐx ∂μ, ∥f x∥ ≤ ∥g x∥) : snorm' f q μ ≤ snorm' g q μ :=
  by 
    rw [snorm']
    refine' Ennreal.rpow_le_rpow _ (one_div_nonneg.2 hq)
    refine' lintegral_mono_ae (h.mono$ fun x hx => _)
    exact Ennreal.rpow_le_rpow (Ennreal.coe_le_coe.2 hx) hq

theorem snorm'_congr_norm_ae {f g : α → F} (hfg : ∀ᵐx ∂μ, ∥f x∥ = ∥g x∥) : snorm' f q μ = snorm' g q μ :=
  by 
    have  : (fun x => (nnnorm (f x)^q : ℝ≥0∞)) =ᵐ[μ] fun x => nnnorm (g x)^q 
    exact
      hfg.mono
        fun x hx =>
          by 
            simp only [←coe_nnnorm, Nnreal.coe_eq] at hx 
            simp [hx]
    simp only [snorm', lintegral_congr_ae this]

theorem snorm'_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm' f q μ = snorm' g q μ :=
  snorm'_congr_norm_ae (hfg.fun_comp _)

theorem snorm_ess_sup_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm_ess_sup f μ = snorm_ess_sup g μ :=
  ess_sup_congr_ae (hfg.fun_comp (coeₓ ∘ nnnorm))

theorem snorm_mono_ae {f : α → F} {g : α → G} (h : ∀ᵐx ∂μ, ∥f x∥ ≤ ∥g x∥) : snorm f p μ ≤ snorm g p μ :=
  by 
    simp only [snorm]
    splitIfs
    ·
      exact le_rfl
    ·
      refine' ess_sup_mono_ae (h.mono$ fun x hx => _)
      exactModCast hx
    ·
      exact snorm'_mono_ae Ennreal.to_real_nonneg h

theorem snorm_mono_ae_real {f : α → F} {g : α → ℝ} (h : ∀ᵐx ∂μ, ∥f x∥ ≤ g x) : snorm f p μ ≤ snorm g p μ :=
  snorm_mono_ae$ h.mono fun x hx => hx.trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)

theorem snorm_mono {f : α → F} {g : α → G} (h : ∀ x, ∥f x∥ ≤ ∥g x∥) : snorm f p μ ≤ snorm g p μ :=
  snorm_mono_ae (eventually_of_forall fun x => h x)

theorem snorm_mono_real {f : α → F} {g : α → ℝ} (h : ∀ x, ∥f x∥ ≤ g x) : snorm f p μ ≤ snorm g p μ :=
  snorm_mono_ae_real (eventually_of_forall fun x => h x)

theorem snorm_ess_sup_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐx ∂μ, ∥f x∥ ≤ C) :
  snorm_ess_sup f μ ≤ Ennreal.ofReal C :=
  by 
    simpRw [snorm_ess_sup, ←of_real_norm_eq_coe_nnnorm]
    refine' ess_sup_le_of_ae_le (Ennreal.ofReal C) (hfC.mono fun x hx => _)
    exact Ennreal.of_real_le_of_real hx

theorem snorm_ess_sup_lt_top_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐx ∂μ, ∥f x∥ ≤ C) : snorm_ess_sup f μ < ∞ :=
  (snorm_ess_sup_le_of_ae_bound hfC).trans_lt Ennreal.of_real_lt_top

theorem snorm_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐx ∂μ, ∥f x∥ ≤ C) :
  snorm f p μ ≤ (μ Set.Univ^p.to_real⁻¹)*Ennreal.ofReal C :=
  by 
    byCases' hμ : μ = 0
    ·
      simp [hμ]
    haveI  : μ.ae.ne_bot := ae_ne_bot.mpr hμ 
    byCases' hp : p = 0
    ·
      simp [hp]
    have hC : 0 ≤ C 
    exact le_transₓ (norm_nonneg _) hfC.exists.some_spec 
    have hC' : ∥C∥ = C :=
      by 
        rw [Real.norm_eq_abs, abs_eq_self.mpr hC]
    have  : ∀ᵐx ∂μ, ∥f x∥ ≤ ∥(fun _ => C) x∥
    exact hfC.mono fun x hx => hx.trans (le_of_eqₓ hC'.symm)
    convert snorm_mono_ae this 
    rw [snorm_const _ hp hμ, mul_commₓ, ←of_real_norm_eq_coe_nnnorm, hC', one_div]

theorem snorm_congr_norm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐx ∂μ, ∥f x∥ = ∥g x∥) : snorm f p μ = snorm g p μ :=
  le_antisymmₓ (snorm_mono_ae$ eventually_eq.le hfg) (snorm_mono_ae$ (eventually_eq.symm hfg).le)

@[simp]
theorem snorm'_norm {f : α → F} : snorm' (fun a => ∥f a∥) q μ = snorm' f q μ :=
  by 
    simp [snorm']

@[simp]
theorem snorm_norm (f : α → F) : snorm (fun x => ∥f x∥) p μ = snorm f p μ :=
  snorm_congr_norm_ae$ eventually_of_forall$ fun x => norm_norm _

theorem snorm'_norm_rpow (f : α → F) (p q : ℝ) (hq_pos : 0 < q) :
  snorm' (fun x => ∥f x∥^q) p μ = (snorm' f (p*q) μ^q) :=
  by 
    simpRw [snorm']
    rw [←Ennreal.rpow_mul, ←one_div_mul_one_div]
    simpRw [one_div]
    rw [mul_assocₓ, inv_mul_cancel hq_pos.ne.symm, mul_oneₓ]
    congr 
    ext1 x 
    simpRw [←of_real_norm_eq_coe_nnnorm]
    rw [Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg_of_nonneg (norm_nonneg _) _), mul_commₓ,
      ←Ennreal.of_real_rpow_of_nonneg (norm_nonneg _) hq_pos.le, Ennreal.rpow_mul]

theorem snorm_norm_rpow (f : α → F) (hq_pos : 0 < q) :
  snorm (fun x => ∥f x∥^q) p μ = (snorm f (p*Ennreal.ofReal q) μ^q) :=
  by 
    byCases' h0 : p = 0
    ·
      simp [h0, Ennreal.zero_rpow_of_pos hq_pos]
    byCases' hp_top : p = ∞
    ·
      simp only [hp_top, snorm_exponent_top, Ennreal.top_mul, hq_pos.not_le, Ennreal.of_real_eq_zero, if_false,
        snorm_exponent_top, snorm_ess_sup]
      have h_rpow :
        essSup (fun x : α => (nnnorm (∥f x∥^q) : ℝ≥0∞)) μ = essSup (fun x : α => «expr↑ » (nnnorm (f x))^q) μ
      ·
        congr 
        ext1 x 
        nthRw 1[←nnnorm_norm]
        rw [Ennreal.coe_rpow_of_nonneg _ hq_pos.le, Ennreal.coe_eq_coe]
        ext 
        pushCast 
        rw [Real.norm_rpow_of_nonneg (norm_nonneg _)]
      rw [h_rpow]
      have h_rpow_mono := Ennreal.rpow_left_strict_mono_of_pos hq_pos 
      have h_rpow_surj := (Ennreal.rpow_left_bijective hq_pos.ne.symm).2
      let iso := h_rpow_mono.order_iso_of_surjective _ h_rpow_surj 
      exact (iso.ess_sup_apply (fun x => (nnnorm (f x) : ℝ≥0∞)) μ).symm 
    rw [snorm_eq_snorm' h0 hp_top, snorm_eq_snorm' _ _]
    swap
    ·
      refine' mul_ne_zero h0 _ 
      rwa [Ne.def, Ennreal.of_real_eq_zero, not_leₓ]
    swap
    ·
      exact Ennreal.mul_ne_top hp_top Ennreal.of_real_ne_top 
    rw [Ennreal.to_real_mul, Ennreal.to_real_of_real hq_pos.le]
    exact snorm'_norm_rpow f p.to_real q hq_pos

theorem snorm_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm f p μ = snorm g p μ :=
  snorm_congr_norm_ae$ hfg.mono fun x hx => hx ▸ rfl

theorem mem_ℒp_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) : mem_ℒp f p μ ↔ mem_ℒp g p μ :=
  by 
    simp only [mem_ℒp, snorm_congr_ae hfg, ae_measurable_congr hfg]

theorem mem_ℒp.ae_eq {f g : α → E} (hfg : f =ᵐ[μ] g) (hf_Lp : mem_ℒp f p μ) : mem_ℒp g p μ :=
  (mem_ℒp_congr_ae hfg).1 hf_Lp

theorem mem_ℒp.of_le [MeasurableSpace F] {f : α → E} {g : α → F} (hg : mem_ℒp g p μ) (hf : AeMeasurable f μ)
  (hfg : ∀ᵐx ∂μ, ∥f x∥ ≤ ∥g x∥) : mem_ℒp f p μ :=
  ⟨hf, (snorm_mono_ae hfg).trans_lt hg.snorm_lt_top⟩

alias mem_ℒp.of_le ← MeasureTheory.Memℒp.mono

theorem mem_ℒp.mono' {f : α → E} {g : α → ℝ} (hg : mem_ℒp g p μ) (hf : AeMeasurable f μ) (h : ∀ᵐa ∂μ, ∥f a∥ ≤ g a) :
  mem_ℒp f p μ :=
  hg.mono hf$ h.mono$ fun x hx => le_transₓ hx (le_abs_self _)

theorem mem_ℒp.congr_norm [MeasurableSpace F] {f : α → E} {g : α → F} (hf : mem_ℒp f p μ) (hg : AeMeasurable g μ)
  (h : ∀ᵐa ∂μ, ∥f a∥ = ∥g a∥) : mem_ℒp g p μ :=
  hf.mono hg$ eventually_eq.le$ eventually_eq.symm h

theorem mem_ℒp_congr_norm [MeasurableSpace F] {f : α → E} {g : α → F} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ)
  (h : ∀ᵐa ∂μ, ∥f a∥ = ∥g a∥) : mem_ℒp f p μ ↔ mem_ℒp g p μ :=
  ⟨fun h2f => h2f.congr_norm hg h, fun h2g => h2g.congr_norm hf$ eventually_eq.symm h⟩

theorem mem_ℒp_top_of_bound {f : α → E} (hf : AeMeasurable f μ) (C : ℝ) (hfC : ∀ᵐx ∂μ, ∥f x∥ ≤ C) : mem_ℒp f ∞ μ :=
  ⟨hf,
    by 
      rw [snorm_exponent_top]
      exact snorm_ess_sup_lt_top_of_ae_bound hfC⟩

theorem mem_ℒp.of_bound [is_finite_measure μ] {f : α → E} (hf : AeMeasurable f μ) (C : ℝ) (hfC : ∀ᵐx ∂μ, ∥f x∥ ≤ C) :
  mem_ℒp f p μ :=
  (mem_ℒp_const C).ofLe hf (hfC.mono fun x hx => le_transₓ hx (le_abs_self _))

@[mono]
theorem snorm'_mono_measure (f : α → F) (hμν : ν ≤ μ) (hq : 0 ≤ q) : snorm' f q ν ≤ snorm' f q μ :=
  by 
    simpRw [snorm']
    suffices h_integral_mono : (∫⁻a, (nnnorm (f a) : ℝ≥0∞)^q ∂ν) ≤ ∫⁻a, nnnorm (f a)^q ∂μ 
    exact
      Ennreal.rpow_le_rpow h_integral_mono
        (by 
          simp [hq])
    exact lintegral_mono' hμν le_rfl

@[mono]
theorem snorm_ess_sup_mono_measure (f : α → F) (hμν : ν ≪ μ) : snorm_ess_sup f ν ≤ snorm_ess_sup f μ :=
  by 
    simpRw [snorm_ess_sup]
    exact ess_sup_mono_measure hμν

@[mono]
theorem snorm_mono_measure (f : α → F) (hμν : ν ≤ μ) : snorm f p ν ≤ snorm f p μ :=
  by 
    byCases' hp0 : p = 0
    ·
      simp [hp0]
    byCases' hp_top : p = ∞
    ·
      simp [hp_top, snorm_ess_sup_mono_measure f (measure.absolutely_continuous_of_le hμν)]
    simpRw [snorm_eq_snorm' hp0 hp_top]
    exact snorm'_mono_measure f hμν Ennreal.to_real_nonneg

theorem mem_ℒp.mono_measure {f : α → E} (hμν : ν ≤ μ) (hf : mem_ℒp f p μ) : mem_ℒp f p ν :=
  ⟨hf.1.mono_measure hμν, (snorm_mono_measure f hμν).trans_lt hf.2⟩

theorem mem_ℒp.restrict (s : Set α) {f : α → E} (hf : mem_ℒp f p μ) : mem_ℒp f p (μ.restrict s) :=
  hf.mono_measure measure.restrict_le_self

theorem snorm'_smul_measure {p : ℝ} (hp : 0 ≤ p) {f : α → F} (c : ℝ≥0∞) : snorm' f p (c • μ) = (c^1 / p)*snorm' f p μ :=
  by 
    rw [snorm', lintegral_smul_measure, Ennreal.mul_rpow_of_nonneg, snorm']
    simp [hp]

theorem snorm_ess_sup_smul_measure {f : α → F} {c : ℝ≥0∞} (hc : c ≠ 0) : snorm_ess_sup f (c • μ) = snorm_ess_sup f μ :=
  by 
    simpRw [snorm_ess_sup]
    exact ess_sup_smul_measure hc

/-- Use `snorm_smul_measure_of_ne_top` instead. -/
private theorem snorm_smul_measure_of_ne_zero_of_ne_top {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → F}
  (c : ℝ≥0∞) : snorm f p (c • μ) = (c^(1 / p).toReal) • snorm f p μ :=
  by 
    simpRw [snorm_eq_snorm' hp_ne_zero hp_ne_top]
    rw [snorm'_smul_measure Ennreal.to_real_nonneg]
    congr 
    simpRw [one_div]
    rw [Ennreal.to_real_inv]

theorem snorm_smul_measure_of_ne_zero {p : ℝ≥0∞} {f : α → F} {c : ℝ≥0∞} (hc : c ≠ 0) :
  snorm f p (c • μ) = (c^(1 / p).toReal) • snorm f p μ :=
  by 
    byCases' hp0 : p = 0
    ·
      simp [hp0]
    byCases' hp_top : p = ∞
    ·
      simp [hp_top, snorm_ess_sup_smul_measure hc]
    exact snorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_top c

theorem snorm_smul_measure_of_ne_top {p : ℝ≥0∞} (hp_ne_top : p ≠ ∞) {f : α → F} (c : ℝ≥0∞) :
  snorm f p (c • μ) = (c^(1 / p).toReal) • snorm f p μ :=
  by 
    byCases' hp0 : p = 0
    ·
      simp [hp0]
    ·
      exact snorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_ne_top c

theorem snorm_one_smul_measure {f : α → F} (c : ℝ≥0∞) : snorm f 1 (c • μ) = c*snorm f 1 μ :=
  by 
    rw [@snorm_smul_measure_of_ne_top _ _ _ μ _ 1 (@Ennreal.coe_ne_top 1) f c]
    simp 

section OpensMeasurableSpace

variable[OpensMeasurableSpace E]

theorem mem_ℒp.norm {f : α → E} (h : mem_ℒp f p μ) : mem_ℒp (fun x => ∥f x∥) p μ :=
  h.of_le h.ae_measurable.norm
    (eventually_of_forall
      fun x =>
        by 
          simp )

theorem mem_ℒp_norm_iff {f : α → E} (hf : AeMeasurable f μ) : mem_ℒp (fun x => ∥f x∥) p μ ↔ mem_ℒp f p μ :=
  ⟨fun h =>
      ⟨hf,
        by 
          rw [←snorm_norm]
          exact h.2⟩,
    fun h => h.norm⟩

theorem snorm'_eq_zero_of_ae_zero {f : α → F} (hq0_lt : 0 < q) (hf_zero : f =ᵐ[μ] 0) : snorm' f q μ = 0 :=
  by 
    rw [snorm'_congr_ae hf_zero, snorm'_zero hq0_lt]

theorem snorm'_eq_zero_of_ae_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) {f : α → F} (hf_zero : f =ᵐ[μ] 0) : snorm' f q μ = 0 :=
  by 
    rw [snorm'_congr_ae hf_zero, snorm'_zero' hq0_ne hμ]

theorem ae_eq_zero_of_snorm'_eq_zero {f : α → E} (hq0 : 0 ≤ q) (hf : AeMeasurable f μ) (h : snorm' f q μ = 0) :
  f =ᵐ[μ] 0 :=
  by 
    rw [snorm', Ennreal.rpow_eq_zero_iff] at h 
    cases h
    ·
      rw [lintegral_eq_zero_iff' (hf.ennnorm.pow_const q)] at h 
      refine' h.left.mono fun x hx => _ 
      rw [Pi.zero_apply, Ennreal.rpow_eq_zero_iff] at hx 
      cases hx
      ·
        cases' hx with hx _ 
        rwa [←Ennreal.coe_zero, Ennreal.coe_eq_coe, nnnorm_eq_zero] at hx
      ·
        exact absurd hx.left Ennreal.coe_ne_top
    ·
      exFalso 
      rw [one_div, inv_lt_zero] at h 
      exact hq0.not_lt h.right

theorem snorm'_eq_zero_iff (hq0_lt : 0 < q) {f : α → E} (hf : AeMeasurable f μ) : snorm' f q μ = 0 ↔ f =ᵐ[μ] 0 :=
  ⟨ae_eq_zero_of_snorm'_eq_zero (le_of_ltₓ hq0_lt) hf, snorm'_eq_zero_of_ae_zero hq0_lt⟩

theorem coe_nnnorm_ae_le_snorm_ess_sup {m : MeasurableSpace α} (f : α → F) (μ : Measureₓ α) :
  ∀ᵐx ∂μ, (nnnorm (f x) : ℝ≥0∞) ≤ snorm_ess_sup f μ :=
  Ennreal.ae_le_ess_sup fun x => (nnnorm (f x) : ℝ≥0∞)

@[simp]
theorem snorm_ess_sup_eq_zero_iff {f : α → F} : snorm_ess_sup f μ = 0 ↔ f =ᵐ[μ] 0 :=
  by 
    simp [eventually_eq, snorm_ess_sup]

theorem snorm_eq_zero_iff {f : α → E} (hf : AeMeasurable f μ) (h0 : p ≠ 0) : snorm f p μ = 0 ↔ f =ᵐ[μ] 0 :=
  by 
    byCases' h_top : p = ∞
    ·
      rw [h_top, snorm_exponent_top, snorm_ess_sup_eq_zero_iff]
    rw [snorm_eq_snorm' h0 h_top]
    exact snorm'_eq_zero_iff (ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_neₓ (zero_le _) h0.symm, h_top⟩) hf

theorem snorm'_add_le {f g : α → E} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) (hq1 : 1 ≤ q) :
  snorm' (f+g) q μ ≤ snorm' f q μ+snorm' g q μ :=
  calc
    ((∫⁻a, «expr↑ » (nnnorm ((f+g) a))^q ∂μ)^1 / q) ≤
      ((∫⁻a, ((fun a => (nnnorm (f a) : ℝ≥0∞))+fun a => (nnnorm (g a) : ℝ≥0∞)) a^q ∂μ)^1 / q) :=
    by 
      refine'
        Ennreal.rpow_le_rpow _
          (by 
            simp [le_transₓ zero_le_one hq1] :
          0 ≤ 1 / q)
      refine' lintegral_mono fun a => Ennreal.rpow_le_rpow _ (le_transₓ zero_le_one hq1)
      simp [←Ennreal.coe_add, nnnorm_add_le]
    _ ≤ snorm' f q μ+snorm' g q μ := Ennreal.lintegral_Lp_add_le hf.ennnorm hg.ennnorm hq1
    

theorem snorm_ess_sup_add_le {f g : α → F} : snorm_ess_sup (f+g) μ ≤ snorm_ess_sup f μ+snorm_ess_sup g μ :=
  by 
    refine' le_transₓ (ess_sup_mono_ae (eventually_of_forall fun x => _)) (Ennreal.ess_sup_add_le _ _)
    simpRw [Pi.add_apply, ←Ennreal.coe_add, Ennreal.coe_le_coe]
    exact nnnorm_add_le _ _

-- error in MeasureTheory.Function.LpSpace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem snorm_add_le
{f g : α → E}
(hf : ae_measurable f μ)
(hg : ae_measurable g μ)
(hp1 : «expr ≤ »(1, p)) : «expr ≤ »(snorm «expr + »(f, g) p μ, «expr + »(snorm f p μ, snorm g p μ)) :=
begin
  by_cases [expr hp0, ":", expr «expr = »(p, 0)],
  { simp [] [] [] ["[", expr hp0, "]"] [] [] },
  by_cases [expr hp_top, ":", expr «expr = »(p, «expr∞»())],
  { simp [] [] [] ["[", expr hp_top, ",", expr snorm_ess_sup_add_le, "]"] [] [] },
  have [ident hp1_real] [":", expr «expr ≤ »(1, p.to_real)] [],
  by rwa ["[", "<-", expr ennreal.one_to_real, ",", expr ennreal.to_real_le_to_real ennreal.one_ne_top hp_top, "]"] [],
  repeat { rw [expr snorm_eq_snorm' hp0 hp_top] [] },
  exact [expr snorm'_add_le hf hg hp1_real]
end

theorem snorm_sub_le {f g : α → E} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) (hp1 : 1 ≤ p) :
  snorm (f - g) p μ ≤ snorm f p μ+snorm g p μ :=
  calc snorm (f - g) p μ = snorm (f+-g) p μ :=
    by 
      rw [sub_eq_add_neg]
    _ = snorm (fun x => ∥f x+-g x∥) p μ := (snorm_norm (f+-g)).symm 
    _ ≤ snorm (fun x => ∥f x∥+∥-g x∥) p μ :=
    by 
      refine' snorm_mono_real fun x => _ 
      rw [norm_norm]
      exact norm_add_le _ _ 
    _ = snorm (fun x => ∥f x∥+∥g x∥) p μ :=
    by 
      simpRw [norm_neg]
    _ ≤ snorm (fun x => ∥f x∥) p μ+snorm (fun x => ∥g x∥) p μ := snorm_add_le hf.norm hg.norm hp1 
    _ = snorm f p μ+snorm g p μ :=
    by 
      rw [←snorm_norm f, ←snorm_norm g]
    

theorem snorm_add_lt_top_of_one_le {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) (hq1 : 1 ≤ p) :
  snorm (f+g) p μ < ∞ :=
  lt_of_le_of_ltₓ (snorm_add_le hf.1 hg.1 hq1) (Ennreal.add_lt_top.mpr ⟨hf.2, hg.2⟩)

theorem snorm'_add_lt_top_of_le_one {f g : α → E} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ)
  (hf_snorm : snorm' f q μ < ∞) (hg_snorm : snorm' g q μ < ∞) (hq_pos : 0 < q) (hq1 : q ≤ 1) : snorm' (f+g) q μ < ∞ :=
  calc
    ((∫⁻a, «expr↑ » (nnnorm ((f+g) a))^q ∂μ)^1 / q) ≤
      ((∫⁻a, ((fun a => (nnnorm (f a) : ℝ≥0∞))+fun a => (nnnorm (g a) : ℝ≥0∞)) a^q ∂μ)^1 / q) :=
    by 
      refine'
        Ennreal.rpow_le_rpow _
          (by 
            simp [hq_pos.le] :
          0 ≤ 1 / q)
      refine' lintegral_mono fun a => Ennreal.rpow_le_rpow _ hq_pos.le 
      simp [←Ennreal.coe_add, nnnorm_add_le]
    _ ≤ ((∫⁻a, ((nnnorm (f a) : ℝ≥0∞)^q)+(nnnorm (g a) : ℝ≥0∞)^q ∂μ)^1 / q) :=
    by 
      refine'
        Ennreal.rpow_le_rpow (lintegral_mono fun a => _)
          (by 
            simp [hq_pos.le] :
          0 ≤ 1 / q)
      exact Ennreal.rpow_add_le_add_rpow _ _ hq_pos hq1 
    _ < ∞ :=
    by 
      refine'
        Ennreal.rpow_lt_top_of_nonneg
          (by 
            simp [hq_pos.le] :
          0 ≤ 1 / q)
          _ 
      rw [lintegral_add' (hf.ennnorm.pow_const q) (hg.ennnorm.pow_const q), Ennreal.add_ne_top, ←lt_top_iff_ne_top,
        ←lt_top_iff_ne_top]
      exact
        ⟨lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hq_pos hf_snorm,
          lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hq_pos hg_snorm⟩
    

theorem snorm_add_lt_top {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) : snorm (f+g) p μ < ∞ :=
  by 
    byCases' h0 : p = 0
    ·
      simp [h0]
    rw [←Ne.def] at h0 
    cases' le_totalₓ 1 p with hp1 hp1
    ·
      exact snorm_add_lt_top_of_one_le hf hg hp1 
    have hp_top : p ≠ ∞
    exact (lt_of_le_of_ltₓ hp1 Ennreal.coe_lt_top).Ne 
    have hp_pos : 0 < p.to_real
    ·
      rw [←Ennreal.zero_to_real, @Ennreal.to_real_lt_to_real 0 p Ennreal.coe_ne_top hp_top]
      exact (zero_le p).lt_of_ne h0.symm 
    have hp1_real : p.to_real ≤ 1
    ·
      rwa [←Ennreal.one_to_real, @Ennreal.to_real_le_to_real p 1 hp_top Ennreal.coe_ne_top]
    rw [snorm_eq_snorm' h0 hp_top]
    rw [mem_ℒp, snorm_eq_snorm' h0 hp_top] at hf hg 
    exact snorm'_add_lt_top_of_le_one hf.1 hg.1 hf.2 hg.2 hp_pos hp1_real

section Trim

theorem snorm'_trim (hm : m ≤ m0) {f : α → E} (hf : @Measurable _ _ m _ f) : snorm' f q (ν.trim hm) = snorm' f q ν :=
  by 
    simpRw [snorm']
    congr 1
    refine' lintegral_trim hm _ 
    refine' @Measurable.pow_const _ _ _ _ _ _ _ m _ (@Measurable.coe_nnreal_ennreal _ m _ _) _ 
    exact @Measurable.nnnorm E _ _ _ _ m _ hf

theorem limsup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : @Measurable _ _ m _ f) :
  (ν.trim hm).ae.limsup f = ν.ae.limsup f :=
  by 
    simpRw [limsup_eq]
    suffices h_set_eq : { a : ℝ≥0∞ | ∀ᵐn ∂ν.trim hm, f n ≤ a } = { a : ℝ≥0∞ | ∀ᵐn ∂ν, f n ≤ a }
    ·
      rw [h_set_eq]
    ext1 a 
    suffices h_meas_eq : ν { x | ¬f x ≤ a } = ν.trim hm { x | ¬f x ≤ a }
    ·
      simpRw [Set.mem_set_of_eq, ae_iff, h_meas_eq]
    refine' (trim_measurable_set_eq hm _).symm 
    refine' @MeasurableSet.compl _ _ m (@measurable_set_le ℝ≥0∞ _ _ _ _ m _ _ _ _ _ hf _)
    exact @measurable_const _ _ _ m _

theorem ess_sup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : @Measurable _ _ m _ f) : essSup f (ν.trim hm) = essSup f ν :=
  by 
    simpRw [essSup]
    exact limsup_trim hm hf

theorem snorm_ess_sup_trim (hm : m ≤ m0) {f : α → E} (hf : @Measurable _ _ m _ f) :
  snorm_ess_sup f (ν.trim hm) = snorm_ess_sup f ν :=
  ess_sup_trim hm (@Measurable.coe_nnreal_ennreal _ m _ (@Measurable.nnnorm E _ _ _ _ m _ hf))

theorem snorm_trim (hm : m ≤ m0) {f : α → E} (hf : @Measurable _ _ m _ f) : snorm f p (ν.trim hm) = snorm f p ν :=
  by 
    byCases' h0 : p = 0
    ·
      simp [h0]
    byCases' h_top : p = ∞
    ·
      simpa only [h_top, snorm_exponent_top] using snorm_ess_sup_trim hm hf 
    simpa only [snorm_eq_snorm' h0 h_top] using snorm'_trim hm hf

theorem snorm_trim_ae (hm : m ≤ m0) {f : α → E} (hf : AeMeasurable f (ν.trim hm)) :
  snorm f p (ν.trim hm) = snorm f p ν :=
  by 
    rw [snorm_congr_ae hf.ae_eq_mk, snorm_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]
    exact snorm_trim hm hf.measurable_mk

theorem mem_ℒp_of_mem_ℒp_trim (hm : m ≤ m0) {f : α → E} (hf : mem_ℒp f p (ν.trim hm)) : mem_ℒp f p ν :=
  ⟨ae_measurable_of_ae_measurable_trim hm hf.1, (le_of_eqₓ (snorm_trim_ae hm hf.1).symm).trans_lt hf.2⟩

end Trim

end OpensMeasurableSpace

@[simp]
theorem snorm'_neg {f : α → F} : snorm' (-f) q μ = snorm' f q μ :=
  by 
    simp [snorm']

@[simp]
theorem snorm_neg {f : α → F} : snorm (-f) p μ = snorm f p μ :=
  by 
    byCases' h0 : p = 0
    ·
      simp [h0]
    byCases' h_top : p = ∞
    ·
      simp [h_top, snorm_ess_sup]
    simp [snorm_eq_snorm' h0 h_top]

section BorelSpace

variable[BorelSpace E]

theorem mem_ℒp.neg {f : α → E} (hf : mem_ℒp f p μ) : mem_ℒp (-f) p μ :=
  ⟨AeMeasurable.neg hf.1,
    by 
      simp [hf.right]⟩

theorem mem_ℒp_neg_iff {f : α → E} : mem_ℒp (-f) p μ ↔ mem_ℒp f p μ :=
  ⟨fun h => neg_negₓ f ▸ h.neg, mem_ℒp.neg⟩

-- error in MeasureTheory.Function.LpSpace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem snorm'_le_snorm'_mul_rpow_measure_univ
{p q : exprℝ()}
(hp0_lt : «expr < »(0, p))
(hpq : «expr ≤ »(p, q))
{f : α → E}
(hf : ae_measurable f μ) : «expr ≤ »(snorm' f p μ, «expr * »(snorm' f q μ, «expr ^ »(μ set.univ, «expr - »(«expr / »(1, p), «expr / »(1, q))))) :=
begin
  have [ident hq0_lt] [":", expr «expr < »(0, q)] [],
  from [expr lt_of_lt_of_le hp0_lt hpq],
  by_cases [expr hpq_eq, ":", expr «expr = »(p, q)],
  { rw ["[", expr hpq_eq, ",", expr sub_self, ",", expr ennreal.rpow_zero, ",", expr mul_one, "]"] [],
    exact [expr le_refl _] },
  have [ident hpq] [":", expr «expr < »(p, q)] [],
  from [expr lt_of_le_of_ne hpq hpq_eq],
  let [ident g] [] [":=", expr λ a : α, (1 : «exprℝ≥0∞»())],
  have [ident h_rw] [":", expr «expr = »(«expr∫⁻ , ∂ »((a), «expr ^ »(«expr↑ »(nnnorm (f a)), p), μ), «expr∫⁻ , ∂ »((a), «expr ^ »(«expr * »(nnnorm (f a), g a), p), μ))] [],
  from [expr lintegral_congr (λ a, by simp [] [] [] [] [] [])],
  repeat { rw [expr snorm'] [] },
  rw [expr h_rw] [],
  let [ident r] [] [":=", expr «expr / »(«expr * »(p, q), «expr - »(q, p))],
  have [ident hpqr] [":", expr «expr = »(«expr / »(1, p), «expr + »(«expr / »(1, q), «expr / »(1, r)))] [],
  { field_simp [] ["[", expr (ne_of_lt hp0_lt).symm, ",", expr (ne_of_lt hq0_lt).symm, "]"] [] [],
    ring [] },
  calc
    «expr ≤ »(«expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(«expr * »(«expr↑ »(nnnorm (f a)), g a), p), μ), «expr / »(1, p)), «expr * »(«expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(«expr↑ »(nnnorm (f a)), q), μ), «expr / »(1, q)), «expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(g a, r), μ), «expr / »(1, r)))) : ennreal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.ennnorm ae_measurable_const
    «expr = »(..., «expr * »(«expr ^ »(«expr∫⁻ , ∂ »((a : α), «expr ^ »(«expr↑ »(nnnorm (f a)), q), μ), «expr / »(1, q)), «expr ^ »(μ set.univ, «expr - »(«expr / »(1, p), «expr / »(1, q))))) : by simp [] [] [] ["[", expr hpqr, "]"] [] []
end

theorem snorm'_le_snorm_ess_sup_mul_rpow_measure_univ (hq_pos : 0 < q) {f : α → F} :
  snorm' f q μ ≤ snorm_ess_sup f μ*μ Set.Univ^1 / q :=
  by 
    have h_le : (∫⁻a : α, «expr↑ » (nnnorm (f a))^q ∂μ) ≤ ∫⁻a : α, snorm_ess_sup f μ^q ∂μ
    ·
      refine' lintegral_mono_ae _ 
      have h_nnnorm_le_snorm_ess_sup := coe_nnnorm_ae_le_snorm_ess_sup f μ 
      refine' h_nnnorm_le_snorm_ess_sup.mono fun x hx => Ennreal.rpow_le_rpow hx (le_of_ltₓ hq_pos)
    rw [snorm', ←Ennreal.rpow_one (snorm_ess_sup f μ)]
    nthRw 1[←mul_inv_cancel (ne_of_ltₓ hq_pos).symm]
    rw [Ennreal.rpow_mul, one_div,
      ←Ennreal.mul_rpow_of_nonneg _ _
        (by 
          simp [hq_pos.le] :
        0 ≤ q⁻¹)]
    refine'
      Ennreal.rpow_le_rpow _
        (by 
          simp [hq_pos.le])
    rwa [lintegral_const] at h_le

theorem snorm_le_snorm_mul_rpow_measure_univ {p q : ℝ≥0∞} (hpq : p ≤ q) {f : α → E} (hf : AeMeasurable f μ) :
  snorm f p μ ≤ snorm f q μ*μ Set.Univ^1 / p.to_real - 1 / q.to_real :=
  by 
    byCases' hp0 : p = 0
    ·
      simp [hp0, zero_le]
    rw [←Ne.def] at hp0 
    have hp0_lt : 0 < p 
    exact lt_of_le_of_neₓ (zero_le _) hp0.symm 
    have hq0_lt : 0 < q 
    exact lt_of_lt_of_leₓ hp0_lt hpq 
    byCases' hq_top : q = ∞
    ·
      simp only [hq_top, div_zero, one_div, Ennreal.top_to_real, sub_zero, snorm_exponent_top, inv_zero]
      byCases' hp_top : p = ∞
      ·
        simp only [hp_top, Ennreal.rpow_zero, mul_oneₓ, Ennreal.top_to_real, sub_zero, inv_zero, snorm_exponent_top]
        exact le_rfl 
      rw [snorm_eq_snorm' hp0 hp_top]
      have hp_pos : 0 < p.to_real 
      exact ennreal.to_real_pos_iff.mpr ⟨hp0_lt, hp_top⟩
      refine' (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hp_pos).trans (le_of_eqₓ _)
      congr 
      exact one_div _ 
    have hp_lt_top : p < ∞
    exact hpq.trans_lt (lt_top_iff_ne_top.mpr hq_top)
    have hp_pos : 0 < p.to_real 
    exact ennreal.to_real_pos_iff.mpr ⟨hp0_lt, hp_lt_top.ne⟩
    rw [snorm_eq_snorm' hp0_lt.ne.symm hp_lt_top.ne, snorm_eq_snorm' hq0_lt.ne.symm hq_top]
    have hpq_real : p.to_real ≤ q.to_real
    ·
      rwa [Ennreal.to_real_le_to_real hp_lt_top.ne hq_top]
    exact snorm'_le_snorm'_mul_rpow_measure_univ hp_pos hpq_real hf

theorem snorm'_le_snorm'_of_exponent_le {m : MeasurableSpace α} {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q)
  (μ : Measureₓ α) [is_probability_measure μ] {f : α → E} (hf : AeMeasurable f μ) : snorm' f p μ ≤ snorm' f q μ :=
  by 
    have h_le_μ := snorm'_le_snorm'_mul_rpow_measure_univ hp0_lt hpq hf 
    rwa [measure_univ, Ennreal.one_rpow, mul_oneₓ] at h_le_μ

theorem snorm'_le_snorm_ess_sup (hq_pos : 0 < q) {f : α → F} [is_probability_measure μ] :
  snorm' f q μ ≤ snorm_ess_sup f μ :=
  le_transₓ (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hq_pos)
    (le_of_eqₓ
      (by 
        simp [measure_univ]))

theorem snorm_le_snorm_of_exponent_le {p q : ℝ≥0∞} (hpq : p ≤ q) [is_probability_measure μ] {f : α → E}
  (hf : AeMeasurable f μ) : snorm f p μ ≤ snorm f q μ :=
  (snorm_le_snorm_mul_rpow_measure_univ hpq hf).trans
    (le_of_eqₓ
      (by 
        simp [measure_univ]))

theorem snorm'_lt_top_of_snorm'_lt_top_of_exponent_le {p q : ℝ} [is_finite_measure μ] {f : α → E}
  (hf : AeMeasurable f μ) (hfq_lt_top : snorm' f q μ < ∞) (hp_nonneg : 0 ≤ p) (hpq : p ≤ q) : snorm' f p μ < ∞ :=
  by 
    cases' le_or_ltₓ p 0 with hp_nonpos hp_pos
    ·
      rw [le_antisymmₓ hp_nonpos hp_nonneg]
      simp 
    have hq_pos : 0 < q 
    exact lt_of_lt_of_leₓ hp_pos hpq 
    calc snorm' f p μ ≤ snorm' f q μ*μ Set.Univ^1 / p - 1 / q :=
      snorm'_le_snorm'_mul_rpow_measure_univ hp_pos hpq hf _ < ∞ :=
      by 
        rw [Ennreal.mul_lt_top_iff]
        refine' Or.inl ⟨hfq_lt_top, Ennreal.rpow_lt_top_of_nonneg _ (measure_ne_top μ Set.Univ)⟩
        rwa [le_sub, sub_zero, one_div, one_div, inv_le_inv hq_pos hp_pos]

-- error in MeasureTheory.Function.LpSpace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem mem_ℒp.mem_ℒp_of_exponent_le
{p q : «exprℝ≥0∞»()}
[is_finite_measure μ]
{f : α → E}
(hfq : mem_ℒp f q μ)
(hpq : «expr ≤ »(p, q)) : mem_ℒp f p μ :=
begin
  cases [expr hfq] ["with", ident hfq_m, ident hfq_lt_top],
  by_cases [expr hp0, ":", expr «expr = »(p, 0)],
  { rwa ["[", expr hp0, ",", expr mem_ℒp_zero_iff_ae_measurable, "]"] [] },
  rw ["<-", expr ne.def] ["at", ident hp0],
  refine [expr ⟨hfq_m, _⟩],
  by_cases [expr hp_top, ":", expr «expr = »(p, «expr∞»())],
  { have [ident hq_top] [":", expr «expr = »(q, «expr∞»())] [],
    by rwa ["[", expr hp_top, ",", expr top_le_iff, "]"] ["at", ident hpq],
    rw ["[", expr hp_top, "]"] [],
    rwa [expr hq_top] ["at", ident hfq_lt_top] },
  have [ident hp_pos] [":", expr «expr < »(0, p.to_real)] [],
  from [expr ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩],
  by_cases [expr hq_top, ":", expr «expr = »(q, «expr∞»())],
  { rw [expr snorm_eq_snorm' hp0 hp_top] [],
    rw ["[", expr hq_top, ",", expr snorm_exponent_top, "]"] ["at", ident hfq_lt_top],
    refine [expr lt_of_le_of_lt (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hp_pos) _],
    refine [expr ennreal.mul_lt_top hfq_lt_top.ne _],
    exact [expr (ennreal.rpow_lt_top_of_nonneg (by simp [] [] [] ["[", expr hp_pos.le, "]"] [] []) (measure_ne_top μ set.univ)).ne] },
  have [ident hq0] [":", expr «expr ≠ »(q, 0)] [],
  { by_contra [ident hq_eq_zero],
    have [ident hp_eq_zero] [":", expr «expr = »(p, 0)] [],
    from [expr le_antisymm (by rwa [expr hq_eq_zero] ["at", ident hpq]) (zero_le _)],
    rw ["[", expr hp_eq_zero, ",", expr ennreal.zero_to_real, "]"] ["at", ident hp_pos],
    exact [expr lt_irrefl _ hp_pos] },
  have [ident hpq_real] [":", expr «expr ≤ »(p.to_real, q.to_real)] [],
  by rwa [expr ennreal.to_real_le_to_real hp_top hq_top] [],
  rw [expr snorm_eq_snorm' hp0 hp_top] [],
  rw [expr snorm_eq_snorm' hq0 hq_top] ["at", ident hfq_lt_top],
  exact [expr snorm'_lt_top_of_snorm'_lt_top_of_exponent_le hfq_m hfq_lt_top (le_of_lt hp_pos) hpq_real]
end

theorem snorm'_sum_le [second_countable_topology E] {ι} {f : ι → α → E} {s : Finset ι}
  (hfs : ∀ i, i ∈ s → AeMeasurable (f i) μ) (hq1 : 1 ≤ q) : snorm' (∑i in s, f i) q μ ≤ ∑i in s, snorm' (f i) q μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → E => snorm' f q μ) (fun f => AeMeasurable f μ)
    (snorm'_zero (zero_lt_one.trans_le hq1)) (fun f g hf hg => snorm'_add_le hf hg hq1) (fun x y => AeMeasurable.add) _
    hfs

theorem snorm_sum_le [second_countable_topology E] {ι} {f : ι → α → E} {s : Finset ι}
  (hfs : ∀ i, i ∈ s → AeMeasurable (f i) μ) (hp1 : 1 ≤ p) : snorm (∑i in s, f i) p μ ≤ ∑i in s, snorm (f i) p μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → E => snorm f p μ) (fun f => AeMeasurable f μ) snorm_zero
    (fun f g hf hg => snorm_add_le hf hg hp1) (fun x y => AeMeasurable.add) _ hfs

section SecondCountableTopology

variable[second_countable_topology E]

theorem mem_ℒp.add {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) : mem_ℒp (f+g) p μ :=
  ⟨AeMeasurable.add hf.1 hg.1, snorm_add_lt_top hf hg⟩

theorem mem_ℒp.sub {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) : mem_ℒp (f - g) p μ :=
  by 
    rw [sub_eq_add_neg]
    exact hf.add hg.neg

theorem mem_ℒp_finset_sum {ι} (s : Finset ι) {f : ι → α → E} (hf : ∀ i _ : i ∈ s, mem_ℒp (f i) p μ) :
  mem_ℒp (fun a => ∑i in s, f i a) p μ :=
  by 
    haveI  : DecidableEq ι := Classical.decEq _ 
    revert hf 
    refine' Finset.induction_on s _ _
    ·
      simp only [zero_mem_ℒp', Finset.sum_empty, implies_true_iff]
    ·
      intro i s his ih hf 
      simp only [his, Finset.sum_insert, not_false_iff]
      exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end SecondCountableTopology

end BorelSpace

section NormedSpace

variable{𝕜 : Type _}[NormedField 𝕜][NormedSpace 𝕜 E][NormedSpace 𝕜 F]

theorem snorm'_const_smul {f : α → F} (c : 𝕜) (hq_pos : 0 < q) : snorm' (c • f) q μ = (nnnorm c : ℝ≥0∞)*snorm' f q μ :=
  by 
    rw [snorm']
    simpRw [Pi.smul_apply, nnnorm_smul, Ennreal.coe_mul, Ennreal.mul_rpow_of_nonneg _ _ hq_pos.le]
    suffices h_integral :
      (∫⁻a, («expr↑ » (nnnorm c)^q)*«expr↑ » (nnnorm (f a))^q ∂μ) = ((nnnorm c : ℝ≥0∞)^q)*∫⁻a, nnnorm (f a)^q ∂μ
    ·
      applyFun fun x => x^1 / q  at h_integral 
      rw [h_integral,
        Ennreal.mul_rpow_of_nonneg _ _
          (by 
            simp [hq_pos.le] :
          0 ≤ 1 / q)]
      congr 
      simpRw [←Ennreal.rpow_mul, one_div, mul_inv_cancel hq_pos.ne.symm, Ennreal.rpow_one]
    rw [lintegral_const_mul']
    rw [Ennreal.coe_rpow_of_nonneg _ hq_pos.le]
    exact Ennreal.coe_ne_top

theorem snorm_ess_sup_const_smul {f : α → F} (c : 𝕜) : snorm_ess_sup (c • f) μ = (nnnorm c : ℝ≥0∞)*snorm_ess_sup f μ :=
  by 
    simpRw [snorm_ess_sup, Pi.smul_apply, nnnorm_smul, Ennreal.coe_mul, Ennreal.ess_sup_const_mul]

-- error in MeasureTheory.Function.LpSpace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem snorm_const_smul
{f : α → F}
(c : 𝕜) : «expr = »(snorm «expr • »(c, f) p μ, «expr * »((nnnorm c : «exprℝ≥0∞»()), snorm f p μ)) :=
begin
  by_cases [expr h0, ":", expr «expr = »(p, 0)],
  { simp [] [] [] ["[", expr h0, "]"] [] [] },
  by_cases [expr h_top, ":", expr «expr = »(p, «expr∞»())],
  { simp [] [] [] ["[", expr h_top, ",", expr snorm_ess_sup_const_smul, "]"] [] [] },
  repeat { rw [expr snorm_eq_snorm' h0 h_top] [] },
  rw ["<-", expr ne.def] ["at", ident h0],
  exact [expr snorm'_const_smul c (ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩)]
end

theorem mem_ℒp.const_smul [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] [BorelSpace E] {f : α → E} (hf : mem_ℒp f p μ)
  (c : 𝕜) : mem_ℒp (c • f) p μ :=
  ⟨AeMeasurable.const_smul hf.1 c, (snorm_const_smul c).le.trans_lt (Ennreal.mul_lt_top Ennreal.coe_ne_top hf.2.Ne)⟩

theorem mem_ℒp.const_mul [MeasurableSpace 𝕜] [BorelSpace 𝕜] {f : α → 𝕜} (hf : mem_ℒp f p μ) (c : 𝕜) :
  mem_ℒp (fun x => c*f x) p μ :=
  hf.const_smul c

theorem snorm'_smul_le_mul_snorm' [OpensMeasurableSpace E] [MeasurableSpace 𝕜] [OpensMeasurableSpace 𝕜] {p q r : ℝ}
  {f : α → E} (hf : AeMeasurable f μ) {φ : α → 𝕜} (hφ : AeMeasurable φ μ) (hp0_lt : 0 < p) (hpq : p < q)
  (hpqr : 1 / p = (1 / q)+1 / r) : snorm' (φ • f) p μ ≤ snorm' φ q μ*snorm' f r μ :=
  by 
    simpRw [snorm', Pi.smul_apply', nnnorm_smul, Ennreal.coe_mul]
    exact Ennreal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hφ.ennnorm hf.ennnorm

end NormedSpace

section Monotonicity

theorem snorm_le_mul_snorm_aux_of_nonneg {f : α → F} {g : α → G} {c : ℝ} (h : ∀ᵐx ∂μ, ∥f x∥ ≤ c*∥g x∥) (hc : 0 ≤ c)
  (p : ℝ≥0∞) : snorm f p μ ≤ Ennreal.ofReal c*snorm g p μ :=
  by 
    lift c to  ℝ≥0  using hc 
    rw [Ennreal.of_real_coe_nnreal, ←c.nnnorm_eq, ←snorm_norm g, ←snorm_const_smul (c : ℝ)]
    swap 
    infer_instance 
    refine' snorm_mono_ae _ 
    simpa

theorem snorm_le_mul_snorm_aux_of_neg {f : α → F} {g : α → G} {c : ℝ} (h : ∀ᵐx ∂μ, ∥f x∥ ≤ c*∥g x∥) (hc : c < 0)
  (p : ℝ≥0∞) : snorm f p μ = 0 ∧ snorm g p μ = 0 :=
  by 
    suffices  : f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0
    ·
      simp [snorm_congr_ae this.1, snorm_congr_ae this.2]
    refine' ⟨h.mono$ fun x hx => _, h.mono$ fun x hx => _⟩
    ·
      refine' norm_le_zero_iff.1 (hx.trans _)
      exact mul_nonpos_of_nonpos_of_nonneg hc.le (norm_nonneg _)
    ·
      refine' norm_le_zero_iff.1 (nonpos_of_mul_nonneg_right _ hc)
      exact (norm_nonneg _).trans hx

theorem snorm_le_mul_snorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ} (h : ∀ᵐx ∂μ, ∥f x∥ ≤ c*∥g x∥) (p : ℝ≥0∞) :
  snorm f p μ ≤ Ennreal.ofReal c*snorm g p μ :=
  by 
    cases' le_or_ltₓ 0 c with hc hc
    ·
      exact snorm_le_mul_snorm_aux_of_nonneg h hc p
    ·
      simp [snorm_le_mul_snorm_aux_of_neg h hc p]

theorem mem_ℒp.of_le_mul [MeasurableSpace F] {f : α → E} {g : α → F} {c : ℝ} (hg : mem_ℒp g p μ) (hf : AeMeasurable f μ)
  (hfg : ∀ᵐx ∂μ, ∥f x∥ ≤ c*∥g x∥) : mem_ℒp f p μ :=
  by 
    simp only [mem_ℒp, hf, true_andₓ]
    apply lt_of_le_of_ltₓ (snorm_le_mul_snorm_of_ae_le_mul hfg p)
    simp [lt_top_iff_ne_top, hg.snorm_ne_top]

end Monotonicity

section IsROrC

variable{𝕜 : Type _}[IsROrC 𝕜][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]{f : α → 𝕜}

theorem mem_ℒp.re (hf : mem_ℒp f p μ) : mem_ℒp (fun x => IsROrC.re (f x)) p μ :=
  by 
    have  : ∀ x, ∥IsROrC.re (f x)∥ ≤ 1*∥f x∥
    ·
      ·
        intro x 
        rw [one_mulₓ]
        exact IsROrC.norm_re_le_norm (f x)
    exact hf.of_le_mul hf.1.re (eventually_of_forall this)

theorem mem_ℒp.im (hf : mem_ℒp f p μ) : mem_ℒp (fun x => IsROrC.im (f x)) p μ :=
  by 
    have  : ∀ x, ∥IsROrC.im (f x)∥ ≤ 1*∥f x∥
    ·
      ·
        intro x 
        rw [one_mulₓ]
        exact IsROrC.norm_im_le_norm (f x)
    exact hf.of_le_mul hf.1.im (eventually_of_forall this)

end IsROrC

section InnerProduct

variable{E' 𝕜 :
    Type
      _}[IsROrC
      𝕜][MeasurableSpace
      𝕜][BorelSpace
      𝕜][InnerProductSpace 𝕜 E'][MeasurableSpace E'][OpensMeasurableSpace E'][second_countable_topology E']

local notation "⟪" x ", " y "⟫" => @inner 𝕜 E' _ x y

theorem mem_ℒp.const_inner (c : E') {f : α → E'} (hf : mem_ℒp f p μ) : mem_ℒp (fun a => ⟪c, f a⟫) p μ :=
  hf.of_le_mul (AeMeasurable.inner ae_measurable_const hf.1) (eventually_of_forall fun x => norm_inner_le_norm _ _)

theorem mem_ℒp.inner_const {f : α → E'} (hf : mem_ℒp f p μ) (c : E') : mem_ℒp (fun a => ⟪f a, c⟫) p μ :=
  hf.of_le_mul (AeMeasurable.inner hf.1 ae_measurable_const)
    (eventually_of_forall
      fun x =>
        by 
          rw [mul_commₓ]
          exact norm_inner_le_norm _ _)

end InnerProduct

end ℒp

/-!
### Lp space

The space of equivalence classes of measurable functions for which `snorm f p μ < ∞`.
-/


@[simp]
theorem snorm_ae_eq_fun {α E : Type _} [MeasurableSpace α] {μ : Measureₓ α} [MeasurableSpace E] [NormedGroup E]
  {p : ℝ≥0∞} {f : α → E} (hf : AeMeasurable f μ) : snorm (ae_eq_fun.mk f hf) p μ = snorm f p μ :=
  snorm_congr_ae (ae_eq_fun.coe_fn_mk _ _)

theorem mem_ℒp.snorm_mk_lt_top {α E : Type _} [MeasurableSpace α] {μ : Measureₓ α} [MeasurableSpace E] [NormedGroup E]
  {p : ℝ≥0∞} {f : α → E} (hfp : mem_ℒp f p μ) : snorm (ae_eq_fun.mk f hfp.1) p μ < ∞ :=
  by 
    simp [hfp.2]

/-- Lp space -/
def Lp {α} (E : Type _) {m : MeasurableSpace α} [MeasurableSpace E] [NormedGroup E] [BorelSpace E]
  [second_countable_topology E] (p : ℝ≥0∞) (μ : Measureₓ α) : AddSubgroup (α →ₘ[μ] E) :=
  { Carrier := { f | snorm f p μ < ∞ },
    zero_mem' :=
      by 
        simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero],
    add_mem' :=
      fun f g hf hg =>
        by 
          simp [snorm_congr_ae (ae_eq_fun.coe_fn_add _ _),
            snorm_add_lt_top ⟨f.ae_measurable, hf⟩ ⟨g.ae_measurable, hg⟩],
    neg_mem' :=
      fun f hf =>
        by 
          rwa [Set.mem_set_of_eq, snorm_congr_ae (ae_eq_fun.coe_fn_neg _), snorm_neg] }

localized [MeasureTheory] notation:25 α " →₁[" μ "] " E => MeasureTheory.lp E 1 μ

localized [MeasureTheory] notation:25 α " →₂[" μ "] " E => MeasureTheory.lp E 2 μ

namespace Memℒp

variable[BorelSpace E][second_countable_topology E]

/-- make an element of Lp from a function verifying `mem_ℒp` -/
def to_Lp (f : α → E) (h_mem_ℒp : mem_ℒp f p μ) : Lp E p μ :=
  ⟨ae_eq_fun.mk f h_mem_ℒp.1, h_mem_ℒp.snorm_mk_lt_top⟩

theorem coe_fn_to_Lp {f : α → E} (hf : mem_ℒp f p μ) : hf.to_Lp f =ᵐ[μ] f :=
  ae_eq_fun.coe_fn_mk _ _

@[simp]
theorem to_Lp_eq_to_Lp_iff {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  hf.to_Lp f = hg.to_Lp g ↔ f =ᵐ[μ] g :=
  by 
    simp [to_Lp]

@[simp]
theorem to_Lp_zero (h : mem_ℒp (0 : α → E) p μ) : h.to_Lp 0 = 0 :=
  rfl

theorem to_Lp_add {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  (hf.add hg).toLp (f+g) = hf.to_Lp f+hg.to_Lp g :=
  rfl

theorem to_Lp_neg {f : α → E} (hf : mem_ℒp f p μ) : hf.neg.to_Lp (-f) = -hf.to_Lp f :=
  rfl

theorem to_Lp_sub {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  (hf.sub hg).toLp (f - g) = hf.to_Lp f - hg.to_Lp g :=
  rfl

end Memℒp

namespace Lp

variable[BorelSpace E][second_countable_topology E]

instance  : CoeFun (Lp E p μ) fun _ => α → E :=
  ⟨fun f => ((f : α →ₘ[μ] E) : α → E)⟩

@[ext]
theorem ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g :=
  by 
    cases f 
    cases g 
    simp only [Subtype.mk_eq_mk]
    exact ae_eq_fun.ext h

theorem ext_iff {f g : Lp E p μ} : f = g ↔ f =ᵐ[μ] g :=
  ⟨fun h =>
      by 
        rw [h],
    fun h => ext h⟩

theorem mem_Lp_iff_snorm_lt_top {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ snorm f p μ < ∞ :=
  Iff.refl _

theorem mem_Lp_iff_mem_ℒp {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ mem_ℒp f p μ :=
  by 
    simp [mem_Lp_iff_snorm_lt_top, mem_ℒp, f.measurable.ae_measurable]

protected theorem Antitone [is_finite_measure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) : Lp E q μ ≤ Lp E p μ :=
  fun f hf => (mem_ℒp.mem_ℒp_of_exponent_le ⟨f.ae_measurable, hf⟩ hpq).2

@[simp]
theorem coe_fn_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α → E) = f :=
  rfl

@[simp]
theorem coe_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) : ((⟨f, hf⟩ : Lp E p μ) : α →ₘ[μ] E) = f :=
  rfl

@[simp]
theorem to_Lp_coe_fn (f : Lp E p μ) (hf : mem_ℒp f p μ) : hf.to_Lp f = f :=
  by 
    cases f 
    simp [mem_ℒp.to_Lp]

theorem snorm_lt_top (f : Lp E p μ) : snorm f p μ < ∞ :=
  f.prop

theorem snorm_ne_top (f : Lp E p μ) : snorm f p μ ≠ ∞ :=
  (snorm_lt_top f).Ne

@[measurability]
protected theorem Measurable (f : Lp E p μ) : Measurable f :=
  f.val.measurable

@[measurability]
protected theorem AeMeasurable (f : Lp E p μ) : AeMeasurable f μ :=
  f.val.ae_measurable

protected theorem mem_ℒp (f : Lp E p μ) : mem_ℒp f p μ :=
  ⟨Lp.ae_measurable f, f.prop⟩

variable(E p μ)

theorem coe_fn_zero : «expr⇑ » (0 : Lp E p μ) =ᵐ[μ] 0 :=
  ae_eq_fun.coe_fn_zero

variable{E p μ}

theorem coe_fn_neg (f : Lp E p μ) : «expr⇑ » (-f) =ᵐ[μ] -f :=
  ae_eq_fun.coe_fn_neg _

theorem coe_fn_add (f g : Lp E p μ) : «expr⇑ » (f+g) =ᵐ[μ] f+g :=
  ae_eq_fun.coe_fn_add _ _

theorem coe_fn_sub (f g : Lp E p μ) : «expr⇑ » (f - g) =ᵐ[μ] f - g :=
  ae_eq_fun.coe_fn_sub _ _

theorem mem_Lp_const α {m : MeasurableSpace α} (μ : Measureₓ α) (c : E) [is_finite_measure μ] :
  @ae_eq_fun.const α _ _ μ _ c ∈ Lp E p μ :=
  (mem_ℒp_const c).snorm_mk_lt_top

instance  : HasNorm (Lp E p μ) :=
  { norm := fun f => Ennreal.toReal (snorm f p μ) }

instance  : HasDist (Lp E p μ) :=
  { dist := fun f g => ∥f - g∥ }

instance  : HasEdist (Lp E p μ) :=
  { edist := fun f g => Ennreal.ofReal (dist f g) }

theorem norm_def (f : Lp E p μ) : ∥f∥ = Ennreal.toReal (snorm f p μ) :=
  rfl

@[simp]
theorem norm_to_Lp (f : α → E) (hf : mem_ℒp f p μ) : ∥hf.to_Lp f∥ = Ennreal.toReal (snorm f p μ) :=
  by 
    rw [norm_def, snorm_congr_ae (mem_ℒp.coe_fn_to_Lp hf)]

theorem dist_def (f g : Lp E p μ) : dist f g = (snorm (f - g) p μ).toReal :=
  by 
    simpRw [dist, norm_def]
    congr 1
    apply snorm_congr_ae (coe_fn_sub _ _)

theorem edist_def (f g : Lp E p μ) : edist f g = snorm (f - g) p μ :=
  by 
    simpRw [edist, dist, norm_def, Ennreal.of_real_to_real (snorm_ne_top _)]
    exact snorm_congr_ae (coe_fn_sub _ _)

@[simp]
theorem edist_to_Lp_to_Lp (f g : α → E) (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  edist (hf.to_Lp f) (hg.to_Lp g) = snorm (f - g) p μ :=
  by 
    rw [edist_def]
    exact snorm_congr_ae (hf.coe_fn_to_Lp.sub hg.coe_fn_to_Lp)

@[simp]
theorem edist_to_Lp_zero (f : α → E) (hf : mem_ℒp f p μ) : edist (hf.to_Lp f) 0 = snorm f p μ :=
  by 
    convert edist_to_Lp_to_Lp f 0 hf zero_mem_ℒp 
    simp 

@[simp]
theorem norm_zero : ∥(0 : Lp E p μ)∥ = 0 :=
  by 
    change (snorm («expr⇑ » (0 : α →ₘ[μ] E)) p μ).toReal = 0
    simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero]

theorem norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ∥f∥ = 0 ↔ f = 0 :=
  by 
    refine'
      ⟨fun hf => _,
        fun hf =>
          by 
            simp [hf]⟩
    rw [norm_def, Ennreal.to_real_eq_zero_iff] at hf 
    cases hf
    ·
      rw [snorm_eq_zero_iff (Lp.ae_measurable f) hp.ne.symm] at hf 
      exact Subtype.eq (ae_eq_fun.ext (hf.trans ae_eq_fun.coe_fn_zero.symm))
    ·
      exact absurd hf (snorm_ne_top f)

theorem eq_zero_iff_ae_eq_zero {f : Lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0 :=
  by 
    split 
    ·
      intro h 
      rw [h]
      exact ae_eq_fun.coe_fn_const _ _
    ·
      intro h 
      ext1 
      filterUpwards [h, ae_eq_fun.coe_fn_const α (0 : E)]
      intro a ha h'a 
      rw [ha]
      exact h'a.symm

@[simp]
theorem norm_neg {f : Lp E p μ} : ∥-f∥ = ∥f∥ :=
  by 
    rw [norm_def, norm_def, snorm_congr_ae (coe_fn_neg _), snorm_neg]

theorem norm_le_mul_norm_of_ae_le_mul [second_countable_topology F] [MeasurableSpace F] [BorelSpace F] {c : ℝ}
  {f : Lp E p μ} {g : Lp F p μ} (h : ∀ᵐx ∂μ, ∥f x∥ ≤ c*∥g x∥) : ∥f∥ ≤ c*∥g∥ :=
  by 
    byCases' pzero : p = 0
    ·
      simp [pzero, norm_def]
    cases' le_or_ltₓ 0 c with hc hc
    ·
      have  := snorm_le_mul_snorm_aux_of_nonneg h hc p 
      rw [←Ennreal.to_real_le_to_real, Ennreal.to_real_mul, Ennreal.to_real_of_real hc] at this
      ·
        exact this
      ·
        exact (Lp.mem_ℒp _).snorm_ne_top
      ·
        simp [(Lp.mem_ℒp _).snorm_ne_top]
    ·
      have  := snorm_le_mul_snorm_aux_of_neg h hc p 
      simp only [snorm_eq_zero_iff (Lp.ae_measurable _) pzero, ←eq_zero_iff_ae_eq_zero] at this 
      simp [this]

theorem norm_le_norm_of_ae_le [second_countable_topology F] [MeasurableSpace F] [BorelSpace F] {f : Lp E p μ}
  {g : Lp F p μ} (h : ∀ᵐx ∂μ, ∥f x∥ ≤ ∥g x∥) : ∥f∥ ≤ ∥g∥ :=
  by 
    rw [norm_def, norm_def, Ennreal.to_real_le_to_real (snorm_ne_top _) (snorm_ne_top _)]
    exact snorm_mono_ae h

theorem mem_Lp_of_ae_le_mul [second_countable_topology F] [MeasurableSpace F] [BorelSpace F] {c : ℝ} {f : α →ₘ[μ] E}
  {g : Lp F p μ} (h : ∀ᵐx ∂μ, ∥f x∥ ≤ c*∥g x∥) : f ∈ Lp E p μ :=
  mem_Lp_iff_mem_ℒp.2$ mem_ℒp.of_le_mul (Lp.mem_ℒp g) f.ae_measurable h

theorem mem_Lp_of_ae_le [second_countable_topology F] [MeasurableSpace F] [BorelSpace F] {f : α →ₘ[μ] E} {g : Lp F p μ}
  (h : ∀ᵐx ∂μ, ∥f x∥ ≤ ∥g x∥) : f ∈ Lp E p μ :=
  mem_Lp_iff_mem_ℒp.2$ mem_ℒp.of_le (Lp.mem_ℒp g) f.ae_measurable h

theorem mem_Lp_of_ae_bound [is_finite_measure μ] {f : α →ₘ[μ] E} (C : ℝ) (hfC : ∀ᵐx ∂μ, ∥f x∥ ≤ C) : f ∈ Lp E p μ :=
  mem_Lp_iff_mem_ℒp.2$ mem_ℒp.of_bound f.ae_measurable _ hfC

theorem norm_le_of_ae_bound [is_finite_measure μ] {f : Lp E p μ} {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ᵐx ∂μ, ∥f x∥ ≤ C) :
  ∥f∥ ≤ (measure_univ_nnreal μ^p.to_real⁻¹)*C :=
  by 
    byCases' hμ : μ = 0
    ·
      byCases' hp : p.to_real⁻¹ = 0
      ·
        simpa [hp, hμ, norm_def] using hC
      ·
        simp [hμ, norm_def, Real.zero_rpow hp]
    let A :  ℝ≥0  := (measure_univ_nnreal μ^p.to_real⁻¹)*⟨C, hC⟩
    suffices  : snorm f p μ ≤ A
    ·
      exact Ennreal.to_real_le_coe_of_le_coe this 
    convert snorm_le_of_ae_bound hfC 
    rw [←coe_measure_univ_nnreal μ, Ennreal.coe_rpow_of_ne_zero (measure_univ_nnreal_pos hμ).ne', Ennreal.coe_mul]
    congr 
    rw [max_eq_leftₓ hC]

instance  [hp : Fact (1 ≤ p)] : NormedGroup (Lp E p μ) :=
  NormedGroup.ofCore _
    { norm_eq_zero_iff := fun f => norm_eq_zero_iff (Ennreal.zero_lt_one.trans_le hp.1),
      triangle :=
        by 
          intro f g 
          simp only [norm_def]
          rw [←Ennreal.to_real_add (snorm_ne_top f) (snorm_ne_top g)]
          suffices h_snorm : snorm («expr⇑ » (f+g)) p μ ≤ snorm («expr⇑ » f) p μ+snorm («expr⇑ » g) p μ
          ·
            rwa [Ennreal.to_real_le_to_real (snorm_ne_top (f+g))]
            exact ennreal.add_ne_top.mpr ⟨snorm_ne_top f, snorm_ne_top g⟩
          rw [snorm_congr_ae (coe_fn_add _ _)]
          exact snorm_add_le (Lp.ae_measurable f) (Lp.ae_measurable g) hp.1,
      norm_neg :=
        by 
          simp  }

instance normed_group_L1 : NormedGroup (Lp E 1 μ) :=
  by 
    infer_instance

instance normed_group_L2 : NormedGroup (Lp E 2 μ) :=
  by 
    infer_instance

instance normed_group_Ltop : NormedGroup (Lp E ∞ μ) :=
  by 
    infer_instance

section NormedSpace

variable{𝕜 : Type _}[NormedField 𝕜][NormedSpace 𝕜 E][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

theorem mem_Lp_const_smul (c : 𝕜) (f : Lp E p μ) : c • «expr↑ » f ∈ Lp E p μ :=
  by 
    rw [mem_Lp_iff_snorm_lt_top, snorm_congr_ae (ae_eq_fun.coe_fn_smul _ _), snorm_const_smul, Ennreal.mul_lt_top_iff]
    exact Or.inl ⟨Ennreal.coe_lt_top, f.prop⟩

variable(E p μ 𝕜)

/-- The `𝕜`-submodule of elements of `α →ₘ[μ] E` whose `Lp` norm is finite.  This is `Lp E p μ`,
with extra structure. -/
def Lp_submodule : Submodule 𝕜 (α →ₘ[μ] E) :=
  { Lp E p μ with
    smul_mem' :=
      fun c f hf =>
        by 
          simpa using mem_Lp_const_smul c ⟨f, hf⟩ }

variable{E p μ 𝕜}

theorem coe_Lp_submodule : (Lp_submodule E p μ 𝕜).toAddSubgroup = Lp E p μ :=
  rfl

instance  : Module 𝕜 (Lp E p μ) :=
  { (Lp_submodule E p μ 𝕜).Module with  }

theorem coe_fn_smul (c : 𝕜) (f : Lp E p μ) : «expr⇑ » (c • f) =ᵐ[μ] c • f :=
  ae_eq_fun.coe_fn_smul _ _

theorem norm_const_smul (c : 𝕜) (f : Lp E p μ) : ∥c • f∥ = ∥c∥*∥f∥ :=
  by 
    rw [norm_def, snorm_congr_ae (coe_fn_smul _ _), snorm_const_smul c, Ennreal.to_real_mul, Ennreal.coe_to_real,
      coe_nnnorm, norm_def]

instance  [Fact (1 ≤ p)] : NormedSpace 𝕜 (Lp E p μ) :=
  { norm_smul_le :=
      fun _ _ =>
        by 
          simp [norm_const_smul] }

instance normed_space_L1 : NormedSpace 𝕜 (Lp E 1 μ) :=
  by 
    infer_instance

instance normed_space_L2 : NormedSpace 𝕜 (Lp E 2 μ) :=
  by 
    infer_instance

instance normed_space_Ltop : NormedSpace 𝕜 (Lp E ∞ μ) :=
  by 
    infer_instance

instance  [NormedSpace ℝ E] [HasScalar ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] : IsScalarTower ℝ 𝕜 (Lp E p μ) :=
  by 
    refine' ⟨fun r c f => _⟩
    ext1 
    refine' (Lp.coe_fn_smul _ _).trans _ 
    rw [smul_assoc]
    refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm 
    refine' (Lp.coe_fn_smul c f).mono fun x hx => _ 
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, hx, Pi.smul_apply]

end NormedSpace

end Lp

namespace Memℒp

variable[BorelSpace
      E][second_countable_topology
      E]{𝕜 : Type _}[NormedField 𝕜][NormedSpace 𝕜 E][MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

theorem to_Lp_const_smul {f : α → E} (c : 𝕜) (hf : mem_ℒp f p μ) : (hf.const_smul c).toLp (c • f) = c • hf.to_Lp f :=
  rfl

end Memℒp

/-! ### Indicator of a set as an element of Lᵖ

For a set `s` with `(hs : measurable_set s)` and `(hμs : μ s < ∞)`, we build
`indicator_const_Lp p hs hμs c`, the element of `Lp` corresponding to `s.indicator (λ x, c)`.
-/


section Indicator

variable{s : Set α}{hs : MeasurableSet s}{c : E}{f : α → E}{hf : AeMeasurable f μ}

theorem snorm_ess_sup_indicator_le (s : Set α) (f : α → G) : snorm_ess_sup (s.indicator f) μ ≤ snorm_ess_sup f μ :=
  by 
    refine' ess_sup_mono_ae (eventually_of_forall fun x => _)
    rw [Ennreal.coe_le_coe, nnnorm_indicator_eq_indicator_nnnorm]
    exact Set.indicator_le_self s _ x

theorem snorm_ess_sup_indicator_const_le (s : Set α) (c : G) : snorm_ess_sup (s.indicator fun x : α => c) μ ≤ ∥c∥₊ :=
  by 
    byCases' hμ0 : μ = 0
    ·
      rw [hμ0, snorm_ess_sup_measure_zero, Ennreal.coe_nonneg]
      exact zero_le'
    ·
      exact (snorm_ess_sup_indicator_le s fun x => c).trans (snorm_ess_sup_const c hμ0).le

-- error in MeasureTheory.Function.LpSpace: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem snorm_ess_sup_indicator_const_eq
(s : set α)
(c : G)
(hμs : «expr ≠ »(μ s, 0)) : «expr = »(snorm_ess_sup (s.indicator (λ x : α, c)) μ, «expr∥ ∥₊»(c)) :=
begin
  refine [expr le_antisymm (snorm_ess_sup_indicator_const_le s c) _],
  by_contra [ident h],
  push_neg ["at", ident h],
  have [ident h'] [] [":=", expr ae_iff.mp (ae_lt_of_ess_sup_lt h)],
  push_neg ["at", ident h'],
  refine [expr hμs (measure_mono_null (λ x hx_mem, _) h')],
  rw ["[", expr set.mem_set_of_eq, ",", expr set.indicator_of_mem hx_mem, "]"] [],
  exact [expr le_rfl]
end

variable(hs)

theorem snorm_indicator_le {E : Type _} [NormedGroup E] (f : α → E) : snorm (s.indicator f) p μ ≤ snorm f p μ :=
  by 
    refine' snorm_mono_ae (eventually_of_forall fun x => _)
    suffices  : ∥s.indicator f x∥₊ ≤ ∥f x∥₊
    ·
      exact Nnreal.coe_mono this 
    rw [nnnorm_indicator_eq_indicator_nnnorm]
    exact s.indicator_le_self _ x

variable{hs}

theorem snorm_indicator_const {c : G} (hs : MeasurableSet s) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
  snorm (s.indicator fun x => c) p μ = ∥c∥₊*μ s^1 / p.to_real :=
  by 
    have hp_pos : 0 < p.to_real 
    exact ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_neₓ (zero_le _) hp.symm, hp_top⟩
    rw [snorm_eq_lintegral_rpow_nnnorm hp hp_top]
    simpRw [nnnorm_indicator_eq_indicator_nnnorm, Ennreal.coe_indicator]
    have h_indicator_pow :
      (fun a : α => s.indicator (fun x : α => (∥c∥₊ : ℝ≥0∞)) a^p.to_real) =
        s.indicator fun x : α => «expr↑ » ∥c∥₊^p.to_real
    ·
      rw [Set.comp_indicator_const (∥c∥₊ : ℝ≥0∞) (fun x => x^p.to_real) _]
      simp [hp_pos]
    rw [h_indicator_pow, lintegral_indicator _ hs, set_lintegral_const, Ennreal.mul_rpow_of_nonneg]
    ·
      rw [←Ennreal.rpow_mul, mul_one_div_cancel hp_pos.ne.symm, Ennreal.rpow_one]
    ·
      simp [hp_pos.le]

theorem snorm_indicator_const' {c : G} (hs : MeasurableSet s) (hμs : μ s ≠ 0) (hp : p ≠ 0) :
  snorm (s.indicator fun _ => c) p μ = ∥c∥₊*μ s^1 / p.to_real :=
  by 
    byCases' hp_top : p = ∞
    ·
      simp [hp_top, snorm_ess_sup_indicator_const_eq s c hμs]
    ·
      exact snorm_indicator_const hs hp hp_top

theorem mem_ℒp.indicator (hs : MeasurableSet s) (hf : mem_ℒp f p μ) : mem_ℒp (s.indicator f) p μ :=
  ⟨hf.ae_measurable.indicator hs, lt_of_le_of_ltₓ (snorm_indicator_le f) hf.snorm_lt_top⟩

theorem snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict {f : α → F} (hs : MeasurableSet s) :
  snorm_ess_sup (s.indicator f) μ = snorm_ess_sup f (μ.restrict s) :=
  by 
    simpRw [snorm_ess_sup, nnnorm_indicator_eq_indicator_nnnorm, Ennreal.coe_indicator]
    byCases' hs_null : μ s = 0
    ·
      rw [measure.restrict_zero_set hs_null]
      simp only [ess_sup_measure_zero, Ennreal.ess_sup_eq_zero_iff, Ennreal.bot_eq_zero]
      have hs_empty : s =ᵐ[μ] (∅ : Set α)
      ·
        ·
          rw [ae_eq_set]
          simpa using hs_null 
      refine' (indicator_ae_eq_of_ae_eq_set hs_empty).trans _ 
      rw [Set.indicator_empty]
      rfl 
    rw [ess_sup_indicator_eq_ess_sup_restrict (eventually_of_forall fun x => _) hs hs_null]
    rw [Pi.zero_apply]
    exact zero_le _

theorem snorm_indicator_eq_snorm_restrict {f : α → F} (hs : MeasurableSet s) :
  snorm (s.indicator f) p μ = snorm f p (μ.restrict s) :=
  by 
    byCases' hp_zero : p = 0
    ·
      simp only [hp_zero, snorm_exponent_zero]
    byCases' hp_top : p = ∞
    ·
      simpRw [hp_top, snorm_exponent_top]
      exact snorm_ess_sup_indicator_eq_snorm_ess_sup_restrict hs 
    simpRw [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top]
    suffices  : (∫⁻x, ∥s.indicator f x∥₊^p.to_real ∂μ) = ∫⁻x in s, ∥f x∥₊^p.to_real ∂μ
    ·
      rw [this]
    rw [←lintegral_indicator _ hs]
    congr 
    simpRw [nnnorm_indicator_eq_indicator_nnnorm, Ennreal.coe_indicator]
    have h_zero : (fun x => x^p.to_real) (0 : ℝ≥0∞) = 0
    ·
      simp [ennreal.to_real_pos_iff.mpr ⟨Ne.bot_lt hp_zero, hp_top⟩]
    exact (Set.indicator_comp_of_zero h_zero).symm

theorem mem_ℒp_indicator_iff_restrict (hs : MeasurableSet s) : mem_ℒp (s.indicator f) p μ ↔ mem_ℒp f p (μ.restrict s) :=
  by 
    simp [mem_ℒp, ae_measurable_indicator_iff hs, snorm_indicator_eq_snorm_restrict hs]

theorem mem_ℒp_indicator_const (p : ℝ≥0∞) (hs : MeasurableSet s) (c : E) (hμsc : c = 0 ∨ μ s ≠ ∞) :
  mem_ℒp (s.indicator fun _ => c) p μ :=
  by 
    rw [mem_ℒp_indicator_iff_restrict hs]
    byCases' hp_zero : p = 0
    ·
      rw [hp_zero]
      exact mem_ℒp_zero_iff_ae_measurable.mpr ae_measurable_const 
    byCases' hp_top : p = ∞
    ·
      rw [hp_top]
      exact mem_ℒp_top_of_bound ae_measurable_const ∥c∥ (eventually_of_forall fun x => le_rfl)
    rw [mem_ℒp_const_iff hp_zero hp_top, measure.restrict_apply_univ]
    cases hμsc
    ·
      exact Or.inl hμsc
    ·
      exact Or.inr hμsc.lt_top

end Indicator

section IndicatorConstLp

open Set Function

variable{s : Set α}{hs : MeasurableSet s}{hμs : μ s ≠ ∞}{c : E}[BorelSpace E][second_countable_topology E]

/-- Indicator of a set as an element of `Lp`. -/
def indicator_const_Lp (p : ℝ≥0∞) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) : Lp E p μ :=
  mem_ℒp.to_Lp (s.indicator fun _ => c) (mem_ℒp_indicator_const p hs c (Or.inr hμs))

theorem indicator_const_Lp_coe_fn : «expr⇑ » (indicator_const_Lp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c :=
  mem_ℒp.coe_fn_to_Lp (mem_ℒp_indicator_const p hs c (Or.inr hμs))

theorem indicator_const_Lp_coe_fn_mem : ∀ᵐx : α ∂μ, x ∈ s → indicator_const_Lp p hs hμs c x = c :=
  indicator_const_Lp_coe_fn.mono fun x hx hxs => hx.trans (Set.indicator_of_mem hxs _)

theorem indicator_const_Lp_coe_fn_nmem : ∀ᵐx : α ∂μ, x ∉ s → indicator_const_Lp p hs hμs c x = 0 :=
  indicator_const_Lp_coe_fn.mono fun x hx hxs => hx.trans (Set.indicator_of_not_mem hxs _)

theorem norm_indicator_const_Lp (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  ∥indicator_const_Lp p hs hμs c∥ = ∥c∥*(μ s).toReal^1 / p.to_real :=
  by 
    rw [Lp.norm_def, snorm_congr_ae indicator_const_Lp_coe_fn, snorm_indicator_const hs hp_ne_zero hp_ne_top,
      Ennreal.to_real_mul, Ennreal.to_real_rpow, Ennreal.coe_to_real, coe_nnnorm]

theorem norm_indicator_const_Lp_top (hμs_ne_zero : μ s ≠ 0) : ∥indicator_const_Lp ∞ hs hμs c∥ = ∥c∥ :=
  by 
    rw [Lp.norm_def, snorm_congr_ae indicator_const_Lp_coe_fn,
      snorm_indicator_const' hs hμs_ne_zero Ennreal.top_ne_zero, Ennreal.top_to_real, div_zero, Ennreal.rpow_zero,
      mul_oneₓ, Ennreal.coe_to_real, coe_nnnorm]

theorem norm_indicator_const_Lp' (hp_pos : p ≠ 0) (hμs_pos : μ s ≠ 0) :
  ∥indicator_const_Lp p hs hμs c∥ = ∥c∥*(μ s).toReal^1 / p.to_real :=
  by 
    byCases' hp_top : p = ∞
    ·
      rw [hp_top, Ennreal.top_to_real, div_zero, Real.rpow_zero, mul_oneₓ]
      exact norm_indicator_const_Lp_top hμs_pos
    ·
      exact norm_indicator_const_Lp hp_pos hp_top

@[simp]
theorem indicator_const_empty :
  indicator_const_Lp p MeasurableSet.empty
      (by 
        simp  :
      μ ∅ ≠ ∞)
      c =
    0 :=
  by 
    rw [Lp.eq_zero_iff_ae_eq_zero]
    convert indicator_const_Lp_coe_fn 
    simp [Set.indicator_empty']

theorem mem_ℒp_add_of_disjoint {f g : α → E} (h : Disjoint (support f) (support g)) (hf : Measurable f)
  (hg : Measurable g) : mem_ℒp (f+g) p μ ↔ mem_ℒp f p μ ∧ mem_ℒp g p μ :=
  by 
    refine' ⟨fun hfg => ⟨_, _⟩, fun h => h.1.add h.2⟩
    ·
      rw [←indicator_add_eq_left h]
      exact hfg.indicator (measurable_set_support hf)
    ·
      rw [←indicator_add_eq_right h]
      exact hfg.indicator (measurable_set_support hg)

/-- The indicator of a disjoint union of two sets is the sum of the indicators of the sets. -/
theorem indicator_const_Lp_disjoint_union {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
  (hμt : μ t ≠ ∞) (hst : s ∩ t = ∅) (c : E) :
  indicator_const_Lp p (hs.union ht)
      ((measure_union_le s t).trans_lt (lt_top_iff_ne_top.mpr (Ennreal.add_ne_top.mpr ⟨hμs, hμt⟩))).Ne c =
    indicator_const_Lp p hs hμs c+indicator_const_Lp p ht hμt c :=
  by 
    ext1 
    refine' indicator_const_Lp_coe_fn.trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm)
    refine' eventually_eq.trans _ (eventually_eq.add indicator_const_Lp_coe_fn.symm indicator_const_Lp_coe_fn.symm)
    rw [Set.indicator_union_of_disjoint (set.disjoint_iff_inter_eq_empty.mpr hst) _]

end IndicatorConstLp

end MeasureTheory

open MeasureTheory

/-!
### Composition on `L^p`

We show that Lipschitz functions vanishing at zero act by composition on `L^p`, and specialize
this to the composition with continuous linear maps, and to the definition of the positive
part of an `L^p` function.
-/


section Composition

variable[second_countable_topology
      E][BorelSpace E][second_countable_topology F][MeasurableSpace F][BorelSpace F]{g : E → F}{c :  ℝ≥0 }

theorem LipschitzWith.comp_mem_ℒp {α E F} {K} [MeasurableSpace α] {μ : Measureₓ α} [MeasurableSpace E]
  [MeasurableSpace F] [NormedGroup E] [NormedGroup F] [BorelSpace E] [BorelSpace F] {f : α → E} {g : E → F}
  (hg : LipschitzWith K g) (g0 : g 0 = 0) (hL : mem_ℒp f p μ) : mem_ℒp (g ∘ f) p μ :=
  by 
    have  : ∀ᵐx ∂μ, ∥g (f x)∥ ≤ K*∥f x∥
    ·
      apply Filter.eventually_of_forall fun x => _ 
      rw [←dist_zero_right, ←dist_zero_right, ←g0]
      apply hg.dist_le_mul 
    exact hL.of_le_mul (hg.continuous.measurable.comp_ae_measurable hL.1) this

theorem MeasureTheory.Memℒp.of_comp_antilipschitz_with {α E F} {K'} [MeasurableSpace α] {μ : Measureₓ α}
  [MeasurableSpace E] [MeasurableSpace F] [NormedGroup E] [NormedGroup F] [BorelSpace E] [BorelSpace F]
  [CompleteSpace E] {f : α → E} {g : E → F} (hL : mem_ℒp (g ∘ f) p μ) (hg : UniformContinuous g)
  (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) : mem_ℒp f p μ :=
  by 
    have  : ∀ᵐx ∂μ, ∥f x∥ ≤ K'*∥g (f x)∥
    ·
      apply Filter.eventually_of_forall fun x => _ 
      rw [←dist_zero_right, ←dist_zero_right, ←g0]
      apply hg'.le_mul_dist 
    exact hL.of_le_mul ((hg'.closed_embedding hg).MeasurableEmbedding.ae_measurable_comp_iff.1 hL.1) this

namespace LipschitzWith

theorem mem_ℒp_comp_iff_of_antilipschitz {α E F} {K K'} [MeasurableSpace α] {μ : Measureₓ α} [MeasurableSpace E]
  [MeasurableSpace F] [NormedGroup E] [NormedGroup F] [BorelSpace E] [BorelSpace F] [CompleteSpace E] {f : α → E}
  {g : E → F} (hg : LipschitzWith K g) (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) :
  mem_ℒp (g ∘ f) p μ ↔ mem_ℒp f p μ :=
  ⟨fun h => h.of_comp_antilipschitz_with hg.uniform_continuous hg' g0, fun h => hg.comp_mem_ℒp g0 h⟩

/-- When `g` is a Lipschitz function sending `0` to `0` and `f` is in `Lp`, then `g ∘ f` is well
defined as an element of `Lp`. -/
def comp_Lp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : Lp F p μ :=
  ⟨ae_eq_fun.comp g hg.continuous.measurable (f : α →ₘ[μ] E),
    by 
      suffices  : ∀ᵐx ∂μ, ∥ae_eq_fun.comp g hg.continuous.measurable (f : α →ₘ[μ] E) x∥ ≤ c*∥f x∥
      ·
        exact Lp.mem_Lp_of_ae_le_mul this 
      filterUpwards [ae_eq_fun.coe_fn_comp g hg.continuous.measurable (f : α →ₘ[μ] E)]
      intro a ha 
      simp only [ha]
      rw [←dist_zero_right, ←dist_zero_right, ←g0]
      exact hg.dist_le_mul (f a) 0⟩

theorem coe_fn_comp_Lp (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : hg.comp_Lp g0 f =ᵐ[μ] (g ∘ f) :=
  ae_eq_fun.coe_fn_comp _ _ _

@[simp]
theorem comp_Lp_zero (hg : LipschitzWith c g) (g0 : g 0 = 0) : hg.comp_Lp g0 (0 : Lp E p μ) = 0 :=
  by 
    rw [Lp.eq_zero_iff_ae_eq_zero]
    apply (coe_fn_comp_Lp _ _ _).trans 
    filterUpwards [Lp.coe_fn_zero E p μ]
    intro a ha 
    simp [ha, g0]

theorem norm_comp_Lp_sub_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f f' : Lp E p μ) :
  ∥hg.comp_Lp g0 f - hg.comp_Lp g0 f'∥ ≤ c*∥f - f'∥ :=
  by 
    apply Lp.norm_le_mul_norm_of_ae_le_mul 
    filterUpwards [hg.coe_fn_comp_Lp g0 f, hg.coe_fn_comp_Lp g0 f', Lp.coe_fn_sub (hg.comp_Lp g0 f) (hg.comp_Lp g0 f'),
      Lp.coe_fn_sub f f']
    intro a ha1 ha2 ha3 ha4 
    simp [ha1, ha2, ha3, ha4, ←dist_eq_norm]
    exact hg.dist_le_mul (f a) (f' a)

theorem norm_comp_Lp_le (hg : LipschitzWith c g) (g0 : g 0 = 0) (f : Lp E p μ) : ∥hg.comp_Lp g0 f∥ ≤ c*∥f∥ :=
  by 
    simpa using hg.norm_comp_Lp_sub_le g0 f 0

theorem lipschitz_with_comp_Lp [Fact (1 ≤ p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
  LipschitzWith c (hg.comp_Lp g0 : Lp E p μ → Lp F p μ) :=
  LipschitzWith.of_dist_le_mul$
    fun f g =>
      by 
        simp [dist_eq_norm, norm_comp_Lp_sub_le]

theorem continuous_comp_Lp [Fact (1 ≤ p)] (hg : LipschitzWith c g) (g0 : g 0 = 0) :
  Continuous (hg.comp_Lp g0 : Lp E p μ → Lp F p μ) :=
  (lipschitz_with_comp_Lp hg g0).Continuous

end LipschitzWith

namespace ContinuousLinearMap

variable{𝕜 : Type _}[NondiscreteNormedField 𝕜][NormedSpace 𝕜 E][NormedSpace 𝕜 F]

/-- Composing `f : Lp ` with `L : E →L[𝕜] F`. -/
def comp_Lp (L : E →L[𝕜] F) (f : Lp E p μ) : Lp F p μ :=
  L.lipschitz.comp_Lp (map_zero L) f

theorem coe_fn_comp_Lp (L : E →L[𝕜] F) (f : Lp E p μ) : ∀ᵐa ∂μ, (L.comp_Lp f) a = L (f a) :=
  LipschitzWith.coe_fn_comp_Lp _ _ _

theorem coe_fn_comp_Lp' (L : E →L[𝕜] F) (f : Lp E p μ) : L.comp_Lp f =ᵐ[μ] fun a => L (f a) :=
  L.coe_fn_comp_Lp f

theorem comp_mem_ℒp (L : E →L[𝕜] F) (f : Lp E p μ) : mem_ℒp (L ∘ f) p μ :=
  (Lp.mem_ℒp (L.comp_Lp f)).ae_eq (L.coe_fn_comp_Lp' f)

theorem comp_mem_ℒp' (L : E →L[𝕜] F) {f : α → E} (hf : mem_ℒp f p μ) : mem_ℒp (L ∘ f) p μ :=
  (L.comp_mem_ℒp (hf.to_Lp f)).ae_eq (eventually_eq.fun_comp hf.coe_fn_to_Lp _)

section IsROrC

variable{K : Type _}[IsROrC K][MeasurableSpace K][BorelSpace K]

theorem _root_.measure_theory.mem_ℒp.of_real {f : α → ℝ} (hf : mem_ℒp f p μ) : mem_ℒp (fun x => (f x : K)) p μ :=
  (@IsROrC.ofRealClm K _).comp_mem_ℒp' hf

theorem _root_.measure_theory.mem_ℒp_re_im_iff {f : α → K} :
  mem_ℒp (fun x => IsROrC.re (f x)) p μ ∧ mem_ℒp (fun x => IsROrC.im (f x)) p μ ↔ mem_ℒp f p μ :=
  by 
    refine' ⟨_, fun hf => ⟨hf.re, hf.im⟩⟩
    rintro ⟨hre, him⟩
    convert hre.of_real.add (him.of_real.const_mul IsROrC.i)
    ·
      ext1 x 
      rw [Pi.add_apply, mul_commₓ, IsROrC.re_add_im]
    all_goals 
      infer_instance

end IsROrC

theorem add_comp_Lp (L L' : E →L[𝕜] F) (f : Lp E p μ) : (L+L').compLp f = L.comp_Lp f+L'.comp_Lp f :=
  by 
    ext1 
    refine' (coe_fn_comp_Lp' (L+L') f).trans _ 
    refine' eventually_eq.trans _ (Lp.coe_fn_add _ _).symm 
    refine' eventually_eq.trans _ (eventually_eq.add (L.coe_fn_comp_Lp' f).symm (L'.coe_fn_comp_Lp' f).symm)
    refine' eventually_of_forall fun x => _ 
    rfl

theorem smul_comp_Lp {𝕜'} [NormedField 𝕜'] [MeasurableSpace 𝕜'] [OpensMeasurableSpace 𝕜'] [NormedSpace 𝕜' F]
  [SmulCommClass 𝕜 𝕜' F] (c : 𝕜') (L : E →L[𝕜] F) (f : Lp E p μ) : (c • L).compLp f = c • L.comp_Lp f :=
  by 
    ext1 
    refine' (coe_fn_comp_Lp' (c • L) f).trans _ 
    refine' eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm 
    refine' (L.coe_fn_comp_Lp' f).mono fun x hx => _ 
    rw [Pi.smul_apply, hx]
    rfl

theorem norm_comp_Lp_le (L : E →L[𝕜] F) (f : Lp E p μ) : ∥L.comp_Lp f∥ ≤ ∥L∥*∥f∥ :=
  LipschitzWith.norm_comp_Lp_le _ _ _

variable(μ p)[MeasurableSpace 𝕜][OpensMeasurableSpace 𝕜]

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a `𝕜`-linear map on `Lp E p μ`. -/
def comp_Lpₗ (L : E →L[𝕜] F) : Lp E p μ →ₗ[𝕜] Lp F p μ :=
  { toFun := fun f => L.comp_Lp f,
    map_add' :=
      by 
        intro f g 
        ext1 
        filterUpwards [Lp.coe_fn_add f g, coe_fn_comp_Lp L (f+g), coe_fn_comp_Lp L f, coe_fn_comp_Lp L g,
          Lp.coe_fn_add (L.comp_Lp f) (L.comp_Lp g)]
        intro a ha1 ha2 ha3 ha4 ha5 
        simp only [ha1, ha2, ha3, ha4, ha5, map_add, Pi.add_apply],
    map_smul' :=
      by 
        intro c f 
        dsimp 
        ext1 
        filterUpwards [Lp.coe_fn_smul c f, coe_fn_comp_Lp L (c • f), Lp.coe_fn_smul c (L.comp_Lp f), coe_fn_comp_Lp L f]
        intro a ha1 ha2 ha3 ha4 
        simp only [ha1, ha2, ha3, ha4, map_smul, Pi.smul_apply] }

/-- Composing `f : Lp E p μ` with `L : E →L[𝕜] F`, seen as a continuous `𝕜`-linear map on
`Lp E p μ`. See also the similar
* `linear_map.comp_left` for functions,
* `continuous_linear_map.comp_left_continuous` for continuous functions,
* `continuous_linear_map.comp_left_continuous_bounded` for bounded continuous functions,
* `continuous_linear_map.comp_left_continuous_compact` for continuous functions on compact spaces.
-/
def comp_LpL [Fact (1 ≤ p)] (L : E →L[𝕜] F) : Lp E p μ →L[𝕜] Lp F p μ :=
  LinearMap.mkContinuous (L.comp_Lpₗ p μ) ∥L∥ L.norm_comp_Lp_le

variable{μ p}

theorem coe_fn_comp_LpL [Fact (1 ≤ p)] (L : E →L[𝕜] F) (f : Lp E p μ) : L.comp_LpL p μ f =ᵐ[μ] fun a => L (f a) :=
  L.coe_fn_comp_Lp f

theorem add_comp_LpL [Fact (1 ≤ p)] (L L' : E →L[𝕜] F) : (L+L').compLpL p μ = L.comp_LpL p μ+L'.comp_LpL p μ :=
  by 
    ext1 f 
    exact add_comp_Lp L L' f

theorem smul_comp_LpL [Fact (1 ≤ p)] (c : 𝕜) (L : E →L[𝕜] F) : (c • L).compLpL p μ = c • L.comp_LpL p μ :=
  by 
    ext1 f 
    exact smul_comp_Lp c L f

/-- TODO: written in an "apply" way because of a missing `has_scalar` instance. -/
theorem smul_comp_LpL_apply [Fact (1 ≤ p)] {𝕜'} [NormedField 𝕜'] [MeasurableSpace 𝕜'] [OpensMeasurableSpace 𝕜']
  [NormedSpace 𝕜' F] [SmulCommClass 𝕜 𝕜' F] (c : 𝕜') (L : E →L[𝕜] F) (f : Lp E p μ) :
  (c • L).compLpL p μ f = c • L.comp_LpL p μ f :=
  smul_comp_Lp c L f

theorem norm_compLpL_le [Fact (1 ≤ p)] (L : E →L[𝕜] F) : ∥L.comp_LpL p μ∥ ≤ ∥L∥ :=
  LinearMap.mk_continuous_norm_le _ (norm_nonneg _) _

end ContinuousLinearMap

namespace MeasureTheory

theorem indicator_const_Lp_eq_to_span_singleton_comp_Lp {s : Set α} [NormedSpace ℝ F] (hs : MeasurableSet s)
  (hμs : μ s ≠ ∞) (x : F) :
  indicator_const_Lp 2 hs hμs x =
    (ContinuousLinearMap.toSpanSingleton ℝ x).compLp (indicator_const_Lp 2 hs hμs (1 : ℝ)) :=
  by 
    ext1 
    refine' indicator_const_Lp_coe_fn.trans _ 
    have h_comp_Lp := (ContinuousLinearMap.toSpanSingleton ℝ x).coe_fn_comp_Lp (indicator_const_Lp 2 hs hμs (1 : ℝ))
    rw [←eventually_eq] at h_comp_Lp 
    refine' eventually_eq.trans _ h_comp_Lp.symm 
    refine' (@indicator_const_Lp_coe_fn _ _ _ 2 μ _ _ s hs hμs (1 : ℝ) _ _).mono fun y hy => _ 
    dsimp only 
    rw [hy]
    simpRw [ContinuousLinearMap.to_span_singleton_apply]
    byCases' hy_mem : y ∈ s <;> simp [hy_mem, ContinuousLinearMap.lsmul_apply]

namespace Lp

section PosPart

theorem lipschitz_with_pos_part : LipschitzWith 1 fun x : ℝ => max x 0 :=
  LipschitzWith.of_dist_le_mul$
    fun x y =>
      by 
        simp [dist, abs_max_sub_max_le_abs]

/-- Positive part of a function in `L^p`. -/
def pos_part (f : Lp ℝ p μ) : Lp ℝ p μ :=
  lipschitz_with_pos_part.compLp (max_eq_rightₓ (le_reflₓ _)) f

/-- Negative part of a function in `L^p`. -/
def neg_part (f : Lp ℝ p μ) : Lp ℝ p μ :=
  pos_part (-f)

@[normCast]
theorem coe_pos_part (f : Lp ℝ p μ) : (pos_part f : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).posPart :=
  rfl

theorem coe_fn_pos_part (f : Lp ℝ p μ) : «expr⇑ » (pos_part f) =ᵐ[μ] fun a => max (f a) 0 :=
  ae_eq_fun.coe_fn_pos_part _

theorem coe_fn_neg_part_eq_max (f : Lp ℝ p μ) : ∀ᵐa ∂μ, neg_part f a = max (-f a) 0 :=
  by 
    rw [neg_part]
    filterUpwards [coe_fn_pos_part (-f), coe_fn_neg f]
    intro a h₁ h₂ 
    rw [h₁, h₂, Pi.neg_apply]

theorem coe_fn_neg_part (f : Lp ℝ p μ) : ∀ᵐa ∂μ, neg_part f a = -min (f a) 0 :=
  (coe_fn_neg_part_eq_max f).mono$
    fun a h =>
      by 
        rw [h, ←max_neg_neg, neg_zero]

theorem continuous_pos_part [Fact (1 ≤ p)] : Continuous fun f : Lp ℝ p μ => pos_part f :=
  LipschitzWith.continuous_comp_Lp _ _

theorem continuous_neg_part [Fact (1 ≤ p)] : Continuous fun f : Lp ℝ p μ => neg_part f :=
  have eq : (fun f : Lp ℝ p μ => neg_part f) = fun f : Lp ℝ p μ => pos_part (-f) := rfl 
  by 
    rw [Eq]
    exact continuous_pos_part.comp continuous_neg

end PosPart

end Lp

end MeasureTheory

end Composition

/-!
## `L^p` is a complete space

We show that `L^p` is a complete space for `1 ≤ p`.
-/


section CompleteSpace

variable[BorelSpace E][second_countable_topology E]

namespace MeasureTheory

namespace Lp

theorem snorm'_lim_eq_lintegral_liminf {ι} [Nonempty ι] [LinearOrderₓ ι] {f : ι → α → G} {p : ℝ} (hp_nonneg : 0 ≤ p)
  {f_lim : α → G} (h_lim : ∀ᵐx : α ∂μ, tendsto (fun n => f n x) at_top (𝓝 (f_lim x))) :
  snorm' f_lim p μ = ((∫⁻a, at_top.liminf fun m => (nnnorm (f m a) : ℝ≥0∞)^p ∂μ)^1 / p) :=
  by 
    suffices h_no_pow : (∫⁻a, nnnorm (f_lim a)^p ∂μ) = ∫⁻a, at_top.liminf fun m => (nnnorm (f m a) : ℝ≥0∞)^p ∂μ
    ·
      rw [snorm', h_no_pow]
    refine' lintegral_congr_ae (h_lim.mono fun a ha => _)
    rw [tendsto.liminf_eq]
    simpRw [Ennreal.coe_rpow_of_nonneg _ hp_nonneg, Ennreal.tendsto_coe]
    refine' ((Nnreal.continuous_rpow_const hp_nonneg).Tendsto (nnnorm (f_lim a))).comp _ 
    exact (continuous_nnnorm.tendsto (f_lim a)).comp ha

theorem snorm'_lim_le_liminf_snorm' {E} [MeasurableSpace E] [NormedGroup E] [BorelSpace E] {f : ℕ → α → E} {p : ℝ}
  (hp_pos : 0 < p) (hf : ∀ n, AeMeasurable (f n) μ) {f_lim : α → E}
  (h_lim : ∀ᵐx : α ∂μ, tendsto (fun n => f n x) at_top (𝓝 (f_lim x))) :
  snorm' f_lim p μ ≤ at_top.liminf fun n => snorm' (f n) p μ :=
  by 
    rw [snorm'_lim_eq_lintegral_liminf hp_pos.le h_lim]
    rw
      [←Ennreal.le_rpow_one_div_iff
        (by 
          simp [hp_pos] :
        0 < 1 / p),
      one_div_one_div]
    refine' (lintegral_liminf_le' fun m => (hf m).ennnorm.pow_const _).trans_eq _ 
    have h_pow_liminf : ((at_top.liminf fun n => snorm' (f n) p μ)^p) = at_top.liminf fun n => snorm' (f n) p μ^p
    ·
      have h_rpow_mono := Ennreal.rpow_left_strict_mono_of_pos hp_pos 
      have h_rpow_surj := (Ennreal.rpow_left_bijective hp_pos.ne.symm).2
      refine' (h_rpow_mono.order_iso_of_surjective _ h_rpow_surj).liminf_apply _ _ _ _ 
      all_goals 
        runTac 
          is_bounded_default 
    rw [h_pow_liminf]
    simpRw [snorm', ←Ennreal.rpow_mul, one_div, inv_mul_cancel hp_pos.ne.symm, Ennreal.rpow_one]

theorem snorm_exponent_top_lim_eq_ess_sup_liminf {ι} [Nonempty ι] [LinearOrderₓ ι] {f : ι → α → G} {f_lim : α → G}
  (h_lim : ∀ᵐx : α ∂μ, tendsto (fun n => f n x) at_top (𝓝 (f_lim x))) :
  snorm f_lim ∞ μ = essSup (fun x => at_top.liminf fun m => (nnnorm (f m x) : ℝ≥0∞)) μ :=
  by 
    rw [snorm_exponent_top, snorm_ess_sup]
    refine' ess_sup_congr_ae (h_lim.mono fun x hx => _)
    rw [tendsto.liminf_eq]
    rw [Ennreal.tendsto_coe]
    exact (continuous_nnnorm.tendsto (f_lim x)).comp hx

theorem snorm_exponent_top_lim_le_liminf_snorm_exponent_top {ι} [Nonempty ι] [Encodable ι] [LinearOrderₓ ι]
  {f : ι → α → F} {f_lim : α → F} (h_lim : ∀ᵐx : α ∂μ, tendsto (fun n => f n x) at_top (𝓝 (f_lim x))) :
  snorm f_lim ∞ μ ≤ at_top.liminf fun n => snorm (f n) ∞ μ :=
  by 
    rw [snorm_exponent_top_lim_eq_ess_sup_liminf h_lim]
    simpRw [snorm_exponent_top, snorm_ess_sup]
    exact Ennreal.ess_sup_liminf_le fun n => fun x => (nnnorm (f n x) : ℝ≥0∞)

theorem snorm_lim_le_liminf_snorm {E} [MeasurableSpace E] [NormedGroup E] [BorelSpace E] {f : ℕ → α → E}
  (hf : ∀ n, AeMeasurable (f n) μ) (f_lim : α → E) (h_lim : ∀ᵐx : α ∂μ, tendsto (fun n => f n x) at_top (𝓝 (f_lim x))) :
  snorm f_lim p μ ≤ at_top.liminf fun n => snorm (f n) p μ :=
  by 
    byCases' hp0 : p = 0
    ·
      simp [hp0]
    rw [←Ne.def] at hp0 
    byCases' hp_top : p = ∞
    ·
      simpRw [hp_top]
      exact snorm_exponent_top_lim_le_liminf_snorm_exponent_top h_lim 
    simpRw [snorm_eq_snorm' hp0 hp_top]
    have hp_pos : 0 < p.to_real 
    exact ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_neₓ (zero_le _) hp0.symm, hp_top⟩
    exact snorm'_lim_le_liminf_snorm' hp_pos hf h_lim

/-! ### `Lp` is complete iff Cauchy sequences of `ℒp` have limits in `ℒp` -/


theorem tendsto_Lp_iff_tendsto_ℒp' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → Lp E p μ) (f_lim : Lp E p μ) :
  fi.tendsto f (𝓝 f_lim) ↔ fi.tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
  by 
    rw [tendsto_iff_dist_tendsto_zero]
    simpRw [dist_def]
    rw [←Ennreal.zero_to_real, Ennreal.tendsto_to_real_iff (fun n => _) Ennreal.zero_ne_top]
    rw [snorm_congr_ae (Lp.coe_fn_sub _ _).symm]
    exact Lp.snorm_ne_top _

theorem tendsto_Lp_iff_tendsto_ℒp {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → Lp E p μ) (f_lim : α → E)
  (f_lim_ℒp : mem_ℒp f_lim p μ) :
  fi.tendsto f (𝓝 (f_lim_ℒp.to_Lp f_lim)) ↔ fi.tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
  by 
    rw [tendsto_Lp_iff_tendsto_ℒp']
    suffices h_eq : (fun n => snorm (f n - mem_ℒp.to_Lp f_lim f_lim_ℒp) p μ) = fun n => snorm (f n - f_lim) p μ
    ·
      rw [h_eq]
    exact funext fun n => snorm_congr_ae (eventually_eq.rfl.sub (mem_ℒp.coe_fn_to_Lp f_lim_ℒp))

theorem tendsto_Lp_iff_tendsto_ℒp'' {ι} {fi : Filter ι} [Fact (1 ≤ p)] (f : ι → α → E) (f_ℒp : ∀ n, mem_ℒp (f n) p μ)
  (f_lim : α → E) (f_lim_ℒp : mem_ℒp f_lim p μ) :
  fi.tendsto (fun n => (f_ℒp n).toLp (f n)) (𝓝 (f_lim_ℒp.to_Lp f_lim)) ↔
    fi.tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
  by 
    convert Lp.tendsto_Lp_iff_tendsto_ℒp' _ _ 
    ext1 n 
    apply snorm_congr_ae 
    filterUpwards [((f_ℒp n).sub f_lim_ℒp).coe_fn_to_Lp, Lp.coe_fn_sub ((f_ℒp n).toLp (f n)) (f_lim_ℒp.to_Lp f_lim)]
    intro x hx₁ hx₂ 
    rw [←hx₂]
    exact hx₁.symm

theorem tendsto_Lp_of_tendsto_ℒp {ι} {fi : Filter ι} [hp : Fact (1 ≤ p)] {f : ι → Lp E p μ} (f_lim : α → E)
  (f_lim_ℒp : mem_ℒp f_lim p μ) (h_tendsto : fi.tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)) :
  fi.tendsto f (𝓝 (f_lim_ℒp.to_Lp f_lim)) :=
  (tendsto_Lp_iff_tendsto_ℒp f f_lim f_lim_ℒp).mpr h_tendsto

theorem cauchy_seq_Lp_iff_cauchy_seq_ℒp {ι} [Nonempty ι] [SemilatticeSup ι] [hp : Fact (1 ≤ p)] (f : ι → Lp E p μ) :
  CauchySeq f ↔ tendsto (fun n : ι × ι => snorm (f n.fst - f n.snd) p μ) at_top (𝓝 0) :=
  by 
    simpRw [cauchy_seq_iff_tendsto_dist_at_top_0, dist_def]
    rw [←Ennreal.zero_to_real, Ennreal.tendsto_to_real_iff (fun n => _) Ennreal.zero_ne_top]
    rw [snorm_congr_ae (Lp.coe_fn_sub _ _).symm]
    exact snorm_ne_top _

theorem complete_space_Lp_of_cauchy_complete_ℒp [hp : Fact (1 ≤ p)]
  (H :
    ∀ f : ℕ → α → E hf : ∀ n, mem_ℒp (f n) p μ B : ℕ → ℝ≥0∞ hB : (∑'i, B i) < ∞ h_cau :
      ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N,
      ∃ (f_lim : α → E)(hf_lim_meas : mem_ℒp f_lim p μ), at_top.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)) :
  CompleteSpace (Lp E p μ) :=
  by 
    let B := fun n : ℕ => (1 : ℝ) / 2^n 
    have hB_pos : ∀ n, 0 < B n 
    exact fun n => pow_pos (div_pos zero_lt_one zero_lt_two) n 
    refine' Metric.complete_of_convergent_controlled_sequences B hB_pos fun f hf => _ 
    suffices h_limit :
      ∃ (f_lim : α → E)(hf_lim_meas : mem_ℒp f_lim p μ), at_top.tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)
    ·
      rcases h_limit with ⟨f_lim, hf_lim_meas, h_tendsto⟩
      exact ⟨hf_lim_meas.to_Lp f_lim, tendsto_Lp_of_tendsto_ℒp f_lim hf_lim_meas h_tendsto⟩
    have hB : Summable B 
    exact summable_geometric_two 
    cases' hB with M hB 
    let B1 := fun n => Ennreal.ofReal (B n)
    have hB1_has : HasSum B1 (Ennreal.ofReal M)
    ·
      have h_tsum_B1 : (∑'i, B1 i) = Ennreal.ofReal M
      ·
        change (∑'n : ℕ, Ennreal.ofReal (B n)) = Ennreal.ofReal M 
        rw [←hB.tsum_eq]
        exact (Ennreal.of_real_tsum_of_nonneg (fun n => le_of_ltₓ (hB_pos n)) hB.summable).symm 
      have h_sum := (@Ennreal.summable _ B1).HasSum 
      rwa [h_tsum_B1] at h_sum 
    have hB1 : (∑'i, B1 i) < ∞
    ·
      ·
        rw [hB1_has.tsum_eq]
        exact Ennreal.of_real_lt_top 
    let f1 : ℕ → α → E := fun n => f n 
    refine' H f1 (fun n => Lp.mem_ℒp (f n)) B1 hB1 fun N n m hn hm => _ 
    specialize hf N n m hn hm 
    rw [dist_def] at hf 
    simpRw [f1, B1]
    rwa [Ennreal.lt_of_real_iff_to_real_lt]
    rw [snorm_congr_ae (Lp.coe_fn_sub _ _).symm]
    exact Lp.snorm_ne_top _

/-! ### Prove that controlled Cauchy sequences of `ℒp` have limits in `ℒp` -/


private theorem snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' {f : ℕ → α → E} (hf : ∀ n, AeMeasurable (f n) μ) {p : ℝ}
  (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) (n : ℕ) :
  snorm' (fun x => ∑i in Finset.range (n+1), norm (f (i+1) x - f i x)) p μ ≤ ∑'i, B i :=
  by 
    let f_norm_diff := fun i x => norm (f (i+1) x - f i x)
    have hgf_norm_diff :
      ∀ n, (fun x => ∑i in Finset.range (n+1), norm (f (i+1) x - f i x)) = ∑i in Finset.range (n+1), f_norm_diff i 
    exact
      fun n =>
        funext
          fun x =>
            by 
              simp [f_norm_diff]
    rw [hgf_norm_diff]
    refine' (snorm'_sum_le (fun i _ => ((hf (i+1)).sub (hf i)).norm) hp1).trans _ 
    simpRw [←Pi.sub_apply, snorm'_norm]
    refine' (Finset.sum_le_sum _).trans (sum_le_tsum _ (fun m _ => zero_le _) Ennreal.summable)
    exact fun m _ => (h_cau m (m+1) m (Nat.le_succₓ m) (le_reflₓ m)).le

private theorem lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum {f : ℕ → α → E} (hf : ∀ n, AeMeasurable (f n) μ) {p : ℝ}
  (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (n : ℕ)
  (hn : snorm' (fun x => ∑i in Finset.range (n+1), norm (f (i+1) x - f i x)) p μ ≤ ∑'i, B i) :
  (∫⁻a, (∑i in Finset.range (n+1), nnnorm (f (i+1) a - f i a) : ℝ≥0∞)^p ∂μ) ≤ ((∑'i, B i)^p) :=
  by 
    have hp_pos : 0 < p := zero_lt_one.trans_le hp1 
    rw [←one_div_one_div p,
      @Ennreal.le_rpow_one_div_iff _ _ (1 / p)
        (by 
          simp [hp_pos]),
      one_div_one_div p]
    simpRw [snorm']  at hn 
    have h_nnnorm_nonneg :
      (fun a => (nnnorm (∑i in Finset.range (n+1), ∥f (i+1) a - f i a∥) : ℝ≥0∞)^p) =
        fun a => (∑i in Finset.range (n+1), (nnnorm (f (i+1) a - f i a) : ℝ≥0∞))^p
    ·
      ext1 a 
      congr 
      simpRw [←of_real_norm_eq_coe_nnnorm]
      rw [←Ennreal.of_real_sum_of_nonneg]
      ·
        rw [Real.norm_of_nonneg _]
        exact Finset.sum_nonneg fun x hx => norm_nonneg _
      ·
        exact fun x hx => norm_nonneg _ 
    change
      ((∫⁻a, (fun x => «expr↑ » (nnnorm (∑i in Finset.range (n+1), ∥f (i+1) x - f i x∥))^p) a ∂μ)^1 / p) ≤ ∑'i, B i at
      hn 
    rwa [h_nnnorm_nonneg] at hn

private theorem lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum {f : ℕ → α → E} (hf : ∀ n, AeMeasurable (f n) μ) {p : ℝ}
  (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞}
  (h : ∀ n, (∫⁻a, (∑i in Finset.range (n+1), nnnorm (f (i+1) a - f i a) : ℝ≥0∞)^p ∂μ) ≤ ((∑'i, B i)^p)) :
  ((∫⁻a, (∑'i, nnnorm (f (i+1) a - f i a) : ℝ≥0∞)^p ∂μ)^1 / p) ≤ ∑'i, B i :=
  by 
    have hp_pos : 0 < p := zero_lt_one.trans_le hp1 
    suffices h_pow : (∫⁻a, (∑'i, nnnorm (f (i+1) a - f i a) : ℝ≥0∞)^p ∂μ) ≤ ((∑'i, B i)^p)
    ·
      rwa
        [←Ennreal.le_rpow_one_div_iff
          (by 
            simp [hp_pos] :
          0 < 1 / p),
        one_div_one_div]
    have h_tsum_1 : ∀ g : ℕ → ℝ≥0∞, (∑'i, g i) = at_top.liminf fun n => ∑i in Finset.range (n+1), g i
    ·
      ·
        intro g 
        rw [Ennreal.tsum_eq_liminf_sum_nat, ←liminf_nat_add _ 1]
    simpRw [h_tsum_1 _]
    rw [←h_tsum_1]
    have h_liminf_pow :
      (∫⁻a, (at_top.liminf fun n => ∑i in Finset.range (n+1), nnnorm (f (i+1) a - f i a))^p ∂μ) =
        ∫⁻a, at_top.liminf fun n => (∑i in Finset.range (n+1), nnnorm (f (i+1) a - f i a))^p ∂μ
    ·
      refine' lintegral_congr fun x => _ 
      have h_rpow_mono := Ennreal.rpow_left_strict_mono_of_pos (zero_lt_one.trans_le hp1)
      have h_rpow_surj := (Ennreal.rpow_left_bijective hp_pos.ne.symm).2
      refine' (h_rpow_mono.order_iso_of_surjective _ h_rpow_surj).liminf_apply _ _ _ _ 
      all_goals 
        runTac 
          is_bounded_default 
    rw [h_liminf_pow]
    refine' (lintegral_liminf_le' _).trans _
    ·
      exact
        fun n => (Finset.ae_measurable_sum (Finset.range (n+1)) fun i _ => ((hf (i+1)).sub (hf i)).ennnorm).pow_const _
    ·
      exact liminf_le_of_frequently_le' (frequently_of_forall h)

private theorem tsum_nnnorm_sub_ae_lt_top {f : ℕ → α → E} (hf : ∀ n, AeMeasurable (f n) μ) {p : ℝ} (hp1 : 1 ≤ p)
  {B : ℕ → ℝ≥0∞} (hB : (∑'i, B i) ≠ ∞) (h : ((∫⁻a, (∑'i, nnnorm (f (i+1) a - f i a) : ℝ≥0∞)^p ∂μ)^1 / p) ≤ ∑'i, B i) :
  ∀ᵐx ∂μ, (∑'i, nnnorm (f (i+1) x - f i x) : ℝ≥0∞) < ∞ :=
  by 
    have hp_pos : 0 < p := zero_lt_one.trans_le hp1 
    have h_integral : (∫⁻a, (∑'i, ∥f (i+1) a - f i a∥₊ : ℝ≥0∞)^p ∂μ) < ∞
    ·
      have h_tsum_lt_top : ((∑'i, B i)^p) < ∞
      exact Ennreal.rpow_lt_top_of_nonneg hp_pos.le hB 
      refine' lt_of_le_of_ltₓ _ h_tsum_lt_top 
      rwa
        [←Ennreal.le_rpow_one_div_iff
          (by 
            simp [hp_pos] :
          0 < 1 / p),
        one_div_one_div] at h 
    have rpow_ae_lt_top : ∀ᵐx ∂μ, ((∑'i, nnnorm (f (i+1) x - f i x) : ℝ≥0∞)^p) < ∞
    ·
      refine' ae_lt_top' (AeMeasurable.pow_const _ _) h_integral.ne 
      exact AeMeasurable.ennreal_tsum fun n => ((hf (n+1)).sub (hf n)).ennnorm 
    refine' rpow_ae_lt_top.mono fun x hx => _ 
    rwa [←Ennreal.lt_rpow_one_div_iff hp_pos,
      Ennreal.top_rpow_of_pos
        (by 
          simp [hp_pos] :
        0 < 1 / p)] at
      hx

theorem ae_tendsto_of_cauchy_snorm' [CompleteSpace E] {f : ℕ → α → E} {p : ℝ} (hf : ∀ n, AeMeasurable (f n) μ)
  (hp1 : 1 ≤ p) {B : ℕ → ℝ≥0∞} (hB : (∑'i, B i) ≠ ∞)
  (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm' (f n - f m) p μ < B N) :
  ∀ᵐx ∂μ, ∃ l : E, at_top.Tendsto (fun n => f n x) (𝓝 l) :=
  by 
    have h_summable : ∀ᵐx ∂μ, Summable fun i : ℕ => f (i+1) x - f i x
    ·
      have h1 : ∀ n, snorm' (fun x => ∑i in Finset.range (n+1), norm (f (i+1) x - f i x)) p μ ≤ ∑'i, B i 
      exact snorm'_sum_norm_sub_le_tsum_of_cauchy_snorm' hf hp1 h_cau 
      have h2 : ∀ n, (∫⁻a, (∑i in Finset.range (n+1), nnnorm (f (i+1) a - f i a) : ℝ≥0∞)^p ∂μ) ≤ ((∑'i, B i)^p)
      exact fun n => lintegral_rpow_sum_coe_nnnorm_sub_le_rpow_tsum hf hp1 n (h1 n)
      have h3 : ((∫⁻a, (∑'i, nnnorm (f (i+1) a - f i a) : ℝ≥0∞)^p ∂μ)^1 / p) ≤ ∑'i, B i 
      exact lintegral_rpow_tsum_coe_nnnorm_sub_le_tsum hf hp1 h2 
      have h4 : ∀ᵐx ∂μ, (∑'i, nnnorm (f (i+1) x - f i x) : ℝ≥0∞) < ∞
      exact tsum_nnnorm_sub_ae_lt_top hf hp1 hB h3 
      exact
        h4.mono
          fun x hx => summable_of_summable_nnnorm (ennreal.tsum_coe_ne_top_iff_summable.mp (lt_top_iff_ne_top.mp hx))
    have h : ∀ᵐx ∂μ, ∃ l : E, at_top.tendsto (fun n => ∑i in Finset.range n, f (i+1) x - f i x) (𝓝 l)
    ·
      refine' h_summable.mono fun x hx => _ 
      let hx_sum := hx.has_sum.tendsto_sum_nat 
      exact ⟨∑'i, f (i+1) x - f i x, hx_sum⟩
    refine' h.mono fun x hx => _ 
    cases' hx with l hx 
    have h_rw_sum : (fun n => ∑i in Finset.range n, f (i+1) x - f i x) = fun n => f n x - f 0 x
    ·
      ext1 n 
      change (∑i : ℕ in Finset.range n, (fun m => f m x) (i+1) - (fun m => f m x) i) = f n x - f 0 x 
      rw [Finset.sum_range_sub]
    rw [h_rw_sum] at hx 
    have hf_rw : (fun n => f n x) = fun n => (f n x - f 0 x)+f 0 x
    ·
      ·
        ext1 n 
        abel 
    rw [hf_rw]
    exact ⟨l+f 0 x, tendsto.add_const _ hx⟩

theorem ae_tendsto_of_cauchy_snorm [CompleteSpace E] {f : ℕ → α → E} (hf : ∀ n, AeMeasurable (f n) μ) (hp : 1 ≤ p)
  {B : ℕ → ℝ≥0∞} (hB : (∑'i, B i) ≠ ∞) (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
  ∀ᵐx ∂μ, ∃ l : E, at_top.Tendsto (fun n => f n x) (𝓝 l) :=
  by 
    byCases' hp_top : p = ∞
    ·
      simpRw [hp_top]  at *
      have h_cau_ae : ∀ᵐx ∂μ, ∀ N n m, N ≤ n → N ≤ m → (nnnorm ((f n - f m) x) : ℝ≥0∞) < B N
      ·
        simpRw [ae_all_iff, ae_imp_iff]
        exact fun N n m hnN hmN => ae_lt_of_ess_sup_lt (h_cau N n m hnN hmN)
      simpRw [snorm_exponent_top, snorm_ess_sup]  at h_cau 
      refine' h_cau_ae.mono fun x hx => cauchy_seq_tendsto_of_complete _ 
      refine' cauchy_seq_of_le_tendsto_0 (fun n => (B n).toReal) _ _
      ·
        intro n m N hnN hmN 
        specialize hx N n m hnN hmN 
        rw [dist_eq_norm, ←Ennreal.to_real_of_real (norm_nonneg _),
          Ennreal.to_real_le_to_real Ennreal.of_real_ne_top (Ennreal.ne_top_of_tsum_ne_top hB N)]
        rw [←of_real_norm_eq_coe_nnnorm] at hx 
        exact hx.le
      ·
        rw [←Ennreal.zero_to_real]
        exact tendsto.comp (Ennreal.tendsto_to_real Ennreal.zero_ne_top) (Ennreal.tendsto_at_top_zero_of_tsum_ne_top hB)
    have hp1 : 1 ≤ p.to_real
    ·
      rw [←Ennreal.of_real_le_iff_le_to_real hp_top, Ennreal.of_real_one]
      exact hp 
    have h_cau' : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm' (f n - f m) p.to_real μ < B N
    ·
      intro N n m hn hm 
      specialize h_cau N n m hn hm 
      rwa [snorm_eq_snorm' (ennreal.zero_lt_one.trans_le hp).Ne.symm hp_top] at h_cau 
    exact ae_tendsto_of_cauchy_snorm' hf hp1 hB h_cau'

theorem cauchy_tendsto_of_tendsto {f : ℕ → α → E} (hf : ∀ n, AeMeasurable (f n) μ) (f_lim : α → E) {B : ℕ → ℝ≥0∞}
  (hB : (∑'i, B i) ≠ ∞) (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N)
  (h_lim : ∀ᵐx : α ∂μ, tendsto (fun n => f n x) at_top (𝓝 (f_lim x))) :
  at_top.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
  by 
    rw [Ennreal.tendsto_at_top_zero]
    intro ε hε 
    have h_B : ∃ N : ℕ, B N ≤ ε
    ·
      suffices h_tendsto_zero : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B n ≤ ε 
      exact ⟨h_tendsto_zero.some, h_tendsto_zero.some_spec _ (le_reflₓ _)⟩
      exact (ennreal.tendsto_at_top_zero.mp (Ennreal.tendsto_at_top_zero_of_tsum_ne_top hB)) ε hε 
    cases' h_B with N h_B 
    refine' ⟨N, fun n hn => _⟩
    have h_sub : snorm (f n - f_lim) p μ ≤ at_top.liminf fun m => snorm (f n - f m) p μ
    ·
      refine' snorm_lim_le_liminf_snorm (fun m => (hf n).sub (hf m)) (f n - f_lim) _ 
      refine' h_lim.mono fun x hx => _ 
      simpRw [sub_eq_add_neg]
      exact tendsto.add tendsto_const_nhds (tendsto.neg hx)
    refine' h_sub.trans _ 
    refine' liminf_le_of_frequently_le' (frequently_at_top.mpr _)
    refine' fun N1 => ⟨max N N1, le_max_rightₓ _ _, _⟩
    exact (h_cau N n (max N N1) hn (le_max_leftₓ _ _)).le.trans h_B

theorem mem_ℒp_of_cauchy_tendsto (hp : 1 ≤ p) {f : ℕ → α → E} (hf : ∀ n, mem_ℒp (f n) p μ) (f_lim : α → E)
  (h_lim_meas : AeMeasurable f_lim μ) (h_tendsto : at_top.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)) :
  mem_ℒp f_lim p μ :=
  by 
    refine' ⟨h_lim_meas, _⟩
    rw [Ennreal.tendsto_at_top_zero] at h_tendsto 
    cases' h_tendsto 1 Ennreal.zero_lt_one with N h_tendsto_1 
    specialize h_tendsto_1 N (le_reflₓ N)
    have h_add : f_lim = (f_lim - f N)+f N
    ·
      abel 
    rw [h_add]
    refine' lt_of_le_of_ltₓ (snorm_add_le (h_lim_meas.sub (hf N).1) (hf N).1 hp) _ 
    rw [Ennreal.add_lt_top]
    split 
    ·
      refine' lt_of_le_of_ltₓ _ Ennreal.one_lt_top 
      have h_neg : f_lim - f N = -(f N - f_lim)
      ·
        simp 
      rwa [h_neg, snorm_neg]
    ·
      exact (hf N).2

theorem cauchy_complete_ℒp [CompleteSpace E] (hp : 1 ≤ p) {f : ℕ → α → E} (hf : ∀ n, mem_ℒp (f n) p μ) {B : ℕ → ℝ≥0∞}
  (hB : (∑'i, B i) ≠ ∞) (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m → snorm (f n - f m) p μ < B N) :
  ∃ (f_lim : α → E)(hf_lim_meas : mem_ℒp f_lim p μ), at_top.Tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0) :=
  by 
    obtain ⟨f_lim, h_f_lim_meas, h_lim⟩ :
      ∃ (f_lim : α → E)(hf_lim_meas : Measurable f_lim), ∀ᵐx ∂μ, tendsto (fun n => f n x) at_top (nhds (f_lim x))
    exact
      measurable_limit_of_tendsto_metric_ae (fun n => (hf n).1)
        (ae_tendsto_of_cauchy_snorm (fun n => (hf n).1) hp hB h_cau)
    have h_tendsto' : at_top.tendsto (fun n => snorm (f n - f_lim) p μ) (𝓝 0)
    exact cauchy_tendsto_of_tendsto (fun m => (hf m).1) f_lim hB h_cau h_lim 
    have h_ℒp_lim : mem_ℒp f_lim p μ 
    exact mem_ℒp_of_cauchy_tendsto hp hf f_lim h_f_lim_meas.ae_measurable h_tendsto' 
    exact ⟨f_lim, h_ℒp_lim, h_tendsto'⟩

/-! ### `Lp` is complete for `1 ≤ p` -/


instance  [CompleteSpace E] [hp : Fact (1 ≤ p)] : CompleteSpace (Lp E p μ) :=
  complete_space_Lp_of_cauchy_complete_ℒp$ fun f hf B hB h_cau => cauchy_complete_ℒp hp.elim hf hB.ne h_cau

end Lp

end MeasureTheory

end CompleteSpace

/-! ### Continuous functions in `Lp` -/


open_locale BoundedContinuousFunction

open BoundedContinuousFunction

variable[BorelSpace E][second_countable_topology E][TopologicalSpace α][BorelSpace α]

variable(E p μ)

/-- An additive subgroup of `Lp E p μ`, consisting of the equivalence classes which contain a
bounded continuous representative. -/
def MeasureTheory.lp.boundedContinuousFunction : AddSubgroup (Lp E p μ) :=
  AddSubgroup.addSubgroupOf ((ContinuousMap.toAeEqFunAddHom μ).comp (forget_boundedness_add_hom α E)).range (Lp E p μ)

variable{E p μ}

/-- By definition, the elements of `Lp.bounded_continuous_function E p μ` are the elements of
`Lp E p μ` which contain a bounded continuous representative. -/
theorem MeasureTheory.lp.mem_bounded_continuous_function_iff {f : Lp E p μ} :
  f ∈ MeasureTheory.lp.boundedContinuousFunction E p μ ↔
    ∃ f₀ : α →ᵇ E, f₀.to_continuous_map.to_ae_eq_fun μ = (f : α →ₘ[μ] E) :=
  AddSubgroup.mem_add_subgroup_of

namespace BoundedContinuousFunction

variable[is_finite_measure μ]

/-- A bounded continuous function on a finite-measure space is in `Lp`. -/
theorem mem_Lp (f : α →ᵇ E) : f.to_continuous_map.to_ae_eq_fun μ ∈ Lp E p μ :=
  by 
    refine' Lp.mem_Lp_of_ae_bound ∥f∥ _ 
    filterUpwards [f.to_continuous_map.coe_fn_to_ae_eq_fun μ]
    intro x hx 
    convert f.norm_coe_le_norm x

/-- The `Lp`-norm of a bounded continuous function is at most a constant (depending on the measure
of the whole space) times its sup-norm. -/
theorem Lp_norm_le (f : α →ᵇ E) :
  ∥(⟨f.to_continuous_map.to_ae_eq_fun μ, mem_Lp f⟩ : Lp E p μ)∥ ≤ (measure_univ_nnreal μ^p.to_real⁻¹)*∥f∥ :=
  by 
    apply Lp.norm_le_of_ae_bound (norm_nonneg f)
    ·
      refine' (f.to_continuous_map.coe_fn_to_ae_eq_fun μ).mono _ 
      intro x hx 
      convert f.norm_coe_le_norm x
    ·
      infer_instance

variable(p μ)

/-- The normed group homomorphism of considering a bounded continuous function on a finite-measure
space as an element of `Lp`. -/
def to_Lp_hom [Fact (1 ≤ p)] : NormedGroupHom (α →ᵇ E) (Lp E p μ) :=
  { AddMonoidHom.codRestrict ((ContinuousMap.toAeEqFunAddHom μ).comp (forget_boundedness_add_hom α E)) (Lp E p μ)
      mem_Lp with
    bound' := ⟨_, Lp_norm_le⟩ }

theorem range_to_Lp_hom [Fact (1 ≤ p)] :
  ((to_Lp_hom p μ).range : AddSubgroup (Lp E p μ)) = MeasureTheory.lp.boundedContinuousFunction E p μ :=
  by 
    symm 
    convert
      AddMonoidHom.add_subgroup_of_range_eq_of_le
        ((ContinuousMap.toAeEqFunAddHom μ).comp (forget_boundedness_add_hom α E))
        (by 
          rintro - ⟨f, rfl⟩
          exact mem_Lp f :
        _ ≤ Lp E p μ)

variable(𝕜 : Type _)[MeasurableSpace 𝕜]

/-- The bounded linear map of considering a bounded continuous function on a finite-measure space
as an element of `Lp`. -/
def to_Lp [NormedField 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] : (α →ᵇ E) →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict (Lp.Lp_submodule E p μ 𝕜)
      ((ContinuousMap.toAeEqFunLinearMap μ).comp (forget_boundedness_linear_map α E 𝕜)) mem_Lp)
    _ Lp_norm_le

variable{𝕜}

theorem range_to_Lp [NormedField 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] :
  ((to_Lp p μ 𝕜).range.toAddSubgroup : AddSubgroup (Lp E p μ)) = MeasureTheory.lp.boundedContinuousFunction E p μ :=
  range_to_Lp_hom p μ

variable{p}

theorem coe_fn_to_Lp [NormedField 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] (f : α →ᵇ E) :
  to_Lp p μ 𝕜 f =ᵐ[μ] f :=
  ae_eq_fun.coe_fn_mk f _

theorem to_Lp_norm_le [NondiscreteNormedField 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E] [Fact (1 ≤ p)] :
  ∥(to_Lp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)∥ ≤ (measure_univ_nnreal μ^p.to_real⁻¹) :=
  LinearMap.mk_continuous_norm_le _ (measure_univ_nnreal μ^p.to_real⁻¹).coe_nonneg _

end BoundedContinuousFunction

namespace ContinuousMap

variable[CompactSpace α][is_finite_measure μ]

variable(𝕜 : Type _)[MeasurableSpace 𝕜](p μ)[Fact (1 ≤ p)]

/-- The bounded linear map of considering a continuous function on a compact finite-measure
space `α` as an element of `Lp`.  By definition, the norm on `C(α, E)` is the sup-norm, transferred
from the space `α →ᵇ E` of bounded continuous functions, so this construction is just a matter of
transferring the structure from `bounded_continuous_function.to_Lp` along the isometry. -/
def to_Lp [NormedField 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E] : C(α, E) →L[𝕜] Lp E p μ :=
  (BoundedContinuousFunction.toLp p μ 𝕜).comp
    (linear_isometry_bounded_of_compact α E 𝕜).toLinearIsometry.toContinuousLinearMap

variable{𝕜}

theorem range_to_Lp [NormedField 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E] :
  ((to_Lp p μ 𝕜).range.toAddSubgroup : AddSubgroup (Lp E p μ)) = MeasureTheory.lp.boundedContinuousFunction E p μ :=
  by 
    refine' SetLike.ext' _ 
    have  := (linear_isometry_bounded_of_compact α E 𝕜).Surjective 
    convert Function.Surjective.range_comp this (BoundedContinuousFunction.toLp p μ 𝕜)
    rw [←BoundedContinuousFunction.range_to_Lp p μ]
    rfl

variable{p}

theorem coe_fn_to_Lp [NormedField 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) : to_Lp p μ 𝕜 f =ᵐ[μ] f :=
  ae_eq_fun.coe_fn_mk f _

theorem to_Lp_def [NormedField 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) :
  to_Lp p μ 𝕜 f = BoundedContinuousFunction.toLp p μ 𝕜 (linear_isometry_bounded_of_compact α E 𝕜 f) :=
  rfl

@[simp]
theorem to_Lp_comp_forget_boundedness [NormedField 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E] (f : α →ᵇ E) :
  to_Lp p μ 𝕜 (BoundedContinuousFunction.forgetBoundedness α E f) = BoundedContinuousFunction.toLp p μ 𝕜 f :=
  rfl

@[simp]
theorem coe_to_Lp [NormedField 𝕜] [OpensMeasurableSpace 𝕜] [NormedSpace 𝕜 E] (f : C(α, E)) :
  (to_Lp p μ 𝕜 f : α →ₘ[μ] E) = f.to_ae_eq_fun μ :=
  rfl

variable[NondiscreteNormedField 𝕜][OpensMeasurableSpace 𝕜][NormedSpace 𝕜 E]

theorem to_Lp_norm_eq_to_Lp_norm_coe :
  ∥(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)∥ = ∥(BoundedContinuousFunction.toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ)∥ :=
  ContinuousLinearMap.op_norm_comp_linear_isometry_equiv _ _

/-- Bound for the operator norm of `continuous_map.to_Lp`. -/
theorem to_Lp_norm_le : ∥(to_Lp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ)∥ ≤ (measure_univ_nnreal μ^p.to_real⁻¹) :=
  by 
    rw [to_Lp_norm_eq_to_Lp_norm_coe]
    exact BoundedContinuousFunction.to_Lp_norm_le μ

end ContinuousMap

