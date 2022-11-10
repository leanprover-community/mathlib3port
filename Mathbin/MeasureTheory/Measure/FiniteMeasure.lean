/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathbin.MeasureTheory.Integral.SetIntegral
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Topology.Algebra.Module.WeakDual

/-!
# Finite measures

This file defines the type of finite measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of finite measures is equipped with the topology of weak convergence
of measures. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f`, the integration of `f` against the
measure is continuous.

## Main definitions

The main definitions are
 * the type `measure_theory.finite_measure Ω` with the topology of weak convergence;
 * `measure_theory.finite_measure.to_weak_dual_bcnn : finite_measure Ω → (weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0))`
   allowing to interpret a finite measure as a continuous linear functional on the space of
   bounded continuous nonnegative functions on `Ω`. This is used for the definition of the
   topology of weak convergence.

## Main results

 * Finite measures `μ` on `Ω` give rise to continuous linear functionals on the space of
   bounded continuous nonnegative functions on `Ω` via integration:
   `measure_theory.finite_measure.to_weak_dual_bcnn : finite_measure Ω → (weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0))`
 * `measure_theory.finite_measure.tendsto_iff_forall_integral_tendsto`: Convergence of finite
   measures is characterized by the convergence of integrals of all bounded continuous functions.
   This shows that the chosen definition of topology coincides with the common textbook definition
   of weak convergence of measures. A similar characterization by the convergence of integrals (in
   the `measure_theory.lintegral` sense) of all bounded continuous nonnegative functions is
   `measure_theory.finite_measure.tendsto_iff_forall_lintegral_tendsto`.

## Implementation notes

The topology of weak convergence of finite Borel measures is defined using a mapping from
`measure_theory.finite_measure Ω` to `weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0)`, inheriting the topology from the
latter.

The implementation of `measure_theory.finite_measure Ω` and is directly as a subtype of
`measure_theory.measure Ω`, and the coercion to a function is the composition `ennreal.to_nnreal`
and the coercion to function of `measure_theory.measure Ω`. Another alternative would have been to
use a bijection with `measure_theory.vector_measure Ω ℝ≥0` as an intermediate step. Some
considerations:
 * Potential advantages of using the `nnreal`-valued vector measure alternative:
   * The coercion to function would avoid need to compose with `ennreal.to_nnreal`, the
     `nnreal`-valued API could be more directly available.
 * Potential drawbacks of the vector measure alternative:
   * The coercion to function would lose monotonicity, as non-measurable sets would be defined to
     have measure 0.
   * No integration theory directly. E.g., the topology definition requires
     `measure_theory.lintegral` w.r.t. a coercion to `measure_theory.measure Ω` in any case.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, finite measure

-/


noncomputable section

open MeasureTheory

open Set

open Filter

open BoundedContinuousFunction

open TopologicalSpace Ennreal Nnreal BoundedContinuousFunction

namespace MeasureTheory

namespace FiniteMeasure

section FiniteMeasure

/-! ### Finite measures

In this section we define the `Type` of `finite_measure Ω`, when `Ω` is a measurable space. Finite
measures on `Ω` are a module over `ℝ≥0`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[opens_measurable_space Ω]`), then `finite_measure Ω` is equipped with the topology
of weak convergence of measures. This is implemented by defining a pairing of finite measures `μ`
on `Ω` with continuous bounded nonnegative functions `f : Ω →ᵇ ℝ≥0` via integration, and using the
associated weak topology (essentially the weak-star topology on the dual of `Ω →ᵇ ℝ≥0`).
-/


variable {Ω : Type _} [MeasurableSpace Ω]

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
def _root_.measure_theory.finite_measure (Ω : Type _) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsFiniteMeasure μ }

/-- A finite measure can be interpreted as a measure. -/
instance : Coe (FiniteMeasure Ω) (MeasureTheory.Measure Ω) :=
  coeSubtype

instance isFiniteMeasure (μ : FiniteMeasure Ω) : IsFiniteMeasure (μ : Measure Ω) :=
  μ.Prop

instance : CoeFun (FiniteMeasure Ω) fun _ => Set Ω → ℝ≥0 :=
  ⟨fun μ s => (μ s).toNnreal⟩

theorem coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : FiniteMeasure Ω) :
    (ν : Set Ω → ℝ≥0) = fun s => ((ν : Measure Ω) s).toNnreal :=
  rfl

@[simp]
theorem ennreal_coe_fn_eq_coe_fn_to_measure (ν : FiniteMeasure Ω) (s : Set Ω) : (ν s : ℝ≥0∞) = (ν : Measure Ω) s :=
  Ennreal.coe_to_nnreal (measure_lt_top (↑ν) s).Ne

@[simp]
theorem val_eq_to_measure (ν : FiniteMeasure Ω) : ν.val = (ν : Measure Ω) :=
  rfl

theorem coe_injective : Function.Injective (coe : FiniteMeasure Ω → Measure Ω) :=
  Subtype.coe_injective

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`(μ : measure Ω) univ`. -/
def mass (μ : FiniteMeasure Ω) : ℝ≥0 :=
  μ Univ

@[simp]
theorem ennreal_mass {μ : FiniteMeasure Ω} : (μ.mass : ℝ≥0∞) = (μ : Measure Ω) Univ :=
  ennreal_coe_fn_eq_coe_fn_to_measure μ Set.Univ

instance hasZero : Zero (FiniteMeasure Ω) where zero := ⟨0, MeasureTheory.isFiniteMeasureZero⟩

@[simp]
theorem Zero.mass : (0 : FiniteMeasure Ω).mass = 0 :=
  rfl

@[simp]
theorem mass_zero_iff (μ : FiniteMeasure Ω) : μ.mass = 0 ↔ μ = 0 := by
  refine' ⟨fun μ_mass => _, fun hμ => by simp only [hμ, zero.mass]⟩
  ext1
  apply measure.measure_univ_eq_zero.mp
  rwa [← ennreal_mass, Ennreal.coe_eq_zero]

theorem mass_nonzero_iff (μ : FiniteMeasure Ω) : μ.mass ≠ 0 ↔ μ ≠ 0 := by
  rw [not_iff_not]
  exact finite_measure.mass_zero_iff μ

@[ext]
theorem extensionality (μ ν : FiniteMeasure Ω) (h : ∀ s : Set Ω, MeasurableSet s → μ s = ν s) : μ = ν := by
  ext1
  ext1 s s_mble
  simpa [ennreal_coe_fn_eq_coe_fn_to_measure] using congr_arg (coe : ℝ≥0 → ℝ≥0∞) (h s s_mble)

instance : Inhabited (FiniteMeasure Ω) :=
  ⟨0⟩

instance : Add (FiniteMeasure Ω) where add μ ν := ⟨μ + ν, MeasureTheory.isFiniteMeasureAdd⟩

variable {R : Type _} [HasSmul R ℝ≥0] [HasSmul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]

instance : HasSmul R (FiniteMeasure Ω) where smul (c : R) μ := ⟨c • μ, MeasureTheory.isFiniteMeasureSmulOfNnrealTower⟩

@[simp, norm_cast]
theorem coe_zero : (coe : FiniteMeasure Ω → Measure Ω) 0 = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_add (μ ν : FiniteMeasure Ω) : ↑(μ + ν) = (↑μ + ↑ν : Measure Ω) :=
  rfl

@[simp, norm_cast]
theorem coe_smul (c : R) (μ : FiniteMeasure Ω) : ↑(c • μ) = (c • ↑μ : Measure Ω) :=
  rfl

@[simp, norm_cast]
theorem coe_fn_zero : (⇑(0 : FiniteMeasure Ω) : Set Ω → ℝ≥0) = (0 : Set Ω → ℝ≥0) := by
  funext
  rfl

@[simp, norm_cast]
theorem coe_fn_add (μ ν : FiniteMeasure Ω) : (⇑(μ + ν) : Set Ω → ℝ≥0) = (⇑μ + ⇑ν : Set Ω → ℝ≥0) := by
  funext
  simp [← Ennreal.coe_eq_coe]

@[simp, norm_cast]
theorem coe_fn_smul [IsScalarTower R ℝ≥0 ℝ≥0] (c : R) (μ : FiniteMeasure Ω) :
    (⇑(c • μ) : Set Ω → ℝ≥0) = c • (⇑μ : Set Ω → ℝ≥0) := by
  funext
  simp [← Ennreal.coe_eq_coe, Ennreal.coe_smul]

instance : AddCommMonoid (FiniteMeasure Ω) :=
  coe_injective.AddCommMonoid coe coe_zero coe_add fun _ _ => coe_smul _ _

/-- Coercion is an `add_monoid_hom`. -/
@[simps]
def coeAddMonoidHom : FiniteMeasure Ω →+ Measure Ω where
  toFun := coe
  map_zero' := coe_zero
  map_add' := coe_add

instance {Ω : Type _} [MeasurableSpace Ω] : Module ℝ≥0 (FiniteMeasure Ω) :=
  Function.Injective.module _ coeAddMonoidHom coe_injective coe_smul

@[simp]
theorem coe_fn_smul_apply [IsScalarTower R ℝ≥0 ℝ≥0] (c : R) (μ : FiniteMeasure Ω) (s : Set Ω) : (c • μ) s = c • μ s :=
  by simp only [coe_fn_smul, Pi.smul_apply]

variable [TopologicalSpace Ω]

/-- The pairing of a finite (Borel) measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure.
This is `finite_measure.test_against_nn`. -/
def testAgainstNn (μ : FiniteMeasure Ω) (f : Ω →ᵇ ℝ≥0) : ℝ≥0 :=
  (∫⁻ ω, f ω ∂(μ : Measure Ω)).toNnreal

theorem _root_.bounded_continuous_function.nnreal.to_ennreal_comp_measurable {Ω : Type _} [TopologicalSpace Ω]
    [MeasurableSpace Ω] [OpensMeasurableSpace Ω] (f : Ω →ᵇ ℝ≥0) : Measurable fun ω => (f ω : ℝ≥0∞) :=
  measurableCoeNnrealEnnreal.comp f.Continuous.Measurable

theorem _root_.measure_theory.lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω →ᵇ ℝ≥0) : (∫⁻ ω, f ω ∂μ) < ∞ := by
  apply IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  use nndist f 0
  intro x
  have key := BoundedContinuousFunction.Nnreal.upper_bound f x
  rw [Ennreal.coe_le_coe]
  have eq : nndist f 0 = ⟨dist f 0, dist_nonneg⟩ := by
    ext
    simp only [Real.coe_to_nnreal', max_eq_left_iff, Subtype.coe_mk, coe_nndist]
  rwa [Eq] at key

@[simp]
theorem test_against_nn_coe_eq {μ : FiniteMeasure Ω} {f : Ω →ᵇ ℝ≥0} :
    (μ.testAgainstNn f : ℝ≥0∞) = ∫⁻ ω, f ω ∂(μ : Measure Ω) :=
  Ennreal.coe_to_nnreal (lintegral_lt_top_of_bounded_continuous_to_nnreal _ f).Ne

theorem test_against_nn_const (μ : FiniteMeasure Ω) (c : ℝ≥0) :
    μ.testAgainstNn (BoundedContinuousFunction.const Ω c) = c * μ.mass := by simp [← Ennreal.coe_eq_coe]

theorem test_against_nn_mono (μ : FiniteMeasure Ω) {f g : Ω →ᵇ ℝ≥0} (f_le_g : (f : Ω → ℝ≥0) ≤ g) :
    μ.testAgainstNn f ≤ μ.testAgainstNn g := by
  simp only [← Ennreal.coe_le_coe, test_against_nn_coe_eq]
  exact lintegral_mono fun ω => Ennreal.coe_mono (f_le_g ω)

@[simp]
theorem test_against_nn_zero (μ : FiniteMeasure Ω) : μ.testAgainstNn 0 = 0 := by
  simpa only [zero_mul] using μ.test_against_nn_const 0

@[simp]
theorem test_against_nn_one (μ : FiniteMeasure Ω) : μ.testAgainstNn 1 = μ.mass := by
  simp only [test_against_nn, BoundedContinuousFunction.coe_one, Pi.one_apply, Ennreal.coe_one, lintegral_one]
  rfl

@[simp]
theorem Zero.test_against_nn_apply (f : Ω →ᵇ ℝ≥0) : (0 : FiniteMeasure Ω).testAgainstNn f = 0 := by
  simp only [test_against_nn, coe_zero, lintegral_zero_measure, Ennreal.zero_to_nnreal]

theorem Zero.test_against_nn : (0 : FiniteMeasure Ω).testAgainstNn = 0 := by
  funext
  simp only [zero.test_against_nn_apply, Pi.zero_apply]

@[simp]
theorem smul_test_against_nn_apply (c : ℝ≥0) (μ : FiniteMeasure Ω) (f : Ω →ᵇ ℝ≥0) :
    (c • μ).testAgainstNn f = c • μ.testAgainstNn f := by
  simp only [test_against_nn, coe_smul, smul_eq_mul, ← Ennreal.smul_to_nnreal, Ennreal.smul_def, lintegral_smul_measure]

variable [OpensMeasurableSpace Ω]

theorem test_against_nn_add (μ : FiniteMeasure Ω) (f₁ f₂ : Ω →ᵇ ℝ≥0) :
    μ.testAgainstNn (f₁ + f₂) = μ.testAgainstNn f₁ + μ.testAgainstNn f₂ := by
  simp only [← Ennreal.coe_eq_coe, BoundedContinuousFunction.coe_add, Ennreal.coe_add, Pi.add_apply,
    test_against_nn_coe_eq]
  exact lintegral_add_left (BoundedContinuousFunction.Nnreal.toEnnrealCompMeasurable _) _

theorem test_against_nn_smul [IsScalarTower R ℝ≥0 ℝ≥0] [PseudoMetricSpace R] [Zero R] [HasBoundedSmul R ℝ≥0]
    (μ : FiniteMeasure Ω) (c : R) (f : Ω →ᵇ ℝ≥0) : μ.testAgainstNn (c • f) = c • μ.testAgainstNn f := by
  simp only [← Ennreal.coe_eq_coe, BoundedContinuousFunction.coe_smul, test_against_nn_coe_eq, Ennreal.coe_smul]
  simp_rw [← smul_one_smul ℝ≥0∞ c (f _ : ℝ≥0∞), ← smul_one_smul ℝ≥0∞ c (lintegral _ _ : ℝ≥0∞), smul_eq_mul]
  exact @lintegral_const_mul _ _ (μ : Measure Ω) (c • 1) _ (BoundedContinuousFunction.Nnreal.toEnnrealCompMeasurable f)

theorem test_against_nn_lipschitz_estimate (μ : FiniteMeasure Ω) (f g : Ω →ᵇ ℝ≥0) :
    μ.testAgainstNn f ≤ μ.testAgainstNn g + nndist f g * μ.mass := by
  simp only [← μ.test_against_nn_const (nndist f g), ← test_against_nn_add, ← Ennreal.coe_le_coe,
    BoundedContinuousFunction.coe_add, const_apply, Ennreal.coe_add, Pi.add_apply, coe_nnreal_ennreal_nndist,
    test_against_nn_coe_eq]
  apply lintegral_mono
  have le_dist : ∀ ω, dist (f ω) (g ω) ≤ nndist f g := BoundedContinuousFunction.dist_coe_le_dist
  intro ω
  have le' : f ω ≤ g ω + nndist f g := by
    apply (Nnreal.le_add_nndist (f ω) (g ω)).trans
    rw [add_le_add_iff_left]
    exact dist_le_coe.mp (le_dist ω)
  have le : (f ω : ℝ≥0∞) ≤ (g ω : ℝ≥0∞) + nndist f g := by
    rw [← Ennreal.coe_add]
    exact Ennreal.coe_mono le'
  rwa [coe_nnreal_ennreal_nndist] at le

theorem testAgainstNnLipschitz (μ : FiniteMeasure Ω) : LipschitzWith μ.mass fun f : Ω →ᵇ ℝ≥0 => μ.testAgainstNn f := by
  rw [lipschitz_with_iff_dist_le_mul]
  intro f₁ f₂
  suffices abs (μ.test_against_nn f₁ - μ.test_against_nn f₂ : ℝ) ≤ μ.mass * dist f₁ f₂ by rwa [Nnreal.dist_eq]
  apply abs_le.mpr
  constructor
  · have key' := μ.test_against_nn_lipschitz_estimate f₂ f₁
    rw [mul_comm] at key'
    suffices ↑(μ.test_against_nn f₂) ≤ ↑(μ.test_against_nn f₁) + ↑μ.mass * dist f₁ f₂ by linarith
    have key := Nnreal.coe_mono key'
    rwa [Nnreal.coe_add, Nnreal.coe_mul, nndist_comm] at key
    
  · have key' := μ.test_against_nn_lipschitz_estimate f₁ f₂
    rw [mul_comm] at key'
    suffices ↑(μ.test_against_nn f₁) ≤ ↑(μ.test_against_nn f₂) + ↑μ.mass * dist f₁ f₂ by linarith
    have key := Nnreal.coe_mono key'
    rwa [Nnreal.coe_add, Nnreal.coe_mul] at key
    

/-- Finite measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `measure_theory.finite_measure.test_against_nn`, i.e., integration. -/
def toWeakDualBcnn (μ : FiniteMeasure Ω) : WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0) where
  toFun f := μ.testAgainstNn f
  map_add' := test_against_nn_add μ
  map_smul' := test_against_nn_smul μ
  cont := μ.testAgainstNnLipschitz.Continuous

@[simp]
theorem coe_to_weak_dual_bcnn (μ : FiniteMeasure Ω) : ⇑μ.toWeakDualBcnn = μ.testAgainstNn :=
  rfl

@[simp]
theorem to_weak_dual_bcnn_apply (μ : FiniteMeasure Ω) (f : Ω →ᵇ ℝ≥0) :
    μ.toWeakDualBcnn f = (∫⁻ x, f x ∂(μ : Measure Ω)).toNnreal :=
  rfl

/-- The topology of weak convergence on `measure_theory.finite_measure Ω` is inherited (induced)
from the weak-* topology on `weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0)` via the function
`measure_theory.finite_measure.to_weak_dual_bcnn`. -/
instance : TopologicalSpace (FiniteMeasure Ω) :=
  TopologicalSpace.induced toWeakDualBcnn inferInstance

theorem to_weak_dual_bcnn_continuous : Continuous (@toWeakDualBcnn Ω _ _ _) :=
  continuous_induced_dom

/- Integration of (nonnegative bounded continuous) test functions against finite Borel measures
depends continuously on the measure. -/
theorem continuous_test_against_nn_eval (f : Ω →ᵇ ℝ≥0) : Continuous fun μ : FiniteMeasure Ω => μ.testAgainstNn f :=
  (by apply (WeakBilin.eval_continuous _ _).comp to_weak_dual_bcnn_continuous :
    Continuous ((fun φ : WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0) => φ f) ∘ to_weak_dual_bcnn))

/-- The total mass of a finite measure depends continuously on the measure. -/
theorem continuous_mass : Continuous fun μ : FiniteMeasure Ω => μ.mass := by
  simp_rw [← test_against_nn_one]
  exact continuous_test_against_nn_eval 1

/-- Convergence of finite measures implies the convergence of their total masses. -/
theorem _root_.filter.tendsto.mass {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure Ω} {μ : FiniteMeasure Ω}
    (h : Tendsto μs F (𝓝 μ)) : Tendsto (fun i => (μs i).mass) F (𝓝 μ.mass) :=
  (continuous_mass.Tendsto μ).comp h

theorem tendsto_iff_weak_star_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure Ω} {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔ Tendsto (fun i => (μs i).toWeakDualBcnn) F (𝓝 μ.toWeakDualBcnn) :=
  Inducing.tendsto_nhds_iff ⟨rfl⟩

theorem tendsto_iff_forall_to_weak_dual_bcnn_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔ ∀ f : Ω →ᵇ ℝ≥0, Tendsto (fun i => (μs i).toWeakDualBcnn f) F (𝓝 (μ.toWeakDualBcnn f)) := by
  rw [tendsto_iff_weak_star_tendsto, tendsto_iff_forall_eval_tendsto_top_dual_pairing]
  rfl

theorem tendsto_iff_forall_test_against_nn_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔ ∀ f : Ω →ᵇ ℝ≥0, Tendsto (fun i => (μs i).testAgainstNn f) F (𝓝 (μ.testAgainstNn f)) := by
  rw [finite_measure.tendsto_iff_forall_to_weak_dual_bcnn_tendsto]
  rfl

/-- If the total masses of finite measures tend to zero, then the measures tend to
zero. This formulation concerns the associated functionals on bounded continuous
nonnegative test functions. See `finite_measure.tendsto_zero_of_tendsto_zero_mass` for
a formulation stating the weak convergence of measures. -/
theorem tendsto_zero_test_against_nn_of_tendsto_zero_mass {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 0)) (f : Ω →ᵇ ℝ≥0) :
    Tendsto (fun i => (μs i).testAgainstNn f) F (𝓝 0) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have obs := fun i => (μs i).test_against_nn_lipschitz_estimate f 0
  simp_rw [test_against_nn_zero, zero_add] at obs
  simp_rw [show ∀ i, dist ((μs i).testAgainstNn f) 0 = (μs i).testAgainstNn f by
      simp only [dist_nndist, Nnreal.nndist_zero_eq_val', eq_self_iff_true, imp_true_iff]]
  refine' squeeze_zero (fun i => Nnreal.coe_nonneg _) obs _
  simp_rw [Nnreal.coe_mul]
  have lim_pair : tendsto (fun i => (⟨nndist f 0, (μs i).mass⟩ : ℝ × ℝ)) F (𝓝 ⟨nndist f 0, 0⟩) := by
    refine' (Prod.tendsto_iff _ _).mpr ⟨tendsto_const_nhds, _⟩
    exact (nnreal.continuous_coe.tendsto 0).comp mass_lim
  have key := tendsto_mul.comp lim_pair
  rwa [mul_zero] at key

/-- If the total masses of finite measures tend to zero, then the measures tend to zero. -/
theorem tendsto_zero_of_tendsto_zero_mass {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    (mass_lim : Tendsto (fun i => (μs i).mass) F (𝓝 0)) : Tendsto μs F (𝓝 0) := by
  rw [tendsto_iff_forall_test_against_nn_tendsto]
  intro f
  convert tendsto_zero_test_against_nn_of_tendsto_zero_mass mass_lim f
  rw [zero.test_against_nn_apply]

/-- A characterization of weak convergence in terms of integrals of bounded continuous
nonnegative functions. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ≥0, Tendsto (fun i => ∫⁻ x, f x ∂(μs i : Measure Ω)) F (𝓝 (∫⁻ x, f x ∂(μ : Measure Ω))) :=
  by
  rw [tendsto_iff_forall_to_weak_dual_bcnn_tendsto]
  simp_rw [to_weak_dual_bcnn_apply _ _, ← test_against_nn_coe_eq, Ennreal.tendsto_coe, Ennreal.to_nnreal_coe]

end FiniteMeasure

-- section
section FiniteMeasureBoundedConvergence

/-! ### Bounded convergence results for finite measures

This section is about bounded convergence theorems for finite measures.
-/


variable {Ω : Type _} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is `measure_theory.lintegral`, i.e., the functions and their integrals are
   `ℝ≥0∞`-valued.
-/
theorem tendsto_lintegral_nn_filter_of_le_const {ι : Type _} {L : Filter ι} [L.IsCountablyGenerated] (μ : Measure Ω)
    [IsFiniteMeasure μ] {fs : ι → Ω →ᵇ ℝ≥0} {c : ℝ≥0} (fs_le_const : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂μ, fs i ω ≤ c) {f : Ω → ℝ≥0}
    (fs_lim : ∀ᵐ ω : Ω ∂μ, Tendsto (fun i => fs i ω) L (𝓝 (f ω))) :
    Tendsto (fun i => ∫⁻ ω, fs i ω ∂μ) L (𝓝 (∫⁻ ω, f ω ∂μ)) := by
  simpa only using
    tendsto_lintegral_filter_of_dominated_convergence (fun _ => c)
      (eventually_of_forall fun i => (ennreal.continuous_coe.comp (fs i).Continuous).Measurable) _
      (@lintegral_const_lt_top _ _ μ _ _ (@Ennreal.coe_ne_top c)).Ne _
  · simpa only [Ennreal.coe_le_coe] using fs_le_const
    
  · simpa only [Ennreal.tendsto_coe] using fs_lim
    

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant
and tend pointwise to a limit, then their integrals (`measure_theory.lintegral`) against the finite
measure tend to the integral of the limit.

A related result with more general assumptions is
`measure_theory.finite_measure.tendsto_lintegral_nn_filter_of_le_const`.
-/
theorem tendsto_lintegral_nn_of_le_const (μ : FiniteMeasure Ω) {fs : ℕ → Ω →ᵇ ℝ≥0} {c : ℝ≥0}
    (fs_le_const : ∀ n ω, fs n ω ≤ c) {f : Ω → ℝ≥0} (fs_lim : ∀ ω, Tendsto (fun n => fs n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n => ∫⁻ ω, fs n ω ∂(μ : Measure Ω)) atTop (𝓝 (∫⁻ ω, f ω ∂(μ : Measure Ω))) :=
  tendsto_lintegral_nn_filter_of_le_const μ (eventually_of_forall fun n => eventually_of_forall (fs_le_const n))
    (eventually_of_forall fs_lim)

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is the pairing against non-negative continuous test functions
   (`measure_theory.finite_measure.test_against_nn`).

A related result using `measure_theory.lintegral` for integration is
`measure_theory.finite_measure.tendsto_lintegral_nn_filter_of_le_const`.
-/
theorem tendsto_test_against_nn_filter_of_le_const {ι : Type _} {L : Filter ι} [L.IsCountablyGenerated]
    {μ : FiniteMeasure Ω} {fs : ι → Ω →ᵇ ℝ≥0} {c : ℝ≥0} (fs_le_const : ∀ᶠ i in L, ∀ᵐ ω : Ω ∂(μ : Measure Ω), fs i ω ≤ c)
    {f : Ω →ᵇ ℝ≥0} (fs_lim : ∀ᵐ ω : Ω ∂(μ : Measure Ω), Tendsto (fun i => fs i ω) L (𝓝 (f ω))) :
    Tendsto (fun i => μ.testAgainstNn (fs i)) L (𝓝 (μ.testAgainstNn f)) := by
  apply (Ennreal.tendsto_to_nnreal (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measure Ω) f).Ne).comp
  exact tendsto_lintegral_nn_filter_of_le_const μ fs_le_const fs_lim

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant and
tend pointwise to a limit, then their integrals (`measure_theory.finite_measure.test_against_nn`)
against the finite measure tend to the integral of the limit.

Related results:
 * `measure_theory.finite_measure.tendsto_test_against_nn_filter_of_le_const`:
   more general assumptions
 * `measure_theory.finite_measure.tendsto_lintegral_nn_of_le_const`:
   using `measure_theory.lintegral` for integration.
-/
theorem tendsto_test_against_nn_of_le_const {μ : FiniteMeasure Ω} {fs : ℕ → Ω →ᵇ ℝ≥0} {c : ℝ≥0}
    (fs_le_const : ∀ n ω, fs n ω ≤ c) {f : Ω →ᵇ ℝ≥0} (fs_lim : ∀ ω, Tendsto (fun n => fs n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n => μ.testAgainstNn (fs n)) atTop (𝓝 (μ.testAgainstNn f)) :=
  tendsto_test_against_nn_filter_of_le_const (eventually_of_forall fun n => eventually_of_forall (fs_le_const n))
    (eventually_of_forall fs_lim)

end FiniteMeasureBoundedConvergence

-- section
section FiniteMeasureConvergenceByBoundedContinuousFunctions

/-! ### Weak convergence of finite measures with bounded continuous real-valued functions

In this section we characterize the weak convergence of finite measures by the usual (defining)
condition that the integrals of all bounded continuous real-valued functions converge.
-/


variable {Ω : Type _} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

theorem integrableOfBoundedContinuousToNnreal (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω →ᵇ ℝ≥0) :
    Integrable ((coe : ℝ≥0 → ℝ) ∘ ⇑f) μ := by
  refine' ⟨(nnreal.continuous_coe.comp f.continuous).Measurable.AeStronglyMeasurable, _⟩
  simp only [has_finite_integral, Nnreal.nnnorm_eq]
  exact lintegral_lt_top_of_bounded_continuous_to_nnreal _ f

theorem integrableOfBoundedContinuousToReal (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω →ᵇ ℝ) : Integrable (⇑f) μ := by
  refine' ⟨f.continuous.measurable.ae_strongly_measurable, _⟩
  have aux : (coe : ℝ≥0 → ℝ) ∘ ⇑f.nnnorm = fun x => ∥f x∥ := by
    ext ω
    simp only [Function.comp_app, BoundedContinuousFunction.nnnorm_coe_fun_eq, coe_nnnorm]
  apply (has_finite_integral_iff_norm ⇑f).mpr
  rw [← of_real_integral_eq_lintegral_of_real]
  · exact Ennreal.of_real_lt_top
    
  · exact aux ▸ integrable_of_bounded_continuous_to_nnreal μ f.nnnorm
    
  · exact eventually_of_forall fun ω => norm_nonneg (f ω)
    

theorem _root_.bounded_continuous_function.integral_eq_integral_nnreal_part_sub (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω →ᵇ ℝ) : (∫ ω, f ω ∂μ) = (∫ ω, f.nnrealPart ω ∂μ) - ∫ ω, (-f).nnrealPart ω ∂μ := by
  simp only [f.self_eq_nnreal_part_sub_nnreal_part_neg, Pi.sub_apply, integral_sub,
    integrable_of_bounded_continuous_to_nnreal]

theorem lintegral_lt_top_of_bounded_continuous_to_real {Ω : Type _} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω →ᵇ ℝ) : (∫⁻ ω, Ennreal.ofReal (f ω) ∂μ) < ∞ :=
  lintegral_lt_top_of_bounded_continuous_to_nnreal _ f.nnrealPart

theorem tendsto_of_forall_integral_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure Ω} {μ : FiniteMeasure Ω}
    (h : ∀ f : Ω →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂(μs i : Measure Ω)) F (𝓝 (∫ x, f x ∂(μ : Measure Ω)))) :
    Tendsto μs F (𝓝 μ) := by
  apply (@tendsto_iff_forall_lintegral_tendsto Ω _ _ _ γ F μs μ).mpr
  intro f
  have key :=
    @Ennreal.tendsto_to_real_iff _ F _
      (fun i => (lintegral_lt_top_of_bounded_continuous_to_nnreal (μs i : Measure Ω) f).Ne) _
      (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measure Ω) f).Ne
  simp only [Ennreal.of_real_coe_nnreal] at key
  apply key.mp
  have lip : LipschitzWith 1 (coe : ℝ≥0 → ℝ) := isometry_subtype_coe.lipschitz
  set f₀ := BoundedContinuousFunction.comp _ lip f with def_f₀
  have f₀_eq : ⇑f₀ = (coe : ℝ≥0 → ℝ) ∘ ⇑f := by rfl
  have f₀_nn : 0 ≤ ⇑f₀ := fun _ => by simp only [f₀_eq, Pi.zero_apply, Nnreal.zero_le_coe]
  have f₀_ae_nn : 0 ≤ᵐ[(μ : Measure Ω)] ⇑f₀ := eventually_of_forall f₀_nn
  have f₀_ae_nns : ∀ i, 0 ≤ᵐ[(μs i : Measure Ω)] ⇑f₀ := fun i => eventually_of_forall f₀_nn
  have aux := integral_eq_lintegral_of_nonneg_ae f₀_ae_nn f₀.continuous.measurable.ae_strongly_measurable
  have auxs := fun i => integral_eq_lintegral_of_nonneg_ae (f₀_ae_nns i) f₀.continuous.measurable.ae_strongly_measurable
  simp only [f₀_eq, Ennreal.of_real_coe_nnreal] at aux auxs
  simpa only [← aux, ← auxs] using h f₀

theorem _root_.bounded_continuous_function.nnreal.to_real_lintegral_eq_integral (f : Ω →ᵇ ℝ≥0) (μ : Measure Ω) :
    (∫⁻ x, (f x : ℝ≥0∞) ∂μ).toReal = ∫ x, f x ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae _ (nnreal.continuous_coe.comp f.continuous).Measurable.AeStronglyMeasurable]
  · simp only [Ennreal.of_real_coe_nnreal]
    
  · apply eventually_of_forall
    simp only [Pi.zero_apply, Nnreal.zero_le_coe, imp_true_iff]
    

/-- A characterization of weak convergence in terms of integrals of bounded continuous
real-valued functions. -/
theorem tendsto_iff_forall_integral_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure Ω}
    {μ : FiniteMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ, Tendsto (fun i => ∫ x, f x ∂(μs i : Measure Ω)) F (𝓝 (∫ x, f x ∂(μ : Measure Ω))) :=
  by
  refine' ⟨_, tendsto_of_forall_integral_tendsto⟩
  rw [tendsto_iff_forall_lintegral_tendsto]
  intro h f
  simp_rw [BoundedContinuousFunction.integral_eq_integral_nnreal_part_sub]
  set f_pos := f.nnreal_part with def_f_pos
  set f_neg := (-f).nnrealPart with def_f_neg
  have tends_pos :=
    (Ennreal.tendsto_to_real (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measure Ω) f_pos).Ne).comp (h f_pos)
  have tends_neg :=
    (Ennreal.tendsto_to_real (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : Measure Ω) f_neg).Ne).comp (h f_neg)
  have aux :
    ∀ g : Ω →ᵇ ℝ≥0,
      (Ennreal.toReal ∘ fun i : γ => ∫⁻ x : Ω, ↑(g x) ∂(μs i : Measure Ω)) = fun i : γ =>
        (∫⁻ x : Ω, ↑(g x) ∂(μs i : Measure Ω)).toReal :=
    fun _ => rfl
  simp_rw [aux, BoundedContinuousFunction.Nnreal.to_real_lintegral_eq_integral] at tends_pos tends_neg
  exact tendsto.sub tends_pos tends_neg

end FiniteMeasureConvergenceByBoundedContinuousFunctions

-- section
end FiniteMeasure

-- namespace
end MeasureTheory

-- namespace
