/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace
import Mathbin.MeasureTheory.Integral.SetIntegral
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Topology.Algebra.Module.WeakDual
import Mathbin.Topology.MetricSpace.ThickenedIndicator

/-!
# Weak convergence of (finite) measures

This file defines the topology of weak convergence of finite measures and probability measures
on topological spaces. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f`, the integration of `f` against the
measure is continuous.

TODOs:
* Prove that an equivalent definition of the topologies is obtained requiring continuity of
  integration of bounded continuous `ℝ`-valued functions instead.
* Include the portmanteau theorem on characterizations of weak convergence of (Borel) probability
  measures.

## Main definitions

The main definitions are the
 * types `finite_measure α` and `probability_measure α` with topologies of weak convergence;
 * `to_weak_dual_bcnn : finite_measure α → (weak_dual ℝ≥0 (α →ᵇ ℝ≥0))`
   allowing to interpret a finite measure as a continuous linear functional on the space of
   bounded continuous nonnegative functions on `α`. This is used for the definition of the
   topology of weak convergence.

## Main results

 * Finite measures `μ` on `α` give rise to continuous linear functionals on the space of
   bounded continuous nonnegative functions on `α` via integration:
   `to_weak_dual_bcnn : finite_measure α → (weak_dual ℝ≥0 (α →ᵇ ℝ≥0))`.
 * `tendsto_iff_forall_lintegral_tendsto`: Convergence of finite measures and probability measures
   is characterized by the convergence of integrals of all bounded continuous (nonnegative)
   functions. This essentially shows that the given definition of topology corresponds to the
   common textbook definition of weak convergence of measures.

TODO:
* Portmanteau theorem:
  * `finite_measure.limsup_measure_closed_le_of_tendsto` proves one implication.
    The current formulation assumes `pseudo_emetric_space`. The only reason is to have
    bounded continuous pointwise approximations to the indicator function of a closed set. Clearly
    for example metrizability or pseudo-emetrizability would be sufficient assumptions. The
    typeclass assumptions should be later adjusted in a way that takes into account use cases, but
    the proof will presumably remain essentially the same.
  * Prove the rest of the implications.

## Notations

No new notation is introduced.

## Implementation notes

The topology of weak convergence of finite Borel measures will be defined using a mapping from
`finite_measure α` to `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)`, inheriting the topology from the latter.

The current implementation of `finite_measure α` and `probability_measure α` is directly as
subtypes of `measure α`, and the coercion to a function is the composition `ennreal.to_nnreal`
and the coercion to function of `measure α`. Another alternative would be to use a bijection
with `vector_measure α ℝ≥0` as an intermediate step. The choice of implementation should not have
drastic downstream effects, so it can be changed later if appropriate.

Potential advantages of using the `nnreal`-valued vector measure alternative:
 * The coercion to function would avoid need to compose with `ennreal.to_nnreal`, the
   `nnreal`-valued API could be more directly available.
Potential drawbacks of the vector measure alternative:
 * The coercion to function would lose monotonicity, as non-measurable sets would be defined to
   have measure 0.
 * No integration theory directly. E.g., the topology definition requires `lintegral` w.r.t.
   a coercion to `measure α` in any case.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, finite measure, probability measure

-/


noncomputable section

open MeasureTheory

open Set

open Filter

open BoundedContinuousFunction

open TopologicalSpace Ennreal Nnreal BoundedContinuousFunction

namespace MeasureTheory

variable {α : Type _} [MeasurableSpace α]

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
def FiniteMeasure (α : Type _) [MeasurableSpace α] : Type _ :=
  { μ : Measure α // IsFiniteMeasure μ }

namespace FiniteMeasure

/-- A finite measure can be interpreted as a measure. -/
instance : Coe (FiniteMeasure α) (MeasureTheory.Measure α) :=
  coeSubtype

instance is_finite_measure (μ : FiniteMeasure α) : IsFiniteMeasure (μ : Measure α) :=
  μ.Prop

instance : CoeFun (FiniteMeasure α) fun _ => Set α → ℝ≥0 :=
  ⟨fun μ s => (μ s).toNnreal⟩

theorem coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : FiniteMeasure α) :
    (ν : Set α → ℝ≥0 ) = fun s => ((ν : Measure α) s).toNnreal :=
  rfl

@[simp]
theorem ennreal_coe_fn_eq_coe_fn_to_measure (ν : FiniteMeasure α) (s : Set α) : (ν s : ℝ≥0∞) = (ν : Measure α) s :=
  Ennreal.coe_to_nnreal (measure_lt_top (↑ν) s).Ne

@[simp]
theorem val_eq_to_measure (ν : FiniteMeasure α) : ν.val = (ν : Measure α) :=
  rfl

theorem coe_injective : Function.Injective (coe : FiniteMeasure α → Measure α) :=
  Subtype.coe_injective

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`(μ : measure α) univ`. -/
def mass (μ : FiniteMeasure α) : ℝ≥0 :=
  μ Univ

@[simp]
theorem ennreal_mass {μ : FiniteMeasure α} : (μ.mass : ℝ≥0∞) = (μ : Measure α) Univ :=
  ennreal_coe_fn_eq_coe_fn_to_measure μ Set.Univ

instance hasZero : Zero (FiniteMeasure α) where
  zero := ⟨0, MeasureTheory.is_finite_measure_zero⟩

instance : Inhabited (FiniteMeasure α) :=
  ⟨0⟩

instance : Add (FiniteMeasure α) where
  add := fun μ ν => ⟨μ + ν, MeasureTheory.is_finite_measure_add⟩

variable {R : Type _} [HasScalar R ℝ≥0 ] [HasScalar R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]

instance : HasScalar R (FiniteMeasure α) where
  smul := fun μ => ⟨c • μ, MeasureTheory.is_finite_measure_smul_of_nnreal_tower⟩

@[simp, norm_cast]
theorem coe_zero : (coe : FiniteMeasure α → Measure α) 0 = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_add (μ ν : FiniteMeasure α) : ↑(μ + ν) = (↑μ + ↑ν : Measure α) :=
  rfl

@[simp, norm_cast]
theorem coe_smul (c : R) (μ : FiniteMeasure α) : ↑(c • μ) = (c • ↑μ : Measure α) :=
  rfl

@[simp, norm_cast]
theorem coe_fn_zero : (⇑(0 : FiniteMeasure α) : Set α → ℝ≥0 ) = (0 : Set α → ℝ≥0 ) := by
  funext
  rfl

@[simp, norm_cast]
theorem coe_fn_add (μ ν : FiniteMeasure α) : (⇑(μ + ν) : Set α → ℝ≥0 ) = (⇑μ + ⇑ν : Set α → ℝ≥0 ) := by
  funext
  simp [← Ennreal.coe_eq_coe]

@[simp, norm_cast]
theorem coe_fn_smul [IsScalarTower R ℝ≥0 ℝ≥0 ] (c : R) (μ : FiniteMeasure α) :
    (⇑(c • μ) : Set α → ℝ≥0 ) = c • (⇑μ : Set α → ℝ≥0 ) := by
  funext
  simp [← Ennreal.coe_eq_coe, Ennreal.coe_smul]

instance : AddCommMonoidₓ (FiniteMeasure α) :=
  FiniteMeasure.coe_injective.AddCommMonoid coe coe_zero coe_add fun _ _ => coe_smul _ _

/-- Coercion is an `add_monoid_hom`. -/
@[simps]
def coeAddMonoidHom : FiniteMeasure α →+ Measure α where
  toFun := coe
  map_zero' := coe_zero
  map_add' := coe_add

instance {α : Type _} [MeasurableSpace α] : Module ℝ≥0 (FiniteMeasure α) :=
  Function.Injective.module _ coeAddMonoidHom FiniteMeasure.coe_injective coe_smul

variable [TopologicalSpace α]

/-- The pairing of a finite (Borel) measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure.
This is `finite_measure.test_against_nn`. -/
def testAgainstNn (μ : FiniteMeasure α) (f : α →ᵇ ℝ≥0 ) : ℝ≥0 :=
  (∫⁻ x, f x ∂(μ : Measure α)).toNnreal

theorem _root_.bounded_continuous_function.nnreal.to_ennreal_comp_measurable {α : Type _} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] (f : α →ᵇ ℝ≥0 ) : Measurable fun x => (f x : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp f.Continuous.Measurable

theorem lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : FiniteMeasure α) (f : α →ᵇ ℝ≥0 ) :
    (∫⁻ x, f x ∂(μ : Measure α)) < ∞ := by
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
theorem test_against_nn_coe_eq {μ : FiniteMeasure α} {f : α →ᵇ ℝ≥0 } :
    (μ.testAgainstNn f : ℝ≥0∞) = ∫⁻ x, f x ∂(μ : Measure α) :=
  Ennreal.coe_to_nnreal (lintegral_lt_top_of_bounded_continuous_to_nnreal μ f).Ne

theorem test_against_nn_const (μ : FiniteMeasure α) (c : ℝ≥0 ) :
    μ.testAgainstNn (BoundedContinuousFunction.const α c) = c * μ.mass := by
  simp [← Ennreal.coe_eq_coe]

theorem test_against_nn_mono (μ : FiniteMeasure α) {f g : α →ᵇ ℝ≥0 } (f_le_g : (f : α → ℝ≥0 ) ≤ g) :
    μ.testAgainstNn f ≤ μ.testAgainstNn g := by
  simp only [← Ennreal.coe_le_coe, test_against_nn_coe_eq]
  apply lintegral_mono
  exact fun x => Ennreal.coe_mono (f_le_g x)

variable [OpensMeasurableSpace α]

theorem test_against_nn_add (μ : FiniteMeasure α) (f₁ f₂ : α →ᵇ ℝ≥0 ) :
    μ.testAgainstNn (f₁ + f₂) = μ.testAgainstNn f₁ + μ.testAgainstNn f₂ := by
  simp only [← Ennreal.coe_eq_coe, BoundedContinuousFunction.coe_add, Ennreal.coe_add, Pi.add_apply,
    test_against_nn_coe_eq]
  exact lintegral_add_left (BoundedContinuousFunction.Nnreal.to_ennreal_comp_measurable _) _

theorem test_against_nn_smul [IsScalarTower R ℝ≥0 ℝ≥0 ] [PseudoMetricSpace R] [Zero R] [HasBoundedSmul R ℝ≥0 ]
    (μ : FiniteMeasure α) (c : R) (f : α →ᵇ ℝ≥0 ) : μ.testAgainstNn (c • f) = c • μ.testAgainstNn f := by
  simp only [← Ennreal.coe_eq_coe, BoundedContinuousFunction.coe_smul, test_against_nn_coe_eq, Ennreal.coe_smul]
  simp_rw [← smul_one_smul ℝ≥0∞ c (f _ : ℝ≥0∞), ← smul_one_smul ℝ≥0∞ c (lintegral _ _ : ℝ≥0∞), smul_eq_mul]
  exact
    @lintegral_const_mul _ _ (μ : Measureₓ α) (c • 1) _ (BoundedContinuousFunction.Nnreal.to_ennreal_comp_measurable f)

theorem test_against_nn_lipschitz_estimate (μ : FiniteMeasure α) (f g : α →ᵇ ℝ≥0 ) :
    μ.testAgainstNn f ≤ μ.testAgainstNn g + nndist f g * μ.mass := by
  simp only [← μ.test_against_nn_const (nndist f g), ← test_against_nn_add, ← Ennreal.coe_le_coe,
    BoundedContinuousFunction.coe_add, const_apply, Ennreal.coe_add, Pi.add_apply, coe_nnreal_ennreal_nndist,
    test_against_nn_coe_eq]
  apply lintegral_mono
  have le_dist : ∀ x, dist (f x) (g x) ≤ nndist f g := BoundedContinuousFunction.dist_coe_le_dist
  intro x
  have le' : f x ≤ g x + nndist f g := by
    apply (Nnreal.le_add_nndist (f x) (g x)).trans
    rw [add_le_add_iff_left]
    exact dist_le_coe.mp (le_dist x)
  have le : (f x : ℝ≥0∞) ≤ (g x : ℝ≥0∞) + nndist f g := by
    rw [← Ennreal.coe_add]
    exact Ennreal.coe_mono le'
  rwa [coe_nnreal_ennreal_nndist] at le

theorem test_against_nn_lipschitz (μ : FiniteMeasure α) : LipschitzWith μ.mass fun f : α →ᵇ ℝ≥0 => μ.testAgainstNn f :=
  by
  rw [lipschitz_with_iff_dist_le_mul]
  intro f₁ f₂
  suffices abs (μ.test_against_nn f₁ - μ.test_against_nn f₂ : ℝ) ≤ μ.mass * dist f₁ f₂ by
    rwa [Nnreal.dist_eq]
  apply abs_le.mpr
  constructor
  · have key' := μ.test_against_nn_lipschitz_estimate f₂ f₁
    rw [mul_comm] at key'
    suffices ↑(μ.test_against_nn f₂) ≤ ↑(μ.test_against_nn f₁) + ↑μ.mass * dist f₁ f₂ by
      linarith
    have key := Nnreal.coe_mono key'
    rwa [Nnreal.coe_add, Nnreal.coe_mul, nndist_comm] at key
    
  · have key' := μ.test_against_nn_lipschitz_estimate f₁ f₂
    rw [mul_comm] at key'
    suffices ↑(μ.test_against_nn f₁) ≤ ↑(μ.test_against_nn f₂) + ↑μ.mass * dist f₁ f₂ by
      linarith
    have key := Nnreal.coe_mono key'
    rwa [Nnreal.coe_add, Nnreal.coe_mul] at key
    

/-- Finite measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `finite_measure.test_against_nn`, i.e., integration. -/
def toWeakDualBcnn (μ : FiniteMeasure α) : WeakDual ℝ≥0 (α →ᵇ ℝ≥0 ) where
  toFun := fun f => μ.testAgainstNn f
  map_add' := test_against_nn_add μ
  map_smul' := test_against_nn_smul μ
  cont := μ.test_against_nn_lipschitz.Continuous

@[simp]
theorem coe_to_weak_dual_bcnn (μ : FiniteMeasure α) : ⇑μ.toWeakDualBcnn = μ.testAgainstNn :=
  rfl

@[simp]
theorem to_weak_dual_bcnn_apply (μ : FiniteMeasure α) (f : α →ᵇ ℝ≥0 ) :
    μ.toWeakDualBcnn f = (∫⁻ x, f x ∂(μ : Measure α)).toNnreal :=
  rfl

/-- The topology of weak convergence on `finite_measures α` is inherited (induced) from the weak-*
topology on `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)` via the function `finite_measures.to_weak_dual_bcnn`. -/
instance : TopologicalSpace (FiniteMeasure α) :=
  TopologicalSpace.induced toWeakDualBcnn inferInstance

theorem to_weak_dual_bcnn_continuous : Continuous (@FiniteMeasure.toWeakDualBcnn α _ _ _) :=
  continuous_induced_dom

/- Integration of (nonnegative bounded continuous) test functions against finite Borel measures
depends continuously on the measure. -/
theorem continuous_test_against_nn_eval (f : α →ᵇ ℝ≥0 ) : Continuous fun μ : FiniteMeasure α => μ.testAgainstNn f :=
  (by
    apply (WeakBilin.eval_continuous _ _).comp to_weak_dual_bcnn_continuous :
    Continuous ((fun φ : WeakDual ℝ≥0 (α →ᵇ ℝ≥0 ) => φ f) ∘ to_weak_dual_bcnn))

theorem tendsto_iff_weak_star_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure α} {μ : FiniteMeasure α} :
    Tendsto μs F (𝓝 μ) ↔ Tendsto (fun i => (μs i).toWeakDualBcnn) F (𝓝 μ.toWeakDualBcnn) :=
  Inducing.tendsto_nhds_iff ⟨rfl⟩

theorem tendsto_iff_forall_test_against_nn_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure α}
    {μ : FiniteMeasure α} :
    Tendsto μs F (𝓝 μ) ↔ ∀ f : α →ᵇ ℝ≥0 , Tendsto (fun i => (μs i).toWeakDualBcnn f) F (𝓝 (μ.toWeakDualBcnn f)) := by
  rw [tendsto_iff_weak_star_tendsto, tendsto_iff_forall_eval_tendsto_top_dual_pairing]
  rfl

theorem tendsto_iff_forall_lintegral_tendsto {γ : Type _} {F : Filter γ} {μs : γ → FiniteMeasure α}
    {μ : FiniteMeasure α} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : α →ᵇ ℝ≥0 , Tendsto (fun i => ∫⁻ x, f x ∂(μs i : Measure α)) F (𝓝 (∫⁻ x, f x ∂(μ : Measure α))) :=
  by
  rw [tendsto_iff_forall_test_against_nn_tendsto]
  simp_rw [to_weak_dual_bcnn_apply _ _, ← test_against_nn_coe_eq, Ennreal.tendsto_coe, Ennreal.to_nnreal_coe]

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is `lintegral`, i.e., the functions and their integrals are `ℝ≥0∞`-valued.
-/
theorem tendsto_lintegral_nn_filter_of_le_const {ι : Type _} {L : Filter ι} [L.IsCountablyGenerated]
    (μ : FiniteMeasure α) {fs : ι → α →ᵇ ℝ≥0 } {c : ℝ≥0 }
    (fs_le_const : ∀ᶠ i in L, ∀ᵐ a : α ∂(μ : Measure α), fs i a ≤ c) {f : α → ℝ≥0 }
    (fs_lim : ∀ᵐ a : α ∂(μ : Measure α), Tendsto (fun i => fs i a) L (𝓝 (f a))) :
    Tendsto (fun i => ∫⁻ a, fs i a ∂(μ : Measure α)) L (𝓝 (∫⁻ a, f a ∂(μ : Measure α))) := by
  simpa only using
    tendsto_lintegral_filter_of_dominated_convergence (fun _ => c)
      (eventually_of_forall fun i => (ennreal.continuous_coe.comp (fs i).Continuous).Measurable) _
      (@lintegral_const_lt_top _ _ (μ : Measureₓ α) _ _ (@Ennreal.coe_ne_top c)).Ne _
  · simpa only [Ennreal.coe_le_coe] using fs_le_const
    
  · simpa only [Ennreal.tendsto_coe] using fs_lim
    

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant
and tend pointwise to a limit, then their integrals (`lintegral`) against the finite measure tend
to the integral of the limit.

A related result with more general assumptions is `tendsto_lintegral_nn_filter_of_le_const`.
-/
theorem tendsto_lintegral_nn_of_le_const (μ : FiniteMeasure α) {fs : ℕ → α →ᵇ ℝ≥0 } {c : ℝ≥0 }
    (fs_le_const : ∀ n a, fs n a ≤ c) {f : α → ℝ≥0 } (fs_lim : ∀ a, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, fs n a ∂(μ : Measure α)) atTop (𝓝 (∫⁻ a, f a ∂(μ : Measure α))) :=
  tendsto_lintegral_nn_filter_of_le_const μ (eventually_of_forall fun n => eventually_of_forall (fs_le_const n))
    (eventually_of_forall fs_lim)

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is the pairing against non-negative continuous test functions (`test_against_nn`).

A related result using `lintegral` for integration is `tendsto_lintegral_nn_filter_of_le_const`.
-/
theorem tendsto_test_against_nn_filter_of_le_const {ι : Type _} {L : Filter ι} [L.IsCountablyGenerated]
    {μ : FiniteMeasure α} {fs : ι → α →ᵇ ℝ≥0 } {c : ℝ≥0 }
    (fs_le_const : ∀ᶠ i in L, ∀ᵐ a : α ∂(μ : Measure α), fs i a ≤ c) {f : α →ᵇ ℝ≥0 }
    (fs_lim : ∀ᵐ a : α ∂(μ : Measure α), Tendsto (fun i => fs i a) L (𝓝 (f a))) :
    Tendsto (fun i => μ.testAgainstNn (fs i)) L (𝓝 (μ.testAgainstNn f)) := by
  apply (Ennreal.tendsto_to_nnreal (μ.lintegral_lt_top_of_bounded_continuous_to_nnreal f).Ne).comp
  exact finite_measure.tendsto_lintegral_nn_filter_of_le_const μ fs_le_const fs_lim

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant
and tend pointwise to a limit, then their integrals (`test_against_nn`) against the finite measure
tend to the integral of the limit.

Related results:
 * `tendsto_test_against_nn_filter_of_le_const`: more general assumptions
 * `tendsto_lintegral_nn_of_le_const`: using `lintegral` for integration.
-/
theorem tendsto_test_against_nn_of_le_const {μ : FiniteMeasure α} {fs : ℕ → α →ᵇ ℝ≥0 } {c : ℝ≥0 }
    (fs_le_const : ∀ n a, fs n a ≤ c) {f : α →ᵇ ℝ≥0 } (fs_lim : ∀ a, Tendsto (fun n => fs n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => μ.testAgainstNn (fs n)) atTop (𝓝 (μ.testAgainstNn f)) :=
  tendsto_test_against_nn_filter_of_le_const (eventually_of_forall fun n => eventually_of_forall (fs_le_const n))
    (eventually_of_forall fs_lim)

end FiniteMeasure

/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def ProbabilityMeasure (α : Type _) [MeasurableSpace α] : Type _ :=
  { μ : Measure α // IsProbabilityMeasure μ }

namespace ProbabilityMeasure

instance [Inhabited α] : Inhabited (ProbabilityMeasure α) :=
  ⟨⟨Measure.dirac default, Measure.dirac.is_probability_measure⟩⟩

/-- A probability measure can be interpreted as a measure. -/
instance : Coe (ProbabilityMeasure α) (MeasureTheory.Measure α) :=
  coeSubtype

instance : CoeFun (ProbabilityMeasure α) fun _ => Set α → ℝ≥0 :=
  ⟨fun μ s => (μ s).toNnreal⟩

instance (μ : ProbabilityMeasure α) : IsProbabilityMeasure (μ : Measure α) :=
  μ.Prop

theorem coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : ProbabilityMeasure α) :
    (ν : Set α → ℝ≥0 ) = fun s => ((ν : Measure α) s).toNnreal :=
  rfl

@[simp]
theorem val_eq_to_measure (ν : ProbabilityMeasure α) : ν.val = (ν : Measure α) :=
  rfl

theorem coe_injective : Function.Injective (coe : ProbabilityMeasure α → Measure α) :=
  Subtype.coe_injective

@[simp]
theorem coe_fn_univ (ν : ProbabilityMeasure α) : ν Univ = 1 :=
  congr_arg Ennreal.toNnreal ν.Prop.measure_univ

/-- A probability measure can be interpreted as a finite measure. -/
def toFiniteMeasure (μ : ProbabilityMeasure α) : FiniteMeasure α :=
  ⟨μ, inferInstance⟩

@[simp]
theorem coe_comp_to_finite_measure_eq_coe (ν : ProbabilityMeasure α) :
    (ν.toFiniteMeasure : Measure α) = (ν : Measure α) :=
  rfl

@[simp]
theorem coe_fn_comp_to_finite_measure_eq_coe_fn (ν : ProbabilityMeasure α) :
    (ν.toFiniteMeasure : Set α → ℝ≥0 ) = (ν : Set α → ℝ≥0 ) :=
  rfl

@[simp]
theorem ennreal_coe_fn_eq_coe_fn_to_measure (ν : ProbabilityMeasure α) (s : Set α) : (ν s : ℝ≥0∞) = (ν : Measure α) s :=
  by
  rw [← coe_fn_comp_to_finite_measure_eq_coe_fn, finite_measure.ennreal_coe_fn_eq_coe_fn_to_measure]
  rfl

@[simp]
theorem mass_to_finite_measure (μ : ProbabilityMeasure α) : μ.toFiniteMeasure.mass = 1 :=
  μ.coe_fn_univ

variable [TopologicalSpace α]

theorem lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : ProbabilityMeasure α) (f : α →ᵇ ℝ≥0 ) :
    (∫⁻ x, f x ∂(μ : Measure α)) < ∞ :=
  μ.toFiniteMeasure.lintegral_lt_top_of_bounded_continuous_to_nnreal f

variable [OpensMeasurableSpace α]

theorem test_against_nn_lipschitz (μ : ProbabilityMeasure α) :
    LipschitzWith 1 fun f : α →ᵇ ℝ≥0 => μ.toFiniteMeasure.testAgainstNn f :=
  μ.mass_to_finite_measure ▸ μ.toFiniteMeasure.test_against_nn_lipschitz

/-- The topology of weak convergence on `probability_measures α`. This is inherited (induced) from
the weak-*  topology on `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)` via the function
`probability_measures.to_weak_dual_bcnn`. -/
instance : TopologicalSpace (ProbabilityMeasure α) :=
  TopologicalSpace.induced toFiniteMeasure inferInstance

theorem to_finite_measure_continuous : Continuous (toFiniteMeasure : ProbabilityMeasure α → FiniteMeasure α) :=
  continuous_induced_dom

/-- Probability measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `finite_measure.test_against_nn`, i.e., integration. -/
def toWeakDualBcnn : ProbabilityMeasure α → WeakDual ℝ≥0 (α →ᵇ ℝ≥0 ) :=
  finite_measure.to_weak_dual_bcnn ∘ to_finite_measure

@[simp]
theorem coe_to_weak_dual_bcnn (μ : ProbabilityMeasure α) : ⇑μ.toWeakDualBcnn = μ.toFiniteMeasure.testAgainstNn :=
  rfl

@[simp]
theorem to_weak_dual_bcnn_apply (μ : ProbabilityMeasure α) (f : α →ᵇ ℝ≥0 ) :
    μ.toWeakDualBcnn f = (∫⁻ x, f x ∂(μ : Measure α)).toNnreal :=
  rfl

theorem to_weak_dual_bcnn_continuous : Continuous fun μ : ProbabilityMeasure α => μ.toWeakDualBcnn :=
  FiniteMeasure.to_weak_dual_bcnn_continuous.comp to_finite_measure_continuous

/- Integration of (nonnegative bounded continuous) test functions against Borel probability
measures depends continuously on the measure. -/
theorem continuous_test_against_nn_eval (f : α →ᵇ ℝ≥0 ) :
    Continuous fun μ : ProbabilityMeasure α => μ.toFiniteMeasure.testAgainstNn f :=
  (FiniteMeasure.continuous_test_against_nn_eval f).comp to_finite_measure_continuous

-- The canonical mapping from probability measures to finite measures is an embedding.
theorem to_finite_measure_embedding (α : Type _) [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] :
    Embedding (toFiniteMeasure : ProbabilityMeasure α → FiniteMeasure α) :=
  { induced := rfl,
    inj := fun μ ν h =>
      Subtype.eq
        (by
          convert congr_arg coe h) }

theorem tendsto_nhds_iff_to_finite_measures_tendsto_nhds {δ : Type _} (F : Filter δ) {μs : δ → ProbabilityMeasure α}
    {μ₀ : ProbabilityMeasure α} : Tendsto μs F (𝓝 μ₀) ↔ Tendsto (to_finite_measure ∘ μs) F (𝓝 μ₀.toFiniteMeasure) :=
  Embedding.tendsto_nhds_iff (ProbabilityMeasure.to_finite_measure_embedding α)

/-- The usual definition of weak convergence of probability measures is given in terms of sequences
of probability measures: it is the requirement that the integrals of all continuous bounded
functions against members of the sequence converge. This version is a characterization using
nonnegative bounded continuous functions. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type _} {F : Filter γ} {μs : γ → ProbabilityMeasure α}
    {μ : ProbabilityMeasure α} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : α →ᵇ ℝ≥0 , Tendsto (fun i => ∫⁻ x, f x ∂(μs i : Measure α)) F (𝓝 (∫⁻ x, f x ∂(μ : Measure α))) :=
  by
  rw [tendsto_nhds_iff_to_finite_measures_tendsto_nhds]
  exact finite_measure.tendsto_iff_forall_lintegral_tendsto

end ProbabilityMeasure

section ConvergenceImpliesLimsupClosedLe

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere.
-/
theorem measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type _} {L : Filter ι} [L.IsCountablyGenerated]
    [TopologicalSpace α] [OpensMeasurableSpace α] (μ : FiniteMeasure α) {c : ℝ≥0 } {E : Set α}
    (E_mble : MeasurableSet E) (fs : ι → α →ᵇ ℝ≥0 ) (fs_bdd : ∀ᶠ i in L, ∀ᵐ a : α ∂(μ : Measure α), fs i a ≤ c)
    (fs_lim :
      ∀ᵐ a : α ∂(μ : Measure α),
        Tendsto (fun i : ι => (coeFn : (α →ᵇ ℝ≥0 ) → α → ℝ≥0 ) (fs i) a) L (𝓝 (indicatorₓ E (fun x => (1 : ℝ≥0 )) a))) :
    Tendsto (fun n => lintegral (μ : Measure α) fun a => fs n a) L (𝓝 ((μ : Measure α) E)) := by
  convert finite_measure.tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim
  have aux : ∀ a, indicator E (fun x => (1 : ℝ≥0∞)) a = ↑(indicator E (fun x => (1 : ℝ≥0 )) a) := fun a => by
    simp only [Ennreal.coe_indicator, Ennreal.coe_one]
  simp_rw [← aux, lintegral_indicator _ E_mble]
  simp only [lintegral_one, measure.restrict_apply, MeasurableSet.univ, univ_inter]

/-- If a sequence of bounded continuous functions tends to the indicator of a measurable set and
the functions are uniformly bounded, then their integrals against a finite measure tend to the
measure of the set.

A similar result with more general assumptions is `measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
theorem measure_of_cont_bdd_of_tendsto_indicator [TopologicalSpace α] [OpensMeasurableSpace α] (μ : FiniteMeasure α)
    {c : ℝ≥0 } {E : Set α} (E_mble : MeasurableSet E) (fs : ℕ → α →ᵇ ℝ≥0 ) (fs_bdd : ∀ n a, fs n a ≤ c)
    (fs_lim :
      Tendsto (fun n : ℕ => (coeFn : (α →ᵇ ℝ≥0 ) → α → ℝ≥0 ) (fs n)) atTop (𝓝 (indicatorₓ E fun x => (1 : ℝ≥0 )))) :
    Tendsto (fun n => lintegral (μ : Measure α) fun a => fs n a) atTop (𝓝 ((μ : Measure α) E)) := by
  have fs_lim' : ∀ a, tendsto (fun n : ℕ => (fs n a : ℝ≥0 )) at_top (𝓝 (indicator E (fun x => (1 : ℝ≥0 )) a)) := by
    rw [tendsto_pi_nhds] at fs_lim
    exact fun a => fs_lim a
  apply
    measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
      (eventually_of_forall fun n => eventually_of_forall (fs_bdd n)) (eventually_of_forall fs_lim')

/-- The integrals of thickenined indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero.
-/
theorem tendsto_lintegral_thickened_indicator_of_is_closed {α : Type _} [MeasurableSpace α] [PseudoEmetricSpace α]
    [OpensMeasurableSpace α] (μ : FiniteMeasure α) {F : Set α} (F_closed : IsClosed F) {δs : ℕ → ℝ}
    (δs_pos : ∀ n, 0 < δs n) (δs_lim : Tendsto δs atTop (𝓝 0)) :
    Tendsto (fun n => lintegral (μ : Measure α) fun a => (thickenedIndicator (δs_pos n) F a : ℝ≥0∞)) atTop
      (𝓝 ((μ : Measure α) F)) :=
  by
  apply
    measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurable_set (fun n => thickenedIndicator (δs_pos n) F)
      fun n a => thickened_indicator_le_one (δs_pos n) F a
  have key := thickened_indicator_tendsto_indicator_closure δs_pos δs_lim F
  rwa [F_closed.closure_eq] at key

/-- One implication of the portmanteau theorem:
Weak convergence of finite measures implies that the limsup of the measures of any closed set is
at most the measure of the closed set under the limit measure.
-/
theorem FiniteMeasure.limsup_measure_closed_le_of_tendsto {α ι : Type _} {L : Filter ι} [MeasurableSpace α]
    [PseudoEmetricSpace α] [OpensMeasurableSpace α] {μ : FiniteMeasure α} {μs : ι → FiniteMeasure α}
    (μs_lim : Tendsto μs L (𝓝 μ)) {F : Set α} (F_closed : IsClosed F) :
    (L.limsup fun i => (μs i : Measure α) F) ≤ (μ : Measure α) F := by
  by_cases' L = ⊥
  · simp only [h, limsup, Filter.map_bot, Limsup_bot, Ennreal.bot_eq_zero, zero_le]
    
  apply Ennreal.le_of_forall_pos_le_add
  intro ε ε_pos μ_F_finite
  set δs := fun n : ℕ => (1 : ℝ) / (n + 1) with def_δs
  have δs_pos : ∀ n, 0 < δs n := fun n => Nat.one_div_pos_of_nat
  have δs_lim : tendsto δs at_top (𝓝 0) := tendsto_one_div_add_at_top_nhds_0_nat
  have key₁ := tendsto_lintegral_thickened_indicator_of_is_closed μ F_closed δs_pos δs_lim
  have room₁ : (μ : Measureₓ α) F < (μ : Measureₓ α) F + ε / 2 := by
    apply
      Ennreal.lt_add_right (measure_lt_top (μ : Measureₓ α) F).Ne
        (ennreal.div_pos_iff.mpr ⟨(ennreal.coe_pos.mpr ε_pos).Ne.symm, Ennreal.two_ne_top⟩).Ne.symm
  rcases eventually_at_top.mp (eventually_lt_of_tendsto_lt room₁ key₁) with ⟨M, hM⟩
  have key₂ := finite_measure.tendsto_iff_forall_lintegral_tendsto.mp μs_lim (thickenedIndicator (δs_pos M) F)
  have room₂ :
    (lintegral (μ : Measureₓ α) fun a => thickenedIndicator (δs_pos M) F a) <
      (lintegral (μ : Measureₓ α) fun a => thickenedIndicator (δs_pos M) F a) + ε / 2 :=
    by
    apply
      Ennreal.lt_add_right (finite_measure.lintegral_lt_top_of_bounded_continuous_to_nnreal μ _).Ne
        (ennreal.div_pos_iff.mpr ⟨(ennreal.coe_pos.mpr ε_pos).Ne.symm, Ennreal.two_ne_top⟩).Ne.symm
  have ev_near := eventually.mono (eventually_lt_of_tendsto_lt room₂ key₂) fun n => le_of_ltₓ
  have aux := fun n =>
    le_transₓ (measure_le_lintegral_thickened_indicator (μs n : Measureₓ α) F_closed.measurable_set (δs_pos M))
  have ev_near' := eventually.mono ev_near aux
  apply (Filter.limsup_le_limsup ev_near').trans
  have : ne_bot L := ⟨h⟩
  rw [limsup_const]
  apply le_transₓ (add_le_add (hM M rfl.le).le (le_reflₓ (ε / 2 : ℝ≥0∞)))
  simp only [add_assocₓ, Ennreal.add_halves, le_reflₓ]

end ConvergenceImpliesLimsupClosedLe

end MeasureTheory

