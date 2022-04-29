/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathbin.MeasureTheory.Measure.MeasureSpace
import Mathbin.MeasureTheory.Integral.Bochner
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Topology.Algebra.Module.WeakDual

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
* Portmanteau theorem.

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
  apply lintegral_add <;> exact BoundedContinuousFunction.Nnreal.to_ennreal_comp_measurable _

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
    apply (eval_continuous _ _).comp to_weak_dual_bcnn_continuous :
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
  congr_argₓ Ennreal.toNnreal ν.Prop.measure_univ

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
          convert congr_argₓ coe h) }

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

end MeasureTheory

