import Mathbin.MeasureTheory.Measure.MeasureSpace
import Mathbin.MeasureTheory.Integral.Bochner
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Topology.Algebra.Module.WeakDual

/-!
# Weak convergence of (finite) measures

This file will define the topology of weak convergence of finite measures and probability measures
on topological spaces. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f`, the integration of `f` against the
measure is continuous.

TODOs:
* Define the topologies (the current version only defines the types) via
  `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)`.
* Prove that an equivalent definition of the topologies is obtained requiring continuity of
  integration of bounded continuous `ℝ`-valued functions instead.
* Include the portmanteau theorem on characterizations of weak convergence of (Borel) probability
  measures.

## Main definitions

The main definitions are the
 * types `finite_measure α` and `probability_measure α`;
 * `to_weak_dual_bounded_continuous_nnreal : finite_measure α → (weak_dual ℝ≥0 (α →ᵇ ℝ≥0))`
   allowing to interpret a finite measure as a continuous linear functional on the space of
   bounded continuous nonnegative functions on `α`. This will be used for the definition of the
   topology of weak convergence.

TODO:
* Define the topologies on the above types.

## Main results

 * Finite measures `μ` on `α` give rise to continuous linear functionals on the space of
   bounded continuous nonnegative functions on `α` via integration:
   `to_weak_dual_of_bounded_continuous_nnreal : finite_measure α → (weak_dual ℝ≥0 (α →ᵇ ℝ≥0))`.

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

open_locale TopologicalSpace Ennreal Nnreal BoundedContinuousFunction

namespace MeasureTheory

variable {α : Type _} [MeasurableSpace α]

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
def finite_measure (α : Type _) [MeasurableSpace α] : Type _ :=
  { μ : Measureₓ α // is_finite_measure μ }

namespace FiniteMeasure

/-- A finite measure can be interpreted as a measure. -/
instance : Coe (finite_measure α) (MeasureTheory.Measure α) :=
  coeSubtype

instance is_finite_measure (μ : finite_measure α) : is_finite_measure (μ : Measureₓ α) :=
  μ.prop

instance : CoeFun (finite_measure α) fun _ => Set α → ℝ≥0 :=
  ⟨fun μ s => (μ s).toNnreal⟩

theorem coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : finite_measure α) :
    (ν : Set α → ℝ≥0 ) = fun s => ((ν : Measureₓ α) s).toNnreal :=
  rfl

@[simp]
theorem ennreal_coe_fn_eq_coe_fn_to_measure (ν : finite_measure α) (s : Set α) : (ν s : ℝ≥0∞) = (ν : Measureₓ α) s :=
  Ennreal.coe_to_nnreal (measure_lt_top (↑ν) s).Ne

@[simp]
theorem val_eq_to_measure (ν : finite_measure α) : ν.val = (ν : Measureₓ α) :=
  rfl

theorem coe_injective : Function.Injective (coe : finite_measure α → Measureₓ α) :=
  Subtype.coe_injective

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`(μ : measure α) univ`. -/
def mass (μ : finite_measure α) : ℝ≥0 :=
  μ univ

@[simp]
theorem ennreal_mass {μ : finite_measure α} : (μ.mass : ℝ≥0∞) = (μ : Measureₓ α) univ :=
  ennreal_coe_fn_eq_coe_fn_to_measure μ Set.Univ

instance Zero : Zero (finite_measure α) where
  zero := ⟨0, MeasureTheory.is_finite_measure_zero⟩

instance : Inhabited (finite_measure α) :=
  ⟨0⟩

instance : Add (finite_measure α) where
  add := fun μ ν => ⟨μ + ν, MeasureTheory.is_finite_measure_add⟩

instance : HasScalar ℝ≥0 (finite_measure α) where
  smul := fun c : ℝ≥0 μ => ⟨c • μ, MeasureTheory.is_finite_measure_smul_nnreal⟩

@[simp, norm_cast]
theorem coe_zero : (coe : finite_measure α → Measureₓ α) 0 = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_add (μ ν : finite_measure α) : ↑(μ + ν) = (↑μ + ↑ν : Measureₓ α) :=
  rfl

@[simp, norm_cast]
theorem coe_smul (c : ℝ≥0 ) (μ : finite_measure α) : ↑(c • μ) = (c • ↑μ : Measureₓ α) :=
  rfl

@[simp, norm_cast]
theorem coe_fn_zero : (⇑(0 : finite_measure α) : Set α → ℝ≥0 ) = (0 : Set α → ℝ≥0 ) := by
  funext
  rfl

@[simp, norm_cast]
theorem coe_fn_add (μ ν : finite_measure α) : (⇑(μ + ν) : Set α → ℝ≥0 ) = (⇑μ + ⇑ν : Set α → ℝ≥0 ) := by
  funext
  simp [← Ennreal.coe_eq_coe]

@[simp, norm_cast]
theorem coe_fn_smul (c : ℝ≥0 ) (μ : finite_measure α) : (⇑(c • μ) : Set α → ℝ≥0 ) = c • (⇑μ : Set α → ℝ≥0 ) := by
  funext
  simp [← Ennreal.coe_eq_coe]

instance : AddCommMonoidₓ (finite_measure α) :=
  finite_measure.coe_injective.AddCommMonoid (coe : finite_measure α → Measureₓ α) finite_measure.coe_zero
    finite_measure.coe_add

/-- Coercion is an `add_monoid_hom`. -/
@[simps]
def coe_add_monoid_hom : finite_measure α →+ Measureₓ α where
  toFun := coe
  map_zero' := coe_zero
  map_add' := coe_add

instance {α : Type _} [MeasurableSpace α] : Module ℝ≥0 (finite_measure α) :=
  Function.Injective.module _ coe_add_monoid_hom finite_measure.coe_injective coe_smul

variable [TopologicalSpace α]

/-- The pairing of a finite (Borel) measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure.
This is `finite_measure.test_against_nn`. -/
def test_against_nn (μ : finite_measure α) (f : α →ᵇ ℝ≥0 ) : ℝ≥0 :=
  (∫⁻ x, f x ∂(μ : Measureₓ α)).toNnreal

theorem _root_.bounded_continuous_function.nnreal.to_ennreal_comp_measurable {α : Type _} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] (f : α →ᵇ ℝ≥0 ) : Measurable fun x => (f x : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp f.continuous.measurable

theorem lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : finite_measure α) (f : α →ᵇ ℝ≥0 ) :
    (∫⁻ x, f x ∂(μ : Measureₓ α)) < ∞ := by
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
theorem test_against_nn_coe_eq {μ : finite_measure α} {f : α →ᵇ ℝ≥0 } :
    (μ.test_against_nn f : ℝ≥0∞) = ∫⁻ x, f x ∂(μ : Measureₓ α) :=
  Ennreal.coe_to_nnreal (lintegral_lt_top_of_bounded_continuous_to_nnreal μ f).Ne

theorem test_against_nn_const (μ : finite_measure α) (c : ℝ≥0 ) :
    μ.test_against_nn (BoundedContinuousFunction.const α c) = c * μ.mass := by
  simp [← Ennreal.coe_eq_coe]

theorem test_against_nn_mono (μ : finite_measure α) {f g : α →ᵇ ℝ≥0 } (f_le_g : (f : α → ℝ≥0 ) ≤ g) :
    μ.test_against_nn f ≤ μ.test_against_nn g := by
  simp only [← Ennreal.coe_le_coe, test_against_nn_coe_eq]
  apply lintegral_mono
  exact fun x => Ennreal.coe_mono (f_le_g x)

variable [OpensMeasurableSpace α]

theorem test_against_nn_add (μ : finite_measure α) (f₁ f₂ : α →ᵇ ℝ≥0 ) :
    μ.test_against_nn (f₁ + f₂) = μ.test_against_nn f₁ + μ.test_against_nn f₂ := by
  simp only [← Ennreal.coe_eq_coe, BoundedContinuousFunction.coe_add, Ennreal.coe_add, Pi.add_apply,
    test_against_nn_coe_eq]
  apply lintegral_add <;> exact BoundedContinuousFunction.Nnreal.to_ennreal_comp_measurable _

theorem test_against_nn_smul (μ : finite_measure α) (c : ℝ≥0 ) (f : α →ᵇ ℝ≥0 ) :
    μ.test_against_nn (c • f) = c * μ.test_against_nn f := by
  simp only [← Ennreal.coe_eq_coe, Algebra.id.smul_eq_mul, BoundedContinuousFunction.coe_smul, test_against_nn_coe_eq,
    Ennreal.coe_mul]
  exact @lintegral_const_mul _ _ (μ : Measureₓ α) c _ (BoundedContinuousFunction.Nnreal.to_ennreal_comp_measurable f)

theorem test_against_nn_lipschitz_estimate (μ : finite_measure α) (f g : α →ᵇ ℝ≥0 ) :
    μ.test_against_nn f ≤ μ.test_against_nn g + nndist f g * μ.mass := by
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

theorem test_against_nn_lipschitz (μ : finite_measure α) :
    LipschitzWith μ.mass fun f : α →ᵇ ℝ≥0 => μ.test_against_nn f := by
  rw [lipschitz_with_iff_dist_le_mul]
  intro f₁ f₂
  suffices abs (μ.test_against_nn f₁ - μ.test_against_nn f₂ : ℝ) ≤ μ.mass * dist f₁ f₂ by
    rwa [Nnreal.dist_eq]
  apply abs_le.mpr
  constructor
  · have key' := μ.test_against_nn_lipschitz_estimate f₂ f₁
    rw [mul_comm] at key'
    suffices ↑μ.test_against_nn f₂ ≤ ↑μ.test_against_nn f₁ + ↑μ.mass * dist f₁ f₂ by
      linarith
    have key := Nnreal.coe_mono key'
    rwa [Nnreal.coe_add, Nnreal.coe_mul, nndist_comm] at key
    
  · have key' := μ.test_against_nn_lipschitz_estimate f₁ f₂
    rw [mul_comm] at key'
    suffices ↑μ.test_against_nn f₁ ≤ ↑μ.test_against_nn f₂ + ↑μ.mass * dist f₁ f₂ by
      linarith
    have key := Nnreal.coe_mono key'
    rwa [Nnreal.coe_add, Nnreal.coe_mul] at key
    

/-- Finite measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `finite_measure.test_against_nn`, i.e., integration. -/
def to_weak_dual_bounded_continuous_nnreal (μ : finite_measure α) : WeakDual ℝ≥0 (α →ᵇ ℝ≥0 ) where
  toFun := fun f => μ.test_against_nn f
  map_add' := test_against_nn_add μ
  map_smul' := test_against_nn_smul μ
  cont := μ.test_against_nn_lipschitz.continuous

end FiniteMeasure

/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def probability_measure (α : Type _) [MeasurableSpace α] : Type _ :=
  { μ : Measureₓ α // is_probability_measure μ }

namespace ProbabilityMeasure

instance [Inhabited α] : Inhabited (probability_measure α) :=
  ⟨⟨measure.dirac default, measure.dirac.is_probability_measure⟩⟩

/-- A probability measure can be interpreted as a measure. -/
instance : Coe (probability_measure α) (MeasureTheory.Measure α) :=
  coeSubtype

instance : CoeFun (probability_measure α) fun _ => Set α → ℝ≥0 :=
  ⟨fun μ s => (μ s).toNnreal⟩

instance (μ : probability_measure α) : is_probability_measure (μ : Measureₓ α) :=
  μ.prop

theorem coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : probability_measure α) :
    (ν : Set α → ℝ≥0 ) = fun s => ((ν : Measureₓ α) s).toNnreal :=
  rfl

@[simp]
theorem val_eq_to_measure (ν : probability_measure α) : ν.val = (ν : Measureₓ α) :=
  rfl

theorem coe_injective : Function.Injective (coe : probability_measure α → Measureₓ α) :=
  Subtype.coe_injective

@[simp]
theorem coe_fn_univ (ν : probability_measure α) : ν univ = 1 :=
  congr_argₓ Ennreal.toNnreal ν.prop.measure_univ

/-- A probability measure can be interpreted as a finite measure. -/
def to_finite_measure (μ : probability_measure α) : finite_measure α :=
  ⟨μ, inferInstance⟩

@[simp]
theorem coe_comp_to_finite_measure_eq_coe (ν : probability_measure α) :
    (ν.to_finite_measure : Measureₓ α) = (ν : Measureₓ α) :=
  rfl

@[simp]
theorem coe_fn_comp_to_finite_measure_eq_coe_fn (ν : probability_measure α) :
    (ν.to_finite_measure : Set α → ℝ≥0 ) = (ν : Set α → ℝ≥0 ) :=
  rfl

@[simp]
theorem ennreal_coe_fn_eq_coe_fn_to_measure (ν : probability_measure α) (s : Set α) :
    (ν s : ℝ≥0∞) = (ν : Measureₓ α) s := by
  rw [← coe_fn_comp_to_finite_measure_eq_coe_fn, finite_measure.ennreal_coe_fn_eq_coe_fn_to_measure]
  rfl

@[simp]
theorem mass_to_finite_measure (μ : probability_measure α) : μ.to_finite_measure.mass = 1 :=
  μ.coe_fn_univ

variable [TopologicalSpace α]

/-- The pairing of a (Borel) probability measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure. This
is `probability_measure.test_against_nn`. -/
def test_against_nn (μ : probability_measure α) (f : α →ᵇ ℝ≥0 ) : ℝ≥0 :=
  (lintegral (μ : Measureₓ α) ((coe : ℝ≥0 → ℝ≥0∞) ∘ f)).toNnreal

theorem lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : probability_measure α) (f : α →ᵇ ℝ≥0 ) :
    (∫⁻ x, f x ∂(μ : Measureₓ α)) < ∞ :=
  μ.to_finite_measure.lintegral_lt_top_of_bounded_continuous_to_nnreal f

@[simp]
theorem test_against_nn_coe_eq {μ : probability_measure α} {f : α →ᵇ ℝ≥0 } :
    (μ.test_against_nn f : ℝ≥0∞) = ∫⁻ x, f x ∂(μ : Measureₓ α) :=
  Ennreal.coe_to_nnreal (lintegral_lt_top_of_bounded_continuous_to_nnreal μ f).Ne

@[simp]
theorem to_finite_measure_test_against_nn_eq_test_against_nn {μ : probability_measure α} {f : α →ᵇ Nnreal} :
    μ.to_finite_measure.test_against_nn f = μ.test_against_nn f :=
  rfl

theorem test_against_nn_const (μ : probability_measure α) (c : ℝ≥0 ) :
    μ.test_against_nn (BoundedContinuousFunction.const α c) = c := by
  simp [← Ennreal.coe_eq_coe, (MeasureTheory.IsProbabilityMeasure μ).measure_univ]

theorem test_against_nn_mono (μ : probability_measure α) {f g : α →ᵇ ℝ≥0 } (f_le_g : (f : α → ℝ≥0 ) ≤ g) :
    μ.test_against_nn f ≤ μ.test_against_nn g := by
  simpa using μ.to_finite_measure.test_against_nn_mono f_le_g

variable [OpensMeasurableSpace α]

theorem test_against_nn_lipschitz (μ : probability_measure α) :
    LipschitzWith 1 fun f : α →ᵇ ℝ≥0 => μ.test_against_nn f := by
  have key := μ.to_finite_measure.test_against_nn_lipschitz
  rwa [μ.mass_to_finite_measure] at key

/-- Probability measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `probability_measure.test_against_nn`, i.e., integration. -/
def to_weak_dual_bounded_continuous_nnreal (μ : probability_measure α) : WeakDual ℝ≥0 (α →ᵇ ℝ≥0 ) where
  toFun := fun f => μ.test_against_nn f
  map_add' := μ.to_finite_measure.test_against_nn_add
  map_smul' := μ.to_finite_measure.test_against_nn_smul
  cont := μ.test_against_nn_lipschitz.continuous

end ProbabilityMeasure

end MeasureTheory

