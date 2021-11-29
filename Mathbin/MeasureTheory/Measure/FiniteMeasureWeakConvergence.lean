import Mathbin.MeasureTheory.Measure.MeasureSpace

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

The main definitions are the types `finite_measure α` and `probability_measure α`.

TODO:
* Define the topologies on the above types.

## Main results

None yet.

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


noncomputable theory

open MeasureTheory

open Set

open Filter

open_locale TopologicalSpace Ennreal Nnreal

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

instance : CoeFun (finite_measure α) fun _ => Set α →  ℝ≥0  :=
  ⟨fun μ s => (μ s).toNnreal⟩

theorem coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : finite_measure α) :
  (ν : Set α →  ℝ≥0 ) = fun s => ((ν : Measureₓ α) s).toNnreal :=
  rfl

@[simp]
theorem ennreal_coe_fn_eq_coe_fn_to_measure (ν : finite_measure α) (s : Set α) : (ν s : ℝ≥0∞) = (ν : Measureₓ α) s :=
  Ennreal.coe_to_nnreal (measure_lt_top («expr↑ » ν) s).Ne

@[simp]
theorem val_eq_to_measure (ν : finite_measure α) : ν.val = (ν : Measureₓ α) :=
  rfl

theorem coe_injective : Function.Injective (coeₓ : finite_measure α → Measureₓ α) :=
  Subtype.coe_injective

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`(μ : measure α) univ`. -/
def mass (μ : finite_measure α) :  ℝ≥0  :=
  μ univ

@[simp]
theorem ennreal_mass {μ : finite_measure α} : (μ.mass : ℝ≥0∞) = (μ : Measureₓ α) univ :=
  ennreal_coe_fn_eq_coe_fn_to_measure μ Set.Univ

instance HasZero : HasZero (finite_measure α) :=
  { zero := ⟨0, MeasureTheory.is_finite_measure_zero⟩ }

instance : Inhabited (finite_measure α) :=
  ⟨0⟩

instance : Add (finite_measure α) :=
  { add := fun μ ν => ⟨μ+ν, MeasureTheory.is_finite_measure_add⟩ }

instance : HasScalar ℝ≥0  (finite_measure α) :=
  { smul := fun c :  ℝ≥0  μ => ⟨c • μ, MeasureTheory.is_finite_measure_smul_nnreal⟩ }

@[simp, normCast]
theorem coe_zero : (coeₓ : finite_measure α → Measureₓ α) 0 = 0 :=
  rfl

@[simp, normCast]
theorem coe_add (μ ν : finite_measure α) : «expr↑ » (μ+ν) = («expr↑ » μ+«expr↑ » ν : Measureₓ α) :=
  rfl

@[simp, normCast]
theorem coe_smul (c :  ℝ≥0 ) (μ : finite_measure α) : «expr↑ » (c • μ) = (c • «expr↑ » μ : Measureₓ α) :=
  rfl

@[simp, normCast]
theorem coe_fn_zero : («expr⇑ » (0 : finite_measure α) : Set α →  ℝ≥0 ) = (0 : Set α →  ℝ≥0 ) :=
  by 
    funext 
    rfl

@[simp, normCast]
theorem coe_fn_add (μ ν : finite_measure α) :
  («expr⇑ » (μ+ν) : Set α →  ℝ≥0 ) = («expr⇑ » μ+«expr⇑ » ν : Set α →  ℝ≥0 ) :=
  by 
    funext 
    simp [←Ennreal.coe_eq_coe]

@[simp, normCast]
theorem coe_fn_smul (c :  ℝ≥0 ) (μ : finite_measure α) :
  («expr⇑ » (c • μ) : Set α →  ℝ≥0 ) = c • («expr⇑ » μ : Set α →  ℝ≥0 ) :=
  by 
    funext 
    simp [←Ennreal.coe_eq_coe]

instance : AddCommMonoidₓ (finite_measure α) :=
  finite_measure.coe_injective.AddCommMonoid (coeₓ : finite_measure α → Measureₓ α) finite_measure.coe_zero
    finite_measure.coe_add

/-- Coercion is an `add_monoid_hom`. -/
@[simps]
def coe_add_monoid_hom : finite_measure α →+ Measureₓ α :=
  { toFun := coeₓ, map_zero' := coe_zero, map_add' := coe_add }

instance {α : Type _} [MeasurableSpace α] : Module ℝ≥0  (finite_measure α) :=
  Function.Injective.module _ coe_add_monoid_hom finite_measure.coe_injective coe_smul

end FiniteMeasure

/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def probability_measure (α : Type _) [MeasurableSpace α] : Type _ :=
  { μ : Measureₓ α // is_probability_measure μ }

namespace ProbabilityMeasure

instance [Inhabited α] : Inhabited (probability_measure α) :=
  ⟨⟨measure.dirac (default α), measure.dirac.is_probability_measure⟩⟩

/-- A probability measure can be interpreted as a measure. -/
instance : Coe (probability_measure α) (MeasureTheory.Measure α) :=
  coeSubtype

instance : CoeFun (probability_measure α) fun _ => Set α →  ℝ≥0  :=
  ⟨fun μ s => (μ s).toNnreal⟩

instance (μ : probability_measure α) : is_probability_measure (μ : Measureₓ α) :=
  μ.prop

theorem coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : probability_measure α) :
  (ν : Set α →  ℝ≥0 ) = fun s => ((ν : Measureₓ α) s).toNnreal :=
  rfl

@[simp]
theorem val_eq_to_measure (ν : probability_measure α) : ν.val = (ν : Measureₓ α) :=
  rfl

theorem coe_injective : Function.Injective (coeₓ : probability_measure α → Measureₓ α) :=
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
  (ν.to_finite_measure : Set α →  ℝ≥0 ) = (ν : Set α →  ℝ≥0 ) :=
  rfl

@[simp]
theorem ennreal_coe_fn_eq_coe_fn_to_measure (ν : probability_measure α) (s : Set α) :
  (ν s : ℝ≥0∞) = (ν : Measureₓ α) s :=
  by 
    rw [←coe_fn_comp_to_finite_measure_eq_coe_fn, finite_measure.ennreal_coe_fn_eq_coe_fn_to_measure]
    rfl

@[simp]
theorem mass_to_finite_measure (μ : probability_measure α) : μ.to_finite_measure.mass = 1 :=
  μ.coe_fn_univ

end ProbabilityMeasure

end MeasureTheory

