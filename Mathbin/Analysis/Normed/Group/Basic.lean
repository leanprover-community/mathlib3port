/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
import Mathbin.Algebra.Module.Ulift
import Mathbin.Analysis.Normed.Group.Seminorm
import Mathbin.Order.LiminfLimsup
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.MetricSpace.Algebra
import Mathbin.Topology.MetricSpace.Isometry
import Mathbin.Topology.Sequences

/-!
# Normed (semi)groups

In this file we define 10 classes:

* `has_norm`, `has_nnnorm`: auxiliary classes endowing a type `α` with a function `norm : α → ℝ`
  (notation: `∥x∥`) and `nnnorm : α → ℝ≥0` (notation: `∥x∥₊`), respectively;
* `seminormed_..._group`: A seminormed (additive) (commutative) group is an (additive) (commutative)
  group with a norm and a compatible pseudometric space structure:
  `∀ x y, dist x y = ∥x / y∥` or `∀ x y, dist x y = ∥x - y∥`, depending on the group operation.
* `normed_..._group`: A normed (additive) (commutative) group is an (additive) (commutative) group
  with a norm and a compatible metric space structure.

We also prove basic properties of (semi)normed groups and provide some instances.

## Notes

The current convention `dist x y = ∥x - y∥` means that the distance is invariant under right
addition, but actions in mathlib are usually from the left. This means we might want to change it to
`dist x y = ∥-x + y∥`.

The normed group hierarchy would lend itself well to a mixin design (that is, having
`seminormed_group` and `seminormed_add_group` not extend `group` and `add_group`), but we choose not
to for performance concerns.

## Tags

normed group
-/


variable {𝓕 𝕜 α ι κ E F G : Type _}

open Filter Function Metric

open BigOperators Ennreal Filter Nnreal uniformity Pointwise TopologicalSpace

/-- Auxiliary class, endowing a type `E` with a function `norm : E → ℝ` with notation `∥x∥`. This
class is designed to be extended in more interesting classes specifying the properties of the norm.
-/
@[notation_class]
class HasNorm (E : Type _) where
  norm : E → ℝ
#align has_norm HasNorm

/-- Auxiliary class, endowing a type `α` with a function `nnnorm : α → ℝ≥0` with notation `∥x∥₊`. -/
@[notation_class]
class HasNnnorm (E : Type _) where
  nnnorm : E → ℝ≥0
#align has_nnnorm HasNnnorm

export HasNorm (norm)

export HasNnnorm (nnnorm)

-- mathport name: «expr∥ ∥»
notation "∥" e "∥" => norm e

-- mathport name: «expr∥ ∥₊»
notation "∥" e "∥₊" => nnnorm e

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥`
defines a pseudometric space structure. -/
class SeminormedAddGroup (E : Type _) extends HasNorm E, AddGroup E, PseudoMetricSpace E where
  dist := fun x y => ∥x - y∥
  dist_eq : ∀ x y, dist x y = ∥x - y∥ := by obviously
#align seminormed_add_group SeminormedAddGroup

/-- A seminormed group is a group endowed with a norm for which `dist x y = ∥x / y∥` defines a
pseudometric space structure. -/
@[to_additive]
class SeminormedGroup (E : Type _) extends HasNorm E, Group E, PseudoMetricSpace E where
  dist := fun x y => ∥x / y∥
  dist_eq : ∀ x y, dist x y = ∥x / y∥ := by obviously
#align seminormed_group SeminormedGroup

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines a
metric space structure. -/
class NormedAddGroup (E : Type _) extends HasNorm E, AddGroup E, MetricSpace E where
  dist := fun x y => ∥x - y∥
  dist_eq : ∀ x y, dist x y = ∥x - y∥ := by obviously
#align normed_add_group NormedAddGroup

/-- A normed group is a group endowed with a norm for which `dist x y = ∥x / y∥` defines a metric
space structure. -/
@[to_additive]
class NormedGroup (E : Type _) extends HasNorm E, Group E, MetricSpace E where
  dist := fun x y => ∥x / y∥
  dist_eq : ∀ x y, dist x y = ∥x / y∥ := by obviously
#align normed_group NormedGroup

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥`
defines a pseudometric space structure. -/
class SeminormedAddCommGroup (E : Type _) extends HasNorm E, AddCommGroup E, PseudoMetricSpace E where
  dist := fun x y => ∥x - y∥
  dist_eq : ∀ x y, dist x y = ∥x - y∥ := by obviously
#align seminormed_add_comm_group SeminormedAddCommGroup

/-- A seminormed group is a group endowed with a norm for which `dist x y = ∥x / y∥`
defines a pseudometric space structure. -/
@[to_additive]
class SeminormedCommGroup (E : Type _) extends HasNorm E, CommGroup E, PseudoMetricSpace E where
  dist := fun x y => ∥x / y∥
  dist_eq : ∀ x y, dist x y = ∥x / y∥ := by obviously
#align seminormed_comm_group SeminormedCommGroup

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines a
metric space structure. -/
class NormedAddCommGroup (E : Type _) extends HasNorm E, AddCommGroup E, MetricSpace E where
  dist := fun x y => ∥x - y∥
  dist_eq : ∀ x y, dist x y = ∥x - y∥ := by obviously
#align normed_add_comm_group NormedAddCommGroup

/-- A normed group is a group endowed with a norm for which `dist x y = ∥x / y∥` defines a metric
space structure. -/
@[to_additive]
class NormedCommGroup (E : Type _) extends HasNorm E, CommGroup E, MetricSpace E where
  dist := fun x y => ∥x / y∥
  dist_eq : ∀ x y, dist x y = ∥x / y∥ := by obviously
#align normed_comm_group NormedCommGroup

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedGroup.toSeminormedGroup [NormedGroup E] : SeminormedGroup E :=
  { ‹NormedGroup E› with }
#align normed_group.to_seminormed_group NormedGroup.toSeminormedGroup

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedCommGroup.toSeminormedCommGroup [NormedCommGroup E] : SeminormedCommGroup E :=
  { ‹NormedCommGroup E› with }
#align normed_comm_group.to_seminormed_comm_group NormedCommGroup.toSeminormedCommGroup

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.toSeminormedGroup [SeminormedCommGroup E] : SeminormedGroup E :=
  { ‹SeminormedCommGroup E› with }
#align seminormed_comm_group.to_seminormed_group SeminormedCommGroup.toSeminormedGroup

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedCommGroup.toNormedGroup [NormedCommGroup E] : NormedGroup E :=
  { ‹NormedCommGroup E› with }
#align normed_comm_group.to_normed_group NormedCommGroup.toNormedGroup

-- See note [reducible non-instances]
/-- Construct a `normed_group` from a `seminormed_group` satisfying `∀ x, ∥x∥ = 0 → x = 1`. This
avoids having to go back to the `(pseudo_)metric_space` level when declaring a `normed_group`
instance as a special case of a more general `seminormed_group` instance. -/
@[to_additive
      "Construct a `normed_add_group` from a `seminormed_add_group` satisfying\n`∀ x, ∥x∥ = 0 → x = 0`. This avoids having to go back to the `(pseudo_)metric_space` level when\ndeclaring a `normed_add_group` instance as a special case of a more general `seminormed_add_group`\ninstance.",
  reducible]
def NormedGroup.ofSeparation [SeminormedGroup E] (h : ∀ x : E, ∥x∥ = 0 → x = 1) : NormedGroup E :=
  { ‹SeminormedGroup E› with
    toMetricSpace :=
      { eq_of_dist_eq_zero := fun x y hxy => div_eq_one.1 $ h _ $ by rwa [← ‹SeminormedGroup E›.dist_eq] } }
#align normed_group.of_separation NormedGroup.ofSeparation

-- See note [reducible non-instances]
/-- Construct a `normed_comm_group` from a `seminormed_comm_group` satisfying
`∀ x, ∥x∥ = 0 → x = 1`. This avoids having to go back to the `(pseudo_)metric_space` level when
declaring a `normed_comm_group` instance as a special case of a more general `seminormed_comm_group`
instance. -/
@[to_additive
      "Construct a `normed_add_comm_group` from a `seminormed_add_comm_group` satisfying\n`∀ x, ∥x∥ = 0 → x = 0`. This avoids having to go back to the `(pseudo_)metric_space` level when\ndeclaring a `normed_add_comm_group` instance as a special case of a more general\n`seminormed_add_comm_group` instance.",
  reducible]
def NormedCommGroup.ofSeparation [SeminormedCommGroup E] (h : ∀ x : E, ∥x∥ = 0 → x = 1) : NormedCommGroup E :=
  { ‹SeminormedCommGroup E›, NormedGroup.ofSeparation h with }
#align normed_comm_group.of_separation NormedCommGroup.ofSeparation

/-- Construct a seminormed group from a multiplication-invariant distance. -/
@[to_additive "Construct a seminormed group from a translation-invariant distance."]
def SeminormedGroup.ofMulDist [HasNorm E] [Group E] [PseudoMetricSpace E] (h₁ : ∀ x : E, ∥x∥ = dist x 1)
    (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    SeminormedGroup E where dist_eq x y := by
    rw [h₁]
    apply le_antisymm
    · simpa only [div_eq_mul_inv, ← mul_right_inv y] using h₂ _ _ _
      
    · simpa only [div_mul_cancel', one_mul] using h₂ (x / y) 1 y
      
#align seminormed_group.of_mul_dist SeminormedGroup.ofMulDist

/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a seminormed group from a translation-invariant pseudodistance."]
def SeminormedGroup.ofMulDist' [HasNorm E] [Group E] [PseudoMetricSpace E] (h₁ : ∀ x : E, ∥x∥ = dist x 1)
    (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    SeminormedGroup E where dist_eq x y := by
    rw [h₁]
    apply le_antisymm
    · simpa only [div_mul_cancel', one_mul] using h₂ (x / y) 1 y
      
    · simpa only [div_eq_mul_inv, ← mul_right_inv y] using h₂ _ _ _
      
#align seminormed_group.of_mul_dist' SeminormedGroup.ofMulDist'

/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a seminormed group from a translation-invariant pseudodistance."]
def SeminormedCommGroup.ofMulDist [HasNorm E] [CommGroup E] [PseudoMetricSpace E] (h₁ : ∀ x : E, ∥x∥ = dist x 1)
    (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) : SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with }
#align seminormed_comm_group.of_mul_dist SeminormedCommGroup.ofMulDist

/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a seminormed group from a translation-invariant pseudodistance."]
def SeminormedCommGroup.ofMulDist' [HasNorm E] [CommGroup E] [PseudoMetricSpace E] (h₁ : ∀ x : E, ∥x∥ = dist x 1)
    (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) : SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with }
#align seminormed_comm_group.of_mul_dist' SeminormedCommGroup.ofMulDist'

/-- Construct a normed group from a multiplication-invariant distance. -/
@[to_additive "Construct a normed group from a translation-invariant distance."]
def NormedGroup.ofMulDist [HasNorm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ∥x∥ = dist x 1)
    (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) : NormedGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with }
#align normed_group.of_mul_dist NormedGroup.ofMulDist

/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a normed group from a translation-invariant pseudodistance."]
def NormedGroup.ofMulDist' [HasNorm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ∥x∥ = dist x 1)
    (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) : NormedGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with }
#align normed_group.of_mul_dist' NormedGroup.ofMulDist'

/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a normed group from a translation-invariant pseudodistance."]
def NormedCommGroup.ofMulDist [HasNorm E] [CommGroup E] [MetricSpace E] (h₁ : ∀ x : E, ∥x∥ = dist x 1)
    (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) : NormedCommGroup E :=
  { NormedGroup.ofMulDist h₁ h₂ with }
#align normed_comm_group.of_mul_dist NormedCommGroup.ofMulDist

/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a normed group from a translation-invariant pseudodistance."]
def NormedCommGroup.ofMulDist' [HasNorm E] [CommGroup E] [MetricSpace E] (h₁ : ∀ x : E, ∥x∥ = dist x 1)
    (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) : NormedCommGroup E :=
  { NormedGroup.ofMulDist' h₁ h₂ with }
#align normed_comm_group.of_mul_dist' NormedCommGroup.ofMulDist'

/-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`uniform_space` instance on `E`). -/
@[to_additive
      "Construct a seminormed group from a seminorm, i.e., registering the pseudodistance*\nand the pseudometric space structure from the seminorm properties. Note that in most cases this\ninstance creates bad definitional equalities (e.g., it does not take into account a possibly\nexisting `uniform_space` instance on `E`)."]
def GroupSeminorm.toSeminormedGroup [Group E] (f : GroupSeminorm E) : SeminormedGroup E where
  dist x y := f (x / y)
  norm := f
  dist_eq x y := rfl
  dist_self x := by simp only [div_self', map_one_eq_zero]
  dist_triangle := le_map_div_add_map_div f
  dist_comm := map_div_rev f
#align group_seminorm.to_seminormed_group GroupSeminorm.toSeminormedGroup

/-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`uniform_space` instance on `E`). -/
@[to_additive
      "Construct a seminormed group from a seminorm, i.e., registering the pseudodistance*\nand the pseudometric space structure from the seminorm properties. Note that in most cases this\ninstance creates bad definitional equalities (e.g., it does not take into account a possibly\nexisting `uniform_space` instance on `E`)."]
def GroupSeminorm.toSeminormedCommGroup [CommGroup E] (f : GroupSeminorm E) : SeminormedCommGroup E :=
  { f.toSeminormedGroup with }
#align group_seminorm.to_seminormed_comm_group GroupSeminorm.toSeminormedCommGroup

/-- Construct a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `uniform_space` instance on
`E`). -/
@[to_additive
      "Construct a normed group from a norm, i.e., registering the distance and the metric\nspace structure from the norm properties. Note that in most cases this instance creates bad\ndefinitional equalities (e.g., it does not take into account a possibly existing `uniform_space`\ninstance on `E`)."]
def GroupNorm.toNormedGroup [Group E] (f : GroupNorm E) : NormedGroup E :=
  { f.toGroupSeminorm.toSeminormedGroup with
    eq_of_dist_eq_zero := fun x y h => div_eq_one.1 $ eq_one_of_map_eq_zero f h }
#align group_norm.to_normed_group GroupNorm.toNormedGroup

/-- Construct a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `uniform_space` instance on
`E`). -/
@[to_additive
      "Construct a normed group from a norm, i.e., registering the distance and the metric\nspace structure from the norm properties. Note that in most cases this instance creates bad\ndefinitional equalities (e.g., it does not take into account a possibly existing `uniform_space`\ninstance on `E`)."]
def GroupNorm.toNormedCommGroup [CommGroup E] (f : GroupNorm E) : NormedCommGroup E :=
  { f.toNormedGroup with }
#align group_norm.to_normed_comm_group GroupNorm.toNormedCommGroup

instance : NormedAddCommGroup PUnit where
  norm := Function.const _ 0
  dist_eq _ _ := rfl

@[simp]
theorem PUnit.norm_eq_zero (r : PUnit) : ∥r∥ = 0 :=
  rfl
#align punit.norm_eq_zero PUnit.norm_eq_zero

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E} {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[to_additive]
theorem dist_eq_norm_div (a b : E) : dist a b = ∥a / b∥ :=
  SeminormedGroup.dist_eq _ _
#align dist_eq_norm_div dist_eq_norm_div

@[to_additive]
theorem dist_eq_norm_div' (a b : E) : dist a b = ∥b / a∥ := by rw [dist_comm, dist_eq_norm_div]
#align dist_eq_norm_div' dist_eq_norm_div'

alias dist_eq_norm_sub ← dist_eq_norm

alias dist_eq_norm_sub' ← dist_eq_norm'

@[simp, to_additive]
theorem dist_one_right (a : E) : dist a 1 = ∥a∥ := by rw [dist_eq_norm_div, div_one]
#align dist_one_right dist_one_right

@[simp, to_additive]
theorem dist_one_left : dist (1 : E) = norm :=
  funext $ fun a => by rw [dist_comm, dist_one_right]
#align dist_one_left dist_one_left

@[to_additive]
theorem Isometry.norm_map_of_map_one {f : E → F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) : ∥f x∥ = ∥x∥ := by
  rw [← dist_one_right, ← h₁, hi.dist_eq, dist_one_right]
#align isometry.norm_map_of_map_one Isometry.norm_map_of_map_one

@[to_additive tendsto_norm_cocompact_at_top]
theorem tendsto_norm_cocompact_at_top' [ProperSpace E] : Tendsto norm (cocompact E) atTop := by
  simpa only [dist_one_right] using tendsto_dist_right_cocompact_at_top (1 : E)
#align tendsto_norm_cocompact_at_top' tendsto_norm_cocompact_at_top'

@[to_additive]
theorem norm_div_rev (a b : E) : ∥a / b∥ = ∥b / a∥ := by simpa only [dist_eq_norm_div] using dist_comm a b
#align norm_div_rev norm_div_rev

@[simp, to_additive norm_neg]
theorem norm_inv' (a : E) : ∥a⁻¹∥ = ∥a∥ := by simpa using norm_div_rev 1 a
#align norm_inv' norm_inv'

@[simp, to_additive]
theorem dist_mul_right (a₁ a₂ b : E) : dist (a₁ * b) (a₂ * b) = dist a₁ a₂ := by simp [dist_eq_norm_div]
#align dist_mul_right dist_mul_right

@[simp, to_additive]
theorem dist_mul_self_right (a b : E) : dist b (a * b) = ∥a∥ := by rw [← dist_one_left, ← dist_mul_right 1 a b, one_mul]
#align dist_mul_self_right dist_mul_self_right

@[simp, to_additive]
theorem dist_mul_self_left (a b : E) : dist (a * b) b = ∥a∥ := by rw [dist_comm, dist_mul_self_right]
#align dist_mul_self_left dist_mul_self_left

@[to_additive]
theorem dist_div_right (a₁ a₂ b : E) : dist (a₁ / b) (a₂ / b) = dist a₁ a₂ := by
  simpa only [div_eq_mul_inv] using dist_mul_right _ _ _
#align dist_div_right dist_div_right

@[simp, to_additive]
theorem dist_div_eq_dist_mul_left (a b c : E) : dist (a / b) c = dist a (c * b) := by
  rw [← dist_mul_right _ _ b, div_mul_cancel']
#align dist_div_eq_dist_mul_left dist_div_eq_dist_mul_left

@[simp, to_additive]
theorem dist_div_eq_dist_mul_right (a b c : E) : dist a (b / c) = dist (a * c) b := by
  rw [← dist_mul_right _ _ c, div_mul_cancel']
#align dist_div_eq_dist_mul_right dist_div_eq_dist_mul_right

/-- In a (semi)normed group, inversion `x ↦ x⁻¹` tends to infinity at infinity. TODO: use
`bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
@[to_additive
      "In a (semi)normed group, negation `x ↦ -x` tends to infinity at infinity. TODO: use\n`bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`."]
theorem Filter.tendsto_inv_cobounded : Tendsto (Inv.inv : E → E) (comap norm atTop) (comap norm atTop) := by
  simpa only [norm_inv', tendsto_comap_iff, (· ∘ ·)] using tendsto_comap
#align filter.tendsto_inv_cobounded Filter.tendsto_inv_cobounded

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le "**Triangle inequality** for the norm."]
theorem norm_mul_le' (a b : E) : ∥a * b∥ ≤ ∥a∥ + ∥b∥ := by simpa [dist_eq_norm_div] using dist_triangle a 1 b⁻¹
#align norm_mul_le' norm_mul_le'

@[to_additive]
theorem norm_mul_le_of_le (h₁ : ∥a₁∥ ≤ r₁) (h₂ : ∥a₂∥ ≤ r₂) : ∥a₁ * a₂∥ ≤ r₁ + r₂ :=
  (norm_mul_le' a₁ a₂).trans $ add_le_add h₁ h₂
#align norm_mul_le_of_le norm_mul_le_of_le

@[to_additive norm_add₃_le]
theorem norm_mul₃_le (a b c : E) : ∥a * b * c∥ ≤ ∥a∥ + ∥b∥ + ∥c∥ :=
  norm_mul_le_of_le (norm_mul_le' _ _) le_rfl
#align norm_mul₃_le norm_mul₃_le

@[simp, to_additive norm_nonneg]
theorem norm_nonneg' (a : E) : 0 ≤ ∥a∥ := by
  rw [← dist_one_right]
  exact dist_nonneg
#align norm_nonneg' norm_nonneg'

section

open Tactic Tactic.Positivity

/-- Extension for the `positivity` tactic: norms are nonnegative. -/
@[positivity]
unsafe def _root_.tactic.positivity_norm : expr → tactic strictness
  | q(∥$(a)∥) => nonnegative <$> mk_app `` norm_nonneg [a] <|> nonnegative <$> mk_app `` norm_nonneg' [a]
  | _ => failed
#align _root_.tactic.positivity_norm _root_.tactic.positivity_norm

end

@[simp, to_additive norm_zero]
theorem norm_one' : ∥(1 : E)∥ = 0 := by rw [← dist_one_right, dist_self]
#align norm_one' norm_one'

@[to_additive]
theorem ne_one_of_norm_ne_zero : ∥a∥ ≠ 0 → a ≠ 1 :=
  mt $ by
    rintro rfl
    exact norm_one'
#align ne_one_of_norm_ne_zero ne_one_of_norm_ne_zero

@[nontriviality, to_additive norm_of_subsingleton]
theorem norm_of_subsingleton' [Subsingleton E] (a : E) : ∥a∥ = 0 := by rw [Subsingleton.elim a 1, norm_one']
#align norm_of_subsingleton' norm_of_subsingleton'

attribute [nontriviality] norm_of_subsingleton

@[to_additive zero_lt_one_add_norm_sq]
theorem zero_lt_one_add_norm_sq' (x : E) : 0 < 1 + ∥x∥ ^ 2 := by positivity
#align zero_lt_one_add_norm_sq' zero_lt_one_add_norm_sq'

@[to_additive]
theorem norm_div_le (a b : E) : ∥a / b∥ ≤ ∥a∥ + ∥b∥ := by simpa [dist_eq_norm_div] using dist_triangle a 1 b
#align norm_div_le norm_div_le

@[to_additive]
theorem norm_div_le_of_le {r₁ r₂ : ℝ} (H₁ : ∥a₁∥ ≤ r₁) (H₂ : ∥a₂∥ ≤ r₂) : ∥a₁ / a₂∥ ≤ r₁ + r₂ :=
  (norm_div_le a₁ a₂).trans $ add_le_add H₁ H₂
#align norm_div_le_of_le norm_div_le_of_le

@[to_additive]
theorem dist_le_norm_mul_norm (a b : E) : dist a b ≤ ∥a∥ + ∥b∥ := by
  rw [dist_eq_norm_div]
  apply norm_div_le
#align dist_le_norm_mul_norm dist_le_norm_mul_norm

@[to_additive abs_norm_sub_norm_le]
theorem abs_norm_sub_norm_le' (a b : E) : |∥a∥ - ∥b∥| ≤ ∥a / b∥ := by
  simpa [dist_eq_norm_div] using abs_dist_sub_le a b 1
#align abs_norm_sub_norm_le' abs_norm_sub_norm_le'

@[to_additive norm_sub_norm_le]
theorem norm_sub_norm_le' (a b : E) : ∥a∥ - ∥b∥ ≤ ∥a / b∥ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le' a b)
#align norm_sub_norm_le' norm_sub_norm_le'

@[to_additive dist_norm_norm_le]
theorem dist_norm_norm_le' (a b : E) : dist ∥a∥ ∥b∥ ≤ ∥a / b∥ :=
  abs_norm_sub_norm_le' a b
#align dist_norm_norm_le' dist_norm_norm_le'

@[to_additive]
theorem norm_le_norm_add_norm_div' (u v : E) : ∥u∥ ≤ ∥v∥ + ∥u / v∥ := by
  rw [add_comm]
  refine' (norm_mul_le' _ _).trans_eq' _
  rw [div_mul_cancel']
#align norm_le_norm_add_norm_div' norm_le_norm_add_norm_div'

@[to_additive]
theorem norm_le_norm_add_norm_div (u v : E) : ∥v∥ ≤ ∥u∥ + ∥u / v∥ := by
  rw [norm_div_rev]
  exact norm_le_norm_add_norm_div' v u
#align norm_le_norm_add_norm_div norm_le_norm_add_norm_div

alias norm_le_norm_add_norm_sub' ← norm_le_insert'

alias norm_le_norm_add_norm_sub ← norm_le_insert

@[to_additive]
theorem norm_le_mul_norm_add (u v : E) : ∥u∥ ≤ ∥u * v∥ + ∥v∥ :=
  calc
    ∥u∥ = ∥u * v / v∥ := by rw [mul_div_cancel'']
    _ ≤ ∥u * v∥ + ∥v∥ := norm_div_le _ _
    
#align norm_le_mul_norm_add norm_le_mul_norm_add

@[to_additive ball_eq]
theorem ball_eq' (y : E) (ε : ℝ) : ball y ε = { x | ∥x / y∥ < ε } :=
  Set.ext $ fun a => by simp [dist_eq_norm_div]
#align ball_eq' ball_eq'

@[to_additive]
theorem ball_one_eq (r : ℝ) : ball (1 : E) r = { x | ∥x∥ < r } :=
  Set.ext $ fun a => by simp
#align ball_one_eq ball_one_eq

@[to_additive mem_ball_iff_norm]
theorem mem_ball_iff_norm'' : b ∈ ball a r ↔ ∥b / a∥ < r := by rw [mem_ball, dist_eq_norm_div]
#align mem_ball_iff_norm'' mem_ball_iff_norm''

@[to_additive mem_ball_iff_norm']
theorem mem_ball_iff_norm''' : b ∈ ball a r ↔ ∥a / b∥ < r := by rw [mem_ball', dist_eq_norm_div]
#align mem_ball_iff_norm''' mem_ball_iff_norm'''

@[simp, to_additive]
theorem mem_ball_one_iff : a ∈ ball (1 : E) r ↔ ∥a∥ < r := by rw [mem_ball, dist_one_right]
#align mem_ball_one_iff mem_ball_one_iff

@[to_additive mem_closed_ball_iff_norm]
theorem mem_closed_ball_iff_norm'' : b ∈ closedBall a r ↔ ∥b / a∥ ≤ r := by rw [mem_closed_ball, dist_eq_norm_div]
#align mem_closed_ball_iff_norm'' mem_closed_ball_iff_norm''

@[simp, to_additive]
theorem mem_closed_ball_one_iff : a ∈ closedBall (1 : E) r ↔ ∥a∥ ≤ r := by rw [mem_closed_ball, dist_one_right]
#align mem_closed_ball_one_iff mem_closed_ball_one_iff

@[to_additive mem_closed_ball_iff_norm']
theorem mem_closed_ball_iff_norm''' : b ∈ closedBall a r ↔ ∥a / b∥ ≤ r := by rw [mem_closed_ball', dist_eq_norm_div]
#align mem_closed_ball_iff_norm''' mem_closed_ball_iff_norm'''

@[to_additive norm_le_of_mem_closed_ball]
theorem norm_le_of_mem_closed_ball' (h : b ∈ closedBall a r) : ∥b∥ ≤ ∥a∥ + r :=
  (norm_le_norm_add_norm_div' _ _).trans $ add_le_add_left (by rwa [← dist_eq_norm_div]) _
#align norm_le_of_mem_closed_ball' norm_le_of_mem_closed_ball'

@[to_additive norm_le_norm_add_const_of_dist_le]
theorem norm_le_norm_add_const_of_dist_le' : dist a b ≤ r → ∥a∥ ≤ ∥b∥ + r :=
  norm_le_of_mem_closed_ball'
#align norm_le_norm_add_const_of_dist_le' norm_le_norm_add_const_of_dist_le'

@[to_additive norm_lt_of_mem_ball]
theorem norm_lt_of_mem_ball' (h : b ∈ ball a r) : ∥b∥ < ∥a∥ + r :=
  (norm_le_norm_add_norm_div' _ _).trans_lt $ add_lt_add_left (by rwa [← dist_eq_norm_div]) _
#align norm_lt_of_mem_ball' norm_lt_of_mem_ball'

@[to_additive]
theorem norm_div_sub_norm_div_le_norm_div (u v w : E) : ∥u / w∥ - ∥v / w∥ ≤ ∥u / v∥ := by
  simpa only [div_div_div_cancel_right'] using norm_sub_norm_le' (u / w) (v / w)
#align norm_div_sub_norm_div_le_norm_div norm_div_sub_norm_div_le_norm_div

@[to_additive bounded_iff_forall_norm_le]
theorem bounded_iff_forall_norm_le' : Bounded s ↔ ∃ C, ∀ x ∈ s, ∥x∥ ≤ C := by
  simpa only [Set.subset_def, mem_closed_ball_one_iff] using bounded_iff_subset_ball (1 : E)
#align bounded_iff_forall_norm_le' bounded_iff_forall_norm_le'

alias bounded_iff_forall_norm_le' ↔ Metric.Bounded.exists_norm_le' _

alias bounded_iff_forall_norm_le ↔ Metric.Bounded.exists_norm_le _

attribute [to_additive Metric.Bounded.exists_norm_le] Metric.Bounded.exists_norm_le'

@[to_additive Metric.Bounded.exists_pos_norm_le]
theorem Metric.Bounded.exists_pos_norm_le' (hs : Metric.Bounded s) : ∃ R > 0, ∀ x ∈ s, ∥x∥ ≤ R :=
  let ⟨R₀, hR₀⟩ := hs.exists_norm_le'
  ⟨max R₀ 1, by positivity, fun x hx => (hR₀ x hx).trans $ le_max_left _ _⟩
#align metric.bounded.exists_pos_norm_le' Metric.Bounded.exists_pos_norm_le'

@[simp, to_additive mem_sphere_iff_norm]
theorem mem_sphere_iff_norm' : b ∈ sphere a r ↔ ∥b / a∥ = r := by simp [dist_eq_norm_div]
#align mem_sphere_iff_norm' mem_sphere_iff_norm'

@[simp, to_additive]
theorem mem_sphere_one_iff_norm : a ∈ sphere (1 : E) r ↔ ∥a∥ = r := by simp [dist_eq_norm_div]
#align mem_sphere_one_iff_norm mem_sphere_one_iff_norm

@[simp, to_additive norm_eq_of_mem_sphere]
theorem norm_eq_of_mem_sphere' (x : sphere (1 : E) r) : ∥(x : E)∥ = r :=
  mem_sphere_one_iff_norm.mp x.2
#align norm_eq_of_mem_sphere' norm_eq_of_mem_sphere'

@[to_additive]
theorem ne_one_of_mem_sphere (hr : r ≠ 0) (x : sphere (1 : E) r) : (x : E) ≠ 1 :=
  ne_one_of_norm_ne_zero $ by rwa [norm_eq_of_mem_sphere' x]
#align ne_one_of_mem_sphere ne_one_of_mem_sphere

@[to_additive ne_zero_of_mem_unit_sphere]
theorem ne_one_of_mem_unit_sphere (x : sphere (1 : E) 1) : (x : E) ≠ 1 :=
  ne_one_of_mem_sphere one_ne_zero _
#align ne_one_of_mem_unit_sphere ne_one_of_mem_unit_sphere

variable (E)

/-- The norm of a seminormed group as a group seminorm. -/
@[to_additive "The norm of a seminormed group as an additive group seminorm."]
def normGroupSeminorm : GroupSeminorm E :=
  ⟨norm, norm_one', norm_mul_le', norm_inv'⟩
#align norm_group_seminorm normGroupSeminorm

@[simp, to_additive]
theorem coe_norm_group_seminorm : ⇑(normGroupSeminorm E) = norm :=
  rfl
#align coe_norm_group_seminorm coe_norm_group_seminorm

variable {E}

namespace Isometric

-- TODO This material is superseded by similar constructions such as
-- `affine_isometry_equiv.const_vadd`; deduplicate
/-- Multiplication `y ↦ y * x` as an `isometry`. -/
@[to_additive "Addition `y ↦ y + x` as an `isometry`"]
protected def mulRight (x : E) : E ≃ᵢ E :=
  { Equiv.mulRight x with isometryToFun := Isometry.ofDistEq $ fun y z => dist_mul_right _ _ _ }
#align isometric.mul_right Isometric.mulRight

@[simp, to_additive]
theorem mul_right_to_equiv (x : E) : (Isometric.mulRight x).toEquiv = Equiv.mulRight x :=
  rfl
#align isometric.mul_right_to_equiv Isometric.mul_right_to_equiv

@[simp, to_additive]
theorem coe_mul_right (x : E) : (Isometric.mulRight x : E → E) = fun y => y * x :=
  rfl
#align isometric.coe_mul_right Isometric.coe_mul_right

@[to_additive]
theorem mul_right_apply (x y : E) : (Isometric.mulRight x : E → E) y = y * x :=
  rfl
#align isometric.mul_right_apply Isometric.mul_right_apply

@[simp, to_additive]
theorem mul_right_symm (x : E) : (Isometric.mulRight x).symm = Isometric.mulRight x⁻¹ :=
  ext $ fun y => rfl
#align isometric.mul_right_symm Isometric.mul_right_symm

end Isometric

@[to_additive]
theorem NormedCommGroup.tendsto_nhds_one {f : α → E} {l : Filter α} :
    Tendsto f l (𝓝 1) ↔ ∀ ε > 0, ∀ᶠ x in l, ∥f x∥ < ε :=
  Metric.tendsto_nhds.trans $ by simp only [dist_one_right]
#align normed_comm_group.tendsto_nhds_one NormedCommGroup.tendsto_nhds_one

@[to_additive]
theorem NormedCommGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ∥x' / x∥ < δ → ∥f x' / y∥ < ε := by
  simp_rw [Metric.tendsto_nhds_nhds, dist_eq_norm_div]
#align normed_comm_group.tendsto_nhds_nhds NormedCommGroup.tendsto_nhds_nhds

@[to_additive]
theorem NormedCommGroup.cauchy_seq_iff [Nonempty α] [SemilatticeSup α] {u : α → E} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → ∥u m / u n∥ < ε := by
  simp [Metric.cauchy_seq_iff, dist_eq_norm_div]
#align normed_comm_group.cauchy_seq_iff NormedCommGroup.cauchy_seq_iff

@[to_additive]
theorem NormedCommGroup.nhds_basis_norm_lt (x : E) : (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ∥y / x∥ < ε } :=
  by
  simp_rw [← ball_eq']
  exact Metric.nhds_basis_ball
#align normed_comm_group.nhds_basis_norm_lt NormedCommGroup.nhds_basis_norm_lt

@[to_additive]
theorem NormedCommGroup.nhds_one_basis_norm_lt : (𝓝 (1 : E)).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ∥y∥ < ε } :=
  by
  convert NormedCommGroup.nhds_basis_norm_lt (1 : E)
  simp
#align normed_comm_group.nhds_one_basis_norm_lt NormedCommGroup.nhds_one_basis_norm_lt

@[to_additive]
theorem NormedCommGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : E × E | ∥p.fst / p.snd∥ < ε } := by
  convert Metric.uniformity_basis_dist
  simp [dist_eq_norm_div]
#align normed_comm_group.uniformity_basis_dist NormedCommGroup.uniformity_basis_dist

open Finset

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. The analogous condition for a linear map of
(semi)normed spaces is in `normed_space.operator_norm`. -/
@[to_additive
      "A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C`\nsuch that for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. The analogous condition for a linear map of\n(semi)normed spaces is in `normed_space.operator_norm`."]
theorem MonoidHomClass.lipschitzOfBound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C * ∥x∥) :
    LipschitzWith (Real.toNnreal C) f :=
  LipschitzWith.ofDistLe' $ fun x y => by simpa only [dist_eq_norm_div, map_div] using h (x / y)
#align monoid_hom_class.lipschitz_of_bound MonoidHomClass.lipschitzOfBound

@[to_additive]
theorem lipschitz_on_with_iff_norm_div_le {f : E → F} {C : ℝ≥0} :
    LipschitzOnWith C f s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∥f x / f y∥ ≤ C * ∥x / y∥ := by
  simp only [lipschitz_on_with_iff_dist_le_mul, dist_eq_norm_div]
#align lipschitz_on_with_iff_norm_div_le lipschitz_on_with_iff_norm_div_le

alias lipschitz_on_with_iff_norm_div_le ↔ LipschitzOnWith.norm_div_le _

attribute [to_additive] LipschitzOnWith.norm_div_le

@[to_additive]
theorem LipschitzOnWith.norm_div_le_of_le {f : E → F} {C : ℝ≥0} (h : LipschitzOnWith C f s) (ha : a ∈ s) (hb : b ∈ s)
    (hr : ∥a / b∥ ≤ r) : ∥f a / f b∥ ≤ C * r :=
  (h.norm_div_le ha hb).trans $ mul_le_mul_of_nonneg_left hr C.2
#align lipschitz_on_with.norm_div_le_of_le LipschitzOnWith.norm_div_le_of_le

@[to_additive]
theorem lipschitz_with_iff_norm_div_le {f : E → F} {C : ℝ≥0} : LipschitzWith C f ↔ ∀ x y, ∥f x / f y∥ ≤ C * ∥x / y∥ :=
  by simp only [lipschitz_with_iff_dist_le_mul, dist_eq_norm_div]
#align lipschitz_with_iff_norm_div_le lipschitz_with_iff_norm_div_le

alias lipschitz_with_iff_norm_div_le ↔ LipschitzWith.norm_div_le _

attribute [to_additive] LipschitzWith.norm_div_le

@[to_additive]
theorem LipschitzWith.norm_div_le_of_le {f : E → F} {C : ℝ≥0} (h : LipschitzWith C f) (hr : ∥a / b∥ ≤ r) :
    ∥f a / f b∥ ≤ C * r :=
  (h.norm_div_le _ _).trans $ mul_le_mul_of_nonneg_left hr C.2
#align lipschitz_with.norm_div_le_of_le LipschitzWith.norm_div_le_of_le

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. -/
@[to_additive
      "A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C`\nsuch that for all `x`, one has `∥f x∥ ≤ C * ∥x∥`"]
theorem MonoidHomClass.continuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C * ∥x∥) :
    Continuous f :=
  (MonoidHomClass.lipschitzOfBound f C h).Continuous
#align monoid_hom_class.continuous_of_bound MonoidHomClass.continuous_of_bound

@[to_additive]
theorem MonoidHomClass.uniform_continuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ) (h : ∀ x, ∥f x∥ ≤ C * ∥x∥) :
    UniformContinuous f :=
  (MonoidHomClass.lipschitzOfBound f C h).UniformContinuous
#align monoid_hom_class.uniform_continuous_of_bound MonoidHomClass.uniform_continuous_of_bound

@[to_additive IsCompact.exists_bound_of_continuous_on]
theorem IsCompact.exists_bound_of_continuous_on' [TopologicalSpace α] {s : Set α} (hs : IsCompact s) {f : α → E}
    (hf : ContinuousOn f s) : ∃ C, ∀ x ∈ s, ∥f x∥ ≤ C :=
  (bounded_iff_forall_norm_le'.1 (hs.image_of_continuous_on hf).Bounded).imp $ fun C hC x hx =>
    hC _ $ Set.mem_image_of_mem _ hx
#align is_compact.exists_bound_of_continuous_on' IsCompact.exists_bound_of_continuous_on'

@[to_additive]
theorem MonoidHomClass.isometry_iff_norm [MonoidHomClass 𝓕 E F] (f : 𝓕) : Isometry f ↔ ∀ x, ∥f x∥ = ∥x∥ := by
  simp only [isometry_iff_dist_eq, dist_eq_norm_div, ← map_div]
  refine' ⟨fun h x => _, fun h x y => h _⟩
  simpa using h x 1
#align monoid_hom_class.isometry_iff_norm MonoidHomClass.isometry_iff_norm

alias MonoidHomClass.isometry_iff_norm ↔ _ MonoidHomClass.isometryOfNorm

attribute [to_additive] MonoidHomClass.isometryOfNorm

section Nnnorm

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedGroup.toHasNnnorm : HasNnnorm E :=
  ⟨fun a => ⟨∥a∥, norm_nonneg' a⟩⟩
#align seminormed_group.to_has_nnnorm SeminormedGroup.toHasNnnorm

@[simp, norm_cast, to_additive coe_nnnorm]
theorem coe_nnnorm' (a : E) : (∥a∥₊ : ℝ) = ∥a∥ :=
  rfl
#align coe_nnnorm' coe_nnnorm'

@[simp, to_additive coe_comp_nnnorm]
theorem coe_comp_nnnorm' : (coe : ℝ≥0 → ℝ) ∘ (nnnorm : E → ℝ≥0) = norm :=
  rfl
#align coe_comp_nnnorm' coe_comp_nnnorm'

@[to_additive norm_to_nnreal]
theorem norm_to_nnreal' : ∥a∥.toNnreal = ∥a∥₊ :=
  @Real.to_nnreal_coe ∥a∥₊
#align norm_to_nnreal' norm_to_nnreal'

@[to_additive]
theorem nndist_eq_nnnorm_div (a b : E) : nndist a b = ∥a / b∥₊ :=
  Nnreal.eq $ dist_eq_norm_div _ _
#align nndist_eq_nnnorm_div nndist_eq_nnnorm_div

alias nndist_eq_nnnorm_sub ← nndist_eq_nnnorm

@[simp, to_additive nnnorm_zero]
theorem nnnorm_one' : ∥(1 : E)∥₊ = 0 :=
  Nnreal.eq norm_one'
#align nnnorm_one' nnnorm_one'

@[to_additive]
theorem ne_one_of_nnnorm_ne_zero {a : E} : ∥a∥₊ ≠ 0 → a ≠ 1 :=
  mt $ by
    rintro rfl
    exact nnnorm_one'
#align ne_one_of_nnnorm_ne_zero ne_one_of_nnnorm_ne_zero

@[to_additive nnnorm_add_le]
theorem nnnorm_mul_le' (a b : E) : ∥a * b∥₊ ≤ ∥a∥₊ + ∥b∥₊ :=
  Nnreal.coe_le_coe.1 $ norm_mul_le' a b
#align nnnorm_mul_le' nnnorm_mul_le'

@[simp, to_additive nnnorm_neg]
theorem nnnorm_inv' (a : E) : ∥a⁻¹∥₊ = ∥a∥₊ :=
  Nnreal.eq $ norm_inv' a
#align nnnorm_inv' nnnorm_inv'

@[to_additive]
theorem nnnorm_div_le (a b : E) : ∥a / b∥₊ ≤ ∥a∥₊ + ∥b∥₊ :=
  Nnreal.coe_le_coe.1 $ norm_div_le _ _
#align nnnorm_div_le nnnorm_div_le

@[to_additive nndist_nnnorm_nnnorm_le]
theorem nndist_nnnorm_nnnorm_le' (a b : E) : nndist ∥a∥₊ ∥b∥₊ ≤ ∥a / b∥₊ :=
  Nnreal.coe_le_coe.1 $ dist_norm_norm_le' a b
#align nndist_nnnorm_nnnorm_le' nndist_nnnorm_nnnorm_le'

@[to_additive]
theorem nnnorm_le_nnnorm_add_nnnorm_div (a b : E) : ∥b∥₊ ≤ ∥a∥₊ + ∥a / b∥₊ :=
  norm_le_norm_add_norm_div _ _
#align nnnorm_le_nnnorm_add_nnnorm_div nnnorm_le_nnnorm_add_nnnorm_div

@[to_additive]
theorem nnnorm_le_nnnorm_add_nnnorm_div' (a b : E) : ∥a∥₊ ≤ ∥b∥₊ + ∥a / b∥₊ :=
  norm_le_norm_add_norm_div' _ _
#align nnnorm_le_nnnorm_add_nnnorm_div' nnnorm_le_nnnorm_add_nnnorm_div'

alias nnnorm_le_nnnorm_add_nnnorm_sub' ← nnnorm_le_insert'

alias nnnorm_le_nnnorm_add_nnnorm_sub ← nnnorm_le_insert

@[to_additive]
theorem nnnorm_le_mul_nnnorm_add (a b : E) : ∥a∥₊ ≤ ∥a * b∥₊ + ∥b∥₊ :=
  norm_le_mul_norm_add _ _
#align nnnorm_le_mul_nnnorm_add nnnorm_le_mul_nnnorm_add

@[to_additive of_real_norm_eq_coe_nnnorm]
theorem of_real_norm_eq_coe_nnnorm' (a : E) : Ennreal.ofReal ∥a∥ = ∥a∥₊ :=
  Ennreal.of_real_eq_coe_nnreal _
#align of_real_norm_eq_coe_nnnorm' of_real_norm_eq_coe_nnnorm'

@[to_additive]
theorem edist_eq_coe_nnnorm_div (a b : E) : edist a b = ∥a / b∥₊ := by
  rw [edist_dist, dist_eq_norm_div, of_real_norm_eq_coe_nnnorm']
#align edist_eq_coe_nnnorm_div edist_eq_coe_nnnorm_div

@[to_additive edist_eq_coe_nnnorm]
theorem edist_eq_coe_nnnorm' (x : E) : edist x 1 = (∥x∥₊ : ℝ≥0∞) := by rw [edist_eq_coe_nnnorm_div, div_one]
#align edist_eq_coe_nnnorm' edist_eq_coe_nnnorm'

@[to_additive]
theorem mem_emetric_ball_one_iff {r : ℝ≥0∞} : a ∈ Emetric.ball (1 : E) r ↔ ↑∥a∥₊ < r := by
  rw [Emetric.mem_ball, edist_eq_coe_nnnorm']
#align mem_emetric_ball_one_iff mem_emetric_ball_one_iff

@[simp, to_additive]
theorem edist_mul_right (a₁ a₂ b : E) : edist (a₁ * b) (a₂ * b) = edist a₁ a₂ := by simp [edist_dist]
#align edist_mul_right edist_mul_right

@[simp, to_additive]
theorem edist_div_right (a₁ a₂ b : E) : edist (a₁ / b) (a₂ / b) = edist a₁ a₂ := by
  simpa only [div_eq_mul_inv] using edist_mul_right _ _ _
#align edist_div_right edist_div_right

@[to_additive]
theorem MonoidHomClass.lipschitzOfBoundNnnorm [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ≥0) (h : ∀ x, ∥f x∥₊ ≤ C * ∥x∥₊) :
    LipschitzWith C f :=
  @Real.to_nnreal_coe C ▸ MonoidHomClass.lipschitzOfBound f C h
#align monoid_hom_class.lipschitz_of_bound_nnnorm MonoidHomClass.lipschitzOfBoundNnnorm

@[to_additive]
theorem MonoidHomClass.antilipschitzOfBound [MonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0} (h : ∀ x, ∥x∥ ≤ K * ∥f x∥) :
    AntilipschitzWith K f :=
  AntilipschitzWith.ofLeMulDist $ fun x y => by simpa only [dist_eq_norm_div, map_div] using h (x / y)
#align monoid_hom_class.antilipschitz_of_bound MonoidHomClass.antilipschitzOfBound

@[to_additive]
theorem MonoidHomClass.bound_of_antilipschitz [MonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0} (h : AntilipschitzWith K f) (x) :
    ∥x∥ ≤ K * ∥f x∥ := by simpa only [dist_one_right, map_one] using h.le_mul_dist x 1
#align monoid_hom_class.bound_of_antilipschitz MonoidHomClass.bound_of_antilipschitz

end Nnnorm

@[to_additive]
theorem tendsto_iff_norm_tendsto_one {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ∥f e / b∥) a (𝓝 0) := by
  convert tendsto_iff_dist_tendsto_zero
  simp [dist_eq_norm_div]
#align tendsto_iff_norm_tendsto_one tendsto_iff_norm_tendsto_one

@[to_additive]
theorem tendsto_one_iff_norm_tendsto_one {f : α → E} {a : Filter α} :
    Tendsto f a (𝓝 1) ↔ Tendsto (fun e => ∥f e∥) a (𝓝 0) := by
  rw [tendsto_iff_norm_tendsto_one]
  simp only [div_one]
#align tendsto_one_iff_norm_tendsto_one tendsto_one_iff_norm_tendsto_one

@[to_additive]
theorem comap_norm_nhds_one : comap norm (𝓝 0) = 𝓝 (1 : E) := by
  simpa only [dist_one_right] using nhds_comap_dist (1 : E)
#align comap_norm_nhds_one comap_norm_nhds_one

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `a` which tends to `0`, then `f` tends to `1`. In this pair of lemmas (`squeeze_one_norm'`
and `squeeze_one_norm`), following a convention of similar lemmas in `topology.metric_space.basic`
and `topology.algebra.order`, the `'` version is phrased using "eventually" and the non-`'` version
is phrased absolutely. -/
@[to_additive
      "Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a\nreal function `a` which tends to `0`, then `f` tends to `1`. In this pair of lemmas\n(`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of similar lemmas in\n`topology.metric_space.basic` and `topology.algebra.order`, the `'` version is phrased using\n\"eventually\" and the non-`'` version is phrased absolutely."]
theorem squeeze_one_norm' {f : α → E} {a : α → ℝ} {t₀ : Filter α} (h : ∀ᶠ n in t₀, ∥f n∥ ≤ a n)
    (h' : Tendsto a t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 1) :=
  tendsto_one_iff_norm_tendsto_one.2 $ squeeze_zero' (eventually_of_forall $ fun n => norm_nonneg' _) h h'
#align squeeze_one_norm' squeeze_one_norm'

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `a` which
tends to `0`, then `f` tends to `1`. -/
@[to_additive
      "Special case of the sandwich theorem: if the norm of `f` is bounded by a real\nfunction `a` which tends to `0`, then `f` tends to `0`."]
theorem squeeze_one_norm {f : α → E} {a : α → ℝ} {t₀ : Filter α} (h : ∀ n, ∥f n∥ ≤ a n) :
    Tendsto a t₀ (𝓝 0) → Tendsto f t₀ (𝓝 1) :=
  squeeze_one_norm' $ eventually_of_forall h
#align squeeze_one_norm squeeze_one_norm

@[to_additive]
theorem tendsto_norm_div_self (x : E) : Tendsto (fun a => ∥a / x∥) (𝓝 x) (𝓝 0) := by
  simpa [dist_eq_norm_div] using tendsto_id.dist (tendsto_const_nhds : tendsto (fun a => (x : E)) (𝓝 x) _)
#align tendsto_norm_div_self tendsto_norm_div_self

@[to_additive tendsto_norm]
theorem tendsto_norm' {x : E} : Tendsto (fun a => ∥a∥) (𝓝 x) (𝓝 ∥x∥) := by
  simpa using tendsto_id.dist (tendsto_const_nhds : tendsto (fun a => (1 : E)) _ _)
#align tendsto_norm' tendsto_norm'

@[to_additive]
theorem tendsto_norm_one : Tendsto (fun a : E => ∥a∥) (𝓝 1) (𝓝 0) := by simpa using tendsto_norm_div_self (1 : E)
#align tendsto_norm_one tendsto_norm_one

@[continuity, to_additive continuous_norm]
theorem continuous_norm' : Continuous fun a : E => ∥a∥ := by
  simpa using continuous_id.dist (continuous_const : Continuous fun a => (1 : E))
#align continuous_norm' continuous_norm'

@[continuity, to_additive continuous_nnnorm]
theorem continuous_nnnorm' : Continuous fun a : E => ∥a∥₊ :=
  continuous_norm'.subtype_mk _
#align continuous_nnnorm' continuous_nnnorm'

@[to_additive lipschitzWithOneNorm]
theorem lipschitzWithOneNorm' : LipschitzWith 1 (norm : E → ℝ) := by
  simpa only [dist_one_left] using LipschitzWith.distRight (1 : E)
#align lipschitz_with_one_norm' lipschitzWithOneNorm'

@[to_additive lipschitzWithOneNnnorm]
theorem lipschitzWithOneNnnorm' : LipschitzWith 1 (HasNnnorm.nnnorm : E → ℝ≥0) :=
  lipschitzWithOneNorm'
#align lipschitz_with_one_nnnorm' lipschitzWithOneNnnorm'

@[to_additive uniform_continuous_norm]
theorem uniform_continuous_norm' : UniformContinuous (norm : E → ℝ) :=
  lipschitzWithOneNorm'.UniformContinuous
#align uniform_continuous_norm' uniform_continuous_norm'

@[to_additive uniform_continuous_nnnorm]
theorem uniform_continuous_nnnorm' : UniformContinuous fun a : E => ∥a∥₊ :=
  uniform_continuous_norm'.subtype_mk _
#align uniform_continuous_nnnorm' uniform_continuous_nnnorm'

@[to_additive]
theorem mem_closure_one_iff_norm {x : E} : x ∈ closure ({1} : Set E) ↔ ∥x∥ = 0 := by
  rw [← closed_ball_zero', mem_closed_ball_one_iff, (norm_nonneg' x).le_iff_eq]
#align mem_closure_one_iff_norm mem_closure_one_iff_norm

@[to_additive]
theorem closure_one_eq : closure ({1} : Set E) = { x | ∥x∥ = 0 } :=
  Set.ext fun x => mem_closure_one_iff_norm
#align closure_one_eq closure_one_eq

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `∥op x y∥ ≤ A * ∥x∥ * ∥y∥` for some constant A instead of
multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive
      "A helper lemma used to prove that the (scalar or usual) product of a function that\ntends to zero and a bounded function tends to zero. This lemma is formulated for any binary\noperation `op : E → F → G` with an estimate `∥op x y∥ ≤ A * ∥x∥ * ∥y∥` for some constant A instead\nof multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`."]
theorem Filter.Tendsto.op_one_is_bounded_under_le' {f : α → E} {g : α → F} {l : Filter α} (hf : Tendsto f l (𝓝 1))
    (hg : IsBoundedUnder (· ≤ ·) l (norm ∘ g)) (op : E → F → G) (h_op : ∃ A, ∀ x y, ∥op x y∥ ≤ A * ∥x∥ * ∥y∥) :
    Tendsto (fun x => op (f x) (g x)) l (𝓝 1) := by
  cases' h_op with A h_op
  rcases hg with ⟨C, hC⟩
  rw [eventually_map] at hC
  rw [NormedCommGroup.tendsto_nhds_one] at hf⊢
  intro ε ε₀
  rcases exists_pos_mul_lt ε₀ (A * C) with ⟨δ, δ₀, hδ⟩
  filter_upwards [hf δ δ₀, hC] with i hf hg
  refine' (h_op _ _).trans_lt _
  cases' le_total A 0 with hA hA
  · exact
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hA $ norm_nonneg' _) $ norm_nonneg' _).trans_lt ε₀
    
  calc
    A * ∥f i∥ * ∥g i∥ ≤ A * δ * C :=
      mul_le_mul (mul_le_mul_of_nonneg_left hf.le hA) hg (norm_nonneg' _) (mul_nonneg hA δ₀.le)
    _ = A * C * δ := mul_right_comm _ _ _
    _ < ε := hδ
    
#align filter.tendsto.op_one_is_bounded_under_le' Filter.Tendsto.op_one_is_bounded_under_le'

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `∥op x y∥ ≤ ∥x∥ * ∥y∥` instead of multiplication so that it
can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive
      "A helper lemma used to prove that the (scalar or usual) product of a function that\ntends to zero and a bounded function tends to zero. This lemma is formulated for any binary\noperation `op : E → F → G` with an estimate `∥op x y∥ ≤ ∥x∥ * ∥y∥` instead of multiplication so that\nit can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`."]
theorem Filter.Tendsto.op_one_is_bounded_under_le {f : α → E} {g : α → F} {l : Filter α} (hf : Tendsto f l (𝓝 1))
    (hg : IsBoundedUnder (· ≤ ·) l (norm ∘ g)) (op : E → F → G) (h_op : ∀ x y, ∥op x y∥ ≤ ∥x∥ * ∥y∥) :
    Tendsto (fun x => op (f x) (g x)) l (𝓝 1) :=
  hf.op_one_is_bounded_under_le' hg op ⟨1, fun x y => (one_mul ∥x∥).symm ▸ h_op x y⟩
#align filter.tendsto.op_one_is_bounded_under_le Filter.Tendsto.op_one_is_bounded_under_le

section

variable {l : Filter α} {f : α → E}

@[to_additive Filter.Tendsto.norm]
theorem Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ∥f x∥) l (𝓝 ∥a∥) :=
  tendsto_norm'.comp h
#align filter.tendsto.norm' Filter.Tendsto.norm'

@[to_additive Filter.Tendsto.nnnorm]
theorem Filter.Tendsto.nnnorm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ∥f x∥₊) l (𝓝 ∥a∥₊) :=
  Tendsto.comp continuous_nnnorm'.ContinuousAt h
#align filter.tendsto.nnnorm' Filter.Tendsto.nnnorm'

end

section

variable [TopologicalSpace α] {f : α → E}

@[to_additive Continuous.norm]
theorem Continuous.norm' : Continuous f → Continuous fun x => ∥f x∥ :=
  continuous_norm'.comp
#align continuous.norm' Continuous.norm'

@[to_additive Continuous.nnnorm]
theorem Continuous.nnnorm' : Continuous f → Continuous fun x => ∥f x∥₊ :=
  continuous_nnnorm'.comp
#align continuous.nnnorm' Continuous.nnnorm'

@[to_additive ContinuousAt.norm]
theorem ContinuousAt.norm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ∥f x∥) a :=
  h.norm'
#align continuous_at.norm' ContinuousAt.norm'

@[to_additive ContinuousAt.nnnorm]
theorem ContinuousAt.nnnorm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ∥f x∥₊) a :=
  h.nnnorm'
#align continuous_at.nnnorm' ContinuousAt.nnnorm'

@[to_additive ContinuousWithinAt.norm]
theorem ContinuousWithinAt.norm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ∥f x∥) s a :=
  h.norm'
#align continuous_within_at.norm' ContinuousWithinAt.norm'

@[to_additive ContinuousWithinAt.nnnorm]
theorem ContinuousWithinAt.nnnorm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ∥f x∥₊) s a :=
  h.nnnorm'
#align continuous_within_at.nnnorm' ContinuousWithinAt.nnnorm'

@[to_additive ContinuousOn.norm]
theorem ContinuousOn.norm' {s : Set α} (h : ContinuousOn f s) : ContinuousOn (fun x => ∥f x∥) s := fun x hx =>
  (h x hx).norm'
#align continuous_on.norm' ContinuousOn.norm'

@[to_additive ContinuousOn.nnnorm]
theorem ContinuousOn.nnnorm' {s : Set α} (h : ContinuousOn f s) : ContinuousOn (fun x => ∥f x∥₊) s := fun x hx =>
  (h x hx).nnnorm'
#align continuous_on.nnnorm' ContinuousOn.nnnorm'

end

/-- If `∥y∥ → ∞`, then we can assume `y ≠ x` for any fixed `x`. -/
@[to_additive eventually_ne_of_tendsto_norm_at_top "If `∥y∥→∞`, then we can assume `y≠x` for any\nfixed `x`"]
theorem eventually_ne_of_tendsto_norm_at_top' {l : Filter α} {f : α → E} (h : Tendsto (fun y => ∥f y∥) l atTop)
    (x : E) : ∀ᶠ y in l, f y ≠ x :=
  (h.eventually_ne_at_top _).mono $ fun x => ne_of_apply_ne norm
#align eventually_ne_of_tendsto_norm_at_top' eventually_ne_of_tendsto_norm_at_top'

@[to_additive]
theorem SeminormedCommGroup.mem_closure_iff : a ∈ closure s ↔ ∀ ε, 0 < ε → ∃ b ∈ s, ∥a / b∥ < ε := by
  simp [Metric.mem_closure_iff, dist_eq_norm_div]
#align seminormed_comm_group.mem_closure_iff SeminormedCommGroup.mem_closure_iff

@[to_additive norm_le_zero_iff']
theorem norm_le_zero_iff''' [T0Space E] {a : E} : ∥a∥ ≤ 0 ↔ a = 1 := by
  letI : NormedGroup E := { ‹SeminormedGroup E› with toMetricSpace := Metric.ofT0PseudoMetricSpace E }
  rw [← dist_one_right, dist_le_zero]
#align norm_le_zero_iff''' norm_le_zero_iff'''

@[to_additive norm_eq_zero']
theorem norm_eq_zero''' [T0Space E] {a : E} : ∥a∥ = 0 ↔ a = 1 :=
  (norm_nonneg' a).le_iff_eq.symm.trans norm_le_zero_iff'''
#align norm_eq_zero''' norm_eq_zero'''

@[to_additive norm_pos_iff']
theorem norm_pos_iff''' [T0Space E] {a : E} : 0 < ∥a∥ ↔ a ≠ 1 := by rw [← not_le, norm_le_zero_iff''']
#align norm_pos_iff''' norm_pos_iff'''

@[to_additive]
theorem SeminormedGroup.tendsto_uniformly_on_one {f : ι → κ → G} {s : Set κ} {l : Filter ι} :
    TendstoUniformlyOn f 1 l s ↔ ∀ ε > 0, ∀ᶠ i in l, ∀ x ∈ s, ∥f i x∥ < ε := by
  simp_rw [tendsto_uniformly_on_iff, Pi.one_apply, dist_one_left]
#align seminormed_group.tendsto_uniformly_on_one SeminormedGroup.tendsto_uniformly_on_one

@[to_additive]
theorem SeminormedGroup.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_one {f : ι → κ → G} {l : Filter ι}
    {l' : Filter κ} :
    UniformCauchySeqOnFilter f l l' ↔
      TendstoUniformlyOnFilter (fun n : ι × ι => fun z => f n.fst z / f n.snd z) 1 (l ×ᶠ l) l' :=
  by
  refine' ⟨fun hf u hu => _, fun hf u hu => _⟩
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine'
      (hf { p : G × G | dist p.fst p.snd < ε } $ dist_mem_uniformity hε).mono fun x hx =>
        H 1 (f x.fst.fst x.snd / f x.fst.snd x.snd) _
    simpa [dist_eq_norm_div, norm_div_rev] using hx
    
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine'
      (hf { p : G × G | dist p.fst p.snd < ε } $ dist_mem_uniformity hε).mono fun x hx =>
        H (f x.fst.fst x.snd) (f x.fst.snd x.snd) _
    simpa [dist_eq_norm_div, norm_div_rev] using hx
    
#align
  seminormed_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_one SeminormedGroup.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_one

@[to_additive]
theorem SeminormedGroup.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_one {f : ι → κ → G} {s : Set κ} {l : Filter ι} :
    UniformCauchySeqOn f l s ↔ TendstoUniformlyOn (fun n : ι × ι => fun z => f n.fst z / f n.snd z) 1 (l ×ᶠ l) s := by
  rw [tendsto_uniformly_on_iff_tendsto_uniformly_on_filter, uniform_cauchy_seq_on_iff_uniform_cauchy_seq_on_filter,
    SeminormedGroup.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_one]
#align
  seminormed_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_one SeminormedGroup.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_one

end SeminormedGroup

section Induced

variable (E F)

-- See note [reducible non-instances]
/-- A group homomorphism from a `group` to a `seminormed_group` induces a `seminormed_group`
structure on the domain. -/
@[reducible,
  to_additive
      "A group homomorphism from an `add_group` to a `seminormed_add_group` induces a\n`seminormed_add_group` structure on the domain."]
def SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) : SeminormedGroup E :=
  { PseudoMetricSpace.induced f _ with norm := fun x => ∥f x∥,
    dist_eq := fun x y => by simpa only [map_div, ← dist_eq_norm_div] }
#align seminormed_group.induced SeminormedGroup.induced

-- See note [reducible non-instances]
/-- A group homomorphism from a `comm_group` to a `seminormed_group` induces a
`seminormed_comm_group` structure on the domain. -/
@[reducible,
  to_additive
      "A group homomorphism from an `add_comm_group` to a `seminormed_add_group` induces a\n`seminormed_add_comm_group` structure on the domain."]
def SeminormedCommGroup.induced [CommGroup E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedCommGroup E :=
  { SeminormedGroup.induced E F f with }
#align seminormed_comm_group.induced SeminormedCommGroup.induced

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `group` to a `normed_group` induces a `normed_group`
structure on the domain. -/
@[reducible,
  to_additive
      "An injective group homomorphism from an `add_group` to a `normed_add_group` induces a\n`normed_add_group` structure on the domain."]
def NormedGroup.induced [Group E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) (h : Injective f) : NormedGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }
#align normed_group.induced NormedGroup.induced

-- See note [reducible non-instances].
/-- An injective group homomorphism from an `comm_group` to a `normed_group` induces a
`normed_comm_group` structure on the domain. -/
@[reducible,
  to_additive
      "An injective group homomorphism from an `comm_group` to a `normed_comm_group` induces a\n`normed_comm_group` structure on the domain."]
def NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) (h : Injective f) :
    NormedCommGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }
#align normed_comm_group.induced NormedCommGroup.induced

end Induced

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[simp, to_additive]
theorem dist_mul_left (a b₁ b₂ : E) : dist (a * b₁) (a * b₂) = dist b₁ b₂ := by simp [dist_eq_norm_div]
#align dist_mul_left dist_mul_left

@[to_additive]
theorem dist_inv (x y : E) : dist x⁻¹ y = dist x y⁻¹ := by
  simp_rw [dist_eq_norm_div, ← norm_inv' (x⁻¹ / y), inv_div, div_inv_eq_mul, mul_comm]
#align dist_inv dist_inv

@[simp, to_additive]
theorem dist_inv_inv (a b : E) : dist a⁻¹ b⁻¹ = dist a b := by rw [dist_inv, inv_inv]
#align dist_inv_inv dist_inv_inv

@[simp, to_additive]
theorem dist_div_left (a b₁ b₂ : E) : dist (a / b₁) (a / b₂) = dist b₁ b₂ := by
  simp only [div_eq_mul_inv, dist_mul_left, dist_inv_inv]
#align dist_div_left dist_div_left

@[simp, to_additive]
theorem dist_self_mul_right (a b : E) : dist a (a * b) = ∥b∥ := by rw [← dist_one_left, ← dist_mul_left a 1 b, mul_one]
#align dist_self_mul_right dist_self_mul_right

@[simp, to_additive]
theorem dist_self_mul_left (a b : E) : dist (a * b) a = ∥b∥ := by rw [dist_comm, dist_self_mul_right]
#align dist_self_mul_left dist_self_mul_left

@[simp, to_additive]
theorem dist_self_div_right (a b : E) : dist a (a / b) = ∥b∥ := by rw [div_eq_mul_inv, dist_self_mul_right, norm_inv']
#align dist_self_div_right dist_self_div_right

@[simp, to_additive]
theorem dist_self_div_left (a b : E) : dist (a / b) a = ∥b∥ := by rw [dist_comm, dist_self_div_right]
#align dist_self_div_left dist_self_div_left

@[to_additive]
theorem dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [dist_mul_left, dist_mul_right] using dist_triangle (a₁ * a₂) (b₁ * a₂) (b₁ * b₂)
#align dist_mul_mul_le dist_mul_mul_le

@[to_additive]
theorem dist_mul_mul_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) : dist (a₁ * a₂) (b₁ * b₂) ≤ r₁ + r₂ :=
  (dist_mul_mul_le a₁ a₂ b₁ b₂).trans $ add_le_add h₁ h₂
#align dist_mul_mul_le_of_le dist_mul_mul_le_of_le

@[to_additive]
theorem dist_div_div_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ / a₂) (b₁ / b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [div_eq_mul_inv, dist_inv_inv] using dist_mul_mul_le a₁ a₂⁻¹ b₁ b₂⁻¹
#align dist_div_div_le dist_div_div_le

@[to_additive]
theorem dist_div_div_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) : dist (a₁ / a₂) (b₁ / b₂) ≤ r₁ + r₂ :=
  (dist_div_div_le a₁ a₂ b₁ b₂).trans $ add_le_add h₁ h₂
#align dist_div_div_le_of_le dist_div_div_le_of_le

@[to_additive]
theorem abs_dist_sub_le_dist_mul_mul (a₁ a₂ b₁ b₂ : E) : |dist a₁ b₁ - dist a₂ b₂| ≤ dist (a₁ * a₂) (b₁ * b₂) := by
  simpa only [dist_mul_left, dist_mul_right, dist_comm b₂] using abs_dist_sub_le (a₁ * a₂) (b₁ * b₂) (b₁ * a₂)
#align abs_dist_sub_le_dist_mul_mul abs_dist_sub_le_dist_mul_mul

theorem norm_multiset_sum_le {E} [SeminormedAddCommGroup E] (m : Multiset E) : ∥m.Sum∥ ≤ (m.map fun x => ∥x∥).Sum :=
  m.le_sum_of_subadditive norm norm_zero norm_add_le
#align norm_multiset_sum_le norm_multiset_sum_le

@[to_additive]
theorem norm_multiset_prod_le (m : Multiset E) : ∥m.Prod∥ ≤ (m.map $ fun x => ∥x∥).Sum := by
  rw [← Multiplicative.of_add_le, of_add_multiset_prod, Multiset.map_map]
  refine' Multiset.le_prod_of_submultiplicative (Multiplicative.ofAdd ∘ norm) _ (fun x y => _) _
  · simp only [comp_app, norm_one', of_add_zero]
    
  · exact norm_mul_le' _ _
    
#align norm_multiset_prod_le norm_multiset_prod_le

theorem norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) : ∥∑ i in s, f i∥ ≤ ∑ i in s, ∥f i∥ :=
  s.le_sum_of_subadditive norm norm_zero norm_add_le f
#align norm_sum_le norm_sum_le

@[to_additive]
theorem norm_prod_le (s : Finset ι) (f : ι → E) : ∥∏ i in s, f i∥ ≤ ∑ i in s, ∥f i∥ := by
  rw [← Multiplicative.of_add_le, of_add_sum]
  refine' Finset.le_prod_of_submultiplicative (Multiplicative.ofAdd ∘ norm) _ (fun x y => _) _ _
  · simp only [comp_app, norm_one', of_add_zero]
    
  · exact norm_mul_le' _ _
    
#align norm_prod_le norm_prod_le

@[to_additive]
theorem norm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀ b ∈ s, ∥f b∥ ≤ n b) :
    ∥∏ b in s, f b∥ ≤ ∑ b in s, n b :=
  (norm_prod_le s f).trans $ Finset.sum_le_sum h
#align norm_prod_le_of_le norm_prod_le_of_le

@[to_additive]
theorem dist_prod_prod_le_of_le (s : Finset ι) {f a : ι → E} {d : ι → ℝ} (h : ∀ b ∈ s, dist (f b) (a b) ≤ d b) :
    dist (∏ b in s, f b) (∏ b in s, a b) ≤ ∑ b in s, d b := by
  simp only [dist_eq_norm_div, ← Finset.prod_div_distrib] at *
  exact norm_prod_le_of_le s h
#align dist_prod_prod_le_of_le dist_prod_prod_le_of_le

@[to_additive]
theorem dist_prod_prod_le (s : Finset ι) (f a : ι → E) :
    dist (∏ b in s, f b) (∏ b in s, a b) ≤ ∑ b in s, dist (f b) (a b) :=
  dist_prod_prod_le_of_le s $ fun _ _ => le_rfl
#align dist_prod_prod_le dist_prod_prod_le

@[to_additive]
theorem mul_mem_ball_iff_norm : a * b ∈ ball a r ↔ ∥b∥ < r := by rw [mem_ball_iff_norm'', mul_div_cancel''']
#align mul_mem_ball_iff_norm mul_mem_ball_iff_norm

@[to_additive]
theorem mul_mem_closed_ball_iff_norm : a * b ∈ closedBall a r ↔ ∥b∥ ≤ r := by
  rw [mem_closed_ball_iff_norm'', mul_div_cancel''']
#align mul_mem_closed_ball_iff_norm mul_mem_closed_ball_iff_norm

@[simp, to_additive]
theorem preimage_mul_ball (a b : E) (r : ℝ) : (· * ·) b ⁻¹' ball a r = ball (a / b) r := by
  ext c
  simp only [dist_eq_norm_div, Set.mem_preimage, mem_ball, div_div_eq_mul_div, mul_comm]
#align preimage_mul_ball preimage_mul_ball

@[simp, to_additive]
theorem preimage_mul_closed_ball (a b : E) (r : ℝ) : (· * ·) b ⁻¹' closedBall a r = closedBall (a / b) r := by
  ext c
  simp only [dist_eq_norm_div, Set.mem_preimage, mem_closed_ball, div_div_eq_mul_div, mul_comm]
#align preimage_mul_closed_ball preimage_mul_closed_ball

@[simp, to_additive]
theorem preimage_mul_sphere (a b : E) (r : ℝ) : (· * ·) b ⁻¹' sphere a r = sphere (a / b) r := by
  ext c
  simp only [Set.mem_preimage, mem_sphere_iff_norm', div_div_eq_mul_div, mul_comm]
#align preimage_mul_sphere preimage_mul_sphere

namespace Isometric

/-- Multiplication `y ↦ x * y` as an `isometry`. -/
@[to_additive "Addition `y ↦ x + y` as an `isometry`"]
protected def mulLeft (x : E) : E ≃ᵢ E where
  isometryToFun := Isometry.ofDistEq $ fun y z => dist_mul_left _ _ _
  toEquiv := Equiv.mulLeft x
#align isometric.mul_left Isometric.mulLeft

@[simp, to_additive]
theorem mul_left_to_equiv (x : E) : (Isometric.mulLeft x).toEquiv = Equiv.mulLeft x :=
  rfl
#align isometric.mul_left_to_equiv Isometric.mul_left_to_equiv

@[simp, to_additive]
theorem coe_mul_left (x : E) : ⇑(Isometric.mulLeft x) = (· * ·) x :=
  rfl
#align isometric.coe_mul_left Isometric.coe_mul_left

@[simp, to_additive]
theorem mul_left_symm (x : E) : (Isometric.mulLeft x).symm = Isometric.mulLeft x⁻¹ :=
  ext $ fun y => rfl
#align isometric.mul_left_symm Isometric.mul_left_symm

variable (E)

/-- Inversion `x ↦ x⁻¹` as an `isometry`. -/
@[to_additive "Negation `x ↦ -x` as an `isometry`."]
protected def inv : E ≃ᵢ E where
  isometryToFun := Isometry.ofDistEq $ fun x y => dist_inv_inv _ _
  toEquiv := Equiv.inv E
#align isometric.inv Isometric.inv

variable {E}

@[simp, to_additive]
theorem inv_symm : (Isometric.inv E).symm = Isometric.inv E :=
  rfl
#align isometric.inv_symm Isometric.inv_symm

@[simp, to_additive]
theorem inv_to_equiv : (Isometric.inv E).toEquiv = Equiv.inv E :=
  rfl
#align isometric.inv_to_equiv Isometric.inv_to_equiv

@[simp, to_additive]
theorem coe_inv : ⇑(Isometric.inv E) = Inv.inv :=
  rfl
#align isometric.coe_inv Isometric.coe_inv

end Isometric

open Finset

@[to_additive]
theorem controlled_prod_of_mem_closure {s : Subgroup E} (hg : a ∈ closure (s : Set E)) {b : ℕ → ℝ}
    (b_pos : ∀ n, 0 < b n) :
    ∃ v : ℕ → E,
      Tendsto (fun n => ∏ i in range (n + 1), v i) atTop (𝓝 a) ∧
        (∀ n, v n ∈ s) ∧ ∥v 0 / a∥ < b 0 ∧ ∀ n, 0 < n → ∥v n∥ < b n :=
  by
  obtain ⟨u : ℕ → E, u_in : ∀ n, u n ∈ s, lim_u : tendsto u at_top (𝓝 a)⟩ := mem_closure_iff_seq_limit.mp hg
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ∥u n / a∥ < b 0 :=
    haveI : { x | ∥x / a∥ < b 0 } ∈ 𝓝 a := by
      simp_rw [← dist_eq_norm_div]
      exact Metric.ball_mem_nhds _ (b_pos _)
    filter.tendsto_at_top'.mp lim_u _ this
  set z : ℕ → E := fun n => u (n + n₀)
  have lim_z : tendsto z at_top (𝓝 a) := lim_u.comp (tendsto_add_at_top_nat n₀)
  have mem_𝓤 : ∀ n, { p : E × E | ∥p.1 / p.2∥ < b (n + 1) } ∈ 𝓤 E := fun n => by
    simpa [← dist_eq_norm_div] using Metric.dist_mem_uniformity (b_pos $ n + 1)
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ∥z (φ $ n + 1) / z (φ n)∥ < b (n + 1)⟩ :=
    lim_z.cauchy_seq.subseq_mem mem_𝓤
  set w : ℕ → E := z ∘ φ
  have hw : tendsto w at_top (𝓝 a) := lim_z.comp φ_extr.tendsto_at_top
  set v : ℕ → E := fun i => if i = 0 then w 0 else w i / w (i - 1)
  refine' ⟨v, tendsto.congr (Finset.eq_prod_range_div' w) hw, _, hn₀ _ (n₀.le_add_left _), _⟩
  · rintro ⟨⟩
    · change w 0 ∈ s
      apply u_in
      
    · apply s.div_mem <;> apply u_in
      
    
  · intro l hl
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1
    exact Nat.exists_eq_succ_of_ne_zero hl.ne'
    apply hφ
    
#align controlled_prod_of_mem_closure controlled_prod_of_mem_closure

@[to_additive]
theorem controlled_prod_of_mem_closure_range {j : E →* F} {b : F} (hb : b ∈ closure (j.range : Set F)) {f : ℕ → ℝ}
    (b_pos : ∀ n, 0 < f n) :
    ∃ a : ℕ → E,
      Tendsto (fun n => ∏ i in range (n + 1), j (a i)) atTop (𝓝 b) ∧
        ∥j (a 0) / b∥ < f 0 ∧ ∀ n, 0 < n → ∥j (a n)∥ < f n :=
  by
  obtain ⟨v, sum_v, v_in, hv₀, hv_pos⟩ := controlled_prod_of_mem_closure hb b_pos
  choose g hg using v_in
  refine' ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀, fun n hn => by simpa [hg] using hv_pos n hn⟩
#align controlled_prod_of_mem_closure_range controlled_prod_of_mem_closure_range

@[to_additive]
theorem nndist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : nndist (a₁ * a₂) (b₁ * b₂) ≤ nndist a₁ b₁ + nndist a₂ b₂ :=
  Nnreal.coe_le_coe.1 $ dist_mul_mul_le a₁ a₂ b₁ b₂
#align nndist_mul_mul_le nndist_mul_mul_le

@[to_additive]
theorem edist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : edist (a₁ * a₂) (b₁ * b₂) ≤ edist a₁ b₁ + edist a₂ b₂ := by
  simp only [edist_nndist]
  norm_cast
  apply nndist_mul_mul_le
#align edist_mul_mul_le edist_mul_mul_le

@[simp, to_additive]
theorem edist_mul_left (a b₁ b₂ : E) : edist (a * b₁) (a * b₂) = edist b₁ b₂ := by simp [edist_dist]
#align edist_mul_left edist_mul_left

@[to_additive]
theorem edist_inv (a b : E) : edist a⁻¹ b = edist a b⁻¹ := by simp_rw [edist_dist, dist_inv]
#align edist_inv edist_inv

@[simp, to_additive]
theorem edist_inv_inv (x y : E) : edist x⁻¹ y⁻¹ = edist x y := by rw [edist_inv, inv_inv]
#align edist_inv_inv edist_inv_inv

@[simp, to_additive]
theorem edist_div_left (a b₁ b₂ : E) : edist (a / b₁) (a / b₂) = edist b₁ b₂ := by
  simp only [div_eq_mul_inv, edist_mul_left, edist_inv_inv]
#align edist_div_left edist_div_left

@[to_additive]
theorem nnnorm_multiset_prod_le (m : Multiset E) : ∥m.Prod∥₊ ≤ (m.map fun x => ∥x∥₊).Sum :=
  Nnreal.coe_le_coe.1 $ by
    push_cast
    rw [Multiset.map_map]
    exact norm_multiset_prod_le _
#align nnnorm_multiset_prod_le nnnorm_multiset_prod_le

@[to_additive]
theorem nnnorm_prod_le (s : Finset ι) (f : ι → E) : ∥∏ a in s, f a∥₊ ≤ ∑ a in s, ∥f a∥₊ :=
  Nnreal.coe_le_coe.1 $ by
    push_cast
    exact norm_prod_le _ _
#align nnnorm_prod_le nnnorm_prod_le

@[to_additive]
theorem nnnorm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ≥0} (h : ∀ b ∈ s, ∥f b∥₊ ≤ n b) :
    ∥∏ b in s, f b∥₊ ≤ ∑ b in s, n b :=
  (norm_prod_le_of_le s h).trans_eq Nnreal.coe_sum.symm
#align nnnorm_prod_le_of_le nnnorm_prod_le_of_le

namespace Real

instance : HasNorm ℝ where norm r := |r|

@[simp]
theorem norm_eq_abs (r : ℝ) : ∥r∥ = |r| :=
  rfl
#align real.norm_eq_abs Real.norm_eq_abs

instance : NormedAddCommGroup ℝ :=
  ⟨fun r y => rfl⟩

theorem norm_of_nonneg (hr : 0 ≤ r) : ∥r∥ = r :=
  abs_of_nonneg hr
#align real.norm_of_nonneg Real.norm_of_nonneg

theorem norm_of_nonpos (hr : r ≤ 0) : ∥r∥ = -r :=
  abs_of_nonpos hr
#align real.norm_of_nonpos Real.norm_of_nonpos

theorem le_norm_self (r : ℝ) : r ≤ ∥r∥ :=
  le_abs_self r
#align real.le_norm_self Real.le_norm_self

@[simp]
theorem norm_coe_nat (n : ℕ) : ∥(n : ℝ)∥ = n :=
  abs_of_nonneg n.cast_nonneg
#align real.norm_coe_nat Real.norm_coe_nat

@[simp]
theorem nnnorm_coe_nat (n : ℕ) : ∥(n : ℝ)∥₊ = n :=
  Nnreal.eq $ norm_coe_nat _
#align real.nnnorm_coe_nat Real.nnnorm_coe_nat

@[simp]
theorem norm_two : ∥(2 : ℝ)∥ = 2 :=
  abs_of_pos (@zero_lt_two ℝ _ _)
#align real.norm_two Real.norm_two

@[simp]
theorem nnnorm_two : ∥(2 : ℝ)∥₊ = 2 :=
  Nnreal.eq $ by simp
#align real.nnnorm_two Real.nnnorm_two

theorem nnnorm_of_nonneg (hr : 0 ≤ r) : ∥r∥₊ = ⟨r, hr⟩ :=
  Nnreal.eq $ norm_of_nonneg hr
#align real.nnnorm_of_nonneg Real.nnnorm_of_nonneg

theorem ennnorm_eq_of_real (hr : 0 ≤ r) : (∥r∥₊ : ℝ≥0∞) = Ennreal.ofReal r := by
  rw [← of_real_norm_eq_coe_nnnorm, norm_of_nonneg hr]
#align real.ennnorm_eq_of_real Real.ennnorm_eq_of_real

theorem to_nnreal_eq_nnnorm_of_nonneg (hr : 0 ≤ r) : r.toNnreal = ∥r∥₊ := by
  rw [Real.to_nnreal_of_nonneg hr]
  congr
  rw [Real.norm_eq_abs, abs_of_nonneg hr]
#align real.to_nnreal_eq_nnnorm_of_nonneg Real.to_nnreal_eq_nnnorm_of_nonneg

theorem of_real_le_ennnorm (r : ℝ) : Ennreal.ofReal r ≤ ∥r∥₊ := by
  obtain hr | hr := le_total 0 r
  · exact (Real.ennnorm_eq_of_real hr).ge
    
  · rw [Ennreal.of_real_eq_zero.2 hr]
    exact bot_le
    
#align real.of_real_le_ennnorm Real.of_real_le_ennnorm

end Real

namespace LipschitzWith

variable [PseudoEmetricSpace α] {K Kf Kg : ℝ≥0} {f g : α → E}

@[to_additive]
theorem inv (hf : LipschitzWith K f) : LipschitzWith K fun x => (f x)⁻¹ := fun x y =>
  (edist_inv_inv _ _).trans_le $ hf x y
#align lipschitz_with.inv LipschitzWith.inv

@[to_additive add]
theorem mul' (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) fun x => f x * g x :=
  fun x y =>
  calc
    edist (f x * g x) (f y * g y) ≤ edist (f x) (f y) + edist (g x) (g y) := edist_mul_mul_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm
    
#align lipschitz_with.mul' LipschitzWith.mul'

@[to_additive]
theorem div (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) fun x => f x / g x := by
  simpa only [div_eq_mul_inv] using hf.mul' hg.inv
#align lipschitz_with.div LipschitzWith.div

end LipschitzWith

namespace AntilipschitzWith

variable [PseudoEmetricSpace α] {K Kf Kg : ℝ≥0} {f g : α → E}

@[to_additive]
theorem mulLipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg g) (hK : Kg < Kf⁻¹) :
    AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ fun x => f x * g x := by
  letI : PseudoMetricSpace α := PseudoEmetricSpace.toPseudoMetricSpace hf.edist_ne_top
  refine' AntilipschitzWith.ofLeMulDist fun x y => _
  rw [Nnreal.coe_inv, ← div_eq_inv_mul]
  rw [le_div_iff (Nnreal.coe_pos.2 $ tsub_pos_iff_lt.2 hK)]
  rw [mul_comm, Nnreal.coe_sub hK.le, sub_mul]
  calc
    ↑Kf⁻¹ * dist x y - Kg * dist x y ≤ dist (f x) (f y) - dist (g x) (g y) :=
      sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
    _ ≤ _ := le_trans (le_abs_self _) (abs_dist_sub_le_dist_mul_mul _ _ _ _)
    
#align antilipschitz_with.mul_lipschitz_with AntilipschitzWith.mulLipschitzWith

@[to_additive]
theorem mulDivLipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg (g / f)) (hK : Kg < Kf⁻¹) :
    AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ g := by
  simpa only [Pi.div_apply, mul_div_cancel'_right] using hf.mul_lipschitz_with hg hK
#align antilipschitz_with.mul_div_lipschitz_with AntilipschitzWith.mulDivLipschitzWith

@[to_additive]
theorem le_mul_norm_div {f : E → F} (hf : AntilipschitzWith K f) (x y : E) : ∥x / y∥ ≤ K * ∥f x / f y∥ := by
  simp [← dist_eq_norm_div, hf.le_mul_dist x y]
#align antilipschitz_with.le_mul_norm_div AntilipschitzWith.le_mul_norm_div

end AntilipschitzWith

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.toHasLipschitzMul : HasLipschitzMul E :=
  ⟨⟨1 + 1, LipschitzWith.prodFst.mul' LipschitzWith.prodSnd⟩⟩
#align seminormed_comm_group.to_has_lipschitz_mul SeminormedCommGroup.toHasLipschitzMul

-- See note [lower instance priority]
/-- A seminormed group is a uniform group, i.e., multiplication and division are uniformly
continuous. -/
@[to_additive
      "A seminormed group is a uniform additive group, i.e., addition and\nsubtraction are uniformly continuous."]
instance (priority := 100) SeminormedCommGroup.to_uniform_group : UniformGroup E :=
  ⟨(LipschitzWith.prodFst.div LipschitzWith.prodSnd).UniformContinuous⟩
#align seminormed_comm_group.to_uniform_group SeminormedCommGroup.to_uniform_group

-- short-circuit type class inference
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.to_topological_group : TopologicalGroup E :=
  inferInstance
#align seminormed_comm_group.to_topological_group SeminormedCommGroup.to_topological_group

@[to_additive]
theorem cauchySeqProdOfEventuallyEq {u v : ℕ → E} {N : ℕ} (huv : ∀ n ≥ N, u n = v n)
    (hv : CauchySeq fun n => ∏ k in range (n + 1), v k) : CauchySeq fun n => ∏ k in range (n + 1), u k := by
  let d : ℕ → E := fun n => ∏ k in range (n + 1), u k / v k
  rw [show (fun n => ∏ k in range (n + 1), u k) = d * fun n => ∏ k in range (n + 1), v k by
      ext n
      simp [d]]
  suffices ∀ n ≥ N, d n = d N by exact (tendsto_at_top_of_eventually_const this).CauchySeq.mul hv
  intro n hn
  dsimp [d]
  rw [eventually_constant_prod _ hn]
  intro m hm
  simp [huv m hm]
#align cauchy_seq_prod_of_eventually_eq cauchySeqProdOfEventuallyEq

end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] [NormedGroup F] {a b : E}

@[simp, to_additive norm_eq_zero]
theorem norm_eq_zero'' : ∥a∥ = 0 ↔ a = 1 :=
  norm_eq_zero'''
#align norm_eq_zero'' norm_eq_zero''

@[to_additive norm_ne_zero_iff]
theorem norm_ne_zero_iff' : ∥a∥ ≠ 0 ↔ a ≠ 1 :=
  norm_eq_zero''.Not
#align norm_ne_zero_iff' norm_ne_zero_iff'

@[simp, to_additive norm_pos_iff]
theorem norm_pos_iff'' : 0 < ∥a∥ ↔ a ≠ 1 :=
  norm_pos_iff'''
#align norm_pos_iff'' norm_pos_iff''

@[simp, to_additive norm_le_zero_iff]
theorem norm_le_zero_iff'' : ∥a∥ ≤ 0 ↔ a = 1 :=
  norm_le_zero_iff'''
#align norm_le_zero_iff'' norm_le_zero_iff''

@[to_additive]
theorem norm_div_eq_zero_iff : ∥a / b∥ = 0 ↔ a = b := by rw [norm_eq_zero'', div_eq_one]
#align norm_div_eq_zero_iff norm_div_eq_zero_iff

@[to_additive]
theorem norm_div_pos_iff : 0 < ∥a / b∥ ↔ a ≠ b := by
  rw [(norm_nonneg' _).lt_iff_ne, ne_comm]
  exact norm_div_eq_zero_iff.not
#align norm_div_pos_iff norm_div_pos_iff

@[to_additive]
theorem eq_of_norm_div_le_zero (h : ∥a / b∥ ≤ 0) : a = b := by rwa [← div_eq_one, ← norm_le_zero_iff'']
#align eq_of_norm_div_le_zero eq_of_norm_div_le_zero

alias norm_div_eq_zero_iff ↔ eq_of_norm_div_eq_zero _

attribute [to_additive] eq_of_norm_div_eq_zero

@[simp, to_additive nnnorm_eq_zero]
theorem nnnorm_eq_zero' : ∥a∥₊ = 0 ↔ a = 1 := by rw [← Nnreal.coe_eq_zero, coe_nnnorm', norm_eq_zero'']
#align nnnorm_eq_zero' nnnorm_eq_zero'

@[to_additive nnnorm_ne_zero_iff]
theorem nnnorm_ne_zero_iff' : ∥a∥₊ ≠ 0 ↔ a ≠ 1 :=
  nnnorm_eq_zero'.Not
#align nnnorm_ne_zero_iff' nnnorm_ne_zero_iff'

@[to_additive]
theorem tendsto_norm_div_self_punctured_nhds (a : E) : Tendsto (fun x => ∥x / a∥) (𝓝[≠] a) (𝓝[>] 0) :=
  (tendsto_norm_div_self a).inf $ tendsto_principal_principal.2 $ fun x hx => norm_pos_iff''.2 $ div_ne_one.2 hx
#align tendsto_norm_div_self_punctured_nhds tendsto_norm_div_self_punctured_nhds

@[to_additive]
theorem tendsto_norm_nhds_within_one : Tendsto (norm : E → ℝ) (𝓝[≠] 1) (𝓝[>] 0) :=
  tendsto_norm_one.inf $ tendsto_principal_principal.2 $ fun x => norm_pos_iff''.2
#align tendsto_norm_nhds_within_one tendsto_norm_nhds_within_one

variable (E)

/-- The norm of a normed group as a group norm. -/
@[to_additive "The norm of a normed group as an additive group norm."]
def normGroupNorm : GroupNorm E :=
  { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero''.1 }
#align norm_group_norm normGroupNorm

@[simp]
theorem coe_norm_group_norm : ⇑(normGroupNorm E) = norm :=
  rfl
#align coe_norm_group_norm coe_norm_group_norm

end NormedGroup

section NormedAddGroup

variable [NormedAddGroup E] [TopologicalSpace α] {f : α → E}

/-! Some relations with `has_compact_support` -/


theorem has_compact_support_norm_iff : (HasCompactSupport fun x => ∥f x∥) ↔ HasCompactSupport f :=
  has_compact_support_comp_left $ fun x => norm_eq_zero
#align has_compact_support_norm_iff has_compact_support_norm_iff

alias has_compact_support_norm_iff ↔ _ HasCompactSupport.norm

theorem Continuous.bounded_above_of_compact_support (hf : Continuous f) (h : HasCompactSupport f) :
    ∃ C, ∀ x, ∥f x∥ ≤ C := by simpa [bdd_above_def] using hf.norm.bdd_above_range_of_has_compact_support h.norm
#align continuous.bounded_above_of_compact_support Continuous.bounded_above_of_compact_support

end NormedAddGroup

/-! ### `ulift` -/


namespace ULift

section HasNorm

variable [HasNorm E]

instance : HasNorm (ULift E) :=
  ⟨fun x => ∥x.down∥⟩

theorem norm_def (x : ULift E) : ∥x∥ = ∥x.down∥ :=
  rfl
#align ulift.norm_def ULift.norm_def

@[simp]
theorem norm_up (x : E) : ∥ULift.up x∥ = ∥x∥ :=
  rfl
#align ulift.norm_up ULift.norm_up

@[simp]
theorem norm_down (x : ULift E) : ∥x.down∥ = ∥x∥ :=
  rfl
#align ulift.norm_down ULift.norm_down

end HasNorm

section HasNnnorm

variable [HasNnnorm E]

instance : HasNnnorm (ULift E) :=
  ⟨fun x => ∥x.down∥₊⟩

theorem nnnorm_def (x : ULift E) : ∥x∥₊ = ∥x.down∥₊ :=
  rfl
#align ulift.nnnorm_def ULift.nnnorm_def

@[simp]
theorem nnnorm_up (x : E) : ∥ULift.up x∥₊ = ∥x∥₊ :=
  rfl
#align ulift.nnnorm_up ULift.nnnorm_up

@[simp]
theorem nnnorm_down (x : ULift E) : ∥x.down∥₊ = ∥x∥₊ :=
  rfl
#align ulift.nnnorm_down ULift.nnnorm_down

end HasNnnorm

@[to_additive]
instance seminormedGroup [SeminormedGroup E] : SeminormedGroup (ULift E) :=
  SeminormedGroup.induced _ _ (⟨ULift.down, rfl, fun _ _ => rfl⟩ : ULift E →* E)
#align ulift.seminormed_group ULift.seminormedGroup

@[to_additive]
instance seminormedCommGroup [SeminormedCommGroup E] : SeminormedCommGroup (ULift E) :=
  SeminormedCommGroup.induced _ _ (⟨ULift.down, rfl, fun _ _ => rfl⟩ : ULift E →* E)
#align ulift.seminormed_comm_group ULift.seminormedCommGroup

@[to_additive]
instance normedGroup [NormedGroup E] : NormedGroup (ULift E) :=
  NormedGroup.induced _ _ (⟨ULift.down, rfl, fun _ _ => rfl⟩ : ULift E →* E) down_injective
#align ulift.normed_group ULift.normedGroup

@[to_additive]
instance normedCommGroup [NormedCommGroup E] : NormedCommGroup (ULift E) :=
  NormedCommGroup.induced _ _ (⟨ULift.down, rfl, fun _ _ => rfl⟩ : ULift E →* E) down_injective
#align ulift.normed_comm_group ULift.normedCommGroup

end ULift

/-! ### `additive`, `multiplicative` -/


section AdditiveMultiplicative

open Additive Multiplicative

section HasNorm

variable [HasNorm E]

instance : HasNorm (Additive E) :=
  ‹HasNorm E›

instance : HasNorm (Multiplicative E) :=
  ‹HasNorm E›

@[simp]
theorem norm_to_mul (x) : ∥(toMul x : E)∥ = ∥x∥ :=
  rfl
#align norm_to_mul norm_to_mul

@[simp]
theorem norm_of_mul (x : E) : ∥ofMul x∥ = ∥x∥ :=
  rfl
#align norm_of_mul norm_of_mul

@[simp]
theorem norm_to_add (x) : ∥(toAdd x : E)∥ = ∥x∥ :=
  rfl
#align norm_to_add norm_to_add

@[simp]
theorem norm_of_add (x : E) : ∥ofAdd x∥ = ∥x∥ :=
  rfl
#align norm_of_add norm_of_add

end HasNorm

section HasNnnorm

variable [HasNnnorm E]

instance : HasNnnorm (Additive E) :=
  ‹HasNnnorm E›

instance : HasNnnorm (Multiplicative E) :=
  ‹HasNnnorm E›

@[simp]
theorem nnnorm_to_mul (x) : ∥(toMul x : E)∥₊ = ∥x∥₊ :=
  rfl
#align nnnorm_to_mul nnnorm_to_mul

@[simp]
theorem nnnorm_of_mul (x : E) : ∥ofMul x∥₊ = ∥x∥₊ :=
  rfl
#align nnnorm_of_mul nnnorm_of_mul

@[simp]
theorem nnnorm_to_add (x) : ∥(toAdd x : E)∥₊ = ∥x∥₊ :=
  rfl
#align nnnorm_to_add nnnorm_to_add

@[simp]
theorem nnnorm_of_add (x : E) : ∥ofAdd x∥₊ = ∥x∥₊ :=
  rfl
#align nnnorm_of_add nnnorm_of_add

end HasNnnorm

instance [SeminormedGroup E] : SeminormedAddGroup (Additive E) where dist_eq := dist_eq_norm_div

instance [SeminormedAddGroup E] : SeminormedGroup (Multiplicative E) where dist_eq := dist_eq_norm_sub

instance [SeminormedCommGroup E] : SeminormedAddCommGroup (Additive E) :=
  { Additive.seminormedAddGroup with }

instance [SeminormedAddCommGroup E] : SeminormedCommGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with }

instance [NormedGroup E] : NormedAddGroup (Additive E) :=
  { Additive.seminormedAddGroup with }

instance [NormedAddGroup E] : NormedGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with }

instance [NormedCommGroup E] : NormedAddCommGroup (Additive E) :=
  { Additive.seminormedAddGroup with }

instance [NormedAddCommGroup E] : NormedCommGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with }

end AdditiveMultiplicative

/-! ### Order dual -/


section OrderDual

open OrderDual

section HasNorm

variable [HasNorm E]

instance : HasNorm Eᵒᵈ :=
  ‹HasNorm E›

@[simp]
theorem norm_to_dual (x : E) : ∥toDual x∥ = ∥x∥ :=
  rfl
#align norm_to_dual norm_to_dual

@[simp]
theorem norm_of_dual (x : Eᵒᵈ) : ∥ofDual x∥ = ∥x∥ :=
  rfl
#align norm_of_dual norm_of_dual

end HasNorm

section HasNnnorm

variable [HasNnnorm E]

instance : HasNnnorm Eᵒᵈ :=
  ‹HasNnnorm E›

@[simp]
theorem nnnorm_to_dual (x : E) : ∥toDual x∥₊ = ∥x∥₊ :=
  rfl
#align nnnorm_to_dual nnnorm_to_dual

@[simp]
theorem nnnorm_of_dual (x : Eᵒᵈ) : ∥ofDual x∥₊ = ∥x∥₊ :=
  rfl
#align nnnorm_of_dual nnnorm_of_dual

end HasNnnorm

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [SeminormedGroup E] : SeminormedGroup Eᵒᵈ :=
  ‹SeminormedGroup E›

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [SeminormedCommGroup E] : SeminormedCommGroup Eᵒᵈ :=
  ‹SeminormedCommGroup E›

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [NormedGroup E] : NormedGroup Eᵒᵈ :=
  ‹NormedGroup E›

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [NormedCommGroup E] : NormedCommGroup Eᵒᵈ :=
  ‹NormedCommGroup E›

end OrderDual

/-! ### Binary product of normed groups -/


section HasNorm

variable [HasNorm E] [HasNorm F] {x : E × F} {r : ℝ}

instance : HasNorm (E × F) :=
  ⟨fun x => ∥x.1∥ ⊔ ∥x.2∥⟩

theorem Prod.norm_def (x : E × F) : ∥x∥ = max ∥x.1∥ ∥x.2∥ :=
  rfl
#align prod.norm_def Prod.norm_def

theorem norm_fst_le (x : E × F) : ∥x.1∥ ≤ ∥x∥ :=
  le_max_left _ _
#align norm_fst_le norm_fst_le

theorem norm_snd_le (x : E × F) : ∥x.2∥ ≤ ∥x∥ :=
  le_max_right _ _
#align norm_snd_le norm_snd_le

theorem norm_prod_le_iff : ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r :=
  max_le_iff
#align norm_prod_le_iff norm_prod_le_iff

end HasNorm

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F]

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive "Product of seminormed groups, using the sup norm."]
instance : SeminormedGroup (E × F) :=
  ⟨fun x y => by simp only [Prod.norm_def, Prod.dist_eq, dist_eq_norm_div, Prod.fst_div, Prod.snd_div]⟩

@[to_additive Prod.nnnorm_def']
theorem Prod.nnorm_def (x : E × F) : ∥x∥₊ = max ∥x.1∥₊ ∥x.2∥₊ :=
  rfl
#align prod.nnorm_def Prod.nnorm_def

end SeminormedGroup

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive "Product of seminormed groups, using the sup norm."]
instance [SeminormedCommGroup E] [SeminormedCommGroup F] : SeminormedCommGroup (E × F) :=
  { Prod.seminormedGroup with }

/-- Product of normed groups, using the sup norm. -/
@[to_additive "Product of normed groups, using the sup norm."]
instance [NormedGroup E] [NormedGroup F] : NormedGroup (E × F) :=
  { Prod.seminormedGroup with }

/-- Product of normed groups, using the sup norm. -/
@[to_additive "Product of normed groups, using the sup norm."]
instance [NormedCommGroup E] [NormedCommGroup F] : NormedCommGroup (E × F) :=
  { Prod.seminormedGroup with }

/-! ### Finite product of normed groups -/


section Pi

variable {π : ι → Type _} [Fintype ι]

section SeminormedGroup

variable [∀ i, SeminormedGroup (π i)] [SeminormedGroup E] (f : ∀ i, π i) {x : ∀ i, π i} {r : ℝ}

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance : SeminormedGroup (∀ i, π i) where
  norm f := ↑(Finset.univ.sup fun b => ∥f b∥₊)
  dist_eq x y :=
    congr_arg (coe : ℝ≥0 → ℝ) $
      congr_arg (Finset.sup Finset.univ) $
        funext $ fun a => show nndist (x a) (y a) = ∥x a / y a∥₊ from nndist_eq_nnnorm_div (x a) (y a)

@[to_additive Pi.norm_def]
theorem Pi.norm_def' : ∥f∥ = ↑(Finset.univ.sup fun b => ∥f b∥₊) :=
  rfl
#align pi.norm_def' Pi.norm_def'

@[to_additive Pi.nnnorm_def]
theorem Pi.nnnorm_def' : ∥f∥₊ = Finset.univ.sup fun b => ∥f b∥₊ :=
  Subtype.eta _ _
#align pi.nnnorm_def' Pi.nnnorm_def'

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_le_iff_of_nonneg
      "The seminorm of an element in a product space is `≤ r` if\nand only if the norm of each component is."]
theorem pi_norm_le_iff_of_nonneg' (hr : 0 ≤ r) : ∥x∥ ≤ r ↔ ∀ i, ∥x i∥ ≤ r := by
  simp only [← dist_one_right, dist_pi_le_iff hr, Pi.one_apply]
#align pi_norm_le_iff_of_nonneg' pi_norm_le_iff_of_nonneg'

@[to_additive pi_nnnorm_le_iff]
theorem pi_nnnorm_le_iff' {r : ℝ≥0} : ∥x∥₊ ≤ r ↔ ∀ i, ∥x i∥₊ ≤ r :=
  pi_norm_le_iff_of_nonneg' r.coe_nonneg
#align pi_nnnorm_le_iff' pi_nnnorm_le_iff'

@[to_additive pi_norm_le_iff_of_nonempty]
theorem pi_norm_le_iff_of_nonempty' [Nonempty ι] : ∥f∥ ≤ r ↔ ∀ b, ∥f b∥ ≤ r := by
  by_cases hr:0 ≤ r
  · exact pi_norm_le_iff_of_nonneg' hr
    
  · exact
      iff_of_false (fun h => hr $ (norm_nonneg' _).trans h) fun h =>
        hr $ (norm_nonneg' _).trans $ h $ Classical.arbitrary _
    
#align pi_norm_le_iff_of_nonempty' pi_norm_le_iff_of_nonempty'

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_lt_iff
      "The seminorm of an element in a product space is `< r` if and only if\nthe norm of each component is."]
theorem pi_norm_lt_iff' (hr : 0 < r) : ∥x∥ < r ↔ ∀ i, ∥x i∥ < r := by
  simp only [← dist_one_right, dist_pi_lt_iff hr, Pi.one_apply]
#align pi_norm_lt_iff' pi_norm_lt_iff'

@[to_additive pi_nnnorm_lt_iff]
theorem pi_nnnorm_lt_iff' {r : ℝ≥0} (hr : 0 < r) : ∥x∥₊ < r ↔ ∀ i, ∥x i∥₊ < r :=
  pi_norm_lt_iff' hr
#align pi_nnnorm_lt_iff' pi_nnnorm_lt_iff'

@[to_additive norm_le_pi_norm]
theorem norm_le_pi_norm' (i : ι) : ∥f i∥ ≤ ∥f∥ :=
  (pi_norm_le_iff_of_nonneg' $ norm_nonneg' _).1 le_rfl i
#align norm_le_pi_norm' norm_le_pi_norm'

@[to_additive nnnorm_le_pi_nnnorm]
theorem nnnorm_le_pi_nnnorm' (i : ι) : ∥f i∥₊ ≤ ∥f∥₊ :=
  norm_le_pi_norm' _ i
#align nnnorm_le_pi_nnnorm' nnnorm_le_pi_nnnorm'

@[to_additive pi_norm_const_le]
theorem pi_norm_const_le' (a : E) : ∥fun _ : ι => a∥ ≤ ∥a∥ :=
  (pi_norm_le_iff_of_nonneg' $ norm_nonneg' _).2 $ fun _ => le_rfl
#align pi_norm_const_le' pi_norm_const_le'

@[to_additive pi_nnnorm_const_le]
theorem pi_nnnorm_const_le' (a : E) : ∥fun _ : ι => a∥₊ ≤ ∥a∥₊ :=
  pi_norm_const_le' _
#align pi_nnnorm_const_le' pi_nnnorm_const_le'

@[simp, to_additive pi_norm_const]
theorem pi_norm_const' [Nonempty ι] (a : E) : ∥fun i : ι => a∥ = ∥a∥ := by
  simpa only [← dist_one_right] using dist_pi_const a 1
#align pi_norm_const' pi_norm_const'

@[simp, to_additive pi_nnnorm_const]
theorem pi_nnnorm_const' [Nonempty ι] (a : E) : ∥fun i : ι => a∥₊ = ∥a∥₊ :=
  Nnreal.eq $ pi_norm_const' a
#align pi_nnnorm_const' pi_nnnorm_const'

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_norm_apply_le_norm "The $L^1$ norm is less than the $L^\\infty$ norm scaled by\nthe cardinality."]
theorem Pi.sum_norm_apply_le_norm' : (∑ i, ∥f i∥) ≤ Fintype.card ι • ∥f∥ :=
  Finset.sum_le_card_nsmul _ _ _ $ fun i hi => norm_le_pi_norm' _ i
#align pi.sum_norm_apply_le_norm' Pi.sum_norm_apply_le_norm'

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_nnnorm_apply_le_nnnorm
      "The $L^1$ norm is less than the $L^\\infty$ norm scaled\nby the cardinality."]
theorem Pi.sum_nnnorm_apply_le_nnnorm' : (∑ i, ∥f i∥₊) ≤ Fintype.card ι • ∥f∥₊ :=
  Nnreal.coe_sum.trans_le $ Pi.sum_norm_apply_le_norm' _
#align pi.sum_nnnorm_apply_le_nnnorm' Pi.sum_nnnorm_apply_le_nnnorm'

end SeminormedGroup

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance Pi.seminormedCommGroup [∀ i, SeminormedCommGroup (π i)] : SeminormedCommGroup (∀ i, π i) :=
  { Pi.seminormedGroup with }
#align pi.seminormed_comm_group Pi.seminormedCommGroup

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance Pi.normedGroup [∀ i, NormedGroup (π i)] : NormedGroup (∀ i, π i) :=
  { Pi.seminormedGroup with }
#align pi.normed_group Pi.normedGroup

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance Pi.normedCommGroup [∀ i, NormedCommGroup (π i)] : NormedCommGroup (∀ i, π i) :=
  { Pi.seminormedGroup with }
#align pi.normed_comm_group Pi.normedCommGroup

end Pi

/-! ### Subgroups of normed groups -/


namespace Subgroup

section SeminormedGroup

variable [SeminormedGroup E] {s : Subgroup E}

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive "A subgroup of a seminormed group is also a seminormed group,\nwith the restriction of the norm."]
instance seminormedGroup : SeminormedGroup s :=
  SeminormedGroup.induced _ _ s.Subtype
#align subgroup.seminormed_group Subgroup.seminormedGroup

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[simp,
  to_additive
      "If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in\n`s` is equal to its norm in `E`."]
theorem coe_norm (x : s) : ∥x∥ = ∥(x : E)∥ :=
  rfl
#align subgroup.coe_norm Subgroup.coe_norm

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`.

This is a reversed version of the `simp` lemma `subgroup.coe_norm` for use by `norm_cast`. -/
@[norm_cast,
  to_additive
      "If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm\nin `s` is equal to its norm in `E`.\n\nThis is a reversed version of the `simp` lemma `add_subgroup.coe_norm` for use by `norm_cast`."]
theorem norm_coe {s : Subgroup E} (x : s) : ∥(x : E)∥ = ∥x∥ :=
  rfl
#align subgroup.norm_coe Subgroup.norm_coe

end SeminormedGroup

@[to_additive]
instance seminormedCommGroup [SeminormedCommGroup E] {s : Subgroup E} : SeminormedCommGroup s :=
  SeminormedCommGroup.induced _ _ s.Subtype
#align subgroup.seminormed_comm_group Subgroup.seminormedCommGroup

@[to_additive]
instance normedGroup [NormedGroup E] {s : Subgroup E} : NormedGroup s :=
  NormedGroup.induced _ _ s.Subtype Subtype.coe_injective
#align subgroup.normed_group Subgroup.normedGroup

@[to_additive]
instance normedCommGroup [NormedCommGroup E] {s : Subgroup E} : NormedCommGroup s :=
  NormedCommGroup.induced _ _ s.Subtype Subtype.coe_injective
#align subgroup.normed_comm_group Subgroup.normedCommGroup

end Subgroup

/-! ### Submodules of normed groups -/


namespace Submodule

-- See note [implicit instance arguments]
/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.
-/
instance seminormedAddCommGroup {_ : Ring 𝕜} [SeminormedAddCommGroup E] {_ : Module 𝕜 E} (s : Submodule 𝕜 E) :
    SeminormedAddCommGroup s :=
  SeminormedAddCommGroup.induced _ _ s.Subtype.toAddMonoidHom
#align submodule.seminormed_add_comm_group Submodule.seminormedAddCommGroup

-- See note [implicit instance arguments].
/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `s` is equal to its
norm in `E`. -/
@[simp]
theorem coe_norm {_ : Ring 𝕜} [SeminormedAddCommGroup E] {_ : Module 𝕜 E} {s : Submodule 𝕜 E} (x : s) :
    ∥x∥ = ∥(x : E)∥ :=
  rfl
#align submodule.coe_norm Submodule.coe_norm

-- See note [implicit instance arguments].
/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

This is a reversed version of the `simp` lemma `submodule.coe_norm` for use by `norm_cast`. -/
@[norm_cast]
theorem norm_coe {_ : Ring 𝕜} [SeminormedAddCommGroup E] {_ : Module 𝕜 E} {s : Submodule 𝕜 E} (x : s) :
    ∥(x : E)∥ = ∥x∥ :=
  rfl
#align submodule.norm_coe Submodule.norm_coe

-- See note [implicit instance arguments].
/-- A submodule of a normed group is also a normed group, with the restriction of the norm. -/
instance {_ : Ring 𝕜} [NormedAddCommGroup E] {_ : Module 𝕜 E} (s : Submodule 𝕜 E) : NormedAddCommGroup s :=
  { Submodule.seminormedAddCommGroup s with }

end Submodule

