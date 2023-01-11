/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yaël Dillies

! This file was ported from Lean 3 source module analysis.normed.order.basic
! leanprover-community/mathlib commit a2d2e18906e2b62627646b5d5be856e6a642062f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Group.TypeTags
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Ordered normed spaces

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/


open Filter Set

open TopologicalSpace

variable {α : Type _}

/-- A `normed_ordered_add_group` is an additive group that is both a `normed_add_comm_group` and an
`ordered_add_comm_group`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
class NormedOrderedAddGroup (α : Type _) extends OrderedAddCommGroup α, HasNorm α,
  MetricSpace α where
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by obviously
#align normed_ordered_add_group NormedOrderedAddGroup

/-- A `normed_ordered_group` is a group that is both a `normed_comm_group` and an
`ordered_comm_group`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
@[to_additive]
class NormedOrderedGroup (α : Type _) extends OrderedCommGroup α, HasNorm α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by obviously
#align normed_ordered_group NormedOrderedGroup

/-- A `normed_linear_ordered_add_group` is an additive group that is both a `normed_add_comm_group`
and a `linear_ordered_add_comm_group`. This class is necessary to avoid diamonds caused by both
classes carrying their own group structure. -/
class NormedLinearOrderedAddGroup (α : Type _) extends LinearOrderedAddCommGroup α, HasNorm α,
  MetricSpace α where
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by obviously
#align normed_linear_ordered_add_group NormedLinearOrderedAddGroup

/-- A `normed_linear_ordered_group` is a group that is both a `normed_comm_group` and a
`linear_ordered_comm_group`. This class is necessary to avoid diamonds caused by both classes
carrying their own group structure. -/
@[to_additive]
class NormedLinearOrderedGroup (α : Type _) extends LinearOrderedCommGroup α, HasNorm α,
  MetricSpace α where
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by obviously
#align normed_linear_ordered_group NormedLinearOrderedGroup

/-- A `normed_linear_ordered_field` is a field that is both a `normed_field` and a
    `linear_ordered_field`. This class is necessary to avoid diamonds. -/
class NormedLinearOrderedField (α : Type _) extends LinearOrderedField α, HasNorm α,
  MetricSpace α where
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by obviously
  norm_mul' : ∀ x y : α, ‖x * y‖ = ‖x‖ * ‖y‖
#align normed_linear_ordered_field NormedLinearOrderedField

@[to_additive]
instance (priority := 100) NormedOrderedGroup.toNormedCommGroup [NormedOrderedGroup α] :
    NormedCommGroup α :=
  ⟨NormedOrderedGroup.dist_eq⟩
#align normed_ordered_group.to_normed_comm_group NormedOrderedGroup.toNormedCommGroup

@[to_additive]
instance (priority := 100) NormedLinearOrderedGroup.toNormedOrderedGroup
    [NormedLinearOrderedGroup α] : NormedOrderedGroup α :=
  ⟨NormedLinearOrderedGroup.dist_eq⟩
#align
  normed_linear_ordered_group.to_normed_ordered_group NormedLinearOrderedGroup.toNormedOrderedGroup

instance (priority := 100) NormedLinearOrderedField.toNormedField (α : Type _)
    [NormedLinearOrderedField α] : NormedField α
    where
  dist_eq := NormedLinearOrderedField.dist_eq
  norm_mul' := NormedLinearOrderedField.norm_mul'
#align normed_linear_ordered_field.to_normed_field NormedLinearOrderedField.toNormedField

instance : NormedLinearOrderedField ℚ :=
  ⟨dist_eq_norm, norm_mul⟩

noncomputable instance : NormedLinearOrderedField ℝ :=
  ⟨dist_eq_norm, norm_mul⟩

@[to_additive]
instance [NormedOrderedGroup α] : NormedOrderedGroup αᵒᵈ :=
  { NormedOrderedGroup.toNormedCommGroup, OrderDual.orderedCommGroup with }

@[to_additive]
instance [NormedLinearOrderedGroup α] : NormedLinearOrderedGroup αᵒᵈ :=
  { OrderDual.normedOrderedGroup, OrderDual.linearOrder _ with }

instance [NormedOrderedGroup α] : NormedOrderedAddGroup (Additive α) :=
  { Additive.normedAddCommGroup with }

instance [NormedOrderedAddGroup α] : NormedOrderedGroup (Multiplicative α) :=
  { Multiplicative.normedCommGroup with }

instance [NormedLinearOrderedGroup α] : NormedLinearOrderedAddGroup (Additive α) :=
  { Additive.normedAddCommGroup with }

instance [NormedLinearOrderedAddGroup α] : NormedLinearOrderedGroup (Multiplicative α) :=
  { Multiplicative.normedCommGroup with }

