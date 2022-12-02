/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Order.Lattice

/-!
# `max` and `min`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/728
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic properties about maxima and minima on a `linear_order`.

## Tags

min, max
-/


universe u v

variable {α : Type u} {β : Type v}

attribute [simp] max_eq_left max_eq_right min_eq_left min_eq_right

section

variable [LinearOrder α] [LinearOrder β] {f : α → β} {s : Set α} {a b c d : α}

/- warning: le_min_iff -> le_min_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) c (LinearOrder.min.{u} α _inst_1 a b)) (And (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) c a) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) c b))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.40 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.40)))))) c (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.40) a b)) (And (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.40)))))) c a) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.40)))))) c b))
Case conversion may be inaccurate. Consider using '#align le_min_iff le_min_iffₓ'. -/
-- translate from lattices to linear orders (sup → max, inf → min)
@[simp]
theorem le_min_iff : c ≤ min a b ↔ c ≤ a ∧ c ≤ b :=
  le_inf_iff
#align le_min_iff le_min_iff

/- warning: le_max_iff -> le_max_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a (LinearOrder.max.{u} α _inst_1 b c)) (Or (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.83 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.83)))))) a (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.83) b c)) (Or (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.83)))))) a b) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.83)))))) a c))
Case conversion may be inaccurate. Consider using '#align le_max_iff le_max_iffₓ'. -/
@[simp]
theorem le_max_iff : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
  le_sup_iff
#align le_max_iff le_max_iff

/- warning: min_le_iff -> min_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) c) (Or (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.126 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.126)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.126) a b) c) (Or (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.126)))))) a c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.126)))))) b c))
Case conversion may be inaccurate. Consider using '#align min_le_iff min_le_iffₓ'. -/
@[simp]
theorem min_le_iff : min a b ≤ c ↔ a ≤ c ∨ b ≤ c :=
  inf_le_iff
#align min_le_iff min_le_iff

/- warning: max_le_iff -> max_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.max.{u} α _inst_1 a b) c) (And (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.169 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.169)))))) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.169) a b) c) (And (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.169)))))) a c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.169)))))) b c))
Case conversion may be inaccurate. Consider using '#align max_le_iff max_le_iffₓ'. -/
@[simp]
theorem max_le_iff : max a b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  sup_le_iff
#align max_le_iff max_le_iff

/- warning: lt_min_iff -> lt_min_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a (LinearOrder.min.{u} α _inst_1 b c)) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.212 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.212)))))) a (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.212) b c)) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.212)))))) a b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.212)))))) a c))
Case conversion may be inaccurate. Consider using '#align lt_min_iff lt_min_iffₓ'. -/
@[simp]
theorem lt_min_iff : a < min b c ↔ a < b ∧ a < c :=
  lt_inf_iff
#align lt_min_iff lt_min_iff

/- warning: lt_max_iff -> lt_max_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a (LinearOrder.max.{u} α _inst_1 b c)) (Or (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.255 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.255)))))) a (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.255) b c)) (Or (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.255)))))) a b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.255)))))) a c))
Case conversion may be inaccurate. Consider using '#align lt_max_iff lt_max_iffₓ'. -/
@[simp]
theorem lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
  lt_sup_iff
#align lt_max_iff lt_max_iff

/- warning: min_lt_iff -> min_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) c) (Or (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.298 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.298)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.298) a b) c) (Or (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.298)))))) a c) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.298)))))) b c))
Case conversion may be inaccurate. Consider using '#align min_lt_iff min_lt_iffₓ'. -/
@[simp]
theorem min_lt_iff : min a b < c ↔ a < c ∨ b < c :=
  inf_lt_iff
#align min_lt_iff min_lt_iff

/- warning: max_lt_iff -> max_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.max.{u} α _inst_1 a b) c) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.341 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.341)))))) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.341) a b) c) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.341)))))) a c) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.341)))))) b c))
Case conversion may be inaccurate. Consider using '#align max_lt_iff max_lt_iffₓ'. -/
@[simp]
theorem max_lt_iff : max a b < c ↔ a < c ∧ b < c :=
  sup_lt_iff
#align max_lt_iff max_lt_iff

/- warning: max_le_max -> max_le_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b d) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.max.{u} α _inst_1 a b) (LinearOrder.max.{u} α _inst_1 c d))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.384 : LinearOrder.{u} α] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.384)))))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.384)))))) b d) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.384)))))) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.384) a b) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.384) c d))
Case conversion may be inaccurate. Consider using '#align max_le_max max_le_maxₓ'. -/
theorem max_le_max : a ≤ c → b ≤ d → max a b ≤ max c d :=
  sup_le_sup
#align max_le_max max_le_max

/- warning: min_le_min -> min_le_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b d) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) (LinearOrder.min.{u} α _inst_1 c d))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.425 : LinearOrder.{u} α] {a : α} {b : α} {c : α} {d : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.425)))))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.425)))))) b d) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.425)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.425) a b) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.425) c d))
Case conversion may be inaccurate. Consider using '#align min_le_min min_le_minₓ'. -/
theorem min_le_min : a ≤ c → b ≤ d → min a b ≤ min c d :=
  inf_le_inf
#align min_le_min min_le_min

/- warning: le_max_of_le_left -> le_max_of_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a (LinearOrder.max.{u} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.466 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.466)))))) a b) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.466)))))) a (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.466) b c))
Case conversion may be inaccurate. Consider using '#align le_max_of_le_left le_max_of_le_leftₓ'. -/
theorem le_max_of_le_left : a ≤ b → a ≤ max b c :=
  le_sup_of_le_left
#align le_max_of_le_left le_max_of_le_left

/- warning: le_max_of_le_right -> le_max_of_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a (LinearOrder.max.{u} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.499 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.499)))))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.499)))))) a (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.499) b c))
Case conversion may be inaccurate. Consider using '#align le_max_of_le_right le_max_of_le_rightₓ'. -/
theorem le_max_of_le_right : a ≤ c → a ≤ max b c :=
  le_sup_of_le_right
#align le_max_of_le_right le_max_of_le_right

/- warning: lt_max_of_lt_left -> lt_max_of_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a (LinearOrder.max.{u} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.532 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.532)))))) a b) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.532)))))) a (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.532) b c))
Case conversion may be inaccurate. Consider using '#align lt_max_of_lt_left lt_max_of_lt_leftₓ'. -/
theorem lt_max_of_lt_left (h : a < b) : a < max b c :=
  h.trans_le (le_max_left b c)
#align lt_max_of_lt_left lt_max_of_lt_left

/- warning: lt_max_of_lt_right -> lt_max_of_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a (LinearOrder.max.{u} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.569 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.569)))))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.569)))))) a (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.569) b c))
Case conversion may be inaccurate. Consider using '#align lt_max_of_lt_right lt_max_of_lt_rightₓ'. -/
theorem lt_max_of_lt_right (h : a < c) : a < max b c :=
  h.trans_le (le_max_right b c)
#align lt_max_of_lt_right lt_max_of_lt_right

/- warning: min_le_of_left_le -> min_le_of_left_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.606 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.606)))))) a c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.606)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.606) a b) c)
Case conversion may be inaccurate. Consider using '#align min_le_of_left_le min_le_of_left_leₓ'. -/
theorem min_le_of_left_le : a ≤ c → min a b ≤ c :=
  inf_le_of_left_le
#align min_le_of_left_le min_le_of_left_le

/- warning: min_le_of_right_le -> min_le_of_right_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.639 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.639)))))) b c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.639)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.639) a b) c)
Case conversion may be inaccurate. Consider using '#align min_le_of_right_le min_le_of_right_leₓ'. -/
theorem min_le_of_right_le : b ≤ c → min a b ≤ c :=
  inf_le_of_right_le
#align min_le_of_right_le min_le_of_right_le

/- warning: min_lt_of_left_lt -> min_lt_of_left_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.672 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.672)))))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.672)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.672) a b) c)
Case conversion may be inaccurate. Consider using '#align min_lt_of_left_lt min_lt_of_left_ltₓ'. -/
theorem min_lt_of_left_lt (h : a < c) : min a b < c :=
  (min_le_left a b).trans_lt h
#align min_lt_of_left_lt min_lt_of_left_lt

/- warning: min_lt_of_right_lt -> min_lt_of_right_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.710 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.710)))))) b c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.710)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.710) a b) c)
Case conversion may be inaccurate. Consider using '#align min_lt_of_right_lt min_lt_of_right_ltₓ'. -/
theorem min_lt_of_right_lt (h : b < c) : min a b < c :=
  (min_le_right a b).trans_lt h
#align min_lt_of_right_lt min_lt_of_right_lt

/- warning: max_min_distrib_left -> max_min_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a (LinearOrder.min.{u} α _inst_1 b c)) (LinearOrder.min.{u} α _inst_1 (LinearOrder.max.{u} α _inst_1 a b) (LinearOrder.max.{u} α _inst_1 a c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.748 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.748) a (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.748) b c)) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.748) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.748) a b) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.748) a c))
Case conversion may be inaccurate. Consider using '#align max_min_distrib_left max_min_distrib_leftₓ'. -/
theorem max_min_distrib_left : max a (min b c) = min (max a b) (max a c) :=
  sup_inf_left
#align max_min_distrib_left max_min_distrib_left

/- warning: max_min_distrib_right -> max_min_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 (LinearOrder.min.{u} α _inst_1 a b) c) (LinearOrder.min.{u} α _inst_1 (LinearOrder.max.{u} α _inst_1 a c) (LinearOrder.max.{u} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.789 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.789) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.789) a b) c) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.789) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.789) a c) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.789) b c))
Case conversion may be inaccurate. Consider using '#align max_min_distrib_right max_min_distrib_rightₓ'. -/
theorem max_min_distrib_right : max (min a b) c = min (max a c) (max b c) :=
  sup_inf_right
#align max_min_distrib_right max_min_distrib_right

/- warning: min_max_distrib_left -> min_max_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a (LinearOrder.max.{u} α _inst_1 b c)) (LinearOrder.max.{u} α _inst_1 (LinearOrder.min.{u} α _inst_1 a b) (LinearOrder.min.{u} α _inst_1 a c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.830 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.830) a (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.830) b c)) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.830) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.830) a b) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.830) a c))
Case conversion may be inaccurate. Consider using '#align min_max_distrib_left min_max_distrib_leftₓ'. -/
theorem min_max_distrib_left : min a (max b c) = max (min a b) (min a c) :=
  inf_sup_left
#align min_max_distrib_left min_max_distrib_left

/- warning: min_max_distrib_right -> min_max_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 (LinearOrder.max.{u} α _inst_1 a b) c) (LinearOrder.max.{u} α _inst_1 (LinearOrder.min.{u} α _inst_1 a c) (LinearOrder.min.{u} α _inst_1 b c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.871 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.871) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.871) a b) c) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.871) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.871) a c) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.871) b c))
Case conversion may be inaccurate. Consider using '#align min_max_distrib_right min_max_distrib_rightₓ'. -/
theorem min_max_distrib_right : min (max a b) c = max (min a c) (min b c) :=
  inf_sup_right
#align min_max_distrib_right min_max_distrib_right

/- warning: min_le_max -> min_le_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) (LinearOrder.max.{u} α _inst_1 a b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.912 : LinearOrder.{u} α] {a : α} {b : α}, LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.912)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.912) a b) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.912) a b)
Case conversion may be inaccurate. Consider using '#align min_le_max min_le_maxₓ'. -/
theorem min_le_max : min a b ≤ max a b :=
  le_trans (min_le_left a b) (le_max_left a b)
#align min_le_max min_le_max

/- warning: min_eq_left_iff -> min_eq_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, Iff (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) a) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.951 : LinearOrder.{u} α] {a : α} {b : α}, Iff (Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.951) a b) a) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.951)))))) a b)
Case conversion may be inaccurate. Consider using '#align min_eq_left_iff min_eq_left_iffₓ'. -/
@[simp]
theorem min_eq_left_iff : min a b = a ↔ a ≤ b :=
  inf_eq_left
#align min_eq_left_iff min_eq_left_iff

/- warning: min_eq_right_iff -> min_eq_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, Iff (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) b) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.986 : LinearOrder.{u} α] {a : α} {b : α}, Iff (Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.986) a b) b) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.986)))))) b a)
Case conversion may be inaccurate. Consider using '#align min_eq_right_iff min_eq_right_iffₓ'. -/
@[simp]
theorem min_eq_right_iff : min a b = b ↔ b ≤ a :=
  inf_eq_right
#align min_eq_right_iff min_eq_right_iff

/- warning: max_eq_left_iff -> max_eq_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, Iff (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) a) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1021 : LinearOrder.{u} α] {a : α} {b : α}, Iff (Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1021) a b) a) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1021)))))) b a)
Case conversion may be inaccurate. Consider using '#align max_eq_left_iff max_eq_left_iffₓ'. -/
@[simp]
theorem max_eq_left_iff : max a b = a ↔ b ≤ a :=
  sup_eq_left
#align max_eq_left_iff max_eq_left_iff

/- warning: max_eq_right_iff -> max_eq_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, Iff (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) b) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1056 : LinearOrder.{u} α] {a : α} {b : α}, Iff (Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1056) a b) b) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1056)))))) a b)
Case conversion may be inaccurate. Consider using '#align max_eq_right_iff max_eq_right_iffₓ'. -/
@[simp]
theorem max_eq_right_iff : max a b = b ↔ a ≤ b :=
  sup_eq_right
#align max_eq_right_iff max_eq_right_iff

/- warning: min_cases -> min_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α), Or (And (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) a) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b)) (And (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1091 : LinearOrder.{u} α] (a : α) (b : α), Or (And (Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1091) a b) a) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1091)))))) a b)) (And (Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1091) a b) b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1091)))))) b a))
Case conversion may be inaccurate. Consider using '#align min_cases min_casesₓ'. -/
/-- For elements `a` and `b` of a linear order, either `min a b = a` and `a ≤ b`,
    or `min a b = b` and `b < a`.
    Use cases on this lemma to automate linarith in inequalities -/
theorem min_cases (a b : α) : min a b = a ∧ a ≤ b ∨ min a b = b ∧ b < a := by
  by_cases a ≤ b
  · left
    exact ⟨min_eq_left h, h⟩
  · right
    exact ⟨min_eq_right (le_of_lt (not_le.mp h)), not_le.mp h⟩
#align min_cases min_cases

/- warning: max_cases -> max_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α), Or (And (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) a) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b a)) (And (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1203 : LinearOrder.{u} α] (a : α) (b : α), Or (And (Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1203) a b) a) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1203)))))) b a)) (And (Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1203) a b) b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1203)))))) a b))
Case conversion may be inaccurate. Consider using '#align max_cases max_casesₓ'. -/
/-- For elements `a` and `b` of a linear order, either `max a b = a` and `b ≤ a`,
    or `max a b = b` and `a < b`.
    Use cases on this lemma to automate linarith in inequalities -/
theorem max_cases (a b : α) : max a b = a ∧ b ≤ a ∨ max a b = b ∧ a < b :=
  @min_cases αᵒᵈ _ a b
#align max_cases max_cases

/- warning: min_eq_iff -> min_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) c) (Or (And (Eq.{succ u} α a c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b)) (And (Eq.{succ u} α b c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b a)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1264 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1264) a b) c) (Or (And (Eq.{succ u} α a c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1264)))))) a b)) (And (Eq.{succ u} α b c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1264)))))) b a)))
Case conversion may be inaccurate. Consider using '#align min_eq_iff min_eq_iffₓ'. -/
theorem min_eq_iff : min a b = c ↔ a = c ∧ a ≤ b ∨ b = c ∧ b ≤ a := by
  constructor
  · intro h
    refine' Or.imp (fun h' => _) (fun h' => _) (le_total a b) <;> exact ⟨by simpa [h'] using h, h'⟩
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp [h]
#align min_eq_iff min_eq_iff

/- warning: max_eq_iff -> max_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) c) (Or (And (Eq.{succ u} α a c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b a)) (And (Eq.{succ u} α b c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1448 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1448) a b) c) (Or (And (Eq.{succ u} α a c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1448)))))) b a)) (And (Eq.{succ u} α b c) (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1448)))))) a b)))
Case conversion may be inaccurate. Consider using '#align max_eq_iff max_eq_iffₓ'. -/
theorem max_eq_iff : max a b = c ↔ a = c ∧ b ≤ a ∨ b = c ∧ a ≤ b :=
  @min_eq_iff αᵒᵈ _ a b c
#align max_eq_iff max_eq_iff

/- warning: min_lt_min_left_iff -> min_lt_min_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a c) (LinearOrder.min.{u} α _inst_1 b c)) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1514 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1514)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1514) a c) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1514) b c)) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1514)))))) a b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1514)))))) a c))
Case conversion may be inaccurate. Consider using '#align min_lt_min_left_iff min_lt_min_left_iffₓ'. -/
theorem min_lt_min_left_iff : min a c < min b c ↔ a < b ∧ a < c := by
  simp_rw [lt_min_iff, min_lt_iff, or_iff_left (lt_irrefl _)]
  exact and_congr_left fun h => or_iff_left_of_imp h.trans
#align min_lt_min_left_iff min_lt_min_left_iff

/- warning: min_lt_min_right_iff -> min_lt_min_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) (LinearOrder.min.{u} α _inst_1 a c)) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b c) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b a))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1580 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1580)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1580) a b) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1580) a c)) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1580)))))) b c) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1580)))))) b a))
Case conversion may be inaccurate. Consider using '#align min_lt_min_right_iff min_lt_min_right_iffₓ'. -/
theorem min_lt_min_right_iff : min a b < min a c ↔ b < c ∧ b < a := by
  simp_rw [min_comm a, min_lt_min_left_iff]
#align min_lt_min_right_iff min_lt_min_right_iff

/- warning: max_lt_max_left_iff -> max_lt_max_left_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.max.{u} α _inst_1 a c) (LinearOrder.max.{u} α _inst_1 b c)) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) c b))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1640 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1640)))))) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1640) a c) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1640) b c)) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1640)))))) a b) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1640)))))) c b))
Case conversion may be inaccurate. Consider using '#align max_lt_max_left_iff max_lt_max_left_iffₓ'. -/
theorem max_lt_max_left_iff : max a c < max b c ↔ a < b ∧ c < b :=
  @min_lt_min_left_iff αᵒᵈ _ _ _ _
#align max_lt_max_left_iff max_lt_max_left_iff

/- warning: max_lt_max_right_iff -> max_lt_max_right_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.max.{u} α _inst_1 a b) (LinearOrder.max.{u} α _inst_1 a c)) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b c) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1692 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1692)))))) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1692) a b) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1692) a c)) (And (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1692)))))) b c) (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1692)))))) a c))
Case conversion may be inaccurate. Consider using '#align max_lt_max_right_iff max_lt_max_right_iffₓ'. -/
theorem max_lt_max_right_iff : max a b < max a c ↔ b < c ∧ a < c :=
  @min_lt_min_right_iff αᵒᵈ _ _ _ _
#align max_lt_max_right_iff max_lt_max_right_iff

/- warning: max_idem -> max_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α], IsIdempotent.{u} α (LinearOrder.max.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1744 : LinearOrder.{u} α], IsIdempotent.{u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1744))
Case conversion may be inaccurate. Consider using '#align max_idem max_idemₓ'. -/
/-- An instance asserting that `max a a = a` -/
instance max_idem : IsIdempotent α max := by infer_instance
#align max_idem max_idem

/- warning: min_idem -> min_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α], IsIdempotent.{u} α (LinearOrder.min.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1774 : LinearOrder.{u} α], IsIdempotent.{u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1774))
Case conversion may be inaccurate. Consider using '#align min_idem min_idemₓ'. -/
-- short-circuit type class inference
/-- An instance asserting that `min a a = a` -/
instance min_idem : IsIdempotent α min := by infer_instance
#align min_idem min_idem

/- warning: min_lt_max -> min_lt_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) (LinearOrder.max.{u} α _inst_1 a b)) (Ne.{succ u} α a b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1804 : LinearOrder.{u} α] {a : α} {b : α}, Iff (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1804)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1804) a b) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1804) a b)) (Ne.{succ u} α a b)
Case conversion may be inaccurate. Consider using '#align min_lt_max min_lt_maxₓ'. -/
-- short-circuit type class inference
theorem min_lt_max : min a b < max a b ↔ a ≠ b :=
  inf_lt_sup
#align min_lt_max min_lt_max

/- warning: max_lt_max -> max_lt_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b d) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.max.{u} α _inst_1 a b) (LinearOrder.max.{u} α _inst_1 c d))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1841 : LinearOrder.{u} α] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1841)))))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1841)))))) b d) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1841)))))) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1841) a b) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1841) c d))
Case conversion may be inaccurate. Consider using '#align max_lt_max max_lt_maxₓ'. -/
theorem max_lt_max (h₁ : a < c) (h₂ : b < d) : max a b < max c d := by
  simp [lt_max_iff, max_lt_iff, *]
#align max_lt_max max_lt_max

/- warning: min_lt_min -> min_lt_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b d) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.min.{u} α _inst_1 a b) (LinearOrder.min.{u} α _inst_1 c d))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1888 : LinearOrder.{u} α] {a : α} {b : α} {c : α} {d : α}, (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1888)))))) a c) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1888)))))) b d) -> (LT.lt.{u} α (Preorder.toLT.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.1888)))))) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1888) a b) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1888) c d))
Case conversion may be inaccurate. Consider using '#align min_lt_min min_lt_minₓ'. -/
theorem min_lt_min (h₁ : a < c) (h₂ : b < d) : min a b < min c d :=
  @max_lt_max αᵒᵈ _ _ _ _ _ h₁ h₂
#align min_lt_min min_lt_min

/- warning: min_right_comm -> min_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 (LinearOrder.min.{u} α _inst_1 a b) c) (LinearOrder.min.{u} α _inst_1 (LinearOrder.min.{u} α _inst_1 a c) b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1937 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1937) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1937) a b) c) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1937) (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.1937) a c) b)
Case conversion may be inaccurate. Consider using '#align min_right_comm min_right_commₓ'. -/
theorem min_right_comm (a b c : α) : min (min a b) c = min (min a c) b :=
  right_comm min min_comm min_assoc a b c
#align min_right_comm min_right_comm

/- warning: max.left_comm -> Max.left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a (LinearOrder.max.{u} α _inst_1 b c)) (LinearOrder.max.{u} α _inst_1 b (LinearOrder.max.{u} α _inst_1 a c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.1986 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1986) a (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1986) b c)) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1986) b (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.1986) a c))
Case conversion may be inaccurate. Consider using '#align max.left_comm Max.left_commₓ'. -/
theorem Max.left_comm (a b c : α) : max a (max b c) = max b (max a c) :=
  left_comm max max_comm max_assoc a b c
#align max.left_comm Max.left_comm

/- warning: max.right_comm -> Max.right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 (LinearOrder.max.{u} α _inst_1 a b) c) (LinearOrder.max.{u} α _inst_1 (LinearOrder.max.{u} α _inst_1 a c) b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2036 : LinearOrder.{u} α] (a : α) (b : α) (c : α), Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2036) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2036) a b) c) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2036) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2036) a c) b)
Case conversion may be inaccurate. Consider using '#align max.right_comm Max.right_commₓ'. -/
theorem Max.right_comm (a b c : α) : max (max a b) c = max (max a c) b :=
  right_comm max max_comm max_assoc a b c
#align max.right_comm Max.right_comm

/- warning: monotone_on.map_max -> MonotoneOn.map_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : LinearOrder.{v} β] {f : α -> β} {s : Set.{u} α} {a : α} {b : α}, (MonotoneOn.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (LinearOrder.toLattice.{v} β _inst_2)))) f s) -> (Membership.Mem.{u, u} α (Set.{u} α) (Set.hasMem.{u} α) a s) -> (Membership.Mem.{u, u} α (Set.{u} α) (Set.hasMem.{u} α) b s) -> (Eq.{succ v} β (f (LinearOrder.max.{u} α _inst_1 a b)) (LinearOrder.max.{v} β _inst_2 (f a) (f b)))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.MinMax._hyg.2086 : LinearOrder.{u} α] [inst._@.Mathlib.Order.MinMax._hyg.2089 : LinearOrder.{v} β] {f : α -> β} {s : Set.{u} α} {a : α} {b : α}, (MonotoneOn.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2086))))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (DistribLattice.toLattice.{v} β (instDistribLattice.{v} β inst._@.Mathlib.Order.MinMax._hyg.2089))))) f s) -> (Membership.mem.{u, u} α (Set.{u} α) (Set.instMembershipSet.{u} α) a s) -> (Membership.mem.{u, u} α (Set.{u} α) (Set.instMembershipSet.{u} α) b s) -> (Eq.{succ v} β (f (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2086) a b)) (Max.max.{v} β (LinearOrder.toMax.{v} β inst._@.Mathlib.Order.MinMax._hyg.2089) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align monotone_on.map_max MonotoneOn.map_maxₓ'. -/
theorem MonotoneOn.map_max (hf : MonotoneOn f s) (ha : a ∈ s) (hb : b ∈ s) :
    f (max a b) = max (f a) (f b) := by
  cases le_total a b <;> simp only [max_eq_right, max_eq_left, hf ha hb, hf hb ha, h]
#align monotone_on.map_max MonotoneOn.map_max

/- warning: monotone_on.map_min -> MonotoneOn.map_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : LinearOrder.{v} β] {f : α -> β} {s : Set.{u} α} {a : α} {b : α}, (MonotoneOn.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (LinearOrder.toLattice.{v} β _inst_2)))) f s) -> (Membership.Mem.{u, u} α (Set.{u} α) (Set.hasMem.{u} α) a s) -> (Membership.Mem.{u, u} α (Set.{u} α) (Set.hasMem.{u} α) b s) -> (Eq.{succ v} β (f (LinearOrder.min.{u} α _inst_1 a b)) (LinearOrder.min.{v} β _inst_2 (f a) (f b)))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.MinMax._hyg.2191 : LinearOrder.{u} α] [inst._@.Mathlib.Order.MinMax._hyg.2194 : LinearOrder.{v} β] {f : α -> β} {s : Set.{u} α} {a : α} {b : α}, (MonotoneOn.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2191))))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (DistribLattice.toLattice.{v} β (instDistribLattice.{v} β inst._@.Mathlib.Order.MinMax._hyg.2194))))) f s) -> (Membership.mem.{u, u} α (Set.{u} α) (Set.instMembershipSet.{u} α) a s) -> (Membership.mem.{u, u} α (Set.{u} α) (Set.instMembershipSet.{u} α) b s) -> (Eq.{succ v} β (f (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.2191) a b)) (Min.min.{v} β (LinearOrder.toMin.{v} β inst._@.Mathlib.Order.MinMax._hyg.2194) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align monotone_on.map_min MonotoneOn.map_minₓ'. -/
theorem MonotoneOn.map_min (hf : MonotoneOn f s) (ha : a ∈ s) (hb : b ∈ s) :
    f (min a b) = min (f a) (f b) :=
  hf.dual.map_max ha hb
#align monotone_on.map_min MonotoneOn.map_min

/- warning: antitone_on.map_max -> AntitoneOn.map_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : LinearOrder.{v} β] {f : α -> β} {s : Set.{u} α} {a : α} {b : α}, (AntitoneOn.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (LinearOrder.toLattice.{v} β _inst_2)))) f s) -> (Membership.Mem.{u, u} α (Set.{u} α) (Set.hasMem.{u} α) a s) -> (Membership.Mem.{u, u} α (Set.{u} α) (Set.hasMem.{u} α) b s) -> (Eq.{succ v} β (f (LinearOrder.max.{u} α _inst_1 a b)) (LinearOrder.min.{v} β _inst_2 (f a) (f b)))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.MinMax._hyg.2248 : LinearOrder.{u} α] [inst._@.Mathlib.Order.MinMax._hyg.2251 : LinearOrder.{v} β] {f : α -> β} {s : Set.{u} α} {a : α} {b : α}, (AntitoneOn.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2248))))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (DistribLattice.toLattice.{v} β (instDistribLattice.{v} β inst._@.Mathlib.Order.MinMax._hyg.2251))))) f s) -> (Membership.mem.{u, u} α (Set.{u} α) (Set.instMembershipSet.{u} α) a s) -> (Membership.mem.{u, u} α (Set.{u} α) (Set.instMembershipSet.{u} α) b s) -> (Eq.{succ v} β (f (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2248) a b)) (Min.min.{v} β (LinearOrder.toMin.{v} β inst._@.Mathlib.Order.MinMax._hyg.2251) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align antitone_on.map_max AntitoneOn.map_maxₓ'. -/
theorem AntitoneOn.map_max (hf : AntitoneOn f s) (ha : a ∈ s) (hb : b ∈ s) :
    f (max a b) = min (f a) (f b) :=
  hf.dual_right.map_max ha hb
#align antitone_on.map_max AntitoneOn.map_max

/- warning: antitone_on.map_min -> AntitoneOn.map_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : LinearOrder.{v} β] {f : α -> β} {s : Set.{u} α} {a : α} {b : α}, (AntitoneOn.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (LinearOrder.toLattice.{v} β _inst_2)))) f s) -> (Membership.Mem.{u, u} α (Set.{u} α) (Set.hasMem.{u} α) a s) -> (Membership.Mem.{u, u} α (Set.{u} α) (Set.hasMem.{u} α) b s) -> (Eq.{succ v} β (f (LinearOrder.min.{u} α _inst_1 a b)) (LinearOrder.max.{v} β _inst_2 (f a) (f b)))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.MinMax._hyg.2305 : LinearOrder.{u} α] [inst._@.Mathlib.Order.MinMax._hyg.2308 : LinearOrder.{v} β] {f : α -> β} {s : Set.{u} α} {a : α} {b : α}, (AntitoneOn.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2305))))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (DistribLattice.toLattice.{v} β (instDistribLattice.{v} β inst._@.Mathlib.Order.MinMax._hyg.2308))))) f s) -> (Membership.mem.{u, u} α (Set.{u} α) (Set.instMembershipSet.{u} α) a s) -> (Membership.mem.{u, u} α (Set.{u} α) (Set.instMembershipSet.{u} α) b s) -> (Eq.{succ v} β (f (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.2305) a b)) (Max.max.{v} β (LinearOrder.toMax.{v} β inst._@.Mathlib.Order.MinMax._hyg.2308) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align antitone_on.map_min AntitoneOn.map_minₓ'. -/
theorem AntitoneOn.map_min (hf : AntitoneOn f s) (ha : a ∈ s) (hb : b ∈ s) :
    f (min a b) = max (f a) (f b) :=
  hf.dual.map_max ha hb
#align antitone_on.map_min AntitoneOn.map_min

/- warning: monotone.map_max -> Monotone.map_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : LinearOrder.{v} β] {f : α -> β} {a : α} {b : α}, (Monotone.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (LinearOrder.toLattice.{v} β _inst_2)))) f) -> (Eq.{succ v} β (f (LinearOrder.max.{u} α _inst_1 a b)) (LinearOrder.max.{v} β _inst_2 (f a) (f b)))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.MinMax._hyg.2362 : LinearOrder.{u} α] [inst._@.Mathlib.Order.MinMax._hyg.2365 : LinearOrder.{v} β] {f : α -> β} {a : α} {b : α}, (Monotone.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2362))))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (DistribLattice.toLattice.{v} β (instDistribLattice.{v} β inst._@.Mathlib.Order.MinMax._hyg.2365))))) f) -> (Eq.{succ v} β (f (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2362) a b)) (Max.max.{v} β (LinearOrder.toMax.{v} β inst._@.Mathlib.Order.MinMax._hyg.2365) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align monotone.map_max Monotone.map_maxₓ'. -/
theorem Monotone.map_max (hf : Monotone f) : f (max a b) = max (f a) (f b) := by
  cases le_total a b <;> simp [h, hf h]
#align monotone.map_max Monotone.map_max

/- warning: monotone.map_min -> Monotone.map_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : LinearOrder.{v} β] {f : α -> β} {a : α} {b : α}, (Monotone.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (LinearOrder.toLattice.{v} β _inst_2)))) f) -> (Eq.{succ v} β (f (LinearOrder.min.{u} α _inst_1 a b)) (LinearOrder.min.{v} β _inst_2 (f a) (f b)))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.MinMax._hyg.2448 : LinearOrder.{u} α] [inst._@.Mathlib.Order.MinMax._hyg.2451 : LinearOrder.{v} β] {f : α -> β} {a : α} {b : α}, (Monotone.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2448))))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (DistribLattice.toLattice.{v} β (instDistribLattice.{v} β inst._@.Mathlib.Order.MinMax._hyg.2451))))) f) -> (Eq.{succ v} β (f (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.2448) a b)) (Min.min.{v} β (LinearOrder.toMin.{v} β inst._@.Mathlib.Order.MinMax._hyg.2451) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align monotone.map_min Monotone.map_minₓ'. -/
theorem Monotone.map_min (hf : Monotone f) : f (min a b) = min (f a) (f b) :=
  hf.dual.map_max
#align monotone.map_min Monotone.map_min

/- warning: antitone.map_max -> Antitone.map_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : LinearOrder.{v} β] {f : α -> β} {a : α} {b : α}, (Antitone.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (LinearOrder.toLattice.{v} β _inst_2)))) f) -> (Eq.{succ v} β (f (LinearOrder.max.{u} α _inst_1 a b)) (LinearOrder.min.{v} β _inst_2 (f a) (f b)))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.MinMax._hyg.2492 : LinearOrder.{u} α] [inst._@.Mathlib.Order.MinMax._hyg.2495 : LinearOrder.{v} β] {f : α -> β} {a : α} {b : α}, (Antitone.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2492))))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (DistribLattice.toLattice.{v} β (instDistribLattice.{v} β inst._@.Mathlib.Order.MinMax._hyg.2495))))) f) -> (Eq.{succ v} β (f (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2492) a b)) (Min.min.{v} β (LinearOrder.toMin.{v} β inst._@.Mathlib.Order.MinMax._hyg.2495) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align antitone.map_max Antitone.map_maxₓ'. -/
theorem Antitone.map_max (hf : Antitone f) : f (max a b) = min (f a) (f b) := by
  cases le_total a b <;> simp [h, hf h]
#align antitone.map_max Antitone.map_max

/- warning: antitone.map_min -> Antitone.map_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{v}} [_inst_1 : LinearOrder.{u} α] [_inst_2 : LinearOrder.{v} β] {f : α -> β} {a : α} {b : α}, (Antitone.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1)))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (LinearOrder.toLattice.{v} β _inst_2)))) f) -> (Eq.{succ v} β (f (LinearOrder.min.{u} α _inst_1 a b)) (LinearOrder.max.{v} β _inst_2 (f a) (f b)))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{v}} [inst._@.Mathlib.Order.MinMax._hyg.2578 : LinearOrder.{u} α] [inst._@.Mathlib.Order.MinMax._hyg.2581 : LinearOrder.{v} β] {f : α -> β} {a : α} {b : α}, (Antitone.{u, v} α β (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2578))))) (PartialOrder.toPreorder.{v} β (SemilatticeInf.toPartialOrder.{v} β (Lattice.toSemilatticeInf.{v} β (DistribLattice.toLattice.{v} β (instDistribLattice.{v} β inst._@.Mathlib.Order.MinMax._hyg.2581))))) f) -> (Eq.{succ v} β (f (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.2578) a b)) (Max.max.{v} β (LinearOrder.toMax.{v} β inst._@.Mathlib.Order.MinMax._hyg.2581) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align antitone.map_min Antitone.map_minₓ'. -/
theorem Antitone.map_min (hf : Antitone f) : f (min a b) = max (f a) (f b) :=
  hf.dual.map_max
#align antitone.map_min Antitone.map_min

/- warning: min_choice -> min_choice is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α), Or (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) a) (Eq.{succ u} α (LinearOrder.min.{u} α _inst_1 a b) b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2619 : LinearOrder.{u} α] (a : α) (b : α), Or (Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.2619) a b) a) (Eq.{succ u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.2619) a b) b)
Case conversion may be inaccurate. Consider using '#align min_choice min_choiceₓ'. -/
theorem min_choice (a b : α) : min a b = a ∨ min a b = b := by cases le_total a b <;> simp [*]
#align min_choice min_choice

/- warning: max_choice -> max_choice is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] (a : α) (b : α), Or (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) a) (Eq.{succ u} α (LinearOrder.max.{u} α _inst_1 a b) b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2683 : LinearOrder.{u} α] (a : α) (b : α), Or (Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2683) a b) a) (Eq.{succ u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2683) a b) b)
Case conversion may be inaccurate. Consider using '#align max_choice max_choiceₓ'. -/
theorem max_choice (a b : α) : max a b = a ∨ max a b = b :=
  @min_choice αᵒᵈ _ a b
#align max_choice max_choice

/- warning: le_of_max_le_left -> le_of_max_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.max.{u} α _inst_1 a b) c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) a c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2728 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2728)))))) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2728) a b) c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2728)))))) a c)
Case conversion may be inaccurate. Consider using '#align le_of_max_le_left le_of_max_le_leftₓ'. -/
theorem le_of_max_le_left {a b c : α} (h : max a b ≤ c) : a ≤ c :=
  le_trans (le_max_left _ _) h
#align le_of_max_le_left le_of_max_le_left

/- warning: le_of_max_le_right -> le_of_max_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) (LinearOrder.max.{u} α _inst_1 a b) c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (LinearOrder.toLattice.{u} α _inst_1))))) b c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2769 : LinearOrder.{u} α] {a : α} {b : α} {c : α}, (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2769)))))) (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2769) a b) c) -> (LE.le.{u} α (Preorder.toLE.{u} α (PartialOrder.toPreorder.{u} α (SemilatticeInf.toPartialOrder.{u} α (Lattice.toSemilatticeInf.{u} α (DistribLattice.toLattice.{u} α (instDistribLattice.{u} α inst._@.Mathlib.Order.MinMax._hyg.2769)))))) b c)
Case conversion may be inaccurate. Consider using '#align le_of_max_le_right le_of_max_le_rightₓ'. -/
theorem le_of_max_le_right {a b c : α} (h : max a b ≤ c) : b ≤ c :=
  le_trans (le_max_right _ _) h
#align le_of_max_le_right le_of_max_le_right

/- warning: max_commutative -> max_commutative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α], Commutative.{u} α (LinearOrder.max.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2810 : LinearOrder.{u} α], Commutative.{u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2810))
Case conversion may be inaccurate. Consider using '#align max_commutative max_commutativeₓ'. -/
theorem max_commutative : Commutative (max : α → α → α) :=
  max_comm
#align max_commutative max_commutative

/- warning: max_associative -> max_associative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α], Associative.{u} α (LinearOrder.max.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2839 : LinearOrder.{u} α], Associative.{u} α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2839))
Case conversion may be inaccurate. Consider using '#align max_associative max_associativeₓ'. -/
theorem max_associative : Associative (max : α → α → α) :=
  max_assoc
#align max_associative max_associative

/- warning: max_left_commutative -> max_left_commutative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α], LeftCommutative.{u, u} α α (LinearOrder.max.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2868 : LinearOrder.{u} α], LeftCommutative.{u, u} α α (Max.max.{u} α (LinearOrder.toMax.{u} α inst._@.Mathlib.Order.MinMax._hyg.2868))
Case conversion may be inaccurate. Consider using '#align max_left_commutative max_left_commutativeₓ'. -/
theorem max_left_commutative : LeftCommutative (max : α → α → α) :=
  max_left_comm
#align max_left_commutative max_left_commutative

/- warning: min_commutative -> min_commutative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α], Commutative.{u} α (LinearOrder.min.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2897 : LinearOrder.{u} α], Commutative.{u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.2897))
Case conversion may be inaccurate. Consider using '#align min_commutative min_commutativeₓ'. -/
theorem min_commutative : Commutative (min : α → α → α) :=
  min_comm
#align min_commutative min_commutative

/- warning: min_associative -> min_associative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α], Associative.{u} α (LinearOrder.min.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2926 : LinearOrder.{u} α], Associative.{u} α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.2926))
Case conversion may be inaccurate. Consider using '#align min_associative min_associativeₓ'. -/
theorem min_associative : Associative (min : α → α → α) :=
  min_assoc
#align min_associative min_associative

/- warning: min_left_commutative -> min_left_commutative is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : LinearOrder.{u} α], LeftCommutative.{u, u} α α (LinearOrder.min.{u} α _inst_1)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Order.MinMax._hyg.2955 : LinearOrder.{u} α], LeftCommutative.{u, u} α α (Min.min.{u} α (LinearOrder.toMin.{u} α inst._@.Mathlib.Order.MinMax._hyg.2955))
Case conversion may be inaccurate. Consider using '#align min_left_commutative min_left_commutativeₓ'. -/
theorem min_left_commutative : LeftCommutative (min : α → α → α) :=
  min_left_comm
#align min_left_commutative min_left_commutative

end

