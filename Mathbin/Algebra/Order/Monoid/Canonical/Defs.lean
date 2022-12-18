/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.canonical.defs
! leanprover-community/mathlib commit c5c7e2760814660967bc27f0de95d190a22297f3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.BoundedOrder
import Mathbin.Order.MinMax
import Mathbin.Algebra.NeZero
import Mathbin.Algebra.Order.Monoid.Defs

/-!
# Canonically ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/778
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u

variable {α : Type u}

#print ExistsMulOfLE /-
/-- An `ordered_comm_monoid` with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_monoid`. -/
class ExistsMulOfLE (α : Type u) [Mul α] [LE α] : Prop where
  exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a * c
#align has_exists_mul_of_le ExistsMulOfLE
-/

#print ExistsAddOfLE /-
/-- An `ordered_add_comm_monoid` with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_add_monoid`. -/
class ExistsAddOfLE (α : Type u) [Add α] [LE α] : Prop where
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c : α, b = a + c
#align has_exists_add_of_le ExistsAddOfLE
-/

attribute [to_additive] ExistsMulOfLE

export ExistsMulOfLE (exists_mul_of_le)

export ExistsAddOfLE (exists_add_of_le)

/- warning: group.has_exists_mul_of_le -> Group.existsMulOfLE is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α], ExistsMulOfLE.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) _inst_2
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Group.{u1} α] [_inst_2 : LE.{u1} α], ExistsMulOfLE.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) _inst_2
Case conversion may be inaccurate. Consider using '#align group.has_exists_mul_of_le Group.existsMulOfLEₓ'. -/
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.existsMulOfLE (α : Type u) [Group α] [LE α] : ExistsMulOfLE α :=
  ⟨fun a b hab => ⟨a⁻¹ * b, (mul_inv_cancel_left _ _).symm⟩⟩
#align group.has_exists_mul_of_le Group.existsMulOfLE

section MulOneClass

variable [MulOneClass α] [Preorder α] [ContravariantClass α α (· * ·) (· < ·)] [ExistsMulOfLE α]
  {a b : α}

/- warning: exists_one_lt_mul_of_lt' -> exists_one_lt_mul_of_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2))] [_inst_4 : ExistsMulOfLE.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1) (Preorder.toLE.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (Exists.{succ u1} α (fun (c : α) => And (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) c) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1)) a c) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] [_inst_2 : Preorder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.195 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.197 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.195 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.197) (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.210 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.212 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.210 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.212)] [_inst_4 : ExistsMulOfLE.{u1} α (MulOneClass.toMul.{u1} α _inst_1) (Preorder.toLE.{u1} α _inst_2)] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) a b) -> (Exists.{succ u1} α (fun (c : α) => And (LT.lt.{u1} α (Preorder.toLT.{u1} α _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) c) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α _inst_1)) a c) b)))
Case conversion may be inaccurate. Consider using '#align exists_one_lt_mul_of_lt' exists_one_lt_mul_of_lt'ₓ'. -/
@[to_additive]
theorem exists_one_lt_mul_of_lt' (h : a < b) : ∃ c, 1 < c ∧ a * c = b := by
  obtain ⟨c, rfl⟩ := exists_mul_of_le h.le
  exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩
#align exists_one_lt_mul_of_lt' exists_one_lt_mul_of_lt'

end MulOneClass

section ExistsMulOfLE

variable [LinearOrder α] [DenselyOrdered α] [Monoid α] [ExistsMulOfLE α]
  [CovariantClass α α (· * ·) (· < ·)] [ContravariantClass α α (· * ·) (· < ·)] {a b : α}

/- warning: le_of_forall_one_lt_le_mul -> le_of_forall_one_lt_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_3 : Monoid.{u1} α] [_inst_4 : ExistsMulOfLE.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_5 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] [_inst_6 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] {a : α} {b : α}, (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))))) ε) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) b ε))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_3 : Monoid.{u1} α] [_inst_4 : ExistsMulOfLE.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.386 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.388 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.386 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.388) (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.401 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.403 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.401 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.403)] [_inst_6 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.420 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.422 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.420 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.422) (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.435 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.437 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.435 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.437)] {a : α} {b : α}, (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_3))) ε) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) b ε))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align le_of_forall_one_lt_le_mul le_of_forall_one_lt_le_mulₓ'. -/
@[to_additive]
theorem le_of_forall_one_lt_le_mul (h : ∀ ε : α, 1 < ε → a ≤ b * ε) : a ≤ b :=
  le_of_forall_le_of_dense fun x hxb => by
    obtain ⟨ε, rfl⟩ := exists_mul_of_le hxb.le
    exact h _ ((lt_mul_iff_one_lt_right' b).1 hxb)
#align le_of_forall_one_lt_le_mul le_of_forall_one_lt_le_mul

/- warning: le_of_forall_one_lt_lt_mul' -> le_of_forall_one_lt_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_3 : Monoid.{u1} α] [_inst_4 : ExistsMulOfLE.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_5 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] [_inst_6 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] {a : α} {b : α}, (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) b ε))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_3 : Monoid.{u1} α] [_inst_4 : ExistsMulOfLE.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.518 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.520 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.518 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.520) (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.533 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.535 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.533 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.535)] [_inst_6 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.552 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.554 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.552 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.554) (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.567 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.569 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.567 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.569)] {a : α} {b : α}, (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_3))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) b ε))) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align le_of_forall_one_lt_lt_mul' le_of_forall_one_lt_lt_mul'ₓ'. -/
@[to_additive]
theorem le_of_forall_one_lt_lt_mul' (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b :=
  le_of_forall_one_lt_le_mul fun ε hε => (h _ hε).le
#align le_of_forall_one_lt_lt_mul' le_of_forall_one_lt_lt_mul'

/- warning: le_iff_forall_one_lt_lt_mul' -> le_iff_forall_one_lt_lt_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_3 : Monoid.{u1} α] [_inst_4 : ExistsMulOfLE.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] [_inst_5 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] [_inst_6 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))))] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a b) (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) b ε)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : DenselyOrdered.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_3 : Monoid.{u1} α] [_inst_4 : ExistsMulOfLE.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] [_inst_5 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.637 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.639 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.637 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.639) (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.652 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.654 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.652 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.654)] [_inst_6 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.671 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.673 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.671 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.673) (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.686 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.688 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.686 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.688)] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a b) (forall (ε : α), (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_3))) ε) -> (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) b ε)))
Case conversion may be inaccurate. Consider using '#align le_iff_forall_one_lt_lt_mul' le_iff_forall_one_lt_lt_mul'ₓ'. -/
@[to_additive]
theorem le_iff_forall_one_lt_lt_mul' : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε :=
  ⟨fun h ε => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul'⟩
#align le_iff_forall_one_lt_lt_mul' le_iff_forall_one_lt_lt_mul'

end ExistsMulOfLE

#print CanonicallyOrderedAddMonoid /-
/-- A canonically ordered additive monoid is an ordered commutative additive monoid
  in which the ordering coincides with the subtractibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other nontrivial `ordered_add_comm_group`s. -/
@[protect_proj]
class CanonicallyOrderedAddMonoid (α : Type _) extends OrderedAddCommMonoid α, Bot α where
  bot_le : ∀ x : α, ⊥ ≤ x
  exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ c, b = a + c
  le_self_add : ∀ a b : α, a ≤ a + b
#align canonically_ordered_add_monoid CanonicallyOrderedAddMonoid
-/

#print CanonicallyOrderedAddMonoid.toOrderBot /-
-- see Note [lower instance priority]
instance (priority := 100) CanonicallyOrderedAddMonoid.toOrderBot (α : Type u)
    [h : CanonicallyOrderedAddMonoid α] : OrderBot α :=
  { h with }
#align canonically_ordered_add_monoid.to_order_bot CanonicallyOrderedAddMonoid.toOrderBot
-/

#print CanonicallyOrderedMonoid /-
/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Examples seem rare; it seems more likely that the `order_dual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1).
-/
@[protect_proj, to_additive]
class CanonicallyOrderedMonoid (α : Type _) extends OrderedCommMonoid α, Bot α where
  bot_le : ∀ x : α, ⊥ ≤ x
  exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ c, b = a * c
  le_self_mul : ∀ a b : α, a ≤ a * b
#align canonically_ordered_monoid CanonicallyOrderedMonoid
-/

#print CanonicallyOrderedMonoid.toOrderBot /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CanonicallyOrderedMonoid.toOrderBot (α : Type u)
    [h : CanonicallyOrderedMonoid α] : OrderBot α :=
  { h with }
#align canonically_ordered_monoid.to_order_bot CanonicallyOrderedMonoid.toOrderBot
-/

/- warning: canonically_ordered_monoid.has_exists_mul_of_le -> CanonicallyOrderedMonoid.existsMulOfLE is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [h : CanonicallyOrderedMonoid.{u1} α], ExistsMulOfLE.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α h))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α h))))
but is expected to have type
  forall (α : Type.{u1}) [h : CanonicallyOrderedMonoid.{u1} α], ExistsMulOfLE.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α h))))) (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α h))))
Case conversion may be inaccurate. Consider using '#align canonically_ordered_monoid.has_exists_mul_of_le CanonicallyOrderedMonoid.existsMulOfLEₓ'. -/
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CanonicallyOrderedMonoid.existsMulOfLE (α : Type u)
    [h : CanonicallyOrderedMonoid α] : ExistsMulOfLE α :=
  { h with }
#align canonically_ordered_monoid.has_exists_mul_of_le CanonicallyOrderedMonoid.existsMulOfLE

section CanonicallyOrderedMonoid

variable [CanonicallyOrderedMonoid α] {a b c d : α}

/- warning: le_self_mul -> le_self_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {c : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {c : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a c)
Case conversion may be inaccurate. Consider using '#align le_self_mul le_self_mulₓ'. -/
@[to_additive]
theorem le_self_mul : a ≤ a * c :=
  CanonicallyOrderedMonoid.le_self_mul _ _
#align le_self_mul le_self_mul

/- warning: le_mul_self -> le_mul_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) b a)
Case conversion may be inaccurate. Consider using '#align le_mul_self le_mul_selfₓ'. -/
@[to_additive]
theorem le_mul_self : a ≤ b * a := by 
  rw [mul_comm]
  exact le_self_mul
#align le_mul_self le_mul_self

/- warning: self_le_mul_right -> self_le_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a b)
Case conversion may be inaccurate. Consider using '#align self_le_mul_right self_le_mul_rightₓ'. -/
@[to_additive]
theorem self_le_mul_right (a b : α) : a ≤ a * b :=
  le_self_mul
#align self_le_mul_right self_le_mul_right

/- warning: self_le_mul_left -> self_le_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) b a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) b a)
Case conversion may be inaccurate. Consider using '#align self_le_mul_left self_le_mul_leftₓ'. -/
@[to_additive]
theorem self_le_mul_left (a b : α) : a ≤ b * a :=
  le_mul_self
#align self_le_mul_left self_le_mul_left

/- warning: le_of_mul_le_left -> le_of_mul_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_left le_of_mul_le_leftₓ'. -/
@[to_additive]
theorem le_of_mul_le_left : a * b ≤ c → a ≤ c :=
  le_self_mul.trans
#align le_of_mul_le_left le_of_mul_le_left

/- warning: le_of_mul_le_right -> le_of_mul_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) b c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a b) c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) b c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_right le_of_mul_le_rightₓ'. -/
@[to_additive]
theorem le_of_mul_le_right : a * b ≤ c → b ≤ c :=
  le_mul_self.trans
#align le_of_mul_le_right le_of_mul_le_right

/- warning: le_iff_exists_mul -> le_iff_exists_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a b) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a c)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a b) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a c)))
Case conversion may be inaccurate. Consider using '#align le_iff_exists_mul le_iff_exists_mulₓ'. -/
@[to_additive]
theorem le_iff_exists_mul : a ≤ b ↔ ∃ c, b = a * c :=
  ⟨exists_mul_of_le, by 
    rintro ⟨c, rfl⟩
    exact le_self_mul⟩
#align le_iff_exists_mul le_iff_exists_mul

/- warning: le_iff_exists_mul' -> le_iff_exists_mul' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a b) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) c a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a b) (Exists.{succ u1} α (fun (c : α) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) c a)))
Case conversion may be inaccurate. Consider using '#align le_iff_exists_mul' le_iff_exists_mul'ₓ'. -/
@[to_additive]
theorem le_iff_exists_mul' : a ≤ b ↔ ∃ c, b = c * a := by
  simpa only [mul_comm _ a] using le_iff_exists_mul
#align le_iff_exists_mul' le_iff_exists_mul'

/- warning: one_le -> one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a
Case conversion may be inaccurate. Consider using '#align one_le one_leₓ'. -/
@[simp, to_additive zero_le]
theorem one_le (a : α) : 1 ≤ a :=
  le_iff_exists_mul.mpr ⟨a, (one_mul _).symm⟩
#align one_le one_le

/- warning: bot_eq_one -> bot_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α], Eq.{succ u1} α (Bot.bot.{u1} α (CanonicallyOrderedMonoid.toHasBot.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α], Eq.{succ u1} α (Bot.bot.{u1} α (CanonicallyOrderedMonoid.toBot.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align bot_eq_one bot_eq_oneₓ'. -/
@[to_additive]
theorem bot_eq_one : (⊥ : α) = 1 :=
  le_antisymm bot_le (one_le ⊥)
#align bot_eq_one bot_eq_one

/- warning: mul_eq_one_iff -> mul_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))) (And (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, Iff (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))) (And (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))) (Eq.{succ u1} α b (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align mul_eq_one_iff mul_eq_one_iffₓ'. -/
@[simp, to_additive]
theorem mul_eq_one_iff : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  mul_eq_one_iff' (one_le _) (one_le _)
#align mul_eq_one_iff mul_eq_one_iff

/- warning: le_one_iff_eq_one -> le_one_iff_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align le_one_iff_eq_one le_one_iff_eq_oneₓ'. -/
@[simp, to_additive]
theorem le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
  (one_le a).le_iff_eq
#align le_one_iff_eq_one le_one_iff_eq_one

/- warning: one_lt_iff_ne_one -> one_lt_iff_ne_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))) a) (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a) (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align one_lt_iff_ne_one one_lt_iff_ne_oneₓ'. -/
@[to_additive]
theorem one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
  (one_le a).lt_iff_ne.trans ne_comm
#align one_lt_iff_ne_one one_lt_iff_ne_one

/- warning: eq_one_or_one_lt -> eq_one_or_one_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α}, Or (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α}, Or (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a)
Case conversion may be inaccurate. Consider using '#align eq_one_or_one_lt eq_one_or_one_ltₓ'. -/
@[to_additive]
theorem eq_one_or_one_lt : a = 1 ∨ 1 < a :=
  (one_le a).eq_or_lt.imp_left Eq.symm
#align eq_one_or_one_lt eq_one_or_one_lt

/- warning: one_lt_mul_iff -> one_lt_mul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a b)) (Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))) a) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a b)) (Or (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) b))
Case conversion may be inaccurate. Consider using '#align one_lt_mul_iff one_lt_mul_iffₓ'. -/
@[simp, to_additive add_pos_iff]
theorem one_lt_mul_iff : 1 < a * b ↔ 1 < a ∨ 1 < b := by
  simp only [one_lt_iff_ne_one, Ne.def, mul_eq_one_iff, not_and_or]
#align one_lt_mul_iff one_lt_mul_iff

/- warning: exists_one_lt_mul_of_lt -> exists_one_lt_mul_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a b) -> (Exists.{succ u1} α (fun (c : α) => Exists.{0} (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))) c) (fun (hc : LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))))) c) => Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a c) b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a b) -> (Exists.{succ u1} α (fun (c : α) => Exists.{0} (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) c) (fun (hc : LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) c) => Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a c) b)))
Case conversion may be inaccurate. Consider using '#align exists_one_lt_mul_of_lt exists_one_lt_mul_of_ltₓ'. -/
@[to_additive]
theorem exists_one_lt_mul_of_lt (h : a < b) : ∃ (c : _)(hc : 1 < c), a * c = b := by
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le
  refine' ⟨c, one_lt_iff_ne_one.2 _, hc.symm⟩
  rintro rfl
  simpa [hc, lt_irrefl] using h
#align exists_one_lt_mul_of_lt exists_one_lt_mul_of_lt

/- warning: le_mul_left -> le_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a c) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align le_mul_left le_mul_leftₓ'. -/
@[to_additive]
theorem le_mul_left (h : a ≤ c) : a ≤ b * c :=
  calc
    a = 1 * a := by simp
    _ ≤ b * c := mul_le_mul' (one_le _) h
    
#align le_mul_left le_mul_left

/- warning: le_mul_right -> le_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α} {c : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a b) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align le_mul_right le_mul_rightₓ'. -/
@[to_additive]
theorem le_mul_right (h : a ≤ b) : a ≤ b * c :=
  calc
    a = a * 1 := by simp
    _ ≤ b * c := mul_le_mul' h (one_le _)
    
#align le_mul_right le_mul_right

/- warning: lt_iff_exists_mul -> lt_iff_exists_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α} [_inst_2 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a b) (Exists.{succ u1} α (fun (c : α) => Exists.{0} (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) c (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))) (fun (H : GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) c (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))) => Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a c))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {a : α} {b : α} [_inst_2 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.1567 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.1569 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.1567 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.1569) (fun (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.1582 : α) (x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.1584 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.1582 x._@.Mathlib.Algebra.Order.Monoid.Canonical.Defs._hyg.1584)], Iff (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) a b) (Exists.{succ u1} α (fun (c : α) => And (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))) c (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))) (Eq.{succ u1} α b (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) a c))))
Case conversion may be inaccurate. Consider using '#align lt_iff_exists_mul lt_iff_exists_mulₓ'. -/
@[to_additive]
theorem lt_iff_exists_mul [CovariantClass α α (· * ·) (· < ·)] : a < b ↔ ∃ c > 1, b = a * c := by
  simp_rw [lt_iff_le_and_ne, and_comm', le_iff_exists_mul, ← exists_and_left, exists_prop]
  apply exists_congr; intro c
  rw [and_congr_left_iff, gt_iff_lt]; rintro rfl
  constructor
  · rw [one_lt_iff_ne_one]
    apply mt
    rintro rfl
    rw [mul_one]
  · rw [← (self_le_mul_right a c).lt_iff_ne]
    apply lt_mul_of_one_lt_right'
#align lt_iff_exists_mul lt_iff_exists_mul

end CanonicallyOrderedMonoid

/- warning: pos_of_gt -> pos_of_gt is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} M] {n : M} {m : M}, (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) n m) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))))))) m)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} M] {n : M} {m : M}, (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) n m) -> (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))))) m)
Case conversion may be inaccurate. Consider using '#align pos_of_gt pos_of_gtₓ'. -/
theorem pos_of_gt {M : Type _} [CanonicallyOrderedAddMonoid M] {n m : M} (h : n < m) : 0 < m :=
  lt_of_le_of_lt (zero_le _) h
#align pos_of_gt pos_of_gt

namespace NeZero

/- warning: ne_zero.pos -> NeZero.pos is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} (a : M) [_inst_1 : CanonicallyOrderedAddMonoid.{u1} M] [_inst_2 : NeZero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1))))) a], LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))))))) a
but is expected to have type
  forall {M : Type.{u1}} (a : M) [_inst_1 : CanonicallyOrderedAddMonoid.{u1} M] [_inst_2 : NeZero.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) a], LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))))) a
Case conversion may be inaccurate. Consider using '#align ne_zero.pos NeZero.posₓ'. -/
theorem pos {M} (a : M) [CanonicallyOrderedAddMonoid M] [NeZero a] : 0 < a :=
  (zero_le a).lt_of_ne <| NeZero.out.symm
#align ne_zero.pos NeZero.pos

/- warning: ne_zero.of_gt -> NeZero.of_gt is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} M] {x : M} {y : M}, (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) x y) -> (NeZero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1))))) y)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} M] {x : M} {y : M}, (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) x y) -> (NeZero.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) y)
Case conversion may be inaccurate. Consider using '#align ne_zero.of_gt NeZero.of_gtₓ'. -/
theorem of_gt {M} [CanonicallyOrderedAddMonoid M] {x y : M} (h : x < y) : NeZero y :=
  of_pos <| pos_of_gt h
#align ne_zero.of_gt NeZero.of_gt

/- warning: ne_zero.of_gt' -> NeZero.of_gt' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} M] [_inst_2 : One.{u1} M] {y : M} [_inst_3 : Fact (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M _inst_2))) y)], NeZero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1))))) y
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} M] [_inst_2 : One.{u1} M] {y : M} [_inst_3 : Fact (LT.lt.{u1} M (Preorder.toLT.{u1} M (PartialOrder.toPreorder.{u1} M (OrderedAddCommMonoid.toPartialOrder.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M _inst_2)) y)], NeZero.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) y
Case conversion may be inaccurate. Consider using '#align ne_zero.of_gt' NeZero.of_gt'ₓ'. -/
-- 1 < p is still an often-used `fact`, due to `nat.prime` implying it, and it implying `nontrivial`
-- on `zmod`'s ring structure. We cannot just set this to be any `x < y`, else that becomes a
-- metavariable and it will hugely slow down typeclass inference.
instance (priority := 10) of_gt' {M} [CanonicallyOrderedAddMonoid M] [One M] {y : M}
    [Fact (1 < y)] : NeZero y :=
  of_gt <| Fact.out <| 1 < y
#align ne_zero.of_gt' NeZero.of_gt'

/- warning: ne_zero.bit0 -> NeZero.bit0 is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} M] {x : M} [_inst_2 : NeZero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1))))) x], NeZero.{u1} M (AddZeroClass.toHasZero.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1))))) (bit0.{u1} M (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1))))) x)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedAddMonoid.{u1} M] {x : M} [_inst_2 : NeZero.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) x], NeZero.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1)))) (bit0.{u1} M (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M (OrderedAddCommMonoid.toAddCommMonoid.{u1} M (CanonicallyOrderedAddMonoid.toOrderedAddCommMonoid.{u1} M _inst_1))))) x)
Case conversion may be inaccurate. Consider using '#align ne_zero.bit0 NeZero.bit0ₓ'. -/
instance bit0 {M} [CanonicallyOrderedAddMonoid M] {x : M} [NeZero x] : NeZero (bit0 x) :=
  of_pos <| bit0_pos <| NeZero.pos x
#align ne_zero.bit0 NeZero.bit0

end NeZero

#print CanonicallyLinearOrderedAddMonoid /-
/-- A canonically linear-ordered additive monoid is a canonically ordered additive monoid
    whose ordering is a linear order. -/
@[protect_proj]
class CanonicallyLinearOrderedAddMonoid (α : Type _) extends CanonicallyOrderedAddMonoid α,
  LinearOrder α
#align canonically_linear_ordered_add_monoid CanonicallyLinearOrderedAddMonoid
-/

#print CanonicallyLinearOrderedMonoid /-
/-- A canonically linear-ordered monoid is a canonically ordered monoid
    whose ordering is a linear order. -/
@[protect_proj, to_additive]
class CanonicallyLinearOrderedMonoid (α : Type _) extends CanonicallyOrderedMonoid α, LinearOrder α
#align canonically_linear_ordered_monoid CanonicallyLinearOrderedMonoid
-/

section CanonicallyLinearOrderedMonoid

variable [CanonicallyLinearOrderedMonoid α]

#print CanonicallyLinearOrderedMonoid.semilatticeSup /-
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CanonicallyLinearOrderedMonoid.semilatticeSup : SemilatticeSup α :=
  { LinearOrder.toLattice with }
#align
  canonically_linear_ordered_monoid.semilattice_sup CanonicallyLinearOrderedMonoid.semilatticeSup
-/

/- warning: min_mul_distrib -> min_mul_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.min.{u1} α (CanonicallyLinearOrderedMonoid.toLinearOrder.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))))))) b c)) (LinearOrder.min.{u1} α (CanonicallyLinearOrderedMonoid.toLinearOrder.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))))))) (LinearOrder.min.{u1} α (CanonicallyLinearOrderedMonoid.toLinearOrder.{u1} α _inst_1) a b) (LinearOrder.min.{u1} α (CanonicallyLinearOrderedMonoid.toLinearOrder.{u1} α _inst_1) a c)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (Min.min.{u1} α (CanonicallyLinearOrderedMonoid.toMin.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))))))) b c)) (Min.min.{u1} α (CanonicallyLinearOrderedMonoid.toMin.{u1} α _inst_1) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))))))) (Min.min.{u1} α (CanonicallyLinearOrderedMonoid.toMin.{u1} α _inst_1) a b) (Min.min.{u1} α (CanonicallyLinearOrderedMonoid.toMin.{u1} α _inst_1) a c)))
Case conversion may be inaccurate. Consider using '#align min_mul_distrib min_mul_distribₓ'. -/
@[to_additive]
theorem min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c) := by
  cases' le_total a b with hb hb
  · simp [hb, le_mul_right]
  · cases' le_total a c with hc hc
    · simp [hc, le_mul_left]
    · simp [hb, hc]
#align min_mul_distrib min_mul_distrib

/- warning: min_mul_distrib' -> min_mul_distrib' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (LinearOrder.min.{u1} α (CanonicallyLinearOrderedMonoid.toLinearOrder.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))))))) a b) c) (LinearOrder.min.{u1} α (CanonicallyLinearOrderedMonoid.toLinearOrder.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))))))) (LinearOrder.min.{u1} α (CanonicallyLinearOrderedMonoid.toLinearOrder.{u1} α _inst_1) a c) (LinearOrder.min.{u1} α (CanonicallyLinearOrderedMonoid.toLinearOrder.{u1} α _inst_1) b c)) c)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedMonoid.{u1} α] (a : α) (b : α) (c : α), Eq.{succ u1} α (Min.min.{u1} α (CanonicallyLinearOrderedMonoid.toMin.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))))))) a b) c) (Min.min.{u1} α (CanonicallyLinearOrderedMonoid.toMin.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))))))) (Min.min.{u1} α (CanonicallyLinearOrderedMonoid.toMin.{u1} α _inst_1) a c) (Min.min.{u1} α (CanonicallyLinearOrderedMonoid.toMin.{u1} α _inst_1) b c)) c)
Case conversion may be inaccurate. Consider using '#align min_mul_distrib' min_mul_distrib'ₓ'. -/
@[to_additive]
theorem min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c := by
  simpa [min_comm _ c] using min_mul_distrib c a b
#align min_mul_distrib' min_mul_distrib'

/- warning: one_min -> one_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedMonoid.{u1} α] (a : α), Eq.{succ u1} α (LinearOrder.min.{u1} α (CanonicallyLinearOrderedMonoid.toLinearOrder.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))))))))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedMonoid.{u1} α] (a : α), Eq.{succ u1} α (Min.min.{u1} α (CanonicallyLinearOrderedMonoid.toMin.{u1} α _inst_1) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))))))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align one_min one_minₓ'. -/
@[simp, to_additive]
theorem one_min (a : α) : min 1 a = 1 :=
  min_eq_left (one_le a)
#align one_min one_min

/- warning: min_one -> min_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedMonoid.{u1} α] (a : α), Eq.{succ u1} α (LinearOrder.min.{u1} α (CanonicallyLinearOrderedMonoid.toLinearOrder.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1)))))))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedMonoid.{u1} α] (a : α), Eq.{succ u1} α (Min.min.{u1} α (CanonicallyLinearOrderedMonoid.toMin.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1)))))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align min_one min_oneₓ'. -/
@[simp, to_additive]
theorem min_one (a : α) : min a 1 = 1 :=
  min_eq_right (one_le a)
#align min_one min_one

/- warning: bot_eq_one' -> bot_eq_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedMonoid.{u1} α], Eq.{succ u1} α (Bot.bot.{u1} α (CanonicallyOrderedMonoid.toHasBot.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedMonoid.{u1} α], Eq.{succ u1} α (Bot.bot.{u1} α (CanonicallyOrderedMonoid.toBot.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α (CanonicallyLinearOrderedMonoid.toCanonicallyOrderedMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align bot_eq_one' bot_eq_one'ₓ'. -/
/-- In a linearly ordered monoid, we are happy for `bot_eq_one` to be a `@[simp]` lemma. -/
@[simp,
  to_additive
      "In a linearly ordered monoid, we are happy for `bot_eq_zero` to be a `@[simp]` lemma"]
theorem bot_eq_one' : (⊥ : α) = 1 :=
  bot_eq_one
#align bot_eq_one' bot_eq_one'

end CanonicallyLinearOrderedMonoid

