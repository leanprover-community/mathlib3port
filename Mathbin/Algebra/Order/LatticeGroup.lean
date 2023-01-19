/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module algebra.order.lattice_group
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.Order.Group.Abs
import Mathbin.Tactic.NthRewrite.Default

/-!
# Lattice ordered groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942].
They form the algebraic underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

This file develops the basic theory, concentrating on the commutative case.

## Main statements

- `pos_div_neg`: Every element `a` of a lattice ordered commutative group has a decomposition
  `a⁺-a⁻` into the difference of the positive and negative component.
- `pos_inf_neg_eq_one`: The positive and negative components are coprime.
- `abs_triangle`: The absolute value operation satisfies the triangle inequality.

It is shown that the inf and sup operations are related to the absolute value operation by a
number of equations and inequalities.

## Notations

- `a⁺ = a ⊔ 0`: The *positive component* of an element `a` of a lattice ordered commutative group
- `a⁻ = (-a) ⊔ 0`: The *negative component* of an element `a` of a lattice ordered commutative group
- `|a| = a⊔(-a)`: The *absolute value* of an element `a` of a lattice ordered commutative group

## Implementation notes

A lattice ordered commutative group is a type `α` satisfying:

* `[lattice α]`
* `[comm_group α]`
* `[covariant_class α α (*) (≤)]`

The remainder of the file establishes basic properties of lattice ordered commutative groups. A
number of these results also hold in the non-commutative case ([Birkhoff][birkhoff1942],
[Fuchs][fuchs1963]) but we have not developed that here, since we are primarily interested in vector
lattices.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, ordered, group
-/


-- Needed for squares
-- Needed for squares
universe u

/- warning: linear_ordered_comm_group.to_covariant_class -> LinearOrderedCommGroup.to_covariantClass is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : LinearOrderedCommGroup.{u1} α], CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1))))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : LinearOrderedCommGroup.{u1} α], CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.18 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.20 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.18 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.20) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.33 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.35 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α (LinearOrderedCommGroup.toOrderedCommGroup.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.33 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.35)
Case conversion may be inaccurate. Consider using '#align linear_ordered_comm_group.to_covariant_class LinearOrderedCommGroup.to_covariantClassₓ'. -/
-- A linearly ordered additive commutative group is a lattice ordered commutative group
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_covariantClass (α : Type u)
    [LinearOrderedCommGroup α] : CovariantClass α α (· * ·) (· ≤ ·)
    where elim a b c bc := LinearOrderedCommGroup.mul_le_mul_left _ _ bc a
#align linear_ordered_comm_group.to_covariant_class LinearOrderedCommGroup.to_covariantClass

variable {α : Type u} [Lattice α] [CommGroup α]

/- warning: mul_sup -> mul_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.90 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.92 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.90 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.92) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.105 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.107 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.105 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.107)] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_sup mul_supₓ'. -/
-- Special case of Bourbaki A.VI.9 (1)
-- c + (a ⊔ b) = (c + a) ⊔ (c + b)
@[to_additive]
theorem mul_sup [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c * b :=
  by
  refine' le_antisymm _ (by simp)
  rw [← mul_le_mul_iff_left c⁻¹, ← mul_assoc, inv_mul_self, one_mul]
  exact sup_le (by simp) (by simp)
#align mul_sup mul_sup
#align add_sup add_sup

/- warning: mul_inf -> mul_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.304 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.306 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.304 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.306) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.319 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.321 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.319 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.321)] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inf mul_infₓ'. -/
@[to_additive]
theorem mul_inf [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : c * (a ⊓ b) = c * a ⊓ c * b :=
  by
  refine' le_antisymm (by simp) _
  rw [← mul_le_mul_iff_left c⁻¹, ← mul_assoc, inv_mul_self, one_mul]
  exact le_inf (by simp) (by simp)
#align mul_inf mul_inf
#align add_inf add_inf

/- warning: inv_sup_eq_inv_inf_inv -> inv_sup_eq_inv_inf_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.518 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.520 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.518 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.520) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.533 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.535 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.533 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.535)] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) b))
Case conversion may be inaccurate. Consider using '#align inv_sup_eq_inv_inf_inv inv_sup_eq_inv_inf_invₓ'. -/
-- Special case of Bourbaki A.VI.9 (2)
-- -(a ⊔ b)=(-a) ⊓ (-b)
@[to_additive]
theorem inv_sup_eq_inv_inf_inv [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹ := by
  apply le_antisymm
  · refine' le_inf _ _
    · rw [inv_le_inv_iff]
      exact le_sup_left
    · rw [inv_le_inv_iff]
      exact le_sup_right
  · rw [← inv_le_inv_iff, inv_inv]
    refine' sup_le _ _
    · rw [← inv_le_inv_iff]
      simp
    · rw [← inv_le_inv_iff]
      simp
#align inv_sup_eq_inv_inf_inv inv_sup_eq_inv_inf_inv
#align neg_sup_eq_neg_inf_neg neg_sup_eq_neg_inf_neg

/- warning: inv_inf_eq_sup_inv -> inv_inf_eq_sup_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.765 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.767 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.765 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.767) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.780 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.782 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.780 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.782)] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a b)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) b))
Case conversion may be inaccurate. Consider using '#align inv_inf_eq_sup_inv inv_inf_eq_sup_invₓ'. -/
-- -(a ⊓ b) = -a ⊔ -b
@[to_additive]
theorem inv_inf_eq_sup_inv [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹ :=
  by rw [← inv_inv (a⁻¹ ⊔ b⁻¹), inv_sup_eq_inv_inf_inv a⁻¹ b⁻¹, inv_inv, inv_inv]
#align inv_inf_eq_sup_inv inv_inf_eq_sup_inv
#align neg_inf_eq_sup_neg neg_inf_eq_sup_neg

/- warning: inf_mul_sup -> inf_mul_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.889 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.891 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.889 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.891) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.904 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.906 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.904 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.906)] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a b) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b)
Case conversion may be inaccurate. Consider using '#align inf_mul_sup inf_mul_supₓ'. -/
-- Bourbaki A.VI.10 Prop 7
-- a ⊓ b + (a ⊔ b) = a + b
@[to_additive]
theorem inf_mul_sup [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a ⊓ b) * (a ⊔ b) = a * b :=
  calc
    (a ⊓ b) * (a ⊔ b) = (a ⊓ b) * (a * b * (b⁻¹ ⊔ a⁻¹)) :=
      by
      rw [mul_sup b⁻¹ a⁻¹ (a * b)]
      simp
    _ = (a ⊓ b) * (a * b * (a ⊓ b)⁻¹) := by rw [inv_inf_eq_sup_inv, sup_comm]
    _ = a * b := by rw [mul_comm, inv_mul_cancel_right]
    
#align inf_mul_sup inf_mul_sup
#align inf_add_sup inf_add_sup

namespace LatticeOrderedCommGroup

#print LatticeOrderedCommGroup.hasOneLatticeHasPosPart /-
-- see Note [lower instance priority]
/--
Let `α` be a lattice ordered commutative group with identity `1`. For an element `a` of type `α`,
the element `a ⊔ 1` is said to be the *positive component* of `a`, denoted `a⁺`.
-/
@[to_additive
      "\nLet `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,\nthe element `a ⊔ 0` is said to be the *positive component* of `a`, denoted `a⁺`.\n"]
instance (priority := 100) hasOneLatticeHasPosPart : PosPart α :=
  ⟨fun a => a ⊔ 1⟩
#align lattice_ordered_comm_group.has_one_lattice_has_pos_part LatticeOrderedCommGroup.hasOneLatticeHasPosPart
#align lattice_ordered_comm_group.has_zero_lattice_has_pos_part LatticeOrderedCommGroup.hasZeroLatticeHasPosPart
-/

/- warning: lattice_ordered_comm_group.m_pos_part_def -> LatticeOrderedCommGroup.m_pos_part_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.m_pos_part_def LatticeOrderedCommGroup.m_pos_part_defₓ'. -/
@[to_additive pos_part_def]
theorem m_pos_part_def (a : α) : a⁺ = a ⊔ 1 :=
  rfl
#align lattice_ordered_comm_group.m_pos_part_def LatticeOrderedCommGroup.m_pos_part_def
#align lattice_ordered_comm_group.pos_part_def LatticeOrderedCommGroup.pos_part_def

#print LatticeOrderedCommGroup.hasOneLatticeHasNegPart /-
-- see Note [lower instance priority]
/--
Let `α` be a lattice ordered commutative group with identity `1`. For an element `a` of type `α`,
the element `(-a) ⊔ 1` is said to be the *negative component* of `a`, denoted `a⁻`.
-/
@[to_additive
      "\nLet `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,\nthe element `(-a) ⊔ 0` is said to be the *negative component* of `a`, denoted `a⁻`.\n"]
instance (priority := 100) hasOneLatticeHasNegPart : NegPart α :=
  ⟨fun a => a⁻¹ ⊔ 1⟩
#align lattice_ordered_comm_group.has_one_lattice_has_neg_part LatticeOrderedCommGroup.hasOneLatticeHasNegPart
#align lattice_ordered_comm_group.has_zero_lattice_has_neg_part LatticeOrderedCommGroup.hasZeroLatticeHasNegPart
-/

/- warning: lattice_ordered_comm_group.m_neg_part_def -> LatticeOrderedCommGroup.m_neg_part_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.m_neg_part_def LatticeOrderedCommGroup.m_neg_part_defₓ'. -/
@[to_additive neg_part_def]
theorem m_neg_part_def (a : α) : a⁻ = a⁻¹ ⊔ 1 :=
  rfl
#align lattice_ordered_comm_group.m_neg_part_def LatticeOrderedCommGroup.m_neg_part_def
#align lattice_ordered_comm_group.neg_part_def LatticeOrderedCommGroup.neg_part_def

/- warning: lattice_ordered_comm_group.pos_one -> LatticeOrderedCommGroup.pos_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α], Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α], Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_one LatticeOrderedCommGroup.pos_oneₓ'. -/
@[simp, to_additive]
theorem pos_one : (1 : α)⁺ = 1 :=
  sup_idem
#align lattice_ordered_comm_group.pos_one LatticeOrderedCommGroup.pos_one
#align lattice_ordered_comm_group.pos_zero LatticeOrderedCommGroup.pos_zero

/- warning: lattice_ordered_comm_group.neg_one -> LatticeOrderedCommGroup.neg_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α], Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α], Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_one LatticeOrderedCommGroup.neg_oneₓ'. -/
@[simp, to_additive]
theorem neg_one : (1 : α)⁻ = 1 := by rw [m_neg_part_def, inv_one, sup_idem]
#align lattice_ordered_comm_group.neg_one LatticeOrderedCommGroup.neg_one
#align lattice_ordered_comm_group.neg_zero LatticeOrderedCommGroup.neg_zero

/- warning: lattice_ordered_comm_group.neg_eq_inv_inf_one -> LatticeOrderedCommGroup.neg_eq_inv_inf_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1335 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1337 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1335 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1337) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1350 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1352 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1350 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1352)] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_eq_inv_inf_one LatticeOrderedCommGroup.neg_eq_inv_inf_oneₓ'. -/
-- a⁻ = -(a ⊓ 0)
@[to_additive]
theorem neg_eq_inv_inf_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁻ = (a ⊓ 1)⁻¹ := by
  rw [m_neg_part_def, ← inv_inj, inv_sup_eq_inv_inf_inv, inv_inv, inv_inv, inv_one]
#align lattice_ordered_comm_group.neg_eq_inv_inf_one LatticeOrderedCommGroup.neg_eq_inv_inf_one
#align lattice_ordered_comm_group.neg_eq_neg_inf_zero LatticeOrderedCommGroup.neg_eq_neg_inf_zero

/- warning: lattice_ordered_comm_group.le_mabs -> LatticeOrderedCommGroup.le_mabs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.le_mabs LatticeOrderedCommGroup.le_mabsₓ'. -/
@[to_additive le_abs]
theorem le_mabs (a : α) : a ≤ |a| :=
  le_sup_left
#align lattice_ordered_comm_group.le_mabs LatticeOrderedCommGroup.le_mabs
#align lattice_ordered_comm_group.le_abs LatticeOrderedCommGroup.le_abs

/- warning: lattice_ordered_comm_group.inv_le_abs -> LatticeOrderedCommGroup.inv_le_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.inv_le_abs LatticeOrderedCommGroup.inv_le_absₓ'. -/
-- -a ≤ |a|
@[to_additive]
theorem inv_le_abs (a : α) : a⁻¹ ≤ |a| :=
  le_sup_right
#align lattice_ordered_comm_group.inv_le_abs LatticeOrderedCommGroup.inv_le_abs
#align lattice_ordered_comm_group.neg_le_abs LatticeOrderedCommGroup.neg_le_abs

/- warning: lattice_ordered_comm_group.one_le_pos -> LatticeOrderedCommGroup.one_le_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.one_le_pos LatticeOrderedCommGroup.one_le_posₓ'. -/
-- 0 ≤ a⁺
@[to_additive pos_nonneg]
theorem one_le_pos (a : α) : 1 ≤ a⁺ :=
  le_sup_right
#align lattice_ordered_comm_group.one_le_pos LatticeOrderedCommGroup.one_le_pos
#align lattice_ordered_comm_group.pos_nonneg LatticeOrderedCommGroup.pos_nonneg

/- warning: lattice_ordered_comm_group.one_le_neg -> LatticeOrderedCommGroup.one_le_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.one_le_neg LatticeOrderedCommGroup.one_le_negₓ'. -/
-- 0 ≤ a⁻
@[to_additive neg_nonneg]
theorem one_le_neg (a : α) : 1 ≤ a⁻ :=
  le_sup_right
#align lattice_ordered_comm_group.one_le_neg LatticeOrderedCommGroup.one_le_neg
#align lattice_ordered_comm_group.neg_nonneg LatticeOrderedCommGroup.neg_nonneg

/- warning: lattice_ordered_comm_group.pos_le_one_iff -> LatticeOrderedCommGroup.pos_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_le_one_iff LatticeOrderedCommGroup.pos_le_one_iffₓ'. -/
-- pos_nonpos_iff
@[to_additive]
theorem pos_le_one_iff {a : α} : a⁺ ≤ 1 ↔ a ≤ 1 :=
  by
  rw [m_pos_part_def, sup_le_iff]
  simp
#align lattice_ordered_comm_group.pos_le_one_iff LatticeOrderedCommGroup.pos_le_one_iff
#align lattice_ordered_comm_group.pos_nonpos_iff LatticeOrderedCommGroup.pos_nonpos_iff

/- warning: lattice_ordered_comm_group.neg_le_one_iff -> LatticeOrderedCommGroup.neg_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_le_one_iff LatticeOrderedCommGroup.neg_le_one_iffₓ'. -/
-- neg_nonpos_iff
@[to_additive]
theorem neg_le_one_iff {a : α} : a⁻ ≤ 1 ↔ a⁻¹ ≤ 1 :=
  by
  rw [m_neg_part_def, sup_le_iff]
  simp
#align lattice_ordered_comm_group.neg_le_one_iff LatticeOrderedCommGroup.neg_le_one_iff
#align lattice_ordered_comm_group.neg_nonpos_iff LatticeOrderedCommGroup.neg_nonpos_iff

/- warning: lattice_ordered_comm_group.pos_eq_one_iff -> LatticeOrderedCommGroup.pos_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_eq_one_iff LatticeOrderedCommGroup.pos_eq_one_iffₓ'. -/
@[to_additive]
theorem pos_eq_one_iff {a : α} : a⁺ = 1 ↔ a ≤ 1 :=
  by
  rw [le_antisymm_iff]
  simp only [one_le_pos, and_true_iff]
  exact pos_le_one_iff
#align lattice_ordered_comm_group.pos_eq_one_iff LatticeOrderedCommGroup.pos_eq_one_iff
#align lattice_ordered_comm_group.pos_eq_zero_iff LatticeOrderedCommGroup.pos_eq_zero_iff

/- warning: lattice_ordered_comm_group.neg_eq_one_iff' -> LatticeOrderedCommGroup.neg_eq_one_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_eq_one_iff' LatticeOrderedCommGroup.neg_eq_one_iff'ₓ'. -/
@[to_additive]
theorem neg_eq_one_iff' {a : α} : a⁻ = 1 ↔ a⁻¹ ≤ 1 :=
  by
  rw [le_antisymm_iff]
  simp only [one_le_neg, and_true_iff]
  rw [neg_le_one_iff]
#align lattice_ordered_comm_group.neg_eq_one_iff' LatticeOrderedCommGroup.neg_eq_one_iff'
#align lattice_ordered_comm_group.neg_eq_zero_iff' LatticeOrderedCommGroup.neg_eq_zero_iff'

/- warning: lattice_ordered_comm_group.neg_eq_one_iff -> LatticeOrderedCommGroup.neg_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] {a : α}, Iff (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Mul.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] {a : α}, Iff (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_eq_one_iff LatticeOrderedCommGroup.neg_eq_one_iffₓ'. -/
@[to_additive]
theorem neg_eq_one_iff [CovariantClass α α Mul.mul LE.le] {a : α} : a⁻ = 1 ↔ 1 ≤ a :=
  by
  rw [le_antisymm_iff]
  simp only [one_le_neg, and_true_iff]
  rw [neg_le_one_iff, inv_le_one']
#align lattice_ordered_comm_group.neg_eq_one_iff LatticeOrderedCommGroup.neg_eq_one_iff
#align lattice_ordered_comm_group.neg_eq_zero_iff LatticeOrderedCommGroup.neg_eq_zero_iff

#print LatticeOrderedCommGroup.m_le_pos /-
@[to_additive le_pos]
theorem m_le_pos (a : α) : a ≤ a⁺ :=
  le_sup_left
#align lattice_ordered_comm_group.m_le_pos LatticeOrderedCommGroup.m_le_pos
#align lattice_ordered_comm_group.le_pos LatticeOrderedCommGroup.le_pos
-/

/- warning: lattice_ordered_comm_group.inv_le_neg -> LatticeOrderedCommGroup.inv_le_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.inv_le_neg LatticeOrderedCommGroup.inv_le_negₓ'. -/
-- -a ≤ a⁻
@[to_additive]
theorem inv_le_neg (a : α) : a⁻¹ ≤ a⁻ :=
  le_sup_left
#align lattice_ordered_comm_group.inv_le_neg LatticeOrderedCommGroup.inv_le_neg
#align lattice_ordered_comm_group.neg_le_neg LatticeOrderedCommGroup.neg_le_neg

/- warning: lattice_ordered_comm_group.neg_eq_pos_inv -> LatticeOrderedCommGroup.neg_eq_pos_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_eq_pos_inv LatticeOrderedCommGroup.neg_eq_pos_invₓ'. -/
-- Bourbaki A.VI.12
--  a⁻ = (-a)⁺
@[to_additive]
theorem neg_eq_pos_inv (a : α) : a⁻ = a⁻¹⁺ :=
  rfl
#align lattice_ordered_comm_group.neg_eq_pos_inv LatticeOrderedCommGroup.neg_eq_pos_inv
#align lattice_ordered_comm_group.neg_eq_pos_neg LatticeOrderedCommGroup.neg_eq_pos_neg

/- warning: lattice_ordered_comm_group.pos_eq_neg_inv -> LatticeOrderedCommGroup.pos_eq_neg_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_eq_neg_inv LatticeOrderedCommGroup.pos_eq_neg_invₓ'. -/
-- a⁺ = (-a)⁻
@[to_additive]
theorem pos_eq_neg_inv (a : α) : a⁺ = a⁻¹⁻ := by simp [neg_eq_pos_inv]
#align lattice_ordered_comm_group.pos_eq_neg_inv LatticeOrderedCommGroup.pos_eq_neg_inv
#align lattice_ordered_comm_group.pos_eq_neg_neg LatticeOrderedCommGroup.pos_eq_neg_neg

/- warning: lattice_ordered_comm_group.mul_inf_eq_mul_inf_mul -> LatticeOrderedCommGroup.mul_inf_eq_mul_inf_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1986 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1988 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1986 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1988) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2001 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2003 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2001 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2003)] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a b)) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c b))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.mul_inf_eq_mul_inf_mul LatticeOrderedCommGroup.mul_inf_eq_mul_inf_mulₓ'. -/
-- We use this in Bourbaki A.VI.12  Prop 9 a)
-- c + (a ⊓ b) = (c + a) ⊓ (c + b)
@[to_additive]
theorem mul_inf_eq_mul_inf_mul [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    c * (a ⊓ b) = c * a ⊓ c * b :=
  by
  refine' le_antisymm (by simp) _
  rw [← mul_le_mul_iff_left c⁻¹, ← mul_assoc, inv_mul_self, one_mul, le_inf_iff]
  simp
#align lattice_ordered_comm_group.mul_inf_eq_mul_inf_mul LatticeOrderedCommGroup.mul_inf_eq_mul_inf_mul
#align lattice_ordered_comm_group.add_inf_eq_add_inf_add LatticeOrderedCommGroup.add_inf_eq_add_inf_add

/- warning: lattice_ordered_comm_group.pos_div_neg -> LatticeOrderedCommGroup.pos_div_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2136 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2138 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2136 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2138) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2151 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2153 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2151 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2153)] (a : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)) a
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_div_neg LatticeOrderedCommGroup.pos_div_negₓ'. -/
-- Bourbaki A.VI.12  Prop 9 a)
-- a = a⁺ - a⁻
@[simp, to_additive]
theorem pos_div_neg [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁺ / a⁻ = a :=
  by
  symm
  rw [div_eq_mul_inv]
  apply eq_mul_inv_of_mul_eq
  rw [m_neg_part_def, mul_sup, mul_one, mul_right_inv, sup_comm, m_pos_part_def]
#align lattice_ordered_comm_group.pos_div_neg LatticeOrderedCommGroup.pos_div_neg
#align lattice_ordered_comm_group.pos_sub_neg LatticeOrderedCommGroup.pos_sub_neg

/- warning: lattice_ordered_comm_group.pos_inf_neg_eq_one -> LatticeOrderedCommGroup.pos_inf_neg_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2260 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2262 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2260 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2262) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2275 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2277 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2275 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2277)] (a : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_inf_neg_eq_one LatticeOrderedCommGroup.pos_inf_neg_eq_oneₓ'. -/
-- Bourbaki A.VI.12  Prop 9 a)
-- a⁺ ⊓ a⁻ = 0 (`a⁺` and `a⁻` are co-prime, and, since they are positive, disjoint)
@[to_additive]
theorem pos_inf_neg_eq_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁺ ⊓ a⁻ = 1 := by
  rw [← mul_right_inj (a⁻)⁻¹, mul_inf_eq_mul_inf_mul, mul_one, mul_left_inv, mul_comm, ←
    div_eq_mul_inv, pos_div_neg, neg_eq_inv_inf_one, inv_inv]
#align lattice_ordered_comm_group.pos_inf_neg_eq_one LatticeOrderedCommGroup.pos_inf_neg_eq_one
#align lattice_ordered_comm_group.pos_inf_neg_eq_zero LatticeOrderedCommGroup.pos_inf_neg_eq_zero

/- warning: lattice_ordered_comm_group.sup_eq_mul_pos_div -> LatticeOrderedCommGroup.sup_eq_mul_pos_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) b (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2366 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2368 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2366 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2368) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2381 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2383 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2381 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2383)] (a : α) (b : α), Eq.{succ u1} α (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) b (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.sup_eq_mul_pos_div LatticeOrderedCommGroup.sup_eq_mul_pos_divₓ'. -/
-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊔b = b + (a - b)⁺
@[to_additive]
theorem sup_eq_mul_pos_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : a ⊔ b = b * (a / b)⁺ :=
  calc
    a ⊔ b = b * (a / b) ⊔ b * 1 := by
      rw [mul_one b, div_eq_mul_inv, mul_comm a, mul_inv_cancel_left]
    _ = b * (a / b ⊔ 1) := by rw [← mul_sup (a / b) 1 b]
    
#align lattice_ordered_comm_group.sup_eq_mul_pos_div LatticeOrderedCommGroup.sup_eq_mul_pos_div
#align lattice_ordered_comm_group.sup_eq_add_pos_sub LatticeOrderedCommGroup.sup_eq_add_pos_sub

/- warning: lattice_ordered_comm_group.inf_eq_div_pos_div -> LatticeOrderedCommGroup.inf_eq_div_pos_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2549 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2551 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2549 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2551) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2564 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2566 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2564 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2566)] (a : α) (b : α), Eq.{succ u1} α (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.inf_eq_div_pos_div LatticeOrderedCommGroup.inf_eq_div_pos_divₓ'. -/
-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊓b = a - (a - b)⁺
@[to_additive]
theorem inf_eq_div_pos_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : a ⊓ b = a / (a / b)⁺ :=
  calc
    a ⊓ b = a * 1 ⊓ a * (b / a) := by
      rw [mul_one a, div_eq_mul_inv, mul_comm b, mul_inv_cancel_left]
    _ = a * (1 ⊓ b / a) := by rw [← mul_inf_eq_mul_inf_mul 1 (b / a) a]
    _ = a * (b / a ⊓ 1) := by rw [inf_comm]
    _ = a * ((a / b)⁻¹ ⊓ 1) := by
      rw [div_eq_mul_inv]
      nth_rw 1 [← inv_inv b]
      rw [← mul_inv, mul_comm b⁻¹, ← div_eq_mul_inv]
    _ = a * ((a / b)⁻¹ ⊓ 1⁻¹) := by rw [inv_one]
    _ = a / (a / b ⊔ 1) := by rw [← inv_sup_eq_inv_inf_inv, ← div_eq_mul_inv]
    
#align lattice_ordered_comm_group.inf_eq_div_pos_div LatticeOrderedCommGroup.inf_eq_div_pos_div
#align lattice_ordered_comm_group.inf_eq_sub_pos_sub LatticeOrderedCommGroup.inf_eq_sub_pos_sub

/- warning: lattice_ordered_comm_group.m_le_iff_pos_le_neg_ge -> LatticeOrderedCommGroup.m_le_iff_pos_le_neg_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a b) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) b) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2999 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3001 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2999 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3001) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3014 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3016 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3014 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3016)] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a b) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) b) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.m_le_iff_pos_le_neg_ge LatticeOrderedCommGroup.m_le_iff_pos_le_neg_geₓ'. -/
-- Bourbaki A.VI.12 Prop 9 c)
@[to_additive le_iff_pos_le_neg_ge]
theorem m_le_iff_pos_le_neg_ge [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    a ≤ b ↔ a⁺ ≤ b⁺ ∧ b⁻ ≤ a⁻ := by
  constructor <;> intro h
  · constructor
    · exact sup_le (h.trans (m_le_pos b)) (one_le_pos b)
    · rw [← inv_le_inv_iff] at h
      exact sup_le (h.trans (inv_le_neg a)) (one_le_neg a)
  · rw [← pos_div_neg a, ← pos_div_neg b]
    exact div_le_div'' h.1 h.2
#align lattice_ordered_comm_group.m_le_iff_pos_le_neg_ge LatticeOrderedCommGroup.m_le_iff_pos_le_neg_ge
#align lattice_ordered_comm_group.le_iff_pos_le_neg_ge LatticeOrderedCommGroup.le_iff_pos_le_neg_ge

/- warning: lattice_ordered_comm_group.m_neg_abs -> LatticeOrderedCommGroup.m_neg_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3198 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3200 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3198 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3200) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3213 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3215 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3213 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3215)] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.m_neg_abs LatticeOrderedCommGroup.m_neg_absₓ'. -/
@[to_additive neg_abs]
theorem m_neg_abs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : |a|⁻ = 1 :=
  by
  refine' le_antisymm _ _
  · rw [← pos_inf_neg_eq_one a]
    apply le_inf
    · rw [pos_eq_neg_inv]
      exact ((m_le_iff_pos_le_neg_ge _ _).mp (inv_le_abs a)).right
    · exact And.right (Iff.mp (m_le_iff_pos_le_neg_ge _ _) (le_mabs a))
  · exact one_le_neg _
#align lattice_ordered_comm_group.m_neg_abs LatticeOrderedCommGroup.m_neg_abs
#align lattice_ordered_comm_group.neg_abs LatticeOrderedCommGroup.neg_abs

/- warning: lattice_ordered_comm_group.m_pos_abs -> LatticeOrderedCommGroup.m_pos_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3360 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3362 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3360 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3362) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3375 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3377 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3375 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3377)] (a : α), Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.m_pos_abs LatticeOrderedCommGroup.m_pos_absₓ'. -/
@[to_additive pos_abs]
theorem m_pos_abs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : |a|⁺ = |a| :=
  by
  nth_rw 2 [← pos_div_neg (|a|)]
  rw [div_eq_mul_inv]
  symm
  rw [mul_right_eq_self, inv_eq_one]
  exact m_neg_abs a
#align lattice_ordered_comm_group.m_pos_abs LatticeOrderedCommGroup.m_pos_abs
#align lattice_ordered_comm_group.pos_abs LatticeOrderedCommGroup.pos_abs

/- warning: lattice_ordered_comm_group.one_le_abs -> LatticeOrderedCommGroup.one_le_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3521 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3523 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3521 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3523) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3536 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3538 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3536 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3538)] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.one_le_abs LatticeOrderedCommGroup.one_le_absₓ'. -/
@[to_additive abs_nonneg]
theorem one_le_abs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : 1 ≤ |a| :=
  by
  rw [← m_pos_abs]
  exact one_le_pos _
#align lattice_ordered_comm_group.one_le_abs LatticeOrderedCommGroup.one_le_abs
#align lattice_ordered_comm_group.abs_nonneg LatticeOrderedCommGroup.abs_nonneg

/- warning: lattice_ordered_comm_group.pos_mul_neg -> LatticeOrderedCommGroup.pos_mul_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3609 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3611 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3609 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3611) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3624 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3626 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3624 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3626)] (a : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_mul_neg LatticeOrderedCommGroup.pos_mul_negₓ'. -/
-- The proof from Bourbaki A.VI.12 Prop 9 d)
-- |a| = a⁺ - a⁻
@[to_additive]
theorem pos_mul_neg [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : |a| = a⁺ * a⁻ :=
  by
  refine' le_antisymm _ _
  · refine' sup_le _ _
    · nth_rw 1 [← mul_one a]
      exact mul_le_mul' (m_le_pos a) (one_le_neg a)
    · nth_rw 1 [← one_mul a⁻¹]
      exact mul_le_mul' (one_le_pos a) (inv_le_neg a)
  · rw [← inf_mul_sup, pos_inf_neg_eq_one, one_mul, ← m_pos_abs a]
    apply sup_le
    · exact ((m_le_iff_pos_le_neg_ge _ _).mp (le_mabs a)).left
    · rw [neg_eq_pos_inv]
      exact ((m_le_iff_pos_le_neg_ge _ _).mp (inv_le_abs a)).left
#align lattice_ordered_comm_group.pos_mul_neg LatticeOrderedCommGroup.pos_mul_neg
#align lattice_ordered_comm_group.pos_add_neg LatticeOrderedCommGroup.pos_add_neg

/- warning: lattice_ordered_comm_group.sup_div_inf_eq_abs_div -> LatticeOrderedCommGroup.sup_div_inf_eq_abs_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3869 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3871 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3869 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3871) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3884 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3886 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3884 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3886)] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a b)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.sup_div_inf_eq_abs_div LatticeOrderedCommGroup.sup_div_inf_eq_abs_divₓ'. -/
-- a ⊔ b - (a ⊓ b) = |b - a|
@[to_additive]
theorem sup_div_inf_eq_abs_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    (a ⊔ b) / (a ⊓ b) = |b / a| :=
  by
  rw [sup_eq_mul_pos_div, inf_comm, inf_eq_div_pos_div, div_eq_mul_inv]
  nth_rw 2 [div_eq_mul_inv]
  rw [mul_inv_rev, inv_inv, mul_comm, ← mul_assoc, inv_mul_cancel_right, pos_eq_neg_inv (a / b)]
  nth_rw 2 [div_eq_mul_inv]
  rw [mul_inv_rev, ← div_eq_mul_inv, inv_inv, ← pos_mul_neg]
#align lattice_ordered_comm_group.sup_div_inf_eq_abs_div LatticeOrderedCommGroup.sup_div_inf_eq_abs_div
#align lattice_ordered_comm_group.sup_sub_inf_eq_abs_sub LatticeOrderedCommGroup.sup_sub_inf_eq_abs_sub

/- warning: lattice_ordered_comm_group.sup_sq_eq_mul_mul_abs_div -> LatticeOrderedCommGroup.sup_sq_eq_mul_mul_abs_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4005 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4007 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4005 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4007) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4020 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4022 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4020 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4022)] (a : α) (b : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a)))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.sup_sq_eq_mul_mul_abs_div LatticeOrderedCommGroup.sup_sq_eq_mul_mul_abs_divₓ'. -/
-- 2•(a ⊔ b) = a + b + |b - a|
@[to_additive two_sup_eq_add_add_abs_sub]
theorem sup_sq_eq_mul_mul_abs_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    (a ⊔ b) ^ 2 = a * b * |b / a| := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_abs_div, div_eq_mul_inv, ← mul_assoc, mul_comm, mul_assoc,
    ← pow_two, inv_mul_cancel_left]
#align lattice_ordered_comm_group.sup_sq_eq_mul_mul_abs_div LatticeOrderedCommGroup.sup_sq_eq_mul_mul_abs_div
#align lattice_ordered_comm_group.two_sup_eq_add_add_abs_sub LatticeOrderedCommGroup.two_sup_eq_add_add_abs_sub

/- warning: lattice_ordered_comm_group.inf_sq_eq_mul_div_abs_div -> LatticeOrderedCommGroup.inf_sq_eq_mul_div_abs_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4112 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4114 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4112 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4114) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4127 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4129 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4127 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4129)] (a : α) (b : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a b) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a)))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.inf_sq_eq_mul_div_abs_div LatticeOrderedCommGroup.inf_sq_eq_mul_div_abs_divₓ'. -/
-- 2•(a ⊓ b) = a + b - |b - a|
@[to_additive two_inf_eq_add_sub_abs_sub]
theorem inf_sq_eq_mul_div_abs_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    (a ⊓ b) ^ 2 = a * b / |b / a| := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_abs_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev,
    inv_inv, mul_assoc, mul_inv_cancel_comm_assoc, ← pow_two]
#align lattice_ordered_comm_group.inf_sq_eq_mul_div_abs_div LatticeOrderedCommGroup.inf_sq_eq_mul_div_abs_div
#align lattice_ordered_comm_group.two_inf_eq_add_sub_abs_sub LatticeOrderedCommGroup.two_inf_eq_add_sub_abs_sub

/- warning: lattice_ordered_comm_group.lattice_ordered_comm_group_to_distrib_lattice -> LatticeOrderedCommGroup.latticeOrderedCommGroupToDistribLattice is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [s : Lattice.{u1} α] [_inst_3 : CommGroup.{u1} α] [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_3))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α s)))))], DistribLattice.{u1} α
but is expected to have type
  forall (α : Type.{u1}) [s : Lattice.{u1} α] [_inst_3 : CommGroup.{u1} α] [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4226 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4228 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_3)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4226 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4228) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4241 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4243 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α s)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4241 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4243)], DistribLattice.{u1} α
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.lattice_ordered_comm_group_to_distrib_lattice LatticeOrderedCommGroup.latticeOrderedCommGroupToDistribLatticeₓ'. -/
/-- Every lattice ordered commutative group is a distributive lattice
-/
@[to_additive "Every lattice ordered commutative additive group is a distributive lattice"]
def latticeOrderedCommGroupToDistribLattice (α : Type u) [s : Lattice α] [CommGroup α]
    [CovariantClass α α (· * ·) (· ≤ ·)] : DistribLattice α :=
  { s with
    le_sup_inf := by
      intros
      rw [← mul_le_mul_iff_left (x ⊓ (y ⊓ z)), inf_mul_sup x (y ⊓ z), ← inv_mul_le_iff_le_mul,
        le_inf_iff]
      constructor
      · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y]
        apply mul_le_mul'
        · apply inf_le_inf_left
          apply inf_le_left
        · apply inf_le_left
      · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x z]
        apply mul_le_mul'
        · apply inf_le_inf_left
          apply inf_le_right
        · apply inf_le_right }
#align lattice_ordered_comm_group.lattice_ordered_comm_group_to_distrib_lattice LatticeOrderedCommGroup.latticeOrderedCommGroupToDistribLattice
#align lattice_ordered_comm_group.lattice_ordered_add_comm_group_to_distrib_lattice LatticeOrderedCommGroup.latticeOrderedAddCommGroupToDistribLattice

/- warning: lattice_ordered_comm_group.abs_div_sup_mul_abs_div_inf -> LatticeOrderedCommGroup.abs_div_sup_mul_abs_div_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a c) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) b c)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4422 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4424 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4422 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4424) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4437 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4439 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4437 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4439)] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a c) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) b c)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.abs_div_sup_mul_abs_div_inf LatticeOrderedCommGroup.abs_div_sup_mul_abs_div_infₓ'. -/
-- See, e.g. Zaanen, Lectures on Riesz Spaces
-- 3rd lecture
-- |a ⊔ c - (b ⊔ c)| + |a ⊓ c-b ⊓ c| = |a - b|
@[to_additive]
theorem abs_div_sup_mul_abs_div_inf [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)| * |(a ⊓ c) / (b ⊓ c)| = |a / b| :=
  by
  letI : DistribLattice α := lattice_ordered_comm_group_to_distrib_lattice α
  calc
    |(a ⊔ c) / (b ⊔ c)| * |(a ⊓ c) / (b ⊓ c)| =
        (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * |(a ⊓ c) / (b ⊓ c)| :=
      by rw [sup_div_inf_eq_abs_div]
    _ = (b ⊔ c ⊔ (a ⊔ c)) / ((b ⊔ c) ⊓ (a ⊔ c)) * ((b ⊓ c ⊔ a ⊓ c) / (b ⊓ c ⊓ (a ⊓ c))) := by
      rw [sup_div_inf_eq_abs_div (b ⊓ c) (a ⊓ c)]
    _ = (b ⊔ a ⊔ c) / (b ⊓ a ⊔ c) * (((b ⊔ a) ⊓ c) / (b ⊓ a ⊓ c)) :=
      by
      rw [← sup_inf_right, ← inf_sup_right, sup_assoc]
      nth_rw 2 [sup_comm]
      rw [sup_right_idem, sup_assoc, inf_assoc]
      nth_rw 4 [inf_comm]
      rw [inf_right_idem, inf_assoc]
    _ = (b ⊔ a ⊔ c) * ((b ⊔ a) ⊓ c) / ((b ⊓ a ⊔ c) * (b ⊓ a ⊓ c)) := by rw [div_mul_div_comm]
    _ = (b ⊔ a) * c / ((b ⊓ a) * c) := by
      rw [mul_comm, inf_mul_sup, mul_comm (b ⊓ a ⊔ c), inf_mul_sup]
    _ = (b ⊔ a) / (b ⊓ a) := by
      rw [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← div_eq_mul_inv]
    _ = |a / b| := by rw [sup_div_inf_eq_abs_div]
    
#align lattice_ordered_comm_group.abs_div_sup_mul_abs_div_inf LatticeOrderedCommGroup.abs_div_sup_mul_abs_div_inf
#align lattice_ordered_comm_group.abs_sub_sup_add_abs_sub_inf LatticeOrderedCommGroup.abs_sub_sup_add_abs_sub_inf

/- warning: lattice_ordered_comm_group.pos_of_one_le -> LatticeOrderedCommGroup.pos_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) a) -> (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) a) -> (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_of_one_le LatticeOrderedCommGroup.pos_of_one_leₓ'. -/
-- pos_of_nonneg
/-- If `a` is positive, then it is equal to its positive component `a⁺`. -/
@[to_additive "If `a` is positive, then it is equal to its positive component `a⁺`."]
theorem pos_of_one_le (a : α) (h : 1 ≤ a) : a⁺ = a :=
  by
  rw [m_pos_part_def]
  exact sup_of_le_left h
#align lattice_ordered_comm_group.pos_of_one_le LatticeOrderedCommGroup.pos_of_one_le
#align lattice_ordered_comm_group.pos_of_nonneg LatticeOrderedCommGroup.pos_of_nonneg

/- warning: lattice_ordered_comm_group.pos_eq_self_of_one_lt_pos -> LatticeOrderedCommGroup.pos_eq_self_of_one_lt_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : LinearOrder.{u1} α] [_inst_4 : CommGroup.{u1} α] {x : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_3))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))))))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α (LinearOrder.toLattice.{u1} α _inst_3) _inst_4) x)) -> (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α (LinearOrder.toLattice.{u1} α _inst_3) _inst_4) x) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : LinearOrder.{u1} α] [_inst_4 : CommGroup.{u1} α] {x : α}, (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_3)))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_4))))))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_3)) _inst_4) x)) -> (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_3)) _inst_4) x) x)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_eq_self_of_one_lt_pos LatticeOrderedCommGroup.pos_eq_self_of_one_lt_posₓ'. -/
-- pos_eq_self_of_pos_pos
@[to_additive]
theorem pos_eq_self_of_one_lt_pos {α} [LinearOrder α] [CommGroup α] {x : α} (hx : 1 < x⁺) :
    x⁺ = x := by
  rw [m_pos_part_def, right_lt_sup, not_le] at hx
  rw [m_pos_part_def, sup_eq_left]
  exact hx.le
#align lattice_ordered_comm_group.pos_eq_self_of_one_lt_pos LatticeOrderedCommGroup.pos_eq_self_of_one_lt_pos
#align lattice_ordered_comm_group.pos_eq_self_of_pos_pos LatticeOrderedCommGroup.pos_eq_self_of_pos_pos

/- warning: lattice_ordered_comm_group.pos_of_le_one -> LatticeOrderedCommGroup.pos_of_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) -> (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) -> (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_of_le_one LatticeOrderedCommGroup.pos_of_le_oneₓ'. -/
-- 0 ≤ a implies a⁺ = a
-- pos_of_nonpos
@[to_additive]
theorem pos_of_le_one (a : α) (h : a ≤ 1) : a⁺ = 1 :=
  pos_eq_one_iff.mpr h
#align lattice_ordered_comm_group.pos_of_le_one LatticeOrderedCommGroup.pos_of_le_one
#align lattice_ordered_comm_group.pos_of_nonpos LatticeOrderedCommGroup.pos_of_nonpos

/- warning: lattice_ordered_comm_group.neg_of_one_le_inv -> LatticeOrderedCommGroup.neg_of_one_le_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a)) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a)) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_of_one_le_inv LatticeOrderedCommGroup.neg_of_one_le_invₓ'. -/
@[to_additive neg_of_inv_nonneg]
theorem neg_of_one_le_inv (a : α) (h : 1 ≤ a⁻¹) : a⁻ = a⁻¹ :=
  by
  rw [neg_eq_pos_inv]
  exact pos_of_one_le _ h
#align lattice_ordered_comm_group.neg_of_one_le_inv LatticeOrderedCommGroup.neg_of_one_le_inv
#align lattice_ordered_comm_group.neg_of_inv_nonneg LatticeOrderedCommGroup.neg_of_inv_nonneg

/- warning: lattice_ordered_comm_group.neg_of_inv_le_one -> LatticeOrderedCommGroup.neg_of_inv_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_of_inv_le_one LatticeOrderedCommGroup.neg_of_inv_le_oneₓ'. -/
-- neg_of_neg_nonpos
@[to_additive]
theorem neg_of_inv_le_one (a : α) (h : a⁻¹ ≤ 1) : a⁻ = 1 :=
  neg_eq_one_iff'.mpr h
#align lattice_ordered_comm_group.neg_of_inv_le_one LatticeOrderedCommGroup.neg_of_inv_le_one
#align lattice_ordered_comm_group.neg_of_neg_nonpos LatticeOrderedCommGroup.neg_of_neg_nonpos

/- warning: lattice_ordered_comm_group.neg_of_le_one -> LatticeOrderedCommGroup.neg_of_le_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5418 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5420 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5418 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5420) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5433 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5435 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5433 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5435)] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_of_le_one LatticeOrderedCommGroup.neg_of_le_oneₓ'. -/
-- neg_of_nonpos
@[to_additive]
theorem neg_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : a ≤ 1) : a⁻ = a⁻¹ :=
  by
  refine' neg_of_one_le_inv _ _
  rw [one_le_inv']
  exact h
#align lattice_ordered_comm_group.neg_of_le_one LatticeOrderedCommGroup.neg_of_le_one
#align lattice_ordered_comm_group.neg_of_nonpos LatticeOrderedCommGroup.neg_of_nonpos

/- warning: lattice_ordered_comm_group.neg_of_one_le -> LatticeOrderedCommGroup.neg_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) a) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5518 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5520 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5518 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5520) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5533 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5535 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5533 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5535)] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) a) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_of_one_le LatticeOrderedCommGroup.neg_of_one_leₓ'. -/
-- neg_of_nonneg'
@[to_additive]
theorem neg_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : 1 ≤ a) : a⁻ = 1 :=
  neg_eq_one_iff.mpr h
#align lattice_ordered_comm_group.neg_of_one_le LatticeOrderedCommGroup.neg_of_one_le
#align lattice_ordered_comm_group.neg_of_nonneg LatticeOrderedCommGroup.neg_of_nonneg

/- warning: lattice_ordered_comm_group.mabs_of_one_le -> LatticeOrderedCommGroup.mabs_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) a) -> (Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5578 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5580 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5578 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5580) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5593 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5595 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5593 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5595)] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) a) -> (Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.mabs_of_one_le LatticeOrderedCommGroup.mabs_of_one_leₓ'. -/
-- 0 ≤ a implies |a| = a
@[to_additive abs_of_nonneg]
theorem mabs_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : 1 ≤ a) : |a| = a :=
  by
  unfold Abs.abs
  rw [sup_eq_mul_pos_div, div_eq_mul_inv, inv_inv, ← pow_two, inv_mul_eq_iff_eq_mul, ← pow_two,
    pos_of_one_le]
  rw [pow_two]
  apply one_le_mul h h
#align lattice_ordered_comm_group.mabs_of_one_le LatticeOrderedCommGroup.mabs_of_one_le
#align lattice_ordered_comm_group.abs_of_nonneg LatticeOrderedCommGroup.abs_of_nonneg

/- warning: lattice_ordered_comm_group.mabs_mabs -> LatticeOrderedCommGroup.mabs_mabs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5705 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5707 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5705 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5707) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5720 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5722 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5720 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5722)] (a : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.mabs_mabs LatticeOrderedCommGroup.mabs_mabsₓ'. -/
/-- The unary operation of taking the absolute value is idempotent. -/
@[simp, to_additive abs_abs "The unary operation of taking the absolute value is idempotent."]
theorem mabs_mabs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : ||a|| = |a| :=
  mabs_of_one_le _ (one_le_abs _)
#align lattice_ordered_comm_group.mabs_mabs LatticeOrderedCommGroup.mabs_mabs
#align lattice_ordered_comm_group.abs_abs LatticeOrderedCommGroup.abs_abs

/- warning: lattice_ordered_comm_group.mabs_sup_div_sup_le_mabs -> LatticeOrderedCommGroup.mabs_sup_div_sup_le_mabs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5773 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5775 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5773 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5775) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5788 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5790 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5788 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5790)] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.mabs_sup_div_sup_le_mabs LatticeOrderedCommGroup.mabs_sup_div_sup_le_mabsₓ'. -/
@[to_additive abs_sup_sub_sup_le_abs]
theorem mabs_sup_div_sup_le_mabs [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)| ≤ |a / b| :=
  by
  apply le_of_mul_le_of_one_le_left
  · rw [abs_div_sup_mul_abs_div_inf]
  · exact one_le_abs _
#align lattice_ordered_comm_group.mabs_sup_div_sup_le_mabs LatticeOrderedCommGroup.mabs_sup_div_sup_le_mabs
#align lattice_ordered_comm_group.abs_sup_sub_sup_le_abs LatticeOrderedCommGroup.abs_sup_sub_sup_le_abs

/- warning: lattice_ordered_comm_group.mabs_inf_div_inf_le_mabs -> LatticeOrderedCommGroup.mabs_inf_div_inf_le_mabs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a c) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5887 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5889 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5887 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5889) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5902 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5904 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5902 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5904)] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a c) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.mabs_inf_div_inf_le_mabs LatticeOrderedCommGroup.mabs_inf_div_inf_le_mabsₓ'. -/
@[to_additive abs_inf_sub_inf_le_abs]
theorem mabs_inf_div_inf_le_mabs [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    |(a ⊓ c) / (b ⊓ c)| ≤ |a / b| :=
  by
  apply le_of_mul_le_of_one_le_right
  · rw [abs_div_sup_mul_abs_div_inf]
  · exact one_le_abs _
#align lattice_ordered_comm_group.mabs_inf_div_inf_le_mabs LatticeOrderedCommGroup.mabs_inf_div_inf_le_mabs
#align lattice_ordered_comm_group.abs_inf_sub_inf_le_abs LatticeOrderedCommGroup.abs_inf_sub_inf_le_abs

/- warning: lattice_ordered_comm_group.m_Birkhoff_inequalities -> LatticeOrderedCommGroup.m_Birkhoff_inequalities is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a c) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) b c)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6001 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6003 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6001 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6003) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6016 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6018 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6016 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6018)] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) a c) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α _inst_1) b c)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.m_Birkhoff_inequalities LatticeOrderedCommGroup.m_Birkhoff_inequalitiesₓ'. -/
-- Commutative case, Zaanen, 3rd lecture
-- For the non-commutative case, see Birkhoff Theorem 19 (27)
-- |(a ⊔ c) - (b ⊔ c)| ⊔ |(a ⊓ c) - (b ⊓ c)| ≤ |a - b|
@[to_additive Birkhoff_inequalities]
theorem m_Birkhoff_inequalities [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    |(a ⊔ c) / (b ⊔ c)| ⊔ |(a ⊓ c) / (b ⊓ c)| ≤ |a / b| :=
  sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)
#align lattice_ordered_comm_group.m_Birkhoff_inequalities LatticeOrderedCommGroup.m_Birkhoff_inequalities
#align lattice_ordered_comm_group.Birkhoff_inequalities LatticeOrderedCommGroup.Birkhoff_inequalities

/- warning: lattice_ordered_comm_group.mabs_mul_le -> LatticeOrderedCommGroup.mabs_mul_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6112 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6114 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6112 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6114) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6127 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6129 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6127 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6129)] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) b))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.mabs_mul_le LatticeOrderedCommGroup.mabs_mul_leₓ'. -/
-- Banasiak Proposition 2.12, Zaanen 2nd lecture
/-- The absolute value satisfies the triangle inequality.
-/
@[to_additive abs_add_le "The absolute value satisfies the triangle inequality."]
theorem mabs_mul_le [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : |a * b| ≤ |a| * |b| :=
  by
  apply sup_le
  · exact mul_le_mul' (le_mabs a) (le_mabs b)
  · rw [mul_inv]
    exact mul_le_mul' (inv_le_abs _) (inv_le_abs _)
#align lattice_ordered_comm_group.mabs_mul_le LatticeOrderedCommGroup.mabs_mul_le
#align lattice_ordered_comm_group.abs_add_le LatticeOrderedCommGroup.abs_add_le

/- warning: lattice_ordered_comm_group.abs_inv_comm -> LatticeOrderedCommGroup.abs_inv_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.abs_inv_comm LatticeOrderedCommGroup.abs_inv_commₓ'. -/
-- |a - b| = |b - a|
@[to_additive]
theorem abs_inv_comm (a b : α) : |a / b| = |b / a| :=
  by
  unfold Abs.abs
  rw [inv_div a b, ← inv_inv (a / b), inv_div, sup_comm]
#align lattice_ordered_comm_group.abs_inv_comm LatticeOrderedCommGroup.abs_inv_comm
#align lattice_ordered_comm_group.abs_neg_comm LatticeOrderedCommGroup.abs_neg_comm

/- warning: lattice_ordered_comm_group.abs_abs_div_abs_le -> LatticeOrderedCommGroup.abs_abs_div_abs_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) b))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6311 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6313 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6311 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6313) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6326 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6328 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6326 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.6328)] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) b))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.abs_abs_div_abs_le LatticeOrderedCommGroup.abs_abs_div_abs_leₓ'. -/
-- | |a| - |b| | ≤ |a - b|
@[to_additive]
theorem abs_abs_div_abs_le [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : ||a| / |b|| ≤ |a / b| :=
  by
  unfold Abs.abs
  rw [sup_le_iff]
  constructor
  · apply div_le_iff_le_mul.2
    convert mabs_mul_le (a / b) b
    · rw [div_mul_cancel']
    · rw [div_mul_cancel']
    · exact covariant_swap_mul_le_of_covariant_mul_le α
  · rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_le_iff_le_mul, ← abs_eq_sup_inv (a / b),
      abs_inv_comm]
    convert mabs_mul_le (b / a) a
    · rw [div_mul_cancel']
    · rw [div_mul_cancel']
#align lattice_ordered_comm_group.abs_abs_div_abs_le LatticeOrderedCommGroup.abs_abs_div_abs_le
#align lattice_ordered_comm_group.abs_abs_sub_abs_le LatticeOrderedCommGroup.abs_abs_sub_abs_le

end LatticeOrderedCommGroup

