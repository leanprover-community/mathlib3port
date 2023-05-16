/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module algebra.order.lattice_group
! leanprover-community/mathlib commit 5dc275ec639221ca4d5f56938eb966f6ad9bc89f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.Order.Group.Abs
import Mathbin.Tactic.NthRewrite.Default
import Mathbin.Order.Closure

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

variable {α : Type u} [Lattice α] [CommGroup α]

/- warning: mul_sup -> mul_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.30 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.32 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.30 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.32) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.45 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.47 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.45 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.47)] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_sup mul_supₓ'. -/
-- Special case of Bourbaki A.VI.9 (1)
-- c + (a ⊔ b) = (c + a) ⊔ (c + b)
@[to_additive]
theorem mul_sup [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : c * (a ⊔ b) = c * a ⊔ c * b :=
  (OrderIso.mulLeft _).map_sup _ _
#align mul_sup mul_sup
#align add_sup add_sup

/- warning: sup_mul -> sup_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) c) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.105 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.107 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.105 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.107) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.120 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.122 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.120 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.122)] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) c) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) b c))
Case conversion may be inaccurate. Consider using '#align sup_mul sup_mulₓ'. -/
@[to_additive]
theorem sup_mul [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : (a ⊔ b) * c = a * c ⊔ b * c :=
  (OrderIso.mulRight _).map_sup _ _
#align sup_mul sup_mul
#align sup_add sup_add

/- warning: mul_inf -> mul_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.180 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.182 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.180 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.182) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.195 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.197 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.195 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.197)] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a b)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) c b))
Case conversion may be inaccurate. Consider using '#align mul_inf mul_infₓ'. -/
@[to_additive]
theorem mul_inf [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : c * (a ⊓ b) = c * a ⊓ c * b :=
  (OrderIso.mulLeft _).map_inf _ _
#align mul_inf mul_inf
#align add_inf add_inf

/- warning: inf_mul -> inf_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b) c) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.255 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.257 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.255 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.257) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.270 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.272 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.270 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.272)] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a b) c) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a c) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) b c))
Case conversion may be inaccurate. Consider using '#align inf_mul inf_mulₓ'. -/
@[to_additive]
theorem inf_mul [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : (a ⊓ b) * c = a * c ⊓ b * c :=
  (OrderIso.mulRight _).map_inf _ _
#align inf_mul inf_mul
#align inf_add inf_add

/- warning: inv_sup_eq_inv_inf_inv -> inv_sup_eq_inv_inf_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.330 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.332 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.330 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.332) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.345 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.347 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.345 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.347)] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) b))
Case conversion may be inaccurate. Consider using '#align inv_sup_eq_inv_inf_inv inv_sup_eq_inv_inf_invₓ'. -/
-- Special case of Bourbaki A.VI.9 (2)
-- -(a ⊔ b)=(-a) ⊓ (-b)
@[to_additive]
theorem inv_sup_eq_inv_inf_inv [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    (a ⊔ b)⁻¹ = a⁻¹ ⊓ b⁻¹ :=
  (OrderIso.inv α).map_sup _ _
#align inv_sup_eq_inv_inf_inv inv_sup_eq_inv_inf_inv
#align neg_sup_eq_neg_inf_neg neg_sup_eq_neg_inf_neg

/- warning: inv_inf_eq_sup_inv -> inv_inf_eq_sup_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.405 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.407 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.405 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.407) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.420 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.422 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.420 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.422)] (a : α) (b : α), Eq.{succ u1} α (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a b)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) b))
Case conversion may be inaccurate. Consider using '#align inv_inf_eq_sup_inv inv_inf_eq_sup_invₓ'. -/
-- -(a ⊓ b) = -a ⊔ -b
@[to_additive]
theorem inv_inf_eq_sup_inv [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a ⊓ b)⁻¹ = a⁻¹ ⊔ b⁻¹ :=
  (OrderIso.inv α).map_inf _ _
#align inv_inf_eq_sup_inv inv_inf_eq_sup_inv
#align neg_inf_eq_sup_neg neg_inf_eq_sup_neg

/- warning: inf_mul_sup -> inf_mul_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.480 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.482 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.480 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.482) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.495 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.497 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.495 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.497)] (a : α) (b : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a b) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b)
Case conversion may be inaccurate. Consider using '#align inf_mul_sup inf_mul_supₓ'. -/
-- Bourbaki A.VI.10 Prop 7
-- a ⊓ b + (a ⊔ b) = a + b
@[to_additive]
theorem inf_mul_sup [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a ⊓ b) * (a ⊔ b) = a * b :=
  calc
    (a ⊓ b) * (a ⊔ b) = (a ⊓ b) * (a * b * (b⁻¹ ⊔ a⁻¹)) := by
      rw [mul_sup b⁻¹ a⁻¹ (a * b), mul_inv_cancel_right, mul_inv_cancel_comm]
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.918 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.920 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.918 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.920) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.933 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.935 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.933 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.935)] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_eq_inv_inf_one LatticeOrderedCommGroup.neg_eq_inv_inf_oneₓ'. -/
-- a⁻ = -(a ⊓ 0)
@[to_additive]
theorem neg_eq_inv_inf_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁻ = (a ⊓ 1)⁻¹ := by
  rw [m_neg_part_def, ← inv_inj, inv_sup_eq_inv_inf_inv, inv_inv, inv_inv, inv_one]
#align lattice_ordered_comm_group.neg_eq_inv_inf_one LatticeOrderedCommGroup.neg_eq_inv_inf_one
#align lattice_ordered_comm_group.neg_eq_neg_inf_zero LatticeOrderedCommGroup.neg_eq_neg_inf_zero

/- warning: lattice_ordered_comm_group.le_mabs -> LatticeOrderedCommGroup.le_mabs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.le_mabs LatticeOrderedCommGroup.le_mabsₓ'. -/
@[to_additive le_abs]
theorem le_mabs (a : α) : a ≤ |a| :=
  le_sup_left
#align lattice_ordered_comm_group.le_mabs LatticeOrderedCommGroup.le_mabs
#align lattice_ordered_comm_group.le_abs LatticeOrderedCommGroup.le_abs

/- warning: lattice_ordered_comm_group.inv_le_abs -> LatticeOrderedCommGroup.inv_le_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.inv_le_abs LatticeOrderedCommGroup.inv_le_absₓ'. -/
-- -a ≤ |a|
@[to_additive]
theorem inv_le_abs (a : α) : a⁻¹ ≤ |a| :=
  le_sup_right
#align lattice_ordered_comm_group.inv_le_abs LatticeOrderedCommGroup.inv_le_abs
#align lattice_ordered_comm_group.neg_le_abs LatticeOrderedCommGroup.neg_le_abs

/- warning: lattice_ordered_comm_group.one_le_pos -> LatticeOrderedCommGroup.one_le_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a)
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_le_one_iff LatticeOrderedCommGroup.pos_le_one_iffₓ'. -/
-- pos_nonpos_iff
@[to_additive]
theorem pos_le_one_iff {a : α} : a⁺ ≤ 1 ↔ a ≤ 1 := by
  rw [m_pos_part_def, sup_le_iff, and_iff_left le_rfl]
#align lattice_ordered_comm_group.pos_le_one_iff LatticeOrderedCommGroup.pos_le_one_iff
#align lattice_ordered_comm_group.pos_nonpos_iff LatticeOrderedCommGroup.pos_nonpos_iff

/- warning: lattice_ordered_comm_group.neg_le_one_iff -> LatticeOrderedCommGroup.neg_le_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_le_one_iff LatticeOrderedCommGroup.neg_le_one_iffₓ'. -/
-- neg_nonpos_iff
@[to_additive]
theorem neg_le_one_iff {a : α} : a⁻ ≤ 1 ↔ a⁻¹ ≤ 1 := by
  rw [m_neg_part_def, sup_le_iff, and_iff_left le_rfl]
#align lattice_ordered_comm_group.neg_le_one_iff LatticeOrderedCommGroup.neg_le_one_iff
#align lattice_ordered_comm_group.neg_nonpos_iff LatticeOrderedCommGroup.neg_nonpos_iff

/- warning: lattice_ordered_comm_group.pos_eq_one_iff -> LatticeOrderedCommGroup.pos_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_eq_one_iff LatticeOrderedCommGroup.pos_eq_one_iffₓ'. -/
@[to_additive]
theorem pos_eq_one_iff {a : α} : a⁺ = 1 ↔ a ≤ 1 :=
  sup_eq_right
#align lattice_ordered_comm_group.pos_eq_one_iff LatticeOrderedCommGroup.pos_eq_one_iff
#align lattice_ordered_comm_group.pos_eq_zero_iff LatticeOrderedCommGroup.pos_eq_zero_iff

/- warning: lattice_ordered_comm_group.neg_eq_one_iff' -> LatticeOrderedCommGroup.neg_eq_one_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] {a : α}, Iff (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_eq_one_iff' LatticeOrderedCommGroup.neg_eq_one_iff'ₓ'. -/
@[to_additive]
theorem neg_eq_one_iff' {a : α} : a⁻ = 1 ↔ a⁻¹ ≤ 1 :=
  sup_eq_right
#align lattice_ordered_comm_group.neg_eq_one_iff' LatticeOrderedCommGroup.neg_eq_one_iff'
#align lattice_ordered_comm_group.neg_eq_zero_iff' LatticeOrderedCommGroup.neg_eq_zero_iff'

/- warning: lattice_ordered_comm_group.neg_eq_one_iff -> LatticeOrderedCommGroup.neg_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] {a : α}, Iff (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (Mul.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] {a : α}, Iff (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_eq_one_iff LatticeOrderedCommGroup.neg_eq_one_iffₓ'. -/
@[to_additive]
theorem neg_eq_one_iff [CovariantClass α α Mul.mul LE.le] {a : α} : a⁻ = 1 ↔ 1 ≤ a := by
  rw [le_antisymm_iff, neg_le_one_iff, inv_le_one', and_iff_left (one_le_neg _)]
#align lattice_ordered_comm_group.neg_eq_one_iff LatticeOrderedCommGroup.neg_eq_one_iff
#align lattice_ordered_comm_group.neg_eq_zero_iff LatticeOrderedCommGroup.neg_eq_zero_iff

/- warning: lattice_ordered_comm_group.m_le_pos -> LatticeOrderedCommGroup.m_le_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.m_le_pos LatticeOrderedCommGroup.m_le_posₓ'. -/
@[to_additive le_pos]
theorem m_le_pos (a : α) : a ≤ a⁺ :=
  le_sup_left
#align lattice_ordered_comm_group.m_le_pos LatticeOrderedCommGroup.m_le_pos
#align lattice_ordered_comm_group.le_pos LatticeOrderedCommGroup.le_pos

/- warning: lattice_ordered_comm_group.inv_le_neg -> LatticeOrderedCommGroup.inv_le_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)
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
theorem pos_eq_neg_inv (a : α) : a⁺ = a⁻¹⁻ := by rw [neg_eq_pos_inv, inv_inv]
#align lattice_ordered_comm_group.pos_eq_neg_inv LatticeOrderedCommGroup.pos_eq_neg_inv
#align lattice_ordered_comm_group.pos_eq_neg_neg LatticeOrderedCommGroup.pos_eq_neg_neg

/- warning: lattice_ordered_comm_group.pos_div_neg -> LatticeOrderedCommGroup.pos_div_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1593 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1595 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1593 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1595) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1608 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1610 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1608 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1610)] (a : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)) a
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1714 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1716 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1714 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1716) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1729 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1731 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1729 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1731)] (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_inf_neg_eq_one LatticeOrderedCommGroup.pos_inf_neg_eq_oneₓ'. -/
-- Bourbaki A.VI.12  Prop 9 a)
-- a⁺ ⊓ a⁻ = 0 (`a⁺` and `a⁻` are co-prime, and, since they are positive, disjoint)
@[to_additive]
theorem pos_inf_neg_eq_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁺ ⊓ a⁻ = 1 := by
  rw [← mul_right_inj (a⁻)⁻¹, mul_inf, mul_one, mul_left_inv, mul_comm, ← div_eq_mul_inv,
    pos_div_neg, neg_eq_inv_inf_one, inv_inv]
#align lattice_ordered_comm_group.pos_inf_neg_eq_one LatticeOrderedCommGroup.pos_inf_neg_eq_one
#align lattice_ordered_comm_group.pos_inf_neg_eq_zero LatticeOrderedCommGroup.pos_inf_neg_eq_zero

/- warning: lattice_ordered_comm_group.sup_eq_mul_pos_div -> LatticeOrderedCommGroup.sup_eq_mul_pos_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) b (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1819 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1821 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1819 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1821) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1834 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1836 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1834 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.1836)] (a : α) (b : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) b (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2001 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2003 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2001 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2003) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2016 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2018 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2016 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2018)] (a : α) (b : α), Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a b) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.inf_eq_div_pos_div LatticeOrderedCommGroup.inf_eq_div_pos_divₓ'. -/
-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊓b = a - (a - b)⁺
@[to_additive]
theorem inf_eq_div_pos_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : a ⊓ b = a / (a / b)⁺ :=
  calc
    a ⊓ b = a * 1 ⊓ a * (b / a) := by
      rw [mul_one a, div_eq_mul_inv, mul_comm b, mul_inv_cancel_left]
    _ = a * (1 ⊓ b / a) := by rw [← mul_inf 1 (b / a) a]
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a b) (And (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) b)) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) b) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2470 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2472 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2470 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2472) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2485 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2487 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2485 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2487)] (a : α) (b : α), Iff (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a b) (And (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) b)) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) b) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a)))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2662 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2664 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2662 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2664) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2677 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2679 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2677 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2679)] (a : α), Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2823 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2825 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2823 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2825) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2838 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2840 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2838 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2840)] (a : α), Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2981 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2983 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2981 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2983) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2996 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2998 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2996 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.2998)] (a : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3068 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3070 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3068 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3070) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3083 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3085 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3083 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3085)] (a : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.pos_mul_neg LatticeOrderedCommGroup.pos_mul_negₓ'. -/
-- |a| = a⁺ - a⁻
@[to_additive]
theorem pos_mul_neg [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : |a| = a⁺ * a⁻ :=
  by
  rw [m_pos_part_def, sup_mul, one_mul, m_neg_part_def, mul_sup, mul_one, mul_inv_self, sup_assoc, ←
    @sup_assoc _ _ a, sup_eq_right.2 le_sup_right]
  exact (sup_eq_left.2 <| one_le_abs a).symm
#align lattice_ordered_comm_group.pos_mul_neg LatticeOrderedCommGroup.pos_mul_neg
#align lattice_ordered_comm_group.pos_add_neg LatticeOrderedCommGroup.pos_add_neg

/- warning: lattice_ordered_comm_group.sup_div_inf_eq_abs_div -> LatticeOrderedCommGroup.sup_div_inf_eq_abs_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3179 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3181 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3179 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3181) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3194 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3196 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3194 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3196)] (a : α) (b : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a b)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.sup_div_inf_eq_abs_div LatticeOrderedCommGroup.sup_div_inf_eq_abs_divₓ'. -/
-- a ⊔ b - (a ⊓ b) = |b - a|
@[to_additive]
theorem sup_div_inf_eq_abs_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) :
    (a ⊔ b) / (a ⊓ b) = |b / a| := by
  rw [sup_eq_mul_pos_div, inf_comm, inf_eq_div_pos_div, div_eq_mul_inv, div_eq_mul_inv b ((b / a)⁺),
    mul_inv_rev, inv_inv, mul_comm, ← mul_assoc, inv_mul_cancel_right, pos_eq_neg_inv (a / b),
    div_eq_mul_inv a b, mul_inv_rev, ← div_eq_mul_inv, inv_inv, ← pos_mul_neg]
#align lattice_ordered_comm_group.sup_div_inf_eq_abs_div LatticeOrderedCommGroup.sup_div_inf_eq_abs_div
#align lattice_ordered_comm_group.sup_sub_inf_eq_abs_sub LatticeOrderedCommGroup.sup_sub_inf_eq_abs_sub

/- warning: lattice_ordered_comm_group.sup_sq_eq_mul_mul_abs_div -> LatticeOrderedCommGroup.sup_sq_eq_mul_mul_abs_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3310 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3312 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3310 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3312) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3325 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3327 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3325 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3327)] (a : α) (b : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a b) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a)))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a b) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3414 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3416 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3414 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3416) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3429 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3431 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3429 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3431)] (a : α) (b : α), Eq.{succ u1} α (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a b) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a)))
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
  forall (α : Type.{u1}) [s : Lattice.{u1} α] [_inst_3 : CommGroup.{u1} α] [_inst_4 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_3))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α s)))))], DistribLattice.{u1} α
but is expected to have type
  forall (α : Type.{u1}) [s : Lattice.{u1} α] [_inst_3 : CommGroup.{u1} α] [_inst_4 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3525 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3527 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_3)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3525 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3527) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3540 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3542 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α s)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3540 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3542)], DistribLattice.{u1} α
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a c) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) b c)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3722 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3724 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3722 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3724) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3737 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3739 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3737 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.3739)] (a : α) (b : α) (c : α), Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a c) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) b c)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
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
    _ = (b ⊔ a ⊔ c) / (b ⊓ a ⊔ c) * (((b ⊔ a) ⊓ c) / (b ⊓ a ⊓ c)) := by
      rw [← sup_inf_right, ← inf_sup_right, sup_assoc, @sup_comm _ _ c (a ⊔ c), sup_right_idem,
        sup_assoc, inf_assoc, @inf_comm _ _ c (a ⊓ c), inf_right_idem, inf_assoc]
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) a) -> (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) a)
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
  forall {α : Type.{u1}} [_inst_3 : LinearOrder.{u1} α] [_inst_4 : CommGroup.{u1} α] {x : α}, (LT.lt.{u1} α (Preorder.toHasLt.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_3))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_4)))))))) (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α (LinearOrder.toLattice.{u1} α _inst_3) _inst_4) x)) -> (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α (LinearOrder.toLattice.{u1} α _inst_3) _inst_4) x) x)
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) -> (Eq.{succ u1} α (PosPart.pos.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasPosPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a)) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))))) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4679 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4681 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4679 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4681) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4694 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4696 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4694 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4696)] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2)))))))) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) a))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_of_le_one LatticeOrderedCommGroup.neg_of_le_oneₓ'. -/
-- neg_of_nonpos
@[to_additive]
theorem neg_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : a ≤ 1) : a⁻ = a⁻¹ :=
  sup_eq_left.2 <| one_le_inv'.2 h
#align lattice_ordered_comm_group.neg_of_le_one LatticeOrderedCommGroup.neg_of_le_one
#align lattice_ordered_comm_group.neg_of_nonpos LatticeOrderedCommGroup.neg_of_nonpos

/- warning: lattice_ordered_comm_group.neg_of_one_le -> LatticeOrderedCommGroup.neg_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) a) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4743 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4745 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4743 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4745) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4758 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4760 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4758 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4760)] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) a) -> (Eq.{succ u1} α (NegPart.neg.{u1} α (LatticeOrderedCommGroup.hasOneLatticeHasNegPart.{u1} α _inst_1 _inst_2) a) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.neg_of_one_le LatticeOrderedCommGroup.neg_of_one_leₓ'. -/
-- neg_of_nonneg'
@[to_additive]
theorem neg_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : 1 ≤ a) : a⁻ = 1 :=
  neg_eq_one_iff.mpr h
#align lattice_ordered_comm_group.neg_of_one_le LatticeOrderedCommGroup.neg_of_one_le
#align lattice_ordered_comm_group.neg_of_nonneg LatticeOrderedCommGroup.neg_of_nonneg

/- warning: lattice_ordered_comm_group.mabs_of_one_le -> LatticeOrderedCommGroup.mabs_of_one_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))))) a) -> (Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4802 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4804 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4802 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4804) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4817 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4819 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4817 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4819)] (a : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))))) a) -> (Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.mabs_of_one_le LatticeOrderedCommGroup.mabs_of_one_leₓ'. -/
-- 0 ≤ a implies |a| = a
@[to_additive abs_of_nonneg]
theorem mabs_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : 1 ≤ a) : |a| = a :=
  sup_eq_left.2 <| Left.inv_le_self h
#align lattice_ordered_comm_group.mabs_of_one_le LatticeOrderedCommGroup.mabs_of_one_le
#align lattice_ordered_comm_group.abs_of_nonneg LatticeOrderedCommGroup.abs_of_nonneg

/- warning: lattice_ordered_comm_group.mabs_mabs -> LatticeOrderedCommGroup.mabs_mabs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4864 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4866 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4864 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4866) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4879 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4881 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4879 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4881)] (a : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a)
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.mabs_mabs LatticeOrderedCommGroup.mabs_mabsₓ'. -/
/-- The unary operation of taking the absolute value is idempotent. -/
@[simp, to_additive abs_abs "The unary operation of taking the absolute value is idempotent."]
theorem mabs_mabs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : ||a|| = |a| :=
  mabs_of_one_le _ (one_le_abs _)
#align lattice_ordered_comm_group.mabs_mabs LatticeOrderedCommGroup.mabs_mabs
#align lattice_ordered_comm_group.abs_abs LatticeOrderedCommGroup.abs_abs

/- warning: lattice_ordered_comm_group.mabs_sup_div_sup_le_mabs -> LatticeOrderedCommGroup.mabs_sup_div_sup_le_mabs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4929 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4931 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4929 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4931) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4944 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4946 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4944 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.4946)] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a c) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5036 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5038 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5036 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5038) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5051 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5053 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5051 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5053)] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a c) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) a c) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) b c)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5143 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5145 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5143 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5145) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5158 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5160 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5158 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5160)] (a : α) (b : α) (c : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) a c) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) b c))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) a c) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) b c)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5255 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5257 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5255 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5257) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5270 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5272 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5270 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5272)] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) a b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) b))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] (a : α) (b : α), Eq.{succ u1} α (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b)) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) b a))
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
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (a : α) (b : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) b))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : CommGroup.{u1} α] [_inst_3 : CovariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5446 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5448 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5446 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5448) (fun (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5461 : α) (x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5463 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5461 x._@.Mathlib.Algebra.Order.LatticeGroup._hyg.5463)] (a : α) (b : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) a) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) b))) (Abs.abs.{u1} α (Inv.toHasAbs.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2)))) a b))
Case conversion may be inaccurate. Consider using '#align lattice_ordered_comm_group.abs_abs_div_abs_le LatticeOrderedCommGroup.abs_abs_div_abs_leₓ'. -/
-- | |a| - |b| | ≤ |a - b|
@[to_additive]
theorem abs_abs_div_abs_le [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : ||a| / |b|| ≤ |a / b| :=
  by
  rw [abs_eq_sup_inv, sup_le_iff]
  constructor
  · apply div_le_iff_le_mul.2
    convert mabs_mul_le (a / b) b
    rw [div_mul_cancel']
    exact covariant_swap_mul_le_of_covariant_mul_le α
  · rw [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_inv_le_iff_le_mul, abs_inv_comm]
    convert mabs_mul_le (b / a) a
    · rw [div_mul_cancel']
#align lattice_ordered_comm_group.abs_abs_div_abs_le LatticeOrderedCommGroup.abs_abs_div_abs_le
#align lattice_ordered_comm_group.abs_abs_sub_abs_le LatticeOrderedCommGroup.abs_abs_sub_abs_le

end LatticeOrderedCommGroup

namespace LatticeOrderedAddCommGroup

variable {β : Type u} [Lattice β] [AddCommGroup β]

section Solid

#print LatticeOrderedAddCommGroup.IsSolid /-
/-- A subset `s ⊆ β`, with `β` an `add_comm_group` with a `lattice` structure, is solid if for
all `x ∈ s` and all `y ∈ β` such that `|y| ≤ |x|`, then `y ∈ s`. -/
def IsSolid (s : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, |y| ≤ |x| → y ∈ s
#align lattice_ordered_add_comm_group.is_solid LatticeOrderedAddCommGroup.IsSolid
-/

#print LatticeOrderedAddCommGroup.solidClosure /-
/-- The solid closure of a subset `s` is the smallest superset of `s` that is solid. -/
def solidClosure (s : Set β) : Set β :=
  { y | ∃ x ∈ s, |y| ≤ |x| }
#align lattice_ordered_add_comm_group.solid_closure LatticeOrderedAddCommGroup.solidClosure
-/

#print LatticeOrderedAddCommGroup.isSolid_solidClosure /-
theorem isSolid_solidClosure (s : Set β) : IsSolid (solidClosure s) := fun x ⟨y, hy, hxy⟩ z hzx =>
  ⟨y, hy, hzx.trans hxy⟩
#align lattice_ordered_add_comm_group.is_solid_solid_closure LatticeOrderedAddCommGroup.isSolid_solidClosure
-/

#print LatticeOrderedAddCommGroup.solidClosure_min /-
theorem solidClosure_min (s t : Set β) (h1 : s ⊆ t) (h2 : IsSolid t) : solidClosure s ⊆ t :=
  fun _ ⟨_, hy, hxy⟩ => h2 (h1 hy) hxy
#align lattice_ordered_add_comm_group.solid_closure_min LatticeOrderedAddCommGroup.solidClosure_min
-/

end Solid

end LatticeOrderedAddCommGroup

