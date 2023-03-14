/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module analysis.normed.order.lattice
! leanprover-community/mathlib commit 17ef379e997badd73e5eabb4d38f11919ab3c4b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order.Lattice
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Algebra.Order.LatticeGroup

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `normed_lattice_add_comm_group` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/


/-!
### Normed lattice orderd groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/


-- mathport name: abs
local notation "|" a "|" => abs a

#print NormedLatticeAddCommGroup /-
/--
Let `α` be a normed commutative group equipped with a partial order covariant with addition, with
respect which `α` forms a lattice. Suppose that `α` is *solid*, that is to say, for `a` and `b` in
`α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `‖a‖ ≤ ‖b‖`. Then `α` is
said to be a normed lattice ordered group.
-/
class NormedLatticeAddCommGroup (α : Type _) extends NormedAddCommGroup α, Lattice α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  solid : ∀ a b : α, |a| ≤ |b| → ‖a‖ ≤ ‖b‖
#align normed_lattice_add_comm_group NormedLatticeAddCommGroup
-/

/- warning: solid -> solid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))) a) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))) b)) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) a) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] {a : α} {b : α}, (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))) a) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))) b)) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) a) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) b))
Case conversion may be inaccurate. Consider using '#align solid solidₓ'. -/
theorem solid {α : Type _} [NormedLatticeAddCommGroup α] {a b : α} (h : |a| ≤ |b|) : ‖a‖ ≤ ‖b‖ :=
  NormedLatticeAddCommGroup.solid a b h
#align solid solid

instance : NormedLatticeAddCommGroup ℝ
    where
  add_le_add_left _ _ h _ := add_le_add le_rfl h
  solid _ _ := id

#print NormedLatticeAddCommGroup.toOrderedAddCommGroup /-
-- see Note [lower instance priority]
/-- A normed lattice ordered group is an ordered additive commutative group
-/
instance (priority := 100) NormedLatticeAddCommGroup.toOrderedAddCommGroup {α : Type _}
    [h : NormedLatticeAddCommGroup α] : OrderedAddCommGroup α :=
  { h with }
#align normed_lattice_add_comm_group_to_ordered_add_comm_group NormedLatticeAddCommGroup.toOrderedAddCommGroup
-/

variable {α : Type _} [NormedLatticeAddCommGroup α]

open LatticeOrderedCommGroup

/- warning: dual_solid -> dual_solid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (a : α) (b : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (NormedLatticeAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1)))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) b (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))) b)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) a (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))) a))) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) a) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (a : α) (b : α), (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (NormedLatticeAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1)))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)) b (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))))) b)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)) a (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))))) a))) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) a) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) b))
Case conversion may be inaccurate. Consider using '#align dual_solid dual_solidₓ'. -/
theorem dual_solid (a b : α) (h : b ⊓ -b ≤ a ⊓ -a) : ‖a‖ ≤ ‖b‖ :=
  by
  apply solid
  rw [abs_eq_sup_neg]
  nth_rw 1 [← neg_neg a]
  rw [← neg_inf_eq_sup_neg]
  rw [abs_eq_sup_neg]
  nth_rw 1 [← neg_neg b]
  rwa [← neg_inf_eq_sup_neg, neg_le_neg_iff, @inf_comm _ _ _ b, @inf_comm _ _ _ a]
#align dual_solid dual_solid

-- see Note [lower instance priority]
/-- Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
instance (priority := 100) : NormedLatticeAddCommGroup αᵒᵈ :=
  { OrderDual.orderedAddCommGroup, OrderDual.normedAddCommGroup with solid := dual_solid }

/- warning: norm_abs_eq_norm -> norm_abs_eq_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (a : α), Eq.{1} Real (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))) a)) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (a : α), Eq.{1} Real (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))) a)) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) a)
Case conversion may be inaccurate. Consider using '#align norm_abs_eq_norm norm_abs_eq_normₓ'. -/
theorem norm_abs_eq_norm (a : α) : ‖|a|‖ = ‖a‖ :=
  (solid (abs_abs a).le).antisymm (solid (abs_abs a).symm.le)
#align norm_abs_eq_norm norm_abs_eq_norm

/- warning: norm_inf_sub_inf_le_add_norm -> norm_inf_sub_inf_le_add_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (a : α) (b : α) (c : α) (d : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) a b) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) c d))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) a c)) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (a : α) (b : α) (c : α) (d : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)) a b) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)) c d))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) a c)) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) b d)))
Case conversion may be inaccurate. Consider using '#align norm_inf_sub_inf_le_add_norm norm_inf_sub_inf_le_add_normₓ'. -/
theorem norm_inf_sub_inf_le_add_norm (a b c d : α) : ‖a ⊓ b - c ⊓ d‖ ≤ ‖a - c‖ + ‖b - d‖ :=
  by
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine' le_trans (solid _) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (|a - c| + |b - d|) (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊓ b - c ⊓ d| = |a ⊓ b - c ⊓ b + (c ⊓ b - c ⊓ d)| := by rw [sub_add_sub_cancel]
    _ ≤ |a ⊓ b - c ⊓ b| + |c ⊓ b - c ⊓ d| := (abs_add_le _ _)
    _ ≤ |a - c| + |b - d| := by
      apply add_le_add
      · exact abs_inf_sub_inf_le_abs _ _ _
      · rw [@inf_comm _ _ c, @inf_comm _ _ c]
        exact abs_inf_sub_inf_le_abs _ _ _
    
#align norm_inf_sub_inf_le_add_norm norm_inf_sub_inf_le_add_norm

/- warning: norm_sup_sub_sup_le_add_norm -> norm_sup_sub_sup_le_add_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (a : α) (b : α) (c : α) (d : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) a b) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) c d))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) a c)) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) b d)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (a : α) (b : α) (c : α) (d : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) a b) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) c d))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) a c)) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) b d)))
Case conversion may be inaccurate. Consider using '#align norm_sup_sub_sup_le_add_norm norm_sup_sub_sup_le_add_normₓ'. -/
theorem norm_sup_sub_sup_le_add_norm (a b c d : α) : ‖a ⊔ b - c ⊔ d‖ ≤ ‖a - c‖ + ‖b - d‖ :=
  by
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine' le_trans (solid _) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (|a - c| + |b - d|) (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊔ b - c ⊔ d| = |a ⊔ b - c ⊔ b + (c ⊔ b - c ⊔ d)| := by rw [sub_add_sub_cancel]
    _ ≤ |a ⊔ b - c ⊔ b| + |c ⊔ b - c ⊔ d| := (abs_add_le _ _)
    _ ≤ |a - c| + |b - d| := by
      apply add_le_add
      · exact abs_sup_sub_sup_le_abs _ _ _
      · rw [@sup_comm _ _ c, @sup_comm _ _ c]
        exact abs_sup_sub_sup_le_abs _ _ _
    
#align norm_sup_sub_sup_le_add_norm norm_sup_sub_sup_le_add_norm

/- warning: norm_inf_le_add -> norm_inf_le_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (x : α) (y : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) x) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (x : α) (y : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) x) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) y))
Case conversion may be inaccurate. Consider using '#align norm_inf_le_add norm_inf_le_addₓ'. -/
theorem norm_inf_le_add (x y : α) : ‖x ⊓ y‖ ≤ ‖x‖ + ‖y‖ :=
  by
  have h : ‖x ⊓ y - 0 ⊓ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_inf_sub_inf_le_add_norm x y 0 0
  simpa only [inf_idem, sub_zero] using h
#align norm_inf_le_add norm_inf_le_add

/- warning: norm_sup_le_add -> norm_sup_le_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (x : α) (y : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) x) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (x : α) (y : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) x) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) y))
Case conversion may be inaccurate. Consider using '#align norm_sup_le_add norm_sup_le_addₓ'. -/
theorem norm_sup_le_add (x y : α) : ‖x ⊔ y‖ ≤ ‖x‖ + ‖y‖ :=
  by
  have h : ‖x ⊔ y - 0 ⊔ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_sup_sub_sup_le_add_norm x y 0 0
  simpa only [sup_idem, sub_zero] using h
#align norm_sup_le_add norm_sup_le_add

/- warning: normed_lattice_add_comm_group_has_continuous_inf -> NormedLatticeAddCommGroup.continuousInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α], ContinuousInf.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))) (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α], ContinuousInf.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))) (Lattice.toInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align normed_lattice_add_comm_group_has_continuous_inf NormedLatticeAddCommGroup.continuousInfₓ'. -/
-- see Note [lower instance priority]
/-- Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
instance (priority := 100) NormedLatticeAddCommGroup.continuousInf : ContinuousInf α :=
  by
  refine' ⟨continuous_iff_continuousAt.2 fun q => tendsto_iff_norm_tendsto_zero.2 <| _⟩
  have : ∀ p : α × α, ‖p.1 ⊓ p.2 - q.1 ⊓ q.2‖ ≤ ‖p.1 - q.1‖ + ‖p.2 - q.2‖ := fun _ =>
    norm_inf_sub_inf_le_add_norm _ _ _ _
  refine' squeeze_zero (fun e => norm_nonneg _) this _
  convert
    ((continuous_fst.tendsto q).sub tendsto_const_nhds).norm.add
      ((continuous_snd.tendsto q).sub tendsto_const_nhds).norm
  simp
#align normed_lattice_add_comm_group_has_continuous_inf NormedLatticeAddCommGroup.continuousInf

/- warning: normed_lattice_add_comm_group_has_continuous_sup -> NormedLatticeAddCommGroup.continuousSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : NormedLatticeAddCommGroup.{u1} α], ContinuousSup.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_2))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : NormedLatticeAddCommGroup.{u1} α], ContinuousSup.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_2))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align normed_lattice_add_comm_group_has_continuous_sup NormedLatticeAddCommGroup.continuousSupₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) NormedLatticeAddCommGroup.continuousSup {α : Type _}
    [NormedLatticeAddCommGroup α] : ContinuousSup α :=
  OrderDual.continuousSup αᵒᵈ
#align normed_lattice_add_comm_group_has_continuous_sup NormedLatticeAddCommGroup.continuousSup

#print NormedLatticeAddCommGroup.toTopologicalLattice /-
-- see Note [lower instance priority]
/--
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
instance (priority := 100) NormedLatticeAddCommGroup.toTopologicalLattice : TopologicalLattice α :=
  TopologicalLattice.mk
#align normed_lattice_add_comm_group_topological_lattice NormedLatticeAddCommGroup.toTopologicalLattice
-/

/- warning: norm_abs_sub_abs -> norm_abs_sub_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (a : α) (b : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))) a) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))) b))) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (a : α) (b : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))) a) (Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1))))))) (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)))) b))) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) a b))
Case conversion may be inaccurate. Consider using '#align norm_abs_sub_abs norm_abs_sub_absₓ'. -/
theorem norm_abs_sub_abs (a b : α) : ‖|a| - |b|‖ ≤ ‖a - b‖ :=
  solid (LatticeOrderedCommGroup.abs_abs_sub_abs_le _ _)
#align norm_abs_sub_abs norm_abs_sub_abs

/- warning: norm_sup_sub_sup_le_norm -> norm_sup_sub_sup_le_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) x z) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) y z))) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) x z) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) y z))) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) x y))
Case conversion may be inaccurate. Consider using '#align norm_sup_sub_sup_le_norm norm_sup_sub_sup_le_normₓ'. -/
theorem norm_sup_sub_sup_le_norm (x y z : α) : ‖x ⊔ z - y ⊔ z‖ ≤ ‖x - y‖ :=
  solid (abs_sup_sub_sup_le_abs x y z)
#align norm_sup_sub_sup_le_norm norm_sup_sub_sup_le_norm

/- warning: norm_inf_sub_inf_le_norm -> norm_inf_sub_inf_le_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) x z) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) y z))) (Norm.norm.{u1} α (NormedAddCommGroup.toHasNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (x : α) (y : α) (z : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)) x z) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1)) y z))) (Norm.norm.{u1} α (NormedAddCommGroup.toNorm.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))))) x y))
Case conversion may be inaccurate. Consider using '#align norm_inf_sub_inf_le_norm norm_inf_sub_inf_le_normₓ'. -/
theorem norm_inf_sub_inf_le_norm (x y z : α) : ‖x ⊓ z - y ⊓ z‖ ≤ ‖x - y‖ :=
  solid (abs_inf_sub_inf_le_abs x y z)
#align norm_inf_sub_inf_le_norm norm_inf_sub_inf_le_norm

/- warning: lipschitz_with_sup_right -> lipschitzWith_sup_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (z : α), LipschitzWith.{u1, u1} α α (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))) (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (fun (x : α) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) x z)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedLatticeAddCommGroup.{u1} α] (z : α), LipschitzWith.{u1, u1} α α (EMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toEMetricSpace.{u1} α (NormedAddCommGroup.toMetricSpace.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))) (EMetricSpace.toPseudoEMetricSpace.{u1} α (MetricSpace.toEMetricSpace.{u1} α (NormedAddCommGroup.toMetricSpace.{u1} α (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} α _inst_1)))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (fun (x : α) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (NormedLatticeAddCommGroup.toLattice.{u1} α _inst_1))) x z)
Case conversion may be inaccurate. Consider using '#align lipschitz_with_sup_right lipschitzWith_sup_rightₓ'. -/
theorem lipschitzWith_sup_right (z : α) : LipschitzWith 1 fun x => x ⊔ z :=
  LipschitzWith.of_dist_le_mul fun x y =>
    by
    rw [Nonneg.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact norm_sup_sub_sup_le_norm x y z
#align lipschitz_with_sup_right lipschitzWith_sup_right

#print lipschitzWith_pos /-
theorem lipschitzWith_pos : LipschitzWith 1 (PosPart.pos : α → α) :=
  lipschitzWith_sup_right 0
#align lipschitz_with_pos lipschitzWith_pos
-/

#print continuous_pos /-
theorem continuous_pos : Continuous (PosPart.pos : α → α) :=
  LipschitzWith.continuous lipschitzWith_pos
#align continuous_pos continuous_pos
-/

#print continuous_neg' /-
theorem continuous_neg' : Continuous (NegPart.neg : α → α) :=
  continuous_pos.comp continuous_neg
#align continuous_neg' continuous_neg'
-/

/- warning: is_closed_nonneg -> isClosed_nonneg is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_2 : NormedLatticeAddCommGroup.{u1} E], IsClosed.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} E _inst_2))))) (setOf.{u1} E (fun (x : E) => LE.le.{u1} E (Preorder.toLE.{u1} E (PartialOrder.toPreorder.{u1} E (OrderedAddCommGroup.toPartialOrder.{u1} E (NormedLatticeAddCommGroup.toOrderedAddCommGroup.{u1} E _inst_2)))) (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} E _inst_2)))))))))) x))
but is expected to have type
  forall {E : Type.{u1}} [_inst_2 : NormedLatticeAddCommGroup.{u1} E], IsClosed.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} E _inst_2))))) (setOf.{u1} E (fun (x : E) => LE.le.{u1} E (Preorder.toLE.{u1} E (PartialOrder.toPreorder.{u1} E (OrderedAddCommGroup.toPartialOrder.{u1} E (NormedLatticeAddCommGroup.toOrderedAddCommGroup.{u1} E _inst_2)))) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E (NormedLatticeAddCommGroup.toNormedAddCommGroup.{u1} E _inst_2))))))))) x))
Case conversion may be inaccurate. Consider using '#align is_closed_nonneg isClosed_nonnegₓ'. -/
theorem isClosed_nonneg {E} [NormedLatticeAddCommGroup E] : IsClosed { x : E | 0 ≤ x } :=
  by
  suffices { x : E | 0 ≤ x } = NegPart.neg ⁻¹' {(0 : E)}
    by
    rw [this]
    exact IsClosed.preimage continuous_neg' isClosed_singleton
  ext1 x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, neg_eq_zero_iff]
#align is_closed_nonneg isClosed_nonneg

/- warning: is_closed_le_of_is_closed_nonneg -> isClosed_le_of_isClosed_nonneg is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_2 : OrderedAddCommGroup.{u1} G] [_inst_3 : TopologicalSpace.{u1} G] [_inst_4 : ContinuousSub.{u1} G _inst_3 (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G _inst_2))))], (IsClosed.{u1} G _inst_3 (setOf.{u1} G (fun (x : G) => LE.le.{u1} G (Preorder.toLE.{u1} G (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G _inst_2))) (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G _inst_2))))))))) x))) -> (IsClosed.{u1} (Prod.{u1, u1} G G) (Prod.topologicalSpace.{u1, u1} G G _inst_3 _inst_3) (setOf.{u1} (Prod.{u1, u1} G G) (fun (p : Prod.{u1, u1} G G) => LE.le.{u1} G (Preorder.toLE.{u1} G (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G _inst_2))) (Prod.fst.{u1, u1} G G p) (Prod.snd.{u1, u1} G G p))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_2 : OrderedAddCommGroup.{u1} G] [_inst_3 : TopologicalSpace.{u1} G] [_inst_4 : ContinuousSub.{u1} G _inst_3 (SubNegMonoid.toSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G _inst_2))))], (IsClosed.{u1} G _inst_3 (setOf.{u1} G (fun (x : G) => LE.le.{u1} G (Preorder.toLE.{u1} G (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G _inst_2))) (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (OrderedAddCommGroup.toAddCommGroup.{u1} G _inst_2)))))))) x))) -> (IsClosed.{u1} (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_3 _inst_3) (setOf.{u1} (Prod.{u1, u1} G G) (fun (p : Prod.{u1, u1} G G) => LE.le.{u1} G (Preorder.toLE.{u1} G (PartialOrder.toPreorder.{u1} G (OrderedAddCommGroup.toPartialOrder.{u1} G _inst_2))) (Prod.fst.{u1, u1} G G p) (Prod.snd.{u1, u1} G G p))))
Case conversion may be inaccurate. Consider using '#align is_closed_le_of_is_closed_nonneg isClosed_le_of_isClosed_nonnegₓ'. -/
theorem isClosed_le_of_isClosed_nonneg {G} [OrderedAddCommGroup G] [TopologicalSpace G]
    [ContinuousSub G] (h : IsClosed { x : G | 0 ≤ x }) : IsClosed { p : G × G | p.fst ≤ p.snd } :=
  by
  have : { p : G × G | p.fst ≤ p.snd } = (fun p : G × G => p.snd - p.fst) ⁻¹' { x : G | 0 ≤ x } :=
    by
    ext1 p
    simp only [sub_nonneg, Set.preimage_setOf_eq]
  rw [this]
  exact IsClosed.preimage (continuous_snd.sub continuous_fst) h
#align is_closed_le_of_is_closed_nonneg isClosed_le_of_isClosed_nonneg

#print NormedLatticeAddCommGroup.orderClosedTopology /-
-- See note [lower instance priority]
instance (priority := 100) NormedLatticeAddCommGroup.orderClosedTopology {E}
    [NormedLatticeAddCommGroup E] : OrderClosedTopology E :=
  ⟨isClosed_le_of_isClosed_nonneg isClosed_nonneg⟩
#align normed_lattice_add_comm_group.order_closed_topology NormedLatticeAddCommGroup.orderClosedTopology
-/

