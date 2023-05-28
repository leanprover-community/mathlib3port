/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module analysis.normed_space.units
! leanprover-community/mathlib commit 6cf5900728239efa287df7761ec2a1ac9cf39b29
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Ring.Ideal
import Mathbin.Analysis.SpecificLimits.Normed

/-!
# The group of units of a complete normed ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `one_sub`, `add` and `unit_of_nearby` state, in varying forms, that perturbations
of a unit are units.  The latter two are not stated in their optimal form; more precise versions
would use the spectral radius.

The first main result is `is_open`:  the group of units of a complete normed ring is an open subset
of the ring.

The function `inverse` (defined in `algebra.ring`), for a ring `R`, sends `a : R` to `a⁻¹` if `a` is
a unit and 0 if not.  The other major results of this file (notably `inverse_add`,
`inverse_add_norm` and `inverse_add_norm_diff_nth_order`) cover the asymptotic properties of
`inverse (x + t)` as `t → 0`.

-/


noncomputable section

open Topology

variable {R : Type _} [NormedRing R] [CompleteSpace R]

namespace Units

/- warning: units.one_sub -> Units.oneSub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (t : R), (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) t) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (t : R), (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) t) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align units.one_sub Units.oneSubₓ'. -/
/-- In a complete normed ring, a perturbation of `1` by an element `t` of distance less than `1`
from `1` is a unit.  Here we construct its `units` structure.  -/
@[simps coe]
def oneSub (t : R) (h : ‖t‖ < 1) : Rˣ where
  val := 1 - t
  inv := ∑' n : ℕ, t ^ n
  val_inv := mul_neg_geom_series t h
  inv_val := geom_series_mul_neg t h
#align units.one_sub Units.oneSub

/- warning: units.add -> Units.add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (t : R), (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) t) (Inv.inv.{0} Real Real.hasInv (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) x))))) -> (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (t : R), (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) t) (Inv.inv.{0} Real Real.instInvReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x))))) -> (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align units.add Units.addₓ'. -/
/-- In a complete normed ring, a perturbation of a unit `x` by an element `t` of distance less than
`‖x⁻¹‖⁻¹` from `x` is a unit.  Here we construct its `units` structure. -/
@[simps coe]
def add (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
  Units.copy
    (-- to make `coe_add` true definitionally, for convenience
      x *
      Units.oneSub (-(↑x⁻¹ * t))
        (by
          nontriviality R using zero_lt_one
          have hpos : 0 < ‖(↑x⁻¹ : R)‖ := Units.norm_pos x⁻¹
          calc
            ‖-(↑x⁻¹ * t)‖ = ‖↑x⁻¹ * t‖ := by rw [norm_neg]
            _ ≤ ‖(↑x⁻¹ : R)‖ * ‖t‖ := (norm_mul_le ↑x⁻¹ _)
            _ < ‖(↑x⁻¹ : R)‖ * ‖(↑x⁻¹ : R)‖⁻¹ := by nlinarith only [h, hpos]
            _ = 1 := mul_inv_cancel (ne_of_gt hpos)
            ))
    (x + t) (by simp [mul_add]) _ rfl
#align units.add Units.add

/- warning: units.unit_of_nearby -> Units.ofNearby is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (y : R), (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) y ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x))) (Inv.inv.{0} Real Real.hasInv (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) x))))) -> (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (y : R), (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) y (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x))) (Inv.inv.{0} Real Real.instInvReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x))))) -> (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align units.unit_of_nearby Units.ofNearbyₓ'. -/
/-- In a complete normed ring, an element `y` of distance less than `‖x⁻¹‖⁻¹` from `x` is a unit.
Here we construct its `units` structure. -/
@[simps coe]
def ofNearby (x : Rˣ) (y : R) (h : ‖y - x‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ :=
  Units.copy (x.add (y - x : R) h) y (by simp) _ rfl
#align units.unit_of_nearby Units.ofNearby

/- warning: units.is_open -> Units.isOpen is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], IsOpen.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (setOf.{u1} R (fun (x : R) => IsUnit.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], IsOpen.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (setOf.{u1} R (fun (x : R) => IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x))
Case conversion may be inaccurate. Consider using '#align units.is_open Units.isOpenₓ'. -/
/-- The group of units of a complete normed ring is an open subset of the ring. -/
protected theorem isOpen : IsOpen { x : R | IsUnit x } :=
  by
  nontriviality R
  apply metric.is_open_iff.mpr
  rintro x' ⟨x, rfl⟩
  refine' ⟨‖(↑x⁻¹ : R)‖⁻¹, _root_.inv_pos.mpr (Units.norm_pos x⁻¹), _⟩
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact (x.unit_of_nearby y hy).IsUnit
#align units.is_open Units.isOpen

/- warning: units.nhds -> Units.nhds is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))), Membership.Mem.{u1, u1} (Set.{u1} R) (Filter.{u1} R) (Filter.hasMem.{u1} R) (setOf.{u1} R (fun (x : R) => IsUnit.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)) x)) (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))), Membership.mem.{u1, u1} (Set.{u1} R) (Filter.{u1} R) (instMembershipSetFilter.{u1} R) (setOf.{u1} R (fun (x : R) => IsUnit.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x)) (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x))
Case conversion may be inaccurate. Consider using '#align units.nhds Units.nhdsₓ'. -/
protected theorem nhds (x : Rˣ) : { x : R | IsUnit x } ∈ 𝓝 (x : R) :=
  IsOpen.mem_nhds Units.isOpen x.IsUnit
#align units.nhds Units.nhds

end Units

namespace nonunits

/- warning: nonunits.subset_compl_ball -> nonunits.subset_compl_ball is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], HasSubset.Subset.{u1} (Set.{u1} R) (Set.hasSubset.{u1} R) (nonunits.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HasCompl.compl.{u1} (Set.{u1} R) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} R) (Set.booleanAlgebra.{u1} R)) (Metric.ball.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], HasSubset.Subset.{u1} (Set.{u1} R) (Set.instHasSubsetSet.{u1} R) (nonunits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (HasCompl.compl.{u1} (Set.{u1} R) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} R) (Set.instBooleanAlgebraSet.{u1} R)) (Metric.ball.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align nonunits.subset_compl_ball nonunits.subset_compl_ballₓ'. -/
/-- The `nonunits` in a complete normed ring are contained in the complement of the ball of radius
`1` centered at `1 : R`. -/
theorem subset_compl_ball : nonunits R ⊆ Metric.ball (1 : R) 1ᶜ :=
  Set.subset_compl_comm.mp fun x hx => by
    simpa [sub_sub_self, Units.oneSub_val] using
      (Units.oneSub (1 - x) (by rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hx)).IsUnit
#align nonunits.subset_compl_ball nonunits.subset_compl_ball

/- warning: nonunits.is_closed -> nonunits.isClosed is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], IsClosed.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (nonunits.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], IsClosed.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (nonunits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align nonunits.is_closed nonunits.isClosedₓ'. -/
-- The `nonunits` in a complete normed ring are a closed set
protected theorem isClosed : IsClosed (nonunits R) :=
  Units.isOpen.isClosed_compl
#align nonunits.is_closed nonunits.isClosed

end nonunits

namespace NormedRing

open Classical BigOperators

open Asymptotics Filter Metric Finset Ring

/- warning: normed_ring.inverse_one_sub -> NormedRing.inverse_one_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (t : R) (h : LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) t) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))), Eq.{succ u1} R (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) t)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.oneSub.{u1} R _inst_1 _inst_2 t h)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (t : R) (h : LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) t) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))), Eq.{succ u1} R (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) t)) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.oneSub.{u1} R _inst_1 _inst_2 t h)))
Case conversion may be inaccurate. Consider using '#align normed_ring.inverse_one_sub NormedRing.inverse_one_subₓ'. -/
theorem inverse_one_sub (t : R) (h : ‖t‖ < 1) : inverse (1 - t) = ↑(Units.oneSub t h)⁻¹ := by
  rw [← inverse_unit (Units.oneSub t h), Units.oneSub_val]
#align normed_ring.inverse_one_sub NormedRing.inverse_one_sub

/- warning: normed_ring.inverse_add -> NormedRing.inverse_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))), Filter.Eventually.{u1} R (fun (t : R) => Eq.{succ u1} R (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x) t)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) x)) t))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) x)))) (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))), Filter.Eventually.{u1} R (fun (t : R) => Eq.{succ u1} R (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x) t)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x)) t))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x)))) (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align normed_ring.inverse_add NormedRing.inverse_addₓ'. -/
/-- The formula `inverse (x + t) = inverse (1 + x⁻¹ * t) * x⁻¹` holds for `t` sufficiently small. -/
theorem inverse_add (x : Rˣ) : ∀ᶠ t in 𝓝 0, inverse ((x : R) + t) = inverse (1 + ↑x⁻¹ * t) * ↑x⁻¹ :=
  by
  nontriviality R
  rw [eventually_iff, Metric.mem_nhds_iff]
  have hinv : 0 < ‖(↑x⁻¹ : R)‖⁻¹ := by cancel_denoms
  use ‖(↑x⁻¹ : R)‖⁻¹, hinv
  intro t ht
  simp only [mem_ball, dist_zero_right] at ht
  have ht' : ‖-↑x⁻¹ * t‖ < 1 :=
    by
    refine' lt_of_le_of_lt (norm_mul_le _ _) _
    rw [norm_neg]
    refine' lt_of_lt_of_le (mul_lt_mul_of_pos_left ht x⁻¹.norm_pos) _
    cancel_denoms
  have hright := inverse_one_sub (-↑x⁻¹ * t) ht'
  have hleft := inverse_unit (x.add t ht)
  simp only [neg_mul, sub_neg_eq_add] at hright
  simp only [Units.add_val] at hleft
  simp [hleft, hright, Units.add]
#align normed_ring.inverse_add NormedRing.inverse_add

/- warning: normed_ring.inverse_one_sub_nth_order -> NormedRing.inverse_one_sub_nth_order is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (n : Nat), Filter.Eventually.{u1} R (fun (t : R) => Eq.{succ u1} R (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) t)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Finset.sum.{u1, 0} R Nat (AddCommGroup.toAddCommMonoid.{u1} R (NormedAddCommGroup.toAddCommGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1)))) (Finset.range n) (fun (i : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) t i)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) t n) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) t))))) (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (n : Nat), Filter.Eventually.{u1} R (fun (t : R) => Eq.{succ u1} R (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) t)) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (Finset.sum.{u1, 0} R Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Finset.range n) (fun (i : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) t i)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) t n) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) t))))) (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align normed_ring.inverse_one_sub_nth_order NormedRing.inverse_one_sub_nth_orderₓ'. -/
theorem inverse_one_sub_nth_order (n : ℕ) :
    ∀ᶠ t in 𝓝 0, inverse ((1 : R) - t) = (∑ i in range n, t ^ i) + t ^ n * inverse (1 - t) :=
  by
  simp only [eventually_iff, Metric.mem_nhds_iff]
  use 1, by norm_num
  intro t ht
  simp only [mem_ball, dist_zero_right] at ht
  simp only [inverse_one_sub t ht, Set.mem_setOf_eq]
  have h : 1 = ((range n).Sum fun i => t ^ i) * Units.oneSub t ht + t ^ n :=
    by
    simp only [Units.oneSub_val]
    rw [geom_sum_mul_neg]
    simp
  rw [← one_mul ↑(Units.oneSub t ht)⁻¹, h, add_mul]
  congr
  · rw [mul_assoc, (Units.oneSub t ht).mul_inv]
    simp
  · simp only [Units.oneSub_val]
    rw [← add_mul, geom_sum_mul_neg]
    simp
#align normed_ring.inverse_one_sub_nth_order NormedRing.inverse_one_sub_nth_order

/- warning: normed_ring.inverse_add_nth_order -> NormedRing.inverse_add_nth_order is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_ring.inverse_add_nth_order NormedRing.inverse_add_nth_orderₓ'. -/
/-- The formula
`inverse (x + t) = (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹ + (- x⁻¹ * t) ^ n * inverse (x + t)`
holds for `t` sufficiently small. -/
theorem inverse_add_nth_order (x : Rˣ) (n : ℕ) :
    ∀ᶠ t in 𝓝 0,
      inverse ((x : R) + t) =
        (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹ + (-↑x⁻¹ * t) ^ n * inverse (x + t) :=
  by
  refine' (inverse_add x).mp _
  have hzero : tendsto (fun t : R => -↑x⁻¹ * t) (𝓝 0) (𝓝 0) :=
    by
    convert((mulLeft_continuous (-(↑x⁻¹ : R))).Tendsto 0).comp tendsto_id
    simp
  refine' (hzero.eventually (inverse_one_sub_nth_order n)).mp (eventually_of_forall _)
  simp only [neg_mul, sub_neg_eq_add]
  intro t h1 h2
  have h := congr_arg (fun a : R => a * ↑x⁻¹) h1
  dsimp at h
  convert h
  rw [add_mul, mul_assoc]
  simp [h2.symm]
#align normed_ring.inverse_add_nth_order NormedRing.inverse_add_nth_order

/- warning: normed_ring.inverse_one_sub_norm -> NormedRing.inverse_one_sub_norm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], Asymptotics.IsBigO.{u1, u1, 0} R R Real (NormedRing.toHasNorm.{u1} R _inst_1) Real.hasNorm (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))))) (fun (t : R) => Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) t)) (fun (t : R) => OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], Asymptotics.IsBigO.{u1, u1, 0} R R Real (NormedRing.toNorm.{u1} R _inst_1) Real.norm (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (fun (t : R) => Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) t)) (fun (t : R) => OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align normed_ring.inverse_one_sub_norm NormedRing.inverse_one_sub_normₓ'. -/
theorem inverse_one_sub_norm : (fun t : R => inverse (1 - t)) =O[𝓝 0] (fun t => 1 : R → ℝ) :=
  by
  simp only [is_O, is_O_with, eventually_iff, Metric.mem_nhds_iff]
  refine' ⟨‖(1 : R)‖ + 1, (2 : ℝ)⁻¹, by norm_num, _⟩
  intro t ht
  simp only [ball, dist_zero_right, Set.mem_setOf_eq] at ht
  have ht' : ‖t‖ < 1 := by
    have : (2 : ℝ)⁻¹ < 1 := by cancel_denoms
    linarith
  simp only [inverse_one_sub t ht', norm_one, mul_one, Set.mem_setOf_eq]
  change ‖∑' n : ℕ, t ^ n‖ ≤ _
  have := NormedRing.tsum_geometric_of_norm_lt_1 t ht'
  have : (1 - ‖t‖)⁻¹ ≤ 2 := by
    rw [← inv_inv (2 : ℝ)]
    refine' inv_le_inv_of_le (by norm_num) _
    have : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by ring
    linarith
  linarith
#align normed_ring.inverse_one_sub_norm NormedRing.inverse_one_sub_norm

/- warning: normed_ring.inverse_add_norm -> NormedRing.inverse_add_norm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))), Asymptotics.IsBigO.{u1, u1, 0} R R Real (NormedRing.toHasNorm.{u1} R _inst_1) Real.hasNorm (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))))) (fun (t : R) => Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x) t)) (fun (t : R) => OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))), Asymptotics.IsBigO.{u1, u1, 0} R R Real (NormedRing.toNorm.{u1} R _inst_1) Real.norm (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (fun (t : R) => Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x) t)) (fun (t : R) => OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align normed_ring.inverse_add_norm NormedRing.inverse_add_normₓ'. -/
/-- The function `λ t, inverse (x + t)` is O(1) as `t → 0`. -/
theorem inverse_add_norm (x : Rˣ) : (fun t : R => inverse (↑x + t)) =O[𝓝 0] fun t => (1 : ℝ) :=
  by
  simp only [is_O_iff, norm_one, mul_one]
  cases' is_O_iff.mp (@inverse_one_sub_norm R _ _) with C hC
  use C * ‖((x⁻¹ : Rˣ) : R)‖
  have hzero : tendsto (fun t => -(↑x⁻¹ : R) * t) (𝓝 0) (𝓝 0) :=
    by
    convert((mulLeft_continuous (-↑x⁻¹ : R)).Tendsto 0).comp tendsto_id
    simp
  refine' (inverse_add x).mp ((hzero.eventually hC).mp (eventually_of_forall _))
  intro t bound iden
  rw [iden]
  simp at bound
  have hmul := norm_mul_le (inverse (1 + ↑x⁻¹ * t)) ↑x⁻¹
  nlinarith [norm_nonneg (↑x⁻¹ : R)]
#align normed_ring.inverse_add_norm NormedRing.inverse_add_norm

/- warning: normed_ring.inverse_add_norm_diff_nth_order -> NormedRing.inverse_add_norm_diff_nth_order is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (n : Nat), Asymptotics.IsBigO.{u1, u1, 0} R R Real (NormedRing.toHasNorm.{u1} R _inst_1) Real.hasNorm (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))))) (fun (t : R) => HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x) t)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Finset.sum.{u1, 0} R Nat (AddCommGroup.toAddCommMonoid.{u1} R (NormedAddCommGroup.toAddCommGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1)))) (Finset.range n) (fun (i : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Neg.neg.{u1} R (SubNegMonoid.toHasNeg.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1)))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) x))) t) i)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) x)))) (fun (t : R) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) t) n)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (n : Nat), Asymptotics.IsBigO.{u1, u1, 0} R R Real (NormedRing.toNorm.{u1} R _inst_1) Real.norm (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (fun (t : R) => HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x) t)) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Finset.sum.{u1, 0} R Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Finset.range n) (fun (i : Nat) => HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Neg.neg.{u1} R (Ring.toNeg.{u1} R (NormedRing.toRing.{u1} R _inst_1)) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x))) t) i)) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x)))) (fun (t : R) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) t) n)
Case conversion may be inaccurate. Consider using '#align normed_ring.inverse_add_norm_diff_nth_order NormedRing.inverse_add_norm_diff_nth_orderₓ'. -/
/-- The function
`λ t, inverse (x + t) - (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹`
is `O(t ^ n)` as `t → 0`. -/
theorem inverse_add_norm_diff_nth_order (x : Rˣ) (n : ℕ) :
    (fun t : R => inverse (↑x + t) - (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹) =O[𝓝 (0 : R)]
      fun t => ‖t‖ ^ n :=
  by
  by_cases h : n = 0
  · simpa [h] using inverse_add_norm x
  have hn : 0 < n := Nat.pos_of_ne_zero h
  simp [is_O_iff]
  cases' is_O_iff.mp (inverse_add_norm x) with C hC
  use C * ‖(1 : ℝ)‖ * ‖(↑x⁻¹ : R)‖ ^ n
  have h :
    eventually_eq (𝓝 (0 : R)) (fun t => inverse (↑x + t) - (∑ i in range n, (-↑x⁻¹ * t) ^ i) * ↑x⁻¹)
      fun t => (-↑x⁻¹ * t) ^ n * inverse (x + t) :=
    by
    refine' (inverse_add_nth_order x n).mp (eventually_of_forall _)
    intro t ht
    convert congr_arg (fun a => a - (range n).Sum (pow (-↑x⁻¹ * t)) * ↑x⁻¹) ht
    simp
  refine' h.mp (hC.mp (eventually_of_forall _))
  intro t _ hLHS
  simp only [neg_mul] at hLHS
  rw [hLHS]
  refine' le_trans (norm_mul_le _ _) _
  have h' : ‖(-(↑x⁻¹ * t)) ^ n‖ ≤ ‖(↑x⁻¹ : R)‖ ^ n * ‖t‖ ^ n :=
    by
    calc
      ‖(-(↑x⁻¹ * t)) ^ n‖ ≤ ‖-(↑x⁻¹ * t)‖ ^ n := norm_pow_le' _ hn
      _ = ‖↑x⁻¹ * t‖ ^ n := by rw [norm_neg]
      _ ≤ (‖(↑x⁻¹ : R)‖ * ‖t‖) ^ n := _
      _ = ‖(↑x⁻¹ : R)‖ ^ n * ‖t‖ ^ n := mul_pow _ _ n
      
    exact pow_le_pow_of_le_left (norm_nonneg _) (norm_mul_le (↑x⁻¹) t) n
  have h'' : 0 ≤ ‖(↑x⁻¹ : R)‖ ^ n * ‖t‖ ^ n := by
    refine' mul_nonneg _ _ <;> exact pow_nonneg (norm_nonneg _) n
  nlinarith [norm_nonneg (inverse (↑x + t))]
#align normed_ring.inverse_add_norm_diff_nth_order NormedRing.inverse_add_norm_diff_nth_order

/- warning: normed_ring.inverse_add_norm_diff_first_order -> NormedRing.inverse_add_norm_diff_first_order is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))), Asymptotics.IsBigO.{u1, u1, 0} R R Real (NormedRing.toHasNorm.{u1} R _inst_1) Real.hasNorm (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))))) (fun (t : R) => HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x) t)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) x))) (fun (t : R) => Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) t)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))), Asymptotics.IsBigO.{u1, u1, 0} R R Real (NormedRing.toNorm.{u1} R _inst_1) Real.norm (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (fun (t : R) => HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x) t)) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x))) (fun (t : R) => Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) t)
Case conversion may be inaccurate. Consider using '#align normed_ring.inverse_add_norm_diff_first_order NormedRing.inverse_add_norm_diff_first_orderₓ'. -/
/-- The function `λ t, inverse (x + t) - x⁻¹` is `O(t)` as `t → 0`. -/
theorem inverse_add_norm_diff_first_order (x : Rˣ) :
    (fun t : R => inverse (↑x + t) - ↑x⁻¹) =O[𝓝 0] fun t => ‖t‖ := by
  simpa using inverse_add_norm_diff_nth_order x 1
#align normed_ring.inverse_add_norm_diff_first_order NormedRing.inverse_add_norm_diff_first_order

/- warning: normed_ring.inverse_add_norm_diff_second_order -> NormedRing.inverse_add_norm_diff_second_order is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))), Asymptotics.IsBigO.{u1, u1, 0} R R Real (NormedRing.toHasNorm.{u1} R _inst_1) Real.hasNorm (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))))) (fun (t : R) => HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toHasAdd.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x) t)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) x))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) x)) t) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) (Inv.inv.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Units.hasInv.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) x)))) (fun (t : R) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) t) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))), Asymptotics.IsBigO.{u1, u1, 0} R R Real (NormedRing.toNorm.{u1} R _inst_1) Real.norm (nhds.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (fun (t : R) => HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x) t)) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x)) t) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Inv.inv.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Units.instInv.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x)))) (fun (t : R) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) t) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align normed_ring.inverse_add_norm_diff_second_order NormedRing.inverse_add_norm_diff_second_orderₓ'. -/
/-- The function
`λ t, inverse (x + t) - x⁻¹ + x⁻¹ * t * x⁻¹`
is `O(t ^ 2)` as `t → 0`. -/
theorem inverse_add_norm_diff_second_order (x : Rˣ) :
    (fun t : R => inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =O[𝓝 0] fun t => ‖t‖ ^ 2 :=
  by
  convert inverse_add_norm_diff_nth_order x 2
  ext t
  simp only [range_succ, range_one, sum_insert, mem_singleton, sum_singleton, not_false_iff,
    one_ne_zero, pow_zero, add_mul, pow_one, one_mul, neg_mul, sub_add_eq_sub_sub_swap,
    sub_neg_eq_add]
#align normed_ring.inverse_add_norm_diff_second_order NormedRing.inverse_add_norm_diff_second_order

/- warning: normed_ring.inverse_continuous_at -> NormedRing.inverse_continuousAt is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))), ContinuousAt.{u1, u1} R R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (x : Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))), ContinuousAt.{u1, u1} R R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (Ring.inverse.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))) x)
Case conversion may be inaccurate. Consider using '#align normed_ring.inverse_continuous_at NormedRing.inverse_continuousAtₓ'. -/
/-- The function `inverse` is continuous at each unit of `R`. -/
theorem inverse_continuousAt (x : Rˣ) : ContinuousAt inverse (x : R) :=
  by
  have h_is_o : (fun t : R => inverse (↑x + t) - ↑x⁻¹) =o[𝓝 0] (fun _ => 1 : R → ℝ) :=
    (inverse_add_norm_diff_first_order x).trans_isLittleO
      (is_o.norm_left <| is_o_id_const one_ne_zero)
  have h_lim : tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) :=
    by
    refine' tendsto_zero_iff_norm_tendsto_zero.mpr _
    exact tendsto_iff_norm_tendsto_zero.mp tendsto_id
  rw [ContinuousAt, tendsto_iff_norm_tendsto_zero, inverse_unit]
  simpa [(· ∘ ·)] using h_is_o.norm_left.tendsto_div_nhds_zero.comp h_lim
#align normed_ring.inverse_continuous_at NormedRing.inverse_continuousAt

end NormedRing

namespace Units

open MulOpposite Filter NormedRing

/- warning: units.is_open_map_coe -> Units.isOpenMap_val is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], IsOpenMap.{u1, u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.topologicalSpace.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], IsOpenMap.{u1, u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) R (Units.instTopologicalSpaceUnits.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align units.is_open_map_coe Units.isOpenMap_valₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- In a normed ring, the coercion from `Rˣ` (equipped with the induced topology from the
embedding in `R × R`) to `R` is an open map. -/
theorem isOpenMap_val : IsOpenMap (coe : Rˣ → R) :=
  by
  rw [isOpenMap_iff_nhds_le]
  intro x s
  rw [mem_map, mem_nhds_induced]
  rintro ⟨t, ht, hts⟩
  obtain ⟨u, hu, v, hv, huvt⟩ :
    ∃ u : Set R, u ∈ 𝓝 ↑x ∧ ∃ v : Set Rᵐᵒᵖ, v ∈ 𝓝 (op ↑x⁻¹) ∧ u ×ˢ v ⊆ t := by
    simpa [embed_product, mem_nhds_prod_iff] using ht
  have : u ∩ op ∘ Ring.inverse ⁻¹' v ∩ Set.range (coe : Rˣ → R) ∈ 𝓝 ↑x :=
    by
    refine' inter_mem (inter_mem hu _) (Units.nhds x)
    refine' (continuous_op.continuous_at.comp (inverse_continuous_at x)).preimage_mem_nhds _
    simpa using hv
  refine' mem_of_superset this _
  rintro _ ⟨⟨huy, hvy⟩, ⟨y, rfl⟩⟩
  have : embed_product R y ∈ u ×ˢ v := ⟨huy, by simpa using hvy⟩
  simpa using hts (huvt this)
#align units.is_open_map_coe Units.isOpenMap_val

/- warning: units.open_embedding_coe -> Units.openEmbedding_val is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], OpenEmbedding.{u1, u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.topologicalSpace.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (coeBase.{succ u1, succ u1} (Units.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Units.hasCoe.{u1} R (Ring.toMonoid.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))], OpenEmbedding.{u1, u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) R (Units.instTopologicalSpaceUnits.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (Units.val.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align units.open_embedding_coe Units.openEmbedding_valₓ'. -/
/-- In a normed ring, the coercion from `Rˣ` (equipped with the induced topology from the
embedding in `R × R`) to `R` is an open embedding. -/
theorem openEmbedding_val : OpenEmbedding (coe : Rˣ → R) :=
  openEmbedding_of_continuous_injective_open continuous_val ext isOpenMap_val
#align units.open_embedding_coe Units.openEmbedding_val

end Units

namespace Ideal

/- warning: ideal.eq_top_of_norm_lt_one -> Ideal.eq_top_of_norm_lt_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (I : Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) {x : R}, (Membership.Mem.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (SetLike.hasMem.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x I) -> (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} R (NormedRing.toHasNorm.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (SubNegMonoid.toHasSub.{u1} R (AddGroup.toSubNegMonoid.{u1} R (NormedAddGroup.toAddGroup.{u1} R (NormedAddCommGroup.toNormedAddGroup.{u1} R (NonUnitalNormedRing.toNormedAddCommGroup.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))))) x)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) I (Top.top.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Submodule.hasTop.{u1, u1} R R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (I : Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) {x : R}, (Membership.mem.{u1, u1} R (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (SetLike.instMembership.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x I) -> (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} R (NormedRing.toNorm.{u1} R _inst_1) (HSub.hSub.{u1, u1, u1} R R R (instHSub.{u1} R (Ring.toSub.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) x)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) I (Top.top.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Submodule.instTopSubmodule.{u1, u1} R R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align ideal.eq_top_of_norm_lt_one Ideal.eq_top_of_norm_lt_oneₓ'. -/
/-- An ideal which contains an element within `1` of `1 : R` is the unit ideal. -/
theorem eq_top_of_norm_lt_one (I : Ideal R) {x : R} (hxI : x ∈ I) (hx : ‖1 - x‖ < 1) : I = ⊤ :=
  let u := Units.oneSub (1 - x) hx
  I.eq_top_iff_one.mpr <| by simpa only [show u.inv * x = 1 by simp] using I.mul_mem_left u.inv hxI
#align ideal.eq_top_of_norm_lt_one Ideal.eq_top_of_norm_lt_one

/- warning: ideal.closure_ne_top -> Ideal.closure_ne_top is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (I : Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))), (Ne.{succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) I (Top.top.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Submodule.hasTop.{u1, u1} R R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) -> (Ne.{succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Ideal.closure.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (NormedRing.toRing.{u1} R _inst_1) (semi_normed_top_ring.{u1} R (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))) I) (Top.top.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Submodule.hasTop.{u1, u1} R R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NormedRing.{u1} R] [_inst_2 : CompleteSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))] (I : Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))), (Ne.{succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) I (Top.top.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Submodule.instTopSubmodule.{u1, u1} R R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)))))) -> (Ne.{succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Ideal.closure.{u1} R (UniformSpace.toTopologicalSpace.{u1} R (PseudoMetricSpace.toUniformSpace.{u1} R (SeminormedRing.toPseudoMetricSpace.{u1} R (NormedRing.toSeminormedRing.{u1} R _inst_1)))) (NormedRing.toRing.{u1} R _inst_1) (semi_normed_top_ring.{u1} R (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} R (NormedRing.toNonUnitalNormedRing.{u1} R _inst_1))) I) (Top.top.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))) (Submodule.instTopSubmodule.{u1, u1} R R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (NormedRing.toRing.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align ideal.closure_ne_top Ideal.closure_ne_topₓ'. -/
/-- The `ideal.closure` of a proper ideal in a complete normed ring is proper. -/
theorem closure_ne_top (I : Ideal R) (hI : I ≠ ⊤) : I.closure ≠ ⊤ :=
  by
  have h := closure_minimal (coe_subset_nonunits hI) nonunits.isClosed
  simpa only [I.closure.eq_top_iff_one, Ne.def] using mt (@h 1) one_not_mem_nonunits
#align ideal.closure_ne_top Ideal.closure_ne_top

#print Ideal.IsMaximal.closure_eq /-
/-- The `ideal.closure` of a maximal ideal in a complete normed ring is the ideal itself. -/
theorem IsMaximal.closure_eq {I : Ideal R} (hI : I.IsMaximal) : I.closure = I :=
  (hI.eq_of_le (I.closure_ne_top hI.ne_top) subset_closure).symm
#align ideal.is_maximal.closure_eq Ideal.IsMaximal.closure_eq
-/

#print Ideal.IsMaximal.isClosed /-
/-- Maximal ideals in complete normed rings are closed. -/
instance IsMaximal.isClosed {I : Ideal R} [hI : I.IsMaximal] : IsClosed (I : Set R) :=
  isClosed_of_closure_subset <| Eq.subset <| congr_arg (coe : Ideal R → Set R) hI.closure_eq
#align ideal.is_maximal.is_closed Ideal.IsMaximal.isClosed
-/

end Ideal

