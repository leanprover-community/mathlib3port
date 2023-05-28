/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.valuation
! leanprover-community/mathlib commit 8eb9c42d4d34c77f6ee84ea766ae4070233a973c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Nonarchimedean.Bases
import Mathbin.Topology.Algebra.UniformFilterBasis
import Mathbin.RingTheory.Valuation.Basic

/-!
# The topology on a valued ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define the non archimedean topology induced by a valuation on a ring.
The main definition is a `valued` type class which equips a ring with a valuation taking
values in a group with zero. Other instances are then deduced from this.
-/


open Classical Topology uniformity

open Set Valuation

noncomputable section

universe v u

variable {R : Type u} [Ring R] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

variable (v : Valuation R Γ₀)

#print Valuation.subgroups_basis /-
/-- The basis of open subgroups for the topology on a ring determined by a valuation. -/
theorem subgroups_basis : RingSubgroupsBasis fun γ : Γ₀ˣ => (v.ltAddSubgroup γ : AddSubgroup R) :=
  { inter := by
      rintro γ₀ γ₁
      use min γ₀ γ₁
      simp [Valuation.ltAddSubgroup] <;> tauto
    mul := by
      rintro γ
      cases' exists_square_le γ with γ₀ h
      use γ₀
      rintro - ⟨r, s, r_in, s_in, rfl⟩
      calc
        (v (r * s) : Γ₀) = v r * v s := Valuation.map_mul _ _ _
        _ < γ₀ * γ₀ := (mul_lt_mul₀ r_in s_in)
        _ ≤ γ := by exact_mod_cast h
        
    leftMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use (1 : Γ₀ˣ)
        rintro y (y_in : (v y : Γ₀) < 1)
        change v (x * y) < _
        rw [Valuation.map_mul, Hx, MulZeroClass.zero_mul]
        exact Units.zero_lt γ
      · simp only [image_subset_iff, set_of_subset_set_of, preimage_set_of_eq, Valuation.map_mul]
        use γx⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        change (v (x * y) : Γ₀) < γ
        rw [Valuation.map_mul, Hx, mul_comm]
        rw [Units.val_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt
    rightMul := by
      rintro x γ
      rcases GroupWithZero.eq_zero_or_unit (v x) with (Hx | ⟨γx, Hx⟩)
      · use 1
        rintro y (y_in : (v y : Γ₀) < 1)
        change v (y * x) < _
        rw [Valuation.map_mul, Hx, MulZeroClass.mul_zero]
        exact Units.zero_lt γ
      · use γx⁻¹ * γ
        rintro y (vy_lt : v y < ↑(γx⁻¹ * γ))
        change (v (y * x) : Γ₀) < γ
        rw [Valuation.map_mul, Hx]
        rw [Units.val_mul, mul_comm] at vy_lt
        simpa using mul_inv_lt_of_lt_mul₀ vy_lt }
#align valuation.subgroups_basis Valuation.subgroups_basis
-/

end Valuation

#print Valued /-
/-- A valued ring is a ring that comes equipped with a distinguished valuation. The class `valued`
is designed for the situation that there is a canonical valuation on the ring.

TODO: show that there always exists an equivalent valuation taking values in a type belonging to
the same universe as the ring.

See Note [forgetful inheritance] for why we extend `uniform_space`, `uniform_add_group`. -/
class Valued (R : Type u) [Ring R] (Γ₀ : outParam (Type v))
  [LinearOrderedCommGroupWithZero Γ₀] extends UniformSpace R, UniformAddGroup R where
  V : Valuation R Γ₀
  is_topological_valuation : ∀ s, s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x : R | v x < γ } ⊆ s
#align valued Valued
-/

attribute [nolint dangerous_instance] Valued.toUniformSpace

namespace Valued

#print Valued.mk' /-
/-- Alternative `valued` constructor for use when there is no preferred `uniform_space`
structure. -/
def mk' (v : Valuation R Γ₀) : Valued R Γ₀ :=
  { V
    toUniformSpace := @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
    to_uniformAddGroup := @comm_topologicalAddGroup_is_uniform _ _ v.subgroups_basis.topology _
    is_topological_valuation :=
      by
      letI := @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _
      intro s
      rw [filter.has_basis_iff.mp v.subgroups_basis.has_basis_nhds_zero s]
      exact exists_congr fun γ => by simpa }
#align valued.mk' Valued.mk'
-/

variable (R Γ₀) [_i : Valued R Γ₀]

include _i

/- warning: valued.has_basis_nhds_zero -> Valued.hasBasis_nhds_zero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u2}) [_inst_1 : Ring.{u2} R] (Γ₀ : Type.{u1}) [_inst_2 : LinearOrderedCommGroupWithZero.{u1} Γ₀] [_i : Valued.{u1, u2} R _inst_1 Γ₀ _inst_2], Filter.HasBasis.{u2, succ u1} R (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) (nhds.{u2} R (UniformSpace.toTopologicalSpace.{u2} R (Valued.toUniformSpace.{u1, u2} R _inst_1 Γ₀ _inst_2 _i)) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R (NonAssocRing.toNonUnitalNonAssocRing.{u2} R (Ring.toNonAssocRing.{u2} R _inst_1))))))))) (fun (_x : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => True) (fun (γ : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => setOf.{u2} R (fun (x : R) => LT.lt.{u1} Γ₀ (Preorder.toHasLt.{u1} Γ₀ (PartialOrder.toPreorder.{u1} Γ₀ (OrderedCommMonoid.toPartialOrder.{u1} Γ₀ (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} Γ₀ (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2)))))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) (fun (_x : Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) => R -> Γ₀) (Valuation.hasCoeToFun.{u2, u1} R Γ₀ _inst_1 (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2)) (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) Γ₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) Γ₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) Γ₀ (coeBase.{succ u1, succ u1} (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) Γ₀ (Units.hasCoe.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2)))))))) γ)))
but is expected to have type
  forall (R : Type.{u2}) [_inst_1 : Ring.{u2} R] (Γ₀ : Type.{u1}) [_inst_2 : LinearOrderedCommGroupWithZero.{u1} Γ₀] [_i : Valued.{u1, u2} R _inst_1 Γ₀ _inst_2], Filter.HasBasis.{u2, succ u1} R (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) (nhds.{u2} R (UniformSpace.toTopologicalSpace.{u2} R (Valued.toUniformSpace.{u1, u2} R _inst_1 Γ₀ _inst_2 _i)) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)))))) (fun (_x : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => True) (fun (γ : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => setOf.{u2} R (fun (x : R) => LT.lt.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) x) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) x) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) x) (OrderedCommMonoid.toPartialOrder.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) x) (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) x) (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) x) (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) x) _inst_2)))))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) R Γ₀ (MulOneClass.toMul.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (MulOneClass.toMul.{u1} Γ₀ (MulZeroOneClass.toMulOneClass.{u1} Γ₀ (MonoidWithZero.toMulZeroOneClass.{u1} Γ₀ (CommMonoidWithZero.toMonoidWithZero.{u1} Γ₀ (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2)))))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) R Γ₀ (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} Γ₀ (MonoidWithZero.toMulZeroOneClass.{u1} Γ₀ (CommMonoidWithZero.toMonoidWithZero.{u1} Γ₀ (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2))))) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) R Γ₀ (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} Γ₀ (CommMonoidWithZero.toMonoidWithZero.{u1} Γ₀ (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2)))) (ValuationClass.toMonoidWithZeroHomClass.{max u2 u1, u2, u1} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1 (Valuation.instValuationClassValuation.{u2, u1} R Γ₀ _inst_1 (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2)))))) (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i) x) (Units.val.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2)))) γ)))
Case conversion may be inaccurate. Consider using '#align valued.has_basis_nhds_zero Valued.hasBasis_nhds_zeroₓ'. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R)).HasBasis (fun _ => True) fun γ : Γ₀ˣ => { x | v x < (γ : Γ₀) } := by
  simp [Filter.hasBasis_iff, is_topological_valuation]
#align valued.has_basis_nhds_zero Valued.hasBasis_nhds_zero

/- warning: valued.has_basis_uniformity -> Valued.hasBasis_uniformity is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u2}) [_inst_1 : Ring.{u2} R] (Γ₀ : Type.{u1}) [_inst_2 : LinearOrderedCommGroupWithZero.{u1} Γ₀] [_i : Valued.{u1, u2} R _inst_1 Γ₀ _inst_2], Filter.HasBasis.{u2, succ u1} (Prod.{u2, u2} R R) (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) (uniformity.{u2} R (Valued.toUniformSpace.{u1, u2} R _inst_1 Γ₀ _inst_2 _i)) (fun (_x : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => True) (fun (γ : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => setOf.{u2} (Prod.{u2, u2} R R) (fun (p : Prod.{u2, u2} R R) => LT.lt.{u1} Γ₀ (Preorder.toHasLt.{u1} Γ₀ (PartialOrder.toPreorder.{u1} Γ₀ (OrderedCommMonoid.toPartialOrder.{u1} Γ₀ (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} Γ₀ (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2)))))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) (fun (_x : Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) => R -> Γ₀) (Valuation.hasCoeToFun.{u2, u1} R Γ₀ _inst_1 (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2)) (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R _inst_1)))))) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) Γ₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) Γ₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) Γ₀ (coeBase.{succ u1, succ u1} (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) Γ₀ (Units.hasCoe.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2)))))))) γ)))
but is expected to have type
  forall (R : Type.{u2}) [_inst_1 : Ring.{u2} R] (Γ₀ : Type.{u1}) [_inst_2 : LinearOrderedCommGroupWithZero.{u1} Γ₀] [_i : Valued.{u1, u2} R _inst_1 Γ₀ _inst_2], Filter.HasBasis.{u2, succ u1} (Prod.{u2, u2} R R) (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) (uniformity.{u2} R (Valued.toUniformSpace.{u1, u2} R _inst_1 Γ₀ _inst_2 _i)) (fun (_x : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => True) (fun (γ : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => setOf.{u2} (Prod.{u2, u2} R R) (fun (p : Prod.{u2, u2} R R) => LT.lt.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R _inst_1)) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (Preorder.toLT.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R _inst_1)) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (PartialOrder.toPreorder.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R _inst_1)) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (OrderedCommMonoid.toPartialOrder.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R _inst_1)) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R _inst_1)) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (LinearOrderedCommMonoidWithZero.toLinearOrderedCommMonoid.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R _inst_1)) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R _inst_1)) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) _inst_2)))))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : R) => Γ₀) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) R Γ₀ (MulOneClass.toMul.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (MulOneClass.toMul.{u1} Γ₀ (MulZeroOneClass.toMulOneClass.{u1} Γ₀ (MonoidWithZero.toMulZeroOneClass.{u1} Γ₀ (CommMonoidWithZero.toMonoidWithZero.{u1} Γ₀ (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2)))))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) R Γ₀ (MulZeroOneClass.toMulOneClass.{u2} R (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (MulZeroOneClass.toMulOneClass.{u1} Γ₀ (MonoidWithZero.toMulZeroOneClass.{u1} Γ₀ (CommMonoidWithZero.toMonoidWithZero.{u1} Γ₀ (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2))))) (MonoidWithZeroHomClass.toMonoidHomClass.{max u2 u1, u2, u1} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) R Γ₀ (NonAssocSemiring.toMulZeroOneClass.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (MonoidWithZero.toMulZeroOneClass.{u1} Γ₀ (CommMonoidWithZero.toMonoidWithZero.{u1} Γ₀ (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2)))) (ValuationClass.toMonoidWithZeroHomClass.{max u2 u1, u2, u1} (Valuation.{u2, u1} R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1) R Γ₀ (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2) _inst_1 (Valuation.instValuationClassValuation.{u2, u1} R Γ₀ _inst_1 (LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero.{u1} Γ₀ _inst_2)))))) (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i) (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R _inst_1)) (Prod.snd.{u2, u2} R R p) (Prod.fst.{u2, u2} R R p))) (Units.val.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2)))) γ)))
Case conversion may be inaccurate. Consider using '#align valued.has_basis_uniformity Valued.hasBasis_uniformityₓ'. -/
theorem hasBasis_uniformity :
    (𝓤 R).HasBasis (fun _ => True) fun γ : Γ₀ˣ => { p : R × R | v (p.2 - p.1) < (γ : Γ₀) } :=
  by
  rw [uniformity_eq_comap_nhds_zero]
  exact (has_basis_nhds_zero R Γ₀).comap _
#align valued.has_basis_uniformity Valued.hasBasis_uniformity

/- warning: valued.to_uniform_space_eq -> Valued.toUniformSpace_eq is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u2}) [_inst_1 : Ring.{u2} R] (Γ₀ : Type.{u1}) [_inst_2 : LinearOrderedCommGroupWithZero.{u1} Γ₀] [_i : Valued.{u1, u2} R _inst_1 Γ₀ _inst_2], Eq.{succ u2} (UniformSpace.{u2} R) (Valued.toUniformSpace.{u1, u2} R _inst_1 Γ₀ _inst_2 _i) (TopologicalAddGroup.toUniformSpace.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R _inst_1))) (RingSubgroupsBasis.topology.{u2, u1} R (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) _inst_1 (instNonempty.{succ u1} (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) (Units.inhabited.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2)))))) (fun (γ : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => Valuation.ltAddSubgroup.{u2, u1} R Γ₀ _inst_1 _inst_2 (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i) γ) (Valuation.subgroups_basis.{u1, u2} R _inst_1 Γ₀ _inst_2 (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i))) (AddGroupFilterBasis.isTopologicalAddGroup.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R _inst_1))) (RingFilterBasis.toAddGroupFilterBasis.{u2} R _inst_1 (RingSubgroupsBasis.toRingFilterBasis.{u2, u1} R (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) _inst_1 (instNonempty.{succ u1} (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) (Units.inhabited.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2)))))) (fun (γ : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => Valuation.ltAddSubgroup.{u2, u1} R Γ₀ _inst_1 _inst_2 (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i) γ) (Valuation.subgroups_basis.{u1, u2} R _inst_1 Γ₀ _inst_2 (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i))))))
but is expected to have type
  forall (R : Type.{u2}) [_inst_1 : Ring.{u2} R] (Γ₀ : Type.{u1}) [_inst_2 : LinearOrderedCommGroupWithZero.{u1} Γ₀] [_i : Valued.{u1, u2} R _inst_1 Γ₀ _inst_2], Eq.{succ u2} (UniformSpace.{u2} R) (Valued.toUniformSpace.{u1, u2} R _inst_1 Γ₀ _inst_2 _i) (TopologicalAddGroup.toUniformSpace.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_1)) (RingSubgroupsBasis.topology.{u2, u1} R (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) _inst_1 (instNonempty.{succ u1} (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) (Units.instInhabitedUnits.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2)))))) (fun (γ : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => Valuation.ltAddSubgroup.{u2, u1} R Γ₀ _inst_1 _inst_2 (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i) γ) (Valuation.subgroups_basis.{u1, u2} R _inst_1 Γ₀ _inst_2 (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i))) (AddGroupFilterBasis.isTopologicalAddGroup.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_1)) (RingFilterBasis.toAddGroupFilterBasis.{u2} R _inst_1 (RingSubgroupsBasis.toRingFilterBasis.{u2, u1} R (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) _inst_1 (instNonempty.{succ u1} (Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) (Units.instInhabitedUnits.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2)))))) (fun (γ : Units.{u1} Γ₀ (MonoidWithZero.toMonoid.{u1} Γ₀ (GroupWithZero.toMonoidWithZero.{u1} Γ₀ (CommGroupWithZero.toGroupWithZero.{u1} Γ₀ (LinearOrderedCommGroupWithZero.toCommGroupWithZero.{u1} Γ₀ _inst_2))))) => Valuation.ltAddSubgroup.{u2, u1} R Γ₀ _inst_1 _inst_2 (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i) γ) (Valuation.subgroups_basis.{u1, u2} R _inst_1 Γ₀ _inst_2 (Valued.v.{u1, u2} R _inst_1 Γ₀ _inst_2 _i))))))
Case conversion may be inaccurate. Consider using '#align valued.to_uniform_space_eq Valued.toUniformSpace_eqₓ'. -/
theorem toUniformSpace_eq :
    toUniformSpace = @TopologicalAddGroup.toUniformSpace R _ v.subgroups_basis.topology _ :=
  uniformSpace_eq
    ((hasBasis_uniformity R Γ₀).eq_of_same_basis <| v.subgroups_basis.hasBasis_nhds_zero.comap _)
#align valued.to_uniform_space_eq Valued.toUniformSpace_eq

variable {R Γ₀}

/- warning: valued.mem_nhds -> Valued.mem_nhds is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align valued.mem_nhds Valued.mem_nhdsₓ'. -/
theorem mem_nhds {s : Set R} {x : R} : s ∈ 𝓝 x ↔ ∃ γ : Γ₀ˣ, { y | (v (y - x) : Γ₀) < γ } ⊆ s := by
  simp only [← nhds_translation_add_neg x, ← sub_eq_add_neg, preimage_set_of_eq, exists_true_left,
    ((has_basis_nhds_zero R Γ₀).comap fun y => y - x).mem_iff]
#align valued.mem_nhds Valued.mem_nhds

/- warning: valued.mem_nhds_zero -> Valued.mem_nhds_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align valued.mem_nhds_zero Valued.mem_nhds_zeroₓ'. -/
theorem mem_nhds_zero {s : Set R} : s ∈ 𝓝 (0 : R) ↔ ∃ γ : Γ₀ˣ, { x | v x < (γ : Γ₀) } ⊆ s := by
  simp only [mem_nhds, sub_zero]
#align valued.mem_nhds_zero Valued.mem_nhds_zero

/- warning: valued.loc_const -> Valued.loc_const is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align valued.loc_const Valued.loc_constₓ'. -/
theorem loc_const {x : R} (h : (v x : Γ₀) ≠ 0) : { y : R | v y = v x } ∈ 𝓝 x :=
  by
  rw [mem_nhds]
  rcases units.exists_iff_ne_zero.mpr h with ⟨γ, hx⟩
  use γ
  rw [hx]
  intro y y_in
  exact Valuation.map_eq_of_sub_lt _ y_in
#align valued.loc_const Valued.loc_const

instance (priority := 100) : TopologicalRing R :=
  (toUniformSpace_eq R Γ₀).symm ▸ v.subgroups_basis.toRingFilterBasis.isTopologicalRing

/- warning: valued.cauchy_iff -> Valued.cauchy_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align valued.cauchy_iff Valued.cauchy_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x y «expr ∈ » M) -/
theorem cauchy_iff {F : Filter R} :
    Cauchy F ↔
      F.ne_bot ∧ ∀ γ : Γ₀ˣ, ∃ M ∈ F, ∀ (x) (_ : x ∈ M) (y) (_ : y ∈ M), (v (y - x) : Γ₀) < γ :=
  by
  rw [to_uniform_space_eq, AddGroupFilterBasis.cauchy_iff]
  apply and_congr Iff.rfl
  simp_rw [valued.v.subgroups_basis.mem_add_group_filter_basis_iff]
  constructor
  · intro h γ
    exact h _ (valued.v.subgroups_basis.mem_add_group_filter_basis _)
  · rintro h - ⟨γ, rfl⟩
    exact h γ
#align valued.cauchy_iff Valued.cauchy_iff

end Valued

