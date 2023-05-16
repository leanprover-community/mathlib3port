/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.punit_instances
! leanprover-community/mathlib commit be24ec5de6701447e5df5ca75400ffee19d65659
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.GcdMonoid.Basic
import Mathbin.Algebra.GroupRingAction.Basic
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.Order.CompleteBooleanAlgebra

/-!
# Instances on punit

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/


universe u

namespace PUnit

variable {R S : Type _} (x y : PUnit.{u + 1}) (s : Set PUnit.{u + 1})

@[to_additive]
instance : CommGroup PUnit := by
  refine_struct
        { mul := fun _ _ => star
          one := star
          inv := fun _ => star
          div := fun _ _ => star
          npow := fun _ _ => star
          zpow := fun _ _ => star.. } <;>
      intros <;>
    exact Subsingleton.elim _ _

/- warning: punit.one_eq -> PUnit.one_eq is a dubious translation:
lean 3 declaration is
  Eq.{succ u_1} PUnit.{succ u_1} (OfNat.ofNat.{u_1} PUnit.{succ u_1} 1 (OfNat.mk.{u_1} PUnit.{succ u_1} 1 (One.one.{u_1} PUnit.{succ u_1} (MulOneClass.toHasOne.{u_1} PUnit.{succ u_1} (Monoid.toMulOneClass.{u_1} PUnit.{succ u_1} (DivInvMonoid.toMonoid.{u_1} PUnit.{succ u_1} (Group.toDivInvMonoid.{u_1} PUnit.{succ u_1} (CommGroup.toGroup.{u_1} PUnit.{succ u_1} PUnit.commGroup.{u_1})))))))) PUnit.unit.{succ u_1}
but is expected to have type
  Eq.{1} PUnit.{1} (OfNat.ofNat.{0} PUnit.{1} 1 (One.toOfNat1.{0} PUnit.{1} PUnit.instOnePUnit)) PUnit.unit.{1}
Case conversion may be inaccurate. Consider using '#align punit.one_eq PUnit.one_eqₓ'. -/
@[simp, to_additive]
theorem one_eq : (1 : PUnit) = unit :=
  rfl
#align punit.one_eq PUnit.one_eq
#align punit.zero_eq PUnit.zero_eq

/- warning: punit.mul_eq -> PUnit.mul_eq is a dubious translation:
lean 3 declaration is
  forall (x : PUnit.{succ u}) (y : PUnit.{succ u}), Eq.{succ u} PUnit.{succ u} (HMul.hMul.{u, u, u} PUnit.{succ u} PUnit.{succ u} PUnit.{succ u} (instHMul.{u} PUnit.{succ u} (MulOneClass.toHasMul.{u} PUnit.{succ u} (Monoid.toMulOneClass.{u} PUnit.{succ u} (DivInvMonoid.toMonoid.{u} PUnit.{succ u} (Group.toDivInvMonoid.{u} PUnit.{succ u} (CommGroup.toGroup.{u} PUnit.{succ u} PUnit.commGroup.{u})))))) x y) PUnit.unit.{succ u}
but is expected to have type
  forall {x : PUnit.{1}} {y : PUnit.{1}}, Eq.{1} PUnit.{1} (HMul.hMul.{0, 0, 0} PUnit.{1} PUnit.{1} PUnit.{1} (instHMul.{0} PUnit.{1} PUnit.instMulPUnit) x y) PUnit.unit.{1}
Case conversion may be inaccurate. Consider using '#align punit.mul_eq PUnit.mul_eqₓ'. -/
@[simp, to_additive]
theorem mul_eq : x * y = unit :=
  rfl
#align punit.mul_eq PUnit.mul_eq
#align punit.add_eq PUnit.add_eq

/- warning: punit.div_eq -> PUnit.div_eq is a dubious translation:
lean 3 declaration is
  forall (x : PUnit.{succ u}) (y : PUnit.{succ u}), Eq.{succ u} PUnit.{succ u} (HDiv.hDiv.{u, u, u} PUnit.{succ u} PUnit.{succ u} PUnit.{succ u} (instHDiv.{u} PUnit.{succ u} (DivInvMonoid.toHasDiv.{u} PUnit.{succ u} (Group.toDivInvMonoid.{u} PUnit.{succ u} (CommGroup.toGroup.{u} PUnit.{succ u} PUnit.commGroup.{u})))) x y) PUnit.unit.{succ u}
but is expected to have type
  forall {x : PUnit.{1}} {y : PUnit.{1}}, Eq.{1} PUnit.{1} (HDiv.hDiv.{0, 0, 0} PUnit.{1} PUnit.{1} PUnit.{1} (instHDiv.{0} PUnit.{1} PUnit.instDivPUnit) x y) PUnit.unit.{1}
Case conversion may be inaccurate. Consider using '#align punit.div_eq PUnit.div_eqₓ'. -/
-- `sub_eq` simplifies `punit.sub_eq`, but the latter is eligible for `dsimp`
@[simp, nolint simp_nf, to_additive]
theorem div_eq : x / y = unit :=
  rfl
#align punit.div_eq PUnit.div_eq
#align punit.sub_eq PUnit.sub_eq

/- warning: punit.inv_eq -> PUnit.inv_eq is a dubious translation:
lean 3 declaration is
  forall (x : PUnit.{succ u}), Eq.{succ u} PUnit.{succ u} (Inv.inv.{u} PUnit.{succ u} (DivInvMonoid.toHasInv.{u} PUnit.{succ u} (Group.toDivInvMonoid.{u} PUnit.{succ u} (CommGroup.toGroup.{u} PUnit.{succ u} PUnit.commGroup.{u}))) x) PUnit.unit.{succ u}
but is expected to have type
  forall {x : PUnit.{1}}, Eq.{1} PUnit.{1} (Inv.inv.{0} PUnit.{1} PUnit.instInvPUnit x) PUnit.unit.{1}
Case conversion may be inaccurate. Consider using '#align punit.inv_eq PUnit.inv_eqₓ'. -/
-- `neg_eq` simplifies `punit.neg_eq`, but the latter is eligible for `dsimp`
@[simp, nolint simp_nf, to_additive]
theorem inv_eq : x⁻¹ = unit :=
  rfl
#align punit.inv_eq PUnit.inv_eq
#align punit.neg_eq PUnit.neg_eq

instance : CommRing PUnit := by
  refine' { PUnit.commGroup, PUnit.addCommGroup with natCast := fun _ => PUnit.unit.. } <;>
      intros <;>
    exact Subsingleton.elim _ _

instance : CancelCommMonoidWithZero PUnit := by
  refine' { PUnit.commRing with .. } <;> intros <;> exact Subsingleton.elim _ _

instance : NormalizedGCDMonoid PUnit := by
  refine' {
          gcd := fun _ _ => star
          lcm := fun _ _ => star
          normUnit := fun x => 1
          gcd_dvd_left := fun _ _ => ⟨star, Subsingleton.elim _ _⟩
          gcd_dvd_right := fun _ _ => ⟨star, Subsingleton.elim _ _⟩
          dvd_gcd := fun _ _ _ _ _ => ⟨star, Subsingleton.elim _ _⟩
          gcd_mul_lcm := fun _ _ => ⟨1, Subsingleton.elim _ _⟩.. } <;>
      intros <;>
    exact Subsingleton.elim _ _

/- warning: punit.gcd_eq -> PUnit.gcd_eq is a dubious translation:
lean 3 declaration is
  forall (x : PUnit.{succ u}) (y : PUnit.{succ u}), Eq.{succ u} PUnit.{succ u} (GCDMonoid.gcd.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u} (NormalizedGCDMonoid.toGcdMonoid.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u} PUnit.normalizedGcdMonoid.{u}) x y) PUnit.unit.{succ u}
but is expected to have type
  forall {x : PUnit.{1}} {y : PUnit.{1}}, Eq.{1} PUnit.{1} (GCDMonoid.gcd.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero (NormalizedGCDMonoid.toGCDMonoid.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero PUnit.normalizedGCDMonoid) x y) PUnit.unit.{1}
Case conversion may be inaccurate. Consider using '#align punit.gcd_eq PUnit.gcd_eqₓ'. -/
@[simp]
theorem gcd_eq : gcd x y = unit :=
  rfl
#align punit.gcd_eq PUnit.gcd_eq

/- warning: punit.lcm_eq -> PUnit.lcm_eq is a dubious translation:
lean 3 declaration is
  forall (x : PUnit.{succ u}) (y : PUnit.{succ u}), Eq.{succ u} PUnit.{succ u} (GCDMonoid.lcm.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u} (NormalizedGCDMonoid.toGcdMonoid.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u} PUnit.normalizedGcdMonoid.{u}) x y) PUnit.unit.{succ u}
but is expected to have type
  forall {x : PUnit.{1}} {y : PUnit.{1}}, Eq.{1} PUnit.{1} (GCDMonoid.lcm.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero (NormalizedGCDMonoid.toGCDMonoid.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero PUnit.normalizedGCDMonoid) x y) PUnit.unit.{1}
Case conversion may be inaccurate. Consider using '#align punit.lcm_eq PUnit.lcm_eqₓ'. -/
@[simp]
theorem lcm_eq : lcm x y = unit :=
  rfl
#align punit.lcm_eq PUnit.lcm_eq

/- warning: punit.norm_unit_eq -> PUnit.norm_unit_eq is a dubious translation:
lean 3 declaration is
  forall (x : PUnit.{succ u}), Eq.{succ u} (Units.{u} PUnit.{succ u} (MonoidWithZero.toMonoid.{u} PUnit.{succ u} (CommMonoidWithZero.toMonoidWithZero.{u} PUnit.{succ u} (CancelCommMonoidWithZero.toCommMonoidWithZero.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u})))) (NormalizationMonoid.normUnit.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u} (normalizationMonoidOfUniqueUnits.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u} (Units.unique.{u} PUnit.{succ u} (MonoidWithZero.toMonoid.{u} PUnit.{succ u} (CommMonoidWithZero.toMonoidWithZero.{u} PUnit.{succ u} (CancelCommMonoidWithZero.toCommMonoidWithZero.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u}))) PUnit.subsingleton.{succ u})) x) (OfNat.ofNat.{u} (Units.{u} PUnit.{succ u} (MonoidWithZero.toMonoid.{u} PUnit.{succ u} (CommMonoidWithZero.toMonoidWithZero.{u} PUnit.{succ u} (CancelCommMonoidWithZero.toCommMonoidWithZero.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u})))) 1 (OfNat.mk.{u} (Units.{u} PUnit.{succ u} (MonoidWithZero.toMonoid.{u} PUnit.{succ u} (CommMonoidWithZero.toMonoidWithZero.{u} PUnit.{succ u} (CancelCommMonoidWithZero.toCommMonoidWithZero.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u})))) 1 (One.one.{u} (Units.{u} PUnit.{succ u} (MonoidWithZero.toMonoid.{u} PUnit.{succ u} (CommMonoidWithZero.toMonoidWithZero.{u} PUnit.{succ u} (CancelCommMonoidWithZero.toCommMonoidWithZero.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u})))) (MulOneClass.toHasOne.{u} (Units.{u} PUnit.{succ u} (MonoidWithZero.toMonoid.{u} PUnit.{succ u} (CommMonoidWithZero.toMonoidWithZero.{u} PUnit.{succ u} (CancelCommMonoidWithZero.toCommMonoidWithZero.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u})))) (Units.mulOneClass.{u} PUnit.{succ u} (MonoidWithZero.toMonoid.{u} PUnit.{succ u} (CommMonoidWithZero.toMonoidWithZero.{u} PUnit.{succ u} (CancelCommMonoidWithZero.toCommMonoidWithZero.{u} PUnit.{succ u} PUnit.cancelCommMonoidWithZero.{u}))))))))
but is expected to have type
  forall {x : PUnit.{1}}, Eq.{1} (Units.{0} PUnit.{1} (MonoidWithZero.toMonoid.{0} PUnit.{1} (CommMonoidWithZero.toMonoidWithZero.{0} PUnit.{1} (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero)))) (NormalizationMonoid.normUnit.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero (NormalizedGCDMonoid.toNormalizationMonoid.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero PUnit.normalizedGCDMonoid) x) (OfNat.ofNat.{0} (Units.{0} PUnit.{1} (MonoidWithZero.toMonoid.{0} PUnit.{1} (CommMonoidWithZero.toMonoidWithZero.{0} PUnit.{1} (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero)))) 1 (One.toOfNat1.{0} (Units.{0} PUnit.{1} (MonoidWithZero.toMonoid.{0} PUnit.{1} (CommMonoidWithZero.toMonoidWithZero.{0} PUnit.{1} (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero)))) (InvOneClass.toOne.{0} (Units.{0} PUnit.{1} (MonoidWithZero.toMonoid.{0} PUnit.{1} (CommMonoidWithZero.toMonoidWithZero.{0} PUnit.{1} (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero)))) (DivInvOneMonoid.toInvOneClass.{0} (Units.{0} PUnit.{1} (MonoidWithZero.toMonoid.{0} PUnit.{1} (CommMonoidWithZero.toMonoidWithZero.{0} PUnit.{1} (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero)))) (DivisionMonoid.toDivInvOneMonoid.{0} (Units.{0} PUnit.{1} (MonoidWithZero.toMonoid.{0} PUnit.{1} (CommMonoidWithZero.toMonoidWithZero.{0} PUnit.{1} (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero)))) (DivisionCommMonoid.toDivisionMonoid.{0} (Units.{0} PUnit.{1} (MonoidWithZero.toMonoid.{0} PUnit.{1} (CommMonoidWithZero.toMonoidWithZero.{0} PUnit.{1} (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero)))) (CommGroup.toDivisionCommMonoid.{0} (Units.{0} PUnit.{1} (MonoidWithZero.toMonoid.{0} PUnit.{1} (CommMonoidWithZero.toMonoidWithZero.{0} PUnit.{1} (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} PUnit.{1} PUnit.cancelCommMonoidWithZero)))) (Units.instCommGroupUnitsToMonoid.{0} PUnit.{1} (CommRing.toCommMonoid.{0} PUnit.{1} PUnit.commRing.{0})))))))))
Case conversion may be inaccurate. Consider using '#align punit.norm_unit_eq PUnit.norm_unit_eqₓ'. -/
@[simp]
theorem norm_unit_eq : normUnit x = 1 :=
  rfl
#align punit.norm_unit_eq PUnit.norm_unit_eq

instance : CanonicallyOrderedAddMonoid PUnit := by
  refine'
        { PUnit.commRing, PUnit.completeBooleanAlgebra with
          exists_add_of_le := fun _ _ _ => ⟨star, Subsingleton.elim _ _⟩.. } <;>
      intros <;>
    trivial

instance : LinearOrderedCancelAddCommMonoid PUnit :=
  { PUnit.canonicallyOrderedAddMonoid, PUnit.linearOrder with
    le_of_add_le_add_left := fun _ _ _ _ => trivial }

instance : LinearOrderedAddCommMonoidWithTop PUnit :=
  { PUnit.completeBooleanAlgebra, PUnit.linearOrderedCancelAddCommMonoid with
    top_add' := fun _ => rfl }

@[to_additive]
instance : SMul R PUnit :=
  ⟨fun _ _ => unit⟩

#print PUnit.smul_eq /-
@[simp, to_additive]
theorem smul_eq (r : R) : r • y = unit :=
  rfl
#align punit.smul_eq PUnit.smul_eq
#align punit.vadd_eq PUnit.vadd_eq
-/

@[to_additive]
instance : IsCentralScalar R PUnit :=
  ⟨fun _ _ => rfl⟩

@[to_additive]
instance : SMulCommClass R S PUnit :=
  ⟨fun _ _ _ => rfl⟩

@[to_additive]
instance [SMul R S] : IsScalarTower R S PUnit :=
  ⟨fun _ _ _ => rfl⟩

instance [Zero R] : SMulWithZero R PUnit := by
  refine' { PUnit.hasSmul with .. } <;> intros <;> exact Subsingleton.elim _ _

instance [Monoid R] : MulAction R PUnit := by
  refine' { PUnit.hasSmul with .. } <;> intros <;> exact Subsingleton.elim _ _

instance [Monoid R] : DistribMulAction R PUnit := by
  refine' { PUnit.mulAction with .. } <;> intros <;> exact Subsingleton.elim _ _

instance [Monoid R] : MulDistribMulAction R PUnit := by
  refine' { PUnit.mulAction with .. } <;> intros <;> exact Subsingleton.elim _ _

instance [Semiring R] : MulSemiringAction R PUnit :=
  { PUnit.distribMulAction, PUnit.mulDistribMulAction with }

instance [MonoidWithZero R] : MulActionWithZero R PUnit :=
  { PUnit.mulAction, PUnit.smulWithZero with }

instance [Semiring R] : Module R PUnit := by
  refine' { PUnit.distribMulAction with .. } <;> intros <;> exact Subsingleton.elim _ _

end PUnit

